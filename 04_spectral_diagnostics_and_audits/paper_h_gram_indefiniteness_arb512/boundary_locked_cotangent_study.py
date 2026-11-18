#!/usr/bin/env python3
"""Track C: Boundary-Locked Affine Pure Cotangent Equivalence on A_N (100-dps & 192-bit Arb).

Formalizes and numerically verifies the doubly constrained Nyman-Beurling affine subspace:
    A_N = { c in R^N | D_N(1) = sum_{k=1}^N c_k / k = 0 and D_N(0) = sum_{k=1}^N c_k = 2 }

For every c in A_N, the BDR distance identity eliminates every smooth and logarithmic
boundary term identically without assuming any asymptotic limit on D_N'(0) or D_N'(1):
    E_N(c) = || 1 - sum_{k=1}^N c_k rho_k ||_{L^2(0,1)}^2 = 1 + Q_N^{(cot)}(c).

This script verifies in 100-digit mpmath and 192-bit flint.arb ball arithmetic for N = 2..100:
  1. Exact KKT minimizers c_unc, c_NB (D1=0), and c_aff in A_N (D1=0, D0=2).
  2. Exact identity E_N(c_aff) = 1 + Q_N^{(cot)}(c_aff) across all N = 2..100 (< 1e-95 error,
     and certified zero-containing 192-bit Arb intervals).
  3. 2-sparse boundary corrector w^{(N)} (w_1 = -1/(N-1), w_N = N/(N-1)) satisfying D1=0, D0=1,
     with asymptotic norm N * ||W_N||^2 -> ln(2*pi) - gamma ~ 1.26065521599068.
  4. Quantitative gap between d_N^2, d_{NB,N}^2, E_N(c_aff), and 1 + Q_N^{(cot)}(c_aff),
     along with explicit governance preservation (NO_RH_PROOF = True).
"""

from __future__ import annotations

import json
import math
from pathlib import Path
import sys
import time
from typing import Any, Dict, List

from flint import arb, arb_mat, ctx
import mpmath as mp

SCRIPT_DIR = Path(__file__).resolve().parent
if str(SCRIPT_DIR) not in sys.path:
    sys.path.insert(0, str(SCRIPT_DIR))

from sparse_bnbd_compression_study import CachedVasyuninEngine  # noqa: E402

DPS = 100
ARB_BITS = 192
MAX_N = 100
OUT_JSON = SCRIPT_DIR / "boundary_locked_cotangent_results.json"


def _build_vasyunin_arb_matrices(
    max_n: int, arb_bits: int = ARB_BITS
) -> Dict[str, Any]:
    """Build full max_n x max_n (G_total, G_smooth, G_cot) and vectors b, h, e in flint.arb."""
    with ctx.workprec(arb_bits):
        ln2pi = (arb(2) * arb.pi()).log()
        gam = arb.const_euler()
        c_val = ln2pi - gam
        pi_half = arb.pi() / 2

        cot_cache: Dict[tuple[int, int], arb] = {}

        def vasyunin_cot_arb(q: int, p: int) -> arb:
            if q <= 2:
                return arb(0)
            p_mod = p % q
            if p_mod == 0:
                return arb(0)
            inv_p = pow(p_mod, -1, q)
            key = (inv_p, q)
            if key in cot_cache:
                return cot_cache[key]
            half = (q - 1) // 2
            pi_over_q = arb.pi() / q
            tot = arb(0)
            for m in range(1, half + 1):
                tot += (2 * m - q) * (pi_over_q * ((m * inv_p) % q)).cot()
            tot /= q
            cot_cache[key] = tot
            return tot

        G_tot = arb_mat(max_n, max_n)
        G_sm = arb_mat(max_n, max_n)
        G_ct = arb_mat(max_n, max_n)

        for j in range(1, max_n + 1):
            for k in range(j, max_n + 1):
                g = math.gcd(j, k)
                a, b = j // g, k // g
                gs_cop = (c_val * (a + b) - 2 - (b - a) * (arb(b) / arb(a)).log()) / (
                    2 * arb(a) * arb(b)
                )
                gs = gs_cop / g + arb(g - 1) / (arb(g) * g * a * b)
                v_ab = vasyunin_cot_arb(a, b) if a > 2 else arb(0)
                v_ba = vasyunin_cot_arb(b, a) if b > 2 else arb(0)
                gc = -(pi_half / (arb(g) * a * b)) * (v_ab + v_ba)
                gt = gs + gc
                G_sm[j - 1, k - 1] = G_sm[k - 1, j - 1] = gs
                G_ct[j - 1, k - 1] = G_ct[k - 1, j - 1] = gc
                G_tot[j - 1, k - 1] = G_tot[k - 1, j - 1] = gt

        b_vec = [((arb(k).log() + 1 - gam) / k) for k in range(1, max_n + 1)]
        h_vec = [arb(1) / k for k in range(1, max_n + 1)]
        e_vec = [arb(1) for _ in range(1, max_n + 1)]
        return {
            "G_tot": G_tot,
            "G_smooth": G_sm,
            "G_cot": G_ct,
            "b": b_vec,
            "h": h_vec,
            "e": e_vec,
            "max_arb_rad": max(abs(G_tot[i, j].rad()) for i in range(max_n) for j in range(i, max_n)),
        }


def _solve_submatrix_kkt_arb(arb_data: Dict[str, Any], n: int) -> Dict[str, Any]:
    """Certify KKT solution and pure cotangent equivalence at dimension n in 192-bit flint.arb."""
    with ctx.workprec(ARB_BITS):
        G = arb_mat([[arb_data["G_tot"][i, j] for j in range(n)] for i in range(n)])
        G_sm = arb_mat([[arb_data["G_smooth"][i, j] for j in range(n)] for i in range(n)])
        G_ct = arb_mat([[arb_data["G_cot"][i, j] for j in range(n)] for i in range(n)])

        rhs = arb_mat(n, 3)
        for i in range(n):
            rhs[i, 0] = arb_data["b"][i]
            rhs[i, 1] = arb_data["h"][i]
            rhs[i, 2] = arb_data["e"][i]

        Z = G.solve(rhs)  # cols: z_b, z_h, z_e

        def dot_col(u_col: int, v_col: int) -> arb:
            return sum((rhs[i, u_col] * Z[i, v_col] for i in range(n)), arb(0))

        bb = dot_col(0, 0)
        hb = dot_col(1, 0)
        eb = dot_col(2, 0)
        hh = dot_col(1, 1)
        he = dot_col(1, 2)
        ee = dot_col(2, 2)

        det_c = hh * ee - he * he
        lam1 = (ee * hb - he * (eb - 2)) / det_c
        lam2 = (-he * hb + hh * (eb - 2)) / det_c

        c_aff = arb_mat(n, 1)
        for i in range(n):
            c_aff[i, 0] = Z[i, 0] - lam1 * Z[i, 1] - lam2 * Z[i, 2]

        d1_val = sum((arb_data["h"][i] * c_aff[i, 0] for i in range(n)), arb(0))
        d0_val = sum((c_aff[i, 0] for i in range(n)), arb(0))
        bt_c = sum((arb_data["b"][i] * c_aff[i, 0] for i in range(n)), arb(0))
        q_sm = (c_aff.transpose() * G_sm * c_aff)[0, 0]
        q_ct = (c_aff.transpose() * G_ct * c_aff)[0, 0]
        q_tot = (c_aff.transpose() * G * c_aff)[0, 0]

        e_full = 1 - 2 * bt_c + q_sm + q_ct
        e_from_qtot = 1 - 2 * bt_c + q_tot
        e_pure_cot = 1 + q_ct
        diff_identity = e_full - e_pure_cot
        diff_sym = e_full - e_from_qtot

        # KKT gradient residual: G c_aff - b + lam1 * h + lam2 * e = 0
        Gc = G * c_aff
        max_kkt_res = max(
            abs((Gc[i, 0] - rhs[i, 0] + lam1 * rhs[i, 1] + lam2 * rhs[i, 2]).upper())
            for i in range(n)
        )

        # 2-sparse corrector w^{(N)}
        w_n = arb_mat(n, 1)
        inv_nm1 = arb(1) / arb(n - 1)
        w_n[0, 0] = -inv_nm1
        w_n[n - 1, 0] = arb(n) * inv_nm1
        w_d1 = sum((arb_data["h"][i] * w_n[i, 0] for i in range(n)), arb(0))
        w_d0 = sum((w_n[i, 0] for i in range(n)), arb(0))
        w_norm_sq = (w_n.transpose() * G * w_n)[0, 0]

        return {
            "N": n,
            "arb_d1_contains_zero": bool(d1_val.contains(0)),
            "arb_d0_contains_two": bool((d0_val - 2).contains(0)),
            "arb_identity_diff_contains_zero": bool(diff_identity.contains(0)),
            "arb_e_full_mid": float(e_full.mid()),
            "arb_e_full_rad": float(e_full.rad()),
            "arb_q_cot_mid": float(q_ct.mid()),
            "arb_identity_diff_abs_upper": float(abs(diff_identity).upper()),
            "arb_sym_diff_abs_upper": float(abs(diff_sym).upper()),
            "arb_kkt_grad_res_upper": float(max_kkt_res),
            "arb_w_d1_contains_zero": bool(w_d1.contains(0)),
            "arb_w_d0_contains_one": bool((w_d0 - 1).contains(0)),
            "arb_w_norm_sq_mid": float(w_norm_sq.mid()),
            "arb_w_norm_sq_rad": float(w_norm_sq.rad()),
        }


def _solve_rank4_corrector_arb(t0: arb, t0p: arb, t1: arb, t1p: arb) -> list[arb]:
    """Exact 192-bit Arb inverse of the 4x4 Clay Vandermonde-log operator U_4^T."""
    rows = []
    for f in (
        lambda k: arb(1),
        lambda k: -arb(k).log(),
        lambda k: arb(1) / arb(k),
        lambda k: -arb(k).log() / arb(k),
    ):
        rows.extend([f(1), f(2), f(3), f(4)])
    return list(arb_mat(4, 4, rows).solve(arb_mat(4, 1, [t0, t0p, t1, t1p])))


def _period12_cotangent_reciprocity_cross_check_arb(
    arb_data: Dict[str, Any], n_checkpoints: tuple[int, ...] = (64, 100)
) -> Dict[str, Any]:
    """192-bit Arb cross-check of Period-12 Dedekind-Ramanujan reciprocity & character injection."""
    with ctx.workprec(ARB_BITS):
        max_n = arb_data["G_cot"].nrows()
        gam = arb.const_euler()
        pi_sq_72 = (arb.pi() ** 2) / arb(72)
        t0p_base = -2 * (2 * arb.pi()).log()
        w_base4 = _solve_rank4_corrector_arb(arb(2), t0p_base, arb(0), arb(-1))
        phi_base = [
            sum((w_base4[j] * arb_data["G_cot"][j, k] for j in range(4)), arb(0))
            for k in range(max_n)
        ]
        phi_smooth = [
            sum((w_base4[j] * arb_data["G_smooth"][j, k] for j in range(4)), arb(0))
            for k in range(max_n)
        ]
        max_sm_err = max(
            float(
                abs(
                    phi_smooth[k - 1] - (arb(1) / arb(2) + (arb(k).log() - gam) / arb(k))
                ).upper()
            )
            for k in range(1, max_n + 1)
        )
        assert max_sm_err < 1e-45

        G_ct_full = arb_data["G_cot"]
        G_sm_full = arb_data["G_smooth"]
        q_base4 = sum(
            (w_base4[i] * w_base4[j] * G_ct_full[i, j] for i in range(4) for j in range(4)),
            arb(0),
        )
        e_base = arb(1) + q_base4

        c_cop = {1: arb(1), 2: arb(-1) / arb(4), 3: arb(-5) / arb(9), 4: arb(-1) / arb(2)}
        alpha_1 = w_base4[0] + (arb(7) / arb(8)) * w_base4[1] + (arb(17) / arb(27)) * w_base4[2] + (arb(5) / arb(8)) * w_base4[3]
        alpha_2 = (arb(9) / arb(8)) * (w_base4[1] + w_base4[3])
        alpha_3 = (arb(32) / arb(27)) * w_base4[2]
        alpha_4 = (arb(9) / arb(8)) * w_base4[3]

        def _c_d(d: int, n: int) -> int:
            if d == 1:
                return 1
            if d == 2:
                return 1 if n % 2 == 0 else -1
            if d == 3:
                return 2 if n % 3 == 0 else -1
            r4 = n % 4
            return 2 if r4 == 0 else (-2 if r4 == 2 else 0)

        max_ram_err = 0.0
        for r in range(1, 13):
            v_gcd = pi_sq_72 * sum(
                (w_base4[j - 1] * arb(math.gcd(j, r)) * c_cop[j // math.gcd(j, r)] for j in range(1, 5)),
                arb(0),
            )
            v_ram = pi_sq_72 * (
                alpha_1 * _c_d(1, r) + alpha_2 * _c_d(2, r) + alpha_3 * _c_d(3, r) + alpha_4 * _c_d(4, r)
            )
            max_ram_err = max(max_ram_err, float(abs(v_gcd - v_ram).upper()))
        assert max_ram_err < 1e-45

        def _hom_proj(vec: list[arb], n: int) -> list[arb]:
            d0 = sum(vec[:n], arb(0))
            d0p = -sum((vec[k - 1] * arb(k).log() for k in range(1, n + 1)), arb(0))
            d1 = sum((vec[k - 1] / arb(k) for k in range(1, n + 1)), arb(0))
            d1p = -sum((vec[k - 1] * arb(k).log() / arb(k) for k in range(1, n + 1)), arb(0))
            corr = _solve_rank4_corrector_arb(-d0, -d0p, -d1, -d1p)
            res = list(vec[:n])
            for j in range(4):
                res[j] += corr[j]
            return res

        def _bilin(u: list[arb], v: list[arb], mat: arb_mat, n: int) -> arb:
            return sum((u[i] * v[j] * mat[i, j] for i in range(n) for j in range(n)), arb(0))

        char6_rows = []
        for n in n_checkpoints:
            w_base = w_base4 + [arb(0)] * (n - 4)
            basis = [
                _hom_proj([arb(_c_d(1, k)) / arb(k * k) for k in range(1, n + 1)], n),
                _hom_proj([arb(_c_d(2, k)) / arb(k * k) for k in range(1, n + 1)], n),
                _hom_proj([arb(_c_d(3, k)) / arb(k * k) for k in range(1, n + 1)], n),
                _hom_proj([arb(_c_d(4, k)) / arb(k * k) for k in range(1, n + 1)], n),
                _hom_proj(
                    [arb(1 if k % 3 == 1 else (-1 if k % 3 == 2 else 0)) / arb(k * k) for k in range(1, n + 1)],
                    n,
                ),
                _hom_proj(
                    [arb(1 if k % 4 == 1 else (-1 if k % 4 == 3 else 0)) / arb(k * k) for k in range(1, n + 1)],
                    n,
                ),
            ]
            m = len(basis)
            M_mat = arb_mat(m, m, [_bilin(basis[r], basis[s], G_ct_full, n) for r in range(m) for s in range(m)])
            R_mat = arb_mat(m, 1, [-_bilin(basis[r], w_base, G_ct_full, n) for r in range(m)])
            pre = M_mat.mid().inv().mid()
            z_mat = (pre * M_mat).solve(pre * R_mat)
            u_dir = [sum((arb(z_mat[r, 0].mid()) * basis[r][k] for r in range(m)), arb(0)) for k in range(n)]
            v_dir = _hom_proj(u_dir, n)
            b_lin = _bilin(w_base, v_dir, G_ct_full, n)
            a_quad = _bilin(v_dir, v_dir, G_ct_full, n)
            alpha = -b_lin / a_quad
            c_char = [w_base[k] + alpha * v_dir[k] for k in range(n)]
            virial_err = float(abs(_bilin(c_char, v_dir, G_ct_full, n)).upper())
            q_sm = _bilin(c_char, c_char, G_sm_full, n)
            q_ct = _bilin(c_char, c_char, G_ct_full, n)
            bt_c = sum((arb_data["b"][k] * c_char[k] for k in range(n)), arb(0))
            e_fl = arb(1) - 2 * bt_c + q_sm + q_ct
            id_err = float(abs(e_fl - (arb(1) + q_ct)).upper())
            assert virial_err < 1e-42 and id_err < 1e-42
            assert bool(e_fl < e_base)
            char6_rows.append(
                {
                    "N": n,
                    "E_base_rank4": float(e_base.mid()),
                    "E_char6_mod12": float(e_fl.mid()),
                    "char6_reduction_from_base": float((e_base - e_fl).mid()),
                    "virial_orth_err_upper": virial_err,
                    "identity_err_upper": id_err,
                }
            )

        return {
            "max_smooth_identity_err_upper": max_sm_err,
            "max_ramanujan_sum_equiv_err_upper": max_ram_err,
            "phi_base_first4_mid": [float(phi_base[j].mid()) for j in range(4)],
            "checkpoints_64_100": char6_rows,
            "char6_strictly_reduces_below_base_at_64_and_100": True,
        }


def run_study(max_n: int = MAX_N, dps: int = DPS) -> Dict[str, Any]:
    """Run full 100-dps mpmath + 192-bit flint.arb study for N = 2..max_n."""
    t0 = time.time()
    engine = CachedVasyuninEngine(dps=dps, arb_bits=360)

    # Prebuild full Gram matrices at 100 dps
    with mp.workdps(dps + 15):
        G_tot = mp.matrix(max_n, max_n)
        G_sm = mp.matrix(max_n, max_n)
        G_ct = mp.matrix(max_n, max_n)
        b_full: List[mp.mpf] = [engine.rhs_entry(k) for k in range(1, max_n + 1)]
        h_full: List[mp.mpf] = [mp.mpf(1) / k for k in range(1, max_n + 1)]
        e_full_vec: List[mp.mpf] = [mp.mpf(1) for _ in range(1, max_n + 1)]

        for j in range(1, max_n + 1):
            for k in range(j, max_n + 1):
                gt, gs, gc = engine.gram_entry(j, k)
                G_tot[j - 1, k - 1] = G_tot[k - 1, j - 1] = gt
                G_sm[j - 1, k - 1] = G_sm[k - 1, j - 1] = gs
                G_ct[j - 1, k - 1] = G_ct[k - 1, j - 1] = gc

        # Incremental Cholesky of G_tot = L L^T
        L_rows: List[List[mp.mpf]] = []
        y_b: List[mp.mpf] = []
        y_h: List[mp.mpf] = []
        y_e: List[mp.mpf] = []
        ln2pi_minus_gamma = mp.log(2 * mp.pi) - mp.euler

        rows_n: List[Dict[str, Any]] = []
        max_identity_err = mp.mpf(0)
        max_d1_err = mp.mpf(0)
        max_d0_err = mp.mpf(0)
        max_kkt_grad_err = mp.mpf(0)
        max_nb_d1_err = mp.mpf(0)

        for n in range(1, max_n + 1):
            # Build Cholesky row n-1
            row: List[mp.mpf] = []
            for j in range(n - 1):
                s = G_tot[n - 1, j]
                lj = L_rows[j]
                for p in range(j):
                    s -= row[p] * lj[p]
                row.append(s / lj[j])
            diag_sq = G_tot[n - 1, n - 1] - sum((v * v for v in row), mp.mpf(0))
            row.append(mp.sqrt(diag_sq))
            L_rows.append(row)

            def fwd_step(rhs_val: mp.mpf, y_prev: List[mp.mpf]) -> mp.mpf:
                s = rhs_val
                for j in range(n - 1):
                    s -= row[j] * y_prev[j]
                return s / row[-1]

            y_b.append(fwd_step(b_full[n - 1], y_b))
            y_h.append(fwd_step(h_full[n - 1], y_h))
            y_e.append(fwd_step(e_full_vec[n - 1], y_e))

            if n < 2:
                continue

            # Inner products <z_u, v> = <y_u, y_v>
            bb = sum(y_b[i] * y_b[i] for i in range(n))
            hb = sum(y_h[i] * y_b[i] for i in range(n))
            eb = sum(y_e[i] * y_b[i] for i in range(n))
            hh = sum(y_h[i] * y_h[i] for i in range(n))
            he = sum(y_h[i] * y_e[i] for i in range(n))
            ee = sum(y_e[i] * y_e[i] for i in range(n))

            d_unc_sq = 1 - bb

            # Singly constrained NB minimizer: D_N(1) = 0
            lam_nb = hb / hh
            delta_nb = (hb * hb) / hh
            d_nb_sq = d_unc_sq + delta_nb

            # Doubly constrained affine minimizer in A_N: D_N(1) = 0, D_N(0) = 2
            det_c = hh * ee - he * he
            r_h = hb
            r_e = eb - 2
            lam1 = (ee * r_h - he * r_e) / det_c
            lam2 = (-he * r_h + hh * r_e) / det_c
            delta_aff = r_h * lam1 + r_e * lam2
            e_aff_chol = d_unc_sq + delta_aff

            # Explicit back-substitution L^T c = y_b - lam1 * y_h - lam2 * y_e
            y_aff = [y_b[i] - lam1 * y_h[i] - lam2 * y_e[i] for i in range(n)]
            c_aff = [mp.mpf(0)] * n
            for i in range(n - 1, -1, -1):
                s = y_aff[i]
                for j in range(i + 1, n):
                    s -= L_rows[j][i] * c_aff[j]
                c_aff[i] = s / L_rows[i][i]

            # Explicit back-substitution for c_NB (check D_N(0; c_NB) drift!)
            y_nb = [y_b[i] - lam_nb * y_h[i] for i in range(n)]
            c_nb = [mp.mpf(0)] * n
            for i in range(n - 1, -1, -1):
                s = y_nb[i]
                for j in range(i + 1, n):
                    s -= L_rows[j][i] * c_nb[j]
                c_nb[i] = s / L_rows[i][i]
            d1_nb = sum(c_nb[i] * h_full[i] for i in range(n))
            d0_nb = sum(c_nb)

            # Direct verification of D1, D0, Q_smooth, Q_cot, and E_N(c_aff) == 1 + Q_cot(c_aff)
            d1_aff = sum(c_aff[i] * h_full[i] for i in range(n))
            d0_aff = sum(c_aff)
            lin_aff = sum(c_aff[i] * b_full[i] for i in range(n))
            q_sm_aff = mp.mpf(0)
            q_ct_aff = mp.mpf(0)
            q_tot_aff = mp.mpf(0)
            kkt_res = mp.mpf(0)
            for i in range(n):
                row_dot = mp.mpf(0)
                for j in range(n):
                    prod = c_aff[i] * c_aff[j]
                    q_sm_aff += prod * G_sm[i, j]
                    q_ct_aff += prod * G_ct[i, j]
                    q_tot_aff += prod * G_tot[i, j]
                    row_dot += G_tot[i, j] * c_aff[j]
                err_i = abs(row_dot - b_full[i] + lam1 * h_full[i] + lam2 * e_full_vec[i])
                if err_i > kkt_res:
                    kkt_res = err_i

            e_full_direct = 1 - 2 * lin_aff + q_sm_aff + q_ct_aff
            e_pure_cot = 1 + q_ct_aff
            id_err = abs(e_full_direct - e_pure_cot)
            chol_err = abs(e_full_direct - e_aff_chol)

            max_identity_err = max(max_identity_err, id_err, chol_err)
            max_d1_err = max(max_d1_err, abs(d1_aff))
            max_d0_err = max(max_d0_err, abs(d0_aff - 2))
            max_kkt_grad_err = max(max_kkt_grad_err, kkt_res)
            max_nb_d1_err = max(max_nb_d1_err, abs(d1_nb))

            # 2-sparse corrector w^{(N)}: w_1 = -1/(N-1), w_N = N/(N-1)
            w1 = -mp.mpf(1) / (n - 1)
            wn = mp.mpf(n) / (n - 1)
            w_norm_sq = (
                w1 * w1 * G_tot[0, 0]
                + 2 * w1 * wn * G_tot[0, n - 1]
                + wn * wn * G_tot[n - 1, n - 1]
            )
            w_scaled = n * w_norm_sq
            w_smooth_only = (
                w1 * w1 * G_sm[0, 0]
                + 2 * w1 * wn * G_sm[0, n - 1]
                + wn * wn * G_sm[n - 1, n - 1]
            )
            w_cot_only = (
                w1 * w1 * G_ct[0, 0]
                + 2 * w1 * wn * G_ct[0, n - 1]
                + wn * wn * G_ct[n - 1, n - 1]
            )
            # Also check unconstrained D1 and D0
            d1_unc = hb
            d0_unc = eb

            rows_n.append(
                {
                    "N": n,
                    "d_unc_sq": float(d_unc_sq),
                    "d_nb_sq": float(d_nb_sq),
                    "E_aff_min": float(e_full_direct),
                    "E_aff_min_str": mp.nstr(e_full_direct, 25),
                    "Q_cot_aff_min": float(q_ct_aff),
                    "Q_cot_aff_min_str": mp.nstr(q_ct_aff, 25),
                    "smooth_residual_aff": float(1 - 2 * lin_aff + q_sm_aff),
                    "delta_nb": float(delta_nb),
                    "delta_aff": float(delta_aff),
                    "affine_over_nb_penalty": float(delta_aff - delta_nb),
                    "d0_unc": float(d0_unc),
                    "d1_unc": float(d1_unc),
                    "d0_nb": float(d0_nb),
                    "lambda1_d1": float(lam1),
                    "lambda2_d0": float(lam2),
                    "identity_err_mp": float(id_err),
                    "d1_aff_err_mp": float(abs(d1_aff)),
                    "d0_aff_err_mp": float(abs(d0_aff - 2)),
                    "kkt_grad_res_mp": float(kkt_res),
                    "w_corrector_norm_sq": float(w_norm_sq),
                    "w_corrector_N_times_norm_sq": float(w_scaled),
                    "w_corrector_remainder_vs_asymptotic": float(w_scaled - ln2pi_minus_gamma),
                    "w_corrector_cot_share": float(w_cot_only),
                    "w_corrector_smooth_share": float(w_smooth_only),
                    "c_aff_norm_l2": float(mp.sqrt(sum(v * v for v in c_aff))),
                }
            )

        # Verify monotonicity across N = 2..100
        d_unc_mono = all(rows_n[i]["d_unc_sq"] >= rows_n[i + 1]["d_unc_sq"] for i in range(len(rows_n) - 1))
        d_nb_mono = all(rows_n[i]["d_nb_sq"] >= rows_n[i + 1]["d_nb_sq"] for i in range(len(rows_n) - 1))
        e_aff_mono = all(rows_n[i]["E_aff_min"] >= rows_n[i + 1]["E_aff_min"] for i in range(len(rows_n) - 1))
        q_cot_aff_mono = all(
            rows_n[i]["Q_cot_aff_min"] >= rows_n[i + 1]["Q_cot_aff_min"] for i in range(len(rows_n) - 1)
        )

    # Independent 192-bit flint.arb verification on checkpoint grid
    arb_data = _build_vasyunin_arb_matrices(max_n, ARB_BITS)
    checkpoints = [2, 3, 5, 10, 15, 20, 30, 40, 50, 60, 75, 80, 90, 95, 100]
    arb_checks = [_solve_submatrix_kkt_arb(arb_data, n) for n in checkpoints if n <= max_n]
    period12_cross_check = _period12_cotangent_reciprocity_cross_check_arb(arb_data, (64, 100))

    with mp.workdps(dps + 10):
        asymptotic_const = float(mp.log(2 * mp.pi) - mp.euler)

    elapsed = time.time() - t0
    by_n = {row["N"]: row for row in rows_n}
    return {
        "metadata": {
            "track": "Track C: Boundary-Locked Affine Pure Cotangent Equivalence on A_N",
            "timestamp_iso": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
            "elapsed_seconds": elapsed,
            "mpmath_dps": dps,
            "arb_bits": ARB_BITS,
            "max_N": max_n,
            "max_arb_cot_radius": float(engine._cot_rad_max),
            "max_arb_gram_radius_192bit": float(arb_data["max_arb_rad"]),
            "NO_RH_PROOF": True,
            "PUBLICATION_STATUS": "HOLD",
        },
        "global_verification": {
            "max_mp_identity_err": float(max_identity_err),
            "max_mp_d1_aff_err": float(max_d1_err),
            "max_mp_d0_aff_err": float(max_d0_err),
            "max_mp_nb_d1_err": float(max_nb_d1_err),
            "max_mp_kkt_grad_res": float(max_kkt_grad_err),
            "all_arb_checkpoints_d1_contains_zero": all(c["arb_d1_contains_zero"] for c in arb_checks),
            "all_arb_checkpoints_d0_contains_two": all(c["arb_d0_contains_two"] for c in arb_checks),
            "all_arb_checkpoints_identity_contains_zero": all(
                c["arb_identity_diff_contains_zero"] for c in arb_checks
            ),
            "all_arb_checkpoints_w_d1_zero": all(c["arb_w_d1_contains_zero"] for c in arb_checks),
            "all_arb_checkpoints_w_d0_one": all(c["arb_w_d0_contains_one"] for c in arb_checks),
            "d_unc_monotone_decreasing": d_unc_mono,
            "d_nb_monotone_decreasing": d_nb_mono,
            "e_aff_monotone_decreasing": e_aff_mono,
            "q_cot_aff_monotone_decreasing": q_cot_aff_mono,
        },
        "corrector_asymptotics": {
            "exact_limit_ln2pi_minus_gamma": asymptotic_const,
            "N_10_N_times_w_sq": by_n[10]["w_corrector_N_times_norm_sq"],
            "N_25_N_times_w_sq": by_n[25]["w_corrector_N_times_norm_sq"],
            "N_50_N_times_w_sq": by_n[50]["w_corrector_N_times_norm_sq"],
            "N_75_N_times_w_sq": by_n[75]["w_corrector_N_times_norm_sq"],
            "N_100_N_times_w_sq": by_n[100]["w_corrector_N_times_norm_sq"],
            "N_100_abs_gap_from_limit": abs(by_n[100]["w_corrector_remainder_vs_asymptotic"]),
        },
        "arb_checkpoints": arb_checks,
        "period12_character_cross_check_64_100": period12_cross_check,
        "checkpoints": [by_n[n] for n in checkpoints if n in by_n],
        "series_N_2_to_100": rows_n,
    }


def main() -> None:
    res = run_study()
    OUT_JSON.write_text(json.dumps(res, indent=2) + "\n", encoding="utf-8")
    gv = res["global_verification"]
    ca = res["corrector_asymptotics"]
    print("=" * 96)
    print("TRACK C: BOUNDARY-LOCKED PURE COTANGENT EQUIVALENCE ON A_N (N = 2..100)")
    print("=" * 96)
    print(
        f"Max 100-dps errors: |E_N - (1+Q_cot)| = {gv['max_mp_identity_err']:.3e}, "
        f"|D1| = {gv['max_mp_d1_aff_err']:.3e}, |D0 - 2| = {gv['max_mp_d0_aff_err']:.3e}, "
        f"KKT res = {gv['max_mp_kkt_grad_res']:.3e}"
    )
    print(
        f"192-bit Arb checks: D1=0={gv['all_arb_checkpoints_d1_contains_zero']}, "
        f"D0=2={gv['all_arb_checkpoints_d0_contains_two']}, "
        f"E=1+Q_cot={gv['all_arb_checkpoints_identity_contains_zero']}, "
        f"w_D1=0={gv['all_arb_checkpoints_w_d1_zero']}, "
        f"w_D0=1={gv['all_arb_checkpoints_w_d0_one']}"
    )
    print(
        f"Corrector asymptotic N*||W_N||^2 -> ln(2pi)-gamma = {ca['exact_limit_ln2pi_minus_gamma']:.12f} "
        f"(at N=100: {ca['N_100_N_times_w_sq']:.12f}, gap={ca['N_100_abs_gap_from_limit']:.6e})"
    )
    print("-" * 96)
    print(
        f"{'N':>4} | {'d_unc^2':>11} | {'d_NB^2':>11} | {'E_aff':>11} | {'Q_cot(c_aff)':>13} | "
        f"{'D0(c_NB)':>10} | {'N*||W_N||^2':>12}"
    )
    print("-" * 96)
    for row in res["checkpoints"]:
        print(
            f"{row['N']:>4d} | {row['d_unc_sq']:>11.8f} | {row['d_nb_sq']:>11.8f} | "
            f"{row['E_aff_min']:>11.8f} | {row['Q_cot_aff_min']:>13.8f} | "
            f"{row['d0_nb']:>10.6f} | {row['w_corrector_N_times_norm_sq']:>12.8f}"
        )
    print("=" * 96)
    print(f"Saved results in {res['metadata']['elapsed_seconds']:.2f}s to: {OUT_JSON}")


if __name__ == "__main__":
    main()
