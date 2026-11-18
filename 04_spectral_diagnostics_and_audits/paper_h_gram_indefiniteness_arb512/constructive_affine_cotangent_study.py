#!/usr/bin/env python3
"""Track 2 (Strategy 1): Constructive Affine-Locked Mollifier Families on A_N.

Evaluates explicit closed-form trial sequences c^{(N)} in A_N (without inverting G_N)
at 80-dps mpmath + 192-bit flint.arb across N in {10, 20, 30, 50, 75, 100, 125, 150}:
  - Family A: 2-Endpoint Corrected SBD (alpha in {1.0, 1.5, 2.0})
  - Family B: Smooth-Subspace (h, e)-Projected SBD (alpha in {1.0, 1.5, 2.0})
  - Family C: Cubic Selberg-Polynomial Envelope in A_N (closed-form optimal a_3)

Verifies the pure cotangent identity E_N(c) = 1 + Q_N^{(cot)}(c) to < 1e-75 in 80-dps
mpmath and zero-enclosing 192-bit flint.arb balls, tracks (1 + Q_N^{(cot)}) * ln(N),
and decomposes Q_N^{(cot)} into unit, prime-prime, prime-composite, and composite-composite
contributions.

Governance invariants:
- NO_RH_PROOF = True
- FULL_POINT_L1 = 'NOT_ISSUED'
- PUBLICATION_STATUS = 'HOLD'
"""

from __future__ import annotations

import json
import math
from pathlib import Path
import sys
import time
from typing import Any, Dict, List, Tuple

from flint import arb, arb_mat, ctx
import mpmath as mp

SCRIPT_DIR = Path(__file__).resolve().parent
if str(SCRIPT_DIR) not in sys.path:
    sys.path.insert(0, str(SCRIPT_DIR))

from boundary_locked_cotangent_study import _build_vasyunin_arb_matrices  # noqa: E402

MP_DPS = 80
ARB_BITS = 192
N_LIST = [10, 20, 30, 50, 75, 100, 125, 150, 175, 200]
MAX_N = max(N_LIST)
ALPHAS = [1.0, 1.5, 2.0]
OUT_JSON = SCRIPT_DIR / "constructive_affine_cotangent_results.json"


def _mobius_sieve(max_n: int) -> List[int]:
    mu = [1] * (max_n + 1)
    mu[0] = 0
    is_prime = [True] * (max_n + 1)
    primes: List[int] = []
    for i in range(2, max_n + 1):
        if is_prime[i]:
            primes.append(i)
            mu[i] = -1
        for p in primes:
            if i * p > max_n:
                break
            is_prime[i * p] = False
            if i % p == 0:
                mu[i * p] = 0
                break
            mu[i * p] = -mu[i]
    return mu


def _is_prime_list(max_n: int) -> List[bool]:
    is_p = [False] * (max_n + 1)
    for n in range(2, max_n + 1):
        ok = True
        d = 2
        while d * d <= n:
            if n % d == 0:
                ok = False
                break
            d += 1
        is_p[n] = ok
    return is_p


def _build_mp_matrices(max_n: int) -> Dict[str, Any]:
    """Build 80-dps mpmath G_tot, G_smooth, G_cot, b, h, e up to max_n."""
    mp.mp.dps = MP_DPS
    ln2pi = mp.log(2 * mp.pi)
    gam = mp.euler
    c_val = ln2pi - gam
    pi_half = mp.pi / 2

    cot_cache: Dict[Tuple[int, int], mp.mpf] = {}

    def vasyunin_cot_mp(q: int, p: int) -> mp.mpf:
        if q <= 2:
            return mp.mpf(0)
        p_mod = p % q
        if p_mod == 0:
            return mp.mpf(0)
        inv_p = pow(p_mod, -1, q)
        key = (inv_p, q)
        if key in cot_cache:
            return cot_cache[key]
        half = (q - 1) // 2
        pi_over_q = mp.pi / q
        tot = mp.mpf(0)
        for m in range(1, half + 1):
            tot += (2 * m - q) * mp.cot(pi_over_q * ((m * inv_p) % q))
        tot /= q
        cot_cache[key] = tot
        return tot

    G_tot = [[mp.mpf(0)] * max_n for _ in range(max_n)]
    G_sm = [[mp.mpf(0)] * max_n for _ in range(max_n)]
    G_ct = [[mp.mpf(0)] * max_n for _ in range(max_n)]

    for j in range(1, max_n + 1):
        for k in range(j, max_n + 1):
            g = math.gcd(j, k)
            a, b = j // g, k // g
            gs_cop = (c_val * (a + b) - 2 - (b - a) * mp.log(mp.mpf(b) / a)) / (2 * mp.mpf(a) * b)
            gs = gs_cop / g + mp.mpf(g - 1) / (mp.mpf(g) * g * a * b)
            v_ab = vasyunin_cot_mp(a, b) if a > 2 else mp.mpf(0)
            v_ba = vasyunin_cot_mp(b, a) if b > 2 else mp.mpf(0)
            gc = -(pi_half / (mp.mpf(g) * a * b)) * (v_ab + v_ba)
            gt = gs + gc
            G_sm[j - 1][k - 1] = G_sm[k - 1][j - 1] = gs
            G_ct[j - 1][k - 1] = G_ct[k - 1][j - 1] = gc
            G_tot[j - 1][k - 1] = G_tot[k - 1][j - 1] = gt

    b_vec = [(mp.log(k) + 1 - gam) / k for k in range(1, max_n + 1)]
    h_vec = [mp.mpf(1) / k for k in range(1, max_n + 1)]
    e_vec = [mp.mpf(1) for _ in range(1, max_n + 1)]
    return {"G_tot": G_tot, "G_smooth": G_sm, "G_cot": G_ct, "b": b_vec, "h": h_vec, "e": e_vec}


def _sbd_base_mp(n: int, alpha: float, mu: List[int]) -> List[mp.mpf]:
    lnN = mp.log(n)
    a_mp = mp.mpf(str(alpha))
    out: List[mp.mpf] = []
    for k in range(1, n + 1):
        if mu[k] == 0:
            out.append(mp.mpf(0))
        else:
            u = mp.log(k) / lnN
            w = (1 - u) ** a_mp
            out.append(mp.mpf(-mu[k]) * w)
    return out


def _family_a_endpoint_mp(c0: List[mp.mpf], n: int) -> List[mp.mpf]:
    d0 = sum(c0, mp.mpf(0))
    d1 = sum((c0[k - 1] / k for k in range(1, n + 1)), mp.mpf(0))
    delta_0 = 2 - d0
    delta_1 = -d1
    a_n = (mp.mpf(n) / (n - 1)) * (delta_0 - delta_1)
    a_1 = delta_0 - a_n
    c = list(c0)
    c[0] += a_1
    c[n - 1] += a_n
    return c


def _family_b_smooth_proj_mp(c0: List[mp.mpf], n: int) -> List[mp.mpf]:
    """Orthogonal projection of c0 onto A_N along span(h, e) in R^N."""
    h = [mp.mpf(1) / k for k in range(1, n + 1)]
    d0 = sum(c0, mp.mpf(0))
    d1 = sum((c0[k - 1] * h[k - 1] for k in range(1, n + 1)), mp.mpf(0))

    hh = sum((v * v for v in h), mp.mpf(0))
    he = sum(h, mp.mpf(0))
    ee = mp.mpf(n)
    det = hh * ee - he * he
    rhs1 = d1
    rhs2 = d0 - 2
    lam_h = (ee * rhs1 - he * rhs2) / det
    lam_e = (-he * rhs1 + hh * rhs2) / det
    return [c0[i] - lam_h * h[i] - lam_e for i in range(n)]


def _family_c_cubic_mp(n: int, mu: List[int], mp_data: Dict[str, Any]) -> Tuple[List[mp.mpf], Dict[str, float]]:
    """Cubic Selberg-polynomial envelope c_k = -mu(k)(1-u_k)(1 + a1 u_k + a2 u_k^2 + a3 u_k^3) in A_N."""
    lnN = mp.log(n)
    f: List[List[mp.mpf]] = [[mp.mpf(0)] * n for _ in range(4)]
    for k in range(1, n + 1):
        if mu[k] != 0:
            u = mp.log(k) / lnN
            base = mp.mpf(-mu[k]) * (1 - u)
            uk = mp.mpf(1)
            for m in range(4):
                f[m][k - 1] = base * uk
                uk *= u

    d0 = [sum(f[m], mp.mpf(0)) for m in range(4)]
    d1 = [sum((f[m][k - 1] / k for k in range(1, n + 1)), mp.mpf(0)) for m in range(4)]

    # Solve 2x2 system for (a1, a2) as affine functions of a3:
    # d1[1]*a1 + d1[2]*a2 = -d1[0] - d1[3]*a3
    # d0[1]*a1 + d0[2]*a2 = (2 - d0[0]) - d0[3]*a3
    det = d1[1] * d0[2] - d1[2] * d0[1]

    def solve_a1_a2(rhs_1: mp.mpf, rhs_0: mp.mpf) -> Tuple[mp.mpf, mp.mpf]:
        a1 = (rhs_1 * d0[2] - d1[2] * rhs_0) / det
        a2 = (d1[1] * rhs_0 - rhs_1 * d0[1]) / det
        return a1, a2

    a1_0, a2_0 = solve_a1_a2(-d1[0], 2 - d0[0])
    a1_s, a2_s = solve_a1_a2(-d1[3], -d0[3])

    c_base = [f[0][i] + a1_0 * f[1][i] + a2_0 * f[2][i] for i in range(n)]
    v = [f[3][i] + a1_s * f[1][i] + a2_s * f[2][i] for i in range(n)]

    G = mp_data["G_tot"]
    b_vec = mp_data["b"]
    Gv = [sum((G[i][j] * v[j] for j in range(n)), mp.mpf(0)) for i in range(n)]
    vGv = sum((v[i] * Gv[i] for i in range(n)), mp.mpf(0))
    vGc = sum((c_base[i] * Gv[i] for i in range(n)), mp.mpf(0))
    bv = sum((b_vec[i] * v[i] for i in range(n)), mp.mpf(0))

    a3_opt = -(vGc - bv) / vGv
    a1_opt = a1_0 + a1_s * a3_opt
    a2_opt = a2_0 + a2_s * a3_opt
    c_opt = [c_base[i] + a3_opt * v[i] for i in range(n)]
    return c_opt, {"a1": float(a1_opt), "a2": float(a2_opt), "a3": float(a3_opt)}


def _affine_lock_mp(c0: List[mp.mpf], n: int) -> List[mp.mpf]:
    """Apply exact Lean-formalized affineLock: c = c0 + (2 - D_N(0)(c0)) * w^{(N)}."""
    d0 = sum(c0, mp.mpf(0))
    gap = mp.mpf(2) - d0
    c = list(c0)
    c[0] += gap * (mp.mpf(-1) / (n - 1))
    c[n - 1] += gap * (mp.mpf(n) / (n - 1))
    return c


def _family_d_decoupled_affine_lock_mp(
    n: int, mu: List[int], mp_data: Dict[str, Any]
) -> Tuple[List[mp.mpf], Dict[str, float]]:
    """Family D: Decoupled affineLock polynomial c^{(0)} = -mu(k)(1-u)(1 + a1*u + a2*u^2).

    Enforces D_N(1) = 0 on c^{(0)} (a1 = -(d1[0] + d1[2]*a2)/d1[1]), applies the
    2-sparse corrector w^{(N)} via affineLock to enforce D_N(0) = 2 without
    distorting low-k weights, and chooses a2 in closed form to minimize E_N.
    """
    lnN = mp.log(n)
    f: List[List[mp.mpf]] = [[mp.mpf(0)] * n for _ in range(3)]
    for k in range(1, n + 1):
        if mu[k] != 0:
            u = mp.log(k) / lnN
            base = mp.mpf(-mu[k]) * (1 - u)
            uk = mp.mpf(1)
            for m in range(3):
                f[m][k - 1] = base * uk
                uk *= u

    d1 = [sum((f[m][k - 1] / k for k in range(1, n + 1)), mp.mpf(0)) for m in range(3)]
    a1_0 = -d1[0] / d1[1]
    a1_s = -d1[2] / d1[1]

    c0_base = [f[0][i] + a1_0 * f[1][i] for i in range(n)]
    v0 = [f[2][i] + a1_s * f[1][i] for i in range(n)]

    # affineLock is affine in c0: affineLock(c0_base + a2 * v0) = affineLock(c0_base) + a2 * (v0 - D0(v0)*w^{(N)})
    c_base = _affine_lock_mp(c0_base, n)
    d0_v0 = sum(v0, mp.mpf(0))
    v = list(v0)
    v[0] -= d0_v0 * (mp.mpf(-1) / (n - 1))
    v[n - 1] -= d0_v0 * (mp.mpf(n) / (n - 1))

    G = mp_data["G_tot"]
    b_vec = mp_data["b"]
    Gv = [sum((G[i][j] * v[j] for j in range(n)), mp.mpf(0)) for i in range(n)]
    vGv = sum((v[i] * Gv[i] for i in range(n)), mp.mpf(0))
    vGc = sum((c_base[i] * Gv[i] for i in range(n)), mp.mpf(0))
    bv = sum((b_vec[i] * v[i] for i in range(n)), mp.mpf(0))

    a2_opt = -(vGc - bv) / vGv
    a1_opt = a1_0 + a1_s * a2_opt
    c_opt = [c_base[i] + a2_opt * v[i] for i in range(n)]
    return c_opt, {"a1": float(a1_opt), "a2": float(a2_opt), "D0_bulk": float(sum(c0_base, mp.mpf(0)) + a2_opt * d0_v0)}


def _family_e_selberg_sieve_affine_lock_mp(
    n: int, mu: List[int]
) -> Tuple[List[mp.mpf], Dict[str, float]]:
    """Family E: Closed-form Selberg sieve envelope -mu(k)(1-u)^2(1 + a1*u) + affineLock."""
    lnN = mp.log(n)
    g0 = [mp.mpf(0)] * n
    g1 = [mp.mpf(0)] * n
    for k in range(1, n + 1):
        if mu[k] != 0:
            u = mp.log(k) / lnN
            base = mp.mpf(-mu[k]) * ((1 - u) ** 2)
            g0[k - 1] = base
            g1[k - 1] = base * u

    d1_0 = sum((g0[k - 1] / k for k in range(1, n + 1)), mp.mpf(0))
    d1_1 = sum((g1[k - 1] / k for k in range(1, n + 1)), mp.mpf(0))
    a1 = -d1_0 / d1_1
    c0 = [g0[i] + a1 * g1[i] for i in range(n)]
    c = _affine_lock_mp(c0, n)
    return c, {"a1": float(a1), "D0_bulk": float(sum(c0, mp.mpf(0)))}


def analyze_cotangent_reciprocity_and_gcd_channels(
    n_targets: List[int], mu: List[int], mp_data: Dict[str, Any]
) -> List[Dict[str, Any]]:
    """Decompose Q_N^{(cot)}(c^{(N)}) for Family D across GCD channels and Bettin-Conrey reciprocity."""
    mp.mp.dps = MP_DPS
    G_ct = mp_data["G_cot"]
    G_sm = mp_data["G_smooth"]
    out_rows: List[Dict[str, Any]] = []

    for n in n_targets:
        c_vec, _ = _family_d_decoupled_affine_lock_mp(n, mu, mp_data)
        gcd_channels = [mp.mpf(0)] * (n + 1)
        q_main = mp.mpf(0)
        q_rem = mp.mpf(0)
        q_smooth = mp.mpf(0)
        q_tot_check = mp.mpf(0)

        for i in range(n):
            ci = c_vec[i]
            if ci == 0:
                continue
            j_idx = i + 1
            for j in range(n):
                cj = c_vec[j]
                if cj == 0:
                    continue
                k_idx = j + 1
                g = math.gcd(j_idx, k_idx)
                a, b = j_idx // g, k_idx // g
                g_ct_ij = G_ct[i][j]
                term_ct = ci * cj * g_ct_ij
                gcd_channels[g] += term_ct
                q_tot_check += term_ct
                q_smooth += ci * cj * G_sm[i][j]

                if a == b:
                    g_main = mp.mpf(0)
                else:
                    lo_ab, hi_ab = (a, b) if a < b else (b, a)
                    g_main = (
                        mp.mpf(hi_ab - lo_ab) * mp.log(mp.mpf(hi_ab) / lo_ab)
                    ) / (2 * mp.mpf(g) * a * b)
                g_rem = g_ct_ij - g_main
                q_main += ci * cj * g_main
                q_rem += ci * cj * g_rem

        d1_val = gcd_channels[1]
        d_ge_2_val = sum(gcd_channels[2:], mp.mpf(0))
        gcd_err = abs((d1_val + d_ge_2_val) - q_tot_check)
        recip_err = abs((q_main + q_rem) - q_tot_check)

        out_rows.append(
            {
                "N": n,
                "Q_cot_total": float(q_tot_check),
                "Q_cot_d1_coprime": float(d1_val),
                "Q_cot_d_ge_2_harmonics": float(d_ge_2_val),
                "Q_cot_d2": float(gcd_channels[2]) if n >= 2 else 0.0,
                "Q_cot_d3": float(gcd_channels[3]) if n >= 3 else 0.0,
                "Q_cot_d4": float(gcd_channels[4]) if n >= 4 else 0.0,
                "Q_cot_d5": float(gcd_channels[5]) if n >= 5 else 0.0,
                "Q_cot_main_smooth_canceling": float(q_main),
                "Q_cot_reciprocity_remainder": float(q_rem),
                "Q_smooth_plus_main": float(q_smooth + q_main),
                "gcd_sum_check_err": float(gcd_err),
                "recip_sum_check_err": float(recip_err),
            }
        )
    return out_rows


def _evaluate_candidate(
    name: str,
    c_mp: List[mp.mpf],
    n: int,
    mp_data: Dict[str, Any],
    arb_data: Dict[str, Any],
    is_prime: List[bool],
    extra: Dict[str, Any] | None = None,
) -> Dict[str, Any]:
    mp.mp.dps = MP_DPS
    G_tot = mp_data["G_tot"]
    G_sm = mp_data["G_smooth"]
    G_ct = mp_data["G_cot"]
    b_vec = mp_data["b"]

    d0_mp = sum(c_mp, mp.mpf(0))
    d1_mp = sum((c_mp[k - 1] / k for k in range(1, n + 1)), mp.mpf(0))
    bt_c = sum((b_vec[i] * c_mp[i] for i in range(n)), mp.mpf(0))

    q_sm = mp.mpf(0)
    q_ct = mp.mpf(0)
    q_tot = mp.mpf(0)
    cot_unit = mp.mpf(0)
    cot_pp = mp.mpf(0)
    cot_pc = mp.mpf(0)
    cot_cc = mp.mpf(0)

    for i in range(n):
        ci = c_mp[i]
        if ci == 0:
            continue
        k1 = i + 1
        row_sm = mp.mpf(0)
        row_ct = mp.mpf(0)
        row_tot = mp.mpf(0)
        for j in range(n):
            cj = c_mp[j]
            if cj == 0:
                continue
            row_sm += G_sm[i][j] * cj
            g_ct_ij = G_ct[i][j]
            row_ct += g_ct_ij * cj
            row_tot += G_tot[i][j] * cj

            k2 = j + 1
            term = ci * cj * g_ct_ij
            if k1 == 1 or k2 == 1:
                cot_unit += term
            elif is_prime[k1] and is_prime[k2]:
                cot_pp += term
            elif is_prime[k1] or is_prime[k2]:
                cot_pc += term
            else:
                cot_cc += term
        q_sm += ci * row_sm
        q_ct += ci * row_ct
        q_tot += ci * row_tot

    e_full = 1 - 2 * bt_c + q_sm + q_ct
    e_pure_cot = 1 + q_ct
    id_err_mp = abs(e_full - e_pure_cot)
    tot_err_mp = abs(e_full - (1 - 2 * bt_c + q_tot))

    # 192-bit flint.arb verification of the same vector
    with ctx.workprec(ARB_BITS):
        c_arb = [arb(mp.nstr(v, 65)) for v in c_mp]
        bt_arb = sum((arb_data["b"][i] * c_arb[i] for i in range(n)), arb(0))
        q_sm_a = arb(0)
        q_ct_a = arb(0)
        for i in range(n):
            ci = c_arb[i]
            rs = arb(0)
            rc = arb(0)
            for j in range(n):
                cj = c_arb[j]
                rs += arb_data["G_smooth"][i, j] * cj
                rc += arb_data["G_cot"][i, j] * cj
            q_sm_a += ci * rs
            q_ct_a += ci * rc
        e_full_a = 1 - 2 * bt_arb + q_sm_a + q_ct_a
        e_cot_a = 1 + q_ct_a
        diff_a = e_full_a - e_cot_a
        arb_contains_zero = diff_a.contains(0)
        arb_diff_abs_upper = float(abs(diff_a).upper())

    ln_n = float(mp.log(n))
    res = {
        "family": name,
        "N": n,
        "D0": float(d0_mp),
        "D1_abs": float(abs(d1_mp)),
        "E_N": float(e_full),
        "Q_cot": float(q_ct),
        "E_N_times_lnN": float(e_full) * ln_n,
        "identity_err_mp_80dps": float(id_err_mp),
        "total_split_err_mp_80dps": float(tot_err_mp),
        "arb192_diff_contains_zero": bool(arb_contains_zero),
        "arb192_diff_upper": arb_diff_abs_upper,
        "cotangent_decomposition": {
            "unit": float(cot_unit),
            "prime_prime": float(cot_pp),
            "prime_comp": float(cot_pc),
            "comp_comp": float(cot_cc),
            "sum_check_err": float(abs((cot_unit + cot_pp + cot_pc + cot_cc) - q_ct)),
        },
    }
    if extra:
        res["params"] = extra
    return res


def main() -> None:
    t0 = time.perf_counter()
    print("=" * 80)
    print("TRACK 2 (STRATEGY 1): CONSTRUCTIVE AFFINE-LOCKED MOLLIFIER FAMILIES ON A_N")
    print("=" * 80)

    mu = _mobius_sieve(MAX_N)
    is_prime = _is_prime_list(MAX_N)
    mp_data = _build_mp_matrices(MAX_N)
    arb_data = _build_vasyunin_arb_matrices(MAX_N, ARB_BITS)

    rows: List[Dict[str, Any]] = []
    max_mp_id_err = 0.0
    all_arb_contain_zero = True

    for n in N_LIST:
        n_rows: List[Dict[str, Any]] = []
        for alpha in ALPHAS:
            c0 = _sbd_base_mp(n, alpha, mu)
            ca = _family_a_endpoint_mp(c0, n)
            cb = _family_b_smooth_proj_mp(c0, n)
            ra = _evaluate_candidate(f"family_A_endpoint_alpha_{alpha}", ca, n, mp_data, arb_data, is_prime, {"alpha": alpha})
            rb = _evaluate_candidate(f"family_B_smooth_proj_alpha_{alpha}", cb, n, mp_data, arb_data, is_prime, {"alpha": alpha})
            n_rows.extend([ra, rb])

        cc, c_params = _family_c_cubic_mp(n, mu, mp_data)
        rc = _evaluate_candidate("family_C_cubic_selberg", cc, n, mp_data, arb_data, is_prime, c_params)
        n_rows.append(rc)

        cd, d_params = _family_d_decoupled_affine_lock_mp(n, mu, mp_data)
        rd = _evaluate_candidate("family_D_decoupled_affine_lock", cd, n, mp_data, arb_data, is_prime, d_params)
        n_rows.append(rd)

        ce, e_params = _family_e_selberg_sieve_affine_lock_mp(n, mu)
        re = _evaluate_candidate("family_E_selberg_sieve_affine_lock", ce, n, mp_data, arb_data, is_prime, e_params)
        n_rows.append(re)

        rows.extend(n_rows)
        for r in n_rows:
            max_mp_id_err = max(max_mp_id_err, r["identity_err_mp_80dps"])
            all_arb_contain_zero = all_arb_contain_zero and r["arb192_diff_contains_zero"]

        best_n = min(n_rows, key=lambda x: x["E_N"])
        print(
            f"  N={n:3d} | best={best_n['family']:35s} | E_N={best_n['E_N']:.6f} "
            f"| Q_cot={best_n['Q_cot']:.6f} | E_N*lnN={best_n['E_N_times_lnN']:.5f} "
            f"| id_err={best_n['identity_err_mp_80dps']:.2e}"
        )

    recip_rows = analyze_cotangent_reciprocity_and_gcd_channels([20, 50, 100, 150, 200], mu, mp_data)
    print("\nFamily D GCD & Bettin-Conrey Reciprocity Decomposition:")
    for rr in recip_rows:
        print(
            f"  N={rr['N']:3d} | Q_cot={rr['Q_cot_total']:+.6f} | d=1:{rr['Q_cot_d1_coprime']:+.6f} "
            f"| d>=2:{rr['Q_cot_d_ge_2_harmonics']:+.6f} | main:{rr['Q_cot_main_smooth_canceling']:+.6f} "
            f"| rem:{rr['Q_cot_reciprocity_remainder']:+.6f}"
        )

    elapsed = time.perf_counter() - t0
    out = {
        "governance": {
            "NO_RH_PROOF": True,
            "FULL_POINT_L1": "NOT_ISSUED",
            "PUBLICATION_STATUS": "HOLD",
        },
        "precision": {"mp_dps": MP_DPS, "arb_bits": ARB_BITS},
        "N_list": N_LIST,
        "max_identity_err_mp_80dps": max_mp_id_err,
        "all_arb192_contain_zero": all_arb_contain_zero,
        "results": rows,
        "family_D_reciprocity_and_gcd_decomposition": recip_rows,
        "elapsed_seconds": round(elapsed, 3),
    }
    OUT_JSON.write_text(json.dumps(out, indent=2), encoding="utf-8")
    print(f"\nMax 80-dps identity err: {max_mp_id_err:.3e}, all_arb192_contain_zero={all_arb_contain_zero}")
    print(f"Saved results in {elapsed:.2f}s to: {OUT_JSON}")


if __name__ == "__main__":
    main()
