#!/usr/bin/env python3
"""
Layer C High-Precision Numerical Frontier Lab (80-digit mpmath arithmetic, 50-digit JSON outputs).

Computes exact Báez–Duarte dipole energies for N in {4, 8, 12, 16, 24, 32, 48, 64} on both:
  1. The exact unconstrained KKT global optimizer c_opt^(N) on A_N
  2. The canonical projected mollified Möbius sequence cCandidateMobius N on A_N

Verifies the Lean 4 Stage G.18 identities from UpstreamPR_7C & UpstreamPR_7D to >70 digits:
  - QCot(h, N) = D_N + O_N  (diagonal + off-diagonal energy split)
  - SCot(c, N) = -pi * c_1 * L_cot - P_N  (global anchor-drive cancellation + pure plaque form)
  - SCot(c, N) = 2 * pi * L_cot - (D_N + O_N)
  - At N = 4: alpha_1 = 2/3, alpha_2 = (5 - sqrt(3)) / 12, SCot = ((19 + sqrt(3)) / 72) * pi

Epistemic Status: NO_RH_PROOF = TRUE.
"""

from __future__ import annotations

import json
import math
import pathlib
from typing import Dict, List

import mpmath as mp

BASE_DIR = pathlib.Path(__file__).resolve().parent
mp.mp.dps = 80


def fmt(val: mp.mpf, digits: int = 50) -> str:
    return mp.nstr(val, digits)


def mobius_sieve(n_max: int) -> List[int]:
    mu = [0] * (n_max + 1)
    mu[1] = 1
    primes: List[int] = []
    is_comp = [False] * (n_max + 1)
    for i in range(2, n_max + 1):
        if not is_comp[i]:
            primes.append(i)
            mu[i] = -1
        for p in primes:
            if i * p > n_max:
                break
            is_comp[i * p] = True
            if i % p == 0:
                mu[i * p] = 0
                break
            mu[i * p] = -mu[i]
    return mu


def precompute_cot_table(n_max: int) -> Dict[int, List[mp.mpf]]:
    """Precompute cot(pi * m / a) for 2 <= a <= n_max, 1 <= m < a at 80 digits."""
    table: Dict[int, List[mp.mpf]] = {}
    for a in range(2, n_max + 1):
        row = [mp.mpf(0)] * a
        for m in range(1, a):
            row[m] = mp.cot(mp.pi * mp.mpf(m) / mp.mpf(a))
        table[a] = row
    return table


def vasyunin_cot_sum(a: int, b: int, cot_table: Dict[int, List[mp.mpf]]) -> mp.mpf:
    if a <= 1:
        return mp.mpf(0)
    row = cot_table[a]
    acc = mp.mpf(0)
    for m in range(1, a):
        rem = (m * b) % a
        if rem != 0:
            acc += (mp.mpf(rem) / mp.mpf(a)) * row[m]
    return acc


def build_kernels(n_max: int):
    cot_table = precompute_cot_table(n_max + 2)
    delta_cot = [mp.mpf(0)] * (n_max + 3)
    for k in range(1, n_max + 3):
        delta_cot[k] = vasyunin_cot_sum(k, 2, cot_table) - vasyunin_cot_sum(k, 1, cot_table)

    # K(j, k) = j * k * vasyuninGCot(j, k) = -(pi / 2) * (V(j, k) + V(k, j))
    k_mat: Dict[tuple[int, int], mp.mpf] = {}
    for j in range(1, n_max + 1):
        for k in range(j, n_max + 1):
            if j == k:
                val = mp.mpf(0)
            else:
                v_jk = vasyunin_cot_sum(j, k, cot_table)
                v_kj = vasyunin_cot_sum(k, j, cot_table)
                val = -(mp.pi / 2) * (v_jk + v_kj)
            k_mat[(j, k)] = val
            k_mat[(k, j)] = val

    def k_cot(j: int, k: int) -> mp.mpf:
        return k_mat[(j, k)]

    m_max = n_max - 2
    plaque = [[mp.mpf(0)] * (m_max + 1) for _ in range(m_max + 1)]
    gram = [[mp.mpf(0)] * (m_max + 1) for _ in range(m_max + 1)]
    for a in range(1, m_max + 1):
        da = delta_cot[a + 2] - delta_cot[a + 1]
        for b in range(a, m_max + 1):
            db = delta_cot[b + 2] - delta_cot[b + 1]
            p_ab = (
                k_cot(a + 1, b + 1)
                - k_cot(a + 1, b + 2)
                - k_cot(a + 2, b + 1)
                + k_cot(a + 2, b + 2)
            )
            g_ab = (mp.pi / 2) * (da + db) + p_ab
            plaque[a][b] = plaque[b][a] = p_ab
            gram[a][b] = gram[b][a] = g_ab
    return delta_cot, plaque, gram


def project_affine_mobius(N: int, mu: List[int]) -> List[mp.mpf]:
    """Exact 80-digit cCandidateMobius N = projectAffine (mollifiedMobius N) N (1-indexed)."""
    u = [mp.mpf(0)] * (N + 1)
    for k in range(1, N + 1):
        u[k] = -mp.mpf(mu[k]) * (1 - mp.mpf(k) / mp.mpf(N)) ** 2
    h_sum = sum(mp.mpf(1) / mp.mpf(k) for k in range(1, N + 1))
    s2_sum = sum(mp.mpf(1) / mp.mpf(k * k) for k in range(1, N + 1))
    delta_det = mp.mpf(N) * s2_sum - h_sum ** 2
    sum_u_div_k = sum(u[k] / mp.mpf(k) for k in range(1, N + 1))
    sum_u = sum(u[k] for k in range(1, N + 1))
    lam1 = (mp.mpf(N) * sum_u_div_k - h_sum * (sum_u - 2)) / delta_det
    lam0 = (s2_sum * (sum_u - 2) - h_sum * sum_u_div_k) / delta_det
    c = [mp.mpf(0)] * (N + 1)
    for k in range(1, N + 1):
        c[k] = u[k] - lam1 / mp.mpf(k) - lam0
    return c


def dipole_coords_from_c(c: List[mp.mpf], N: int) -> List[mp.mpf]:
    """1-indexed alpha_m = dipoleCoord c N m = sum_{j=m+2}^N c_j / j for m in 1..N-2."""
    alpha = [mp.mpf(0)] * (N - 1)
    running = mp.mpf(0)
    for m in range(N - 2, 0, -1):
        running += c[m + 2] / mp.mpf(m + 2)
        alpha[m] = running
    return alpha


def c_from_dipole_coords(alpha: List[mp.mpf], N: int) -> List[mp.mpf]:
    """Reconstruct affine vector c in A_N from alpha_1..alpha_{N-2} + cBaseAnchor."""
    c = [mp.mpf(0)] * (N + 1)
    # c_base = (-2, 4, 0, ...), cumulativeDipole m k = 1_{k=1} - 2_{k=2} - (m+1)_{k=m+1} + (m+2)_{k=m+2}
    sum_alpha = sum(alpha[m] for m in range(1, N - 1))
    c[1] = -2 + sum_alpha
    c[2] = 4 - 2 * sum_alpha - (2 * alpha[1] if N >= 3 else mp.mpf(0))
    for k in range(3, N + 1):
        val = mp.mpf(0)
        if k - 1 <= N - 2:
            val -= mp.mpf(k) * alpha[k - 1]
        if k - 2 >= 1:
            val += mp.mpf(k) * alpha[k - 2]
        c[k] = val
    return c


def solve_kkt_alpha(N: int, delta_cot: List[mp.mpf], gram: List[List[mp.mpf]]) -> List[mp.mpf]:
    m_dim = N - 2
    a_mat = mp.matrix([[gram[a + 1][b + 1] for b in range(m_dim)] for a in range(m_dim)])
    rhs = mp.matrix([[mp.pi * (delta_cot[a + 3] - delta_cot[a + 2])] for a in range(m_dim)])
    sol = mp.lu_solve(a_mat, rhs)
    return [mp.mpf(0)] + [sol[i, 0] for i in range(m_dim)]


def evaluate_profile(
    label: str,
    N: int,
    c: List[mp.mpf],
    alpha: List[mp.mpf],
    delta_cot: List[mp.mpf],
    plaque: List[List[mp.mpf]],
    gram: List[List[mp.mpf]],
) -> Dict[str, object]:
    m_dim = N - 2
    d1_err = abs(sum(c[k] / mp.mpf(k) for k in range(1, N + 1)))
    d0_err = abs(sum(c[k] for k in range(1, N + 1)) - 2)
    assert d1_err < mp.mpf("1e-70"), f"{label} N={N} D1 err {d1_err}"
    assert d0_err < mp.mpf("1e-70"), f"{label} N={N} D0 err {d0_err}"

    l_cot = sum(alpha[m] * (delta_cot[m + 2] - delta_cot[m + 1]) for m in range(1, m_dim + 1))
    diag_e = sum((alpha[m] ** 2) * gram[m][m] for m in range(1, m_dim + 1))
    off_diag_e = mp.mpf(0)
    plaque_e = mp.mpf(0)
    q_cot = mp.mpf(0)
    for a in range(1, m_dim + 1):
        aa = alpha[a]
        for b in range(1, m_dim + 1):
            ab = aa * alpha[b]
            term_g = ab * gram[a][b]
            q_cot += term_g
            if a != b:
                off_diag_e += term_g
            plaque_e += ab * plaque[a][b]

    s_cot = 2 * mp.pi * l_cot - q_cot
    l2_dist_sq = 1 - s_cot
    anchor_drive = -mp.pi * c[1] * l_cot
    s_cot_plaque = anchor_drive - plaque_e

    assert abs(q_cot - (diag_e + off_diag_e)) < mp.mpf("1e-68"), "QCot != D + O"
    assert abs(s_cot - s_cot_plaque) < mp.mpf("1e-68"), "SCot != anchor_drive - P"
    assert l2_dist_sq > 0, "L2 dist sq must stay positive"

    ratio_abs_o_over_d = abs(off_diag_e) / diag_e if diag_e != 0 else mp.mpf(0)
    return {
        "N": N,
        "c1": fmt(c[1]),
        "linear_cot_drive_L": fmt(l_cot),
        "diag_energy_D": fmt(diag_e),
        "off_diag_energy_O": fmt(off_diag_e),
        "q_cot_total": fmt(q_cot),
        "pure_plaque_energy_P": fmt(plaque_e),
        "anchor_drive_term": fmt(anchor_drive),
        "s_cot": fmt(s_cot),
        "l2_dist_sq": fmt(l2_dist_sq),
        "abs_off_diag_over_diag_ratio": fmt(ratio_abs_o_over_d),
        "diag_float": float(diag_e),
        "neg_off_diag_float": float(-off_diag_e),
        "q_cot_float": float(q_cot),
        "plaque_float": float(plaque_e),
        "anchor_drive_float": float(anchor_drive),
        "l2_dist_sq_float": float(l2_dist_sq),
        "ratio_float": float(ratio_abs_o_over_d),
        "identity_err_q_split": fmt(abs(q_cot - (diag_e + off_diag_e)), 10),
        "identity_err_anchor_cancel": fmt(abs(s_cot - s_cot_plaque), 10),
    }


def main() -> None:
    ns = [4, 8, 12, 16, 24, 32, 48, 64]
    n_max = max(ns)
    delta_cot, plaque, gram = build_kernels(n_max)
    mu = mobius_sieve(n_max)

    # Exact N=4 KKT cross-check against Lean theorems (UpstreamPR_4G & 4L)
    alpha4 = solve_kkt_alpha(4, delta_cot, gram)
    err_a1 = abs(alpha4[1] - mp.mpf(2) / 3)
    err_a2 = abs(alpha4[2] - (5 - mp.sqrt(3)) / 12)
    assert err_a1 < mp.mpf("1e-70"), f"N=4 alpha1 err {err_a1}"
    assert err_a2 < mp.mpf("1e-70"), f"N=4 alpha2 err {err_a2}"

    kkt_rows = []
    mobius_rows = []
    for N in ns:
        a_opt = solve_kkt_alpha(N, delta_cot, gram)
        c_opt = c_from_dipole_coords(a_opt, N)
        kkt_rows.append(evaluate_profile("KKT", N, c_opt, a_opt, delta_cot, plaque, gram))

        c_mob = project_affine_mobius(N, mu)
        a_mob = dipole_coords_from_c(c_mob, N)
        mobius_rows.append(evaluate_profile("Mobius", N, c_mob, a_mob, delta_cot, plaque, gram))

    payload = {
        "meta": {
            "precision_dps_internal": 80,
            "reported_digits": 50,
            "epistemic_invariant": "NO_RH_PROOF = TRUE",
            "n_values": ns,
            "n4_kkt_exact_check": {
                "alpha1_err": fmt(err_a1, 10),
                "alpha2_err": fmt(err_a2, 10),
            },
        },
        "kkt_optimizer": kkt_rows,
        "mollified_mobius": mobius_rows,
    }
    out_path = BASE_DIR / "layer_c_dipole_asymptotic_results.json"
    out_path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")
    print(f"Wrote {out_path} ({len(kkt_rows)} KKT rows, {len(mobius_rows)} Mobius rows)")
    for row in kkt_rows:
        print(
            f"  [KKT    N={row['N']:2d}] D={row['diag_float']:.6f}  -O={row['neg_off_diag_float']:.6f}  "
            f"Q=D+O={row['q_cot_float']:.6f}  |O|/D={row['ratio_float']:.6f}  "
            f"P={row['plaque_float']:.6f}  L2^2={row['l2_dist_sq_float']:.6f}"
        )
    for row in mobius_rows:
        print(
            f"  [Mobius N={row['N']:2d}] D={row['diag_float']:.6f}  -O={row['neg_off_diag_float']:.6f}  "
            f"Q=D+O={row['q_cot_float']:.6f}  |O|/D={row['ratio_float']:.6f}  "
            f"P={row['plaque_float']:.6f}  L2^2={row['l2_dist_sq_float']:.6f}"
        )


if __name__ == "__main__":
    main()
