"""85-digit palindromic period & prime-harmonic cell verification lab.

Computes and verifies full fundamental periods A_c(0), A_c(1), ..., A_c(L_N - 1) for:
  - N = 4 (L_4 = lcm(1,2,3,4) = 12) at the exact Dirichlet optimum cDirichletOptFour:
      c* = (-1, 1 - 2/(3*sqrt(3)), 2/sqrt(3), 2 - 4/(3*sqrt(3)))
  - N = 5 (L_5 = 60) and N = 6 (L_6 = 60) for:
      (a) the Gram-optimal Dirichlet-anchored vector on A_N^{dir}, and
      (b) the Selberg-damped Mobius simplex profile on A_N^{dir}.

Verifies to 85-digit precision:
  1. A_c(1) = 0 (top-half annihilation on x in (1/2, 1]).
  2. A_c(2) = c_2 - 1 and A_c(3) = c_2 + c_3 - 2 (with A_c(3) - A_c(2) = c_3 - 1).
  3. max_{0 <= m < L_N} |A_c(L_N - 1 - m) + A_c(m)| < 1e-80 (modularCellResidual_palindromic_neg).
  4. |sum_{m=0}^{L_N-1} A_c(m)| < 1e-80 (sum_Ico_modularCellResidual_eq_zero).

Under NO_RH_PROOF = TRUE, all computations certify finite-N arithmetic identities.
"""

from __future__ import annotations

import json
import math
import pathlib
from typing import Dict, List

import mpmath as mp

from layer_c_dirichlet_locked_plaque_lab import (
    ONE,
    PI,
    ROOT_DIR,
    TWO,
    ZERO,
    build_unweighted_k_cot,
    eta_to_c,
    lu_solve,
    vasyunin_cot_sum,
)
from layer_c_simplex_test_families_lab import dirichlet_project_raw, mobius_sieve

mp.mp.dps = 85


def solve_dirichlet_opt_c(N: int) -> List[mp.mpf]:
    """Solve the Dirichlet-anchored KKT system at truncation degree N."""
    kmat = build_unweighted_k_cot(N)
    delta = [ZERO] * (N + 1)
    for k in range(1, N + 1):
        delta[k] = vasyunin_cot_sum(k, 2) - vasyunin_cot_sum(k, 1)
    m_dim = N - 2
    ell = [delta[a + 2] - delta[a + 1] for a in range(1, m_dim + 1)]
    kkt_dir = [[ZERO for _ in range(m_dim + 1)] for _ in range(m_dim + 1)]
    for a in range(1, m_dim + 1):
        for b in range(1, m_dim + 1):
            kkt_dir[a - 1][b - 1] = (
                kmat[a + 1][b + 1] - kmat[a + 1][b + 2] - kmat[a + 2][b + 1] + kmat[a + 2][b + 2]
            )
        kkt_dir[a - 1][m_dim] = ONE
        kkt_dir[m_dim][a - 1] = ONE
    rhs_dir = [(PI / TWO) * ell[i] for i in range(m_dim)] + [ONE]
    sol_dir = lu_solve(kkt_dir, rhs_dir)
    return eta_to_c(sol_dir[:m_dim], N)


def lcm_one_to(n: int) -> int:
    L = 1
    for k in range(1, n + 1):
        L = math.lcm(L, k)
    return L


def modular_cell_residual(c: List[mp.mpf], N: int, n: int) -> mp.mpf:
    """Compute A_c(n) = 1 - sum_{k=1}^N c_k * fract(n / k) at 85-digit precision."""
    acc = ONE
    for k in range(1, N + 1):
        frac_part = mp.frac(mp.mpf(n) / mp.mpf(k))
        acc -= c[k] * frac_part
    return acc


def floor_cell_residual(c: List[mp.mpf], N: int, n: int) -> mp.mpf:
    """Compute D_cell(n) = 1 + sum_{k=1}^N c_k * (n // k) at 85-digit precision."""
    acc = ONE
    for k in range(1, N + 1):
        acc += c[k] * mp.mpf(n // k)
    return acc


def harmonic_cell_l2_partial_sum(c: List[mp.mpf], N: int, M: int) -> mp.mpf:
    """Compute sum_{n=1}^M D_cell(n)^2 / (n * (n + 1)) at 85-digit precision."""
    acc = ZERO
    for n in range(1, M + 1):
        d = floor_cell_residual(c, N, n)
        acc += (d * d) / mp.mpf(n * (n + 1))
    return acc


def verify_profile(name: str, N: int, c: List[mp.mpf]) -> Dict:
    L = lcm_one_to(N)
    D1 = sum(c[k] / mp.mpf(k) for k in range(1, N + 1))
    D0 = sum(c[k] for k in range(1, N + 1))
    A_vals = [modular_cell_residual(c, N, m) for m in range(L)]
    D_vals = [floor_cell_residual(c, N, m) for m in range(L)]

    max_dual_err = max(abs(A_vals[m] - D_vals[m]) for m in range(L))
    max_pal_err = max(abs(A_vals[L - 1 - m] + A_vals[m]) for m in range(L))
    period_sum = abs(sum(A_vals, ZERO))
    top_half_err = abs(A_vals[1])
    dyadic_err = abs(A_vals[2] - (c[2] - ONE))
    ternary_err = abs(A_vals[3] - (c[2] + c[3] - mp.mpf(2)))
    jump3_err = abs((A_vals[3] - A_vals[2]) - (c[3] - ONE))
    l2_m2 = harmonic_cell_l2_partial_sum(c, N, 2)
    l2_m3 = harmonic_cell_l2_partial_sum(c, N, 3)
    l2_head = harmonic_cell_l2_partial_sum(c, N, L - 1)
    l2_m2_err = abs(l2_m2 - ((c[2] - ONE) ** 2) / mp.mpf(6))
    l2_m3_err = abs(
        l2_m3
        - (
            ((c[2] - ONE) ** 2) / mp.mpf(6)
            + ((c[2] + c[3] - mp.mpf(2)) ** 2) / mp.mpf(12)
        )
    )

    return {
        "profile": name,
        "N": N,
        "L": L,
        "c": [mp.nstr(c[k], 30) for k in range(1, N + 1)],
        "D1_abs_err": mp.nstr(abs(D1), 15),
        "D0_sub_2_abs_err": mp.nstr(abs(D0 - mp.mpf(2)), 15),
        "top_half_A1_abs_err": mp.nstr(top_half_err, 15),
        "dyadic_A2_abs_err": mp.nstr(dyadic_err, 15),
        "ternary_A3_abs_err": mp.nstr(ternary_err, 15),
        "prime3_jump_abs_err": mp.nstr(jump3_err, 15),
        "l2_partial_M2": mp.nstr(l2_m2, 20),
        "l2_partial_M3": mp.nstr(l2_m3, 20),
        "l2_partial_head_L_sub_1": mp.nstr(l2_head, 20),
        "l2_partial_M2_abs_err": mp.nstr(l2_m2_err, 15),
        "l2_partial_M3_abs_err": mp.nstr(l2_m3_err, 15),
        "max_floor_mod_duality_abs_err": mp.nstr(max_dual_err, 15),
        "max_palindromic_reflection_abs_err": mp.nstr(max_pal_err, 15),
        "period_sum_abs_err": mp.nstr(period_sum, 15),
        "A_period_18digits": [float(mp.nstr(v, 18)) for v in A_vals],
    }


def selberg_dirichlet_c(N: int) -> List[mp.mpf]:
    mu = mobius_sieve(N)
    c_raw = [ZERO] * (N + 1)
    denom = mp.log(mp.mpf(N + 1))
    for k in range(2, N + 1):
        c_raw[k] = -mp.mpf(mu[k]) * (ONE - mp.log(mp.mpf(k)) / denom)
    return dirichlet_project_raw(c_raw, N)


def exact_n4_dirichlet_c() -> List[mp.mpf]:
    sq3 = mp.sqrt(mp.mpf(3))
    return [
        ZERO,
        -ONE,
        ONE - mp.mpf(2) / (mp.mpf(3) * sq3),
        mp.mpf(2) / sq3,
        mp.mpf(2) - mp.mpf(4) / (mp.mpf(3) * sq3),
    ]


def main() -> int:
    records = []
    # N = 4 exact closed-form Dirichlet optimum
    records.append(verify_profile("N4_exact_dirichlet_opt", 4, exact_n4_dirichlet_c()))

    # N = 5 and N = 6: Gram-optimal Dirichlet-anchored + Selberg-damped Mobius simplex
    for N in (5, 6):
        c_opt = solve_dirichlet_opt_c(N)
        records.append(verify_profile(f"N{N}_gram_dirichlet_opt", N, c_opt))
        c_sel = selberg_dirichlet_c(N)
        records.append(verify_profile(f"N{N}_selberg_mobius_simplex", N, c_sel))

    max_pal = max(mp.mpf(r["max_palindromic_reflection_abs_err"]) for r in records)
    max_sum = max(mp.mpf(r["period_sum_abs_err"]) for r in records)
    max_dual = max(mp.mpf(r["max_floor_mod_duality_abs_err"]) for r in records)
    max_quad = max(mp.mpf(r["l2_partial_M3_abs_err"]) for r in records)
    assert max_pal < mp.mpf("1e-80"), f"Palindromic error too large: {max_pal}"
    assert max_sum < mp.mpf("1e-80"), f"Period sum error too large: {max_sum}"
    assert max_dual < mp.mpf("1e-80"), f"Duality error too large: {max_dual}"
    assert max_quad < mp.mpf("1e-80"), f"L2 quadrature error too large: {max_quad}"

    out = {
        "no_rh_proof": True,
        "dps": 85,
        "max_palindromic_reflection_abs_err": mp.nstr(max_pal, 15),
        "max_period_sum_abs_err": mp.nstr(max_sum, 15),
        "max_floor_mod_duality_abs_err": mp.nstr(max_dual, 15),
        "max_l2_quadrature_M3_abs_err": mp.nstr(max_quad, 15),
        "profiles": records,
    }
    out_path = ROOT_DIR / "palindromic_period_certificates.json"
    out_path.write_text(json.dumps(out, indent=2) + "\n", encoding="utf-8")
    print(f"Wrote {out_path} ({len(records)} profiles verified to 85 digits)")
    print(f"  max_pal_err={out['max_palindromic_reflection_abs_err']}")
    print(f"  max_sum_err={out['max_period_sum_abs_err']}")
    print(f"  max_dual_err={out['max_floor_mod_duality_abs_err']}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
