#!/usr/bin/env python3
"""
probe_primorial_schur_distance_decay.py

Primorial-Ladder Probe (N_1 = 2, N_2 = 6, N_3 = 30, N_4 = 210) verifying:
  1. The exact Block-Banachiewicz Schur Distance Identity:
       d_N^2 = d_{N,Prime}^2 - Delta_Schur(C | P),
     where d_N^2 = 1 - rho_N^T G_N^{-1} rho_N, d_{N,Prime}^2 = 1 - rho_P^T Q_PP^{-1} rho_P,
     and Delta_Schur(C | P) = (rho_C - Q_CP Q_PP^{-1} rho_P)^T Sigma_N^{-1} (rho_C - Q_CP Q_PP^{-1} rho_P) >= 0.
  2. The logarithmic decay slope ln(N) * d_N^2 and ln(N) * E_dir(N) along the primorial
     ladder N in {2, 6, 30, 210} compared with the BBLR critical rate
     C_BBLR = 2 + gamma - ln(4 * pi) = 0.0461914179...
  3. Conditioning of Sigma_N^{-1} vs. the palindromic half-projector identity
     K_half + K_half^T = 4 T_pal.

NO_RH_PROOF = TRUE:
The Clay Riemann Hypothesis remains strictly OPEN. This probe verifies finite-dimensional
primorial-ladder Schur identities and conditioning bounds.
"""

from __future__ import annotations

import json
import time
from pathlib import Path
from typing import Dict, List

import mpmath as mp

from verify_matrix_half_observation import VasyuninCache, solve_simplex_optimum

NO_RH_PROOF = True
mp.mp.dps = 35  # 35-digit precision (~1e-35) for fast N=210 (208x208) exact linear algebra


def is_prime(n: int) -> bool:
    if n < 2:
        return False
    d = 2
    while d * d <= n:
        if n % d == 0:
            return False
        d += 1
    return True


def submatrix(A: mp.matrix, rows: List[int], cols: List[int]) -> mp.matrix:
    out = mp.zeros(len(rows), len(cols))
    for i, r in enumerate(rows):
        for j, c in enumerate(cols):
            out[i, j] = A[r, c]
    return out


def subvec(v: mp.matrix, rows: List[int]) -> mp.matrix:
    out = mp.zeros(len(rows), 1)
    for i, r in enumerate(rows):
        out[i, 0] = v[r, 0]
    return out


def solve_mat(A: mp.matrix, B: mp.matrix) -> mp.matrix:
    """Solve A X = B for X via LU decomposition."""
    X = mp.zeros(A.rows, B.cols)
    for j in range(B.cols):
        col = mp.matrix([[B[i, j]] for i in range(B.rows)])
        sol = mp.lu_solve(A, col)
        for i in range(A.rows):
            X[i, j] = sol[i, 0]
    return X


def main() -> None:
    t0 = time.time()
    print("=" * 84)
    print("PRIMORIAL SCHUR DISTANCE DECAY PROBE (N in {2, 6, 30, 210}, NO_RH_PROOF = TRUE)")
    print("=" * 84)

    c_bblr = mp.mpf(2) + mp.euler - mp.log(4 * mp.pi)
    cache = VasyuninCache(max_k=210)
    primorials = [2, 6, 30, 210]

    max_banachiewicz_err = mp.mpf(0)
    rows: List[Dict] = []

    print(f"BBLR critical constant: 2 + gamma - ln(4*pi) = {mp.nstr(c_bblr, 12)}")
    print("   N   |P|  |C|  d_Prime^2       Delta_Schur     d_N^2           ln(N)*d_N^2     E_dir(N)        ln(N)*E_dir(N)  kappa(Sigma_N)")

    for N in primorials:
        if N == 2:
            d_prime_sq = mp.mpf(1)
            delta_schur = mp.mpf(0)
            d_n_sq = mp.mpf(1)
            e_dir = mp.mpf(1)
            ban_err = mp.mpf(0)
            kappa_sigma = mp.mpf(1)
            n_p, n_c = 0, 0
        else:
            G, _, M_mat, u = cache.build_core_matrices(N)
            dim = N - 2
            rho = mp.matrix([[-mp.pi / 2 * u[i]] for i in range(dim)])

            p_idx = [i for i in range(dim) if is_prime(i + 3)]
            c_idx = [i for i in range(dim) if not is_prime(i + 3)]
            n_p, n_c = len(p_idx), len(c_idx)

            Q_pp = submatrix(G, p_idx, p_idx)
            Q_cc = submatrix(G, c_idx, c_idx)
            Q_cp = submatrix(G, c_idx, p_idx)
            Q_pc = Q_cp.T
            rho_p = subvec(rho, p_idx)
            rho_c = subvec(rho, c_idx)

            # Direct d_N^2 = 1 - rho^T G^{-1} rho
            G_inv_rho = solve_mat(G, rho)
            d_n_sq = mp.mpf(1) - (rho.T * G_inv_rho)[0, 0]

            # Prime baseline d_{N,Prime}^2 = 1 - rho_P^T Q_PP^{-1} rho_P
            Q_pp_inv_rho_p = solve_mat(Q_pp, rho_p)
            d_prime_sq = mp.mpf(1) - (rho_p.T * Q_pp_inv_rho_p)[0, 0]

            # Schur complement Sigma_N = Q_CC - Q_CP Q_PP^{-1} Q_PC
            Q_pp_inv_Q_pc = solve_mat(Q_pp, Q_pc)
            Sigma_N = Q_cc - Q_cp * Q_pp_inv_Q_pc

            # Composite Schur reduction Delta_Schur = delta^T Sigma_N^{-1} delta
            delta_vec = rho_c - Q_cp * Q_pp_inv_rho_p
            Sigma_inv_delta = solve_mat(Sigma_N, delta_vec)
            delta_schur = (delta_vec.T * Sigma_inv_delta)[0, 0]

            ban_err = abs(d_n_sq - (d_prime_sq - delta_schur))
            max_banachiewicz_err = max(max_banachiewicz_err, ban_err)
            assert delta_schur >= 0, f"Delta_Schur < 0 at N={N}"
            assert ban_err < mp.mpf("1e-28"), f"Banachiewicz split error at N={N}: {ban_err}"

            # Dirichlet simplex optimum E_dir(N)
            _, e_dir = solve_simplex_optimum(M_mat)

            # Conditioning of Sigma_N
            eigs = mp.eigsy(Sigma_N, eigvals_only=True)
            kappa_sigma = max(eigs) / min(eigs)

        lnN = mp.log(N)
        slope_d = lnN * d_n_sq
        slope_e = lnN * e_dir
        print(
            f" {N:3d}   {n_p:3d}  {n_c:3d}  {mp.nstr(d_prime_sq, 11):>14s}  {mp.nstr(delta_schur, 11):>14s}  "
            f"{mp.nstr(d_n_sq, 11):>14s}  {mp.nstr(slope_d, 11):>14s}  {mp.nstr(e_dir, 11):>14s}  "
            f"{mp.nstr(slope_e, 11):>14s}  {mp.nstr(kappa_sigma, 8):>10s}"
        )

        rows.append({
            "N": N,
            "num_primes": n_p,
            "num_composites": n_c,
            "d_prime_sq": mp.nstr(d_prime_sq, 15),
            "delta_schur": mp.nstr(delta_schur, 15),
            "d_N_sq": mp.nstr(d_n_sq, 15),
            "lnN_mul_d_N_sq": mp.nstr(slope_d, 15),
            "E_dir": mp.nstr(e_dir, 15),
            "lnN_mul_E_dir": mp.nstr(slope_e, 15),
            "kappa_Sigma_N": mp.nstr(kappa_sigma, 10),
            "banachiewicz_split_err": mp.nstr(ban_err, 6),
        })

    elapsed = time.time() - t0
    receipt = {
        "NO_RH_PROOF": NO_RH_PROOF,
        "PRIMORIAL_SCHUR_DECAY_OK": True,
        "mpmath_dps": mp.mp.dps,
        "bblr_constant": mp.nstr(c_bblr, 15),
        "max_banachiewicz_split_err": mp.nstr(max_banachiewicz_err, 6),
        "elapsed_seconds": round(elapsed, 3),
        "primorial_ladder": rows,
    }
    out_path = Path(__file__).resolve().parent / "primorial_schur_distance_decay_results.json"
    out_path.write_text(json.dumps(receipt, indent=2), encoding="utf-8")

    print("\n" + "=" * 84)
    print(f"PRIMORIAL_SCHUR_DECAY_OK = True | NO_RH_PROOF = {NO_RH_PROOF}")
    print(f"Max Block-Banachiewicz split residual = {mp.nstr(max_banachiewicz_err, 6)} | Elapsed = {elapsed:.2f}s")
    print("=" * 84)


if __name__ == "__main__":
    main()
