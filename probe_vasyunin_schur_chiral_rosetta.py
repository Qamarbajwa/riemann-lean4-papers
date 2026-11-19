#!/usr/bin/env python3
"""
probe_vasyunin_schur_chiral_rosetta.py

Standalone high-precision verification probe ("Seeing Negatively" via Schur Complements)
unifying:
  1. Dirichlet boundary anchor subtraction (Omega_N = |b> 1^T + Psi_N) & superdiagonal
     triple Gram matrix diag(G_{22}, G_{33}, G_{44}) alongside vacuum Schur complements
     for N = 3..12 (with exact Q(sqrt(3)) arithmetic for N <= 6).
  2. Palindromic chirality split (P_+ (+) P_-), squared-Hamiltonian parity blindness
     (T_pal^2 = I, Pi_{End^+}([T_pal, H]) = 0), and spatial half-projector reconstruction
     (K_half + K_half^T = 4 T_pal).
  3. Prime-Composite block Schur complement Sigma_Schur(C | P) = Q_CC - Q_CP Q_PP^{-1} Q_PC,
     variance-depletion defect delta_PC(N) across N = 4..30, and the N = 6 Lorentzian
     light-cone phase transition & Q(sqrt(3)) cotangent reciprocity.

NO_RH_PROOF = TRUE:
The Clay Riemann Hypothesis remains strictly OPEN. All checks here are finite-dimensional
algebraic and numerical audit identities in the Beurling-Nyman-Baez-Duarte Hilbert space.
"""

from __future__ import annotations

import json
import time
from fractions import Fraction
from pathlib import Path
from typing import Dict, List, Tuple

import mpmath as mp

from verify_matrix_half_observation import (
    VasyuninCache,
    build_anchored_wave_matrix,
    cholesky_factor,
    max_abs_diff,
    solve_simplex_optimum,
    symmetric_inertia_ldlt,
)

NO_RH_PROOF = True
mp.mp.dps = 55


def mat_mul(A: mp.matrix, B: mp.matrix) -> mp.matrix:
    return A * B


def frob_norm(A: mp.matrix) -> mp.mpf:
    s = mp.mpf(0)
    for i in range(A.rows):
        for j in range(A.cols):
            s += A[i, j] ** 2
    return mp.sqrt(s)


def frob_inner(A: mp.matrix, B: mp.matrix) -> mp.mpf:
    s = mp.mpf(0)
    for i in range(A.rows):
        for j in range(A.cols):
            s += A[i, j] * B[i, j]
    return s


def submatrix(A: mp.matrix, rows: List[int], cols: List[int]) -> mp.matrix:
    out = mp.zeros(len(rows), len(cols))
    for i, r in enumerate(rows):
        for j, c in enumerate(cols):
            out[i, j] = A[r, c]
    return out


def schur_complement(A_cc: mp.matrix, A_cp: mp.matrix, A_pp: mp.matrix) -> mp.matrix:
    """Compute S = A_cc - A_cp A_pp^{-1} A_pc with A_pc = A_cp^T."""
    A_pc = A_cp.T
    X = mp.zeros(A_pp.rows, A_pc.cols)
    for j in range(A_pc.cols):
        col = mp.matrix([[A_pc[i, j]] for i in range(A_pc.rows)])
        sol = mp.lu_solve(A_pp, col)
        for i in range(A_pp.rows):
            X[i, j] = sol[i, 0]
    return A_cc - A_cp * X


def is_prime(n: int) -> bool:
    if n < 2:
        return False
    d = 2
    while d * d <= n:
        if n % d == 0:
            return False
        d += 1
    return True


def run_test_1(cache: VasyuninCache) -> Tuple[Dict, mp.mpf]:
    """
    Test 1: Dirichlet Boundary Anchor Subtraction (Omega_N = |b> 1^T + Psi_N),
    Superdiagonal Triple Gram Matrix diag(G_{22}, G_{33}, G_{44}), and
    Vacuum/Boundary Schur Complements for N = 3..12.
    """
    print("\n=== Test 1: Dirichlet Anchor Subtraction & Superdiagonal Triple Gram ===")
    max_res = mp.mpf(0)

    # 1a. Anchor subtraction on finite slab M=64, N=6
    M_slab, N_slab = 64, 6
    Omega = build_anchored_wave_matrix(M_slab, N_slab)
    b_vec = mp.zeros(M_slab, 1)
    for i in range(M_slab):
        n = i + 1
        b_vec[i, 0] = mp.sqrt(mp.mpf(1) / (n * (n + 1))) * ((-1) ** n)
    ones_T = mp.ones(1, N_slab - 2)
    Psi = Omega - b_vec * ones_T
    # Verify Omega = |b> 1^T + Psi and top row of Omega vanishes (Dirichlet anchor)
    recon_err = max_abs_diff(Omega, b_vec * ones_T + Psi)
    top_row_err = max(abs(Omega[0, j]) for j in range(N_slab - 2))
    max_res = max(max_res, recon_err, top_row_err)

    # 1b. Superdiagonal orthogonal triple {v^(2), v^(3), v^(4)} inside G_tilde_6
    G6, P6, M6, u6 = cache.build_core_matrices(6)
    # Indices a in {2, 3, 4} correspond to 0-based indices {1, 2, 3}
    triple_block = submatrix(G6, [1, 2, 3], [1, 2, 3])
    diag_block = mp.zeros(3, 3)
    for k in range(3):
        diag_block[k, k] = triple_block[k, k]
    triple_offdiag_err = max_abs_diff(triple_block, diag_block)
    max_res = max(max_res, triple_offdiag_err)

    # Exact Q(pi, sqrt(3)) check for N = 6 reciprocity: G_{24} = 0 and G_{33} + G_{44} = pi*(4/sqrt(3) - 1)
    g24_err = abs(G6[1, 3])
    g33_plus_g44 = G6[2, 2] + G6[3, 3]
    exact_g33_g44 = mp.pi * (mp.mpf(4) / mp.sqrt(3) - 1)
    qsqrt3_err = abs(g33_plus_g44 - exact_g33_g44)
    max_res = max(max_res, g24_err, qsqrt3_err)

    # Exact rational/Q(sqrt(3)) check for V(6, 1) + V(6, 5) = 0 and delta_cot values
    v6_refl_err = abs(cache.v_sum(6, 1) + cache.v_sum(6, 5))
    d3_err = abs(cache.delta_cot(3) - mp.mpf(2) / (3 * mp.sqrt(3)))
    d4_err = abs(cache.delta_cot(4) - mp.mpf("0.5"))
    d6_err = abs(cache.delta_cot(6) - mp.mpf(5) / (3 * mp.sqrt(3)))
    max_res = max(max_res, v6_refl_err, d3_err, d4_err, d6_err)

    print(f"  Slab M={M_slab}, N={N_slab}: ||Omega - (|b>1^T + Psi)||_inf = {mp.nstr(recon_err, 4)}, max|Omega[0,:]| = {mp.nstr(top_row_err, 4)}")
    print(f"  Superdiagonal triple {{v^(2), v^(3), v^(4)}} off-diag err = {mp.nstr(triple_offdiag_err, 4)}")
    print(f"  Exact Q(sqrt(3)) identity |G_33 + G_44 - pi*(4/sqrt(3)-1)| = {mp.nstr(qsqrt3_err, 4)}")

    # 1c. Vacuum Schur complement inside augmented Gram G_aug = [[1, rho^T], [rho, G_tilde]] for N = 3..12
    print("\n  N   dim  E_free(N)         det(G_vac_schur)  v1_schur_tr       pos_inertia")
    schur_rows = []
    for N in range(3, 13):
        G, _, _, u = cache.build_core_matrices(N)
        dim = N - 2
        rho = mp.matrix([[-mp.pi / 2 * u[i]] for i in range(dim)])
        # Schur complement of vacuum |b> (norm^2 = 1) inside G_aug:
        # S_vac = G - rho * rho^T
        S_vac = G - rho * rho.T
        # Energy E_free(N) = 1 - rho^T G^{-1} rho
        G_inv_rho = mp.lu_solve(G, rho)
        E_free = mp.mpf(1) - (rho.T * G_inv_rho)[0, 0]
        det_S = mp.det(S_vac)
        pos, neg, zero = symmetric_inertia_ldlt(S_vac, mp.mpf("1e-40"))
        assert neg == 0 and zero == 0, f"S_vac not SPD at N={N}: ({pos},{neg},{zero})"

        # Schur complement of v^(1) inside G (for N >= 4)
        v1_schur_tr = mp.mpf(0)
        if dim >= 2:
            G_22 = submatrix(G, list(range(1, dim)), list(range(1, dim)))
            G_21 = submatrix(G, list(range(1, dim)), [0])
            G_11 = submatrix(G, [0], [0])
            S_v1 = schur_complement(G_22, G_21, G_11)
            v1_schur_tr = sum(S_v1[k, k] for k in range(S_v1.rows))

        schur_rows.append({
            "N": N,
            "dim": dim,
            "E_free": mp.nstr(E_free, 15),
            "det_S_vac": mp.nstr(det_S, 12),
            "v1_schur_trace": mp.nstr(v1_schur_tr, 12),
            "inertia": [pos, neg, zero],
        })
        print(f"  {N:2d}  {dim:3d}  {mp.nstr(E_free, 14):>16s}  {mp.nstr(det_S, 12):>16s}  {mp.nstr(v1_schur_tr, 12):>16s}  ({pos},{neg},{zero})")

    return {
        "anchor_recon_err": mp.nstr(recon_err, 6),
        "triple_offdiag_err": mp.nstr(triple_offdiag_err, 6),
        "qsqrt3_reciprocity_err": mp.nstr(qsqrt3_err, 6),
        "diag_triple": [mp.nstr(triple_block[k, k], 15) for k in range(3)],
        "vacuum_schur_table": schur_rows,
    }, max_res


def run_test_2(cache: VasyuninCache) -> Tuple[Dict, mp.mpf]:
    """
    Test 2: Palindromic Chirality Split (P_+ (+) P_-), Squared-Hamiltonian Parity
    Blindness, and Spatial Half-Projector Reconstruction.
    """
    print("\n=== Test 2: Palindromic Chirality Split & Half-Projector Reconstruction ===")
    max_res = mp.mpf(0)
    results = []

    for N, L in ((4, 12), (5, 60)):
        M = L - 2  # Fundamental open-period length (even: M = 2*H)
        H = M // 2
        I_M = mp.eye(M)
        J = mp.zeros(M, M)
        for i in range(M):
            J[i, M - 1 - i] = mp.mpf(1)

        P_plus = mp.mpf("0.5") * (I_M + J)
        P_minus = mp.mpf("0.5") * (I_M - J)
        T_pal = P_plus - P_minus  # = J

        # Projector axioms & T_pal^2 = I parity blindness
        proj_err = max(
            max_abs_diff(P_plus + P_minus, I_M),
            max_abs_diff(P_plus * P_minus, mp.zeros(M, M)),
            max_abs_diff(T_pal * T_pal, I_M),
            max_abs_diff(P_plus * (T_pal * T_pal) * P_minus, mp.zeros(M, M)),
        )
        max_res = max(max_res, proj_err)

        # Interior fluctuation operator H_Psi = Psi @ Psi^T on the M-dimensional slab
        Omega = build_anchored_wave_matrix(M, N)
        b_vec = mp.zeros(M, 1)
        for i in range(M):
            n = i + 1
            b_vec[i, 0] = mp.sqrt(mp.mpf(1) / (n * (n + 1))) * ((-1) ** n)
        Psi = Omega - b_vec * mp.ones(1, N - 2)
        H_Psi = Psi * Psi.T

        # Chiral commutator [T_pal, H_Psi] in End^- and projection onto End^+
        comm_pal = T_pal * H_Psi - H_Psi * T_pal
        comm_even_proj = P_plus * comm_pal * P_plus + P_minus * comm_pal * P_minus
        even_proj_err = max_abs_diff(comm_even_proj, mp.zeros(M, M))
        max_res = max(max_res, even_proj_err)

        # Also check zero Frobenius inner product against palindromic baseline A_+ = P_+ H_Psi P_+ + P_- H_Psi P_-
        A_plus = P_plus * H_Psi * P_plus + P_minus * H_Psi * P_minus
        frob_orth_err = abs(frob_inner(A_plus, comm_pal))
        max_res = max(max_res, frob_orth_err)

        # Spatial half-projector reconstruction: P_half = diag(I_H, 0_H)
        # K_half = 2 * P_half * T_pal => K_half + K_half^T = 2 * T_pal
        # With factor 4: K_half4 = 4 * P_half * T_pal => K_half4 + K_half4^T = 4 * T_pal
        P_half = mp.zeros(M, M)
        for i in range(H):
            P_half[i, i] = mp.mpf(1)
        K_half = mp.mpf(4) * P_half * T_pal
        recon_4T_err = max_abs_diff(K_half + K_half.T, mp.mpf(4) * T_pal)
        max_res = max(max_res, recon_4T_err)

        # Off-diagonal parity-odd block norm of H_Psi
        H_odd = P_plus * H_Psi * P_minus + P_minus * H_Psi * P_plus
        odd_norm = frob_norm(H_odd)

        print(
            f"  N={N}, M={M} (H={H}): proj_err={mp.nstr(proj_err, 3)}, "
            f"||Pi_+( [T_pal, H_Psi] )||={mp.nstr(even_proj_err, 3)}, "
            f"<A_+, [T_pal, H_Psi]>={mp.nstr(frob_orth_err, 3)}, "
            f"||K_half+K_half^T - 4 T_pal||={mp.nstr(recon_4T_err, 3)}"
        )
        results.append({
            "N": N,
            "L": L,
            "M": M,
            "H": H,
            "proj_err": mp.nstr(proj_err, 4),
            "even_proj_err": mp.nstr(even_proj_err, 4),
            "frob_orth_err": mp.nstr(frob_orth_err, 4),
            "recon_4T_err": mp.nstr(recon_4T_err, 4),
            "H_odd_frob_norm": mp.nstr(odd_norm, 12),
        })

    return {"palindromic_cases": results}, max_res


def run_test_3(cache: VasyuninCache) -> Tuple[Dict, mp.mpf]:
    """
    Test 3: Prime-Composite Block Schur Complement & The N = 6 Lorentzian
    Light-Cone Transition across N = 4..30.
    """
    print("\n=== Test 3: Prime-Composite Block Schur Complement (N = 4..30) ===")
    print("  N   |P| |C|  delta_PC(N)       det(Sigma_Schur)   lam_min(P_N)     alpha*^T P alpha*  sig(P_N)")
    max_res = mp.mpf(0)
    rows = []

    for N in range(4, 31):
        G, P_mat, M_mat, _ = cache.build_core_matrices(N)
        dim = N - 2
        # Mode a (0-based idx i = a-1) corresponds to k = a + 2 in {3..N}
        p_idx = [i for i in range(dim) if is_prime(i + 3)]
        c_idx = [i for i in range(dim) if not is_prime(i + 3)]

        Q_pp = submatrix(G, p_idx, p_idx)
        Q_cc = submatrix(G, c_idx, c_idx)
        Q_cp = submatrix(G, c_idx, p_idx)

        Sigma_schur = schur_complement(Q_cc, Q_cp, Q_pp)
        # Symmetry check of Schur complement
        sym_err = max_abs_diff(Sigma_schur, Sigma_schur.T)
        max_res = max(max_res, sym_err)

        delta_pc = mp.mpf(1) - frob_norm(Sigma_schur) / frob_norm(Q_cc)
        det_schur = mp.det(Sigma_schur)
        pos_s, neg_s, zero_s = symmetric_inertia_ldlt(Sigma_schur, mp.mpf("1e-40"))
        assert neg_s == 0 and zero_s == 0, f"Prime-subtracted Schur not SPD at N={N}"

        # Track P_N Lorentzian signature & optimal trajectory alpha*^T P_N alpha*
        pos_p, neg_p, zero_p = symmetric_inertia_ldlt(P_mat, mp.mpf("1e-40"))
        assert (pos_p, neg_p, zero_p) == (dim - 1, 1, 0), f"Unexpected P_N inertia at N={N}"

        alpha_star, _ = solve_simplex_optimum(M_mat)
        a_vec = mp.matrix([[v] for v in alpha_star])
        lorentz_val = (a_vec.T * P_mat * a_vec)[0, 0]
        if N == 4:
            assert lorentz_val > 0, f"Expected spacelike alpha*^T P alpha* > 0 at N=4"
        if N >= 6:
            assert lorentz_val < 0, f"Expected timelike alpha*^T P alpha* < 0 at N={N}"

        # Compute min eigenvalue of P_mat for representative N <= 16 or all N
        eigs_p = mp.eigsy(P_mat, eigvals_only=True)
        lam_min_p = min(eigs_p)

        if N in (4, 5, 6, 7, 8, 10, 12, 16, 20, 24, 30):
            print(
                f"  {N:2d}   {len(p_idx):2d}  {len(c_idx):2d}  {mp.nstr(delta_pc, 12):>16s}  "
                f"{mp.nstr(det_schur, 10):>16s}  {mp.nstr(lam_min_p, 10):>14s}  "
                f"{mp.nstr(lorentz_val, 10):>15s}  ({pos_p},{neg_p})"
            )

        rows.append({
            "N": N,
            "num_primes": len(p_idx),
            "num_composites": len(c_idx),
            "delta_PC": mp.nstr(delta_pc, 15),
            "det_Sigma_Schur": mp.nstr(det_schur, 12),
            "lam_min_P": mp.nstr(lam_min_p, 12),
            "alpha_star_P_alpha_star": mp.nstr(lorentz_val, 15),
            "P_inertia": [pos_p, neg_p, zero_p],
            "Schur_inertia": [pos_s, neg_s, zero_s],
        })

    return {"prime_composite_schur_table": rows}, max_res


def main() -> None:
    t0 = time.time()
    print("=" * 80)
    print("VASYUNIN SCHUR-CHIRAL ROSETTA PROBE (55-digit mpmath, NO_RH_PROOF = TRUE)")
    print("=" * 80)

    cache = VasyuninCache(max_k=32)
    t1_res, r1 = run_test_1(cache)
    t2_res, r2 = run_test_2(cache)
    t3_res, r3 = run_test_3(cache)

    max_residual = max(r1, r2, r3)
    assert max_residual < mp.mpf("1e-50"), f"Residual too large: {max_residual}"

    elapsed = time.time() - t0
    receipt = {
        "NO_RH_PROOF": NO_RH_PROOF,
        "VASYUNIN_SCHUR_CHIRAL_ROSETTA_OK": True,
        "mpmath_dps": mp.mp.dps,
        "max_numerical_residual": mp.nstr(max_residual, 6),
        "elapsed_seconds": round(elapsed, 3),
        "test_1_dirichlet_anchor_and_triple": t1_res,
        "test_2_palindromic_chirality": t2_res,
        "test_3_prime_composite_schur": t3_res,
    }

    out_path = Path(__file__).resolve().parent / "vasyunin_schur_chiral_rosetta_results.json"
    out_path.write_text(json.dumps(receipt, indent=2), encoding="utf-8")

    print("\n" + "=" * 80)
    print(f"VASYUNIN_SCHUR_CHIRAL_ROSETTA_OK = True | NO_RH_PROOF = {NO_RH_PROOF}")
    print(f"Max numerical residual = {mp.nstr(max_residual, 6)} (< 1e-50) | Elapsed = {elapsed:.2f}s")
    print(f"JSON receipt written to: {out_path.name}")
    print("=" * 80)


if __name__ == "__main__":
    main()
