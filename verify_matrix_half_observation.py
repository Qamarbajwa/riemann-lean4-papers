#!/usr/bin/env python3
"""
High-precision (50-60 digit mpmath + exact integer arithmetic) verification of:
  1. Two-matrix additive-multiplicative factorization F = Sigma @ D and exact
     inversion (M_mu @ Delta) @ F = I.
  2. Spatial (0, 1/2] and palindromic half-period folding:
       A_R = -J @ A_L,  E_full = 2 * A_L^T W_bar A_L.
  3. Three-matrix sandwich Q_M = D^T (Sigma^T W_M Sigma) D convergence and Book X.1
     tail bound E_dir(N) - E_M(c*) <= B^2 / (M + 1).
  4. Core (N - 2) x (N - 2) matrices G_tilde_N, P_N, and M_N:
       - rank-2 shift identities,
       - universal superdiagonal zeros G_tilde_{m, m+1} = 0 and isolated exact zeros
         (2, 4), (2, 7), (4, 8),
       - positive definiteness of G_tilde_N and M_N and Lorentzian signature (N - 3, 1)
         of the pure plaque matrix P_N across N = 4..64,
       - closed-form Dirichlet simplex optimum E_dir(N) = 1 / (1^T M_N^{-1} 1)
         above the prime floor sum_{N < p <= 500} 1/(2p^2).
"""

from __future__ import annotations

import math
import time
from typing import Dict, List, Tuple

import mpmath as mp


# ---------------------------------------------------------------------------
# 1. Exact Integer Factorization & Inversion
# ---------------------------------------------------------------------------

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
            ip = i * p
            if ip > n_max:
                break
            is_comp[ip] = True
            if i % p == 0:
                mu[ip] = 0
                break
            mu[ip] = -mu[i]
    return mu


def matmul_int(A: List[List[int]], B: List[List[int]]) -> List[List[int]]:
    rows = len(A)
    inner = len(B)
    cols = len(B[0]) if inner > 0 else 0
    return [
        [sum(A[i][k] * B[k][j] for k in range(inner)) for j in range(cols)]
        for i in range(rows)
    ]


def verify_integer_factorization_and_inversion(M: int = 64, N: int = 16) -> None:
    mu = mobius_sieve(M)
    Sigma = [[1 if m <= i else 0 for m in range(M)] for i in range(M)]
    D_rect = [[1 if (m + 1) % (j + 1) == 0 else 0 for j in range(N)] for m in range(M)]
    F_rect = [[(i + 1) // (j + 1) for j in range(N)] for i in range(M)]
    assert matmul_int(Sigma, D_rect) == F_rect, "F_{M,N} != Sigma_M @ D_{M,N}"

    D_sq = [[1 if (m + 1) % (j + 1) == 0 else 0 for j in range(M)] for m in range(M)]
    F_sq = [[(i + 1) // (j + 1) for j in range(M)] for i in range(M)]
    Delta = [
        [1 if i == m else (-1 if i == m + 1 else 0) for m in range(M)]
        for i in range(M)
    ]
    M_mu = [
        [mu[(i + 1) // (m + 1)] if (i + 1) % (m + 1) == 0 else 0 for m in range(M)]
        for i in range(M)
    ]
    I_M = [[1 if i == j else 0 for j in range(M)] for i in range(M)]

    assert matmul_int(Delta, Sigma) == I_M, "Delta @ Sigma != I"
    assert matmul_int(M_mu, D_sq) == I_M, "M_mu @ D != I"
    F_inv = matmul_int(M_mu, Delta)
    assert matmul_int(F_inv, F_sq) == I_M, "(M_mu @ Delta) @ F != I"
    print(f"[PASS] Exact integer factorization & inversion verified (M={M}, N={N})")


# ---------------------------------------------------------------------------
# 2. Vasyunin Cotangent Kernels & Core Matrix Builders (mpmath)
# ---------------------------------------------------------------------------

class VasyuninCache:
    """Cached arbitrary-precision evaluator for V(a, b), delta(k), K(j, k), G_tilde, P, M."""

    def __init__(self, max_k: int) -> None:
        self.max_k = max_k
        self.cot_table: Dict[int, List[mp.mpf]] = {}
        self.v_cache: Dict[Tuple[int, int], mp.mpf] = {}
        for a in range(2, max_k + 1):
            row = [mp.mpf(0)] * a
            for m in range(1, a):
                row[m] = mp.cot(mp.pi * m / a)
            self.cot_table[a] = row

    def v_sum(self, a: int, b: int) -> mp.mpf:
        if a <= 1:
            return mp.mpf(0)
        r = b % a
        if r == 0:
            return mp.mpf(0)
        key = (a, r)
        val = self.v_cache.get(key)
        if val is not None:
            return val
        row = self.cot_table[a]
        s = mp.mpf(0)
        for m in range(1, a):
            frac_num = (m * r) % a
            if frac_num:
                s += (mp.mpf(frac_num) / a) * row[m]
        self.v_cache[key] = s
        return s

    def delta_cot(self, k: int) -> mp.mpf:
        return self.v_sum(k, 2) - self.v_sum(k, 1)

    def unweighted_k_cot(self, j: int, k: int) -> mp.mpf:
        return -(mp.pi / 2) * (self.v_sum(j, k) + self.v_sum(k, j))

    def plaque_entry(self, a: int, b: int) -> mp.mpf:
        return (
            self.unweighted_k_cot(a + 1, b + 1)
            - self.unweighted_k_cot(a + 1, b + 2)
            - self.unweighted_k_cot(a + 2, b + 1)
            + self.unweighted_k_cot(a + 2, b + 2)
        )

    def dipole_gram_entry(self, a: int, b: int) -> mp.mpf:
        return (mp.pi / 2) * (
            self.delta_cot(a + 2) - self.delta_cot(a + 1) + self.delta_cot(b + 2) - self.delta_cot(b + 1)
        ) + self.plaque_entry(a, b)

    def unit_defect_entry(self, a: int, b: int) -> mp.mpf:
        return (
            mp.mpf(1)
            - (mp.pi / 2) * (self.delta_cot(a + 2) - self.delta_cot(a + 1) + self.delta_cot(b + 2) - self.delta_cot(b + 1))
            + self.plaque_entry(a, b)
        )

    def build_core_matrices(self, N: int) -> Tuple[mp.matrix, mp.matrix, mp.matrix, List[mp.mpf]]:
        dim = N - 2
        G = mp.zeros(dim, dim)
        P = mp.zeros(dim, dim)
        M_mat = mp.zeros(dim, dim)
        u = [self.delta_cot(i + 3) - self.delta_cot(i + 2) for i in range(dim)]
        for i in range(dim):
            a = i + 1
            for j in range(i, dim):
                b = j + 1
                p_val = self.plaque_entry(a, b)
                shift = (mp.pi / 2) * (u[i] + u[j])
                g_val = shift + p_val
                m_val = mp.mpf(1) - shift + p_val
                P[i, j] = P[j, i] = p_val
                G[i, j] = G[j, i] = g_val
                M_mat[i, j] = M_mat[j, i] = m_val
        return G, P, M_mat, u


# ---------------------------------------------------------------------------
# 3. Linear Algebra Helpers (Pure mpmath, No NumPy)
# ---------------------------------------------------------------------------

def max_abs_diff(A: mp.matrix, B: mp.matrix) -> mp.mpf:
    err = mp.mpf(0)
    for i in range(A.rows):
        for j in range(A.cols):
            d = abs(A[i, j] - B[i, j])
            if d > err:
                err = d
    return err


def mat_vec_mul(A: mp.matrix, x: List[mp.mpf]) -> List[mp.mpf]:
    return [sum(A[i, j] * x[j] for j in range(A.cols)) for i in range(A.rows)]


def dot(x: List[mp.mpf], y: List[mp.mpf]) -> mp.mpf:
    return sum(a * b for a, b in zip(x, y))


def symmetric_inertia_ldlt(A: mp.matrix, tol: mp.mpf) -> Tuple[int, int, int]:
    """
    Exact Sylvester inertia (n_pos, n_neg, n_zero) via Bunch-Parlett diagonal/2x2 pivoting
    on a symmetric matrix in O(n^3 / 3) time.
    """
    n = A.rows
    B = [[A[i, j] for j in range(n)] for i in range(n)]
    pos = neg = zero = 0
    k = 0
    while k < n:
        # Find largest diagonal magnitude in remaining submatrix k..n-1
        diag_piv = k
        diag_max = abs(B[k][k])
        for r in range(k + 1, n):
            v = abs(B[r][r])
            if v > diag_max:
                diag_max = v
                diag_piv = r

        # Find largest off-diagonal magnitude in k..n-1
        off_i, off_j, off_max = k, k, mp.mpf(0)
        for r in range(k, n):
            for c in range(r + 1, n):
                v = abs(B[r][c])
                if v > off_max:
                    off_max = v
                    off_i, off_j = r, c

        if diag_max <= tol and off_max <= tol:
            zero += n - k
            break

        if diag_max >= off_max:
            # Swap rows/cols k and diag_piv symmetrically
            if diag_piv != k:
                B[k], B[diag_piv] = B[diag_piv], B[k]
                for r in range(n):
                    B[r][k], B[r][diag_piv] = B[r][diag_piv], B[r][k]
            d = B[k][k]
            if d > tol:
                pos += 1
            elif d < -tol:
                neg += 1
            else:
                zero += 1
            for i in range(k + 1, n):
                mult = B[i][k] / d
                B[i][i] -= mult * B[k][i]
                for j in range(i + 1, n):
                    val = B[i][j] - mult * B[k][j]
                    B[i][j] = val
                    B[j][i] = val
            k += 1
        else:
            # Move off_i -> k, off_j -> k+1 and eliminate 2x2 block
            def swap_rc(a: int, b: int) -> None:
                if a == b:
                    return
                B[a], B[b] = B[b], B[a]
                for r in range(n):
                    B[r][a], B[r][b] = B[r][b], B[r][a]

            swap_rc(k, off_i)
            if off_j == k:
                off_j = off_i
            swap_rc(k + 1, off_j)

            a11, a12, a22 = B[k][k], B[k][k + 1], B[k + 1][k + 1]
            tr = a11 + a22
            det = a11 * a22 - a12 * a12
            disc = mp.sqrt(max(mp.mpf(0), tr * tr - 4 * det))
            lam1 = (tr + disc) / 2
            lam2 = (tr - disc) / 2
            for lam in (lam1, lam2):
                if lam > tol:
                    pos += 1
                elif lam < -tol:
                    neg += 1
                else:
                    zero += 1
            inv_det = mp.mpf(1) / det
            for i in range(k + 2, n):
                u1, u2 = B[i][k], B[i][k + 1]
                m1 = (a22 * u1 - a12 * u2) * inv_det
                m2 = (-a12 * u1 + a11 * u2) * inv_det
                for j in range(i, n):
                    val = B[i][j] - (m1 * B[k][j] + m2 * B[k + 1][j])
                    B[i][j] = val
                    B[j][i] = val
            k += 2
    return pos, neg, zero


def solve_simplex_optimum(M_mat: mp.matrix) -> Tuple[List[mp.mpf], mp.mpf]:
    """Return alpha* = M^{-1} 1 / (1^T M^{-1} 1) and E_dir(N) = 1 / (1^T M^{-1} 1)."""
    dim = M_mat.rows
    ones = mp.matrix([[mp.mpf(1)] for _ in range(dim)])
    x = mp.lu_solve(M_mat, ones)
    denom = sum(x[i, 0] for i in range(dim))
    alpha = [x[i, 0] / denom for i in range(dim)]
    e_dir = mp.mpf(1) / denom
    return alpha, e_dir


def reconstruct_c_from_alpha(N: int, alpha: List[mp.mpf]) -> List[mp.mpf]:
    """Reconstruct c[1..N] (1-indexed via list length N+1) matching Lean's cumulativeDipole basis."""
    c = [mp.mpf(0)] * (N + 1)
    c[1] = mp.mpf(-2)
    c[2] = mp.mpf(4)
    for m in range(1, N - 1):
        am = alpha[m - 1]
        for r in range(1, m + 1):
            c[r] += am * r
            c[r + 1] += am * (-2 * (r + 1))
            c[r + 2] += am * (r + 2)
    return c


def discrete_residual(c: List[mp.mpf], N: int, n: int) -> mp.mpf:
    return mp.mpf(1) + sum(c[k] * (n // k) for k in range(1, N + 1))


def primes_in_range(lo_exclusive: int, hi_inclusive: int) -> List[int]:
    out = []
    for n in range(max(2, lo_exclusive + 1), hi_inclusive + 1):
        if all(n % d != 0 for d in range(2, int(math.isqrt(n)) + 1)):
            out.append(n)
    return out


# ---------------------------------------------------------------------------
# 4. End-to-End Verification Suite
# ---------------------------------------------------------------------------

def main() -> None:
    t0 = time.perf_counter()
    mp.mp.dps = 55
    tol_eq = mp.mpf("1e-45")
    tol_eig = mp.mpf("1e-35")

    print("=" * 78)
    print("MATRIX RELATIONS & HALF-OBSERVATION HIGH-PRECISION VERIFIER (55-digit mpmath)")
    print("=" * 78)

    # 1. Exact integer identities
    verify_integer_factorization_and_inversion(M=64, N=16)

    # 2. Build Vasyunin cache up to N = 64
    N_list = [4, 6, 8, 12, 16, 24, 32, 48, 64]
    cache = VasyuninCache(max_k=max(N_list))

    # 3. Check G_tilde zeros: superdiagonal G_{m, m+1} = 0 and isolated non-superdiagonal zeros
    G32, P32, M32, u32 = cache.build_core_matrices(32)
    max_superdiag = max(abs(G32[i, i + 1]) for i in range(G32.rows - 1))
    assert max_superdiag < tol_eq, f"Superdiagonal non-zero: {max_superdiag}"
    for a, b in [(1, 2), (2, 4), (2, 7), (4, 8)]:
        val = abs(G32[a - 1, b - 1])
        assert val < tol_eq, f"Expected exact zero G_tilde({a},{b}), got {val}"
    print(f"[PASS] Superdiagonal zeros (max |G_{{m,m+1}}| = {mp.nstr(max_superdiag, 4)}) "
          "and non-superdiagonal zeros (2,4), (2,7), (4,8) verified")

    # 4. Core matrix rank-2 shift laws, signatures, condition numbers, & simplex optima
    print("\n--- Core Matrix Signatures & Dirichlet Simplex Optima (N = 4..64) ---")
    print(f"{'N':>4} {'dim':>4} {'sig(P_N)':>11} {'sig(G_tilde)':>13} {'sig(M_N)':>11} "
          f"{'E_dir(N)':>20} {'prime_floor(>N,<=500)':>21} {'t(s)':>6}  spectral notes")

    opt_data: Dict[int, Tuple[List[mp.mpf], List[mp.mpf], mp.mpf]] = {}
    for N in N_list:
        t_n = time.perf_counter()
        dim = N - 2
        G, P, M_mat, u = cache.build_core_matrices(N)

        # Verify rank-2 shift identities: G - (P + (pi/2)(u 1^T + 1 u^T)) = 0
        # and M - (1 1^T - (pi/2)(u 1^T + 1 u^T) + P) = 0
        G_rhs = mp.zeros(dim, dim)
        M_rhs = mp.zeros(dim, dim)
        for i in range(dim):
            for j in range(dim):
                shift = (mp.pi / 2) * (u[i] + u[j])
                G_rhs[i, j] = P[i, j] + shift
                M_rhs[i, j] = mp.mpf(1) - shift + P[i, j]
        assert max_abs_diff(G, G_rhs) < tol_eq, f"Rank-2 shift failed for G_{N}"
        assert max_abs_diff(M_mat, M_rhs) < tol_eq, f"Rank-2 shift failed for M_{N}"

        # Exact Sylvester inertia via symmetric LDL^T (cross-checked with eigsy for N <= 24)
        sig_P = symmetric_inertia_ldlt(P, tol_eig)
        sig_G = symmetric_inertia_ldlt(G, tol_eig)
        sig_M = symmetric_inertia_ldlt(M_mat, tol_eig)

        if N <= 24:
            eigs_P = mp.eigsy(P, eigvals_only=True)
            eigs_G = mp.eigsy(G, eigvals_only=True)
            eigs_M = mp.eigsy(M_mat, eigvals_only=True)
            eig_sig_P = (
                sum(1 for e in eigs_P if e > tol_eig),
                sum(1 for e in eigs_P if e < -tol_eig),
                sum(1 for e in eigs_P if abs(e) <= tol_eig),
            )
            eig_sig_G = (
                sum(1 for e in eigs_G if e > tol_eig),
                sum(1 for e in eigs_G if e < -tol_eig),
                sum(1 for e in eigs_G if abs(e) <= tol_eig),
            )
            eig_sig_M = (
                sum(1 for e in eigs_M if e > tol_eig),
                sum(1 for e in eigs_M if e < -tol_eig),
                sum(1 for e in eigs_M if abs(e) <= tol_eig),
            )
            assert sig_P == eig_sig_P, f"LDLT vs eigsy mismatch on P_{N}: {sig_P} vs {eig_sig_P}"
            assert sig_G == eig_sig_G, f"LDLT vs eigsy mismatch on G_{N}: {sig_G} vs {eig_sig_G}"
            assert sig_M == eig_sig_M, f"LDLT vs eigsy mismatch on M_{N}: {sig_M} vs {eig_sig_M}"
            kappa_G = max(eigs_G) / min(eigs_G)
            kappa_M = max(eigs_M) / min(eigs_M)
            spectral_note = (f"kappa(G)={mp.nstr(kappa_G, 4)}, kappa(M)={mp.nstr(kappa_M, 5)}, "
                             f"lam_min(P)={mp.nstr(min(eigs_P), 5)}")
        else:
            spectral_note = ""

        assert sig_P == (N - 3, 1, 0), f"Expected Lorentzian ({N - 3}, 1, 0) for P_{N}, got {sig_P}"
        assert sig_G == (dim, 0, 0), f"Expected PD ({dim}, 0, 0) for G_{N}, got {sig_G}"
        assert sig_M == (dim, 0, 0), f"Expected PD ({dim}, 0, 0) for M_{N}, got {sig_M}"

        alpha, e_dir = solve_simplex_optimum(M_mat)
        c_vec = reconstruct_c_from_alpha(N, alpha)
        assert abs(sum(alpha) - 1) < tol_eq, f"Sum alpha != 1 at N={N}"
        assert abs(c_vec[1] + 1) < tol_eq, f"c_1 != -1 at N={N}"
        assert abs(sum(c_vec[k] / k for k in range(1, N + 1))) < tol_eq, f"D1 != 0 at N={N}"
        assert abs(sum(c_vec[k] for k in range(1, N + 1)) - 2) < tol_eq, f"D0 != 2 at N={N}"

        p_list = primes_in_range(N, 500)
        prime_floor = sum(mp.mpf(1) / (2 * p * p) for p in p_list)
        assert e_dir > prime_floor, f"Simplex optimum {e_dir} below prime floor {prime_floor} at N={N}"

        if N in (4, 6):
            opt_data[N] = (alpha, c_vec, e_dir)

        dt = time.perf_counter() - t_n
        print(f"{N:>4} {dim:>4} {str((sig_P[0], sig_P[1])):>11} {str((sig_G[0], sig_G[1])):>13} "
              f"{str((sig_M[0], sig_M[1])):>11} {mp.nstr(e_dir, 14):>20} "
              f"{mp.nstr(prime_floor, 14):>21} {dt:>6.2f}  {spectral_note}")

    # N = 5 also needed for L_5 = 60 period folding
    _, _, M5, _ = cache.build_core_matrices(5)
    alpha5, e_dir5 = solve_simplex_optimum(M5)
    opt_data[5] = (alpha5, reconstruct_c_from_alpha(5, alpha5), e_dir5)

    # 5. Half-observation folding verification at N = 4 (L = 12, H = 5) and N = 5 (L = 60, H = 29)
    print("\n--- Spatial (1/2, 1] Annihilation & Palindromic Half-Period Folding ---")
    for N, L in [(4, 12), (5, 60)]:
        H = (L - 2) // 2
        _, c_vec, _ = opt_data[N]
        # Verify spatial upper-half (1/2, 1] cell A_c(1) = 0 and mirror A_c(L - 2) = 0
        a1 = discrete_residual(c_vec, N, 1)
        a_end = discrete_residual(c_vec, N, L - 2)
        assert abs(a1) < tol_eq, f"A_c(1) != 0 at N={N}: {a1}"
        assert abs(a_end) < tol_eq, f"A_c(L-2) != 0 at N={N}: {a_end}"

        aL = [discrete_residual(c_vec, N, i + 1) for i in range(H)]
        aR = [discrete_residual(c_vec, N, H + 1 + i) for i in range(H)]
        # Reversal J * aL check: aR + J * aL == 0
        max_anti = max(abs(aR[i] + aL[H - 1 - i]) for i in range(H))
        assert max_anti < tol_eq, f"Palindromic antisymmetry failed at N={N}: {max_anti}"

        wL = [mp.mpf(1) / ((i + 1) * (i + 2)) for i in range(H)]
        wR = [mp.mpf(1) / ((H + 1 + i) * (H + 2 + i)) for i in range(H)]
        w_bar = [(wL[i] + wR[H - 1 - i]) / 2 for i in range(H)]

        energy_full = sum(aL[i] ** 2 * wL[i] + aR[i] ** 2 * wR[i] for i in range(H))
        energy_half_doubled = 2 * sum(aL[i] ** 2 * w_bar[i] for i in range(H))
        fold_err = abs(energy_full - energy_half_doubled)
        assert fold_err < tol_eq, f"Half-period energy folding mismatch at N={N}: {fold_err}"
        print(f"[PASS] N={N}, L={L}, H={H}: |A(1)|={mp.nstr(abs(a1), 3)}, "
              f"||a_R + J a_L||_inf={mp.nstr(max_anti, 3)}, "
              f"E_full={mp.nstr(energy_full, 12)}, |E_full - 2 E_half|={mp.nstr(fold_err, 3)}")

    # 6. Three-matrix sandwich convergence Q_M -> E_dir(N) and Book X.1 tail bound
    print("\n--- Three-Matrix Sandwich Convergence & Book X.1 Tail Bound ---")
    for N, M_grid in [(4, [12, 60, 240, 1000]), (6, [60, 300, 1200])]:
        _, c_vec, e_dir = opt_data[N]
        B = mp.mpf(1) + sum(abs(c_vec[k]) for k in range(1, N + 1))
        for M in M_grid:
            e_m = sum(
                (discrete_residual(c_vec, N, n) ** 2) / (n * (n + 1))
                for n in range(1, M + 1)
            )
            tail = e_dir - e_m
            bound = (B ** 2) / (M + 1)
            assert mp.mpf(0) <= tail <= bound + tol_eq, (
                f"Tail bound violated at N={N}, M={M}: tail={tail}, bound={bound}"
            )
            print(f"[PASS] N={N}, M={M:>4}: E_M={mp.nstr(e_m, 12)}, "
                  f"E_dir - E_M={mp.nstr(tail, 6)} <= B^2/(M+1)={mp.nstr(bound, 6)}")

    total_t = time.perf_counter() - t0
    print("=" * 78)
    print(f"ALL MATRIX & HALF-OBSERVATION CHECKS PASSED ({total_t:.2f}s)")
    print("=" * 78)


if __name__ == "__main__":
    main()
