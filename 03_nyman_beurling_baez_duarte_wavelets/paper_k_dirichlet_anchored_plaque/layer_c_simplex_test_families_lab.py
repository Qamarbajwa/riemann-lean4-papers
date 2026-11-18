"""85-digit analytical simplex test-family lab & Graph-Laplacian verification.

Verifies Stage G.27/G.28 Lean 4 identities at 85-digit precision for N in
{4, 8, 12, 16, 24, 32, 48, 64}:
  1. Universal superdiagonal orthogonality G_tilde(m, m+1) = 0 for all 1 <= m <= N - 3.
  2. 1D plaque row-sum telescoping sum_b P(a, b) = (K(a+1,2)-K(a+2,2)) - (K(a+1,N)-K(a+2,N)).
  3. 2D total plaque sum sum_{a,b} P(a, b) = -2*K(N, 2) = pi * V(N, 2).
  4. Unit-defect row sum R_a^(N) = sum_b M_{ab} and Graph-Laplacian simplex decomposition:
       1 - S_cot(c, N) = sum_a alpha_a^2 R_a^(N) - (1/2) sum_{a,b} (alpha_a - alpha_b)^2 M_{ab}.

Evaluates three explicit matrix-inversion-free analytical simplex test families on A_N^{dir}
(c_1 = -1, sum alpha_m = 1) against the Dirichlet-anchored KKT optimum E_dir^(N):
  - Family I:   Dirichlet-projected Mobius simplex (c_k^raw = -mu(k), k >= 2, L2-projected onto
                sum_{k>=2} c_k/k = 1 and sum_{k>=2} c_k = 3).
  - Family II:  Selberg-BBLR log-smoothed Mobius simplex (c_k^raw = -mu(k)*(1 - ln k / ln(N+1)),
                k >= 2, L2-projected onto sum_{k>=2} c_k/k = 1 and sum_{k>=2} c_k = 3).
  - Family III: Cesaro-tapered harmonic simplex (alpha_m proportional to (1/(m+1))*(1 - m/(N-1))).

Under NO_RH_PROOF = TRUE, all computations are finite-N arithmetic and numerical diagnostics.
"""

from __future__ import annotations

import json
import pathlib
import time
from typing import Dict, List, Tuple

import mpmath as mp

from layer_c_dirichlet_locked_plaque_lab import (
    N_GRID,
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

HALF = ONE / TWO


def mobius_sieve(max_n: int) -> List[int]:
    """Return Mobius mu[0..max_n]."""
    mu = [1] * (max_n + 1)
    mu[0] = 0
    is_prime = [True] * (max_n + 1)
    for p in range(2, max_n + 1):
        if is_prime[p]:
            for m in range(p, max_n + 1, p):
                is_prime[m] = False
                mu[m] = -mu[m]
            p2 = p * p
            for m in range(p2, max_n + 1, p2):
                mu[m] = 0
    return mu


def c_dirichlet_to_eta(c: List[mp.mpf], N: int) -> List[mp.mpf]:
    """Extract cumulative dipole suffix weights alpha_m = sum_{j=m+2}^N c_j / j for m=1..N-2."""
    m_dim = N - 2
    eta = [ZERO] * m_dim
    running = ZERO
    for j in range(N, 2, -1):
        running += c[j] / mp.mpf(j)
        eta[j - 3] = running
    return eta


def dirichlet_project_raw(c_raw: List[mp.mpf], N: int) -> List[mp.mpf]:
    """Lock c_1 = -1 and L2-project (c_k^raw)_{k=2..N} onto sum c_k/k = 1, sum c_k = 3."""
    s0 = mp.mpf(N - 1)
    s1 = sum(ONE / mp.mpf(k) for k in range(2, N + 1))
    s2 = sum(ONE / mp.mpf(k * k) for k in range(2, N + 1))
    r0 = mp.mpf(3) - sum(c_raw[k] for k in range(2, N + 1))
    r1 = ONE - sum(c_raw[k] / mp.mpf(k) for k in range(2, N + 1))
    det = s0 * s2 - s1 * s1
    lam0 = (r0 * s2 - r1 * s1) / det
    lam1 = (s0 * r1 - s1 * r0) / det
    c = [ZERO] * (N + 1)
    c[1] = -ONE
    for k in range(2, N + 1):
        c[k] = c_raw[k] + lam0 + lam1 / mp.mpf(k)
    return c


def evaluate_simplex_candidate(
    c: List[mp.mpf],
    eta: List[mp.mpf],
    ell: List[mp.mpf],
    M_plaque: List[List[mp.mpf]],
    M_defect: List[List[mp.mpf]],
    row_sums: List[mp.mpf],
    N: int,
) -> Dict[str, mp.mpf]:
    """Evaluate quadratic energy, Graph-Laplacian split, and residual errors."""
    m_dim = N - 2
    d0 = sum(c[1 : N + 1])
    d1 = sum(c[k] / mp.mpf(k) for k in range(1, N + 1))
    alpha_sum = sum(eta)

    pi_drive = PI * sum(eta[a] * ell[a] for a in range(m_dim))
    plaque = ZERO
    for a in range(m_dim):
        ea = eta[a]
        row = M_plaque[a]
        for b in range(m_dim):
            plaque += ea * eta[b] * row[b]
    energy = ONE - pi_drive + plaque

    homog_energy = ZERO
    row_term = ZERO
    diff_energy = ZERO
    for a in range(m_dim):
        ea = eta[a]
        row_term += (ea * ea) * row_sums[a]
        row_m = M_defect[a]
        for b in range(m_dim):
            eb = eta[b]
            homog_energy += ea * eb * row_m[b]
            diff = ea - eb
            diff_energy += (diff * diff) * row_m[b]
    laplacian_energy = row_term - HALF * diff_energy
    return {
        "c1_err": abs(c[1] + ONE),
        "d0_err": abs(d0 - TWO),
        "d1_err": abs(d1),
        "alpha_sum_err": abs(alpha_sum - ONE),
        "l2_energy": energy,
        "row_sum_energy": row_term,
        "pair_diff_correction": -HALF * diff_energy,
        "homog_abs_err": abs(homog_energy - energy),
        "graph_laplacian_abs_err": abs(laplacian_energy - energy),
    }


def analyze_N(
    N: int, kmat: List[List[mp.mpf]], delta: List[mp.mpf], mu: List[int]
) -> Dict[str, object]:
    """Verify PR-8K/8L identities and evaluate Families I-III plus KKT optimum at horizon N."""
    m_dim = N - 2
    ell = [delta[a + 2] - delta[a + 1] for a in range(1, m_dim + 1)]
    M_plaque = [[ZERO for _ in range(m_dim)] for _ in range(m_dim)]
    M_gram = [[ZERO for _ in range(m_dim)] for _ in range(m_dim)]
    M_defect = [[ZERO for _ in range(m_dim)] for _ in range(m_dim)]
    half_pi = PI * HALF

    for a in range(1, m_dim + 1):
        for b in range(a, m_dim + 1):
            pab = kmat[a + 1][b + 1] - kmat[a + 1][b + 2] - kmat[a + 2][b + 1] + kmat[a + 2][b + 2]
            ds = ell[a - 1] + ell[b - 1]
            gab = half_pi * ds + pab
            mab = ONE - half_pi * ds + pab
            M_plaque[a - 1][b - 1] = M_plaque[b - 1][a - 1] = pab
            M_gram[a - 1][b - 1] = M_gram[b - 1][a - 1] = gab
            M_defect[a - 1][b - 1] = M_defect[b - 1][a - 1] = mab

    # Verify Lean 4 PR-8K and PR-8L identities
    max_superdiag_err = ZERO
    for m in range(m_dim - 1):
        max_superdiag_err = max(max_superdiag_err, abs(M_gram[m][m + 1]))

    max_row_plaque_err = ZERO
    total_plaque_sum = ZERO
    row_sums = [ZERO] * m_dim
    max_unit_row_err = ZERO
    for a in range(1, m_dim + 1):
        p_row = sum(M_plaque[a - 1])
        total_plaque_sum += p_row
        p_tel = (kmat[a + 1][2] - kmat[a + 2][2]) - (kmat[a + 1][N] - kmat[a + 2][N])
        max_row_plaque_err = max(max_row_plaque_err, abs(p_row - p_tel))

        u_row = sum(M_defect[a - 1])
        row_sums[a - 1] = u_row
        u_exact = mp.mpf(m_dim) * (ONE - half_pi * ell[a - 1]) - half_pi * delta[N] + p_row
        max_unit_row_err = max(max_unit_row_err, abs(u_row - u_exact))

    total_plaque_k_err = abs(total_plaque_sum - (-TWO * kmat[N][2]))
    total_plaque_v_err = abs(total_plaque_sum - (PI * vasyunin_cot_sum(N, 2)))

    # KKT Dirichlet-anchored optimum
    kkt = [[ZERO for _ in range(m_dim + 1)] for _ in range(m_dim + 1)]
    for i in range(m_dim):
        for j in range(m_dim):
            kkt[i][j] = M_plaque[i][j]
        kkt[i][m_dim] = ONE
        kkt[m_dim][i] = ONE
    rhs = [half_pi * ell[i] for i in range(m_dim)] + [ONE]
    eta_kkt = lu_solve(kkt, rhs)[:m_dim]
    c_kkt = eta_to_c(eta_kkt, N)

    # Family I: Dirichlet-projected Mobius simplex
    c_raw_mob = [ZERO] * (N + 1)
    for k in range(2, N + 1):
        c_raw_mob[k] = mp.mpf(-mu[k])
    c_fam1 = dirichlet_project_raw(c_raw_mob, N)
    eta_fam1 = c_dirichlet_to_eta(c_fam1, N)

    # Family II: Selberg-BBLR log-smoothed Mobius simplex
    log_np1 = mp.log(mp.mpf(N + 1))
    c_raw_sel = [ZERO] * (N + 1)
    for k in range(2, N + 1):
        c_raw_sel[k] = mp.mpf(-mu[k]) * (ONE - mp.log(mp.mpf(k)) / log_np1)
    c_fam2 = dirichlet_project_raw(c_raw_sel, N)
    eta_fam2 = c_dirichlet_to_eta(c_fam2, N)

    # Family III: Cesaro-tapered harmonic simplex
    raw_alpha = [
        (ONE / mp.mpf(m + 1)) * (ONE - mp.mpf(m) / mp.mpf(N - 1))
        for m in range(1, m_dim + 1)
    ]
    z_norm = sum(raw_alpha)
    eta_fam3 = [w / z_norm for w in raw_alpha]
    c_fam3 = eta_to_c(eta_fam3, N)

    families = {
        "kkt_dirichlet_opt": evaluate_simplex_candidate(
            c_kkt, eta_kkt, ell, M_plaque, M_defect, row_sums, N
        ),
        "family_i_mobius_proj": evaluate_simplex_candidate(
            c_fam1, eta_fam1, ell, M_plaque, M_defect, row_sums, N
        ),
        "family_ii_selberg_mobius": evaluate_simplex_candidate(
            c_fam2, eta_fam2, ell, M_plaque, M_defect, row_sums, N
        ),
        "family_iii_cesaro_harmonic": evaluate_simplex_candidate(
            c_fam3, eta_fam3, ell, M_plaque, M_defect, row_sums, N
        ),
    }

    log_n = mp.log(mp.mpf(N))
    e_kkt = families["kkt_dirichlet_opt"]["l2_energy"]
    formatted = {}
    for name, d in families.items():
        out = {k: mp.nstr(v, 30) for k, v in d.items()}
        out["log_n_mul_l2_energy"] = mp.nstr(log_n * d["l2_energy"], 30)
        out["ratio_to_kkt"] = mp.nstr(d["l2_energy"] / e_kkt, 30)
        formatted[name] = out

    return {
        "N": N,
        "log_n": mp.nstr(log_n, 30),
        "max_superdiag_abs_err": mp.nstr(max_superdiag_err, 12),
        "max_row_plaque_abs_err": mp.nstr(max_row_plaque_err, 12),
        "total_plaque_k_abs_err": mp.nstr(total_plaque_k_err, 12),
        "total_plaque_v_abs_err": mp.nstr(total_plaque_v_err, 12),
        "max_unit_row_abs_err": mp.nstr(max_unit_row_err, 12),
        "families": formatted,
    }


def main() -> None:
    t0 = time.time()
    max_n = max(N_GRID)
    kmat = build_unweighted_k_cot(max_n)
    delta = [ZERO] * (max_n + 1)
    for k in range(1, max_n + 1):
        delta[k] = vasyunin_cot_sum(k, 2) - vasyunin_cot_sum(k, 1)
    mu = mobius_sieve(max_n)

    rows = [analyze_N(N, kmat, delta, mu) for N in N_GRID]
    max_id_err = ZERO
    max_lap_err = ZERO
    for r in rows:
        for key in (
            "max_superdiag_abs_err",
            "max_row_plaque_abs_err",
            "total_plaque_k_abs_err",
            "total_plaque_v_abs_err",
            "max_unit_row_abs_err",
        ):
            max_id_err = max(max_id_err, mp.mpf(r[key]))
        for fam in r["families"].values():
            max_lap_err = max(max_lap_err, mp.mpf(fam["graph_laplacian_abs_err"]))
            max_lap_err = max(max_lap_err, mp.mpf(fam["homog_abs_err"]))

    payload = {
        "dps": mp.mp.dps,
        "no_rh_proof": True,
        "n_grid": N_GRID,
        "max_identity_abs_err": mp.nstr(max_id_err, 12),
        "max_graph_laplacian_abs_err": mp.nstr(max_lap_err, 12),
        "elapsed_seconds": round(time.time() - t0, 3),
        "rows": rows,
    }
    out_path = ROOT_DIR / "layer_c_simplex_test_families_results.json"
    out_path.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    print(
        f"Wrote {out_path.name} in {payload['elapsed_seconds']}s | "
        f"max_id_err={payload['max_identity_abs_err']} | "
        f"max_lap_err={payload['max_graph_laplacian_abs_err']}"
    )
    for r in rows:
        fams = r["families"]
        ek = float(fams["kkt_dirichlet_opt"]["l2_energy"])
        e1 = float(fams["family_i_mobius_proj"]["l2_energy"])
        e2 = float(fams["family_ii_selberg_mobius"]["l2_energy"])
        e3 = float(fams["family_iii_cesaro_harmonic"]["l2_energy"])
        rs2 = float(fams["family_ii_selberg_mobius"]["row_sum_energy"])
        pd2 = float(fams["family_ii_selberg_mobius"]["pair_diff_correction"])
        print(
            f"N={r['N']:2d} | E_dir={ek:.8f} | F1(Mob)={e1:.8f} | F2(Sel)={e2:.8f} "
            f"(Row={rs2:.6f}, Diff={pd2:+.6f}) | F3(Ces)={e3:.8f}"
        )


if __name__ == "__main__":
    main()
