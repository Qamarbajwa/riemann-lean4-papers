"""80-digit high-precision pure plaque & Dirichlet-anchored (c1 = -1) variational lab.

Computes exact high-precision solutions for N in {4, 8, 12, 16, 24, 32, 48, 64} across three
formulations on the affine Baez-Duarte manifold A_N = {c | D1(c,N) = 0, D0(c,N) = 2}:
  1. Unconstrained KKT optimum c_opt^(N) maximizing S_cot(c, N) over A_N.
  2. Dirichlet-anchored (c1 = -1) KKT optimum c_dir^(N) maximizing S_cot(c, N) subject to c1 = -1.
  3. Unit-drive Dirichlet-anchored optimum c_unit^(N) minimizing P_N(h) = 1 - S_cot(c, N)
     subject to c1 = -1 and pi * L_cot(h, N) = 1.

Also verifies the 2D discrete Abel telescoping identity:
  sum_{j,k=3}^N (c_j c_k / (j k)) * (K_cot(j,k) - K_cot(j,2) - K_cot(2,k)) = P_N(h)
to < 1e-78 precision across all N and all three solution families.
Under NO_RH_PROOF = TRUE, all quantities represent finite-N variational diagnostics.
"""

from __future__ import annotations

import json
import pathlib
import time
from typing import Dict, List, Tuple

import mpmath as mp

mp.mp.dps = 85
ZERO = mp.mpf(0)
ONE = mp.mpf(1)
TWO = mp.mpf(2)
PI = mp.pi

N_GRID = [4, 8, 12, 16, 24, 32, 48, 64]
ROOT_DIR = pathlib.Path(__file__).resolve().parent


def vasyunin_cot_sum(j: int, k: int) -> mp.mpf:
    """Compute sum_{a=1}^{j-1} {a k / j} cot(pi a / j)."""
    if j <= 1:
        return ZERO
    total = ZERO
    for a in range(1, j):
        rem = (a * k) % j
        if rem != 0:
            frac = mp.mpf(rem) / mp.mpf(j)
            total += frac * mp.cot(PI * mp.mpf(a) / mp.mpf(j))
    return total


def build_unweighted_k_cot(max_n: int) -> List[List[mp.mpf]]:
    """Build symmetric unweighted K_cot(j, k) = -(pi / 2) * (S(j,k) + S(k,j)) for 1..max_n."""
    kmat = [[ZERO for _ in range(max_n + 1)] for _ in range(max_n + 1)]
    half_pi = -PI / TWO
    for j in range(1, max_n + 1):
        for k in range(j, max_n + 1):
            val = half_pi * (vasyunin_cot_sum(j, k) + vasyunin_cot_sum(k, j))
            kmat[j][k] = val
            kmat[k][j] = val
    return kmat


def lu_solve(mat: List[List[mp.mpf]], rhs: List[mp.mpf]) -> List[mp.mpf]:
    """Solve dense linear system mat * x = rhs with partial pivoting at 85-digit precision."""
    n = len(rhs)
    aug = [row[:] + [rhs[i]] for i, row in enumerate(mat)]
    for col in range(n):
        piv = max(range(col, n), key=lambda r: abs(aug[r][col]))
        if piv != col:
            aug[col], aug[piv] = aug[piv], aug[col]
        diag = aug[col][col]
        if abs(diag) < mp.mpf("1e-75"):
            raise RuntimeError(f"Near-singular pivot at col {col}: {diag}")
        for r in range(col + 1, n):
            factor = aug[r][col] / diag
            if factor != ZERO:
                for c in range(col, n + 1):
                    aug[r][c] -= factor * aug[col][c]
    sol = [ZERO] * n
    for r in range(n - 1, -1, -1):
        s = aug[r][n]
        for c in range(r + 1, n):
            s -= aug[r][c] * sol[c]
        sol[r] = s / aug[r][r]
    return sol


def eta_to_c(eta: List[mp.mpf], N: int) -> List[mp.mpf]:
    """Convert cumulative dipole coordinates eta[0..N-3] to full vector c[1..N]."""
    m_dim = N - 2
    h = [ZERO] * (N + 1)
    h[1] = sum(eta)
    h[2] = -TWO * h[1] - TWO * eta[0]
    for j in range(3, N + 1):
        idx = j - 3
        diff = eta[idx] - (eta[idx + 1] if idx + 1 < m_dim else ZERO)
        h[j] = mp.mpf(j) * diff
    c = h[:]
    c[1] += -TWO
    c[2] += mp.mpf(4)
    return c


def evaluate_candidate(
    c: List[mp.mpf],
    eta: List[mp.mpf],
    ell: List[mp.mpf],
    M_plaque: List[List[mp.mpf]],
    kmat: List[List[mp.mpf]],
    N: int,
) -> Dict[str, mp.mpf]:
    """Compute D0, D1, L_cot, S_cot, E = 1 - S_cot, P_N(h), and 2D telescoping residual."""
    m_dim = N - 2
    d0 = sum(c[1 : N + 1])
    d1 = sum(c[k] / mp.mpf(k) for k in range(1, N + 1))
    drive = sum(eta[a] * ell[a] for a in range(m_dim))
    pi_drive = PI * drive
    plaque = ZERO
    for a in range(m_dim):
        ea = eta[a]
        row = M_plaque[a]
        for b in range(m_dim):
            plaque += ea * eta[b] * row[b]
    scot = -c[1] * pi_drive - plaque
    energy = ONE - scot
    telescoped = ZERO
    for j in range(3, N + 1):
        cj_j = c[j] / mp.mpf(j)
        k_j2 = kmat[j][2]
        for k in range(3, N + 1):
            telescoped += cj_j * (c[k] / mp.mpf(k)) * (kmat[j][k] - k_j2 - kmat[2][k])
    tel_err = abs(telescoped - plaque)
    # Also check Q_cot = pi * h_1 * L_cot + P_N against direct double sum
    qcot_direct = ZERO
    for j in range(1, N + 1):
        for k in range(1, N + 1):
            qcot_direct += (c[j] / mp.mpf(j)) * (c[k] / mp.mpf(k)) * kmat[j][k]
    scot_err = abs((-qcot_direct) - scot)
    cs_rhs = plaque - (pi_drive ** 2 - (c[1] + TWO) * pi_drive)
    return {
        "c1": c[1],
        "d0_err": abs(d0 - TWO),
        "d1_err": abs(d1),
        "pi_drive": pi_drive,
        "plaque": plaque,
        "scot": scot,
        "l2_energy": energy,
        "telescoping_abs_err": tel_err,
        "scot_identity_abs_err": scot_err,
        "plaque_cs_slack": cs_rhs,
    }


def solve_for_N(N: int, kmat: List[List[mp.mpf]], delta: List[mp.mpf]) -> Dict[str, object]:
    """Solve all 3 formulations at truncation degree N."""
    m_dim = N - 2
    ell = [delta[a + 2] - delta[a + 1] for a in range(1, m_dim + 1)]
    M_plaque = [[ZERO for _ in range(m_dim)] for _ in range(m_dim)]
    M_full = [[ZERO for _ in range(m_dim)] for _ in range(m_dim)]
    half_pi = PI / TWO
    for a in range(1, m_dim + 1):
        for b in range(a, m_dim + 1):
            pab = kmat[a + 1][b + 1] - kmat[a + 1][b + 2] - kmat[a + 2][b + 1] + kmat[a + 2][b + 2]
            fab = half_pi * (ell[a - 1] + ell[b - 1]) + pab
            M_plaque[a - 1][b - 1] = pab
            M_plaque[b - 1][a - 1] = pab
            M_full[a - 1][b - 1] = fab
            M_full[b - 1][a - 1] = fab

    # 1. Unconstrained KKT: M_full * eta_opt = pi * ell
    rhs_opt = [PI * ell[i] for i in range(m_dim)]
    eta_opt = lu_solve(M_full, rhs_opt)
    c_opt = eta_to_c(eta_opt, N)
    eval_opt = evaluate_candidate(c_opt, eta_opt, ell, M_plaque, kmat, N)

    # 2. Dirichlet-anchored (c1 = -1 <=> sum eta = 1):
    # Minimize alpha^T M_plaque alpha - pi * ell^T alpha s.t. 1^T alpha = 1
    # => [M_plaque, 1; 1^T, 0] [alpha; lambda] = [(pi/2)*ell; 1]
    kkt_dir = [[ZERO for _ in range(m_dim + 1)] for _ in range(m_dim + 1)]
    for i in range(m_dim):
        for j in range(m_dim):
            kkt_dir[i][j] = M_plaque[i][j]
        kkt_dir[i][m_dim] = ONE
        kkt_dir[m_dim][i] = ONE
    rhs_dir = [(PI / TWO) * ell[i] for i in range(m_dim)] + [ONE]
    sol_dir = lu_solve(kkt_dir, rhs_dir)
    eta_dir = sol_dir[:m_dim]
    c_dir = eta_to_c(eta_dir, N)
    eval_dir = evaluate_candidate(c_dir, eta_dir, ell, M_plaque, kmat, N)

    # 3. Unit-drive Dirichlet-anchored (c1 = -1 and pi * L_cot = 1):
    # Minimize alpha^T M_plaque alpha s.t. 1^T alpha = 1 and pi * ell^T alpha = 1
    kkt_unit = [[ZERO for _ in range(m_dim + 2)] for _ in range(m_dim + 2)]
    for i in range(m_dim):
        for j in range(m_dim):
            kkt_unit[i][j] = M_plaque[i][j]
        kkt_unit[i][m_dim] = ONE
        kkt_unit[m_dim][i] = ONE
        kkt_unit[i][m_dim + 1] = PI * ell[i]
        kkt_unit[m_dim + 1][i] = PI * ell[i]
    rhs_unit = [ZERO] * m_dim + [ONE, ONE]
    sol_unit = lu_solve(kkt_unit, rhs_unit)
    eta_unit = sol_unit[:m_dim]
    c_unit = eta_to_c(eta_unit, N)
    eval_unit = evaluate_candidate(c_unit, eta_unit, ell, M_plaque, kmat, N)

    def fmt(d: Dict[str, mp.mpf]) -> Dict[str, str]:
        return {k: mp.nstr(v, 30) for k, v in d.items()}

    return {
        "N": N,
        "unconstrained": fmt(eval_opt),
        "dirichlet_anchored": fmt(eval_dir),
        "unit_drive_dirichlet": fmt(eval_unit),
    }


def main() -> None:
    t0 = time.time()
    max_n = max(N_GRID)
    kmat = build_unweighted_k_cot(max_n)
    delta = [ZERO] * (max_n + 1)
    for k in range(1, max_n + 1):
        delta[k] = vasyunin_cot_sum(k, 2) - vasyunin_cot_sum(k, 1)

    rows = []
    max_tel_err = ZERO
    max_scot_err = ZERO
    for N in N_GRID:
        res = solve_for_N(N, kmat, delta)
        rows.append(res)
        for key in ("unconstrained", "dirichlet_anchored", "unit_drive_dirichlet"):
            max_tel_err = max(max_tel_err, mp.mpf(res[key]["telescoping_abs_err"]))
            max_scot_err = max(max_scot_err, mp.mpf(res[key]["scot_identity_abs_err"]))

    payload = {
        "dps": mp.mp.dps,
        "no_rh_proof": True,
        "n_grid": N_GRID,
        "max_telescoping_abs_err": mp.nstr(max_tel_err, 12),
        "max_scot_identity_abs_err": mp.nstr(max_scot_err, 12),
        "elapsed_seconds": round(time.time() - t0, 3),
        "rows": rows,
    }
    out_path = ROOT_DIR / "layer_c_dirichlet_locked_plaque_results.json"
    out_path.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    print(f"Wrote {out_path.name} in {payload['elapsed_seconds']}s")
    print(f"Max 2D telescoping abs error: {payload['max_telescoping_abs_err']}")
    for r in rows:
        N = r["N"]
        eo = float(r["unconstrained"]["l2_energy"])
        ed = float(r["dirichlet_anchored"]["l2_energy"])
        eu = float(r["unit_drive_dirichlet"]["l2_energy"])
        pu = float(r["unit_drive_dirichlet"]["plaque"])
        c1o = float(r["unconstrained"]["c1"])
        print(
            f"N={N:2d} | c1_opt={c1o:8.5f} | E_opt={eo:.8f} | "
            f"E_dir={ed:.8f} | E_unit=P_unit={eu:.8f} (P={pu:.8f})"
        )


if __name__ == "__main__":
    main()
