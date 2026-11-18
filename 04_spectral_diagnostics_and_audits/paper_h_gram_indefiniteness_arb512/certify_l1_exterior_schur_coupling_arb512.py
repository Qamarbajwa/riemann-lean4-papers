#!/usr/bin/env python3
"""512-bit flint.arb Exterior Schur Coupling Audit (P650 <-> Q650) at L = 1, T = 400.

Task 1: Certifies and bounds the infinite-dimensional exterior Schur coupling between
the 12 dressed critical modes Z_tilde = Z_crit - X_bulk * Y in P_650 H and the
exterior space Q_650 H under B = Q_650 (K_400 + V + W) P_650 at L = 1, T = 400.

Governance & Invariants:
- NO_RH_PROOF = True
- FULL_POINT_L1 = 'NOT_ISSUED'
- PUBLICATION_STATUS = 'HOLD'
- Strictly read-only with respect to research/certification_v2/.
"""

from __future__ import annotations

from fractions import Fraction as F
import gzip
import hashlib
import json
from pathlib import Path
import sys
import time

import flint
from flint import arb, arb_mat, ctx, fmpq

sys.set_int_max_str_digits(50000)

REPO_ROOT = Path(__file__).resolve().parents[3]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from research.certification_v2.certified_legendre_rule import certify_rule
from research.certification_v2.compact_tail_bound import cutoff_tail_bound
from research.certification_v2.pole_compact_tail import pole_compact_bound
from research.interactive_lab.monograph_additive_multiplicative.certify_p650_and_critical_schur_arb512 import (
    q2arb,
    sha256_file,
)
from research.interactive_lab.monograph_additive_multiplicative.non_dilation_hilbert_comparison import (
    CERT_BETA_FRACTION,
    build_composite_gl_nodes,
    exact_archimedean_h,
    spherical_i_0f1,
    spherical_j_vector,
)

OUT_DIR = Path(__file__).resolve().parent
CERT_JSON_PATH = OUT_DIR / "l1_exterior_schur_coupling_arb512_certificate.json"

WORK_PREC_BITS = 512
ACTIVE_PRIME_POWERS = [(2, 2), (3, 3), (4, 2), (5, 5), (7, 7)]
COARSED_UNIFORM_ARCH_L_23_20 = F(20331, 10**16)
C_HYBRID = F(9, 10)
C_CANONICAL = F(1, 5)


def interval_pair_to_arb(pair: list[str]) -> arb:
    """Convert a rational [lo, hi] string pair into an enclosing flint.arb ball."""
    lo, hi = F(pair[0]), F(pair[1])
    mid = (lo + hi) / 2
    rad = (hi - lo) / 2
    return arb(fmpq(mid.numerator, mid.denominator), fmpq(rad.numerator, rad.denominator))


def arb_sci(val: arb, digits: int = 12) -> str:
    """Format a flint.arb midpoint as scientific string without float64 underflow."""
    return val.mid().str(digits, radius=False)


def arb_upper_sci(val: arb, digits: int = 12) -> str:
    """Format the upper endpoint of a flint.arb ball without float64 underflow."""
    return val.upper().str(digits, radius=False)


def arb_lower_sci(val: arb, digits: int = 12) -> str:
    """Format the lower endpoint of a flint.arb ball without float64 underflow."""
    return val.lower().str(digits, radius=False)


def arb_log10_upper(val: arb) -> float:
    """Return log10(|val|.upper()) cleanly even for magnitudes << 1e-308."""
    hi = abs(val).upper()
    if hi <= 0:
        return float("-inf")
    return float((hi.log() / arb(10).log()).upper())


def legendre_polys_on_ball(max_degree: int, x: arb) -> list[arb]:
    """Evaluate P_0(x), ..., P_{max_degree}(x) safely via 1536-bit midpoint recurrence + derivative bound.

    Uses the exact Markov/Legendre bound |P_k'(t)| <= k(k+1)/2 on [-1, 1] and
    1536-bit inner recurrence so zero interval recurrence wrapping occurs.
    """
    if float(abs(x).upper()) > 1.0 + 1e-12:
        raise ValueError(f"Legendre evaluation point outside [-1, 1]: {x}")
    x_mid = arb(x.mid())
    rad = abs(x - x_mid).upper()
    if max_degree == 0:
        return [arb(1)]
    with ctx.workprec(1536):
        xh = arb(x_mid)
        mids = [arb(1), xh]
        for k in range(1, max_degree):
            mids.append(((2 * k + 1) * xh * mids[-1] - k * mids[-2]) / (k + 1))
    out = [mids[0] + arb(0)]
    for k in range(1, max_degree + 1):
        rad_k = (arb(k) * arb(k + 1) / arb(2)) * rad
        out.append((mids[k] + arb(0)) + arb(0, rad_k.upper()))
    return out


def mat_frob_norm_sq(M: arb_mat) -> arb:
    """Return ||M||_F^2 = sum_{i,j} M_{ij}^2 in active Arb precision."""
    acc = arb(0)
    for i in range(M.nrows()):
        for j in range(M.ncols()):
            acc += M[i, j] * M[i, j]
    return acc


def load_midpoint_mat(entries: list) -> arb_mat:
    """Build exact midpoint flint.arb_mat from a 2D array of [lo, hi] rational string intervals."""
    rows = len(entries)
    cols = len(entries[0])
    M = arb_mat(rows, cols)
    for i in range(rows):
        for j in range(cols):
            lo, hi = F(entries[i][j][0]), F(entries[i][j][1])
            M[i, j] = q2arb((lo + hi) / 2)
    return M


def run_interval_ldlt_6x6(S: arb_mat, sector_name: str, sector_offset: int) -> dict:
    """Compute rigorous 512-bit interval LDL^T decomposition of a 6x6 symmetric matrix."""
    n = 6
    L = arb_mat(n, n)
    D: list[arb] = [arb(0)] * n
    pivots: list[dict] = []
    aborted = False
    for j in range(n):
        L[j, j] = arb(1)
        d = S[j, j] - sum((L[j, m] ** 2 * D[m] for m in range(j)), arb(0))
        D[j] = d
        lo_val = float(d.lower())
        hi_val = float(d.upper())
        mid_val = float(d.mid())
        rad_val = float(d.rad())
        strictly_pos = bool(d.lower() > 0) and not aborted
        pivots.append(
            {
                "mode_index": sector_offset + j + 1,
                "parity": sector_name,
                "pivot_mid": mid_val,
                "pivot_rad": rad_val,
                "pivot_lower": lo_val,
                "pivot_upper": hi_val,
                "pivot_mid_sci": arb_sci(d),
                "pivot_lower_sci": arb_lower_sci(d),
                "strictly_positive": bool(d.lower() > 0) if not aborted else False,
            }
        )
        if not (d.lower() > 0) or d.contains(0):
            aborted = True
            for rem in range(j + 1, n):
                pivots.append(
                    {
                        "mode_index": sector_offset + rem + 1,
                        "parity": sector_name,
                        "pivot_mid": None,
                        "pivot_rad": None,
                        "pivot_lower": None,
                        "pivot_upper": None,
                        "pivot_mid_sci": "ABORTED_AT_NONPOSITIVE_PIVOT",
                        "pivot_lower_sci": "ABORTED_AT_NONPOSITIVE_PIVOT",
                        "strictly_positive": False,
                    }
                )
            break
        for i in range(j + 1, n):
            L[i, j] = (S[i, j] - sum((L[i, m] * L[j, m] * D[m] for m in range(j)), arb(0))) / d

    pos_count = sum(1 for p in pivots if p["strictly_positive"])
    neg_candidates = sum(1 for p in pivots if p["pivot_upper"] is not None and p["pivot_upper"] < 0)
    min_lower = min((p["pivot_lower"] for p in pivots if p["pivot_lower"] is not None), default=float("nan"))
    return {
        "sector": sector_name,
        "pos_count": pos_count,
        "all_pivots_positive": (not aborted and pos_count == n),
        "aborted_on_nonpositive_pivot": aborted,
        "definite_negative_pivot_detected": neg_candidates > 0,
        "min_pivot_lower": min_lower,
        "pivots": pivots,
    }


def run_interval_ldlt_nxn_positive(S: arb_mat) -> tuple[bool, int, float]:
    """Compute 512-bit interval LDL^T positivity for an n x n symmetric matrix."""
    n = S.nrows()
    L = arb_mat(n, n)
    D: list[arb] = [arb(0)] * n
    pos_count = 0
    min_lower = float("inf")
    for j in range(n):
        L[j, j] = arb(1)
        s = arb(0)
        for m in range(j):
            s += (L[j, m] ** 2) * D[m]
        d = S[j, j] - s
        D[j] = d
        lo_val = float(d.lower())
        if lo_val < min_lower:
            min_lower = lo_val
        if not (d.lower() > 0) or d.contains(0):
            return False, pos_count, min_lower
        pos_count += 1
        for i in range(j + 1, n):
            s_ij = arb(0)
            for m in range(j):
                s_ij += L[i, m] * L[j, m] * D[m]
            L[i, j] = (S[i, j] - s_ij) / d
    return True, pos_count, min_lower


def summarize_legendre_decay(Z_mat: arb_mat, label: str) -> dict:
    """Measure coefficient decay of a 650 x 6 basis across Legendre degree windows."""
    windows = [
        ("0_49", 0, 50),
        ("50_499", 50, 500),
        ("500_599", 500, 600),
        ("600_649", 600, 650),
    ]
    out = {"label": label, "frob_norm": float(mat_frob_norm_sq(Z_mat).sqrt()), "windows": {}}
    for wname, d0, d1 in windows:
        max_abs = arb(0)
        energy_sq = arb(0)
        for d in range(d0, d1):
            for k in range(Z_mat.ncols()):
                v = abs(Z_mat[d, k])
                if v > max_abs:
                    max_abs = v
                energy_sq += Z_mat[d, k] ** 2
        out["windows"][wname] = {
            "max_abs_coeff": float(max_abs.upper()),
            "l2_frob_norm": float(energy_sq.sqrt().upper()),
            "l2_frob_norm_sci": arb_upper_sci(energy_sq.sqrt()),
        }
    return out


def compute_dressed_critical_basis(
    direct_dir: Path, repair_dir: Path, p650_dir: Path
) -> tuple[dict, arb_mat, arb_mat, arb_mat, arb_mat, list[arb_mat], list[arb_mat]]:
    """Step 1: Solve Y = A_BB^{-1} A_BC in 512-bit Arb, form Z_tilde, and record decay."""
    comp = json.loads((direct_dir / "CRITICAL_COMPOSITION_WRITER.json").read_text(encoding="utf-8"))
    boxes = comp["boxes"]
    coarse_penalty = F(comp["bulk_solve_penalty"])
    bulk_rc = json.loads((repair_dir / "BULK_SPLIT_RECEIPT.json").read_text(encoding="utf-8"))
    lambda_min_bulk_lower = F(bulk_rc["bulk_gershgorin_lower_bound"])

    schur_entries = json.loads(gzip.decompress((p650_dir / "SCHUR_LOWER.json.gz").read_bytes()).decode("utf-8"))
    columns = [
        list(map(F, col))
        for col in json.loads(gzip.decompress((repair_dir / "FULL_DYADIC_SPLIT_BASIS.json.gz").read_bytes()).decode("utf-8"))
    ]

    M_schur_mid = load_midpoint_mat(schur_entries)

    Z_bare_secs: list[arb_mat] = []
    Z_tilde_secs: list[arb_mat] = []
    S_crit_secs: list[arb_mat] = []
    X_bulk_secs: list[arb_mat] = []
    A_BB_secs: list[arb_mat] = []
    A_BC_secs: list[arb_mat] = []
    A_CC_secs: list[arb_mat] = []
    Y_bulk_secs: list[arb_mat] = []
    sector_summaries: list[dict] = []

    for sector in range(2):
        sec_name = ["even", "odd"][sector]
        bulk_cols = columns[12:331] if sector == 0 else columns[331:650]
        crit_cols = columns[0:6] if sector == 0 else columns[6:12]
        idx = list(range(0, 6)) if sector == 0 else list(range(6, 12))

        X_bulk = arb_mat([[q2arb(bulk_cols[j][i]) for j in range(len(bulk_cols))] for i in range(650)])
        Z_crit = arb_mat([[q2arb(crit_cols[j][i]) for j in range(6)] for i in range(650)])

        A_BB = X_bulk.transpose() * M_schur_mid * X_bulk
        A_BC = X_bulk.transpose() * M_schur_mid * Z_crit

        t0 = time.time()
        Y = A_BB.solve(A_BC)
        t_solve = time.time() - t0

        R = A_BB * Y - A_BC
        max_r = max(abs(R[i, j].upper()) for i in range(319) for j in range(6))
        frob_r_sq = (319 * 6) * (max_r ** 2)
        delta_quad = frob_r_sq / q2arb(lambda_min_bulk_lower)

        dressing_shift = X_bulk * Y
        Z_tilde = Z_crit - dressing_shift

        A_CC = arb_mat(6, 6)
        for i in range(6):
            for j in range(6):
                lo, hi = F(boxes[idx[i]][idx[j]][0]), F(boxes[idx[i]][idx[j]][1])
                mid = (lo + hi) / 2
                rad = (hi - lo) / 2
                if i == j:
                    mid += coarse_penalty
                A_CC[i, j] = arb(fmpq(mid.numerator, mid.denominator), fmpq(rad.numerator, rad.denominator))

        G_bulk = A_BC.transpose() * Y
        eye6 = arb_mat([[arb(1 if i == j else 0) for j in range(6)] for i in range(6)])
        S_crit = A_CC - G_bulk - delta_quad * eye6

        y_frob = mat_frob_norm_sq(Y).sqrt()
        shift_frob = mat_frob_norm_sq(dressing_shift).sqrt()
        zt_frob = mat_frob_norm_sq(Z_tilde).sqrt()

        bare_decay = summarize_legendre_decay(Z_crit, f"{sec_name}_bare_Z_crit")
        dressed_decay = summarize_legendre_decay(Z_tilde, f"{sec_name}_dressed_Z_tilde")

        Z_bare_secs.append(Z_crit)
        Z_tilde_secs.append(Z_tilde)
        S_crit_secs.append(S_crit)
        X_bulk_secs.append(X_bulk)
        A_BB_secs.append(A_BB)
        A_BC_secs.append(A_BC)
        A_CC_secs.append(A_CC)
        Y_bulk_secs.append(Y)
        sector_summaries.append(
            {
                "sector": sec_name,
                "solve_time_seconds": t_solve,
                "Y_frob_norm": float(y_frob.upper()),
                "Y_frob_norm_sci": arb_sci(y_frob),
                "dressing_shift_frob_norm": float(shift_frob.upper()),
                "dressing_shift_frob_norm_sci": arb_sci(shift_frob),
                "Z_tilde_frob_norm": float(zt_frob.upper()),
                "delta_quad_upper_sci": arb_upper_sci(delta_quad),
                "delta_quad_log10": arb_log10_upper(delta_quad),
                "bare_legendre_decay": bare_decay,
                "dressed_legendre_decay": dressed_decay,
            }
        )

    # Concatenate into 650 x 12 matrices
    Z_bare_12 = arb_mat(650, 12)
    Z_tilde_12 = arb_mat(650, 12)
    for d in range(650):
        for k in range(6):
            Z_bare_12[d, k] = Z_bare_secs[0][d, k]
            Z_bare_12[d, 6 + k] = Z_bare_secs[1][d, k]
            Z_tilde_12[d, k] = Z_tilde_secs[0][d, k]
            Z_tilde_12[d, 6 + k] = Z_tilde_secs[1][d, k]

    step1_info = {
        "status": "VERIFIED_DECAY_PROFILE",
        "total_Z_tilde_frob_norm": float(mat_frob_norm_sq(Z_tilde_12).sqrt().upper()),
        "sectors": sector_summaries,
    }
    bulk_blocks = {
        "X_bulk_secs": X_bulk_secs,
        "Z_bare_secs": Z_bare_secs,
        "A_BB_secs": A_BB_secs,
        "A_BC_secs": A_BC_secs,
        "A_CC_secs": A_CC_secs,
        "Y_bulk_secs": Y_bulk_secs,
        "lambda_min_bulk_lower": lambda_min_bulk_lower,
    }
    return step1_info, M_schur_mid, Z_bare_12, Z_tilde_12, S_crit_secs[0], S_crit_secs[1], Z_tilde_secs, bulk_blocks


def certify_pole_exterior_leakage(Z_tilde_12: arb_mat, ztilde_frob: arb, wr: dict) -> dict:
    """Step 2.1: Bound ||Q_650 W Z_tilde||_F in 512-bit Arb + explicit rank-2 exterior band."""
    pole_650 = q2arb(F(wr["pole_delta"]["pole_delta_upper"]))
    pole_32 = q2arb(F(wr["pole_truncation_delta32"]))
    pole_670 = q2arb(F(pole_compact_bound(F(1), 670)["pole_delta_upper"]))

    # Direct evaluation of W on P_650 (first 650 coeffs) and exterior band n in [650, 670)
    # W = 2 |cosh(x/2)><cosh(x/2)| - 2 |sinh(x/2)><sinh(x/2)|, where
    # <phi_n, cosh(x/2)> = sqrt(2(2n+1)) i_n(1/2) (even n)
    # <phi_n, sinh(x/2)> = sqrt(2(2n+1)) i_n(1/2) (odd n)
    half = arb("0.5")
    c_coeffs = [arb(2 * (2 * n + 1)).sqrt() * spherical_i_0f1(n, half) if n % 2 == 0 else arb(0) for n in range(670)]
    s_coeffs = [arb(2 * (2 * n + 1)).sqrt() * spherical_i_0f1(n, half) if n % 2 == 1 else arb(0) for n in range(670)]

    # Inner products <c, z_k> and <s, z_k> for k=0..11
    c_dot_z = [sum((c_coeffs[d] * Z_tilde_12[d, k] for d in range(0, 650, 2)), arb(0)) for k in range(12)]
    s_dot_z = [sum((s_coeffs[d] * Z_tilde_12[d, k] for d in range(1, 650, 2)), arb(0)) for k in range(12)]

    band_frob_sq = arb(0)
    for n in range(650, 670):
        coeff_n = c_coeffs[n] if n % 2 == 0 else s_coeffs[n]
        sign = arb(2) if n % 2 == 0 else arb(-2)
        for k in range(12):
            proj_dot = c_dot_z[k] if n % 2 == 0 else s_dot_z[k]
            band_frob_sq += (sign * coeff_n * proj_dot) ** 2

    directed_band_frob = band_frob_sq.sqrt()
    tail_670_bound = pole_670 * ztilde_frob
    uniform_650_bound = pole_650 * ztilde_frob

    return {
        "uniform_operator_delta_650_sci": arb_upper_sci(pole_650),
        "uniform_operator_delta_650_log10": arb_log10_upper(pole_650),
        "pole_truncation_delta_32_sci": arb_upper_sci(pole_32),
        "uniform_W_Z_tilde_frob_upper_sci": arb_upper_sci(uniform_650_bound),
        "uniform_W_Z_tilde_frob_log10": arb_log10_upper(uniform_650_bound),
        "directed_band_650_669_frob_sci": arb_upper_sci(directed_band_frob),
        "directed_band_650_669_log10": arb_log10_upper(directed_band_frob),
        "tail_670_operator_upper_sci": arb_upper_sci(tail_670_bound),
        "tail_670_log10": arb_log10_upper(tail_670_bound),
        "penalty_c0_20_upper_sci": arb_upper_sci((uniform_650_bound ** 2) / arb("0.2")),
        "penalty_c0_20_log10": arb_log10_upper((uniform_650_bound ** 2) / arb("0.2")),
    }


def _compute_arch_band_projections(
    Z_tilde_secs: list[arb_mat], n_ext_max: int, density_scale: int
) -> tuple[arb_mat, arb_mat]:
    """Compute Q_{[650, n_ext_max)} K_400 Z_tilde on composite GL nodes for both sectors."""
    t_nodes, w_nodes, h_nodes = build_composite_gl_nodes(400.0, density_scale=density_scale)
    beta_arb = q2arb(CERT_BETA_FRACTION)
    pref = arb(2) / arb.pi()

    even_in = list(range(0, 650, 2))
    odd_in = list(range(1, 650, 2))
    even_ext = list(range(650, n_ext_max, 2))
    odd_ext = list(range(651, n_ext_max, 2))

    s_even_in = [arb(1 if (d // 2) % 2 == 0 else -1) * arb(2 * d + 1).sqrt() for d in even_in]
    s_odd_in = [arb(1 if (d // 2) % 2 == 0 else -1) * arb(2 * d + 1).sqrt() for d in odd_in]
    s_even_ext = [arb(1 if (d // 2) % 2 == 0 else -1) * arb(2 * d + 1).sqrt() for d in even_ext]
    s_odd_ext = [arb(1 if (d // 2) % 2 == 0 else -1) * arb(2 * d + 1).sqrt() for d in odd_ext]

    Z_ev_weighted = arb_mat([[Z_tilde_secs[0][d, k] * s_even_in[c] for k in range(6)] for c, d in enumerate(even_in)])
    Z_od_weighted = arb_mat([[Z_tilde_secs[1][d, k] * s_odd_in[c] for k in range(6)] for c, d in enumerate(odd_in)])

    num_pts = len(t_nodes)
    J_in_ev = arb_mat(num_pts, len(even_in))
    J_in_od = arb_mat(num_pts, len(odd_in))
    J_ex_ev = arb_mat(num_pts, len(even_ext))
    J_ex_od = arb_mat(num_pts, len(odd_ext))

    for m_idx, (t_m, w_m, h_m) in enumerate(zip(t_nodes, w_nodes, h_nodes)):
        jv = spherical_j_vector(n_ext_max, t_m)
        ker = w_m * (h_m - beta_arb)
        for c, d in enumerate(even_in):
            J_in_ev[m_idx, c] = jv[d]
        for c, d in enumerate(odd_in):
            J_in_od[m_idx, c] = jv[d]
        for c, d in enumerate(even_ext):
            J_ex_ev[m_idx, c] = ker * s_even_ext[c] * jv[d]
        for c, d in enumerate(odd_ext):
            J_ex_od[m_idx, c] = ker * s_odd_ext[c] * jv[d]

    wave_ev = J_in_ev * Z_ev_weighted
    wave_od = J_in_od * Z_od_weighted
    return pref * (J_ex_ev.transpose() * wave_ev), pref * (J_ex_od.transpose() * wave_od)


def certify_archimedean_exterior_leakage(
    Z_tilde_secs: list[arb_mat], ztilde_frob: arb, M_sym: F, wr: dict
) -> dict:
    """Step 2.2: Bound ||Q_650 K_400 Z_tilde||_F uniformly & via directed Bessel band [650, 666)."""
    arch_650_uni = q2arb(F(wr["compact_delta650"]))
    scc = q2arb(F(wr["scalar_coupling_correction"]))
    arch_coarse_23_20 = q2arb(COARSED_UNIFORM_ARCH_L_23_20)

    t0 = time.time()
    B_ev_1, B_od_1 = _compute_arch_band_projections(Z_tilde_secs, n_ext_max=666, density_scale=1)
    B_ev_2, B_od_2 = _compute_arch_band_projections(Z_tilde_secs, n_ext_max=666, density_scale=2)
    t_band = time.time() - t0

    diff_ev = max(abs(B_ev_1[i, j] - B_ev_2[i, j]).upper() for i in range(B_ev_1.nrows()) for j in range(6))
    diff_od = max(abs(B_od_1[i, j] - B_od_2[i, j]).upper() for i in range(B_od_1.nrows()) for j in range(6))
    quad_doubling_diff = max(diff_ev, diff_od)

    band_even_frob = mat_frob_norm_sq(B_ev_1).sqrt()
    band_odd_frob = mat_frob_norm_sq(B_od_1).sqrt()
    band_total_frob = (band_even_frob ** 2 + band_odd_frob ** 2).sqrt() + q2arb(F(16 * 12)) * quad_doubling_diff

    tail_666_op = q2arb(F(cutoff_tail_bound(1, 400, 666, M_sym)["arch_compact_delta_upper"]))
    tail_666_on_ztilde = tail_666_op * ztilde_frob
    directed_plus_tail_frob = (band_total_frob ** 2 + tail_666_on_ztilde ** 2).sqrt()

    uniform_650_on_ztilde = arch_650_uni * ztilde_frob
    c_can = q2arb(C_CANONICAL)

    modewise_norms_sci = []
    for k in range(6):
        col_sq = sum(B_ev_1[i, k] ** 2 for i in range(B_ev_1.nrows()))
        modewise_norms_sci.append(arb_upper_sci(col_sq.sqrt(), 6))
    for k in range(6):
        col_sq = sum(B_od_1[i, k] ** 2 for i in range(B_od_1.nrows()))
        modewise_norms_sci.append(arb_upper_sci(col_sq.sqrt(), 6))

    return {
        "band_eval_time_seconds": t_band,
        "quadrature_doubling_max_diff_sci": arb_upper_sci(quad_doubling_diff),
        "directed_band_650_665_even_frob_sci": arb_upper_sci(band_even_frob),
        "directed_band_650_665_odd_frob_sci": arb_upper_sci(band_odd_frob),
        "directed_band_650_665_total_frob_sci": arb_upper_sci(band_total_frob),
        "directed_band_650_665_modewise_sci": modewise_norms_sci,
        "tail_666_uniform_op_upper_sci": arb_upper_sci(tail_666_op),
        "tail_666_on_Z_tilde_upper_sci": arb_upper_sci(tail_666_on_ztilde),
        "directed_total_arch_Z_tilde_frob_upper_sci": arb_upper_sci(directed_plus_tail_frob),
        "directed_penalty_c0_20_upper_sci": arb_upper_sci((directed_plus_tail_frob ** 2) / c_can),
        "uniform_delta_650_L1_sci": arb_upper_sci(arch_650_uni),
        "uniform_delta_650_on_Z_tilde_upper_sci": arb_upper_sci(uniform_650_on_ztilde),
        "uniform_L1_penalty_c0_20_upper_sci": arb_upper_sci((uniform_650_on_ztilde ** 2) / c_can),
        "scalar_coupling_correction_L1_sci": arb_upper_sci(scc),
        "coarse_uniform_L_le_23_20_op_norm": float(arch_coarse_23_20),
        "coarse_uniform_L_le_23_20_penalty_c0_20": float((arch_coarse_23_20 ** 2) / c_can),
    }


def _evaluate_weighted_legendre_matrix(
    x_balls: list[arb], max_degree: int
) -> arb_mat:
    """Return matrix Phi[q, d] = phi_d(x_q) = sqrt((2d+1)/2) * P_d(x_q)."""
    num_q = len(x_balls)
    sqrt_factors = [(arb(2 * d + 1) / arb(2)).sqrt() for d in range(max_degree + 1)]
    Phi = arb_mat(num_q, max_degree + 1)
    for q_idx, x_q in enumerate(x_balls):
        p_vals = legendre_polys_on_ball(max_degree, x_q)
        for d in range(max_degree + 1):
            Phi[q_idx, d] = sqrt_factors[d] * p_vals[d]
    return Phi


def certify_spatial_exterior_leakage(
    Z_bare_12: arb_mat,
    Z_tilde_12: arb_mat,
    p650_dir: Path,
    direct_dir: Path,
    batch_gram_dir: Path,
    wr: dict,
) -> tuple[dict, arb_mat, arb_mat]:
    """Step 2.3: Exact 512-bit 11-cell Parseval & [650, 750) band audit of Q_650 V Z_tilde."""
    t0 = time.time()
    # 512-bit+ certified GL700 is algebraically exact through degree 1399 >= 649 + 749 = 1398.
    rule700 = certify_rule(700, bits=640, bracket_bits=560, newton_steps=11)
    if rule700["status"] != "CERTIFIED_GAUSS_LEGENDRE_RULE_BOXES":
        raise RuntimeError(f"GL700 rule certification failed: {rule700['status']}")
    nodes_base = [interval_pair_to_arb(item["node"]) for item in rule700["nodes_weights"]]
    weights_base = [interval_pair_to_arb(item["weight"]) for item in rule700["nodes_weights"]]

    arith = json.loads((direct_dir / "ARITHMETIC_RECEIPT.json").read_text(encoding="utf-8"))
    partitions = arith["partitions"]

    # Pack 24 columns: [0..11] = Z_bare_12, [12..23] = Z_tilde_12
    U_24 = arb_mat(650, 24)
    for d in range(650):
        for k in range(12):
            U_24[d, k] = Z_bare_12[d, k]
            U_24[d, 12 + k] = Z_tilde_12[d, k]

    # Precompute 10 shifts and coefficients matching ARITHMETIC_RECEIPT active_images ordering:
    # index 2*idx:   -ln(n) active for x in [ln(n)-1, 1]   (eval u(x - ln n))
    # index 2*idx+1: +ln(n) active for x in [-1, 1-ln(n)]  (eval u(x + ln n))
    log_n = {n: arb(n).log() for n, _ in ACTIVE_PRIME_POWERS}
    img_shifts: list[tuple[arb, arb]] = []
    for n, p_base in ACTIVE_PRIME_POWERS:
        ln_n = log_n[n]
        coef = -(arb(p_base).log() / arb(n).sqrt())
        img_shifts.append((-ln_n, coef))
        img_shifts.append((+ln_n, coef))

    # 1. Exact full L^2([-1, 1]) Gram <V U, V U> across all 11 open support cells
    full_V_gram = arb_mat(24, 24)
    for cell in partitions:
        lo_c = interval_pair_to_arb(cell["lo"])
        hi_c = interval_pair_to_arb(cell["hi"])
        mid_c = (lo_c + hi_c) / 2
        half_c = (hi_c - lo_c) / 2
        active = cell["active_images"]
        if not active:
            continue

        V_cell = arb_mat(700, 24)
        for img_idx in active:
            shift, coef = img_shifts[img_idx]
            y_pts = [mid_c + half_c * xi + shift for xi in nodes_base]
            Phi_y = _evaluate_weighted_legendre_matrix(y_pts, 649)
            V_cell += coef * (Phi_y * U_24)

        W_V_cell = arb_mat(700, 24)
        for q_idx in range(700):
            w_phys = half_c * weights_base[q_idx]
            for c_idx in range(24):
                W_V_cell[q_idx, c_idx] = w_phys * V_cell[q_idx, c_idx]
        full_V_gram += V_cell.transpose() * W_V_cell

    # 2. Exact P_750 V U on the 5 active prime-power overlap intervals [ln(n)-1, 1]
    P750_V_U = arb_mat(750, 24)
    for n, p_base in ACTIVE_PRIME_POWERS:
        ln_n = log_n[n]
        coef = -(arb(p_base).log() / arb(n).sqrt())
        lo_ov = ln_n - arb(1)
        hi_ov = arb(1)
        mid_ov = (lo_ov + hi_ov) / 2
        half_ov = (hi_ov - lo_ov) / 2

        x_pts = [mid_ov + half_ov * xi for xi in nodes_base]
        y_pts = [x_q - ln_n for x_q in x_pts]

        Phi_x_750 = _evaluate_weighted_legendre_matrix(x_pts, 749)  # 700 x 750
        Phi_y_750 = _evaluate_weighted_legendre_matrix(y_pts, 749)  # 700 x 750

        Phi_x_650 = arb_mat([[Phi_x_750[q, d] for d in range(650)] for q in range(700)])
        Phi_y_650 = arb_mat([[Phi_y_750[q, d] for d in range(650)] for q in range(700)])

        UX = Phi_x_650 * U_24  # u(x)
        UY = Phi_y_650 * U_24  # u(x - ln n)
        W_UY = arb_mat(700, 24)
        W_UX = arb_mat(700, 24)
        for q_idx in range(700):
            w_phys = half_ov * weights_base[q_idx]
            for c_idx in range(24):
                W_UY[q_idx, c_idx] = w_phys * UY[q_idx, c_idx]
                W_UX[q_idx, c_idx] = w_phys * UX[q_idx, c_idx]

        P750_V_U += coef * (Phi_x_750.transpose() * W_UY + Phi_y_750.transpose() * W_UX)

    # Extract 650 and [650, 750) blocks cleanly
    C650_bare = arb_mat([[P750_V_U[d, k] for k in range(12)] for d in range(650)])
    C650_dressed = arb_mat([[P750_V_U[d, 12 + k] for k in range(12)] for d in range(650)])
    Band_dressed = arb_mat([[P750_V_U[d, 12 + k] for k in range(12)] for d in range(650, 750)])

    def subblock(M: arb_mat, r0: int, c0: int, sz: int = 12) -> arb_mat:
        return arb_mat([[M[r0 + i, c0 + j] for j in range(sz)] for i in range(sz)])

    VV_bare = subblock(full_V_gram, 0, 0)
    VV_dressed = subblock(full_V_gram, 12, 12)

    G_V_bare = VV_bare - C650_bare.transpose() * C650_bare
    G_V_dressed = VV_dressed - C650_dressed.transpose() * C650_dressed
    G_band_dressed = Band_dressed.transpose() * Band_dressed
    G_tail750_dressed = G_V_dressed - G_band_dressed

    # Cross-checks against frozen V2 receipts (without modifying them)
    q650vz_ref = arith["entries"]["Q650VZ_gram"]
    max_bare_ref_diff = arb(0)
    for i in range(12):
        for j in range(12):
            ref_ij = interval_pair_to_arb(q650vz_ref[i][j])
            d_ij = abs(G_V_bare[i, j] - ref_ij).upper()
            if d_ij > max_bare_ref_diff:
                max_bare_ref_diff = d_ij

    gv_650 = json.loads((batch_gram_dir / "d650_RECEIPT.json").read_text(encoding="utf-8"))["entries"]
    GV_650_mid = load_midpoint_mat(gv_650)
    G_V_dressed_from_650 = Z_tilde_12.transpose() * GV_650_mid * Z_tilde_12
    max_dressed_vs_650_diff = max(
        abs(G_V_dressed[i, j] - G_V_dressed_from_650[i, j]).upper()
        for i in range(12)
        for j in range(12)
    )

    M_finite_raw = json.loads(gzip.decompress((p650_dir / "FINITE_LOWER.json.gz").read_bytes()).decode("utf-8"))
    M_schur_raw = json.loads(gzip.decompress((p650_dir / "SCHUR_LOWER.json.gz").read_bytes()).decode("utf-8"))
    M_finite_mid = load_midpoint_mat(M_finite_raw)
    M_schur_mid = load_midpoint_mat(M_schur_raw)
    D_ext_mid = M_finite_mid - M_schur_mid
    P_ext_dressed_from_diff = Z_tilde_12.transpose() * D_ext_mid * Z_tilde_12

    young_090 = q2arb((1 + F(wr["epsilon"])) / C_HYBRID)
    scc = q2arb(F(wr["scalar_coupling_correction"]))
    ZtZ = Z_tilde_12.transpose() * Z_tilde_12
    P_ext_dressed_parseval = young_090 * G_V_dressed + scc * ZtZ
    max_schur_diff_vs_parseval = max(
        abs(P_ext_dressed_from_diff[i, j] - P_ext_dressed_parseval[i, j]).upper()
        for i in range(12)
        for j in range(12)
    )

    dressing_delta = G_V_dressed - G_V_bare
    dressing_delta_frob = mat_frob_norm_sq(dressing_delta).sqrt()

    band_energy_tr = sum((G_band_dressed[k, k] for k in range(12)), arb(0))
    total_energy_tr = sum((G_V_dressed[k, k] for k in range(12)), arb(0))
    tail_energy_tr = sum((G_tail750_dressed[k, k] for k in range(12)), arb(0))
    band_fraction = float((band_energy_tr / total_energy_tr).mid())

    diag_dressed = [float(G_V_dressed[k, k].mid()) for k in range(12)]
    diag_band_650_749 = [float(G_band_dressed[k, k].mid()) for k in range(12)]
    diag_tail_750_plus = [float(G_tail750_dressed[k, k].mid()) for k in range(12)]

    spatial_info = {
        "eval_time_seconds": time.time() - t0,
        "gl_degree_exact": 700,
        "gl_exactness_polynomial_degree": 1399,
        "max_overlap_product_degree": 1398,
        "bare_G_V_frob_norm": float(mat_frob_norm_sq(G_V_bare).sqrt().upper()),
        "dressed_G_V_frob_norm": float(mat_frob_norm_sq(G_V_dressed).sqrt().upper()),
        "dressing_delta_G_V_frob_norm": float(dressing_delta_frob.upper()),
        "dressing_delta_G_V_frob_norm_sci": arb_upper_sci(dressing_delta_frob),
        "max_diff_bare_vs_ARITHMETIC_RECEIPT": float(max_bare_ref_diff),
        "max_diff_dressed_vs_650x650_GV": float(max_dressed_vs_650_diff),
        "max_diff_dressed_penalty_vs_FINITE_minus_SCHUR": float(max_schur_diff_vs_parseval),
        "trace_Q650_V_Z_tilde_sq": float(total_energy_tr.mid()),
        "trace_Q650_750_band_sq": float(band_energy_tr.mid()),
        "trace_Q750_inf_tail_sq": float(tail_energy_tr.mid()),
        "band_650_749_fraction_of_exterior_energy": band_fraction,
        "mode_diag_G_V_dressed": diag_dressed,
        "mode_diag_band_650_749": diag_band_650_749,
        "mode_diag_tail_750_inf": diag_tail_750_plus,
        "G_V_dressed_diag_rad_max_sci": arb_upper_sci(max(G_V_dressed[k, k].rad() for k in range(12))),
    }
    return spatial_info, G_V_dressed, G_band_dressed, G_tail750_dressed, P_ext_dressed_parseval


def evaluate_schur_configurations(
    S_even: arb_mat,
    S_odd: arb_mat,
    Z_tilde_12: arb_mat,
    G_V_dressed: arb_mat,
    P_ext_dressed_090: arb_mat,
    wr: dict,
    M_sym: F,
    directed_arch_frob_upper_sci: str,
) -> dict:
    """Step 2.4: Certify 12-pivot interval LDL^T across exterior Schur regimes."""

    def sec_block(M12: arb_mat, sec: int) -> arb_mat:
        off = 0 if sec == 0 else 6
        return arb_mat([[M12[off + i, off + j] for j in range(6)] for i in range(6)])

    def run_pair(name: str, M_ev: arb_mat, M_od: arb_mat) -> dict:
        r_ev = run_interval_ldlt_6x6(M_ev, "even", 0)
        r_od = run_interval_ldlt_6x6(M_od, "odd", 6)
        all_p = r_ev["pivots"] + r_od["pivots"]
        pos_c = r_ev["pos_count"] + r_od["pos_count"]
        min_lo = min(r_ev["min_pivot_lower"], r_od["min_pivot_lower"])
        return {
            "config_name": name,
            "all_12_pivots_positive": (r_ev["all_pivots_positive"] and r_od["all_pivots_positive"] and pos_c == 12),
            "pos_count": pos_c,
            "min_pivot_lower": min_lo,
            "sectors": [r_ev, r_od],
            "all_pivots": all_p,
        }

    eye6 = arb_mat([[arb(1 if i == j else 0) for j in range(6)] for i in range(6)])
    young_090 = q2arb((1 + F(wr["epsilon"])) / C_HYBRID)
    young_020 = q2arb((1 + F(wr["epsilon"])) / C_CANONICAL)

    P_ev_090 = sec_block(P_ext_dressed_090, 0)
    P_od_090 = sec_block(P_ext_dressed_090, 1)

    # Config 1: Pure finite P_650 Schur complement (recovering state before Q_650 subtraction)
    cfg_pure_finite = run_pair("pure_finite_P650_schur", S_even + P_ev_090, S_odd + P_od_090)

    # Config 2: Certified Lower-Hybrid H_h infinite-dimensional Schur (c = 0.90)
    cfg_hybrid = run_pair("full_H_h_c_0_90", S_even, S_odd)

    # Config 3: H_h with canonical c = 0.20 Archimedean + Pole L = 1 exterior penalty
    zt_frob_sq = mat_frob_norm_sq(Z_tilde_12)
    delta_arch_650 = q2arb(F(wr["compact_delta650"]))
    delta_pole_650 = q2arb(F(wr["pole_delta"]["pole_delta_upper"]))
    # Note: S_crit already includes (1 + 1/eps)/0.90 * (delta_arch_650 + delta_pole_650)^2 * ZtZ.
    # Conservatively subtract the full c = 0.20 Archimedean+Pole Schur penalty without crediting the 0.90 scalar term:
    pen_arch_pole_uni = (((delta_arch_650 + delta_pole_650) ** 2) * zt_frob_sq) / arb("0.2")
    cfg_L1_uni = run_pair(
        "H_h_with_canonical_c_0_20_arch_pole_L1",
        S_even - pen_arch_pole_uni * eye6,
        S_odd - pen_arch_pole_uni * eye6,
    )
    cfg_L1_uni["subtracted_scalar_penalty_sci"] = arb_upper_sci(pen_arch_pole_uni)

    # Config 4: H_h with coarse uniform L <= 23/20 Archimedean penalty at c = 0.20 (2.066748e-23)
    pen_coarse_arch = (q2arb(COARSED_UNIFORM_ARCH_L_23_20) ** 2) / arb("0.2")
    cfg_coarse = run_pair(
        "H_h_with_coarse_L_le_23_20_arch_c_0_20",
        S_even - pen_coarse_arch * eye6,
        S_odd - pen_coarse_arch * eye6,
    )
    cfg_coarse["subtracted_scalar_penalty"] = float(pen_coarse_arch.upper())

    # Config 5 (Diagnostic only): Scaling H_h's spatial exterior penalty from c=0.90 to c=0.20
    # without switching operator from H_h to canonical A(1).
    delta_young = young_020 - young_090
    GV_ev = sec_block(G_V_dressed, 0)
    GV_od = sec_block(G_V_dressed, 1)
    cfg_diag_020 = run_pair(
        "diagnostic_uncompensated_H_h_spatial_scaled_to_c_0_20",
        S_even - delta_young * GV_ev - pen_arch_pole_uni * eye6,
        S_odd - delta_young * GV_od - pen_arch_pole_uni * eye6,
    )

    return {
        "quotient_identity_summary": (
            "SCHUR_LOWER and CRITICAL_COMPOSITION_WRITER already eliminate infinite Q_650 H "
            "at lower-hybrid exterior floor c = 0.90 via -(1+eps)/0.90 * G_V - scalar_correction * I; "
            "pure finite P_650 Schur complement equals S_crit + Z_tilde^T D_ext(0.90) Z_tilde."
        ),
        "configs": {
            "pure_finite_P650_schur": cfg_pure_finite,
            "full_H_h_c_0_90": cfg_hybrid,
            "H_h_with_canonical_c_0_20_arch_pole_L1": cfg_L1_uni,
            "H_h_with_coarse_L_le_23_20_arch_c_0_20": cfg_coarse,
            "diagnostic_uncompensated_H_h_spatial_scaled_to_c_0_20": cfg_diag_020,
        },
    }


def certify_banded_and_fourier_tail_compensation(
    S_even: arb_mat,
    S_odd: arb_mat,
    Z_tilde_12: arb_mat,
    G_V_dressed: arb_mat,
    G_band_dressed: arb_mat,
    G_tail750_dressed: arb_mat,
    wr: dict,
) -> dict:
    """Step 4 (Track A): Exact critical c*, banded [650,749] (+) Q_750, and r_400 Fourier tail closure."""

    def sec_block(M12: arb_mat, sec: int) -> arb_mat:
        off = 0 if sec == 0 else 6
        return arb_mat([[M12[off + i, off + j] for j in range(6)] for i in range(6)])

    def run_pair(name: str, M_ev: arb_mat, M_od: arb_mat) -> dict:
        r_ev = run_interval_ldlt_6x6(M_ev, "even", 0)
        r_od = run_interval_ldlt_6x6(M_od, "odd", 6)
        all_p = r_ev["pivots"] + r_od["pivots"]
        pos_c = r_ev["pos_count"] + r_od["pos_count"]
        min_lo = min(r_ev["min_pivot_lower"], r_od["min_pivot_lower"])
        return {
            "config_name": name,
            "all_12_pivots_positive": (
                r_ev["all_pivots_positive"] and r_od["all_pivots_positive"] and pos_c == 12
            ),
            "pos_count": pos_c,
            "min_pivot_lower": min_lo,
            "sectors": [r_ev, r_od],
            "all_pivots": all_p,
        }

    eye6 = arb_mat([[arb(1 if i == j else 0) for j in range(6)] for i in range(6)])
    eps_f = F(wr["epsilon"])
    young_090 = q2arb((1 + eps_f) / C_HYBRID)
    zt_frob_sq = mat_frob_norm_sq(Z_tilde_12)
    zt_frob = zt_frob_sq.sqrt()
    delta_ap_sq_zt = (
        (q2arb(F(wr["compact_delta650"])) + q2arb(F(wr["pole_delta"]["pole_delta_upper"]))) ** 2
    ) * zt_frob_sq

    GV_ev = sec_block(G_V_dressed, 0)
    GV_od = sec_block(G_V_dressed, 1)
    Gband_ev = sec_block(G_band_dressed, 0)
    Gband_od = sec_block(G_band_dressed, 1)
    Gtail750_ev = sec_block(G_tail750_dressed, 0)
    Gtail750_od = sec_block(G_tail750_dressed, 1)

    def m_full_sec(sec: int, c_arb: arb, extra_eye_pen: arb | None = None) -> arb_mat:
        S_sec = S_even if sec == 0 else S_odd
        GV_sec = GV_ev if sec == 0 else GV_od
        delta_young = q2arb(1 + eps_f) / c_arb - young_090
        pen_ap = delta_ap_sq_zt / c_arb
        if extra_eye_pen is not None:
            pen_ap = pen_ap + extra_eye_pen
        return S_sec - delta_young * GV_sec - pen_ap * eye6

    def m_tail750_sec(sec: int, c_tail: arb) -> arb_mat:
        S_sec = S_even if sec == 0 else S_odd
        Gt_sec = Gtail750_ev if sec == 0 else Gtail750_od
        delta_young = q2arb(1 + eps_f) / c_tail - young_090
        pen_ap = delta_ap_sq_zt / c_tail
        return S_sec - delta_young * Gt_sec - pen_ap * eye6

    def bisect_critical_c(
        mat_fn, sec: int, sec_name: str, off: int, lo_val: str = "0.15", hi_val: str = "0.30", steps: int = 64
    ) -> float:
        lo = arb(lo_val)
        hi = arb(hi_val)
        half = arb("0.5")
        for _ in range(steps):
            mid = (lo + hi) * half
            res = run_interval_ldlt_6x6(mat_fn(sec, mid), sec_name, off)
            if res["all_pivots_positive"]:
                hi = mid
            else:
                lo = mid
        return float(hi.mid())

    # Part 1: Boundary values z_tilde_k(+/-1) and exact critical coercivity thresholds c_crit^*
    sqrt_half = arb(2).sqrt()
    boundary_values = []
    for k in range(12):
        z1 = arb(0)
        zm1 = arb(0)
        l2_sq = arb(0)
        for d in range(650):
            c_dk = Z_tilde_12[d, k]
            l2_sq += c_dk * c_dk
            w_d = arb(2 * d + 1).sqrt() / sqrt_half
            term = w_d * c_dk
            z1 += term
            zm1 += term if (d % 2 == 0) else -term
        l2_norm = l2_sq.sqrt()
        boundary_values.append(
            {
                "mode": k + 1,
                "sector": "even" if k < 6 else "odd",
                "z_tilde_at_pos_1": float(z1.mid()),
                "z_tilde_at_neg_1": float(zm1.mid()),
                "l2_norm": float(l2_norm.mid()),
                "boundary_to_l2_ratio": float((abs(z1) / l2_norm).mid()),
            }
        )

    c_crit_even_star = bisect_critical_c(m_full_sec, 0, "even", 0)
    c_crit_odd_star = bisect_critical_c(m_full_sec, 1, "odd", 6)
    c_crit_overall_star = max(c_crit_even_star, c_crit_odd_star)
    cfg_c_0_25 = run_pair("canonical_spatial_at_c_0_25", m_full_sec(0, arb("0.25")), m_full_sec(1, arb("0.25")))

    # Part 2: Banded two-tier [650, 749] (+) Q_750 exterior Schur analysis
    cfg_banded_090_020 = run_pair(
        "banded_resolved_090_tail_020", m_tail750_sec(0, arb("0.2")), m_tail750_sec(1, arb("0.2"))
    )
    c_tail750_even_star = bisect_critical_c(m_tail750_sec, 0, "even", 0)
    c_tail750_odd_star = bisect_critical_c(m_tail750_sec, 1, "odd", 6)
    c_tail750_overall_star = max(c_tail750_even_star, c_tail750_odd_star)

    # Part 3: Dressed-mode frequency localization on [0, 400] & r_400 Fourier tail retention
    t_nodes, w_nodes, _h_nodes = build_composite_gl_nodes(400.0, density_scale=1)
    beta_arb = q2arb(CERT_BETA_FRACTION)
    s_weights = [arb(1 if (d // 2) % 2 == 0 else -1) * arb(2 * d + 1).sqrt() for d in range(650)]
    Z_weighted = arb_mat([[Z_tilde_12[d, k] * s_weights[d] for k in range(12)] for d in range(650)])
    J_mat = arb_mat(len(t_nodes), 650)
    J_band_ev = arb_mat(len(t_nodes), 50)
    W_band_ev = arb_mat(len(t_nodes), 50)
    J_band_od = arb_mat(len(t_nodes), 50)
    W_band_od = arb_mat(len(t_nodes), 50)
    sqrt_2k1_band = [arb(2 * d + 1).sqrt() for d in range(650, 750)]
    for m_idx, (t_m, w_m, h_m) in enumerate(zip(t_nodes, w_nodes, _h_nodes)):
        jv = spherical_j_vector(750, t_m)
        for d in range(650):
            J_mat[m_idx, d] = jv[d]
        ker = w_m * (h_m - beta_arb)
        for c_idx in range(50):
            d_ev = 650 + 2 * c_idx
            val_ev = sqrt_2k1_band[2 * c_idx] * jv[d_ev]
            J_band_ev[m_idx, c_idx] = val_ev
            W_band_ev[m_idx, c_idx] = ker * val_ev

            d_od = 651 + 2 * c_idx
            val_od = sqrt_2k1_band[2 * c_idx + 1] * jv[d_od]
            J_band_od[m_idx, c_idx] = val_od
            W_band_od[m_idx, c_idx] = ker * val_od
    W_waves = J_mat * Z_weighted
    pref = arb(2) / arb.pi()
    K_arch_band_ev = pref * (J_band_ev.transpose() * W_band_ev)
    K_arch_band_od = pref * (J_band_od.transpose() * W_band_od)
    K_arch_650_band_ev = pref * (J_mat.transpose() * W_band_ev)
    K_arch_650_band_od = pref * (J_mat.transpose() * W_band_od)

    # Part 2b: Rigorous 512-bit Arb coercivity certification on P_{[650, 749]} H P_{[650, 749]}
    rule750 = certify_rule(750, bits=640, bracket_bits=560, newton_steps=11)
    if rule750["status"] != "CERTIFIED_GAUSS_LEGENDRE_RULE_BOXES":
        raise RuntimeError(f"GL750 rule certification failed: {rule750['status']}")
    nodes750 = [interval_pair_to_arb(item["node"]) for item in rule750["nodes_weights"]]
    weights750 = [interval_pair_to_arb(item["weight"]) for item in rule750["nodes_weights"]]

    V_band = arb_mat(100, 100)
    V_650_band = arb_mat(650, 100)
    for n, p_base in ACTIVE_PRIME_POWERS:
        ln_n = arb(n).log()
        coef = -(arb(p_base).log() / arb(n).sqrt())
        lo_ov = ln_n - arb(1)
        hi_ov = arb(1)
        mid_ov = (lo_ov + hi_ov) / 2
        half_ov = (hi_ov - lo_ov) / 2
        x_pts = [mid_ov + half_ov * xi for xi in nodes750]
        y_pts = [x_q - ln_n for x_q in x_pts]
        Phi_x_all = _evaluate_weighted_legendre_matrix(x_pts, 749)
        Phi_y_all = _evaluate_weighted_legendre_matrix(y_pts, 749)
        Phi_x_650 = arb_mat([[Phi_x_all[q, d] for d in range(650)] for q in range(750)])
        Phi_y_650 = arb_mat([[Phi_y_all[q, d] for d in range(650)] for q in range(750)])
        Phi_x_b = arb_mat([[Phi_x_all[q, 650 + c] for c in range(100)] for q in range(750)])
        Phi_y_b = arb_mat([[Phi_y_all[q, 650 + c] for c in range(100)] for q in range(750)])
        W_Phi_x = arb_mat(750, 100)
        W_Phi_y = arb_mat(750, 100)
        for q_idx in range(750):
            w_phys = half_ov * weights750[q_idx]
            for c_idx in range(100):
                W_Phi_x[q_idx, c_idx] = w_phys * Phi_x_b[q_idx, c_idx]
                W_Phi_y[q_idx, c_idx] = w_phys * Phi_y_b[q_idx, c_idx]
        V_band += coef * (Phi_x_b.transpose() * W_Phi_y + Phi_y_b.transpose() * W_Phi_x)
        V_650_band += coef * (Phi_x_650.transpose() * W_Phi_y + Phi_y_650.transpose() * W_Phi_x)

    delta_pole_650 = q2arb(F(wr["pole_delta"]["pole_delta_upper"]))
    B_band_ev = arb_mat(50, 50)
    B_band_od = arb_mat(50, 50)
    V_band_ev = arb_mat(50, 50)
    V_band_od = arb_mat(50, 50)
    eye50 = arb_mat([[arb(1 if i == j else 0) for j in range(50)] for i in range(50)])
    for i in range(50):
        for j in range(50):
            V_band_ev[i, j] = V_band[2 * i, 2 * j]
            V_band_od[i, j] = V_band[2 * i + 1, 2 * j + 1]
            B_band_ev[i, j] = K_arch_band_ev[i, j] + V_band_ev[i, j]
            B_band_od[i, j] = K_arch_band_od[i, j] + V_band_od[i, j]
            if i == j:
                B_band_ev[i, j] += beta_arb - delta_pole_650
                B_band_od[i, j] += beta_arb - delta_pole_650

    ok_ev_090, pos_ev_090, min_lo_ev_090 = run_interval_ldlt_nxn_positive(B_band_ev - arb("0.9") * eye50)
    ok_od_090, pos_od_090, min_lo_od_090 = run_interval_ldlt_nxn_positive(B_band_od - arb("0.9") * eye50)

    def bisect_band_lambda_min(B_sec: arb_mat, steps: int = 44) -> float:
        lo = arb("0.0")
        hi = arb("4.2")
        half = arb("0.5")
        for _ in range(steps):
            mid = (lo + hi) * half
            ok, _, _ = run_interval_ldlt_nxn_positive(B_sec - mid * eye50)
            if ok:
                lo = mid
            else:
                hi = mid
        return float(lo.mid())

    c_band_ev_lower = bisect_band_lambda_min(B_band_ev)
    c_band_od_lower = bisect_band_lambda_min(B_band_od)
    c_band_overall_lower = min(c_band_ev_lower, c_band_od_lower)
    mode_frequency_localization = []
    for k in range(12):
        l2_sq = sum((Z_tilde_12[d, k] ** 2 for d in range(650)), arb(0))
        e_lf = pref * sum((w_nodes[m] * (W_waves[m, k] ** 2) for m in range(len(t_nodes))), arb(0))
        delta_hf = arb(1) - e_lf / l2_sq
        mode_frequency_localization.append(
            {
                "mode": k + 1,
                "sector": "even" if k < 6 else "odd",
                "l2_norm_sq": float(l2_sq.mid()),
                "low_freq_energy_0_400": float(e_lf.mid()),
                "high_freq_fraction_400_inf": float(delta_hf.mid()),
            }
        )

    inv_eps_plus_1 = arb(1) + arb(1) / q2arb(eps_f)
    c_can_arb = q2arb(C_CANONICAL)
    fourier_tail_results = []
    for T2 in [405, 410, 415, 420, 430, 450]:
        ctb = cutoff_tail_bound(1, T2, 650, 1)
        trace_upper = q2arb(F(ctb["trace_upper"]))
        delta_beta = exact_archimedean_h(arb(T2)) - beta_arb
        c_eff = c_can_arb + delta_beta * (arb(1) - trace_upper)
        delta_proj = delta_beta * trace_upper.sqrt()
        young_pen = (inv_eps_plus_1 / c_eff) * ((delta_proj * zt_frob) ** 2)
        ldlt_res = run_pair(
            f"fourier_tail_T2_{T2}",
            m_full_sec(0, c_eff, extra_eye_pen=young_pen),
            m_full_sec(1, c_eff, extra_eye_pen=young_pen),
        )
        fourier_tail_results.append(
            {
                "T2": T2,
                "trace_upper": float(trace_upper.upper()),
                "trace_upper_sci": arb_upper_sci(trace_upper),
                "delta_beta": float(delta_beta.mid()),
                "c_eff": float(c_eff.lower()),
                "delta_proj": float(delta_proj.upper()),
                "delta_proj_sci": arb_upper_sci(delta_proj),
                "young_pen": float(young_pen.upper()),
                "young_pen_sci": arb_upper_sci(young_pen),
                "exceeds_c_crit_overall_star": bool(float(c_eff.lower()) > c_crit_overall_star),
                "all_12_pivots_positive": ldlt_res["all_12_pivots_positive"],
                "pos_count": ldlt_res["pos_count"],
                "min_pivot_lower": ldlt_res["min_pivot_lower"],
                "sectors": ldlt_res["sectors"],
            }
        )

    step4_out = {
        "critical_coercivity_thresholds": {
            "c_crit_even_star": c_crit_even_star,
            "c_crit_odd_star": c_crit_odd_star,
            "c_crit_overall_star": c_crit_overall_star,
            "canonical_spatial_at_c_0_25": cfg_c_0_25,
            "boundary_values_z_tilde": boundary_values,
        },
        "banded_two_tier_650_749_plus_Q750": {
            "band_650_749_frob_even": float(mat_frob_norm_sq(Gband_ev).sqrt().mid()),
            "band_650_749_frob_odd": float(mat_frob_norm_sq(Gband_od).sqrt().mid()),
            "tail_750_plus_frob_even": float(mat_frob_norm_sq(Gtail750_ev).sqrt().mid()),
            "tail_750_plus_frob_odd": float(mat_frob_norm_sq(Gtail750_od).sqrt().mid()),
            "banded_resolved_090_tail_020": cfg_banded_090_020,
            "c_tail750_even_star": c_tail750_even_star,
            "c_tail750_odd_star": c_tail750_odd_star,
            "c_tail750_overall_star": c_tail750_overall_star,
            "band_650_749_coercivity": {
                "beta_lower": float(beta_arb.lower()),
                "arch_band_frob_even": float(mat_frob_norm_sq(K_arch_band_ev).sqrt().upper()),
                "arch_band_frob_odd": float(mat_frob_norm_sq(K_arch_band_od).sqrt().upper()),
                "spatial_band_frob_even": float(mat_frob_norm_sq(V_band_ev).sqrt().upper()),
                "spatial_band_frob_odd": float(mat_frob_norm_sq(V_band_od).sqrt().upper()),
                "c_band_090_certified_even": ok_ev_090,
                "c_band_090_certified_odd": ok_od_090,
                "c_band_090_pos_count": pos_ev_090 + pos_od_090,
                "c_band_090_min_pivot_lower": min(min_lo_ev_090, min_lo_od_090),
                "c_band_even_lower": c_band_ev_lower,
                "c_band_odd_lower": c_band_od_lower,
                "c_band_overall_lower": c_band_overall_lower,
                "exceeds_c_band_090": bool(c_band_overall_lower > 0.90),
            },
        },
        "mode_frequency_localization_0_400": mode_frequency_localization,
        "fourier_tail_r400_retention": fourier_tail_results,
    }
    band_coupling_data = {
        "B_band_secs": [B_band_ev, B_band_od],
        "K_arch_650_band_secs": [K_arch_650_band_ev, K_arch_650_band_od],
        "V_650_band": V_650_band,
        "nodes750": nodes750,
        "weights750": weights750,
        "delta_pole_650": delta_pole_650,
    }
    return step4_out, band_coupling_data


def certify_joint_738_block_schur(
    bulk_blocks: dict,
    band_coupling_data: dict,
    wr: dict,
    arch_dir_frob_upper_sci: str,
) -> dict:
    """Track 3 (Strategy 2): Full 738-dimensional (X_bulk (+) P_[650,749]) block-Schur elimination at L=1."""
    V_650_band = band_coupling_data["V_650_band"]
    nodes750 = band_coupling_data["nodes750"]
    weights750 = band_coupling_data["weights750"]
    delta_pole_650 = band_coupling_data["delta_pole_650"]
    c_tail_750 = q2arb(C_CANONICAL)  # c = 0.20 on Q_750

    pole_pen_650 = (delta_pole_650 ** 2) / c_tail_750
    arch_frob = arb(arch_dir_frob_upper_sci)
    arch_pen = (arch_frob ** 2) / c_tail_750
    lambda_min_bulk = q2arb(bulk_blocks["lambda_min_bulk_lower"])

    sector_results = []
    joint_sector_data = []
    all_12_pos = True
    total_pos = 0
    min_pivot_lower = float("inf")

    for sec in range(2):
        sec_name = ["even", "odd"][sec]
        X_bulk = bulk_blocks["X_bulk_secs"][sec]  # 650 x 319
        Z_crit = bulk_blocks["Z_bare_secs"][sec]  # 650 x 6
        A_BB = bulk_blocks["A_BB_secs"][sec]  # 319 x 319
        A_BC = bulk_blocks["A_BC_secs"][sec]  # 319 x 6
        A_CC = bulk_blocks["A_CC_secs"][sec]  # 6 x 6
        B_band = band_coupling_data["B_band_secs"][sec]  # 50 x 50
        K_650_band = band_coupling_data["K_arch_650_band_secs"][sec]  # 650 x 50

        V_650_band_sec = arb_mat(650, 50)
        for d in range(650):
            for c_idx in range(50):
                V_650_band_sec[d, c_idx] = V_650_band[d, 2 * c_idx + sec]

        H_650_band = K_650_band + V_650_band_sec  # 650 x 50
        B_bulk_band = X_bulk.transpose() * H_650_band  # 319 x 50
        B_crit_band = Z_crit.transpose() * H_650_band  # 6 x 50

        # Form 369 x 369 combined bulk+band block M_369 and 369 x 6 RHS R_369
        M_369 = arb_mat(369, 369)
        R_369 = arb_mat(369, 6)
        for i in range(319):
            for j in range(319):
                M_369[i, j] = A_BB[i, j]
            for j in range(50):
                M_369[i, 319 + j] = B_bulk_band[i, j]
                M_369[319 + j, i] = B_bulk_band[i, j]
            for j in range(6):
                R_369[i, j] = A_BC[i, j]
        for i in range(50):
            for j in range(50):
                M_369[319 + i, 319 + j] = B_band[i, j]
            for j in range(6):
                R_369[319 + i, j] = B_crit_band[j, i]

        t0 = time.time()
        Y_369 = M_369.solve(R_369)
        t_solve = time.time() - t0

        Res_369 = M_369 * Y_369 - R_369
        max_r = max(abs(Res_369[i, j].upper()) for i in range(369) for j in range(6))
        frob_r_sq = (369 * 6) * (max_r ** 2)
        # Rigorous lower bound on lambda_min(M_369): min(lambda_min(A_BB), 1e-18) verified via shifted LDLT
        shift_369 = min(lambda_min_bulk * arb("0.5"), arb("1e-16"))
        eye369 = arb_mat(369, 369)
        for i in range(369):
            eye369[i, i] = shift_369
        ok_m369, _, _ = run_interval_ldlt_nxn_positive(M_369 - eye369)
        if not ok_m369:
            raise RuntimeError(f"M_369 shifted LDL^T failed for sector {sec_name}")
        delta_quad_369 = frob_r_sq / shift_369

        # Construct full 750 x 6 jointly dressed basis Z_joint = Z_crit - X_bulk * Y_bulk - P_band * Y_band
        Y_bulk_j = arb_mat([[Y_369[i, k] for k in range(6)] for i in range(319)])
        Y_band_j = arb_mat([[Y_369[319 + i, k] for k in range(6)] for i in range(50)])
        Z_650_j = Z_crit - X_bulk * Y_bulk_j
        Z_joint_750 = arb_mat(750, 6)
        for d in range(650):
            for k in range(6):
                Z_joint_750[d, k] = Z_650_j[d, k]
        for c_idx in range(50):
            d_band = 650 + 2 * c_idx + sec
            for k in range(6):
                Z_joint_750[d_band, k] = -Y_band_j[c_idx, k]

        # Exact GL750 Parseval Q_750 spatial tail Gram of Z_joint_750 (and X_bulk Q_750 tail norm)
        G_V_750_joint = arb_mat(6, 6)
        C_total = arb_mat(750, 6)
        x_bulk_tail_sq = arb(0)
        for n, p_base in ACTIVE_PRIME_POWERS:
            ln_n = arb(n).log()
            coef = -(arb(p_base).log() / arb(n).sqrt())
            lo_ov = ln_n - arb(1)
            hi_ov = arb(1)
            mid_ov = (lo_ov + hi_ov) / 2
            half_ov = (hi_ov - lo_ov) / 2
            x_pts = [mid_ov + half_ov * xi for xi in nodes750]
            y_pts = [x_q - ln_n for x_q in x_pts]
            Phi_x_750 = _evaluate_weighted_legendre_matrix(x_pts, 749)
            Phi_y_750 = _evaluate_weighted_legendre_matrix(y_pts, 749)

            # Shift action V Z_joint_750 on x_pts, projected onto P_750 via y_pts
            # Exact L^2 norm via physical integration of f(x) = sum_n c_n phi(x - ln n)
            # Reuse Parseval over orthonormal Legendre basis: G_V_total - C_750^T C_750
            Vx_j = Phi_y_750 * Z_joint_750  # 750 x 6: Z_joint evaluated at x - ln_n
            # Wait: V Z_joint at x is sum_{n} coef * 1_{x in [ln_n - 1, 1]} * Z_joint(x - ln_n)
            # Project onto P_750: C_750[d, k] = int_{ln_n-1}^1 P_d(x) Z_joint(x - ln_n) dx
            W_Phi_x_750 = arb_mat(750, 750)
            for q_idx in range(750):
                w_phys = half_ov * weights750[q_idx]
                for d in range(750):
                    W_Phi_x_750[q_idx, d] = w_phys * Phi_x_750[q_idx, d]
            C_total += coef * (W_Phi_x_750.transpose() * Vx_j)  # 750 x 6

        P_750_joint = C_total.transpose() * C_total

        # Full L^2 Gram of V Z_joint_750: compute on GL750 over [-1, 1] directly using piecewise exactness
        # Note: for n=2,3,4,5,7, V Z_joint_750(x) is a sum of smooth degree <= 749 polynomials on each of the subintervals!
        breaks = sorted(
            [arb(-1), arb(1)]
            + [arb(n).log() - arb(1) for n, _ in ACTIVE_PRIME_POWERS]
            + [arb(1) - arb(n).log() for n, _ in ACTIVE_PRIME_POWERS],
            key=lambda x: float(x.mid()),
        )
        # Filter unique breaks in [-1, 1]
        uniq_breaks = [breaks[0]]
        for b_val in breaks[1:]:
            if (b_val - uniq_breaks[-1]).lower() > 1e-30:
                uniq_breaks.append(b_val)
        G_V_total_j = arb_mat(6, 6)
        for c_i in range(len(uniq_breaks) - 1):
            a_c, b_c = uniq_breaks[c_i], uniq_breaks[c_i + 1]
            mid_c = (a_c + b_c) / 2
            half_c = (b_c - a_c) / 2
            x_c = [mid_c + half_c * xi for xi in nodes750]
            vals_j = arb_mat(750, 6)
            for n, p_base in ACTIVE_PRIME_POWERS:
                ln_n = arb(n).log()
                if (mid_c - (ln_n - arb(1))).lower() > 0:
                    coef = -(arb(p_base).log() / arb(n).sqrt())
                    y_c = [xv - ln_n for xv in x_c]
                    Phi_yc = _evaluate_weighted_legendre_matrix(y_c, 749)
                    vals_j += coef * (Phi_yc * Z_joint_750)
            W_vals = arb_mat(750, 6)
            for q_idx in range(750):
                w_phys = half_c * weights750[q_idx]
                for k in range(6):
                    W_vals[q_idx, k] = w_phys * vals_j[q_idx, k]
            G_V_total_j += vals_j.transpose() * W_vals

        G_V_750_joint = G_V_total_j - P_750_joint
        eye6 = arb_mat([[arb(1 if i == j else 0) for j in range(6)] for i in range(6)])
        S_joint = (
            A_CC
            - R_369.transpose() * Y_369
            - delta_quad_369 * eye6
            - (arb(1) / c_tail_750) * G_V_750_joint
            - (pole_pen_650 + arch_pen) * eye6
        )

        ldlt_sec = run_interval_ldlt_6x6(S_joint, sec_name, 0 if sec == 0 else 6)
        all_12_pos = all_12_pos and ldlt_sec["all_pivots_positive"]
        total_pos += ldlt_sec["pos_count"]
        min_pivot_lower = min(min_pivot_lower, ldlt_sec["min_pivot_lower"])

        sector_results.append(
            {
                "sector": sec_name,
                "dim_combined_bulk_band": 369,
                "solve_time_seconds": round(t_solve, 3),
                "B_bulk_band_frob": float(mat_frob_norm_sq(B_bulk_band).sqrt().upper()),
                "B_crit_band_frob": float(mat_frob_norm_sq(B_crit_band).sqrt().upper()),
                "Y_band_frob": float(mat_frob_norm_sq(Y_band_j).sqrt().upper()),
                "delta_quad_369_upper_sci": arb_upper_sci(delta_quad_369),
                "tail_750_joint_trace": float(sum((G_V_750_joint[i, i] for i in range(6)), arb(0)).upper()),
                "ldlt": ldlt_sec,
            }
        )
        joint_sector_data.append(
            {
                "sector": sec_name,
                "S_joint": S_joint,
                "Z_crit": Z_crit,
                "Z_joint_750": Z_joint_750,
            }
        )

    return (
        {
            "dim_total_eliminated": 738,
            "c_tail_750": float(C_CANONICAL),
            "all_12_pivots_positive": all_12_pos,
            "pos_count": total_pos,
            "min_pivot_lower": min_pivot_lower,
            "sectors": sector_results,
        },
        joint_sector_data,
    )


def certify_end_to_end_true_integral_l1(
    joint_sector_data: list[dict],
    Z_tilde_secs: list[arb_mat],
    band_coupling_data: dict,
    M_sym: arb_mat,
    p650_dir: Path,
    direct_dir: Path,
    wr: dict,
) -> dict:
    """Step 6: End-to-end 750x750 true-integral L=1 Schur enclosure with eps_32 & odd low-deg check."""
    # 1. Exact analytic 32-node panel quadrature remainder eps_32 = 4225 / 166153499473114484112975882535043072
    eps_32 = arb(fmpq(4225, 166153499473114484112975882535043072))

    # 2. Exact 512-bit true-integral verification of odd low-degree modes d in {1, 3, 5, 7, 9, 11}
    odd_low_degs = [1, 3, 5, 7, 9, 11]
    nodes750 = band_coupling_data["nodes750"]
    weights750 = band_coupling_data["weights750"]

    # Pole operator W on odd low degrees
    half = arb("0.5")
    s_pole = [arb(2 * (2 * d + 1)).sqrt() * spherical_i_0f1(d, half) for d in odd_low_degs]
    W_low = arb_mat(6, 6)
    for i in range(6):
        for j in range(6):
            W_low[i, j] = -arb(2) * s_pole[i] * s_pole[j]

    # Spatial prime-shift operator V on odd low degrees via GL750 exact piecewise integration
    V_low = arb_mat(6, 6)
    for n, p_base in ACTIVE_PRIME_POWERS:
        ln_n = arb(n).log()
        coef = -(arb(p_base).log() / arb(n).sqrt())
        lo_ov = ln_n - arb(1)
        hi_ov = arb(1)
        mid_ov = (lo_ov + hi_ov) / 2
        half_ov = (hi_ov - lo_ov) / 2
        x_pts = [mid_ov + half_ov * xi for xi in nodes750]
        y_pts = [x_q - ln_n for x_q in x_pts]
        Phi_x = _evaluate_weighted_legendre_matrix(x_pts, 11)
        Phi_y = _evaluate_weighted_legendre_matrix(y_pts, 11)
        # <phi_di, T_{-ln n} phi_dj>
        T_mat = arb_mat(6, 6)
        for q_idx in range(750):
            w_phys = half_ov * weights750[q_idx]
            for i, di in enumerate(odd_low_degs):
                for j, dj in enumerate(odd_low_degs):
                    T_mat[i, j] += w_phys * Phi_x[q_idx, di] * Phi_y[q_idx, dj]
        V_low += coef * (T_mat + T_mat.transpose())

    # Archimedean operator K_inf(h) = K_400(h - beta) + beta*I on odd low degrees (density_scale=2 vs 1)
    beta_arb = q2arb(CERT_BETA_FRACTION)
    pref = arb(2) / arb.pi()
    s_odd_low = [arb(1 if (d // 2) % 2 == 0 else -1) * arb(2 * d + 1).sqrt() for d in odd_low_degs]

    def _compute_k_low(density_scale: int) -> arb_mat:
        t_nodes, w_nodes, h_nodes = build_composite_gl_nodes(400.0, density_scale=density_scale)
        K_m = arb_mat(6, 6)
        for t_m, w_m, h_m in zip(t_nodes, w_nodes, h_nodes):
            jv = spherical_j_vector(12, t_m)
            ker = pref * w_m * (h_m - beta_arb)
            for i, di in enumerate(odd_low_degs):
                vi = s_odd_low[i] * jv[di]
                for j, dj in enumerate(odd_low_degs):
                    K_m[i, j] += ker * vi * (s_odd_low[j] * jv[dj])
        for i in range(6):
            K_m[i, i] += beta_arb
        return K_m

    K_low_d2 = _compute_k_low(density_scale=2)
    K_low_d1 = _compute_k_low(density_scale=1)
    k_quad_doubling_max_diff = max(
        float(abs(K_low_d2[i, j] - K_low_d1[i, j]).upper()) for i in range(6) for j in range(6)
    )
    H_low_direct = K_low_d2 + V_low + W_low

    M_finite_raw = json.loads(gzip.decompress((p650_dir / "FINITE_LOWER.json.gz").read_bytes()).decode("utf-8"))
    M_finite_mid = load_midpoint_mat(M_finite_raw)
    max_diff_vs_FINITE_LOWER = max(
        float(abs(H_low_direct[i, j] - M_finite_mid[odd_low_degs[i], odd_low_degs[j]]).upper())
        for i in range(6)
        for j in range(6)
    )

    # Compute exact Q_650 V P_low Gram on odd low degrees via Parseval (11 cells - P_650 projection)
    arith = json.loads((direct_dir / "ARITHMETIC_RECEIPT.json").read_text(encoding="utf-8"))
    partitions = arith["partitions"]
    log_n = {n: arb(n).log() for n, _ in ACTIVE_PRIME_POWERS}
    img_shifts = []
    for n, p_base in ACTIVE_PRIME_POWERS:
        ln_n = log_n[n]
        coef = -(arb(p_base).log() / arb(n).sqrt())
        img_shifts.append((-ln_n, coef))
        img_shifts.append((+ln_n, coef))

    G_V_full_low = arb_mat(6, 6)
    for cell in partitions:
        lo_c = interval_pair_to_arb(cell["lo"])
        hi_c = interval_pair_to_arb(cell["hi"])
        mid_c = (lo_c + hi_c) / 2
        half_c = (hi_c - lo_c) / 2
        active = cell["active_images"]
        if not active:
            continue
        V_cell = arb_mat(750, 6)
        for img_idx in active:
            shift, coef = img_shifts[img_idx]
            y_pts = [mid_c + half_c * xi + shift for xi in nodes750]
            Phi_y = _evaluate_weighted_legendre_matrix(y_pts, 11)
            for q_idx in range(750):
                for k, dk in enumerate(odd_low_degs):
                    V_cell[q_idx, k] += coef * Phi_y[q_idx, dk]
        W_V_cell = arb_mat(750, 6)
        for q_idx in range(750):
            w_phys = half_c * weights750[q_idx]
            for k in range(6):
                W_V_cell[q_idx, k] = w_phys * V_cell[q_idx, k]
        G_V_full_low += V_cell.transpose() * W_V_cell

    P650_V_low = arb_mat(650, 6)
    for n, p_base in ACTIVE_PRIME_POWERS:
        ln_n = log_n[n]
        coef = -(arb(p_base).log() / arb(n).sqrt())
        lo_ov = ln_n - arb(1)
        hi_ov = arb(1)
        mid_ov = (lo_ov + hi_ov) / 2
        half_ov = (hi_ov - lo_ov) / 2
        x_pts = [mid_ov + half_ov * xi for xi in nodes750]
        y_pts = [x_q - ln_n for x_q in x_pts]
        Phi_x_650 = _evaluate_weighted_legendre_matrix(x_pts, 649)
        Phi_y_11 = _evaluate_weighted_legendre_matrix(y_pts, 11)
        # P650(-ln n) and P650(+ln n)
        W_Phi_x = arb_mat(750, 650)
        W_Phi_y = arb_mat(750, 650)
        Phi_y_650 = _evaluate_weighted_legendre_matrix(y_pts, 649)
        Phi_x_11 = _evaluate_weighted_legendre_matrix(x_pts, 11)
        Phi_y_low = arb_mat([[Phi_y_11[q, dk] for dk in odd_low_degs] for q in range(750)])
        Phi_x_low = arb_mat([[Phi_x_11[q, dk] for dk in odd_low_degs] for q in range(750)])
        for q_idx in range(750):
            w_phys = half_ov * weights750[q_idx]
            for d in range(650):
                W_Phi_x[q_idx, d] = w_phys * Phi_x_650[q_idx, d]
                W_Phi_y[q_idx, d] = w_phys * Phi_y_650[q_idx, d]
        P650_V_low += coef * (W_Phi_x.transpose() * Phi_y_low + W_Phi_y.transpose() * Phi_x_low)

    G_V_ext_low = G_V_full_low - P650_V_low.transpose() * P650_V_low
    young_090 = q2arb((1 + F(wr["epsilon"])) / C_HYBRID)
    scc = q2arb(F(wr["scalar_coupling_correction"]))
    H_schur_low = H_low_direct - young_090 * G_V_ext_low
    for i in range(6):
        H_schur_low[i, i] -= scc
    max_diff_schur_vs_SCHUR_LOWER = max(
        float(abs(H_schur_low[i, j] - M_sym[odd_low_degs[i], odd_low_degs[j]]).upper())
        for i in range(6)
        for j in range(6)
    )

    # 3. End-to-end 512-bit interval LDL^T after subtracting eps_32 * (Z_tilde^T Z_tilde)
    sector_results = []
    all_12_pos = True
    total_pos = 0
    min_pivot_lower = float("inf")

    for sec in range(2):
        sdata = joint_sector_data[sec]
        sec_name = sdata["sector"]
        S_joint = sdata["S_joint"]
        Z_crit = sdata["Z_crit"]
        Z_tilde = Z_tilde_secs[sec]
        Z_joint_750 = sdata["Z_joint_750"]

        G_bare = Z_crit.transpose() * Z_crit
        G_tilde = Z_tilde.transpose() * Z_tilde
        G_joint = Z_joint_750.transpose() * Z_joint_750
        eps32_G_tilde = eps_32 * G_tilde
        eps32_G_bare = eps_32 * G_bare

        S_e2e = S_joint - eps32_G_tilde
        ldlt_sec = run_interval_ldlt_6x6(S_e2e, sec_name, 0 if sec == 0 else 6)
        all_12_pos = all_12_pos and ldlt_sec["all_pivots_positive"]
        total_pos += ldlt_sec["pos_count"]
        min_pivot_lower = min(min_pivot_lower, ldlt_sec["min_pivot_lower"])

        trace_tilde = sum((eps32_G_tilde[i, i] for i in range(6)), arb(0))
        trace_bare = sum((eps32_G_bare[i, i] for i in range(6)), arb(0))
        max_diff_joint_tilde = max(
            float((eps_32 * abs(G_joint[i, j] - G_tilde[i, j])).upper()) for i in range(6) for j in range(6)
        )

        sector_results.append(
            {
                "sector": sec_name,
                "eps32_G_tilde_trace_upper_sci": arb_upper_sci(trace_tilde),
                "eps32_G_bare_trace_upper_sci": arb_upper_sci(trace_bare),
                "eps32_joint_vs_tilde_max_diff": max_diff_joint_tilde,
                "ldlt": ldlt_sec,
            }
        )

    return {
        "dim_joint_system": 750,
        "dim_eliminated": 738,
        "c_tail_750": float(C_CANONICAL),
        "eps_32_rational": "4225 / 166153499473114484112975882535043072",
        "eps_32_upper_sci": arb_upper_sci(eps_32),
        "all_12_pivots_positive": all_12_pos,
        "pos_count": total_pos,
        "min_pivot_lower": min_pivot_lower,
        "odd_low_degree_true_integral_check": {
            "degrees": odd_low_degs,
            "k400_quad_doubling_max_diff": k_quad_doubling_max_diff,
            "max_diff_direct_H_vs_FINITE_LOWER": max_diff_vs_FINITE_LOWER,
            "max_diff_direct_schur_vs_SCHUR_LOWER": max_diff_schur_vs_SCHUR_LOWER,
        },
        "sectors": sector_results,
    }


def main() -> None:
    started = time.time()
    print("=" * 80)
    print("512-BIT FLINT.ARB EXTERIOR SCHUR COUPLING AUDIT (P_650 <-> Q_650, L = 1, T = 400)")
    print("=" * 80)

    p650_dir = REPO_ROOT / "research/certification_v2/p650_stable_assembly"
    direct_dir = REPO_ROOT / "research/certification_v2/direct_critical_form"
    repair_dir = REPO_ROOT / "research/certification_v2/structured_schur_repair"
    batch_gram_dir = REPO_ROOT / "research/certification_v2/batch_arithmetic_gram"
    sym_path = REPO_ROOT / "research/certification_v2/authenticated_symbol_tail/PILOT_RECEIPT.json"

    wr = json.loads((p650_dir / "WRITER_RECEIPT.json").read_text(encoding="utf-8"))
    M_sym = F(json.loads(sym_path.read_text(encoding="utf-8"))["symbol_sup_authenticated"])

    with ctx.workprec(WORK_PREC_BITS):
        print("\n--- Step 1: Dressed Critical Modes Z_tilde = Z_crit - X_bulk * Y & Decay ---")
        step1_info, _M_schur_mid, Z_bare_12, Z_tilde_12, S_even, S_odd, Z_tilde_secs, bulk_blocks = compute_dressed_critical_basis(
            direct_dir, repair_dir, p650_dir
        )
        ztilde_frob = mat_frob_norm_sq(Z_tilde_12).sqrt()
        for sec in step1_info["sectors"]:
            dec = sec["dressed_legendre_decay"]["windows"]
            print(
                f"  {sec['sector']:<4}: ||Y||_F={sec['Y_frob_norm_sci']}, "
                f"max|Z_tilde|_[0,50)={dec['0_49']['max_abs_coeff']:.4e}, "
                f"_[500,600)={dec['500_599']['max_abs_coeff']:.4e}, "
                f"_[600,650)={dec['600_649']['max_abs_coeff']:.4e}"
            )

        print("\n--- Step 2.1: Canonical Pole Exterior Leakage Q_650 W Z_tilde ---")
        pole_info = certify_pole_exterior_leakage(Z_tilde_12, ztilde_frob, wr)
        print(
            f"  delta_pole_650 = {pole_info['uniform_operator_delta_650_sci']} "
            f"(log10={pole_info['uniform_operator_delta_650_log10']:.2f}), "
            f"directed band [650,670) = {pole_info['directed_band_650_669_frob_sci']}"
        )

        print("\n--- Step 2.2: Archimedean Exterior Leakage Q_650 K_400 Z_tilde ---")
        arch_info = certify_archimedean_exterior_leakage(Z_tilde_secs, ztilde_frob, M_sym, wr)
        print(
            f"  Directed band [650,666) ||B||_F = {arch_info['directed_band_650_665_total_frob_sci']} "
            f"(quad doubling diff={arch_info['quadrature_doubling_max_diff_sci']})"
        )
        print(
            f"  + Q_666 tail = {arch_info['tail_666_on_Z_tilde_upper_sci']} "
            f"(vs uniform delta_650(L=1) = {arch_info['uniform_delta_650_L1_sci']})"
        )
        print(f"  Coarse uniform L<=23/20 penalty (c=0.20): {arch_info['coarse_uniform_L_le_23_20_penalty_c0_20']:.6e}")

        print("\n--- Step 2.3: Spatial Prime-Shift Exterior Leakage Q_650 V Z_tilde (GL700 exact) ---")
        spatial_info, G_V_dressed, G_band_dressed, G_tail750_dressed, P_ext_dressed_090 = (
            certify_spatial_exterior_leakage(Z_bare_12, Z_tilde_12, p650_dir, direct_dir, batch_gram_dir, wr)
        )
        print(
            f"  Tr(G_V_dressed) = {spatial_info['trace_Q650_V_Z_tilde_sq']:.6e} "
            f"([650,750) band share = {100.0 * spatial_info['band_650_749_fraction_of_exterior_energy']:.2f}%)"
        )
        print(
            f"  Cross-checks: bare vs ARITHMETIC_RECEIPT = {spatial_info['max_diff_bare_vs_ARITHMETIC_RECEIPT']:.3e}, "
            f"dressed vs FINITE-SCHUR = {spatial_info['max_diff_dressed_penalty_vs_FINITE_minus_SCHUR']:.3e}"
        )

        print("\n--- Step 2.4: 512-Bit Interval LDL^T Across Schur Coupling Regimes ---")
        schur_info = evaluate_schur_configurations(
            S_even, S_odd, Z_tilde_12, G_V_dressed, P_ext_dressed_090, wr, M_sym, arch_info["directed_total_arch_Z_tilde_frob_upper_sci"]
        )
        for cname, cdata in schur_info["configs"].items():
            print(
                f"  {cname:<55}: pos={cdata['pos_count']:2d}/12, "
                f"min_pivot_lo={cdata['min_pivot_lower']:+.6e}"
            )

        print("\n--- Step 4: Critical c*, Banded [650,749] (+) Q_750, and r_400 Fourier Tail ---")
        step4_info, band_coupling_data = certify_banded_and_fourier_tail_compensation(
            S_even, S_odd, Z_tilde_12, G_V_dressed, G_band_dressed, G_tail750_dressed, wr
        )
        crit = step4_info["critical_coercivity_thresholds"]
        print(
            f"  c_crit_even*={crit['c_crit_even_star']:.12f}, "
            f"c_crit_odd*={crit['c_crit_odd_star']:.12f}, "
            f"c_0.25 pos={crit['canonical_spatial_at_c_0_25']['pos_count']}/12"
        )
        band = step4_info["banded_two_tier_650_749_plus_Q750"]
        print(
            f"  banded_090_020 pos={band['banded_resolved_090_tail_020']['pos_count']}/12, "
            f"c_tail750*={band['c_tail750_overall_star']:.12f}"
        )
        for row in step4_info["fourier_tail_r400_retention"]:
            print(
                f"  T2={row['T2']:3d}: c_eff={row['c_eff']:.6f}, "
                f"trace={row['trace_upper_sci']}, young_pen={row['young_pen_sci']}, "
                f"pos={row['pos_count']}/12, min_lo={row['min_pivot_lower']:+.3e}"
            )

        print("\n--- Step 5: Joint 738-Dimensional (X_bulk (+) P_[650,749]) Block-Schur Elimination ---")
        step5_info, joint_sector_data = certify_joint_738_block_schur(
            bulk_blocks, band_coupling_data, wr, arch_info["directed_total_arch_Z_tilde_frob_upper_sci"]
        )
        print(
            f"  738-dim joint Schur: pos={step5_info['pos_count']}/12, "
            f"min_pivot_lo={step5_info['min_pivot_lower']:+.6e}"
        )

        print("\n--- Step 6: End-to-End 750x750 True-Integral L=1 Schur Enclosure (eps_32 & Odd Low-Deg Check) ---")
        step6_info = certify_end_to_end_true_integral_l1(
            joint_sector_data, Z_tilde_secs, band_coupling_data, _M_schur_mid, p650_dir, direct_dir, wr
        )
        chk = step6_info["odd_low_degree_true_integral_check"]
        print(
            f"  End-to-end 750x750 LDL^T: pos={step6_info['pos_count']}/12, "
            f"min_pivot_lo={step6_info['min_pivot_lower']:+.6e}, "
            f"H_vs_FINITE={chk['max_diff_direct_H_vs_FINITE_LOWER']:.3e}, "
            f"Schur_vs_SCHUR={chk['max_diff_direct_schur_vs_SCHUR_LOWER']:.3e}, "
            f"K400_doubling={chk['k400_quad_doubling_max_diff']:.3e}"
        )

    elapsed = time.time() - started
    certificate = {
        "certificate_id": "RH-V2-L1-EXTERIOR-SCHUR-COUPLING-512BIT-ARB-001",
        "timestamp_iso": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
        "elapsed_seconds": elapsed,
        "working_precision_bits": WORK_PREC_BITS,
        "library": f"python-flint {flint.__version__}",
        "governance": {
            "NO_RH_PROOF": True,
            "FULL_POINT_L1": "NOT_ISSUED",
            "PUBLICATION_STATUS": "HOLD",
            "scope": (
                "Exterior P_650 <-> Q_650 Schur coupling audit on the 12 dressed critical modes "
                "at N=650, L=1, T=400. Certifies H_h positivity with full infinite-dimensional Q_650 "
                "Schur elimination at c=0.90; canonical A(1) remains uncertified."
            ),
        },
        "input_files_sha256": {
            "p650_FINITE_LOWER": sha256_file(p650_dir / "FINITE_LOWER.json.gz"),
            "p650_SCHUR_LOWER": sha256_file(p650_dir / "SCHUR_LOWER.json.gz"),
            "p650_WRITER_RECEIPT": sha256_file(p650_dir / "WRITER_RECEIPT.json"),
            "batch_arithmetic_gram_d650": sha256_file(batch_gram_dir / "d650_RECEIPT.json"),
            "direct_ARITHMETIC_RECEIPT": sha256_file(direct_dir / "ARITHMETIC_RECEIPT.json"),
            "direct_CRITICAL_COMPOSITION_WRITER": sha256_file(direct_dir / "CRITICAL_COMPOSITION_WRITER.json"),
            "repair_FULL_DYADIC_SPLIT_BASIS": sha256_file(repair_dir / "FULL_DYADIC_SPLIT_BASIS.json.gz"),
            "repair_BULK_SPLIT_RECEIPT": sha256_file(repair_dir / "BULK_SPLIT_RECEIPT.json"),
        },
        "step1_dressed_critical_decay": step1_info,
        "step2_exterior_leakage": {
            "pole_Q650_W": pole_info,
            "archimedean_Q650_K400": arch_info,
            "spatial_Q650_V": spatial_info,
        },
        "step3_schur_coupling_ldlt": schur_info,
        "step4_banded_and_fourier_tail": step4_info,
        "step5_joint_738_block_schur": step5_info,
        "step6_end_to_end_true_integral_l1": step6_info,
    }

    CERT_JSON_PATH.write_text(json.dumps(certificate, indent=2) + "\n", encoding="utf-8")
    print(f"\nSaved certificate in {elapsed:.2f}s to: {CERT_JSON_PATH}")


if __name__ == "__main__":
    main()
