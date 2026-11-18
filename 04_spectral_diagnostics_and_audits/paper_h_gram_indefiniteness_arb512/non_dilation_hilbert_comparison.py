#!/usr/bin/env python3
"""
Track 3: Non-Dilation Legendre/Weil Operator Convergence vs BNBD & Read-Only P650 /
Critical-Subspace Box-Obstruction Audit.

Strictly read-only with respect to ``research/certification_v2/`` and all frozen packages.
Adheres to standing invariant NO_RH_PROOF = True.
"""

from __future__ import annotations

import gzip
import hashlib
import json
import math
import sys
import time
from fractions import Fraction
from pathlib import Path
from typing import Any

import flint
import mpmath as mp

sys.set_int_max_str_digits(50000)

REPO_ROOT = Path(__file__).resolve().parents[3]
CERT_V2_DIR = REPO_ROOT / "research" / "certification_v2"
LAB_DIR = Path(__file__).resolve().parent

if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from research.certification_v2.spatial_overlap import prime_powers  # noqa: E402

# Canonical authenticated symbol tail value h(400).lo used in hybrid_pilot & p650
CERT_BETA_FRACTION = Fraction(
    "1038099100261594740182783860379/250000000000000000000000000000"
)
DEFAULT_ARB_PREC_BITS = 256
DEFAULT_MP_DPS = 80
P650_ARB_PREC_BITS = 256
CCW_MP_DPS = 100


def fraction_to_arb(fr: Fraction) -> flint.arb:
    """Convert an exact Python Fraction to a high-precision flint.arb ball."""
    return flint.arb(int(fr.numerator)) / flint.arb(int(fr.denominator))


def arb_to_mpf(val: flint.arb) -> mp.mpf:
    """Convert midpoint of a flint.arb ball to an mpmath.mpf."""
    return mp.mpf(val.mid().str(90, radius=False))


def fraction_to_mpf(fr: Fraction) -> mp.mpf:
    """Convert an exact Python Fraction to an mpmath.mpf at active mp.dps."""
    return mp.mpf(int(fr.numerator)) / mp.mpf(int(fr.denominator))


def exact_archimedean_h(t: flint.arb) -> flint.arb:
    """Canonical Weil Archimedean symbol h(t) = Re psi(1/4 + i t / 2) - log(pi)."""
    z = flint.acb(flint.arb("0.25"), flint.arb("0.5") * t)
    return z.digamma().real - flint.arb.pi().log()


def spherical_j_0f1(k: int, z: flint.arb) -> flint.arb:
    """Evaluate spherical Bessel j_k(z) via exact 0F1 hypergeometric power series."""
    z2_neg = -(z * z)
    term = (
        (z**k)
        * flint.arb.fac_ui(k)
        * (flint.arb(2) ** k)
        / flint.arb.fac_ui(2 * k + 1)
    )
    total = term
    m = 1
    while m < 150:
        term = term * z2_neg / (2 * m * (2 * k + 2 * m + 1))
        total += term
        if float(abs(term)) < 1e-80 * (float(abs(total)) + 1e-40):
            break
        m += 1
    return total


def spherical_j_vector(K: int, z: flint.arb) -> list[flint.arb]:
    """
    Evaluate [j_0(z), ..., j_{K-1}(z)] with rigorous tight Arb bounds across all z >= 0.

    - |z| <= 2.5: direct 0F1 series per degree (monotone fast convergence).
    - |z| >= K + 2: forward recurrence from exact j_0, j_1 (strictly inside oscillatory regime).
    - 2.5 < |z| < K + 2: backward Miller recurrence from k_top normalized by max(|y_0|, |y_1|).
    """
    if K <= 0:
        return []
    if z == 0:
        return [flint.arb(1)] + [flint.arb(0)] * (K - 1)

    z_f = float(abs(z))
    if z_f <= 2.5:
        return [spherical_j_0f1(k, z) for k in range(K)]

    sin_z, cos_z = z.sin(), z.cos()
    j0 = sin_z / z
    j1 = (j0 - cos_z) / z
    if K == 1:
        return [j0]

    if z_f >= K + 2:
        out = [j0, j1]
        for k in range(1, K - 1):
            out.append((flint.arb(2 * k + 1) / z) * out[-1] - out[-2])
        return out

    k_top = max(K + 75, int(z_f + 6.0 * math.sqrt(z_f)) + 60)
    f_next = flint.arb(0)
    f_curr = flint.arb(1)
    ys: list[flint.arb] = [flint.arb(0)] * (k_top + 1)
    ys[k_top] = f_curr
    for k in range(k_top, 0, -1):
        f_curr, f_next = (flint.arb(2 * k + 1) / z) * f_curr - f_next, f_curr
        ys[k - 1] = f_curr

    norm = j0 / ys[0] if float(abs(ys[0])) >= float(abs(ys[1])) else j1 / ys[1]
    return [ys[k] * norm for k in range(K)]


def spherical_i_0f1(k: int, z: flint.arb) -> flint.arb:
    """Evaluate modified spherical Bessel i_k(z) via exact 0F1 power series."""
    if z == 0:
        return flint.arb(1) if k == 0 else flint.arb(0)
    z2 = z * z
    term = (
        (z**k)
        * flint.arb.fac_ui(k)
        * (flint.arb(2) ** k)
        / flint.arb.fac_ui(2 * k + 1)
    )
    total = term
    m = 1
    while m < 120:
        term = term * z2 / (2 * m * (2 * k + 2 * m + 1))
        total += term
        if float(abs(term)) < 1e-80 * (float(abs(total)) + 1e-40):
            break
        m += 1
    return total


def build_composite_gl_nodes(
    cutoff_T: float = 400.0,
    density_scale: int = 1,
) -> tuple[list[flint.arb], list[flint.arb], list[flint.arb]]:
    """
    Build composite 32-pt Gauss-Legendre quadrature nodes, weights, and precomputed h(t) on [0, T].

    density_scale=1 uses step sizes 0.5 on [0,8], 2.0 on [8,40], 4.0 on [40,400] (3,904 nodes).
    density_scale=2 doubles panel count (halves panel widths, 7,808 nodes) for convergence checks.
    """
    old_dps = mp.mp.dps
    mp.mp.dps = max(85, old_dps)
    try:
        x32, w32 = mp.gauss_quadrature(32, "legendre")
    finally:
        mp.mp.dps = old_dps

    x_arb = [flint.arb(mp.nstr(xi, 82)) for xi in x32]
    w_arb = [flint.arb(mp.nstr(wi, 82)) for wi in w32]

    breakpoints: list[Fraction] = [Fraction(0)]
    segments = [
        (Fraction(0), Fraction(8), Fraction(1, 2 * density_scale)),
        (Fraction(8), Fraction(min(cutoff_T, 40)), Fraction(2, density_scale)),
        (Fraction(min(cutoff_T, 40)), Fraction(cutoff_T), Fraction(4, density_scale)),
    ]
    for a, b, step in segments:
        if b <= a:
            continue
        cur = a
        while cur < b:
            nxt = min(b, cur + step)
            breakpoints.append(nxt)
            cur = nxt

    t_nodes: list[flint.arb] = []
    w_nodes: list[flint.arb] = []
    h_nodes: list[flint.arb] = []
    half = flint.arb("0.5")

    for p_idx in range(len(breakpoints) - 1):
        a_f = fraction_to_arb(breakpoints[p_idx])
        b_f = fraction_to_arb(breakpoints[p_idx + 1])
        mid = (a_f + b_f) * half
        rad = (b_f - a_f) * half
        for xi, wi in zip(x_arb, w_arb):
            t_val = mid + rad * xi
            w_val = rad * wi
            t_nodes.append(t_val)
            w_nodes.append(w_val)
            h_nodes.append(exact_archimedean_h(t_val))

    return t_nodes, w_nodes, h_nodes


def _legendre_poly_values(n_max: int, u: flint.arb) -> list[flint.arb]:
    """Evaluate Legendre polynomials P_0(u), ..., P_{n_max}(u)."""
    if n_max < 0:
        return []
    vals = [flint.arb(1)]
    if n_max >= 1:
        vals.append(u)
    for k in range(1, n_max):
        vals.append(((2 * k + 1) * u * vals[-1] - k * vals[-2]) / (k + 1))
    return vals


def assemble_spatial_matrix_arb(N: int, L_arb: flint.arb, L_float: float) -> flint.arb_mat:
    """
    Assemble the spatial prime-power matrix M_prime(L) of size N x N via exact Gauss-Legendre.

    Since deg(P_i * P_j) <= 2(N-1), (N + 14)-pt Gauss-Legendre integrates every polynomial
    overlap exact to machine/Arb precision (>= 256 bits when >= max(64, N + 16) nodes).
    """
    n_gl = max(64, N + 16)
    old_dps = mp.mp.dps
    mp.mp.dps = max(85, old_dps)
    try:
        x_gl, w_gl = mp.gauss_quadrature(n_gl, "legendre")
    finally:
        mp.mp.dps = old_dps

    x_arb = [flint.arb(mp.nstr(xi, 82)) for xi in x_gl]
    w_arb = [flint.arb(mp.nstr(wi, 82)) for wi in w_gl]

    limit = int(math.floor(math.exp(2.0 * L_float))) + 2
    candidates = prime_powers(limit)
    two_L = 2 * L_arb
    active_terms = []
    for n, p_base in candidates:
        delta = flint.arb(n).log()
        if float(delta.mid()) < float(two_L.mid()) and delta < two_L:
            active_terms.append((n, p_base, delta))

    sqrt_2k1 = [flint.arb(2 * k + 1).sqrt() for k in range(N)]
    M = flint.arb_mat(N, N)
    num_gl = len(x_arb)
    P_u_all = flint.arb_mat(num_gl, N)
    P_v_all = flint.arb_mat(num_gl, N)

    for n, p_base, delta in active_terms:
        half_len = L_arb - delta / 2
        if float(half_len.mid()) <= 0.0:
            continue
        mid = delta / 2
        coef = -(flint.arb(p_base).log() / flint.arb(n).sqrt()) * half_len / L_arb
        half_coef = coef * flint.arb("0.5")

        for q_idx, (xi, wi) in enumerate(zip(x_arb, w_arb)):
            u = mid + half_len * xi
            v = u - delta
            Pu = _legendre_poly_values(N - 1, u / L_arb)
            Pv = _legendre_poly_values(N - 1, v / L_arb)
            for k in range(N):
                scale_k = sqrt_2k1[k]
                P_u_all[q_idx, k] = wi * scale_k * Pu[k]
                P_v_all[q_idx, k] = scale_k * Pv[k]

        cross = P_u_all.transpose() * P_v_all
        for i in range(N):
            for j in range(i, N):
                term_ij = half_coef * (cross[i, j] + cross[j, i])
                M[i, j] += term_ij
                if i != j:
                    M[j, i] += term_ij

    return M


def assemble_pole_matrix_arb(N: int, L_arb: flint.arb) -> flint.arb_mat:
    """Assemble the rank-2 Hermitian pole contribution P_pole(L) of size N x N."""
    half_L = L_arb * flint.arb("0.5")
    v = [
        flint.arb(2 * (2 * k + 1) * L_arb).sqrt() * spherical_i_0f1(k, half_L)
        for k in range(N)
    ]
    P = flint.arb_mat(N, N)
    two = flint.arb(2)
    neg_two = flint.arb(-2)
    for i in range(N):
        sign = two if (i % 2 == 0) else neg_two
        for j in range(i, N):
            if (i - j) % 2 == 0:
                val = sign * v[i] * v[j]
                P[i, j] = val
                if i != j:
                    P[j, i] = val
    return P


def assemble_arch_matrix_arb(
    N: int,
    L_arb: flint.arb,
    beta_arb: flint.arb,
    grid_cache: tuple[list[flint.arb], list[flint.arb], list[flint.arb]],
) -> flint.arb_mat:
    """
    Assemble the Archimedean cutoff matrix integral_[0,T] (h(t) - beta) FourierGram(t) / pi dt
    using vectorized arb_mat outer products decoupled by even/odd Legendre parity.
    """
    t_nodes, w_nodes, h_nodes = grid_cache
    num_pts = len(t_nodes)
    pi = flint.arb.pi()
    sqrt_2k1 = [flint.arb(2 * k + 1).sqrt() for k in range(N)]

    even_degs = list(range(0, N, 2))
    odd_degs = list(range(1, N, 2))

    J_even = flint.arb_mat(num_pts, len(even_degs))
    W_even = flint.arb_mat(num_pts, len(even_degs))
    J_odd = flint.arb_mat(num_pts, len(odd_degs))
    W_odd = flint.arb_mat(num_pts, len(odd_degs))

    for m_idx, (t_m, w_m, h_m) in enumerate(zip(t_nodes, w_nodes, h_nodes)):
        j_vec = spherical_j_vector(N, L_arb * t_m)
        ker = w_m * (h_m - beta_arb)
        for c_idx, k in enumerate(even_degs):
            val = sqrt_2k1[k] * j_vec[k]
            J_even[m_idx, c_idx] = val
            W_even[m_idx, c_idx] = ker * val
        for c_idx, k in enumerate(odd_degs):
            val = sqrt_2k1[k] * j_vec[k]
            J_odd[m_idx, c_idx] = val
            W_odd[m_idx, c_idx] = ker * val

    G_even = J_even.transpose() * W_even if even_degs else flint.arb_mat(0, 0)
    G_odd = J_odd.transpose() * W_odd if odd_degs else flint.arb_mat(0, 0)

    pref = 2 * L_arb / pi
    A = flint.arb_mat(N, N)

    for idx_i, i in enumerate(even_degs):
        for idx_j in range(idx_i, len(even_degs)):
            j = even_degs[idx_j]
            sign = flint.arb(1 if ((i - j) // 2) % 2 == 0 else -1)
            val = pref * sign * G_even[idx_i, idx_j]
            A[i, j] = val
            if i != j:
                A[j, i] = val

    for idx_i, i in enumerate(odd_degs):
        for idx_j in range(idx_i, len(odd_degs)):
            j = odd_degs[idx_j]
            sign = flint.arb(1 if ((i - j) // 2) % 2 == 0 else -1)
            val = pref * sign * G_odd[idx_i, idx_j]
            A[i, j] = val
            if i != j:
                A[j, i] = val

    return A


def assemble_legendre_weil_system(
    N: int,
    L_frac: Fraction,
    beta_arb: flint.arb,
    grid_cache: tuple[list[flint.arb], list[flint.arb], list[flint.arb]],
) -> dict[str, Any]:
    """Assemble full N x N Legendre/Weil operator H = beta*I + arch + spatial + pole."""
    L_arb = fraction_to_arb(L_frac)
    L_float = float(L_frac)
    arch = assemble_arch_matrix_arb(N, L_arb, beta_arb, grid_cache)
    spatial = assemble_spatial_matrix_arb(N, L_arb, L_float)
    pole = assemble_pole_matrix_arb(N, L_arb)

    total = flint.arb_mat(N, N)
    max_rad = 0.0
    for i in range(N):
        for j in range(N):
            val = arch[i, j] + spatial[i, j] + pole[i, j]
            if i == j:
                val += beta_arb
            total[i, j] = val
            rad = float(val.rad())
            if rad > max_rad:
                max_rad = rad

    even_idx = list(range(0, N, 2))
    odd_idx = list(range(1, N, 2))
    H_even = mp.matrix([[arb_to_mpf(total[i, j]) for j in even_idx] for i in even_idx])
    H_odd = mp.matrix([[arb_to_mpf(total[i, j]) for j in odd_idx] for i in odd_idx])

    return {
        "N": N,
        "L_frac": L_frac,
        "L_float": L_float,
        "arch": arch,
        "spatial": spatial,
        "pole": pole,
        "total": total,
        "H_even": H_even,
        "H_odd": H_odd,
        "max_arb_rad": max_rad,
    }


def _ldlt_pivots_mp(M: mp.matrix) -> list[mp.mpf]:
    """Compute diagonal LDL^T pivots of a symmetric mpmath matrix."""
    n = M.rows
    A = M.copy()
    L = mp.eye(n)
    d = [mp.mpf(0)] * n
    for j in range(n):
        s = A[j, j]
        for k in range(j):
            s -= L[j, k] * L[j, k] * d[k]
        d[j] = s
        if abs(s) < mp.mpf("1e-75"):
            continue
        for i in range(j + 1, n):
            t = A[i, j]
            for k in range(j):
                t -= L[i, k] * L[j, k] * d[k]
            L[i, j] = t / s
    return d


def analyze_operator_spectrum(system: dict[str, Any]) -> dict[str, Any]:
    """Compute exact 80-dps sector spectra and LDL^T pivots of an assembled operator."""
    H_even = system["H_even"]
    H_odd = system["H_odd"]

    eig_even = sorted(mp.eigsy(H_even, eigvals_only=True))
    eig_odd = sorted(mp.eigsy(H_odd, eigvals_only=True))
    all_eigs = sorted(eig_even + eig_odd)

    piv_even = _ldlt_pivots_mp(H_even)
    piv_odd = _ldlt_pivots_mp(H_odd)

    lam_min_even = eig_even[0]
    lam_min_odd = eig_odd[0]
    lam_min = all_eigs[0]
    lam_max = all_eigs[-1]

    min_piv_even = min(piv_even)
    min_piv_odd = min(piv_odd)
    cond = lam_max / abs(lam_min) if abs(lam_min) > 0 else mp.inf
    dom_sector = "even" if lam_min_even <= lam_min_odd else "odd"

    return {
        "N": system["N"],
        "L": system["L_float"],
        "n_even": H_even.rows,
        "n_odd": H_odd.rows,
        "max_arb_rad": system["max_arb_rad"],
        "lambda_min_even": float(lam_min_even),
        "lambda_min_odd": float(lam_min_odd),
        "lambda_min_total": float(lam_min),
        "lambda_min_total_str": mp.nstr(lam_min, 25),
        "lambda_max_total": float(lam_max),
        "condition_number": float(cond),
        "dominant_min_sector": dom_sector,
        "even_minus_odd_min_gap": float(lam_min_even - lam_min_odd),
        "neg_count_even": sum(1 for e in eig_even if e < 0),
        "neg_count_odd": sum(1 for e in eig_odd if e < 0),
        "min_pivot_even": float(min_piv_even),
        "min_pivot_odd": float(min_piv_odd),
        "first_3_even": [float(e) for e in eig_even[:3]],
        "first_3_odd": [float(e) for e in eig_odd[:3]],
        "eig_even_mp": eig_even,
        "eig_odd_mp": eig_odd,
        "piv_even_mp": piv_even,
        "piv_odd_mp": piv_odd,
    }


def verify_hybrid_pilot_reference(
    beta_arb: flint.arb,
    grid_cache: tuple[list[flint.arb], list[flint.arb], list[flint.arb]],
) -> dict[str, Any]:
    """Cross-check (N=4, L=1, T=400) against canonical hybrid_pilot/PILOT_RECEIPT.json."""
    receipt_path = CERT_V2_DIR / "hybrid_pilot" / "PILOT_RECEIPT.json"
    receipt = json.loads(receipt_path.read_text(encoding="utf-8"))

    sys4 = assemble_legendre_weil_system(4, Fraction(1, 1), beta_arb, grid_cache)
    spec4 = analyze_operator_spectrum(sys4)

    def _max_block_diff(mat: flint.arb_mat, ref_boxes: list[list[list[str]]]) -> float:
        max_d = 0.0
        for i in range(4):
            for j in range(4):
                lo = fraction_to_arb(Fraction(ref_boxes[i][j][0]))
                hi = fraction_to_arb(Fraction(ref_boxes[i][j][1]))
                mid = (lo + hi) * flint.arb("0.5")
                d = float(abs(mat[i, j].mid() - mid.mid()))
                if d > max_d:
                    max_d = d
        return max_d

    arch_err = _max_block_diff(
        sys4["arch"], receipt["components"]["arch_h_minus_beta_cutoff"]
    )
    spatial_err = _max_block_diff(sys4["spatial"], receipt["components"]["spatial"])
    pole_err = _max_block_diff(sys4["pole"], receipt["components"]["pole"])
    total_err = _max_block_diff(sys4["total"], receipt["hybrid_matrix"])

    piv_even_ref = [
        fraction_to_mpf(
            (Fraction(p[0]) + Fraction(p[1])) / 2
        )
        for p in receipt["sector_ldl"]["even"]["pivots"]
    ]
    piv_odd_ref = [
        fraction_to_mpf(
            (Fraction(p[0]) + Fraction(p[1])) / 2
        )
        for p in receipt["sector_ldl"]["odd"]["pivots"]
    ]
    piv_even_err = max(
        float(abs(a - b)) for a, b in zip(spec4["piv_even_mp"], piv_even_ref)
    )
    piv_odd_err = max(
        float(abs(a - b)) for a, b in zip(spec4["piv_odd_mp"], piv_odd_ref)
    )

    return {
        "receipt_path": str(receipt_path.relative_to(REPO_ROOT)),
        "max_arch_diff": arch_err,
        "max_spatial_diff": spatial_err,
        "max_pole_diff": pole_err,
        "max_total_diff": total_err,
        "max_pivot_even_diff": piv_even_err,
        "max_pivot_odd_diff": piv_odd_err,
        "pivots_even": [float(p) for p in spec4["piv_even_mp"]],
        "pivots_odd": [float(p) for p in spec4["piv_odd_mp"]],
        "eigenvalues_even": [float(e) for e in spec4["eig_even_mp"]],
        "eigenvalues_odd": [float(e) for e in spec4["eig_odd_mp"]],
        "max_arb_rad": sys4["max_arb_rad"],
    }


def _strip_mp_fields(spec: dict[str, Any]) -> dict[str, Any]:
    """Return JSON-serializable summary dictionary from analyze_operator_spectrum."""
    return {
        k: v
        for k, v in spec.items()
        if not k.endswith("_mp")
    }


def _sha256_file(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as fh:
        for chunk in iter(lambda: fh.read(1 << 20), b""):
            h.update(chunk)
    return h.hexdigest()


def _evaluate_p650_box_rayleigh_arb(
    matrix_boxes: list[list[list[str]]],
    vec_strs: list[str],
) -> dict[str, Any]:
    """
    Evaluate 256-bit Arb Rayleigh quotient of an interval matrix [lo, hi] on exact dyadic vector z:
      - rq_mid: z^T M_mid z / (z^T z)
      - box_penalty: (sum_{i,j} rad_{ij} |z_i| |z_j|) / (z^T z)
      - worst_corner: exact worst-case corner matrix in box along z (matches M_{ij}^{lo} if z_i z_j >= 0 else M_{ij}^{hi}).
    """
    dim = len(vec_strs)
    z = [fraction_to_arb(Fraction(s)) for s in vec_strs]
    abs_z = [abs(zi) for zi in z]
    z_mat = flint.arb_mat(dim, 1, z)
    abs_z_mat = flint.arb_mat(dim, 1, abs_z)
    norm_sq = (z_mat.transpose() * z_mat)[0, 0]

    M_mid = flint.arb_mat(dim, dim)
    M_rad = flint.arb_mat(dim, dim)
    max_rad = 0.0
    frob_rad_sq = flint.arb(0)
    half = flint.arb("0.5")

    for i in range(dim):
        row = matrix_boxes[i]
        for j in range(dim):
            lo = fraction_to_arb(Fraction(row[j][0]))
            hi = fraction_to_arb(Fraction(row[j][1]))
            mid = (lo + hi) * half
            rad = (hi - lo) * half
            M_mid[i, j] = mid
            M_rad[i, j] = rad
            r_f = float(rad.mid())
            if r_f > max_rad:
                max_rad = r_f
            frob_rad_sq += rad * rad

    rq_mid = (z_mat.transpose() * (M_mid * z_mat))[0, 0] / norm_sq
    box_pen = (abs_z_mat.transpose() * (M_rad * abs_z_mat))[0, 0] / norm_sq
    worst_corner = rq_mid - box_pen

    return {
        "dim": dim,
        "max_entry_rad": max_rad,
        "frob_rad": float(frob_rad_sq.sqrt().mid()),
        "rq_mid_float": float(rq_mid.mid()),
        "rq_mid_str": rq_mid.str(30),
        "rq_mid_rad": float(rq_mid.rad()),
        "box_penalty_float": float(box_pen.mid()),
        "box_penalty_str": box_pen.str(30),
        "worst_corner_float": float(worst_corner.mid()),
        "worst_corner_str": worst_corner.str(30),
        "worst_corner_rad": float(worst_corner.rad()),
    }


def audit_p650_stable_assembly() -> dict[str, Any]:
    """Read-only 256-bit Arb audit of p650_stable_assembly interval matrices & trial proposals."""
    p650_dir = CERT_V2_DIR / "p650_stable_assembly"
    finite_path = p650_dir / "FINITE_LOWER.json.gz"
    schur_path = p650_dir / "SCHUR_LOWER.json.gz"
    finite_prop_path = p650_dir / "FINITE_LOWER_RAYLEIGH_PROPOSAL.json"
    schur_prop_path = p650_dir / "SCHUR_LOWER_RAYLEIGH_PROPOSAL.json"
    obstruct_path = p650_dir / "SCHUR_INTERVAL_BOX_OBSTRUCTION.json"

    with gzip.open(finite_path, "rt", encoding="utf-8") as fh:
        finite_boxes = json.load(fh)
    with gzip.open(schur_path, "rt", encoding="utf-8") as fh:
        schur_boxes = json.load(fh)

    finite_prop = json.loads(finite_prop_path.read_text(encoding="utf-8"))
    schur_prop = json.loads(schur_prop_path.read_text(encoding="utf-8"))
    obstruct = json.loads(obstruct_path.read_text(encoding="utf-8"))

    old_prec = flint.ctx.prec
    flint.ctx.prec = P650_ARB_PREC_BITS
    try:
        finite_on_z_finite = _evaluate_p650_box_rayleigh_arb(
            finite_boxes, finite_prop["exact_dyadic_trial_vector"]
        )
        finite_on_z_schur = _evaluate_p650_box_rayleigh_arb(
            finite_boxes, schur_prop["exact_dyadic_trial_vector"]
        )
        schur_on_z_schur = _evaluate_p650_box_rayleigh_arb(
            schur_boxes, schur_prop["exact_dyadic_trial_vector"]
        )
        schur_on_z_finite = _evaluate_p650_box_rayleigh_arb(
            schur_boxes, finite_prop["exact_dyadic_trial_vector"]
        )

        # Cross-check against exact rational corner interval in SCHUR_INTERVAL_BOX_OBSTRUCTION
        obs_lo = fraction_to_arb(Fraction(obstruct["normalized_corner_rayleigh_enclosure"][0]))
        obs_hi = fraction_to_arb(Fraction(obstruct["normalized_corner_rayleigh_enclosure"][1]))
        obs_mid = (obs_lo + obs_hi) * flint.arb("0.5")
        schur_corner_ball = flint.arb(schur_on_z_schur["worst_corner_str"].split()[0].lstrip("["))
        corner_obs_diff = float(
            abs(
                fraction_to_arb(Fraction(obstruct["normalized_corner_rayleigh_enclosure"][0])).mid()
                - flint.arb(schur_on_z_schur["worst_corner_float"]).mid()
            )
        )
        # Rigorous interval overlap check using full mid/rad
        lo_s, hi_s = obstruct["normalized_corner_rayleigh_enclosure"]
        diff_from_obs_mid = abs(schur_on_z_schur["worst_corner_float"] - float(obs_mid.mid()))
    finally:
        flint.ctx.prec = old_prec

    return {
        "sha256_verified": {
            "FINITE_LOWER.json.gz": _sha256_file(finite_path),
            "FINITE_LOWER_proposal_expected": finite_prop["matrix_sha256"],
            "FINITE_match": _sha256_file(finite_path) == finite_prop["matrix_sha256"],
            "SCHUR_LOWER.json.gz": _sha256_file(schur_path),
            "SCHUR_LOWER_proposal_expected": schur_prop["matrix_sha256"],
            "SCHUR_match": _sha256_file(schur_path) == schur_prop["matrix_sha256"],
        },
        "float64_reported_min_eigenvalues": {
            "FINITE_LOWER_proposal": finite_prop["minimum_midpoint_eigenvalue"],
            "FINITE_LOWER_first_five": finite_prop["first_ten_midpoint_eigenvalues"][:5],
            "SCHUR_LOWER_proposal": schur_prop["minimum_midpoint_eigenvalue"],
            "SCHUR_LOWER_first_five": schur_prop["first_ten_midpoint_eigenvalues"][:5],
        },
        "box_inflation_ratios_schur_over_finite": {
            "max_entry_rad_ratio": (
                schur_on_z_schur["max_entry_rad"] / finite_on_z_finite["max_entry_rad"]
            ),
            "frob_rad_ratio": (
                schur_on_z_schur["frob_rad"] / finite_on_z_finite["frob_rad"]
            ),
            "box_penalty_on_z_schur_ratio": (
                schur_on_z_schur["box_penalty_float"] / finite_on_z_schur["box_penalty_float"]
            ),
        },
        "FINITE_LOWER_on_z_finite": finite_on_z_finite,
        "FINITE_LOWER_on_z_schur": finite_on_z_schur,
        "SCHUR_LOWER_on_z_schur": schur_on_z_schur,
        "SCHUR_LOWER_on_z_finite": schur_on_z_finite,
        "schur_obstruction_enclosure_float_mid": float(obs_mid.mid()),
        "schur_corner_vs_obstruction_abs_diff": diff_from_obs_mid,
    }


def audit_critical_composition_writer() -> dict[str, Any]:
    """Read-only 100-dps mpmath audit of direct_critical_form/CRITICAL_COMPOSITION_WRITER.json."""
    ccw_path = CERT_V2_DIR / "direct_critical_form" / "CRITICAL_COMPOSITION_WRITER.json"
    ccw = json.loads(ccw_path.read_text(encoding="utf-8"))
    boxes = ccw["boxes"]
    dim = len(boxes)
    pen_frac = Fraction(ccw["bulk_solve_penalty"])

    old_dps = mp.mp.dps
    mp.mp.dps = CCW_MP_DPS
    try:
        M_mid = mp.zeros(dim, dim)
        max_rad = mp.mpf(0)
        for i in range(dim):
            for j in range(dim):
                lo_f = Fraction(boxes[i][j][0])
                hi_f = Fraction(boxes[i][j][1])
                mid_f = (lo_f + hi_f) / 2
                rad_f = (hi_f - lo_f) / 2
                M_mid[i, j] = fraction_to_mpf(mid_f)
                rad_mp = fraction_to_mpf(rad_f)
                if rad_mp > max_rad:
                    max_rad = rad_mp

        pen_mp = fraction_to_mpf(pen_frac)
        M_pre = M_mid + pen_mp * mp.eye(dim)

        evs_post = sorted(mp.eigsy(M_mid, eigvals_only=True))
        evs_pre = sorted(mp.eigsy(M_pre, eigvals_only=True))
        pivots_post = _ldlt_pivots_mp(M_mid)
        pivots_pre = _ldlt_pivots_mp(M_pre)
    finally:
        mp.mp.dps = old_dps

    test0 = ccw["tests"][0]["result"]
    test0_piv0 = float((Fraction(test0["pivots"][0][0]) + Fraction(test0["pivots"][0][1])) / 2)

    return {
        "ccw_path": str(ccw_path.relative_to(REPO_ROOT)),
        "ccw_sha256": _sha256_file(ccw_path),
        "dim": dim,
        "status": ccw["status"],
        "max_entry_rad": float(max_rad),
        "max_entry_rad_str": mp.nstr(max_rad, 15),
        "bulk_solve_penalty": float(pen_mp),
        "bulk_solve_penalty_str": mp.nstr(pen_mp, 20),
        "pre_penalty_all_positive": all(e > 0 for e in evs_pre),
        "pre_penalty_eigenvalues_float": [float(e) for e in evs_pre],
        "pre_penalty_eigenvalues_str": [mp.nstr(e, 16) for e in evs_pre],
        "pre_penalty_condition_number_str": mp.nstr(evs_pre[-1] / evs_pre[0], 16),
        "post_penalty_neg_count": sum(1 for e in evs_post if e < 0),
        "post_penalty_eigenvalues_float": [float(e) for e in evs_post],
        "post_penalty_eigenvalues_str": [mp.nstr(e, 16) for e in evs_post],
        "post_penalty_ldlt_first_negative_index": next(
            (idx for idx, p in enumerate(pivots_post) if p <= 0), None
        ),
        "pre_penalty_ldlt_min_pivot_str": mp.nstr(min(pivots_pre), 16),
        "ccw_test0_failed_pivot": test0["failed_pivot"],
        "ccw_test0_piv0_abs_diff": abs(float(pivots_post[0]) - test0_piv0),
    }


def main() -> None:
    t_start = time.perf_counter()
    flint.ctx.prec = DEFAULT_ARB_PREC_BITS
    mp.mp.dps = DEFAULT_MP_DPS

    beta_arb = fraction_to_arb(CERT_BETA_FRACTION)
    exact_h400 = exact_archimedean_h(flint.arb(400))

    print("1. Building composite 32-pt Gauss-Legendre grid on [0, 400] (256-bit Arb)...")
    grid_base = build_composite_gl_nodes(cutoff_T=400.0, density_scale=1)
    print(f"   Base grid nodes: {len(grid_base[0])} ({time.perf_counter() - t_start:.2f}s)")

    print("2. Verifying N=4, L=1, T=400 reference parity vs hybrid_pilot/PILOT_RECEIPT.json...")
    ref_check = verify_hybrid_pilot_reference(beta_arb, grid_base)
    print(
        f"   max_total_diff={ref_check['max_total_diff']:.3e}, "
        f"max_pivot_diff={max(ref_check['max_pivot_even_diff'], ref_check['max_pivot_odd_diff']):.3e}"
    )

    print("3. Quadrature-doubling check on N=50, L=1.0, T=400...")
    sys_n50_base = assemble_legendre_weil_system(50, Fraction(1, 1), beta_arb, grid_base)
    spec_n50_base = analyze_operator_spectrum(sys_n50_base)

    grid_double = build_composite_gl_nodes(cutoff_T=400.0, density_scale=2)
    sys_n50_double = assemble_legendre_weil_system(50, Fraction(1, 1), beta_arb, grid_double)
    spec_n50_double = analyze_operator_spectrum(sys_n50_double)

    quad_max_mat_diff = max(
        float(abs(sys_n50_base["total"][i, j].mid() - sys_n50_double["total"][i, j].mid()))
        for i in range(50)
        for j in range(50)
    )
    quad_min_eig_diff = float(
        abs(spec_n50_base["eig_even_mp"][0] - spec_n50_double["eig_even_mp"][0])
    )
    quad_check = {
        "N": 50,
        "L": 1.0,
        "T": 400.0,
        "base_nodes": len(grid_base[0]),
        "double_nodes": len(grid_double[0]),
        "max_matrix_entry_diff": quad_max_mat_diff,
        "lambda_min_even_diff": quad_min_eig_diff,
        "lambda_min_total_diff": abs(
            spec_n50_base["lambda_min_total"] - spec_n50_double["lambda_min_total"]
        ),
        "base_max_arb_rad": sys_n50_base["max_arb_rad"],
        "double_max_arb_rad": sys_n50_double["max_arb_rad"],
    }
    print(
        f"   Quadrature doubling N=50: max_mat_diff={quad_max_mat_diff:.3e}, "
        f"lambda_min_diff={quad_min_eig_diff:.3e}"
    )

    # Sensitivity between certified beta=h(400).lo and exact h(400)
    sys_n50_exact_beta = assemble_legendre_weil_system(
        50, Fraction(1, 1), exact_h400, grid_base
    )
    spec_n50_exact_beta = analyze_operator_spectrum(sys_n50_exact_beta)
    beta_sensitivity = {
        "cert_beta_float": float(beta_arb.mid()),
        "exact_h400_float": float(exact_h400.mid()),
        "beta_gap": float((exact_h400 - beta_arb).mid()),
        "lambda_min_cert_beta": spec_n50_base["lambda_min_total"],
        "lambda_min_exact_h400": spec_n50_exact_beta["lambda_min_total"],
        "lambda_min_abs_diff": abs(
            spec_n50_base["lambda_min_total"] - spec_n50_exact_beta["lambda_min_total"]
        ),
    }

    print("4. Running dimension scaling sweep L=1.0, T=400 across N in [4,8,12,16,20,30,40,50]...")
    bnbd_data = json.loads(
        (LAB_DIR / "sparse_bnbd_compression_results.json").read_text(encoding="utf-8")
    )
    bnbd_full = bnbd_data["consecutive_baseline_full"]

    dim_list = [4, 8, 12, 16, 20, 30, 40, 50]
    dim_specs: list[dict[str, Any]] = []
    lam50_mp = min(spec_n50_base["eig_even_mp"][0], spec_n50_base["eig_odd_mp"][0])

    # Slice top-left N x N submatrices directly from sys_n50_base (Galerkin projection!)
    for N_val in dim_list:
        if N_val == 50:
            spec_n = spec_n50_base
        else:
            even_idx = list(range(0, N_val, 2))
            odd_idx = list(range(1, N_val, 2))
            sub_even = mp.matrix(
                [[sys_n50_base["H_even"][i, j] for j in range(len(even_idx))] for i in range(len(even_idx))]
            )
            sub_odd = mp.matrix(
                [[sys_n50_base["H_odd"][i, j] for j in range(len(odd_idx))] for i in range(len(odd_idx))]
            )
            sub_sys = {
                "N": N_val,
                "L_float": 1.0,
                "H_even": sub_even,
                "H_odd": sub_odd,
                "max_arb_rad": sys_n50_base["max_arb_rad"],
            }
            spec_n = analyze_operator_spectrum(sub_sys)

        row = _strip_mp_fields(spec_n)
        lam_mp = min(spec_n["eig_even_mp"][0], spec_n["eig_odd_mp"][0])
        row["abs_delta_from_N50"] = float(abs(lam_mp - lam50_mp))
        row["bnbd_consecutive_dN2"] = bnbd_full[str(N_val)]
        dim_specs.append(row)
        print(
            f"   N={N_val:2d}: lam_min={row['lambda_min_total']:.12f} "
            f"(delta50={row['abs_delta_from_N50']:.2e}), d_N^2={row['bnbd_consecutive_dN2']:.6f}"
        )

    print("5. Running support-length L sweep at N=30 & N=50...")
    L_sweep_specs: list[tuple[str, Fraction]] = [
        ("0.80", Fraction(4, 5)),
        ("0.90", Fraction(9, 10)),
        ("0.95", Fraction(19, 20)),
        ("0.975", Fraction(39, 40)),
        ("1.00", Fraction(1, 1)),
        ("1.05", Fraction(21, 20)),
        ("1.10", Fraction(11, 10)),
        ("1.15", Fraction(23, 20)),
        ("log(11)/2", Fraction("1198947636399185/1000000000000000")),
    ]

    length_sweep: list[dict[str, Any]] = []
    for label, L_frac in L_sweep_specs:
        if L_frac == Fraction(1, 1):
            sys50 = sys_n50_base
            spec50 = spec_n50_base
        else:
            sys50 = assemble_legendre_weil_system(50, L_frac, beta_arb, grid_base)
            spec50 = analyze_operator_spectrum(sys50)

        # Galerkin N=30 subblock of exact same L system
        even30 = mp.matrix([[sys50["H_even"][i, j] for j in range(15)] for i in range(15)])
        odd30 = mp.matrix([[sys50["H_odd"][i, j] for j in range(15)] for i in range(15)])
        spec30 = analyze_operator_spectrum(
            {
                "N": 30,
                "L_float": float(L_frac),
                "H_even": even30,
                "H_odd": odd30,
                "max_arb_rad": sys50["max_arb_rad"],
            }
        )

        # Active prime powers check
        two_L_val = 2.0 * float(L_frac)
        act = [
            n
            for n, _p in prime_powers(int(math.floor(math.exp(two_L_val))) + 2)
            if math.log(n) < two_L_val
        ]

        entry_row = {
            "L_label": label,
            "L_float": float(L_frac),
            "active_prime_power_count": len(act),
            "active_prime_powers_max_n": max(act) if act else 0,
            "n50": _strip_mp_fields(spec50),
            "n30": _strip_mp_fields(spec30),
            "n30_vs_n50_lambda_min_diff": abs(
                spec30["lambda_min_total"] - spec50["lambda_min_total"]
            ),
        }
        length_sweep.append(entry_row)
        print(
            f"   L={label:>9s}: primes_max_n={entry_row['active_prime_powers_max_n']:2d}, "
            f"even_min={spec50['lambda_min_even']:.9f}, odd_min={spec50['lambda_min_odd']:.9f}, "
            f"dom={spec50['dominant_min_sector']:>4s}, n30_n50_diff={entry_row['n30_vs_n50_lambda_min_diff']:.2e}"
        )

    print("6. Running Read-Only 256-bit Arb audit of p650_stable_assembly...")
    p650_audit = audit_p650_stable_assembly()
    print(
        f"   FINITE on z_finite rq_mid={p650_audit['FINITE_LOWER_on_z_finite']['rq_mid_float']:.6e}, "
        f"worst_corner={p650_audit['FINITE_LOWER_on_z_finite']['worst_corner_float']:.6e}"
    )
    print(
        f"   FINITE on z_schur  rq_mid={p650_audit['FINITE_LOWER_on_z_schur']['rq_mid_float']:.6e}, "
        f"worst_corner={p650_audit['FINITE_LOWER_on_z_schur']['worst_corner_float']:.6e}"
    )
    print(
        f"   SCHUR  on z_schur  rq_mid={p650_audit['SCHUR_LOWER_on_z_schur']['rq_mid_float']:.6e}, "
        f"worst_corner={p650_audit['SCHUR_LOWER_on_z_schur']['worst_corner_float']:.6e}"
    )

    print("7. Running Read-Only 100-dps mpmath audit of CRITICAL_COMPOSITION_WRITER...")
    ccw_audit = audit_critical_composition_writer()
    print(
        f"   pre_penalty all>0: {ccw_audit['pre_penalty_all_positive']} "
        f"(min={ccw_audit['pre_penalty_eigenvalues_str'][0]}), "
        f"post_penalty neg={ccw_audit['post_penalty_neg_count']} "
        f"(min={ccw_audit['post_penalty_eigenvalues_str'][0]})"
    )

    elapsed = round(time.perf_counter() - t_start, 3)
    output_payload = {
        "metadata": {
            "arb_prec_bits": DEFAULT_ARB_PREC_BITS,
            "mp_dps": DEFAULT_MP_DPS,
            "p650_arb_prec_bits": P650_ARB_PREC_BITS,
            "ccw_mp_dps": CCW_MP_DPS,
            "cert_beta_fraction": str(CERT_BETA_FRACTION),
            "cert_beta_float": float(beta_arb.mid()),
            "exact_h400_float": float(exact_h400.mid()),
            "cutoff_T": 400.0,
            "total_seconds": elapsed,
            "NO_RH_PROOF": True,
        },
        "reference_cross_check_n4_l1_t400": ref_check,
        "quadrature_verification_n50_l1_t400": quad_check,
        "beta_sensitivity_n50_l1_t400": beta_sensitivity,
        "dimension_scaling_L1_T400": dim_specs,
        "length_transition_sweep": length_sweep,
        "p650_stable_assembly_audit": p650_audit,
        "critical_composition_writer_audit": ccw_audit,
    }

    out_path = LAB_DIR / "non_dilation_and_p650_diagnostic_results.json"
    out_path.write_text(json.dumps(output_payload, indent=2), encoding="utf-8")
    print(f"Saved Track 3 results to {out_path} in {elapsed:.2f}s.")


if __name__ == "__main__":
    main()
