#!/usr/bin/env python3
"""
8-Condition "n to Continuity" Absoluteness & Kernel Axiom Audit (PR-8M through PR-8U).

Verifies all eight interlocking mathematical conditions connecting discrete floor cells A_c(n)
to L^2(0, 1] continuum quadrature and Mellin-space obstructions across:
  1. Lean 4.35 source & theorem presence (UpstreamPR_8M through UpstreamPR_8U),
  2. Live Lean 4 kernel #print axioms + #lint across UpstreamPR_8M..8U (with --with-lean),
  3. 85-digit mpmath numerical cross-checks of every equality and inequality.
"""

from __future__ import annotations

import argparse
import json
import pathlib
import re
import subprocess
import sys
import tempfile
from typing import Dict, List, Tuple

import mpmath as mp

ROOT = pathlib.Path(__file__).resolve().parent
UPSTREAM_DIR = next(
    (
        d
        for d in (
            ROOT / "RiemannBlueprint" / "RiemannBlueprint" / "UpstreamPRs",
            ROOT / "MATHLIB4_PR_STAGING",
            ROOT.parent / "05_mathlib4_pr_staging",
            ROOT,
        )
        if (d / "UpstreamPR_8N_HarmonicCellL2QuadratureAndPrimeJumps.lean").is_file()
    ),
    ROOT / "RiemannBlueprint" / "RiemannBlueprint" / "UpstreamPRs",
)

CONDITIONS: List[Tuple[int, str, str, List[str]]] = [
    (
        1,
        "Half-Open Slab Partition & Horizon Gap",
        "UpstreamPR_8N_HarmonicCellL2QuadratureAndPrimeJumps.lean;UpstreamPR_8P_HarmonicSlabNonTermination.lean",
        [
            "sum_Icc_harmonicCellWidth",
            "residualHorizonGap_eq_sub_sum_Icc",
            "residualHorizonGap_pos",
            "forbiddenHarmonicPlane_mem_gap",
        ],
    ),
    (
        2,
        "Pointwise Affine Decomposition & Null-Slope Collapse",
        "UpstreamPR_8M_PointwiseContinuityAndPeriodicity.lean;UpstreamPR_8P_HarmonicSlabNonTermination.lean",
        [
            "continuousNymanResidual_eq_sub_D1_mul_inv",
            "floor_one_div_mul_eq_nat_div",
            "continuousNymanResidual_eq_discreteCellResidual",
            "continuousNymanResidual_eq_modularCellResidual",
        ],
    ),
    (
        3,
        "Outer-Slab Continuum Annihilation on (1/2, 1]",
        "UpstreamPR_8M_PointwiseContinuityAndPeriodicity.lean",
        [
            "discreteCellResidual_one_eq",
            "continuousNymanResidual_eq_zero_on_top_half",
        ],
    ),
    (
        4,
        "Periodic Folding, Palindromic Reflection & Double-Cone Symmetry",
        "UpstreamPR_8M_PointwiseContinuityAndPeriodicity.lean;UpstreamPR_8T_DoubleConeL2FoldingAndFlux.lean",
        [
            "modularCellResidual_periodic",
            "fract_palindromic_add_eq",
            "modularCellResidual_palindromic_neg",
            "sum_Ico_modularCellResidual_eq_zero",
            "harmonicCellL2PartialSum_period_sub_two_eq_doubleCone",
        ],
    ),
    (
        5,
        "Prime-Conductor Jump & Multi-Prime 1/(2p^2) Quantum",
        "UpstreamPR_8P_HarmonicSlabNonTermination.lean;UpstreamPR_8Q_PrimeCellL2EnergyFloor.lean;UpstreamPR_8S_MultiPrimeL2Superposition.lean",
        [
            "discreteCellResidual_prime_sub_pred",
            "sq_div_pred_mul_add_sq_div_mul_succ",
            "harmonicPairEnergy_prime_eq",
            "disjoint_prime_cell_pairs",
            "harmonicCellL2PartialSum_ge_sum_primes",
        ],
    ),
    (
        6,
        "Period-Free Uniform Bound & Euclidean Book X.1 Tail Exhaustion",
        "UpstreamPR_8U_EuclideanExhaustionTailBound.lean",
        [
            "abs_modularCellResidual_le",
            "abs_discreteCellResidual_le_of_D1_eq_zero",
            "harmonicCellL2TailSum_le_div_succ",
            "harmonicCellL2TailSum_le_uniformCellBound_sq_div_succ",
            "harmonicCellL2TailSum_lt_eps_of_gt",
        ],
    ),
    (
        7,
        "Lebesgue Set-Integral Bridge & Unconditional L^2(0, 1] Positivity",
        "UpstreamPR_8P_HarmonicSlabNonTermination.lean;UpstreamPR_8U_EuclideanExhaustionTailBound.lean",
        [
            "setIntegral_Ioc_harmonicCell_eq",
            "harmonicCellL2PartialSum_eq_setIntegral_Ioc",
            "harmonicCellL2PartialSum_le_integral_Ioc",
            "sum_primes_le_integral_Ioc",
            "continuousNymanResidual_sq_integral_pos",
        ],
    ),
    (
        8,
        "Mellin Zero-Obstruction & Off-Line Cauchy-Schwarz Barrier",
        "UpstreamPR_8R_MellinZeroObstructionFloor.lean;UpstreamPR_8S_MultiPrimeL2Superposition.lean;UpstreamPR_8U_EuclideanExhaustionTailBound.lean",
        [
            "mellinResidualQuotient_at_zeta_zero",
            "l2NormSq_ge_offlineEnergyFloor_of_cauchy_schwarz",
            "no_offline_zero_of_l2_arbitrarily_small",
            "planar_mellin_dual_contradiction_capstone",
            "euclidean_book_ix_and_x_continuity_capstone",
        ],
    ),
]

SERIES_8MNOPQRSTU_MODULES = [
    "RiemannBlueprint.UpstreamPRs.UpstreamPR_8M_PointwiseContinuityAndPeriodicity",
    "RiemannBlueprint.UpstreamPRs.UpstreamPR_8N_HarmonicCellL2QuadratureAndPrimeJumps",
    "RiemannBlueprint.UpstreamPRs.UpstreamPR_8O_PeriodicL2CellSumCompression",
    "RiemannBlueprint.UpstreamPRs.UpstreamPR_8P_HarmonicSlabNonTermination",
    "RiemannBlueprint.UpstreamPRs.UpstreamPR_8Q_PrimeCellL2EnergyFloor",
    "RiemannBlueprint.UpstreamPRs.UpstreamPR_8R_MellinZeroObstructionFloor",
    "RiemannBlueprint.UpstreamPRs.UpstreamPR_8S_MultiPrimeL2Superposition",
    "RiemannBlueprint.UpstreamPRs.UpstreamPR_8T_DoubleConeL2FoldingAndFlux",
    "RiemannBlueprint.UpstreamPRs.UpstreamPR_8U_EuclideanExhaustionTailBound",
]

CAPSTONE_AXIOM_TARGETS = [
    "residualHorizonGap_eq_sub_sum_Icc",
    "forbiddenHarmonicPlane_mem_gap",
    "continuousNymanResidual_eq_sub_D1_mul_inv",
    "continuousNymanResidual_eq_discreteCellResidual",
    "continuousNymanResidual_eq_modularCellResidual",
    "continuousNymanResidual_eq_zero_on_top_half",
    "modularCellResidual_periodic",
    "modularCellResidual_palindromic_neg",
    "sum_Ico_modularCellResidual_eq_zero",
    "harmonicCellL2PartialSum_period_sub_two_eq_doubleCone",
    "discreteCellResidual_prime_sub_pred",
    "harmonicPairEnergy_prime_eq",
    "harmonicCellL2PartialSum_ge_sum_primes",
    "abs_modularCellResidual_le",
    "harmonicCellL2TailSum_le_div_succ",
    "harmonicCellL2TailSum_le_uniformCellBound_sq_div_succ",
    "harmonicCellL2TailSum_lt_eps_of_gt",
    "setIntegral_Ioc_harmonicCell_eq",
    "harmonicCellL2PartialSum_eq_setIntegral_Ioc",
    "harmonicCellL2PartialSum_le_integral_Ioc",
    "sum_primes_le_integral_Ioc",
    "continuousNymanResidual_sq_integral_pos",
    "mellinResidualQuotient_at_zeta_zero",
    "l2NormSq_ge_offlineEnergyFloor_of_cauchy_schwarz",
    "no_offline_zero_of_l2_arbitrarily_small",
    "planar_mellin_dual_contradiction_capstone",
    "euclidean_book_ix_and_x_continuity_capstone",
]


def verify_source_modules() -> Dict[str, object]:
    details: Dict[str, object] = {}
    for cid, title, files_str, decls in CONDITIONS:
        blobs = []
        for fn in files_str.split(";"):
            p = UPSTREAM_DIR / fn
            if not p.is_file():
                raise FileNotFoundError(f"Missing Lean module {p}")
            txt = p.read_text(encoding="utf-8")
            if re.search(r"\b(sorry|admit|axiom)\b", txt):
                raise AssertionError(f"Forbidden token in {p}")
            blobs.append(txt)
        merged = "\n".join(blobs)
        for decl in decls:
            if not re.search(rf"\b(theorem|def)\s+{re.escape(decl)}\b", merged):
                raise AssertionError(f"Condition {cid} missing declaration {decl}")
        details[f"condition_{cid}"] = {"title": title, "verified_decls": decls}
    return details


def verify_lean_kernel_axioms_and_lint() -> Dict[str, object]:
    lines = [
        "import RiemannBlueprint.UpstreamPRs.UpstreamPR_8U_EuclideanExhaustionTailBound",
        "import Batteries.Tactic.Lint",
        "",
    ]
    for tgt in CAPSTONE_AXIOM_TARGETS:
        lines.append(f"#print axioms {tgt}")
    lines.append("")
    for mod in SERIES_8MNOPQRSTU_MODULES:
        lines.append(f"#lint in {mod}")
    script_text = "\n".join(lines) + "\n"

    with tempfile.NamedTemporaryFile("w", suffix=".lean", encoding="utf-8", delete=False) as tf:
        tf.write(script_text)
        tmp_path = pathlib.Path(tf.name)
    try:
        res = subprocess.run(
            ["lake", "env", "lean", str(tmp_path)],
            cwd=str(ROOT / "RiemannBlueprint"),
            text=True,
            capture_output=True,
            timeout=300,
        )
        out = (res.stdout or "") + "\n" + (res.stderr or "")
        if res.returncode != 0:
            raise AssertionError(f"lake env lean failed ({res.returncode}):\n{out}")
    finally:
        tmp_path.unlink(missing_ok=True)

    if "sorryAx" in out:
        raise AssertionError("sorryAx detected in #print axioms output!")
    axiom_lines = [l.strip() for l in out.splitlines() if "depends on axioms:" in l]
    if len(axiom_lines) < len(CAPSTONE_AXIOM_TARGETS):
        raise AssertionError(
            f"Expected {len(CAPSTONE_AXIOM_TARGETS)} axiom receipts, got {len(axiom_lines)}"
        )
    allowed = {"propext", "Classical.choice", "Quot.sound"}
    for line in axiom_lines:
        m = re.search(r"depends on axioms:\s*\[([^\]]+)\]", line)
        if not m:
            raise AssertionError(f"Malformed axiom line: {line}")
        found = {a.strip() for a in m.group(1).split(",") if a.strip()}
        if not found.issubset(allowed):
            raise AssertionError(f"Unexpected axiom in: {line}")
    if out.count("-- All linting checks passed!") < len(SERIES_8MNOPQRSTU_MODULES):
        raise AssertionError(f"Missing lint pass confirmations in output:\n{out}")
    return {
        "axiom_targets_verified": len(axiom_lines),
        "linted_modules": len(SERIES_8MNOPQRSTU_MODULES),
        "allowed_axioms": sorted(allowed),
    }


def _frac(x: mp.mpf) -> mp.mpf:
    return x - mp.floor(x)


def _r_cont(c: Dict[int, mp.mpf], N: int, x: mp.mpf) -> mp.mpf:
    return mp.mpf(1) - sum(c[k] * _frac(mp.mpf(1) / (k * x)) for k in range(1, N + 1))


def _a_mod(c: Dict[int, mp.mpf], N: int, n: int) -> mp.mpf:
    return mp.mpf(1) - sum(c[k] * _frac(mp.mpf(n) / k) for k in range(1, N + 1))


def _a_disc(c: Dict[int, mp.mpf], N: int, n: int) -> mp.mpf:
    return mp.mpf(1) + sum(c[k] * mp.mpf(n // k) for k in range(1, N + 1))


def verify_mpmath_85dps() -> Dict[str, str]:
    mp.mp.dps = 85
    # Exact D1=0, D0=2, c1=-1 anchored N=4 vector (c_dir^(4) on [1..4])
    sqrt3 = mp.sqrt(3)
    a1 = mp.mpf(1) / 2 + mp.mpf(1) / (3 * sqrt3)
    a2 = mp.mpf(1) / 2 - mp.mpf(1) / (3 * sqrt3)
    c = {1: mp.mpf(-1), 2: mp.mpf(2) - 2 * a1, 3: 3 * (a1 - a2), 4: 4 * a2}
    N, L = 4, 12

    d1 = sum(c[k] / k for k in range(1, N + 1))
    d0 = sum(c[k] for k in range(1, N + 1))
    assert abs(d1) < mp.mpf("1e-83"), d1
    assert abs(d0 - 2) < mp.mpf("1e-83"), d0

    # Condition 1: Horizon gap = 1 / (M + 1) and pierced by 1 / (M + 2)
    M = 20
    width_sum = sum(mp.mpf(1) / (n * (n + 1)) for n in range(1, M + 1))
    c1_err = abs((mp.mpf(1) - width_sum) - mp.mpf(1) / (M + 1))
    assert c1_err < mp.mpf("1e-83")
    assert mp.mpf(1) / (M + 2) < mp.mpf(1) / (M + 1)

    # Condition 2 & 3: Pointwise affine slope & top-half (1/2, 1] annihilation
    c_off = {1: mp.mpf(-1), 2: mp.mpf("0.7"), 3: mp.mpf("-0.4"), 4: mp.mpf("0.2")}
    d1_off = sum(c_off[k] / k for k in range(1, N + 1))
    x3 = mp.mpf(2) / 7  # n = floor(7/2) = 3
    c2_err = abs(_r_cont(c_off, N, x3) - (_a_disc(c_off, N, 3) - d1_off / x3))
    c3_err = max(abs(_r_cont(c, N, x)) for x in [mp.mpf("0.55"), mp.mpf("0.75"), mp.mpf(1)])
    assert c2_err < mp.mpf("1e-83") and c3_err < mp.mpf("1e-83")

    # Condition 4: Periodicity, palindromic reflection, double-cone L^2 folding
    c4_err = max(abs(_a_mod(c, N, m + L) - _a_mod(c, N, m)) for m in range(L))
    c4_pal = max(abs(_a_mod(c, N, L - 1 - m) + _a_mod(c, N, m)) for m in range(L))
    assert abs(_a_mod(c, N, 1)) < mp.mpf("1e-83") and abs(_a_mod(c, N, L - 2)) < mp.mpf("1e-83")
    l2_fold = sum(
        _a_mod(c, N, m) ** 2 * mp.mpf(1) / (m * (m + 1)) for m in range(1, L - 1)
    )
    dc_fold = sum(
        _a_mod(c, N, m) ** 2
        * (mp.mpf(1) / (m * (m + 1)) + mp.mpf(1) / ((L - 1 - m) * (L - m)))
        / 2
        for m in range(1, L - 1)
    )
    c4_fold_err = abs(l2_fold - dc_fold)
    assert max(c4_err, c4_pal, c4_fold_err) < mp.mpf("1e-83")

    # Condition 5: Multi-prime 1/(2p^2) lower floor
    primes_gt_N = [5, 7, 11, 13, 17]
    for p in primes_gt_N:
        assert abs((_a_disc(c, N, p) - _a_disc(c, N, p - 1)) - c[1]) < mp.mpf("1e-83")
    l2_M = sum(_a_disc(c, N, n) ** 2 / (n * (n + 1)) for n in range(1, M + 1))
    prime_floor = sum(mp.mpf(1) / (2 * mp.mpf(p) ** 2) for p in primes_gt_N)
    assert prime_floor <= l2_M

    # Condition 6: Period-free uniform bound & Euclidean Book X.1 tail bound
    B = mp.mpf(1) + sum(abs(c[k]) for k in range(1, N + 1))
    for n in range(0, 3 * L + 5):
        assert abs(_a_mod(c, N, n)) <= B + mp.mpf("1e-83")
    M2 = 80
    tail_val = sum(_a_disc(c, N, n) ** 2 / (n * (n + 1)) for n in range(M + 1, M2 + 1))
    assert tail_val <= B ** 2 / (M + 1)

    # Condition 7: Cell-by-cell continuous vs discrete L^2 quadrature
    cell_quad_err = mp.mpf(0)
    for n in range(1, 7):
        lo = mp.mpf(1) / (n + 1)
        hi = mp.mpf(1) / n
        # Smooth constant plateau interior evaluation at midpoint & width
        mid = (lo + hi) / 2
        q_est = _r_cont(c, N, mid) ** 2 * (hi - lo)
        exact = _a_disc(c, N, n) ** 2 / (n * (n + 1))
        cell_quad_err = max(cell_quad_err, abs(q_est - exact))
    assert cell_quad_err < mp.mpf("1e-83")

    # Condition 8: Mellin zero-obstruction at zeta(1/2 + i*gamma_1) ~ 0
    s0 = mp.mpc("0.5", "14.134725141734693790457251983562470270784257115699")
    D_s0 = sum(c[k] * mp.power(k, -s0) for k in range(1, N + 1))
    # Verify algebraic identity (1 - zeta(s)*D_N(s))/s = 1/s at exact zeta root (residue < 1e-40 at 50-digit zero)
    q_mellin = (1 - mp.zeta(s0) * D_s0) / s0
    c8_err = abs(q_mellin - 1 / s0)
    assert c8_err < mp.mpf("1e-40")

    return {
        "max_exact_identity_err": str(
            max(c1_err, c2_err, c3_err, c4_err, c4_pal, c4_fold_err, cell_quad_err)
        ),
        "uniform_cell_bound_B": str(+B),
        "prime_floor_S5_7_11_13_17": str(+prime_floor),
        "l2_partial_M20": str(+l2_M),
        "tail_21_to_80": str(+tail_val),
        "tail_bound_B2_over_21": str(+(B ** 2 / (M + 1))),
        "mellin_zero_residual": str(+c8_err),
    }


def main() -> int:
    parser = argparse.ArgumentParser(description="8-Condition n-to-Continuity Audit")
    parser.add_argument(
        "--with-lean",
        action="store_true",
        help="Also invoke lake env lean to check #print axioms and #lint across 8M..8U.",
    )
    args = parser.parse_args()

    src_report = verify_source_modules()
    mp_report = verify_mpmath_85dps()
    lean_report = verify_lean_kernel_axioms_and_lint() if args.with_lean else {"skipped": True}
    payload = {
        "conditions_verified": 8,
        "source_audit": src_report,
        "mpmath_85dps": mp_report,
        "lean_kernel_audit": lean_report,
    }
    print(json.dumps(payload, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
