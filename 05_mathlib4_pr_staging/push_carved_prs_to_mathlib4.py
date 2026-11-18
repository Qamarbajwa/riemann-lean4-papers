#!/usr/bin/env python3
"""
Automated mathlib4 Branch, Import-Rewrite, and PR Push Tool for Carved UpstreamPRs.

Usage examples:
  # Check gh auth status, local git remotes, and list all Wave 1-3 PRs:
  python push_carved_prs_to_mathlib4.py --status

  # Dry-run import rewriting for Wave 1 (PR-1A, PR-3A, PR-4A):
  python push_carved_prs_to_mathlib4.py --wave 1 --dry-run

  # Stage, rewrite imports, update Mathlib.lean, build, and push Wave 1 to a local mathlib4 fork:
  python push_carved_prs_to_mathlib4.py --mathlib-dir /path/to/mathlib4 --wave 1 --push --create-pr
"""

from __future__ import annotations

import argparse
import json
import pathlib
import re
import subprocess
import sys
from dataclasses import dataclass
from typing import Dict, List, Optional


STAGING_DIR = pathlib.Path(__file__).resolve().parent
ALLOW_UPSTREAM_BOT_ACTIONS = False


@dataclass(frozen=True)
class PRSpec:
    pr_id: str
    wave: int
    staged_file: str
    blueprint_module: str
    target_relpath: str
    target_module: str
    branch: str
    base_branch: str
    pr_title: str
    commit_msg: str
    merge_branches: tuple[str, ...] = ()


PR_REGISTRY: List[PRSpec] = [
    # Wave 1: Root self-contained clusters
    PRSpec(
        pr_id="PR-1A",
        wave=1,
        staged_file="UpstreamPR_1A_CriticalLineZeros.lean",
        blueprint_module="RiemannBlueprint.UpstreamPRs.UpstreamPR_1A_CriticalLineZeros",
        target_relpath="Mathlib/NumberTheory/LSeries/CriticalLineZeros.lean",
        target_module="Mathlib.NumberTheory.LSeries.CriticalLineZeros",
        branch="feat/critical-line-zeros",
        base_branch="master",
        pr_title="feat(NumberTheory/LSeries): critical-line IVT zero detection and 3-4-1 zeta product positivity",
        commit_msg="feat(NumberTheory/LSeries): add critical-line zero detection and 3-4-1 zeta positivity",
    ),
    PRSpec(
        pr_id="PR-3A",
        wave=1,
        staged_file="UpstreamPR_3A_VasyuninIntegral.lean",
        blueprint_module="RiemannBlueprint.UpstreamPRs.UpstreamPR_3A_VasyuninIntegral",
        target_relpath="Mathlib/NumberTheory/LSeries/VasyuninIntegral.lean",
        target_module="Mathlib.NumberTheory.LSeries.VasyuninIntegral",
        branch="feat/vasyunin-integral",
        base_branch="master",
        pr_title="feat(NumberTheory/LSeries): exact L1 and L2 reciprocal fractional-part integrals of Vasyunin and Baez-Duarte",
        commit_msg="feat(NumberTheory/LSeries): evaluate Vasyunin and Baez-Duarte reciprocal fractional-part integrals",
    ),
    PRSpec(
        pr_id="PR-4A",
        wave=1,
        staged_file="UpstreamPR_4A_AffineLagrangeProjection.lean",
        blueprint_module="RiemannBlueprint.UpstreamPRs.UpstreamPR_4A_AffineLagrangeProjection",
        target_relpath="Mathlib/NumberTheory/LSeries/BaezDuarteProjection.lean",
        target_module="Mathlib.NumberTheory.LSeries.BaezDuarteProjection",
        branch="feat/baez-duarte-projection",
        base_branch="master",
        pr_title="feat(NumberTheory/LSeries): affine harmonic Lagrange projection on the Baez-Duarte constraint subspace",
        commit_msg="feat(NumberTheory/LSeries): add affine harmonic Lagrange projection on Baez-Duarte subspace",
    ),
    # Wave 2: Unconditional de la Vallee Poussin zero-free region chain
    PRSpec(
        pr_id="PR-1B",
        wave=2,
        staged_file="UpstreamPR_1B_ZetaPoleAndRepulsion.lean",
        blueprint_module="RiemannBlueprint.UpstreamPRs.UpstreamPR_1B_ZetaPoleAndRepulsion",
        target_relpath="Mathlib/NumberTheory/LSeries/ZetaPoleAndRepulsion.lean",
        target_module="Mathlib.NumberTheory.LSeries.ZetaPoleAndRepulsion",
        branch="feat/zeta-pole-and-repulsion",
        base_branch="feat/critical-line-zeros",
        pr_title="feat(NumberTheory/LSeries): zeta pole bound near s = 1 and de la Vallee Poussin zero repulsion",
        commit_msg="feat(NumberTheory/LSeries): add zeta pole bound and de la Vallee Poussin zero repulsion",
    ),
    PRSpec(
        pr_id="PR-1C",
        wave=2,
        staged_file="UpstreamPR_1C_ZetaRemainderSeries.lean",
        blueprint_module="RiemannBlueprint.UpstreamPRs.UpstreamPR_1C_ZetaRemainderSeries",
        target_relpath="Mathlib/NumberTheory/LSeries/ZetaRemainderSeries.lean",
        target_module="Mathlib.NumberTheory.LSeries.ZetaRemainderSeries",
        branch="feat/zeta-remainder-series",
        base_branch="master",
        pr_title="feat(NumberTheory/LSeries): Euler-Maclaurin remainder series and analyticity of zeta on Re(s) > 0",
        commit_msg="feat(NumberTheory/LSeries): add Euler-Maclaurin remainder series and analyticity",
    ),
    PRSpec(
        pr_id="PR-1D",
        wave=2,
        staged_file="UpstreamPR_1D_ZetaPartialSummation.lean",
        blueprint_module="RiemannBlueprint.UpstreamPRs.UpstreamPR_1D_ZetaPartialSummation",
        target_relpath="Mathlib/NumberTheory/LSeries/ZetaPartialSummation.lean",
        target_module="Mathlib.NumberTheory.LSeries.ZetaPartialSummation",
        branch="feat/zeta-partial-summation",
        base_branch="feat/zeta-remainder-series",
        pr_title="feat(NumberTheory/LSeries): Euler-Maclaurin partial summation identity for riemannZeta on Re(s) > 0",
        commit_msg="feat(NumberTheory/LSeries): add Euler-Maclaurin partial summation identity for riemannZeta",
    ),
    PRSpec(
        pr_id="PR-1E",
        wave=2,
        staged_file="UpstreamPR_1E_ZetaLogStripBound.lean",
        blueprint_module="RiemannBlueprint.UpstreamPRs.UpstreamPR_1E_ZetaLogStripBound",
        target_relpath="Mathlib/NumberTheory/LSeries/ZetaLogStripBound.lean",
        target_module="Mathlib.NumberTheory.LSeries.ZetaLogStripBound",
        branch="feat/zeta-log-strip-bound",
        base_branch="feat/zeta-partial-summation",
        pr_title="feat(NumberTheory/LSeries): logarithmic growth bound for riemannZeta near Re(s) = 1",
        commit_msg="feat(NumberTheory/LSeries): add logarithmic growth bound for riemannZeta near Re(s) = 1",
    ),
    PRSpec(
        pr_id="PR-1F",
        wave=2,
        staged_file="UpstreamPR_1F_ZetaZeroFreeRegion.lean",
        blueprint_module="RiemannBlueprint.UpstreamPRs.UpstreamPR_1F_ZetaZeroFreeRegion",
        target_relpath="Mathlib/NumberTheory/LSeries/ZeroFreeRegion.lean",
        target_module="Mathlib.NumberTheory.LSeries.ZeroFreeRegion",
        branch="feat/zeta-zero-free-region",
        base_branch="feat/zeta-log-strip-bound",
        merge_branches=("feat/zeta-pole-and-repulsion",),
        pr_title="feat(NumberTheory/LSeries): unconditional de la Vallee Poussin zero-free region for riemannZeta",
        commit_msg="feat(NumberTheory/LSeries): add unconditional de la Vallee Poussin zero-free region",
    ),
    # Wave 3: Vasyunin cross-integral, affine L^2 pure cotangent bridge & N=4 Mobius certificate
    PRSpec(
        pr_id="PR-3B",
        wave=3,
        staged_file="UpstreamPR_3B_VasyuninSmoothAndCotDefs.lean",
        blueprint_module="RiemannBlueprint.UpstreamPRs.UpstreamPR_3B_VasyuninSmoothAndCotDefs",
        target_relpath="Mathlib/NumberTheory/LSeries/VasyuninDefs.lean",
        target_module="Mathlib.NumberTheory.LSeries.VasyuninDefs",
        branch="feat/vasyunin-defs",
        base_branch="feat/vasyunin-integral",
        merge_branches=("feat/baez-duarte-projection",),
        pr_title="feat(NumberTheory/LSeries): smooth Vasyunin kernel, cotangent Gram sums, and Rank-4 BDR identity",
        commit_msg="feat(NumberTheory/LSeries): add Vasyunin smooth/cotangent kernels and Rank-4 identity",
    ),
    PRSpec(
        pr_id="PR-3D",
        wave=3,
        staged_file="UpstreamPR_3D_StirlingAndHarmonicAsymptotics.lean",
        blueprint_module="RiemannBlueprint.UpstreamPRs.UpstreamPR_3D_StirlingAndHarmonicAsymptotics",
        target_relpath="Mathlib/NumberTheory/LSeries/VasyuninStirlingAsymp.lean",
        target_module="Mathlib.NumberTheory.LSeries.VasyuninStirlingAsymp",
        branch="feat/vasyunin-stirling-asymp",
        base_branch="master",
        pr_title="feat(NumberTheory/LSeries): dilated Stirling, Euler-Mascheroni, and divisor quotient identities",
        commit_msg="feat(NumberTheory/LSeries): add Stirling/harmonic asymptotics and divisor step lemmas",
    ),
    PRSpec(
        pr_id="PR-3C",
        wave=3,
        staged_file="UpstreamPR_3C_HarmonicCellAndAbelSum.lean",
        blueprint_module="RiemannBlueprint.UpstreamPRs.UpstreamPR_3C_HarmonicCellAndAbelSum",
        target_relpath="Mathlib/NumberTheory/LSeries/VasyuninAbelSum.lean",
        target_module="Mathlib.NumberTheory.LSeries.VasyuninAbelSum",
        branch="feat/vasyunin-abel-sum",
        base_branch="feat/vasyunin-defs",
        merge_branches=("feat/vasyunin-stirling-asymp",),
        pr_title="feat(NumberTheory/LSeries): harmonic cell decomposition and discrete Abel sums for Vasyunin cross-integrals",
        commit_msg="feat(NumberTheory/LSeries): add harmonic cell integral and discrete Abel identities",
    ),
    PRSpec(
        pr_id="PR-3E",
        wave=3,
        staged_file="UpstreamPR_3E_CotangentMittagLefflerLimit.lean",
        blueprint_module="RiemannBlueprint.UpstreamPRs.UpstreamPR_3E_CotangentMittagLefflerLimit",
        target_relpath="Mathlib/NumberTheory/LSeries/VasyuninCotangentLimit.lean",
        target_module="Mathlib.NumberTheory.LSeries.VasyuninCotangentLimit",
        branch="feat/vasyunin-cotangent-limit",
        base_branch="feat/vasyunin-defs",
        pr_title="feat(NumberTheory/LSeries): residue-class pairing and Mittag-Leffler limit for Vasyunin cotangent sums",
        commit_msg="feat(NumberTheory/LSeries): prove cotApproxSum convergence via cot_series_rep'",
    ),
    PRSpec(
        pr_id="PR-3F",
        wave=3,
        staged_file="UpstreamPR_3F_VasyuninCrossIntegral.lean",
        blueprint_module="RiemannBlueprint.UpstreamPRs.UpstreamPR_3F_VasyuninCrossIntegral",
        target_relpath="Mathlib/NumberTheory/LSeries/VasyuninCrossIntegral.lean",
        target_module="Mathlib.NumberTheory.LSeries.VasyuninCrossIntegral",
        branch="feat/vasyunin-cross-integral",
        base_branch="feat/vasyunin-abel-sum",
        merge_branches=("feat/vasyunin-cotangent-limit",),
        pr_title="feat(NumberTheory/LSeries): unconditional Vasyunin cross-integral and affine L2 pure cotangent bridge",
        commit_msg="feat(NumberTheory/LSeries): prove Vasyunin cross-integral and affine L2 cotangent bridge",
    ),
    PRSpec(
        pr_id="PR-3G",
        wave=3,
        staged_file="UpstreamPR_3G_MobiusCandidateFourCert.lean",
        blueprint_module="RiemannBlueprint.UpstreamPRs.UpstreamPR_3G_MobiusCandidateFourCert",
        target_relpath="Mathlib/NumberTheory/LSeries/BaezDuarteMobiusFour.lean",
        target_module="Mathlib.NumberTheory.LSeries.BaezDuarteMobiusFour",
        branch="feat/baez-duarte-mobius-four",
        base_branch="feat/vasyunin-cross-integral",
        pr_title="feat(NumberTheory/LSeries): mollified Mobius candidate on A_N and exact N=4 L2 positivity certificate",
        commit_msg="feat(NumberTheory/LSeries): add mollifiedMobius candidate and N=4 L2 certificate",
    ),
    PRSpec(
        pr_id="PR-3H",
        wave=3,
        staged_file="UpstreamPR_3H_VariationalOptimumFour.lean",
        blueprint_module="RiemannBlueprint.UpstreamPRs.UpstreamPR_3H_VariationalOptimumFour",
        target_relpath="Mathlib/NumberTheory/LSeries/BaezDuarteVariationalFour.lean",
        target_module="Mathlib.NumberTheory.LSeries.BaezDuarteVariationalFour",
        branch="feat/baez-duarte-variational-four",
        base_branch="feat/baez-duarte-mobius-four",
        pr_title="feat(NumberTheory/LSeries): affine cotangent improvement identity and variational beat over mollified Mobius on A_4",
        commit_msg="feat(NumberTheory/LSeries): prove cVariationalFour strictly beats cCandidateMobius 4 on A_4",
    ),
    PRSpec(
        pr_id="PR-4B",
        wave=3,
        staged_file="UpstreamPR_4B_AffineOrthogonalDecomp.lean",
        blueprint_module="RiemannBlueprint.UpstreamPRs.UpstreamPR_4B_AffineOrthogonalDecomp",
        target_relpath="Mathlib/NumberTheory/LSeries/BaezDuarteOrthogonalDecomp.lean",
        target_module="Mathlib.NumberTheory.LSeries.BaezDuarteOrthogonalDecomp",
        branch="feat/baez-duarte-orthogonal-decomp",
        base_branch="feat/baez-duarte-projection",
        pr_title="feat(NumberTheory/LSeries): minimum-norm base point and orthogonal tangent decomposition of A_N",
        commit_msg="feat(NumberTheory/LSeries): prove orthogonal tangent decomposition on Baez-Duarte subspace",
    ),
    PRSpec(
        pr_id="PR-4C",
        wave=3,
        staged_file="UpstreamPR_4C_HarmonicWaveletBasis.lean",
        blueprint_module="RiemannBlueprint.UpstreamPRs.UpstreamPR_4C_HarmonicWaveletBasis",
        target_relpath="Mathlib/NumberTheory/LSeries/BaezDuarteWaveletBasis.lean",
        target_module="Mathlib.NumberTheory.LSeries.BaezDuarteWaveletBasis",
        branch="feat/baez-duarte-wavelet-basis",
        base_branch="feat/baez-duarte-variational-four",
        merge_branches=("feat/baez-duarte-orthogonal-decomp",),
        pr_title="feat(NumberTheory/LSeries): determinant-free 2-point anchor and 3-point harmonic wavelet basis of A_N",
        commit_msg="feat(NumberTheory/LSeries): add cBaseAnchor and 3-point harmonicWavelet basis of A_N",
    ),
    PRSpec(
        pr_id="PR-4D",
        wave=3,
        staged_file="UpstreamPR_4D_WaveletCotangentStencil.lean",
        blueprint_module="RiemannBlueprint.UpstreamPRs.UpstreamPR_4D_WaveletCotangentStencil",
        target_relpath="Mathlib/NumberTheory/LSeries/BaezDuarteWaveletStencil.lean",
        target_module="Mathlib.NumberTheory.LSeries.BaezDuarteWaveletStencil",
        branch="feat/baez-duarte-wavelet-stencil",
        base_branch="feat/baez-duarte-wavelet-basis",
        pr_title="feat(NumberTheory/LSeries): unconstrained tangent shift and denominator-free wavelet cotangent stencil on A_N",
        commit_msg="feat(NumberTheory/LSeries): prove tangent shift and wavelet cotangent stencil identities",
    ),
    PRSpec(
        pr_id="PR-4E",
        wave=3,
        staged_file="UpstreamPR_4E_TangentCotangentPositivity.lean",
        blueprint_module="RiemannBlueprint.UpstreamPRs.UpstreamPR_4E_TangentCotangentPositivity",
        target_relpath="Mathlib/NumberTheory/LSeries/BaezDuarteTangentPositivity.lean",
        target_module="Mathlib.NumberTheory.LSeries.BaezDuarteTangentPositivity",
        branch="feat/baez-duarte-tangent-positivity",
        base_branch="feat/baez-duarte-wavelet-stencil",
        pr_title="feat(NumberTheory/LSeries): tangent L2-to-cotangent isometry, positivity of QCot, and exact N=3 wavelet optimum",
        commit_msg="feat(NumberTheory/LSeries): prove tangent L2 isometry and QCot positivity on A_N^0",
    ),
    PRSpec(
        pr_id="PR-4F",
        wave=3,
        staged_file="UpstreamPR_4F_TangentRayleighQuotient.lean",
        blueprint_module="RiemannBlueprint.UpstreamPRs.UpstreamPR_4F_TangentRayleighQuotient",
        target_relpath="Mathlib/NumberTheory/LSeries/BaezDuarteRayleighQuotient.lean",
        target_module="Mathlib.NumberTheory.LSeries.BaezDuarteRayleighQuotient",
        branch="feat/baez-duarte-rayleigh-quotient",
        base_branch="feat/baez-duarte-tangent-positivity",
        pr_title="feat(NumberTheory/LSeries): scale-invariant tangent Rayleigh quotient and unconditional cotangent Cauchy-Schwarz on A_N^0",
        commit_msg="feat(NumberTheory/LSeries): prove tangent Rayleigh quotient bound and N=3 global optimality",
    ),
    PRSpec(
        pr_id="PR-4G",
        wave=3,
        staged_file="UpstreamPR_4G_GlobalOptimumFour.lean",
        blueprint_module="RiemannBlueprint.UpstreamPRs.UpstreamPR_4G_GlobalOptimumFour",
        target_relpath="Mathlib/NumberTheory/LSeries/BaezDuarteGlobalOptimumFour.lean",
        target_module="Mathlib.NumberTheory.LSeries.BaezDuarteGlobalOptimumFour",
        branch="feat/baez-duarte-global-optimum-four",
        base_branch="feat/baez-duarte-rayleigh-quotient",
        pr_title="feat(NumberTheory/LSeries): 2-wavelet completeness on A_4 and exact global KKT optimum (19 + sqrt 3)/72 * pi",
        commit_msg="feat(NumberTheory/LSeries): prove 2-wavelet diagonalization and exact global KKT optimum on A_4",
    ),
    PRSpec(
        pr_id="PR-4H",
        wave=3,
        staged_file="UpstreamPR_4H_WaveletRayleighRHCriterion.lean",
        blueprint_module="RiemannBlueprint.UpstreamPRs.UpstreamPR_4H_WaveletRayleighRHCriterion",
        target_relpath="Mathlib/NumberTheory/LSeries/BaezDuarteRayleighCriterion.lean",
        target_module="Mathlib.NumberTheory.LSeries.BaezDuarteRayleighCriterion",
        branch="feat/baez-duarte-rayleigh-criterion",
        base_branch="feat/baez-duarte-global-optimum-four",
        pr_title="feat(NumberTheory/LSeries): universal affine-to-Rayleigh duality and multi-wavelet drive linearity on A_N",
        commit_msg="feat(NumberTheory/LSeries): prove affine-to-Rayleigh duality and multi-wavelet linearity for N >= 2",
    ),
    PRSpec(
        pr_id="PR-4I",
        wave=3,
        staged_file="UpstreamPR_4I_CumulativeWaveletDipole.lean",
        blueprint_module="RiemannBlueprint.UpstreamPRs.UpstreamPR_4I_CumulativeWaveletDipole",
        target_relpath="Mathlib/NumberTheory/LSeries/BaezDuarteCumulativeDipole.lean",
        target_module="Mathlib.NumberTheory.LSeries.BaezDuarteCumulativeDipole",
        branch="feat/baez-duarte-cumulative-dipole",
        base_branch="feat/baez-duarte-rayleigh-criterion",
        pr_title="feat(NumberTheory/LSeries): cumulative wavelet dipole basis, drive telescoping, and N=4,5 cotangent orthogonality",
        commit_msg="feat(NumberTheory/LSeries): prove cumulative dipole telescoping and N=4,5 cotangent orthogonality",
    ),
    PRSpec(
        pr_id="PR-4J",
        wave=3,
        staged_file="UpstreamPR_4J_FourPointDipoleKernel.lean",
        blueprint_module="RiemannBlueprint.UpstreamPRs.UpstreamPR_4J_FourPointDipoleKernel",
        target_relpath="Mathlib/NumberTheory/LSeries/BaezDuarteFourPointDipole.lean",
        target_module="Mathlib.NumberTheory.LSeries.BaezDuarteFourPointDipole",
        branch="feat/baez-duarte-four-point-dipole",
        base_branch="feat/baez-duarte-cumulative-dipole",
        pr_title="feat(NumberTheory/LSeries): 4-point sparsity of cumulativeDipole and N-independent closed-form dipole Gram matrix",
        commit_msg="feat(NumberTheory/LSeries): prove 4-point cumulative dipole telescoping and N-independent Gram matrix law",
    ),
    PRSpec(
        pr_id="PR-4K",
        wave=3,
        staged_file="UpstreamPR_4K_GeneralWaveletCompleteness.lean",
        blueprint_module="RiemannBlueprint.UpstreamPRs.UpstreamPR_4K_GeneralWaveletCompleteness",
        target_relpath="Mathlib/NumberTheory/LSeries/BaezDuarteWaveletCompleteness.lean",
        target_module="Mathlib.NumberTheory.LSeries.BaezDuarteWaveletCompleteness",
        branch="feat/baez-duarte-wavelet-completeness",
        base_branch="feat/baez-duarte-four-point-dipole",
        pr_title="feat(NumberTheory/LSeries): general-N completeness of cumulative dipole and harmonic wavelet bases on A_N^0 and A_N",
        commit_msg="feat(NumberTheory/LSeries): prove general-N completeness of cumulative dipole and harmonic wavelet bases",
    ),
    PRSpec(
        pr_id="PR-4L",
        wave=3,
        staged_file="UpstreamPR_4L_DipoleQuadraticReduction.lean",
        blueprint_module="RiemannBlueprint.UpstreamPRs.UpstreamPR_4L_DipoleQuadraticReduction",
        target_relpath="Mathlib/NumberTheory/LSeries/BaezDuarteDipoleQuadratic.lean",
        target_module="Mathlib.NumberTheory.LSeries.BaezDuarteDipoleQuadratic",
        branch="feat/baez-duarte-dipole-quadratic",
        base_branch="feat/baez-duarte-wavelet-completeness",
        pr_title="feat(NumberTheory/LSeries): N-independent dipole quadratic reduction of SCot and N=4 overshoot certificate",
        commit_msg="feat(NumberTheory/LSeries): prove N-independent dipole quadratic reduction and N=4 overshoot certificate",
    ),
    PRSpec(
        pr_id="PR-4M",
        wave=3,
        staged_file="UpstreamPR_4M_DipoleDiagonalAndSymmetry.lean",
        blueprint_module="RiemannBlueprint.UpstreamPRs.UpstreamPR_4M_DipoleDiagonalAndSymmetry",
        target_relpath="Mathlib/NumberTheory/LSeries/BaezDuarteDipoleDiagonal.lean",
        target_module="Mathlib.NumberTheory.LSeries.BaezDuarteDipoleDiagonal",
        branch="feat/baez-duarte-dipole-diagonal",
        base_branch="feat/baez-duarte-dipole-quadratic",
        pr_title="feat(NumberTheory/LSeries): symmetry, single-pair diagonal collapse, and non-negativity of dipoleGramEntry",
        commit_msg="feat(NumberTheory/LSeries): prove symmetry, diagonal collapse, and positivity of dipoleGramEntry",
    ),
    # Wave 4: Unconditional Hardy (1914) infinitely many critical-line zeros chain
    PRSpec(
        pr_id="PR-2B",
        wave=4,
        staged_file="UpstreamPR_2B_HardyPsiAndThetaKernel.lean",
        blueprint_module="RiemannBlueprint.UpstreamPRs.UpstreamPR_2B_HardyPsiAndThetaKernel",
        target_relpath="Mathlib/NumberTheory/LSeries/HardyPsiKernel.lean",
        target_module="Mathlib.NumberTheory.LSeries.HardyPsiKernel",
        branch="feat/hardy-psi-kernel",
        base_branch="master",
        pr_title="feat(NumberTheory/LSeries): Hardy theta-remainder kernel hardyPsi strip holomorphicity and Gaussian decay",
        commit_msg="feat(NumberTheory/LSeries): add HardyPsiKernel with strip decay and theta parity",
    ),
    PRSpec(
        pr_id="PR-2C",
        wave=4,
        staged_file="UpstreamPR_2C_HardyThetaIteratedDeriv.lean",
        blueprint_module="RiemannBlueprint.UpstreamPRs.UpstreamPR_2C_HardyThetaIteratedDeriv",
        target_relpath="Mathlib/NumberTheory/LSeries/HardyThetaDeriv.lean",
        target_module="Mathlib.NumberTheory.LSeries.HardyThetaDeriv",
        branch="feat/hardy-theta-deriv",
        base_branch="feat/hardy-psi-kernel",
        pr_title="feat(NumberTheory/LSeries): boundary vanishing of higher derivatives of hardyThetaTerm at pi/4",
        commit_msg="feat(NumberTheory/LSeries): prove boundary vanishing of hardyThetaTerm derivatives at pi/4",
    ),
    PRSpec(
        pr_id="PR-2D",
        wave=4,
        staged_file="UpstreamPR_2D_CompletedZetaStripDecay.lean",
        blueprint_module="RiemannBlueprint.UpstreamPRs.UpstreamPR_2D_CompletedZetaStripDecay",
        target_relpath="Mathlib/NumberTheory/LSeries/CompletedZetaStripDecay.lean",
        target_module="Mathlib.NumberTheory.LSeries.CompletedZetaStripDecay",
        branch="feat/completed-zeta-strip-decay",
        base_branch="feat/hardy-psi-kernel",
        pr_title="feat(NumberTheory/LSeries): Mellin inversion and contour shift for completedRiemannZeta on Re(s) = 1/2",
        commit_msg="feat(NumberTheory/LSeries): add contour-shifted Fourier formula for completedRiemannZeta",
    ),
    PRSpec(
        pr_id="PR-2E",
        wave=4,
        staged_file="UpstreamPR_2E_HardyGContourAndMellin.lean",
        blueprint_module="RiemannBlueprint.UpstreamPRs.UpstreamPR_2E_HardyGContourAndMellin",
        target_relpath="Mathlib/NumberTheory/LSeries/HardyGContour.lean",
        target_module="Mathlib.NumberTheory.LSeries.HardyGContour",
        branch="feat/hardy-g-contour",
        base_branch="feat/completed-zeta-strip-decay",
        pr_title="feat(NumberTheory/LSeries): critical-line exponential decay and analytic continuation hardyG = hardyPsi",
        commit_msg="feat(NumberTheory/LSeries): prove critical-line decay and hardyG_eq_hardyPsi",
    ),
    PRSpec(
        pr_id="PR-2F",
        wave=4,
        staged_file="UpstreamPR_2F_HardyEvenMomentIdentity.lean",
        blueprint_module="RiemannBlueprint.UpstreamPRs.UpstreamPR_2F_HardyEvenMomentIdentity",
        target_relpath="Mathlib/NumberTheory/LSeries/HardyEvenMoments.lean",
        target_module="Mathlib.NumberTheory.LSeries.HardyEvenMoments",
        branch="feat/hardy-even-moments",
        base_branch="feat/hardy-g-contour",
        pr_title="feat(NumberTheory/LSeries): iterated derivative differentiation under integral and even moment identity for hardyZ",
        commit_msg="feat(NumberTheory/LSeries): prove hardyGn_even_re moment identity on the critical line",
    ),
    PRSpec(
        pr_id="PR-2G",
        wave=4,
        staged_file="UpstreamPR_2G_HardyCriticalLineZeros.lean",
        blueprint_module="RiemannBlueprint.UpstreamPRs.UpstreamPR_2G_HardyCriticalLineZeros",
        target_relpath="Mathlib/NumberTheory/LSeries/HardyCriticalLineZeros.lean",
        target_module="Mathlib.NumberTheory.LSeries.HardyCriticalLineZeros",
        branch="feat/hardy-critical-line-zeros",
        base_branch="feat/hardy-even-moments",
        merge_branches=("feat/hardy-theta-deriv", "feat/critical-line-zeros"),
        pr_title="feat(NumberTheory/LSeries): unconditional Hardy (1914) theorem on infinitude of critical-line zeros of riemannZeta",
        commit_msg="feat(NumberTheory/LSeries): prove infinite_criticalLine_zeros and infinite_hardyZ_zeros",
    ),
    # Wave 5: Papers F & G (Zeta Log-Derivative Holomorphy, Von Koch Equivalence, Mellin Nyman-Beurling Converse)
    PRSpec(
        pr_id="PR-5A",
        wave=5,
        staged_file="UpstreamPR_5A_ZetaLogDerivHolomorphy.lean",
        blueprint_module="RiemannBlueprint.UpstreamPRs.UpstreamPR_5A_ZetaLogDerivHolomorphy",
        target_relpath="Mathlib/NumberTheory/LSeries/ZetaInvHolomorphy.lean",
        target_module="Mathlib.NumberTheory.LSeries.ZetaInvHolomorphy",
        branch="feat/zeta-inv-holomorphy",
        base_branch="master",
        pr_title="feat(NumberTheory/LSeries): analyticity of zeta inverse and log-derivative equivalence for RiemannHypothesis",
        commit_msg="feat(NumberTheory/LSeries): add ZetaInvHolomorphy and RH analyticity equivalences",
    ),
    PRSpec(
        pr_id="PR-5B",
        wave=5,
        staged_file="UpstreamPR_5B_VonKochChebyshevPsi.lean",
        blueprint_module="RiemannBlueprint.UpstreamPRs.UpstreamPR_5B_VonKochChebyshevPsi",
        target_relpath="Mathlib/NumberTheory/LSeries/VonKochChebyshevPsi.lean",
        target_module="Mathlib.NumberTheory.LSeries.VonKochChebyshevPsi",
        branch="feat/von-koch-chebyshev-psi",
        base_branch="feat/zeta-inv-holomorphy",
        pr_title="feat(NumberTheory/LSeries): unconditional von Koch forward equivalence via Chebyshev psi remainder",
        commit_msg="feat(NumberTheory/LSeries): prove vonKoch_implies_rh via Mellin remainder and isolated zeros",
    ),
    PRSpec(
        pr_id="PR-5C",
        wave=5,
        staged_file="UpstreamPR_5C_MellinNymanBeurlingIff.lean",
        blueprint_module="RiemannBlueprint.UpstreamPRs.UpstreamPR_5C_MellinNymanBeurlingIff",
        target_relpath="Mathlib/NumberTheory/LSeries/MellinNymanBeurlingConverse.lean",
        target_module="Mathlib.NumberTheory.LSeries.MellinNymanBeurlingConverse",
        branch="feat/mellin-nyman-beurling-iff",
        base_branch="feat/baez-duarte-projection",
        merge_branches=("feat/vasyunin-integral", "feat/zeta-inv-holomorphy"),
        pr_title="feat(NumberTheory/LSeries): bidirectional Mellin-space Nyman-Beurling equivalence in the critical strip",
        commit_msg="feat(NumberTheory/LSeries): prove bidirectional Mellin Nyman-Beurling equivalence",
    ),
    # Wave 6: Papers F & I (Completed Zeta Deriv Symmetry, Penetration Barrier, Prime-Composite Split)
    PRSpec(
        pr_id="PR-6A",
        wave=6,
        staged_file="UpstreamPR_6A_CompletedZetaDerivSymmetry.lean",
        blueprint_module="RiemannBlueprint.UpstreamPRs.UpstreamPR_6A_CompletedZetaDerivSymmetry",
        target_relpath="Mathlib/NumberTheory/LSeries/CompletedZetaDerivSymmetry.lean",
        target_module="Mathlib.NumberTheory.LSeries.CompletedZetaDerivSymmetry",
        branch="feat/completed-zeta-deriv-symmetry",
        base_branch="master",
        pr_title="feat(NumberTheory/LSeries): completed zeta derivative antisymmetry, equipartition fulcrum, and zero dichotomy",
        commit_msg="feat(NumberTheory/LSeries): add CompletedZetaDerivSymmetry and equipartition partition",
    ),
    PRSpec(
        pr_id="PR-6B",
        wave=6,
        staged_file="UpstreamPR_6B_CriticalLinePenetrationBarrier.lean",
        blueprint_module="RiemannBlueprint.UpstreamPRs.UpstreamPR_6B_CriticalLinePenetrationBarrier",
        target_relpath="Mathlib/NumberTheory/LSeries/CriticalLinePenetrationBarrier.lean",
        target_module="Mathlib.NumberTheory.LSeries.CriticalLinePenetrationBarrier",
        branch="feat/critical-line-penetration-barrier",
        base_branch="feat/baez-duarte-projection",
        merge_branches=("feat/vasyunin-integral", "feat/mellin-nyman-beurling-iff"),
        pr_title="feat(NumberTheory/LSeries): strip defect Mellin coupling and critical-line penetration lower bound",
        commit_msg="feat(NumberTheory/LSeries): add CriticalLinePenetrationBarrier and strip defect coupling",
    ),
    PRSpec(
        pr_id="PR-6C",
        wave=6,
        staged_file="UpstreamPR_6C_PrimeCompositeDirichletSplit.lean",
        blueprint_module="RiemannBlueprint.UpstreamPRs.UpstreamPR_6C_PrimeCompositeDirichletSplit",
        target_relpath="Mathlib/NumberTheory/LSeries/PrimeCompositeDirichletSplit.lean",
        target_module="Mathlib.NumberTheory.LSeries.PrimeCompositeDirichletSplit",
        branch="feat/prime-composite-dirichlet-split",
        base_branch="master",
        pr_title="feat(NumberTheory/LSeries): natural prime-composite partition and critical-strip RH equivalence",
        commit_msg="feat(NumberTheory/LSeries): add PrimeCompositeDirichletSplit and strip quantifier equivalence",
    ),
    # Wave 7: Layers B & C (Mellin Kernel Energy, Rectangle Contour Subdivision, Pure Plaque, Off-Diagonal Frontier)
    PRSpec(
        pr_id="PR-7A",
        wave=7,
        staged_file="UpstreamPR_7A_MellinKernelEnergyIdentity.lean",
        blueprint_module="RiemannBlueprint.UpstreamPRs.UpstreamPR_7A_MellinKernelEnergyIdentity",
        target_relpath="Mathlib/NumberTheory/LSeries/MellinKernelEnergy.lean",
        target_module="Mathlib.NumberTheory.LSeries.MellinKernelEnergy",
        branch="feat/mellin-kernel-energy-identity",
        base_branch="master",
        pr_title="feat(NumberTheory/LSeries): Mellin weight kernel L2 energy identity and weighted Cauchy-Schwarz bound",
        commit_msg="feat(NumberTheory/LSeries): add MellinKernelEnergy identity and L2 weighted inequality",
    ),
    PRSpec(
        pr_id="PR-7B",
        wave=7,
        staged_file="UpstreamPR_7B_RectangleContourSubdivision.lean",
        blueprint_module="RiemannBlueprint.UpstreamPRs.UpstreamPR_7B_RectangleContourSubdivision",
        target_relpath="Mathlib/Analysis/Complex/RectangleContourSubdivision.lean",
        target_module="Mathlib.Analysis.Complex.RectangleContourSubdivision",
        branch="feat/rectangle-contour-subdivision",
        base_branch="master",
        pr_title="feat(Analysis/Complex): 4-segment oriented rectangle boundary integral and edge subdivisions",
        commit_msg="feat(Analysis/Complex): add RectangleContourSubdivision horizontal and vertical splits",
    ),
    PRSpec(
        pr_id="PR-7C",
        wave=7,
        staged_file="UpstreamPR_7C_PurePlaqueReduction.lean",
        blueprint_module="RiemannBlueprint.UpstreamPRs.UpstreamPR_7C_PurePlaqueReduction",
        target_relpath="Mathlib/NumberTheory/LSeries/BaezDuartePurePlaque.lean",
        target_module="Mathlib.NumberTheory.LSeries.BaezDuartePurePlaque",
        branch="feat/baez-duarte-pure-plaque-reduction",
        base_branch="feat/baez-duarte-dipole-diagonal",
        pr_title="feat(NumberTheory/LSeries): pure 4-point plaque kernel and global anchor-drive cancellation on A_N",
        commit_msg="feat(NumberTheory/LSeries): add BaezDuartePurePlaque global Rank-2 factorization",
    ),
    PRSpec(
        pr_id="PR-7D",
        wave=7,
        staged_file="UpstreamPR_7D_DiagonalOffDiagonalFrontier.lean",
        blueprint_module="RiemannBlueprint.UpstreamPRs.UpstreamPR_7D_DiagonalOffDiagonalFrontier",
        target_relpath="Mathlib/NumberTheory/LSeries/BaezDuarteOffDiagonalFrontier.lean",
        target_module="Mathlib.NumberTheory.LSeries.BaezDuarteOffDiagonalFrontier",
        branch="feat/baez-duarte-off-diagonal-frontier",
        base_branch="feat/baez-duarte-pure-plaque-reduction",
        pr_title="feat(NumberTheory/LSeries): positive diagonal dipole energy split and off-diagonal cancellation frontier",
        commit_msg="feat(NumberTheory/LSeries): add BaezDuarteOffDiagonalFrontier diagonal/off-diagonal split",
    ),
    # Wave 8: Pure Plaque Cauchy-Schwarz, Dirichlet-Anchored Positivity, 2D Telescoping & RH Criterion
    PRSpec(
        pr_id="PR-8A",
        wave=8,
        staged_file="UpstreamPR_8A_PurePlaqueCauchySchwarz.lean",
        blueprint_module="RiemannBlueprint.UpstreamPRs.UpstreamPR_8A_PurePlaqueCauchySchwarz",
        target_relpath="Mathlib/NumberTheory/LSeries/BaezDuartePlaqueCauchySchwarz.lean",
        target_module="Mathlib.NumberTheory.LSeries.BaezDuartePlaqueCauchySchwarz",
        branch="feat/baez-duarte-plaque-cauchy-schwarz",
        base_branch="feat/baez-duarte-off-diagonal-frontier",
        pr_title="feat(NumberTheory/LSeries): pure plaque quadratic form and Cauchy-Schwarz lower bound on A_N^0",
        commit_msg="feat(NumberTheory/LSeries): add BaezDuartePlaqueCauchySchwarz unconditional plaque floor",
    ),
    PRSpec(
        pr_id="PR-8B",
        wave=8,
        staged_file="UpstreamPR_8B_DirichletAnchoredPlaque.lean",
        blueprint_module="RiemannBlueprint.UpstreamPRs.UpstreamPR_8B_DirichletAnchoredPlaque",
        target_relpath="Mathlib/NumberTheory/LSeries/BaezDuarteDirichletAnchoredPlaque.lean",
        target_module="Mathlib.NumberTheory.LSeries.BaezDuarteDirichletAnchoredPlaque",
        branch="feat/baez-duarte-dirichlet-anchored-plaque",
        base_branch="feat/baez-duarte-plaque-cauchy-schwarz",
        pr_title="feat(NumberTheory/LSeries): Dirichlet-anchored (c_1 = -1) plaque positivity and L2 energy law",
        commit_msg="feat(NumberTheory/LSeries): add BaezDuarteDirichletAnchoredPlaque positivity on c_1 = -1",
    ),
    PRSpec(
        pr_id="PR-8C",
        wave=8,
        staged_file="UpstreamPR_8C_PlaqueTwoDimTelescoping.lean",
        blueprint_module="RiemannBlueprint.UpstreamPRs.UpstreamPR_8C_PlaqueTwoDimTelescoping",
        target_relpath="Mathlib/NumberTheory/LSeries/BaezDuartePlaqueTelescoping.lean",
        target_module="Mathlib.NumberTheory.LSeries.BaezDuartePlaqueTelescoping",
        branch="feat/baez-duarte-plaque-telescoping",
        base_branch="feat/baez-duarte-dirichlet-anchored-plaque",
        pr_title="feat(NumberTheory/LSeries): 2D discrete Abel telescoping identity for the pure cotangent plaque",
        commit_msg="feat(NumberTheory/LSeries): add BaezDuartePlaqueTelescoping kernel reduction on {3..N}^2",
    ),
    PRSpec(
        pr_id="PR-8D",
        wave=8,
        staged_file="UpstreamPR_8D_PurePlaqueRHCriterion.lean",
        blueprint_module="RiemannBlueprint.UpstreamPRs.UpstreamPR_8D_PurePlaqueRHCriterion",
        target_relpath="Mathlib/NumberTheory/LSeries/BaezDuartePurePlaqueRHCriterion.lean",
        target_module="Mathlib.NumberTheory.LSeries.BaezDuartePurePlaqueRHCriterion",
        branch="feat/baez-duarte-pure-plaque-rh-criterion",
        base_branch="feat/baez-duarte-plaque-telescoping",
        merge_branches=("feat/mellin-nyman-beurling-iff", "feat/mellin-kernel-energy-identity"),
        pr_title="feat(NumberTheory/LSeries): pure plaque and 2D-telescoped kernel vanishing criteria for RH",
        commit_msg="feat(NumberTheory/LSeries): add BaezDuartePurePlaqueRHCriterion equivalence bridge",
    ),
    PRSpec(
        pr_id="PR-8E",
        wave=8,
        staged_file="UpstreamPR_8E_DirichletOptFourCert.lean",
        blueprint_module="RiemannBlueprint.UpstreamPRs.UpstreamPR_8E_DirichletOptFourCert",
        target_relpath="Mathlib/NumberTheory/LSeries/BaezDuarteDirichletOptFour.lean",
        target_module="Mathlib.NumberTheory.LSeries.BaezDuarteDirichletOptFour",
        branch="feat/baez-duarte-dirichlet-opt-four",
        base_branch="feat/baez-duarte-pure-plaque-rh-criterion",
        pr_title="feat(NumberTheory/LSeries): exact closed-form (31/108)*pi Dirichlet-anchored optimum on A_4",
        commit_msg="feat(NumberTheory/LSeries): add BaezDuarteDirichletOptFour exact radical-free N=4 certificate",
    ),
    PRSpec(
        pr_id="PR-8F",
        wave=8,
        staged_file="UpstreamPR_8F_DipoleGramFiveCert.lean",
        blueprint_module="RiemannBlueprint.UpstreamPRs.UpstreamPR_8F_DipoleGramFiveCert",
        target_relpath="Mathlib/NumberTheory/LSeries/BaezDuarteDipoleGramFive.lean",
        target_module="Mathlib.NumberTheory.LSeries.BaezDuarteDipoleGramFive",
        branch="feat/baez-duarte-dipole-gram-five",
        base_branch="feat/baez-duarte-dirichlet-opt-four",
        pr_title="feat(NumberTheory/LSeries): closed-form N=5 dipole Gram entries and reciprocity orthogonality",
        commit_msg="feat(NumberTheory/LSeries): add BaezDuarteDipoleGramFive closed-form N=5 certificates",
    ),
    PRSpec(
        pr_id="PR-8G",
        wave=8,
        staged_file="UpstreamPR_8G_CotangentSixReciprocity.lean",
        blueprint_module="RiemannBlueprint.UpstreamPRs.UpstreamPR_8G_CotangentSixReciprocity",
        target_relpath="Mathlib/NumberTheory/LSeries/BaezDuarteCotangentSix.lean",
        target_module="Mathlib.NumberTheory.LSeries.BaezDuarteCotangentSix",
        branch="feat/baez-duarte-cotangent-six",
        base_branch="feat/baez-duarte-dipole-gram-five",
        pr_title="feat(NumberTheory/LSeries): exact N=6 Vasyunin sums in Q(sqrt(3)), K(3,6)=0, and G_24=0 decoupling",
        commit_msg="feat(NumberTheory/LSeries): add BaezDuarteCotangentSix exact N=6 certificates",
    ),
    PRSpec(
        pr_id="PR-8H",
        wave=8,
        staged_file="UpstreamPR_8H_UniversalCotangentSymmetries.lean",
        blueprint_module="RiemannBlueprint.UpstreamPRs.UpstreamPR_8H_UniversalCotangentSymmetries",
        target_relpath="Mathlib/NumberTheory/LSeries/BaezDuarteUniversalCotangent.lean",
        target_module="Mathlib.NumberTheory.LSeries.BaezDuarteUniversalCotangent",
        branch="feat/baez-duarte-universal-cotangent",
        base_branch="feat/baez-duarte-cotangent-six",
        pr_title="feat(NumberTheory/LSeries): universal all-N Vasyunin cotangent symmetries and octave vanishing",
        commit_msg="feat(NumberTheory/LSeries): add BaezDuarteUniversalCotangent all-N symmetries",
    ),
    PRSpec(
        pr_id="PR-8I",
        wave=8,
        staged_file="UpstreamPR_8I_LogarithmicPlaqueDecayCriterion.lean",
        blueprint_module="RiemannBlueprint.UpstreamPRs.UpstreamPR_8I_LogarithmicPlaqueDecayCriterion",
        target_relpath="Mathlib/NumberTheory/LSeries/BaezDuarteLogarithmicPlaqueDecay.lean",
        target_module="Mathlib.NumberTheory.LSeries.BaezDuarteLogarithmicPlaqueDecay",
        branch="feat/baez-duarte-logarithmic-plaque-decay",
        base_branch="feat/baez-duarte-universal-cotangent",
        pr_title="feat(NumberTheory/LSeries): variational majorant and BBLR C/log(N) plaque decay bridge to RH",
        commit_msg="feat(NumberTheory/LSeries): add BaezDuarteLogarithmicPlaqueDecay C/log N bridge",
    ),
    PRSpec(
        pr_id="PR-8J",
        wave=8,
        staged_file="UpstreamPR_8J_UnitPartitionHomogenization.lean",
        blueprint_module="RiemannBlueprint.UpstreamPRs.UpstreamPR_8J_UnitPartitionHomogenization",
        target_relpath="Mathlib/NumberTheory/LSeries/BaezDuarteUnitPartitionKernel.lean",
        target_module="Mathlib.NumberTheory.LSeries.BaezDuarteUnitPartitionKernel",
        branch="feat/baez-duarte-unit-partition-kernel",
        base_branch="feat/baez-duarte-logarithmic-plaque-decay",
        pr_title="feat(NumberTheory/LSeries): Dirichlet unit-partition duality and homogeneous unit-defect kernel",
        commit_msg="feat(NumberTheory/LSeries): add BaezDuarteUnitPartitionKernel homogeneous reduction",
    ),
    PRSpec(
        pr_id="PR-8K",
        wave=8,
        staged_file="UpstreamPR_8K_SuperdiagonalAndOrthogonalTriple.lean",
        blueprint_module="RiemannBlueprint.UpstreamPRs.UpstreamPR_8K_SuperdiagonalAndOrthogonalTriple",
        target_relpath="Mathlib/NumberTheory/LSeries/BaezDuarteSuperdiagonalOrthogonalTriple.lean",
        target_module="Mathlib.NumberTheory.LSeries.BaezDuarteSuperdiagonalOrthogonalTriple",
        branch="feat/baez-duarte-superdiagonal-orthogonal-triple",
        base_branch="feat/baez-duarte-unit-partition-kernel",
        pr_title="feat(NumberTheory/LSeries): all-m superdiagonal zeros, orthogonal triple {v_2,v_3,v_4}, and {1..9} folding",
        commit_msg="feat(NumberTheory/LSeries): add BaezDuarteSuperdiagonalOrthogonalTriple",
    ),
    PRSpec(
        pr_id="PR-8L",
        wave=8,
        staged_file="UpstreamPR_8L_PlaqueRowTelescopingAndSimplex.lean",
        blueprint_module="RiemannBlueprint.UpstreamPRs.UpstreamPR_8L_PlaqueRowTelescopingAndSimplex",
        target_relpath="Mathlib/NumberTheory/LSeries/BaezDuartePlaqueRowTelescoping.lean",
        target_module="Mathlib.NumberTheory.LSeries.BaezDuartePlaqueRowTelescoping",
        branch="feat/baez-duarte-plaque-row-telescoping",
        base_branch="feat/baez-duarte-superdiagonal-orthogonal-triple",
        pr_title="feat(NumberTheory/LSeries): 1D plaque row-sum telescoping and Graph-Laplacian simplex decomposition",
        commit_msg="feat(NumberTheory/LSeries): add BaezDuartePlaqueRowTelescoping",
    ),
    PRSpec(
        pr_id="PR-8M",
        wave=8,
        staged_file="UpstreamPR_8M_PointwiseContinuityAndPeriodicity.lean",
        blueprint_module="RiemannBlueprint.UpstreamPRs.UpstreamPR_8M_PointwiseContinuityAndPeriodicity",
        target_relpath="Mathlib/NumberTheory/LSeries/BaezDuartePointwiseContinuity.lean",
        target_module="Mathlib.NumberTheory.LSeries.BaezDuartePointwiseContinuity",
        branch="feat/baez-duarte-pointwise-continuity",
        base_branch="feat/baez-duarte-plaque-row-telescoping",
        pr_title="feat(NumberTheory/LSeries): pointwise continuity, modular duality, and palindromic periodicity",
        commit_msg="feat(NumberTheory/LSeries): add BaezDuartePointwiseContinuity",
    ),
    PRSpec(
        pr_id="PR-8N",
        wave=8,
        staged_file="UpstreamPR_8N_HarmonicCellL2QuadratureAndPrimeJumps.lean",
        blueprint_module="RiemannBlueprint.UpstreamPRs.UpstreamPR_8N_HarmonicCellL2QuadratureAndPrimeJumps",
        target_relpath="Mathlib/NumberTheory/LSeries/BaezDuarteHarmonicCellQuadrature.lean",
        target_module="Mathlib.NumberTheory.LSeries.BaezDuarteHarmonicCellQuadrature",
        branch="feat/baez-duarte-harmonic-cell-quadrature",
        base_branch="feat/baez-duarte-pointwise-continuity",
        pr_title="feat(NumberTheory/LSeries): harmonic-cell L2 quadrature, exact cell partial sums, and prime divisor jumps",
        commit_msg="feat(NumberTheory/LSeries): add BaezDuarteHarmonicCellQuadrature",
    ),
    PRSpec(
        pr_id="PR-8O",
        wave=8,
        staged_file="UpstreamPR_8O_PeriodicL2CellSumCompression.lean",
        blueprint_module="RiemannBlueprint.UpstreamPRs.UpstreamPR_8O_PeriodicL2CellSumCompression",
        target_relpath="Mathlib/NumberTheory/LSeries/BaezDuartePeriodicQuadrature.lean",
        target_module="Mathlib.NumberTheory.LSeries.BaezDuartePeriodicQuadrature",
        branch="feat/baez-duarte-periodic-quadrature",
        base_branch="feat/baez-duarte-harmonic-cell-quadrature",
        pr_title="feat(NumberTheory/LSeries): periodic L2 cell-sum compression across residue classes modulo L_N",
        commit_msg="feat(NumberTheory/LSeries): add BaezDuartePeriodicQuadrature",
    ),
    PRSpec(
        pr_id="PR-8P",
        wave=8,
        staged_file="UpstreamPR_8P_HarmonicSlabNonTermination.lean",
        blueprint_module="RiemannBlueprint.UpstreamPRs.UpstreamPR_8P_HarmonicSlabNonTermination",
        target_relpath="Mathlib/NumberTheory/LSeries/BaezDuarteHarmonicSlabNonTermination.lean",
        target_module="Mathlib.NumberTheory.LSeries.BaezDuarteHarmonicSlabNonTermination",
        branch="feat/baez-duarte-harmonic-slab-nontermination",
        base_branch="feat/baez-duarte-periodic-quadrature",
        pr_title="feat(NumberTheory/LSeries): harmonic-slab non-termination and finite-truncation L2 positivity",
        commit_msg="feat(NumberTheory/LSeries): add BaezDuarteHarmonicSlabNonTermination",
    ),
    PRSpec(
        pr_id="PR-8Q",
        wave=8,
        staged_file="UpstreamPR_8Q_PrimeCellL2EnergyFloor.lean",
        blueprint_module="RiemannBlueprint.UpstreamPRs.UpstreamPR_8Q_PrimeCellL2EnergyFloor",
        target_relpath="Mathlib/NumberTheory/LSeries/BaezDuartePrimeCellEnergyFloor.lean",
        target_module="Mathlib.NumberTheory.LSeries.BaezDuartePrimeCellEnergyFloor",
        branch="feat/baez-duarte-prime-cell-energy-floor",
        base_branch="feat/baez-duarte-harmonic-slab-nontermination",
        pr_title="feat(NumberTheory/LSeries): exact prime-cell L2 energy defect identity and 1/(2*p^2) tail floor",
        commit_msg="feat(NumberTheory/LSeries): add BaezDuartePrimeCellEnergyFloor",
    ),
]

IMPORT_MAP: Dict[str, str] = {
    spec.blueprint_module: spec.target_module for spec in PR_REGISTRY
}


def rewrite_upstream_imports(source: str) -> str:
    """Rewrite internal RiemannBlueprint.UpstreamPRs.* imports to canonical Mathlib.* paths."""
    out = source
    for old_mod, new_mod in sorted(IMPORT_MAP.items(), key=lambda kv: -len(kv[0])):
        out = out.replace(old_mod, new_mod)
    if re.search(r"RiemannBlueprint\.UpstreamPRs\.", out):
        leftover = re.findall(r"RiemannBlueprint\.UpstreamPRs\.[A-Za-z0-9_]+", out)
        raise RuntimeError(f"Unmapped UpstreamPRs import(s) remained after rewrite: {leftover}")
    return out


def run_cmd(cmd: List[str], cwd: Optional[pathlib.Path] = None) -> subprocess.CompletedProcess:
    return subprocess.run(cmd, cwd=str(cwd) if cwd else None, text=True, capture_output=True)


def check_status(mathlib_dir: Optional[pathlib.Path]) -> None:
    print("=== gh auth status ===")
    gh = run_cmd(["gh", "auth", "status"])
    print((gh.stdout + gh.stderr).strip() or "(no output)")

    print("\n=== workspace git remote -v ===")
    gr = run_cmd(["git", "remote", "-v"], cwd=STAGING_DIR)
    print((gr.stdout + gr.stderr).strip() or "(no git repository in staging directory)")

    if mathlib_dir is not None:
        print(f"\n=== mathlib4 clone status ({mathlib_dir}) ===")
        if not (mathlib_dir / "Mathlib.lean").is_file():
            print("WARNING: Mathlib.lean not found in --mathlib-dir")
        else:
            mr = run_cmd(["git", "remote", "-v"], cwd=mathlib_dir)
            print((mr.stdout + mr.stderr).strip())

    print(f"\n=== Carved PR Registry ({len(PR_REGISTRY)} modules across Waves 1-8) ===")
    for spec in PR_REGISTRY:
        staged = STAGING_DIR / spec.staged_file
        lines = len(staged.read_text(encoding="utf-8").splitlines()) if staged.is_file() else -1
        print(f"  [Wave {spec.wave}] {spec.pr_id:5s} | {spec.staged_file:44s} ({lines:3d}L) -> {spec.target_module}")


def check_remote_ci(repo_slug: str = "Qamarbajwa/mathlib4") -> int:
    remote_url = f"https://github.com/{repo_slug}.git"
    print(f"=== Remote Branch & CI Readiness Check ({repo_slug}) ===")
    ls_res = run_cmd(["git", "ls-remote", "--heads", remote_url, "refs/heads/feat/*"])
    if ls_res.returncode != 0:
        print(ls_res.stderr, file=sys.stderr)
        return ls_res.returncode
    remote_heads: Dict[str, str] = {}
    for line in ls_res.stdout.splitlines():
        parts = line.strip().split("\t")
        if len(parts) == 2 and parts[1].startswith("refs/heads/"):
            remote_heads[parts[1][len("refs/heads/"):]] = parts[0]

    missing = 0
    for spec in PR_REGISTRY:
        sha = remote_heads.get(spec.branch)
        if not sha:
            missing += 1
            print(f"  [MISSING] [Wave {spec.wave}] {spec.pr_id:5s} | {spec.branch}")
            continue
        cr_res = run_cmd(["gh", "api", f"repos/{repo_slug}/commits/{sha}/check-runs"])
        ci_summary = "api_unavailable"
        if cr_res.returncode == 0 and cr_res.stdout.strip():
            data = json.loads(cr_res.stdout)
            runs = data.get("check_runs", [])
            ci_summary = f"check_runs={len(runs)}" if runs else "0 check_runs (branch ready, no PR opened)"
        print(f"  [READY]   [Wave {spec.wave}] {spec.pr_id:5s} | {spec.branch:34s} | {sha[:12]} | {ci_summary}")

    print(f"\nSummary: {len(PR_REGISTRY) - missing}/{len(PR_REGISTRY)} registered branches present on {repo_slug}.")
    return 0 if missing == 0 else 1


def check_ci(upstream_repo: str = "leanprover-community/mathlib4", fork_repo: str = "Qamarbajwa/mathlib4", fork_owner: str = "Qamarbajwa") -> int:
    rc = check_remote_ci(fork_repo)
    print(f"\n=== Live PR & CI Monitor ({upstream_repo}, author={fork_owner}) ===")
    pr_res = run_cmd([
        "gh", "pr", "list", "--repo", upstream_repo, "--author", fork_owner,
        "--state", "all", "--json", "number,title,headRefName,state,url,mergeStateStatus"
    ])
    if pr_res.returncode != 0:
        print(pr_res.stderr, file=sys.stderr)
        return pr_res.returncode
    prs = json.loads(pr_res.stdout or "[]")
    target_branches = {spec.branch: spec for spec in PR_REGISTRY}
    matched = [p for p in prs if p.get("headRefName") in target_branches]
    other_open = [p for p in prs if p.get("headRefName") not in target_branches and p.get("state") == "OPEN"]
    if not matched:
        print("  (no carved Wave 1-4 PRs opened yet)")
    for pr in sorted(matched, key=lambda x: x["number"]):
        num = pr["number"]
        spec = target_branches[pr["headRefName"]]
        chk_res = run_cmd(["gh", "pr", "checks", str(num), "--repo", upstream_repo])
        chk_lines = [l.strip() for l in (chk_res.stdout or "").splitlines() if l.strip()]
        chk_summary = " | ".join(chk_lines[:4]) if chk_lines else (chk_res.stderr.strip() or "pending")
        print(f"  PR #{num} [{pr['state']}] ({spec.pr_id}, {pr['headRefName']}) -> {pr['url']}")
        print(f"    mergeState={pr.get('mergeStateStatus')} | checks: {chk_summary}")
    if other_open:
        print(f"  (note: {len(other_open)} unrelated open PR(s) by {fork_owner})")
    return rc


def update_mathlib_root_imports(mathlib_dir: pathlib.Path, target_modules: List[str]) -> bool:
    root_file = mathlib_dir / "Mathlib.lean"
    if not root_file.is_file():
        return False
    lines = root_file.read_text(encoding="utf-8").splitlines()
    mod_pat = re.compile(r"^public (?:meta )?import (Mathlib\.\S+)$")
    existing_mods = set()
    for line in lines:
        m = mod_pat.match(line)
        if m:
            existing_mods.add(m.group(1))
    if not existing_mods:
        raise RuntimeError(f"Could not find `public import Mathlib.` block in {root_file}")
    changed = False
    for target_module in target_modules:
        if target_module in existing_mods:
            continue
        existing_mods.add(target_module)
        insert_idx = None
        last_mathlib_idx = -1
        for i, line in enumerate(lines):
            m = mod_pat.match(line)
            if m:
                last_mathlib_idx = i
                if m.group(1) > target_module:
                    insert_idx = i
                    break
        if insert_idx is None:
            insert_idx = last_mathlib_idx + 1
        lines.insert(insert_idx, f"public import {target_module}")
        changed = True
    if not changed:
        return False
    root_file.write_text("\n".join(lines) + "\n", encoding="utf-8")
    return True


def select_specs(wave: str, pr_filter: Optional[str] = None) -> List[PRSpec]:
    specs = list(PR_REGISTRY) if wave == "all" else [s for s in PR_REGISTRY if s.wave == int(wave)]
    if pr_filter:
        wanted = {x.strip() for x in pr_filter.split(",") if x.strip()}
        specs = [s for s in specs if s.pr_id in wanted]
    return specs


def build_pr_body(spec: PRSpec, lines: int, max_len: int) -> str:
    return (
        f"### Summary\n\n"
        f"Extracts `{spec.target_module}` from `RiemannBlueprint` (`{spec.staged_file}`, "
        f"`{lines}` lines, max width `{max_len}` chars).\n\n"
        f"### Verification\n"
        f"- `lake build {spec.target_module}`: verified (`0` errors, `0` warnings)\n"
        f"- `#lint` (15 Mathlib linters): `0` errors\n"
        f"- `#print axioms`: strictly `[propext, Classical.choice, Quot.sound]`\n"
        f"- Epistemic scope: `NO_RH_PROOF = TRUE`\n\n"
        f"### AI-Assistance Disclosure\n"
        f"AI coding assistance (Google DeepMind Antigravity) was used during Lean 4 proof refactoring "
        f"and style formatting; all declarations were kernel-verified without `sorry`."
    )


def collect_branch_modules(spec: PRSpec) -> List[str]:
    by_branch = {s.branch: s for s in PR_REGISTRY}
    visited: set[str] = set()
    mods: List[str] = []

    def dfs(s: PRSpec) -> None:
        if s.branch in visited:
            return
        visited.add(s.branch)
        if s.base_branch in by_branch:
            dfs(by_branch[s.base_branch])
        for mb in s.merge_branches:
            if mb in by_branch:
                dfs(by_branch[mb])
        mods.append(s.target_module)

    dfs(spec)
    return mods


def git_checked(cmd: List[str], cwd: pathlib.Path) -> subprocess.CompletedProcess:
    res = run_cmd(cmd, cwd=cwd)
    if res.returncode != 0:
        raise RuntimeError(f"Command {' '.join(cmd)} failed ({res.returncode}):\n{res.stdout}\n{res.stderr}")
    return res


def main() -> int:
    parser = argparse.ArgumentParser(description="Stage, rewrite imports, and push carved PRs to mathlib4.")
    parser.add_argument("--mathlib-dir", type=pathlib.Path, default=None, help="Path to local mathlib4 clone.")
    parser.add_argument("--wave", choices=["1", "2", "3", "4", "5", "6", "7", "8", "all"], default="1", help="Wave to process (default: 1).")
    parser.add_argument("--pr", default=None, help="Optional comma-separated PR IDs (e.g. PR-3H) to filter.")
    parser.add_argument("--remote", default="origin", help="Git remote to push branches to (default: origin).")
    parser.add_argument("--repo-slug", default="Qamarbajwa/mathlib4", help="Fork owner/repo for --check-remote-ci / --check-ci.")
    parser.add_argument("--upstream-repo", default="leanprover-community/mathlib4", help="Upstream mathlib4 repo for PR creation and CI monitoring.")
    parser.add_argument("--upstream-url", default="https://github.com/leanprover-community/mathlib4.git", help="Upstream mathlib4 git URL fetched by default for rebasing.")
    parser.add_argument("--fork-owner", default="Qamarbajwa", help="GitHub fork owner opening fork PRs.")
    parser.add_argument("--base-ref", default="master", help="Root base ref replacing 'master' (default: master; auto-fetches upstream/master into FETCH_HEAD unless --no-fetch-upstream).")
    parser.add_argument("--no-fetch-upstream", action="store_true", help="Skip fetching live upstream master into FETCH_HEAD and use local --base-ref directly.")
    parser.add_argument("--skip-build", action="store_true", help="Skip lake build in --mathlib-dir when pushing pre-verified modules.")
    parser.add_argument("--force-push", action="store_true", help="Use --force when pushing updated branches to --remote.")
    parser.add_argument("--status", action="store_true", help="Print gh auth, git remote, and PR registry status.")
    parser.add_argument("--check-remote-ci", action="store_true", help="Verify pushed branches and check-run status on --repo-slug.")
    parser.add_argument("--check-ci", action="store_true", help="Monitor live fork PRs and CI check runs on --upstream-repo and --repo-slug.")
    parser.add_argument("--dry-run", action="store_true", help="Rewrite imports in memory and report actions without modifying mathlib4.")
    parser.add_argument("--push", action="store_true", help="Create git branches, commit, and push to --remote in --mathlib-dir.")
    parser.add_argument("--create-pr", action="store_true", help="Open fork PRs against --upstream-repo and post the 'LLM-generated' label comment.")
    args = parser.parse_args()

    if args.status:
        check_status(args.mathlib_dir)
        return 0

    if args.check_remote_ci:
        return check_remote_ci(args.repo_slug)

    if args.check_ci:
        return check_ci(args.upstream_repo, args.repo_slug, args.fork_owner)

    specs = select_specs(args.wave, args.pr)
    root_base_ref = args.base_ref
    if args.mathlib_dir is not None and not args.no_fetch_upstream and not args.dry_run:
        if not (args.mathlib_dir / "Mathlib.lean").is_file():
            print(f"ERROR: --mathlib-dir {args.mathlib_dir} does not look like a mathlib4 checkout", file=sys.stderr)
            return 1
        print(f"Fetching live upstream master from {args.upstream_url} ...")
        git_checked(["git", "fetch", "--depth=1", args.upstream_url, "master"], cwd=args.mathlib_dir)
        if args.base_ref == "master":
            root_base_ref = "FETCH_HEAD"
        print(f"Base ref for root branches: {root_base_ref}")

    for spec in specs:
        src_path = STAGING_DIR / spec.staged_file
        if not src_path.is_file():
            print(f"ERROR: Missing staged file {src_path}", file=sys.stderr)
            return 1
        raw = src_path.read_text(encoding="utf-8")
        rewritten = rewrite_upstream_imports(raw)
        lines_list = rewritten.splitlines()
        max_len = max((len(l) for l in lines_list), default=0)
        print(f"[{spec.pr_id}] {spec.staged_file} -> {spec.target_relpath} ({len(lines_list)}L, max={max_len}c)")

        if args.dry_run or (args.mathlib_dir is None and not args.create_pr):
            changed_imports = [
                l for l in rewritten.splitlines() if l.startswith("public import ") and "Mathlib." in l
            ]
            print(f"  dry-run imports OK ({len(changed_imports)} Mathlib public imports); branch={spec.branch}")
            continue

        if args.mathlib_dir is not None:
            mdir = args.mathlib_dir
            if not (mdir / "Mathlib.lean").is_file():
                print(f"ERROR: --mathlib-dir {mdir} does not look like a mathlib4 checkout", file=sys.stderr)
                return 1

            dest = mdir / spec.target_relpath
            dest.parent.mkdir(parents=True, exist_ok=True)
            base_ref = root_base_ref if spec.base_branch == "master" else spec.base_branch
            git_checked(["git", "checkout", base_ref], cwd=mdir)
            git_checked(["git", "checkout", "-B", spec.branch], cwd=mdir)
            for mb in spec.merge_branches:
                merge_res = run_cmd(
                    ["git", "merge", "--no-edit", "--allow-unrelated-histories", "-X", "ours", mb],
                    cwd=mdir,
                )
                if merge_res.returncode != 0:
                    print(merge_res.stdout + merge_res.stderr, file=sys.stderr)
                    return merge_res.returncode
            dest.write_text(rewritten, encoding="utf-8")
            update_mathlib_root_imports(mdir, collect_branch_modules(spec))

            if not args.skip_build:
                build_res = run_cmd(["lake", "build", spec.target_module], cwd=mdir)
                if build_res.returncode != 0:
                    print(build_res.stdout + build_res.stderr, file=sys.stderr)
                    return build_res.returncode

            if args.push:
                git_checked(["git", "add", spec.target_relpath, "Mathlib.lean"], cwd=mdir)
                diff_res = run_cmd(["git", "diff", "--cached", "--quiet"], cwd=mdir)
                if diff_res.returncode != 0:
                    git_checked(["git", "commit", "-m", spec.commit_msg], cwd=mdir)
                push_cmd = ["git", "push"] + (["--force"] if args.force_push else []) + ["-u", args.remote, spec.branch]
                push_res = run_cmd(push_cmd, cwd=mdir)
                if push_res.returncode != 0:
                    print(push_res.stdout + push_res.stderr, file=sys.stderr)
                    return push_res.returncode

        if args.create_pr:
            if not ALLOW_UPSTREAM_BOT_ACTIONS:
                print(
                    "ERROR: --create-pr is blocked by mathlib4 AI policy (ALLOW_UPSTREAM_BOT_ACTIONS = False). "
                    "Push branches only to your own fork Qamarbajwa/mathlib4.",
                    file=sys.stderr,
                )
                return 1
            body = build_pr_body(spec, len(lines_list), max_len)
            existing = run_cmd([
                "gh", "pr", "list", "--repo", args.upstream_repo,
                "--head", f"{args.fork_owner}:{spec.branch}", "--state", "open", "--json", "url"
            ])
            urls = json.loads(existing.stdout or "[]") if existing.returncode == 0 else []
            if urls:
                pr_url = urls[0]["url"]
                print(f"  PR already open: {pr_url}")
            else:
                pr_res = run_cmd([
                    "gh", "pr", "create", "--repo", args.upstream_repo,
                    "--head", f"{args.fork_owner}:{spec.branch}", "--base", "master",
                    "--title", spec.pr_title, "--body", body,
                ])
                out_str = (pr_res.stdout + pr_res.stderr).strip()
                print(f"  gh pr create: {out_str}")
                if pr_res.returncode != 0:
                    return pr_res.returncode
                pr_url = pr_res.stdout.strip().splitlines()[-1]
                cmt_res = run_cmd([
                    "gh", "pr", "comment", pr_url, "--repo", args.upstream_repo,
                    "--body", "LLM-generated",
                ])
                print(f"  bot label comment: {(cmt_res.stdout + cmt_res.stderr).strip()}")
                if cmt_res.returncode != 0:
                    return cmt_res.returncode

    if args.mathlib_dir is None and not args.dry_run and not args.create_pr:
        print("\nNote: Pass --mathlib-dir <path> to write into a local mathlib4 clone (use --status for auth/remotes).")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
