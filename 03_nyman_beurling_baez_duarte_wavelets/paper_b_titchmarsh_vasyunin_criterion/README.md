<!-- Zenodo DOI: 10.5281/zenodo.24328037 | Epistemic Status: NO_RH_PROOF = TRUE -->
# Paper B: Formalizing Titchmarsh Fractional-Part Identity and the Forward Nyman-Beurling Criterion in Lean 4

- **Zenodo DOI:** [10.5281/zenodo.24328037](https://doi.org/10.5281/zenodo.24328037)
- **Epistemic Invariant:** NO_RH_PROOF = TRUE

# Submission Package: Titchmarsh's Fractional-Part Identity and the Nyman–Beurling / Vasyunin Reduction

## Title
**Formalizing Titchmarsh's Fractional-Part Identity and the Forward Nyman–Beurling Criterion in Lean 4**

## Author
- **Qamar Munawer**, Brandenburg University of Technology Cottbus–Senftenberg

## Overview
This package contains the complete LaTeX source, compiled 9-page manuscript, and kernel-verified Lean 4 formalization (6,951 lines across five core modules plus `VerifyNoTraps.lean`) of:
1. **Titchmarsh's Mellin Fractional-Part Identity (`MellinFracPart.lean`):**
   $$\zeta(s) = \frac{s}{s-1} - s\int_0^1 \left\{\frac{1}{x}\right\} x^{s-1}\,\mathrm{d}x \qquad (\operatorname{Re}(s) > 0,\; s \neq 1)$$
   proved unconditionally via `mellin_recipFract_unit_interval_of_pos_re`.
2. **Forward Nyman–Beurling and Báez-Duarte Criteria (`MathlibPR_NymanBeurling.lean`):**
   Unconditional implications toward Mathlib's `_root_.RiemannHypothesis`: `RiemannHypothesis.of_nymanBeurling_approx` and `RiemannHypothesis.of_baezDuarte_approx`.
3. **Unconditional Base, Target, Diagonal, and Cross-Integrals (`MathlibPR_VasyuninIntegral.lean`, `MathlibPR_VasyuninCrossIntegral.lean`):**
   Exact closed-form evaluation of `intervalIntegral_recipFract_zero_to_one` ($1 - \gamma$), `intervalIntegral_recipFractScaled_eq_bVasyunin`, and the unreduced general Vasyunin cross-integral `intervalIntegral_recipFractScaled_cross` for all $j, k \ge 1$ via Stirling asymptotics (`Stirling.tendsto_stirlingSeq_sqrt_pi`), Euler–Mascheroni asymptotics (`Real.tendsto_eulerMascheroniSeq'`), and Mathlib's cotangent series (`cot_series_rep'`).
4. **Affine Rank-4 Boundary Collapse (`Section8_VasyuninBDR.lean`, `MathlibPR_VasyuninCrossIntegral.lean`):**
   Zero-assumption pure cotangent distance identities on $\mathcal{A}_N = \{c \mid D_1(c, N) = 0 \land D_0(c, N) = 2\}$: `affine_l2_pure_cotangent_bridge`, `affine_l2_dist_eq_one_sub_scot`, `nymanBeurling_approx_iff_scot_gt`, and `riemannHypothesis_of_cotangent_limit`.

## Epistemic Status and Verification Invariants
- **Epistemic Invariant:** `NO_RH_PROOF = TRUE`. All theorems establish unconditional integral/matrix identities or conditional implications toward `RiemannHypothesis`; no unconditional proof of RH is claimed.
- **Foundational Axioms:** Strictly `[propext, Classical.choice, Quot.sound]` with zero `sorry`, zero `admit`, and zero custom axioms.

## Package File Manifest
- `paper_b_nyman_beurling.tex`: LaTeX source (synchronized bit-for-bit with root `paper_b_nyman_beurling.tex`).
- `paper_b_nyman_beurling.pdf`: Compiled PDF (9 pages, 0 LaTeX errors, 0 Overfull hboxes > 10 pt).
- `MellinFracPart.lean`: Fractional-part Mellin representation on $\operatorname{Re}(s) > 0$ (1,366 lines).
- `MathlibPR_NymanBeurling.lean`: Forward Nyman–Beurling and Báez-Duarte criteria (1,461 lines).
- `MathlibPR_VasyuninIntegral.lean`: Base and diagonal fractional-part dilation integrals (207 lines).
- `MathlibPR_VasyuninCrossIntegral.lean`: Unconditional Vasyunin cross-integral and affine cotangent bridge (1,454 lines).
- `Section8_VasyuninBDR.lean`: Unreduced rank-4 `GSmooth` factorization and BDR boundary identities (2,463 lines).
- `VerifyNoTraps.lean`: Definitional alignment and non-vacuity checks (220 lines).

## Verification Instructions
Run from the `RiemannBlueprint` Lean project root:
```bash
lake env lean RiemannBlueprint/MellinFracPart.lean
lake env lean RiemannBlueprint/MathlibPR_NymanBeurling.lean
lake env lean RiemannBlueprint/MathlibPR_VasyuninIntegral.lean
lake env lean RiemannBlueprint/MathlibPR_VasyuninCrossIntegral.lean
lake env lean RiemannBlueprint/Section8_VasyuninBDR.lean
lake env lean RiemannBlueprint/VerifyNoTraps.lean
```
All commands exit with code 0 and zero `sorry` warnings.
