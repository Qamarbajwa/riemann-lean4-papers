<!-- Zenodo DOI: 10.5281/zenodo.24328035 | Epistemic Status: NO_RH_PROOF = TRUE -->
# Paper A: Formalizing Littlewood Equivalence for the Riemann Hypothesis in Lean 4

- **Zenodo DOI:** [10.5281/zenodo.24328035](https://doi.org/10.5281/zenodo.24328035)
- **Epistemic Invariant:** NO_RH_PROOF = TRUE

# Submission Package: Littlewood's (1912) Mertens Equivalence for the Riemann Hypothesis

## Title
**Formalizing Littlewood's Equivalence for the Riemann Hypothesis in Lean 4**

## Author
- **Qamar Munawer**, Brandenburg University of Technology Cottbus–Senftenberg

## Overview
This package provides the complete LaTeX source, compiled 9-page manuscript, and kernel-verified Lean 4 formalization of J. E. Littlewood's (1912) classical equivalence:
$$\_root\_.\operatorname{RiemannHypothesis} \iff \forall \varepsilon > 0,\; M(x) = \mathcal{O}\bigl(x^{1/2 + \varepsilon}\bigr)$$
where $M(x) = \sum_{1 \le n \le x} \mu(n)$ is the Mertens summatory function.

- **Forward direction (`MathlibPR_LittlewoodMertens.lean`):** Discrete Abel summation and Mellin–Mertens analytic continuation (`mellinMertens`) yielding `RiemannHypothesis.of_mertens_isBigO`.
- **Reciprocal sub-polynomial bound (`MathlibPR_ZetaInvSubpolynomial.lean`):** Quantitative Borel–Carathéodory bounds and Hadamard three-lines interpolation under RH yielding `riemannZeta_inv_growth_of_riemannHypothesis`.
- **Converse direction and equivalence (`MathlibPR_LittlewoodConverse.lean`):** Smoothed trapezoidal mollifier contour shift yielding `isBigO_mertens_of_riemannHypothesis` and `riemannHypothesis_iff_mertens_isBigO`.

## Epistemic Status and Verification Invariants
- **Epistemic Invariant:** `NO_RH_PROOF = TRUE`. This work formalizes a classical logical equivalence; no unconditional proof of the Riemann Hypothesis is claimed.
- **Foundational Axioms:** Strictly `[propext, Classical.choice, Quot.sound]` with zero `sorry`, zero `admit`, and zero custom axioms.
- **Anti-Trap Suite:** `VerifyNoTraps.lean` certifies definitional equality against `_root_.RiemannHypothesis` and `_root_.riemannZeta` (`rfl`) and evaluates `mertens` non-vacuously on concrete inputs.

## Package File Manifest
- `paper_a_littlewood.tex`: LaTeX source (synchronized bit-for-bit with root `paper_a_littlewood.tex`).
- `paper_a_littlewood.pdf`: Compiled PDF (9 pages, 0 LaTeX errors, 0 Overfull hboxes).
- `MathlibPR_LittlewoodMertens.lean`: Forward theorem and Mellin–Mertens continuation (342 lines).
- `MathlibPR_ZetaInvSubpolynomial.lean`: Sub-polynomial $1/\zeta(s)$ growth bound under RH (1,622 lines).
- `MathlibPR_LittlewoodConverse.lean`: Converse theorem and bidirectional equivalence `riemannHypothesis_iff_mertens_isBigO` (1,790 lines).
- `VerifyNoTraps.lean`: Definitional alignment and anti-trap suite (220 lines).
- `SHA256SUMS.txt`: Recorded checksum inventory from package creation.

## Verification Instructions
Run from the `RiemannBlueprint` Lean project root:
```bash
lake env lean RiemannBlueprint/MathlibPR_LittlewoodMertens.lean
lake env lean RiemannBlueprint/MathlibPR_ZetaInvSubpolynomial.lean
lake env lean RiemannBlueprint/MathlibPR_LittlewoodConverse.lean
lake env lean RiemannBlueprint/VerifyNoTraps.lean
```
All commands exit with code 0 and zero `sorry` warnings.
