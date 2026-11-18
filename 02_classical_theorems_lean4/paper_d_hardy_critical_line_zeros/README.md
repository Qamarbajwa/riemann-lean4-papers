<!-- Zenodo DOI: 10.5281/zenodo.24328045 | Epistemic Status: NO_RH_PROOF = TRUE -->
# Paper D: Formalizing Hardy (1914) Unconditional Theorem on Critical-Line Zeros of the Riemann Zeta Function in Lean 4

- **Zenodo DOI:** [10.5281/zenodo.24328045](https://doi.org/10.5281/zenodo.24328045)
- **Epistemic Invariant:** NO_RH_PROOF = TRUE

# Submission Package: Hardy's (1914) Unconditional Critical-Line Zeros Theorem

## Title
**Formalizing Hardy's (1914) Unconditional Theorem on Critical-Line Zeros of the Riemann Zeta Function in Lean 4**

## Author
- **Qamar Munawer**, Brandenburg University of Technology Cottbus–Senftenberg

## Overview
This package contains the complete LaTeX source, compiled 6-page manuscript, and kernel-verified Lean 4 formalization of G. H. Hardy's (1914) unconditional theorem proving that $\zeta(s)$ has infinitely many zeros on the critical line $\operatorname{Re}(s) = 1/2$:
1. **IVT Sign-Change Detector (`MathlibPR_CriticalLineZeros.lean`, `MathlibPR_HardyZeros.lean`):** `criticalLine`, `exists_criticalLine_zero_of_sign_change`, `infinite_criticalLine_zeros_of_sign_changes`, and `infinite_hardyZ_zeros_of_sign_changes`.
2. **Fourier–Mellin Strip Identity (`MathlibPR_HardyZeros.lean`):** Constructs `hardyG` and the Jacobi theta kernel `hardyPsi` on $|\operatorname{Im}(z)| < \pi/4$, proving `hardyG_eq_hardyPsi` via modular inversion (`jacobiTheta_S_smul`), rectangular contour shifting (`integral_boundary_rect_eq_zero_of_differentiableOn`), and Fourier inversion.
3. **Boundary Vanishing of Even Theta Derivatives & $6\pi$ Ceiling:** Proves `tendsto_iteratedDeriv_hardyThetaTerm` as $\alpha \to (\pi/4)^-$ so all even moments remain uniformly bounded by $6\pi$.
4. **Geometric Moment Contradiction & Unconditional Main Theorems:** Rules out eventual constant sign (`hardyZ_unbounded_sign_changes`), proving `infinite_criticalLine_zeros` and `infinite_hardyZ_zeros` unconditionally.

## Epistemic Status and Verification Invariants
- **Epistemic Invariant:** `NO_RH_PROOF = TRUE`. Hardy's theorem proves unconditionally that infinitely many non-trivial zeros lie on $\operatorname{Re}(s) = 1/2$; it does not establish that all non-trivial zeros lie on the critical line.
- **Foundational Axioms:** Strictly `[propext, Classical.choice, Quot.sound]` with zero `sorry`, zero `admit`, and zero custom axioms.

## Package File Manifest
- `paper_d_hardy_zeros.tex`: LaTeX source (synchronized bit-for-bit with root `paper_d_hardy_zeros.tex`).
- `paper_d_hardy_zeros.pdf`: Compiled PDF (6 pages, 0 LaTeX errors, 0 Overfull hboxes).
- `MathlibPR_HardyZeros.lean`: Unconditional Hardy (1914) proof and headline theorems (1,984 lines).
- `MathlibPR_CriticalLineZeros.lean`: Critical-line embedding and IVT sign-change detector (80 lines).
- `VerifyNoTraps.lean`: Definitional alignment and anti-trap suite (220 lines).

## Verification Instructions
Run from the `RiemannBlueprint` Lean project root:
```bash
lake env lean RiemannBlueprint/MathlibPR_CriticalLineZeros.lean
lake env lean RiemannBlueprint/MathlibPR_HardyZeros.lean
lake env lean RiemannBlueprint/VerifyNoTraps.lean
```
All commands exit with code 0 and zero `sorry` warnings.
