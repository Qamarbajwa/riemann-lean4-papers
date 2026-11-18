<!-- Zenodo DOI: 10.5281/zenodo.24353574 -->
# Paper C: Formalizing De la Vallee Poussin (1899) Unconditional Zero-Free Region for the Riemann Zeta Function in Lean 4

- **Zenodo DOI:** [`10.5281/zenodo.24353574`](https://doi.org/10.5281/zenodo.24353574) (prev `10.5281/zenodo.24328039`)
- **MSC 2020:** Primary 11M26; Secondary 46E20, 68V20

# Submission Package: De la Vallée Poussin's (1899) Unconditional Zero-Free Region

## Title
**Formalizing De la Vallée Poussin's (1899) Unconditional Zero-Free Region for the Riemann Zeta Function in Lean 4**

## Author
- **Qamar Munawer**, Brandenburg University of Technology Cottbus–Senftenberg

## Overview
This package provides the complete LaTeX source, compiled 7-page manuscript, and kernel-verified Lean 4 formalization of de la Vallée Poussin's unconditional polynomial-logarithmic zero-free region in `MathlibPR_ZeroFreeRegion.lean`:
$$\exists c > 0,\;\forall s \in \mathbb{C},\quad 2 \le |\operatorname{Im}(s)| \implies 1 - \frac{c}{\ln^9(|\operatorname{Im}(s)| + 2)} < \operatorname{Re}(s) \implies \zeta(s) \neq 0.$$

Rather than introducing logarithmic derivatives $-\zeta'/\zeta$, the proof specializes Mathlib's `norm_LFunction_product_ge_one` directly on $\zeta(s)$ (`norm_riemannZeta_product_ge_one`) and discharges all analytic ingredients unconditionally:
1. `exists_pole_bound_one_add`: Constructive pole bound $\|\zeta(1+x)\| \le C_{\text{pole}} / x$ on $(0, 1]$ from continuity of Mathlib's `riemannZeta₀`.
2. `norm_riemannZeta_le_of_log_strip`: Euler–Maclaurin strip growth bound $\|\zeta(s)\| \le (10e + 3)\ln(|\operatorname{Im}(s)|+2)$ on $1 - (2\ln(|t|+2))^{-1} \le \operatorname{Re}(s) \le 2$ (`|t| ≥ 3/2`).
3. `riemannZeta_horizontal_lipschitz_of_zero`: Horizontal Lipschitz estimate via Cauchy's integral formula on a disk of radius $R = (8\ln(|y|+2))^{-1}$ with `C_lip = 16 * (10 * Real.exp 1 + 3)`.
4. `valleePoussin_cubic_opt_identity` & `deLaValleePoussin_contradiction`: The $\eta = 3\delta$ optimization ($256/27$).
5. `deLaValleePoussin_zero_free_region_unconditional`: Final hypothesis-free boundary theorem with $c = \min(1/8, c_0)$.

## Mathematical Scope and Verification Invariants
- **MSC 2020:** Primary `11M26`; Secondary `46E20`, `68V20`. Formalizes an unconditional classical zero-free boundary inside the critical strip.
- **Foundational Axioms:** Strictly `[propext, Classical.choice, Quot.sound]` with zero `sorry`, zero `admit`, and zero custom axioms.
- **Definitional Binding:** `VerifyNoTraps.lean` certifies `riemannZeta = _root_.riemannZeta` by `rfl`.

## Package File Manifest
- `paper_c_zero_free_region.tex`: LaTeX source (synchronized bit-for-bit with root `paper_c_zero_free_region.tex`).
- `paper_c_zero_free_region.pdf`: Compiled PDF (7 pages, 0 LaTeX errors, 0 Overfull hboxes > 10 pt).
- `MathlibPR_ZeroFreeRegion.lean`: Unconditional zero-free region theorem and analytic bounds (1,092 lines).
- `MathlibPR_CriticalLineZeros.lean`: 3-4-1 trigonometric positivity and critical-line utilities (80 lines).
- `VerifyNoTraps.lean`: Definitional alignment and anti-trap verification suite (220 lines).

## Verification Instructions
Run from the `RiemannBlueprint` Lean project root:
```bash
lake env lean RiemannBlueprint/MathlibPR_CriticalLineZeros.lean
lake env lean RiemannBlueprint/MathlibPR_ZeroFreeRegion.lean
lake env lean RiemannBlueprint/VerifyNoTraps.lean
```
All commands exit with code 0 and zero `sorry` warnings.
