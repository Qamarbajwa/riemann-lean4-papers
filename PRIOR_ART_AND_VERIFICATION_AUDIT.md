# Prior-Art and Formal Verification Audit

**Repository:** `Qamarbajwa/RiemannBlueprint` (Lean `v4.35.0`, Mathlib `v4.35.0`)  
**Companion Notes:** `Qamarbajwa/riemann-lean4-papers`  
**Audit Date:** 2026-11-19

---

## 1. Ecosystem Prior-Art Comparison (`mathlib4` and `PrimeNumberTheoremAnd`)

### 1.1 De la Vallée Poussin Zero-Free Region (`deLaValleePoussin_zero_free_region_unconditional`)
- **Files in this repository:**
  - `RiemannBlueprint/RiemannBlueprint/MathlibPR_ZeroFreeRegion.lean` (`L995`)
  - `RiemannBlueprint/RiemannBlueprint/Modules/ZetaZeroFreeRegion.lean` (`L134`)
- **Statement formalized:**
  $$\exists c > 0,\ \forall s \in \mathbb{C},\ 2 \le |\operatorname{Im}(s)| \implies 1 - \frac{c}{\ln^9(|\operatorname{Im}(s)| + 2)} < \operatorname{Re}(s) \implies \zeta(s) \neq 0.$$
- **Comparison with `leanprover-community/mathlib4`:**
  - `mathlib4` (`Mathlib.NumberTheory.LSeries.Nonvanishing`) already provides `riemannZeta_ne_zero_of_one_le_re` (nonvanishing on $\operatorname{Re}(s) \ge 1$) and `norm_LFunction_product_ge_one` (the 3-4-1 trigonometric product inequality for Dirichlet $L$-functions).
  - `mathlib4` does **not** currently contain a classical strip zero-free region of the form $\sigma > 1 - c / \log^k |t|$.
- **Comparison with `AlexKontorovich/PrimeNumberTheoremAnd`:**
  - `PrimeNumberTheoremAnd` (`PrimeNumberTheoremAnd/ZetaBounds.lean`, `lemma ZetaZeroFree9 : ZetaZeroFreeGenProp 9`) **already formalized** the $\log^9 |t|$ zero-free region:
    $$\exists A \in (0, 1/2],\ \forall \sigma, t,\ 3 < |t| \implies 1 - \frac{A}{\log^9 |t|} \le \sigma < 1 \implies \zeta(\sigma + it) \neq 0.$$
  - **Shared mathematical structure:** Both proofs arrive at the **same $\log^9$ exponent** via the same underlying mechanism: combining the 3-4-1 inequality with a $\log |t|$ strip bound for $\zeta(s)$ and a $\log^2 |t|$ derivative/Lipschitz bound along a horizontal segment of length $O(\delta)$ near $\sigma = 1$ (since $(1/\delta)^3 \cdot (\log^2 |t| \cdot \delta)^4 \cdot \log |t| = \delta \log^9 |t|$ forces $\delta \ge c / \log^9 |t|$).
  - **Technical differences:** `PrimeNumberTheoremAnd/ZetaBounds.lean` develops its own Euler–Maclaurin continuation `riemannZeta0` and `LogDerivZetaBnd`, whereas `RiemannBlueprint` specializes `mathlib4`'s `norm_LFunction_product_ge_one` directly and applies Cauchy's derivative estimate on a closed ball of radius $R = 1/(8\ln(|t|+2))$ with $\ln(|t|+2)^9$ for $|t| \ge 2$.
  - **Attribution:** `PrimeNumberTheoremAnd` is the established ecosystem prior art for the $\log^9$ de la Vallée Poussin zero-free region in Lean 4; neither formalization achieves the classical $\log^1 |t|$ exponent (which requires logarithmic-derivative $-\zeta'/\zeta$ Borel–Carathéodory zero-isolation estimates).

### 1.2 Hardy's (1914) Critical-Line Zeros Theorem (`infinite_criticalLine_zeros`)
- **Files in this repository:**
  - `RiemannBlueprint/RiemannBlueprint/MathlibPR_HardyZeros.lean` (`L1976`)
  - `RiemannBlueprint/RiemannBlueprint/Modules/HardyCriticalLineZeros.lean` (`L221`)
- **Statement formalized:** `{t : ℝ | riemannZeta (criticalLine t) = 0}.Infinite` (`criticalLine t = 1/2 + I * t`).
- **Comparison with `mathlib4` & `PrimeNumberTheoremAnd`:**
  - Neither `mathlib4` nor `PrimeNumberTheoremAnd` currently formalizes Hardy's (1914) theorem (`infinite_criticalLine_zeros` / `hardyZ_unbounded_sign_changes`).
  - Built directly atop `mathlib4`'s `completedRiemannZeta`, `Complex.Gamma`, Mellin transforms, and `MeasureTheory` Lebesgue integrals.

### 1.3 Littlewood's (1912) Forward Theorem (`mertens_inversion_of_bound`)
- **File in this repository:** `RiemannBlueprint/RiemannBlueprint/LittlewoodForward.lean` (`L319`, 329 lines)
- **Statement formalized:** `MertensBound → ∃ I_M : ℂ → ℂ, ∀ s : ℂ, 1 / 2 < s.re → riemannZeta s * I_M s = 1` (paired with `LittlewoodConverse.lean` / `MathlibPR_LittlewoodMertens.lean`).
- **Comparison with `mathlib4` & `PrimeNumberTheoremAnd`:**
  - `PrimeNumberTheoremAnd/Unused/Hardy_Tauberian_theorem.lean` formalizes Hardy's real-analysis Tauberian theorem for Cesàro means, which is unrelated to Littlewood's $\zeta(s)$ Mertens-bound equivalence.
  - Neither `mathlib4` nor `PrimeNumberTheoremAnd` formalizes Littlewood's forward theorem `MertensBound → RiemannHypothesis`.
  - Uses `mathlib4`'s `LSeries_eq_mul_integral'`, `mellin_differentiableAt_of_isBigO_rpow`, and `AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq`.

### 1.4 Unconditional Bridges & Finite-$N$ Baez–Duarte / Matrix Modules
- **`UnconditionalTitchmarshBridge.lean` & `OpenStripRouche.lean`:** Discharge Titchmarsh's Mellin fractional-part identity (`mellin_recipFract_unit_interval_of_pos_re`) and compact rectangle zero-exclusion (`rectRoucheProperty_unconditional` via `Complex.norm_le_of_forall_mem_frontier_norm_le` from `mathlib4`).
- **Finite-$N$ Baez–Duarte / Vasyunin Modules (`RiemannBlueprint/Modules/`, `MatrixFactorizationAndHalfObservation.lean`):** Finite-dimensional algebraic computations ($N = 3, 4, 5, 6$), known cotangent periodicities/symmetries, Gram factorizations ($M_{M,N} = \mathbf{\Omega}_{M,N}^T \mathbf{\Omega}_{M,N}$), orthogonal Gram–Schmidt innovation telescoping ($E_{\mathrm{free}}(N) = 1 - \sum_{k=3}^N \rho_k^2/s_k$), and conditional RH criteria whose $N \to \infty$ analytic hypotheses remain open.

---

## 2. Independent Build & Axiom Receipts (Lean `v4.35.0`)

All modules listed below compile under `lake build` with zero `sorry`, zero `axiom`, and zero `opaque` declarations, and depend strictly on Lean's three standard kernel axioms `[propext, Classical.choice, Quot.sound]`:

| Theorem | Module | Axioms |
| :--- | :--- | :--- |
| `RiemannBlueprint.LittlewoodForward.mertens_inversion_of_bound` | `RiemannBlueprint.LittlewoodForward` | `[propext, Classical.choice, Quot.sound]` |
| `deLaValleePoussin_zero_free_region_unconditional` | `RiemannBlueprint.MathlibPR_ZeroFreeRegion` & `RiemannBlueprint.Modules.ZetaZeroFreeRegion` | `[propext, Classical.choice, Quot.sound]` |
| `infinite_criticalLine_zeros` | `RiemannBlueprint.MathlibPR_HardyZeros` & `RiemannBlueprint.Modules.HardyCriticalLineZeros` | `[propext, Classical.choice, Quot.sound]` |
| `anchoredWave_gram_quadForm_eq_norm_sq` | `RiemannBlueprint.MatrixFactorizationAndHalfObservation` | `[propext, Classical.choice, Quot.sound]` |
| `variational_inverse_quadForm_identity` | `RiemannBlueprint.MatrixFactorizationAndHalfObservation` | `[propext, Classical.choice, Quot.sound]` |
| `orthogonal_innovation_telescoping_energy` | `RiemannBlueprint.MatrixFactorizationAndHalfObservation` | `[propext, Classical.choice, Quot.sound]` |
| `titchmarshMellinProperty_unconditional` | `RiemannBlueprint.UnconditionalTitchmarshBridge` | `[propext, Classical.choice, Quot.sound]` |
| `rectRoucheProperty_unconditional` | `RiemannBlueprint.OpenStripRouche` | `[propext, Classical.choice, Quot.sound]` |
