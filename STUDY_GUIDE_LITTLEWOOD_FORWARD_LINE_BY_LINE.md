# Line-by-Line Study Guide: `LittlewoodForward.lean`

**Source File:** [`RiemannBlueprint/RiemannBlueprint/LittlewoodForward.lean`](./RiemannBlueprint/RiemannBlueprint/LittlewoodForward.lean) (329 lines)  
**Classical Reference:** E. C. Titchmarsh, *The Theory of the Riemann Zeta-Function* (2nd ed., rev. D. R. Heath-Brown, Oxford University Press, 1986), Chapter XIV, §14.25 (Littlewood's 1912 theorem: $M(x) = O(x^{1/2 + \varepsilon}) \implies \text{RH}$).

---

## 1. High-Level Architecture vs. Titchmarsh §14.25

Titchmarsh's classical proof proceeds in three analytic steps:
1. **Partial summation for $\operatorname{Re}(s) > 1$:** Writing $M(x) = \sum_{n \le x} \mu(n)$, Abel summation gives
   $$\frac{1}{\zeta(s)} = \sum_{n=1}^{\infty} \frac{\mu(n)}{n^s} = s \int_1^\infty M(x)\, x^{-s-1}\,dx \qquad (\operatorname{Re}(s) > 1).$$
2. **Convergence and holomorphicity for $\operatorname{Re}(s) > \frac{1}{2}$:** Assuming $M(x) = O_\varepsilon(x^{1/2+\varepsilon})$ for every $\varepsilon > 0$, the integral $\int_1^\infty M(x)\, x^{-s-1}\,dx$ converges uniformly on compact subsets of $\{s \in \mathbb{C} : \operatorname{Re}(s) > \frac{1}{2}\}$, defining a holomorphic function $M_\zeta(s)$ on that half-plane.
3. **Analytic continuation / nonvanishing:** By the identity theorem, $\zeta(s)\, M_\zeta(s) = 1$ extends from $\operatorname{Re}(s) > 1$ to $\{s \in \mathbb{C} : \operatorname{Re}(s) > \frac{1}{2}\} \setminus \{1\}$, forcing $\zeta(s) \neq 0$ for $\operatorname{Re}(s) > \frac{1}{2}$ (with $s = 1$ handled separately by $\zeta(1) \neq 0$ or the pole).

In `LittlewoodForward.lean`, those three steps correspond to **Stage A** (`L49–L102`), **Stage B** (`L104–L199`), and **Stage C** (`L201–L328`). Notice one subtle Lean/Mathlib engineering choice: Mathlib's `AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq` requires a *preconnected* open set, and `{s : ℂ | 1/2 < s.re} \ {1}` is covered in Stage C by three *convex* (hence preconnected) open regions `U_top` ($\operatorname{Im} s > 0$), `U_bot` ($\operatorname{Im} s < 0$), and `U_strip` ($1/2 < \operatorname{Re} s < 1$), avoiding a direct proof that the punctured half-plane itself is preconnected.

---

## 2. Imports, Options, and Definitions (`L1–L48`)

### Imports (`L1–L8`)
- `Mathlib.NumberTheory.LSeries.RiemannZeta`, `Dirichlet`, `Nonvanishing`, `SumCoeff`: provides `riemannZeta`, `LSeries`, `LSeries_eq_mul_integral'` (Abel summation), `LSeries_one_eq_riemannZeta`, `LSeries_one_mul_Lseries_moebius`, and `riemannZeta_ne_zero_of_one_le_re`.
- `Mathlib.Analysis.MellinTransform`: provides `mellin` and `mellin_differentiableAt_of_isBigO_rpow`.
- `Mathlib.Analysis.Complex.CauchyIntegral`, `Mathlib.Analysis.Analytic.Uniqueness`: provides `DifferentiableOn.analyticOnNhd` and `AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq`.
- `RiemannBlueprint.ClassicalAnalyticInterface`: defines `RiemannBlueprint.mertens` and `RiemannBlueprint.MertensBound`.

### Linter Suppressions (`L24–L26`)
```lean
set_option linter.style.header false
set_option linter.style.longLine false
set_option linter.style.openClassical false
```
These suppress Mathlib style linters locally. A hand-written Mathlib contribution would remove all three, add an Apache-2.0 copyright header, wrap lines to 100 characters, and eliminate any `Classical` dependency warnings.

### Core Definitions (`L33–L47`)
| Lean Definition | Lines | Mathematical Meaning |
| :--- | :--- | :--- |
| `moebiusC` | `L34` | $n \mapsto (\mu(n) : \mathbb{C})$, lifting `ArithmeticFunction.moebius` (`ℤ`-valued) to `ℂ`. |
| `mellinMertens s` | `L38–L39` | $M_\zeta(s) := s \int_{(1,\infty)} M(x)\, x^{-(s+1)}\,dx$. |
| `mertensIndicator x` | `L42–L43` | $\mathbf{1}_{(1,\infty)}(x)\, M(x)$, zeroed on $(0,1]$ so `mellin mertensIndicator (-s)` matches $\int_{(1,\infty)}$ on $(0,\infty)$. |
| `mellinMertensInv s` | `L46–L47` | Piecewise right inverse equal to $(\zeta(1))^{-1}$ at $s=1$ and $M_\zeta(s)$ elsewhere (needed because `riemannZeta 1` takes a dummy nonzero value in Mathlib). |

---

## 3. Line-by-Line Walkthrough of Stage A (`L49–L102`)

### `mertens_cast_eq_sum_Icc` (`L52–L62`)
- **Statement:** `(RiemannBlueprint.mertens x : ℂ) = ∑ k ∈ Finset.Icc 1 ⌊x⌋₊, moebiusC k`.
- **Classical counterpart:** Re-indexing $\sum_{0 \le k \le x} \mu(k) = \sum_{1 \le k \le x} \mu(k)$ using $\mu(0) = 0$.
- **Tactics:**
  - `L55`: `dsimp [RiemannBlueprint.mertens, moebiusC]` unfolds `mertens` (which sums over `Finset.Iic ⌊x⌋₊`) and `moebiusC`.
  - `L56`: `push_cast` pushes the `ℤ → ℂ` coercion inside `Finset.sum`.
  - `L57–L60`: `have hIic : Finset.Iic ⌊x⌋₊ = insert 0 (Finset.Icc 1 ⌊x⌋₊)` is proved by `ext k`, `simp only [Finset.mem_Iic, Finset.mem_insert, Finset.mem_Icc]`, and `omega` (which discharges the integer arithmetic equivalence $k \le n \iff k = 0 \lor (1 \le k \land k \le n)$).
  - `L61–L62`: `rw [hIic, Finset.sum_insert (by simp)]` splits off the $k=0$ term (`0 ∉ Icc 1 _`), and `simp` evaluates `moebius 0 = 0` (`ArithmeticFunction.map_zero`).
- **Human golf:** `Iic_eq_insert` / `Finset.sum_eq_sum_Icc_of_zero` or `Finset.Icc_succ_left_eq_Ioc` patterns avoid writing `ext k` + `omega`. Often `by_cases` or `Finset.sum_subset` (showing $0$ maps to $0$) is 2 lines shorter.

### `moebiusC_sum_norm_isBigO` (`L65–L81`)
- **Statement:** `(fun n => ∑ k ∈ Finset.Icc 1 n, ‖moebiusC k‖) =O[atTop] fun n => (n : ℝ) ^ (1 : ℝ)`.
- **Classical counterpart:** $|\sum_{k=1}^n |\mu(k)|| \le n = O(n)$, required as the abscissa-of-convergence bound in Abel summation.
- **Tactics:**
  - `L67`: `refine IsBigO.of_bound 1 (Eventually.of_forall fun n => ?_)` reduces `f =O[atTop] g` to showing `‖f n‖ ≤ 1 * ‖g n‖` for all `n : ℕ`.
  - `L68–L78`: `calc` bounds each term `‖moebiusC k‖ ≤ 1` via `Finset.sum_le_sum`, `Complex.norm_intCast`, and `ArithmeticFunction.abs_moebius_le_one` (`exact_mod_cast`), evaluates `∑ _ ∈ Icc 1 n, 1 = (Icc 1 n).card`, and converts `(n + 1 - 1 : ℕ) ≤ n` via `norm_cast; simp [Nat.card_Icc]`.
  - `L79–L81`: `simpa [Real.norm_of_nonneg h_nn, Real.rpow_one, Real.norm_natCast] using h_le` strips all norms cleanly.
- **Human golf:** `have h_nn` could be `positivity` inside `rw [Real.norm_of_nonneg (by positivity)]`, and `Nat.card_Icc` gives `(n + 1 - 1) = n` directly via `omega`.

### `riemannZeta_mul_mellinMertens_of_one_lt_re` (`L84–L102`)
- **Statement:** For `1 < s.re`, `riemannZeta s * mellinMertens s = 1`.
- **Classical counterpart:** $\zeta(s) \sum_{n=1}^\infty \mu(n) n^{-s} = 1$ combined with Abel summation (`LSeries_eq_mul_integral'`).
- **Tactics:**
  - `L86–L91`: `LSeries_eq_mul_integral' moebiusC zero_le_one hs moebiusC_sum_norm_isBigO` applies Mathlib's Abel summation lemma with exponent `a = 1` (`zero_le_one : (0 : ℝ) ≤ 1`). Then `dsimp [mellinMertens]`, `congr 1` strips the leading `s *`, and `setIntegral_congr_fun measurableSet_Ioi` rewrites the integrand using `mertens_cast_eq_sum_Icc`.
  - `L92–L100`: Uses `LSeries_one_eq_riemannZeta hs` and `LSeries_one_mul_Lseries_moebius hs`, then bridges `↗ArithmeticFunction.moebius` to `moebiusC` via `LSeries_congr`.
  - `L101–L102`: Rewrites `LSeries moebiusC s` to `mellinMertens s`.
- **Human golf:** `moebiusC` could be replaced everywhere by `↗ArithmeticFunction.moebius` (`CoeFun` coercion), eliminating `LSeries_congr` (`L97–L99`) and simplifying `mertens_cast_eq_sum_Icc`!

---

## 4. Line-by-Line Walkthrough of Stage B (`L104–L199`)

### `mellinMertens_eq_mul_mellin` (`L107–L129`)
- **Statement:** `mellinMertens s = s * mellin mertensIndicator (-s)`.
- **Classical counterpart:** Writing $\int_1^\infty M(x)\, x^{-(s+1)}\,dx = \int_0^\infty \mathbf{1}_{(1,\infty)}(x) M(x)\, x^{(-s)-1}\,dx = (\mathcal{M}\, \mathbf{1}_{(1,\infty)} M)(-s)$ so Mathlib's `mellin` API applies directly.
- **Tactics:**
  - `L109–L110`: Unfolds `mellinMertens` and `mellin`, stripping `s *` with `congr 1`.
  - `L111–L119`: Proves `EqOn` on `Set.Ioi 0` by splitting `by_cases ht1 : 1 < t` and matching `(-s - 1 : ℂ) = -(s + 1)` via `ring`.
  - `L120–L129`: Rewrites the integral over `Set.Ioi 0` to `Set.Ioi 1` via `setIntegral_indicator measurableSet_Ioi` and `Set.Ioi 0 ∩ Set.Ioi 1 = Set.Ioi 1`.
- **Human golf:** `h_eq'` (`L120–L123`) is redundant; `rw [setIntegral_congr_fun measurableSet_Ioi h_eq]` works directly, and `Set.Ioi_inter_Ioi` + `max_eq_right zero_le_one` replaces `L125–L129` in one line.

### `locallyIntegrableOn_mertensIndicator` (`L132–L150`)
- **Statement:** `LocallyIntegrableOn mertensIndicator (Set.Ioi 0)`.
- **Why needed:** First hypothesis of `mellin_differentiableAt_of_isBigO_rpow`.
- **Tactics:**
  - `L134–L136`: Calls Mathlib's `locallyIntegrableOn_mul_sum_Icc` (step-function local integrability on `[0, ∞)`).
  - `L137–L142`: Transfers from `[0, ∞)` to `(0, ∞)` via `.mono_set Set.Ioi_subset_Ici_self` after `funext mertens_cast_eq_sum_Icc`.
  - `L143–L150`: Unfolds `locallyIntegrableOn_iff isLocallyClosed_Ioi`, restricts to compact `K ⊆ (0, ∞)`, applies `.indicator measurableSet_Ioi`, and uses `IntegrableOn.congr_fun` to identify the indicator with `mertensIndicator`.

### `mertensIndicator_isBigO_atTop` (`L153–L165`) & `mertensIndicator_isBigO_nhdsWithin_zero` (`L168–L172`)
- **Statements:**
  - Under `MertensBound`, `mertensIndicator =O[atTop] fun x => x ^ ((1/2 : ℝ) + ε)` for `0 < ε`.
  - Near `0+`, `mertensIndicator =O[𝓝[>] 0] fun x => x ^ (-b)` for every `b : ℝ`.
- **Tactics:**
  - `L156–L165`: Unpacks `C, hC, hbd` from `h_mertens ε hε`, uses `IsBigO.of_bound C`, restricts to `x ≥ 1` via `filter_upwards [eventually_ge_atTop (1 : ℝ)]`, and splits `1 < x` vs `x ≤ 1` (where `mertensIndicator x = 0`, closed by `positivity`).
  - `L169–L172`: Uses `isBigO_zero` (since `0 =O f`) and `congr'` on `(0, 1)`, where `mertensIndicator x = 0`.

### `mellinMertens_differentiableAt` (`L175–L199`)
- **Statement:** Under `MertensBound`, `DifferentiableAt ℂ mellinMertens s` for `1/2 < s.re`.
- **Classical counterpart:** Uniform convergence of the Mellin integral on $\operatorname{Re}(s) > 1/2$.
- **Tactics:**
  - `L178–L180`: Replaces `mellinMertens` with `fun z => z * mellin mertensIndicator (-z)`.
  - `L181–L193`: Chooses `ε := (s.re - 1/2) / 2 > 0`, sets `a := -(1/2 + ε)` and `b := (-s).re - 1`, and checks `b < (-s).re < a` by `linarith`.
  - `L194–L199`: Invokes `mellin_differentiableAt_of_isBigO_rpow` at `-s`, composes with `z ↦ -z`, and multiplies by `z` via `differentiableAt_id.mul`.

---

## 5. Line-by-Line Walkthrough of Stage C (`L201–L328`)

### Openness and Convexity Helpers (`L203–L249`)
- `isOpen_re_gt`, `isOpen_re_lt`, `isOpen_im_gt`, `isOpen_im_lt` (`L203–L213`): Use `isOpen_lt` with `Complex.continuous_re` / `Complex.continuous_im`.
- `convex_combination_gt`, `convex_combination_lt`, and `convex_{re,im}_{gt,lt}` (`L215–L249`): Manually prove convexity of open half-planes in `ℂ`.
- **Human golf:** Mathlib already has `convex_halfSpace_re_gt`, `convex_halfSpace_re_lt`, `convex_halfSpace_im_gt`, `convex_halfSpace_im_lt` (or `Convex.isPreconnected` directly via `LinearMap.isOpenMap` / `convex_halfspace_lt`!). All 47 lines (`L203–L249`) collapse to ~4 lines using Mathlib's half-space convexity lemmas.

### `riemannZeta_mul_mellinMertens_eq_one` (`L252–L315`)
- **Statement:** Under `MertensBound`, `riemannZeta s * mellinMertens s = 1` for all `1/2 < s.re` with `s ≠ 1`.
- **Tactics:**
  - `L254–L259`: Defines `F s := riemannZeta s * mellinMertens s` and `U := {s | 1/2 < s.re} \ {1}`; establishes `AnalyticOnNhd ℂ F U` from `DifferentiableOn.analyticOnNhd hU_open` using `differentiableAt_riemannZeta hs.2`.
  - `L260–L283`: Defines three overlapping convex open regions inside `U`:
    - `U_top`: `1/2 < s.re ∧ 0 < s.im` (contains `2 + I`),
    - `U_bot`: `1/2 < s.re ∧ s.im < 0` (contains `2 - I`),
    - `U_strip`: `1/2 < s.re ∧ s.re < 1` (contains `3/4 + I ∈ U_top ∩ U_strip`).
  - `L286–L297`: Uses `AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq` on `U_top` (anchored at `2 + I`) and `U_bot` (anchored at `2 - I`), where `F =ᶠ[𝓝 z₀] 1` by `riemannZeta_mul_mellinMertens_of_one_lt_re`.
  - `L298–L304`: Propagates `F = 1` from `U_top` into `U_strip` at the overlap point `3/4 + I`.
  - `L305–L315`: Splits `s.re` via `lt_trichotomy s.re 1`: `< 1` uses `U_strip`, `= 1` splits `s.im ≠ 0` (since `s ≠ 1`) into `U_bot` / `U_top`, and `> 1` uses Stage A directly.
- **Human golf:** `U_top`, `U_bot`, `U_strip` can instead be replaced by showing `{s : ℂ | 1/2 < s.re} \ {1}` is directly `IsPreconnected` (or `IsConnected`) since removing a point from a connected open subset of `ℝ²` (`ℂ`) leaves it connected (`IsOpen.isConnected_diff_singleton` / punctured plane argument), cutting ~45 lines.

### `mertens_inversion_of_bound` (`L319–L328`)
- **Statement:** `∃ I_M : ℂ → ℂ, ∀ s : ℂ, 1/2 < s.re → riemannZeta s * I_M s = 1`.
- **Tactics:** Witnesses `mellinMertensInv`; splits `by_cases h1 : s = 1`; at `s = 1` closes with `mul_inv_cancel₀ (riemannZeta_ne_zero_of_one_le_re (by norm_num))`; at `s ≠ 1` applies `riemannZeta_mul_mellinMertens_eq_one`.

---

## 6. Fifteen Self-Test Reviewer Questions

1. Why does `LittlewoodForward.lean` define `mellinMertensInv` with an explicit branch `if s = 1 then (riemannZeta 1)⁻¹ else mellinMertens s` instead of using `mellinMertens` directly?
2. Why is `riemannZeta_ne_zero_of_one_le_re (by norm_num)` valid at `s = 1` in Mathlib, and what convention does Mathlib use for `riemannZeta 1`?
3. Why does `mellinMertens` integrate over `Set.Ioi (1 : ℝ)` while `Mathlib`'s `mellin` integrates over `Set.Ioi (0 : ℝ)`? What role does `mertensIndicator` play in bridging them?
4. In `mellinMertens_eq_mul_mellin`, why is `mellin mertensIndicator` evaluated at `-s` rather than `s`?
5. Why is `moebiusC_sum_norm_isBigO` (`O(n^1)`) sufficient for `LSeries_eq_mul_integral'` in Stage A even though `MertensBound` is not assumed in Stage A?
6. Why does `locallyIntegrableOn_mertensIndicator` invoke `locallyIntegrableOn_mul_sum_Icc` on `Set.Ici 0` and then restrict to `Set.Ioi 0` via `mono_set`?
7. In `mertensIndicator_isBigO_nhdsWithin_zero`, why does `mertensIndicator =O[𝓝[>] 0] (· ^ (-b))` hold for *every* `b : ℝ`?
8. In `mellinMertens_differentiableAt`, why is `ε` chosen as `(s.re - 1/2) / 2` instead of a fixed constant?
9. What are the exact four hypotheses of Mathlib's `mellin_differentiableAt_of_isBigO_rpow`, and how do `a = -(1/2 + ε)` and `b = (-s).re - 1` satisfy the strict inequalities `b < (-s).re < a`?
10. Why does `riemannZeta_mul_mellinMertens_eq_one` avoid applying `AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq` directly on `{s : ℂ | 1/2 < s.re} \ {1}`?
11. How do the three convex sets `U_top`, `U_bot`, and `U_strip` cover `{s : ℂ | 1/2 < s.re} \ {1}`, and why is `3/4 + I` chosen as the basepoint for `U_strip`?
12. Could `U_strip` have been anchored at `3/4 - I` using `U_bot` instead of `U_top`? Would any proof step change?
13. Why is `F` (`riemannZeta * mellinMertens`) proved `DifferentiableOn` first and then converted to `AnalyticOnNhd` via `DifferentiableOn.analyticOnNhd hU_open`?
14. Which Mathlib lemmas could replace the custom `isOpen_*` and `convex_*` private helpers (`L203–L249`)?
15. Where does `LittlewoodForward.lean` connect to `RiemannHypothesis` (`∀ s, riemannZeta s = 0 → ...`), and what trivial corollary turns `riemannZeta s * I_M s = 1` for `1/2 < s.re` into `RiemannHypothesis`?
