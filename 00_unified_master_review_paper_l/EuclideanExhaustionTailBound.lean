/-
Copyright (c) 2026 Qamar Munawer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qamar Munawer
-/
module

public import RiemannBlueprint.Modules.DoubleConeL2FoldingAndFlux

/-!
# Euclidean Book X.1 L² Tail Exhaustion Bound and Lebesgue Set-Integral Bridge

* `uniformCellBound`, `abs_modularCellResidual_le`, `abs_discreteCellResidual_le_of_D1_eq_zero`:
  period-free uniform bound `|A_c(n)| ≤ 1 + ∑ k ∈ Icc 1 N, |c k|` independent of `L_N`.
* `harmonicCellL2TailSum`, `harmonicCellL2TailSum_le_div_succ`,
  `harmonicCellL2TailSum_le_uniformCellBound_sq_div_succ`, `harmonicCellL2TailSum_lt_eps_of_gt`:
  Euclidean Book X.1 tail exhaustion bound `≤ B^2 / (M + 1)`.
* `setIntegral_Ioc_harmonicCell_eq`, `harmonicCellL2PartialSum_eq_setIntegral_Ioc`,
  `harmonicCellL2PartialSum_le_integral_Ioc`, `sum_primes_le_integral_Ioc`,
  `euclidean_book_ix_and_x_continuity_capstone`: exact `MeasureTheory` Lebesgue set-integral bridge.
-/

@[expose] public section

open scoped BigOperators
open MeasureTheory Set Finset

/-- Period-independent uniform `ℓ¹` amplitude bound `1 + ∑ k ∈ Icc 1 N, |c k|`. -/
noncomputable def uniformCellBound (c : ℕ → ℝ) (N : ℕ) : ℝ :=
  1 + ∑ k ∈ Finset.Icc 1 N, |c k|

/-- `uniformCellBound c N` is always non-negative (`1 ≤ uniformCellBound c N`). -/
theorem uniformCellBound_nonneg (c : ℕ → ℝ) (N : ℕ) : 0 ≤ uniformCellBound c N :=
  add_nonneg zero_le_one (Finset.sum_nonneg fun k _ => abs_nonneg (c k))

/-- **Period-Free Uniform Modular Residual Bound**: `|modularCellResidual c N n| ≤ B`. -/
theorem abs_modularCellResidual_le (c : ℕ → ℝ) (N n : ℕ) :
    |modularCellResidual c N n| ≤ uniformCellBound c N := by
  unfold modularCellResidual uniformCellBound
  have hsum : |∑ k ∈ Finset.Icc 1 N, c k * Int.fract ((n : ℝ) / (k : ℝ))| ≤
      ∑ k ∈ Finset.Icc 1 N, |c k| :=
    (Finset.abs_sum_le_sum_abs _ _).trans <| Finset.sum_le_sum fun k _ => by
      rw [abs_mul]
      exact mul_le_of_le_one_right (abs_nonneg _)
        (by rw [abs_of_nonneg (Int.fract_nonneg _)]; exact (Int.fract_lt_one _).le)
  calc |1 - ∑ k ∈ Finset.Icc 1 N, c k * Int.fract ((n : ℝ) / (k : ℝ))|
      ≤ |(1 : ℝ)| + |∑ k ∈ Finset.Icc 1 N, c k * Int.fract ((n : ℝ) / (k : ℝ))| := abs_sub _ _
    _ ≤ 1 + ∑ k ∈ Finset.Icc 1 N, |c k| := by rw [abs_one]; exact add_le_add le_rfl hsum

/-- On `D1 c N = 0`, `|discreteCellResidual c N n| ≤ uniformCellBound c N` for all `n : ℕ`. -/
theorem abs_discreteCellResidual_le_of_D1_eq_zero {c : ℕ → ℝ} {N : ℕ} (hD1 : D1 c N = 0)
    (n : ℕ) : |discreteCellResidual c N n| ≤ uniformCellBound c N := by
  rw [discreteCellResidual_eq_modularCellResidual_of_D1_eq_zero c N n hD1]
  exact abs_modularCellResidual_le c N n

/-- Partial L² quadrature tail over harmonic slabs `M + 1 ≤ n ≤ M'`. -/
noncomputable def harmonicCellL2TailSum (c : ℕ → ℝ) (N M M' : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc (M + 1) M', (discreteCellResidual c N n) ^ 2 / ((n : ℝ) * ((n : ℝ) + 1))

/-- Every term of `harmonicCellL2TailSum c N M M'` is non-negative. -/
theorem harmonicCellL2TailSum_nonneg (c : ℕ → ℝ) (N M M' : ℕ) :
    0 ≤ harmonicCellL2TailSum c N M M' := Finset.sum_nonneg fun _ _ => by positivity

/-- **Tail Splitting Identity**: `partialSum M' - partialSum M = tailSum M M'`. -/
theorem harmonicCellL2PartialSum_sub_eq_tailSum (c : ℕ → ℝ) (N : ℕ) {M M' : ℕ}
    (hM : 1 ≤ M) (hMM' : M ≤ M') :
    harmonicCellL2PartialSum c N M' - harmonicCellL2PartialSum c N M =
      harmonicCellL2TailSum c N M M' := by
  have hsplit : Finset.Icc 1 M' = Finset.Icc 1 M ∪ Finset.Icc (M + 1) M' := by
    ext n; simp only [Finset.mem_Icc, Finset.mem_union]; omega
  have hdisj : Disjoint (Finset.Icc 1 M) (Finset.Icc (M + 1) M') :=
    Finset.disjoint_left.mpr fun n h1 h2 => by simp only [Finset.mem_Icc] at h1 h2; omega
  have hcongr : ∑ n ∈ Finset.Icc (M + 1) M',
        (discreteCellResidual c N n) ^ 2 * harmonicCellWidth n =
      harmonicCellL2TailSum c N M M' :=
    Finset.sum_congr rfl fun n _ => by unfold harmonicCellWidth; ring
  unfold harmonicCellL2PartialSum
  rw [hsplit, Finset.sum_union hdisj, hcongr]; ring

/-- **Tail Measure Telescoping**: `∑ n ∈ Icc (M + 1) M', width n = 1 / (M + 1) - 1 / (M' + 1)`. -/
theorem sum_Icc_harmonicCellWidth_tail {M M' : ℕ} (hM : 1 ≤ M) (hMM' : M ≤ M') :
    ∑ n ∈ Finset.Icc (M + 1) M', harmonicCellWidth n =
      1 / ((M : ℝ) + 1) - 1 / ((M' : ℝ) + 1) := by
  rcases eq_or_lt_of_le hMM' with rfl | hlt
  · rw [Finset.Icc_eq_empty (by omega), Finset.sum_empty, sub_self]
  · rcases eq_or_lt_of_le hM with rfl | hM2
    · rw [show (1 : ℕ) + 1 = 2 by rfl, sum_Icc_harmonicCellWidth (by omega : 2 ≤ M')]
      push_cast; ring
    · have hsplit : Finset.Icc 2 M' = Finset.Icc 2 M ∪ Finset.Icc (M + 1) M' := by
        ext n; simp only [Finset.mem_Icc, Finset.mem_union]; omega
      have hdisj : Disjoint (Finset.Icc 2 M) (Finset.Icc (M + 1) M') :=
        Finset.disjoint_left.mpr fun n h1 h2 => by simp only [Finset.mem_Icc] at h1 h2; omega
      have hbig := sum_Icc_harmonicCellWidth (by omega : 2 ≤ M')
      rw [hsplit, Finset.sum_union hdisj, sum_Icc_harmonicCellWidth hM2] at hbig; linarith

/-- For `1 ≤ M ≤ M'`, the tail cell-width sum is at most `1 / (M + 1)`. -/
theorem sum_Icc_harmonicCellWidth_tail_le {M M' : ℕ} (hM : 1 ≤ M) (hMM' : M ≤ M') :
    ∑ n ∈ Finset.Icc (M + 1) M', harmonicCellWidth n ≤ 1 / ((M : ℝ) + 1) := by
  rw [sum_Icc_harmonicCellWidth_tail hM hMM']
  linarith [show (0 : ℝ) ≤ 1 / ((M' : ℝ) + 1) by positivity]

/-- **Euclidean Book X.1 Refined Tail Bound** via `B^2 * (1 / (M + 1) - 1 / (M' + 1))`. -/
theorem harmonicCellL2TailSum_le_mul_sub {c : ℕ → ℝ} {N M M' : ℕ} {B : ℝ} (hM : 1 ≤ M)
    (hMM' : M ≤ M') (hB : 0 ≤ B)
    (hbd : ∀ n ∈ Finset.Icc (M + 1) M', |discreteCellResidual c N n| ≤ B) :
    harmonicCellL2TailSum c N M M' ≤ B ^ 2 * (1 / ((M : ℝ) + 1) - 1 / ((M' : ℝ) + 1)) := by
  unfold harmonicCellL2TailSum
  have hstep : ∑ n ∈ Finset.Icc (M + 1) M',
        (discreteCellResidual c N n) ^ 2 / ((n : ℝ) * ((n : ℝ) + 1)) ≤
      ∑ n ∈ Finset.Icc (M + 1) M', B ^ 2 * harmonicCellWidth n := by
    refine Finset.sum_le_sum fun n hn => ?_
    have hsq : (discreteCellResidual c N n) ^ 2 ≤ B ^ 2 :=
      sq_le_sq.mpr (by rw [abs_of_nonneg hB]; exact hbd n hn)
    have hmul := mul_le_mul_of_nonneg_right hsq
      (show 0 ≤ harmonicCellWidth n by unfold harmonicCellWidth; positivity)
    unfold harmonicCellWidth at hmul ⊢
    linarith [show (discreteCellResidual c N n) ^ 2 / ((n : ℝ) * ((n : ℝ) + 1)) =
      (discreteCellResidual c N n) ^ 2 * (1 / ((n : ℝ) * ((n : ℝ) + 1))) by ring]
  rw [← Finset.mul_sum, sum_Icc_harmonicCellWidth_tail hM hMM'] at hstep; exact hstep

/-- **Euclidean Book X.1 Uniform Tail Bound**: `harmonicCellL2TailSum c N M M' ≤ B^2 / (M + 1)`. -/
theorem harmonicCellL2TailSum_le_div_succ {c : ℕ → ℝ} {N M M' : ℕ} {B : ℝ} (hM : 1 ≤ M)
    (hMM' : M ≤ M') (hB : 0 ≤ B)
    (hbd : ∀ n ∈ Finset.Icc (M + 1) M', |discreteCellResidual c N n| ≤ B) :
    harmonicCellL2TailSum c N M M' ≤ B ^ 2 / ((M : ℝ) + 1) := by
  have h1 := harmonicCellL2TailSum_le_mul_sub hM hMM' hB hbd
  have h2 := mul_le_mul_of_nonneg_left
    (show 1 / ((M : ℝ) + 1) - 1 / ((M' : ℝ) + 1) ≤ 1 / ((M : ℝ) + 1) by
      linarith [show (0 : ℝ) ≤ 1 / ((M' : ℝ) + 1) by positivity]) (sq_nonneg B)
  linarith [show B ^ 2 * (1 / ((M : ℝ) + 1)) = B ^ 2 / ((M : ℝ) + 1) by ring]

/-- **Period-Free Uniform Book X.1 Tail Bound**: on `D1 c N = 0`, for all `1 ≤ M ≤ M'`,
`harmonicCellL2TailSum c N M M' ≤ (uniformCellBound c N)^2 / (M + 1)`. -/
theorem harmonicCellL2TailSum_le_uniformCellBound_sq_div_succ {c : ℕ → ℝ} {N M M' : ℕ}
    (hD1 : D1 c N = 0) (hM : 1 ≤ M) (hMM' : M ≤ M') :
    harmonicCellL2TailSum c N M M' ≤ (uniformCellBound c N) ^ 2 / ((M : ℝ) + 1) :=
  harmonicCellL2TailSum_le_div_succ hM hMM' (uniformCellBound_nonneg c N)
    fun n _ => abs_discreteCellResidual_le_of_D1_eq_zero hD1 n

/-- **Archimedean ε-Exhaustion Criterion**: `B^2 / ε < M + 1` forces tail `< ε`. -/
theorem harmonicCellL2TailSum_lt_eps_of_gt {c : ℕ → ℝ} {N M M' : ℕ} {B ε : ℝ} (hM : 1 ≤ M)
    (hMM' : M ≤ M') (hB : 0 ≤ B) (hε : 0 < ε) (hgt : B ^ 2 / ε < (M : ℝ) + 1)
    (hbd : ∀ n ∈ Finset.Icc (M + 1) M', |discreteCellResidual c N n| ≤ B) :
    harmonicCellL2TailSum c N M M' < ε := by
  have h1 := mul_lt_mul_of_pos_left hgt hε; rw [mul_div_cancel₀ _ hε.ne'] at h1
  exact lt_of_le_of_lt (harmonicCellL2TailSum_le_div_succ hM hMM' hB hbd)
    ((div_lt_iff₀ (by positivity : (0 : ℝ) < (M : ℝ) + 1)).mpr (by linarith))

/-- **Single-Cell Lebesgue Set-Integral Identity**: on `D1 c N = 0`, for every `n ≥ 1`,
`∫ x in Set.Ioc (1 / (n + 1)) (1 / n), (continuousNymanResidual c N x)^2 =
(A_c(n))^2 / (n * (n + 1))`. -/
theorem setIntegral_Ioc_harmonicCell_eq (c : ℕ → ℝ) (N : ℕ) {n : ℕ} (hn : 1 ≤ n)
    (hD1 : D1 c N = 0) :
    ∫ x in Set.Ioc (1 / ((n : ℝ) + 1)) (1 / (n : ℝ)), (continuousNymanResidual c N x) ^ 2 =
      (discreteCellResidual c N n) ^ 2 / ((n : ℝ) * ((n : ℝ) + 1)) := by
  have hle : (1 : ℝ) / ((n : ℝ) + 1) ≤ 1 / (n : ℝ) :=
    one_div_le_one_div_of_le (Nat.cast_pos.mpr hn) (by linarith)
  have heq := continuousNymanResidual_sq_mul_width_eq c N hn hD1
  rw [intervalIntegral.integral_of_le hle] at heq
  rw [heq]; unfold harmonicCellWidth; ring

/-- **Finite-Horizon Lebesgue Set-Integral Bridge**: on `D1 c N = 0`, for all `M ≥ 1`,
`∫ x in Set.Ioc (1 / (M + 1)) 1, (continuousNymanResidual c N x)^2 =
harmonicCellL2PartialSum c N M`. -/
theorem harmonicCellL2PartialSum_eq_setIntegral_Ioc (c : ℕ → ℝ) (N : ℕ) {M : ℕ} (hM : 1 ≤ M)
    (hD1 : D1 c N = 0) :
    ∫ x in Set.Ioc (1 / ((M : ℝ) + 1)) 1, (continuousNymanResidual c N x) ^ 2 =
      harmonicCellL2PartialSum c N M := by
  induction M, hM using Nat.le_induction with
  | base =>
    have h1 := setIntegral_Ioc_harmonicCell_eq c N le_rfl hD1
    simp only [Nat.cast_one, div_one] at h1 ⊢
    rw [h1]; unfold harmonicCellL2PartialSum harmonicCellWidth; simp; ring
  | succ k hk ih =>
    have hf := continuousNymanResidual_sq_integrableOn_Ioc c N
    set a : ℝ := 1 / (((k + 1 : ℕ) : ℝ) + 1)
    set b : ℝ := 1 / ((k + 1 : ℕ) : ℝ)
    have hab : a ≤ b := one_div_le_one_div_of_le (by positivity) (by push_cast; linarith)
    have hb1 : b ≤ 1 := div_le_self zero_le_one (by exact_mod_cast (by omega : 1 ≤ k + 1))
    have hunion : Set.Ioc a 1 = Set.Ioc a b ∪ Set.Ioc b 1 := by
      ext x; simp only [Set.mem_Ioc, Set.mem_union]
      exact ⟨fun hx => if hxb : x ≤ b then Or.inl ⟨hx.1, hxb⟩ else Or.inr ⟨lt_of_not_ge hxb, hx.2⟩,
        fun h => h.elim (fun h => ⟨h.1, h.2.trans hb1⟩) (fun h => ⟨hab.trans_lt h.1, h.2⟩)⟩
    have hdisj : Disjoint (Set.Ioc a b) (Set.Ioc b 1) :=
      Set.disjoint_left.mpr fun x h1 h2 => by linarith [h1.2, h2.1]
    rw [hunion, MeasureTheory.setIntegral_union hdisj measurableSet_Ioc
      (hf.mono_set (Set.Ioc_subset_Ioc (by positivity) hb1))
      (hf.mono_set (Set.Ioc_subset_Ioc (by positivity) le_rfl)),
      setIntegral_Ioc_harmonicCell_eq c N (by omega : 1 ≤ k + 1) hD1,
      show b = 1 / ((k : ℝ) + 1) by dsimp [b]; push_cast; rfl, ih]
    unfold harmonicCellL2PartialSum
    rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ k + 1)]
    unfold harmonicCellWidth; push_cast; ring

/-- **Global Lebesgue Monotonicity Lower Bound**: on `D1 c N = 0` (`M ≥ 1`),
`harmonicCellL2PartialSum c N M ≤ ∫ x in Set.Ioc 0 1, (continuousNymanResidual c N x)^2`. -/
theorem harmonicCellL2PartialSum_le_integral_Ioc (c : ℕ → ℝ) (N : ℕ) {M : ℕ} (hM : 1 ≤ M)
    (hD1 : D1 c N = 0) :
    harmonicCellL2PartialSum c N M ≤
      ∫ x in Set.Ioc (0 : ℝ) 1, (continuousNymanResidual c N x) ^ 2 := by
  rw [← harmonicCellL2PartialSum_eq_setIntegral_Ioc c N hM hD1]
  exact MeasureTheory.setIntegral_mono_set (continuousNymanResidual_sq_integrableOn_Ioc c N)
    (Filter.Eventually.of_forall fun x => sq_nonneg (continuousNymanResidual c N x))
    (Filter.Eventually.of_forall fun _ hx => Set.Ioc_subset_Ioc (by positivity) le_rfl hx)

/-- **Full-Interval Multi-Prime Lebesgue Lower Floor**: under `IsDirichletAnchored c N` (`N ≥ 2`),
`∑ p ∈ S, 1 / (2 * p^2) ≤ ∫ x in Set.Ioc 0 1, (continuousNymanResidual c N x)^2`. -/
theorem sum_primes_le_integral_Ioc {c : ℕ → ℝ} {N M : ℕ} (hN : 2 ≤ N) (hM : 1 ≤ M)
    (hc : IsDirichletAnchored c N) {S : Finset ℕ} (hS : S ⊆ Finset.Icc (N + 1) M)
    (hp : ∀ p ∈ S, Nat.Prime p) :
    ∑ p ∈ S, (1 : ℝ) / (2 * (p : ℝ) ^ 2) ≤
      ∫ x in Set.Ioc (0 : ℝ) 1, (continuousNymanResidual c N x) ^ 2 :=
  (harmonicCellL2PartialSum_ge_sum_primes hN hc hS hp).trans
    (harmonicCellL2PartialSum_le_integral_Ioc c N hM hc.1)

/-- **Dual Book IX.20 / Book X.1 Continuity Capstone**: unifies Book IX.20 multi-prime `L²`
lower floor, double-cone `L²` folding, and Book X.1 `B^2 / (M + 1)` tail exhaustion. -/
theorem euclidean_book_ix_and_x_continuity_capstone {c : ℕ → ℝ} {N : ℕ} (hN : 2 ≤ N)
    (hc : IsDirichletAnchored c N) :
    (∀ (M : ℕ) (S : Finset ℕ), S ⊆ Finset.Icc (N + 1) M → (∀ p ∈ S, Nat.Prime p) →
      ∑ p ∈ S, (1 : ℝ) / (2 * (p : ℝ) ^ 2) ≤ harmonicCellL2PartialSum c N M) ∧
    (∀ (L : ℕ), (∀ k ∈ Finset.Icc 1 N, k ∣ L) → harmonicCellL2PartialSum c N (L - 2) =
      ∑ m ∈ Finset.Icc 1 (L - 2),
        (modularCellResidual c N m) ^ 2 * doubleConeSymmetricWidth L m) ∧
    (∀ {M M' : ℕ} {B : ℝ}, 1 ≤ M → M ≤ M' → 0 ≤ B →
      (∀ n ∈ Finset.Icc (M + 1) M', |discreteCellResidual c N n| ≤ B) →
      harmonicCellL2PartialSum c N M' - harmonicCellL2PartialSum c N M ≤
        B ^ 2 / ((M : ℝ) + 1)) := by
  refine ⟨fun M S hS hp => harmonicCellL2PartialSum_ge_sum_primes hN hc hS hp,
    fun L hL => harmonicCellL2PartialSum_period_sub_two_eq_doubleCone c N L hc.1 hc.2.1 hL,
    fun hM hMM' hB hbd => by
      rw [harmonicCellL2PartialSum_sub_eq_tailSum c N hM hMM']
      exact harmonicCellL2TailSum_le_div_succ hM hMM' hB hbd⟩
