/-
Copyright (c) 2026 Qamar Munawer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qamar Munawer
-/
module

public import RiemannBlueprint.UpstreamPRs.UpstreamPR_8T_DoubleConeL2FoldingAndFlux

/-!
# Euclidean Book X.1 L² Tail Exhaustion Bound and Dual Book IX.20 / Book X.1 Capstone

Complementing the Book IX.20 multi-prime lower floor (`UpstreamPR_8S`) and double-cone folding
(`UpstreamPR_8T`), this module proves the Euclidean Book X.1 method-of-exhaustion upper bound on
the unexhausted L² tail between harmonic horizons `M` and `M'`:

* `harmonicCellL2TailSum`, `harmonicCellL2TailSum_nonneg`,
  `harmonicCellL2PartialSum_sub_eq_tailSum`: exact partial L² difference identity
  `harmonicCellL2PartialSum c N M' - harmonicCellL2PartialSum c N M =
  harmonicCellL2TailSum c N M M'` for `1 ≤ M ≤ M'`.
* `sum_Icc_harmonicCellWidth_tail`, `sum_Icc_harmonicCellWidth_tail_le`: exact measure
  telescoping `1 / (M + 1) - 1 / (M' + 1) ≤ 1 / (M + 1)`.
* `harmonicCellL2TailSum_le_mul_sub`, `harmonicCellL2TailSum_le_div_succ`,
  `harmonicCellL2TailSum_lt_eps_of_gt`: uniform `B^2 / (M + 1)` tail bound and `< ε` exhaustion
  when `B^2 / ε < M + 1`.
* `euclidean_book_ix_and_x_continuity_capstone`: unifies Book IX.20 multi-prime lower floor,
  double-cone palindromic L² folding, and Book X.1 upper tail exhaustion.
-/

@[expose] public section

open scoped BigOperators

private lemma harmonicCellWidth_nonneg_8u (n : ℕ) : 0 ≤ harmonicCellWidth n := by
  unfold harmonicCellWidth; positivity

/-- Partial L² quadrature tail over harmonic slabs `M + 1 ≤ n ≤ M'`. -/
noncomputable def harmonicCellL2TailSum (c : ℕ → ℝ) (N M M' : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc (M + 1) M', (discreteCellResidual c N n) ^ 2 / ((n : ℝ) * ((n : ℝ) + 1))

/-- Every term of `harmonicCellL2TailSum c N M M'` is non-negative. -/
theorem harmonicCellL2TailSum_nonneg (c : ℕ → ℝ) (N M M' : ℕ) :
    0 ≤ harmonicCellL2TailSum c N M M' := by
  unfold harmonicCellL2TailSum
  exact Finset.sum_nonneg fun n _ => by positivity

/-- **Tail Splitting Identity**: for `1 ≤ M ≤ M'`,
`harmonicCellL2PartialSum c N M' - harmonicCellL2PartialSum c N M =
harmonicCellL2TailSum c N M M'`. -/
theorem harmonicCellL2PartialSum_sub_eq_tailSum (c : ℕ → ℝ) (N : ℕ) {M M' : ℕ}
    (hM : 1 ≤ M) (hMM' : M ≤ M') :
    harmonicCellL2PartialSum c N M' - harmonicCellL2PartialSum c N M =
      harmonicCellL2TailSum c N M M' := by
  have hsplit : Finset.Icc 1 M' = Finset.Icc 1 M ∪ Finset.Icc (M + 1) M' := by
    ext n; simp only [Finset.mem_Icc, Finset.mem_union]; omega
  have hdisj : Disjoint (Finset.Icc 1 M) (Finset.Icc (M + 1) M') := by
    rw [Finset.disjoint_left]
    intro n hn1 hn2
    simp only [Finset.mem_Icc] at hn1 hn2
    omega
  have hterm : ∀ n : ℕ, (discreteCellResidual c N n) ^ 2 * harmonicCellWidth n =
      (discreteCellResidual c N n) ^ 2 / ((n : ℝ) * ((n : ℝ) + 1)) := fun n => by
    unfold harmonicCellWidth; ring
  unfold harmonicCellL2PartialSum harmonicCellL2TailSum
  rw [hsplit, Finset.sum_union hdisj]
  have hcongr :
      ∑ n ∈ Finset.Icc (M + 1) M', (discreteCellResidual c N n) ^ 2 * harmonicCellWidth n =
      ∑ n ∈ Finset.Icc (M + 1) M', (discreteCellResidual c N n) ^ 2 / ((n : ℝ) * ((n : ℝ) + 1)) :=
    Finset.sum_congr rfl fun n _ => hterm n
  rw [hcongr]
  ring

/-- **Tail Measure Telescoping**: for `1 ≤ M ≤ M'`,
`∑ n ∈ Icc (M + 1) M', harmonicCellWidth n = 1 / (M + 1) - 1 / (M' + 1)`. -/
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
      have hdisj : Disjoint (Finset.Icc 2 M) (Finset.Icc (M + 1) M') := by
        rw [Finset.disjoint_left]
        intro n hn1 hn2
        simp only [Finset.mem_Icc] at hn1 hn2
        omega
      have hbig := sum_Icc_harmonicCellWidth (by omega : 2 ≤ M')
      have hsmall := sum_Icc_harmonicCellWidth hM2
      rw [hsplit, Finset.sum_union hdisj, hsmall] at hbig
      linarith

/-- For `1 ≤ M ≤ M'`, the tail cell-width sum is at most `1 / (M + 1)`. -/
theorem sum_Icc_harmonicCellWidth_tail_le {M M' : ℕ} (hM : 1 ≤ M) (hMM' : M ≤ M') :
    ∑ n ∈ Finset.Icc (M + 1) M', harmonicCellWidth n ≤ 1 / ((M : ℝ) + 1) := by
  rw [sum_Icc_harmonicCellWidth_tail hM hMM']
  have hpos : (0 : ℝ) ≤ 1 / ((M' : ℝ) + 1) := by positivity
  linarith

/-- **Euclidean Book X.1 Refined Tail Bound**: if `|discreteCellResidual c N n| ≤ B` on
`Icc (M + 1) M'` (`0 ≤ B`, `1 ≤ M ≤ M'`), then
`harmonicCellL2TailSum c N M M' ≤ B^2 * (1 / (M + 1) - 1 / (M' + 1))`. -/
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
    have hw : 0 ≤ harmonicCellWidth n := harmonicCellWidth_nonneg_8u n
    have hmul := mul_le_mul_of_nonneg_right hsq hw
    unfold harmonicCellWidth at hmul ⊢
    linarith [show (discreteCellResidual c N n) ^ 2 / ((n : ℝ) * ((n : ℝ) + 1)) =
      (discreteCellResidual c N n) ^ 2 * (1 / ((n : ℝ) * ((n : ℝ) + 1))) by ring]
  rw [← Finset.mul_sum, sum_Icc_harmonicCellWidth_tail hM hMM'] at hstep
  exact hstep

/-- **Euclidean Book X.1 Uniform Tail Bound**: under `|discreteCellResidual c N n| ≤ B` on
`Icc (M + 1) M'` (`0 ≤ B`, `1 ≤ M ≤ M'`), `harmonicCellL2TailSum c N M M' ≤ B^2 / (M + 1)`. -/
theorem harmonicCellL2TailSum_le_div_succ {c : ℕ → ℝ} {N M M' : ℕ} {B : ℝ} (hM : 1 ≤ M)
    (hMM' : M ≤ M') (hB : 0 ≤ B)
    (hbd : ∀ n ∈ Finset.Icc (M + 1) M', |discreteCellResidual c N n| ≤ B) :
    harmonicCellL2TailSum c N M M' ≤ B ^ 2 / ((M : ℝ) + 1) := by
  have h1 := harmonicCellL2TailSum_le_mul_sub hM hMM' hB hbd
  have hsub : 1 / ((M : ℝ) + 1) - 1 / ((M' : ℝ) + 1) ≤ 1 / ((M : ℝ) + 1) := by
    have hpos : (0 : ℝ) ≤ 1 / ((M' : ℝ) + 1) := by positivity
    linarith
  have h2 : B ^ 2 * (1 / ((M : ℝ) + 1) - 1 / ((M' : ℝ) + 1)) ≤ B ^ 2 * (1 / ((M : ℝ) + 1)) :=
    mul_le_mul_of_nonneg_left hsub (sq_nonneg B)
  calc harmonicCellL2TailSum c N M M' ≤ B ^ 2 * (1 / ((M : ℝ) + 1)) := le_trans h1 h2
    _ = B ^ 2 / ((M : ℝ) + 1) := by ring

/-- **Archimedean ε-Exhaustion Criterion**: for every `ε > 0`, choosing `M` with
`B^2 / ε < M + 1` forces `harmonicCellL2TailSum c N M M' < ε` for all `M' ≥ M`. -/
theorem harmonicCellL2TailSum_lt_eps_of_gt {c : ℕ → ℝ} {N M M' : ℕ} {B ε : ℝ} (hM : 1 ≤ M)
    (hMM' : M ≤ M') (hB : 0 ≤ B) (hε : 0 < ε) (hgt : B ^ 2 / ε < (M : ℝ) + 1)
    (hbd : ∀ n ∈ Finset.Icc (M + 1) M', |discreteCellResidual c N n| ≤ B) :
    harmonicCellL2TailSum c N M M' < ε := by
  have hle := harmonicCellL2TailSum_le_div_succ hM hMM' hB hbd
  have hMpos : (0 : ℝ) < (M : ℝ) + 1 := by positivity
  have hmul : B ^ 2 < ε * ((M : ℝ) + 1) := by
    have h1 := mul_lt_mul_of_pos_left hgt hε
    rwa [mul_div_cancel₀ _ hε.ne'] at h1
  have hdiv : B ^ 2 / ((M : ℝ) + 1) < ε := (div_lt_iff₀ hMpos).mpr (by linarith)
  exact lt_of_le_of_lt hle hdiv

/-- **Dual Book IX.20 / Book X.1 Continuity Capstone**: for `N ≥ 2` and
`IsDirichletAnchored c N`, unifies (1) the Book IX.20 multi-prime `L²` lower floor,
(2) palindromic double-cone `L²` quadrature folding across `[1, L - 2]`, and (3) the Book X.1
`B^2 / (M + 1)` upper tail exhaustion bound between horizons `M ≤ M'`. -/
theorem euclidean_book_ix_and_x_continuity_capstone {c : ℕ → ℝ} {N : ℕ} (hN : 2 ≤ N)
    (hc : IsDirichletAnchored c N) :
    (∀ (M : ℕ) (S : Finset ℕ), S ⊆ Finset.Icc (N + 1) M → (∀ p ∈ S, Nat.Prime p) →
      ∑ p ∈ S, (1 : ℝ) / (2 * (p : ℝ) ^ 2) ≤ harmonicCellL2PartialSum c N M) ∧
    (∀ (L : ℕ), (∀ k ∈ Finset.Icc 1 N, k ∣ L) →
      harmonicCellL2PartialSum c N (L - 2) =
        ∑ m ∈ Finset.Icc 1 (L - 2),
          (modularCellResidual c N m) ^ 2 * doubleConeSymmetricWidth L m) ∧
    (∀ {M M' : ℕ} {B : ℝ}, 1 ≤ M → M ≤ M' → 0 ≤ B →
      (∀ n ∈ Finset.Icc (M + 1) M', |discreteCellResidual c N n| ≤ B) →
      harmonicCellL2PartialSum c N M' - harmonicCellL2PartialSum c N M ≤
        B ^ 2 / ((M : ℝ) + 1)) := by
  refine ⟨fun M S hS hp => harmonicCellL2PartialSum_ge_sum_primes hN hc hS hp,
    fun L hL => harmonicCellL2PartialSum_period_sub_two_eq_doubleCone c N L hc.1 hc.2.1 hL, ?_⟩
  intro M M' B hM hMM' hB hbd
  rw [harmonicCellL2PartialSum_sub_eq_tailSum c N hM hMM']
  exact harmonicCellL2TailSum_le_div_succ hM hMM' hB hbd
