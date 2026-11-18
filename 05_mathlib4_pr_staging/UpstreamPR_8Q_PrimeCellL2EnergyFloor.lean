/-
Copyright (c) 2026 Qamar Munawer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qamar Munawer
-/
module

public import RiemannBlueprint.UpstreamPRs.UpstreamPR_8P_HarmonicSlabNonTermination

/-!
# Exact Prime-Cell L² Energy Identity and Quantitative Prime-Harmonic Tail Floor

This module establishes the exact adjacent harmonic-cell Cauchy–Schwarz defect identity and derives
an explicit quantitative `1 / (2 * p^2)` lower bound on each prime cell pair `{p - 1, p}` for all
primes `p > N`:

* `harmonicPairEnergy`: total `L²` quadrature energy contributed by cells `p - 1` and `p`.
* `adjacentCellEnergy_eq_jump_sq_add_defect`, `harmonicPairEnergy_eq_jump_sq_add_defect`:
  exact algebraic decomposition of `a^2 / ((p - 1) * p) + b^2 / (p * (p + 1))` into
  `(b - a)^2 / (2 * p^2)` plus an explicit non-negative defect square.
* `harmonicPairEnergy_prime_eq`, `harmonicPairEnergy_prime_ge_c_one_sq`: exact `L²` prime quantum
  using the prime-jump identity `discreteCellResidual_prime_sub_pred` (`p > N`).
* `harmonicPairEnergy_prime_ge_inv_two_sq_of_anchored`,
  `harmonicCellL2PartialSum_ge_inv_two_prime_sq`, `harmonicCellL2PartialSum_ge_add_two_primes`:
  `1 / (2 * p^2)` and two-prime disjoint tail floors for `harmonicCellL2PartialSum` under
  `IsDirichletAnchored`.
-/

@[expose] public section

open scoped BigOperators
open Finset

/-- Total L² harmonic-cell energy contributed by adjacent cells `p - 1` and `p`. -/
noncomputable def harmonicPairEnergy (c : ℕ → ℝ) (N p : ℕ) : ℝ :=
  (discreteCellResidual c N (p - 1)) ^ 2 / (((p - 1 : ℕ) : ℝ) * (p : ℝ)) +
    (discreteCellResidual c N p) ^ 2 / ((p : ℝ) * ((p : ℝ) + 1))

/-- Rewriting `harmonicPairEnergy c N p` directly in terms of `harmonicCellWidth` for `p ≥ 2`. -/
theorem harmonicPairEnergy_eq_width_sum (c : ℕ → ℝ) (N : ℕ) {p : ℕ} (hp : 2 ≤ p) :
    harmonicPairEnergy c N p =
      (discreteCellResidual c N (p - 1)) ^ 2 * harmonicCellWidth (p - 1) +
        (discreteCellResidual c N p) ^ 2 * harmonicCellWidth p := by
  have hp1 : 1 ≤ p := by omega
  have hsub : ((p - 1 : ℕ) : ℝ) + 1 = (p : ℝ) := by
    rw [Nat.cast_sub hp1, Nat.cast_one]; ring
  unfold harmonicPairEnergy harmonicCellWidth
  rw [hsub]
  simp only [div_eq_mul_inv, one_mul]

/-- Non-negative Cauchy-Schwarz defect of the adjacent harmonic cells `p - 1` and `p`. -/
noncomputable def harmonicPairDefect (c : ℕ → ℝ) (N p : ℕ) : ℝ :=
  ((((p : ℝ) + 1) * discreteCellResidual c N (p - 1) +
      ((p : ℝ) - 1) * discreteCellResidual c N p) ^ 2) /
    (2 * (p : ℝ) ^ 2 * ((p : ℝ) - 1) * ((p : ℝ) + 1))

/-- The Cauchy-Schwarz defect `harmonicPairDefect c N p` is non-negative for `p ≥ 2`. -/
theorem harmonicPairDefect_nonneg (c : ℕ → ℝ) (N : ℕ) {p : ℕ} (hp : 2 ≤ p) :
    0 ≤ harmonicPairDefect c N p := by
  have hpR : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have h1 : 0 ≤ (p : ℝ) - 1 := by linarith
  unfold harmonicPairDefect
  exact div_nonneg (sq_nonneg _) (by positivity)

/-- **Exact Adjacent-Cell Defect Identity**: for any real `a, b` and `p ≥ 2`,
`a^2 / ((p - 1) * p) + b^2 / (p * (p + 1))` splits orthogonally into `(b - a)^2 / (2 * p^2)`
plus a non-negative defect square. -/
theorem sq_div_pred_mul_add_sq_div_mul_succ (a b : ℝ) {p : ℕ} (hp : 2 ≤ p) :
    a ^ 2 / (((p - 1 : ℕ) : ℝ) * (p : ℝ)) + b ^ 2 / ((p : ℝ) * ((p : ℝ) + 1)) =
      (b - a) ^ 2 / (2 * (p : ℝ) ^ 2) +
        (((p : ℝ) + 1) * a + ((p : ℝ) - 1) * b) ^ 2 /
          (2 * (p : ℝ) ^ 2 * ((p : ℝ) - 1) * ((p : ℝ) + 1)) := by
  have hp1 : 1 ≤ p := by omega
  have hcast : ((p - 1 : ℕ) : ℝ) = (p : ℝ) - 1 := by rw [Nat.cast_sub hp1, Nat.cast_one]
  have hpR : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have hp0 : (p : ℝ) ≠ 0 := by linarith
  have hpm1 : (p : ℝ) - 1 ≠ 0 := by linarith
  have hpp1 : (p : ℝ) + 1 ≠ 0 := by linarith
  rw [hcast]
  field_simp [hp0, hpm1, hpp1]
  ring

/-- Alias of `sq_div_pred_mul_add_sq_div_mul_succ` for compatibility. -/
theorem adjacentCellEnergy_eq_jump_sq_add_defect (a b : ℝ) {p : ℕ} (hp : 2 ≤ p) :
    a ^ 2 / (((p - 1 : ℕ) : ℝ) * (p : ℝ)) + b ^ 2 / ((p : ℝ) * ((p : ℝ) + 1)) =
      (b - a) ^ 2 / (2 * (p : ℝ) ^ 2) +
        (((p : ℝ) + 1) * a + ((p : ℝ) - 1) * b) ^ 2 /
          (2 * (p : ℝ) ^ 2 * ((p : ℝ) - 1) * ((p : ℝ) + 1)) :=
  sq_div_pred_mul_add_sq_div_mul_succ a b hp

/-- General lower bound `a^2 / ((p - 1) * p) + b^2 / (p * (p + 1)) ≥ (b - a)^2 / (2 * p^2)` for
all real `a, b` and `p ≥ 2`. -/
theorem adjacentCellEnergy_ge_jump_sq_div_two_sq (a b : ℝ) {p : ℕ} (hp : 2 ≤ p) :
    (b - a) ^ 2 / (2 * (p : ℝ) ^ 2) ≤
      a ^ 2 / (((p - 1 : ℕ) : ℝ) * (p : ℝ)) + b ^ 2 / ((p : ℝ) * ((p : ℝ) + 1)) := by
  have hpR : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have hdef : 0 ≤ (((p : ℝ) + 1) * a + ((p : ℝ) - 1) * b) ^ 2 /
      (2 * (p : ℝ) ^ 2 * ((p : ℝ) - 1) * ((p : ℝ) + 1)) := by
    refine div_nonneg (sq_nonneg _) ?_
    have h1 : 0 ≤ (p : ℝ) - 1 := by linarith
    positivity
  linarith [adjacentCellEnergy_eq_jump_sq_add_defect a b hp]

/-- Exact defect identity specialized to `harmonicPairEnergy c N p` (`2 ≤ p`). -/
theorem harmonicPairEnergy_eq_jump_sq_add_defect (c : ℕ → ℝ) (N : ℕ) {p : ℕ} (hp : 2 ≤ p) :
    harmonicPairEnergy c N p =
      (discreteCellResidual c N p - discreteCellResidual c N (p - 1)) ^ 2 /
          (2 * (p : ℝ) ^ 2) +
        (((p : ℝ) + 1) * discreteCellResidual c N (p - 1) +
            ((p : ℝ) - 1) * discreteCellResidual c N p) ^ 2 /
          (2 * (p : ℝ) ^ 2 * ((p : ℝ) - 1) * ((p : ℝ) + 1)) :=
  adjacentCellEnergy_eq_jump_sq_add_defect
    (discreteCellResidual c N (p - 1)) (discreteCellResidual c N p) hp

/-- Lower bound on `harmonicPairEnergy c N p` by the squared step jump divided by `2 * p^2`. -/
theorem harmonicPairEnergy_ge_jump_sq_div_two_sq (c : ℕ → ℝ) (N : ℕ) {p : ℕ} (hp : 2 ≤ p) :
    (discreteCellResidual c N p - discreteCellResidual c N (p - 1)) ^ 2 / (2 * (p : ℝ) ^ 2) ≤
      harmonicPairEnergy c N p :=
  adjacentCellEnergy_ge_jump_sq_div_two_sq
    (discreteCellResidual c N (p - 1)) (discreteCellResidual c N p) hp

/-- **Exact Prime-Jump L² Energy Identity**: for every prime `p > N` (`1 ≤ N`),
`harmonicPairEnergy c N p` equals `(c 1)^2 / (2 * p^2)` plus the non-negative defect square. -/
theorem harmonicPairEnergy_prime_eq (c : ℕ → ℝ) {N p : ℕ} (hN : 1 ≤ N)
    (hp : Nat.Prime p) (hpN : N < p) :
    harmonicPairEnergy c N p =
      (c 1) ^ 2 / (2 * (p : ℝ) ^ 2) +
        (((p : ℝ) + 1) * discreteCellResidual c N (p - 1) +
            ((p : ℝ) - 1) * discreteCellResidual c N p) ^ 2 /
          (2 * (p : ℝ) ^ 2 * ((p : ℝ) - 1) * ((p : ℝ) + 1)) := by
  rw [harmonicPairEnergy_eq_jump_sq_add_defect c N hp.two_le,
    discreteCellResidual_prime_sub_pred c hN hp hpN]

/-- Quantitative prime-pair energy floor `(c 1)^2 / (2 * p^2) ≤ harmonicPairEnergy c N p` for
every prime `p > N` (`1 ≤ N`). -/
theorem harmonicPairEnergy_prime_ge_c_one_sq (c : ℕ → ℝ) {N p : ℕ} (hN : 1 ≤ N)
    (hp : Nat.Prime p) (hpN : N < p) :
    (c 1) ^ 2 / (2 * (p : ℝ) ^ 2) ≤ harmonicPairEnergy c N p := by
  have := harmonicPairEnergy_ge_jump_sq_div_two_sq c N hp.two_le
  rwa [discreteCellResidual_prime_sub_pred c hN hp hpN] at this

/-- Under `IsDirichletAnchored c N` (`c 1 = -1`), every prime `p > N` contributes at least
`1 / (2 * p^2) > 0` to `harmonicPairEnergy c N p`. -/
theorem harmonicPairEnergy_prime_ge_inv_two_sq_of_anchored {c : ℕ → ℝ} {N p : ℕ} (hN : 1 ≤ N)
    (hc : IsDirichletAnchored c N) (hp : Nat.Prime p) (hpN : N < p) :
    0 < 1 / (2 * (p : ℝ) ^ 2) ∧ 1 / (2 * (p : ℝ) ^ 2) ≤ harmonicPairEnergy c N p := by
  have hp_pos : (0 : ℝ) < (p : ℝ) := Nat.cast_pos.mpr hp.pos
  have hge := harmonicPairEnergy_prime_ge_c_one_sq c hN hp hpN
  rw [hc.2.2, neg_sq, one_pow] at hge
  exact ⟨by positivity, hge⟩

private lemma harmonicCellWidth_nonneg (n : ℕ) : 0 ≤ harmonicCellWidth n := by
  unfold harmonicCellWidth; positivity

/-- For any `p` with `2 ≤ p ≤ M`, `harmonicPairEnergy c N p ≤ harmonicCellL2PartialSum c N M`. -/
theorem harmonicPairEnergy_le_harmonicCellL2PartialSum (c : ℕ → ℝ) (N : ℕ) {p M : ℕ}
    (hp : 2 ≤ p) (hpM : p ≤ M) :
    harmonicPairEnergy c N p ≤ harmonicCellL2PartialSum c N M := by
  have hpair : ({p - 1, p} : Finset ℕ) ⊆ Finset.Icc 1 M := by
    intro n hn
    simp only [Finset.mem_insert, Finset.mem_singleton] at hn
    simp only [Finset.mem_Icc]
    rcases hn with rfl | rfl <;> omega
  have hsum := Finset.sum_le_sum_of_subset_of_nonneg hpair (f := fun n =>
      (discreteCellResidual c N n) ^ 2 * harmonicCellWidth n)
    (fun n _ _ => mul_nonneg (sq_nonneg _) (harmonicCellWidth_nonneg n))
  have hne : p - 1 ≠ p := by omega
  rw [Finset.sum_pair hne, ← harmonicPairEnergy_eq_width_sum c N hp] at hsum
  exact hsum

/-- **Quantitative Prime-Harmonic Tail Floor**: under `IsDirichletAnchored c N`, every prime
`p` with `N < p ≤ M` (`1 ≤ N`) forces `harmonicCellL2PartialSum c N M ≥ harmonicPairEnergy c N p ≥
1 / (2 * p^2)`. -/
theorem harmonicCellL2PartialSum_ge_inv_two_prime_sq {c : ℕ → ℝ} {N p M : ℕ} (hN : 1 ≤ N)
    (hc : IsDirichletAnchored c N) (hp : Nat.Prime p) (hpN : N < p) (hpM : p ≤ M) :
    1 / (2 * (p : ℝ) ^ 2) ≤ harmonicPairEnergy c N p ∧
      harmonicPairEnergy c N p ≤ harmonicCellL2PartialSum c N M :=
  ⟨(harmonicPairEnergy_prime_ge_inv_two_sq_of_anchored hN hc hp hpN).2,
    harmonicPairEnergy_le_harmonicCellL2PartialSum c N hp.two_le hpM⟩

/-- **Disjoint Two-Prime Superposition Bound**: for any two primes `p, q` satisfying `N < p`,
`p + 2 ≤ q`, and `q ≤ M` under `IsDirichletAnchored c N`, the four cells `{p - 1, p, q - 1, q}`
are pairwise distinct in `Icc 1 M`, yielding `1 / (2 * p^2) + 1 / (2 * q^2) ≤
harmonicCellL2PartialSum c N M`. -/
theorem harmonicCellL2PartialSum_ge_add_two_primes {c : ℕ → ℝ} {N p q M : ℕ} (hN : 1 ≤ N)
    (hc : IsDirichletAnchored c N) (hp : Nat.Prime p) (hq : Nat.Prime q)
    (hpN : N < p) (hpq : p + 2 ≤ q) (hqM : q ≤ M) :
    1 / (2 * (p : ℝ) ^ 2) + 1 / (2 * (q : ℝ) ^ 2) ≤ harmonicCellL2PartialSum c N M := by
  have hp2 : 2 ≤ p := hp.two_le
  have hq2 : 2 ≤ q := hq.two_le
  have hsub : ({p - 1, p} ∪ {q - 1, q} : Finset ℕ) ⊆ Finset.Icc 1 M := by
    intro n hn
    simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at hn
    simp only [Finset.mem_Icc]
    rcases hn with (rfl | rfl) | (rfl | rfl) <;> omega
  have hdisj : Disjoint ({p - 1, p} : Finset ℕ) {q - 1, q} := by
    rw [Finset.disjoint_left]
    intro x hx1 hx2
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx1 hx2
    rcases hx1 with rfl | rfl <;> rcases hx2 with h1 | h2 <;> omega
  have hsum := Finset.sum_le_sum_of_subset_of_nonneg hsub (f := fun n =>
      (discreteCellResidual c N n) ^ 2 * harmonicCellWidth n)
    (fun n _ _ => mul_nonneg (sq_nonneg _) (harmonicCellWidth_nonneg n))
  rw [Finset.sum_union hdisj, Finset.sum_pair (by omega : p - 1 ≠ p),
    Finset.sum_pair (by omega : q - 1 ≠ q), ← harmonicPairEnergy_eq_width_sum c N hp2,
    ← harmonicPairEnergy_eq_width_sum c N hq2] at hsum
  have hfp := (harmonicPairEnergy_prime_ge_inv_two_sq_of_anchored hN hc hp hpN).2
  have hfq := (harmonicPairEnergy_prime_ge_inv_two_sq_of_anchored hN hc hq
    (by omega : N < q)).2
  exact le_trans (add_le_add hfp hfq) hsum
