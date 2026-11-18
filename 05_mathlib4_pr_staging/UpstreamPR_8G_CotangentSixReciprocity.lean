/-
Copyright (c) 2026 Qamar Munawer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qamar Munawer
-/
module

public import RiemannBlueprint.UpstreamPRs.UpstreamPR_8F_DipoleGramFiveCert

/-!
# Exact `N = 6` Vasyunin Sums in `ℚ(√3)`, `K(3, 6) = 0`, and `N = 6` Decoupling `G₂₄ = 0`

This module evaluates the `a = 6` Vasyunin cotangent row in `ℚ(√3)`, establishes divisibility
vanishing along the `k = 6` kernel column (`K(3, 6) = 0`), proves horizontal telescoping of
`dipoleGramEntry`, and deduces complete decoupling `dipoleGramEntry 2 4 = 0`:

* `vasyuninCotSum_six_eval` & `deltaCot_six_eq`: exact `ℚ(√3)` values at denominator `6`.
* `vasyuninCotSum_two_six_eq_zero`, `vasyuninCotSum_three_six_eq_zero`,
  `vasyuninCotSum_four_six_eq_zero`, `unweightedKCot_two_six_eq`,
  `unweightedKCot_three_six_eq_zero`, `unweightedKCot_four_six_eq`: `k = 6` vanishing & values.
* `dipoleGramEntry_add_succ_right`, `dipoleGramEntry_one_three_add_one_four_eq`,
  `dipoleGramEntry_one_four_eq`, `dipoleGramEntry_two_four_eq_zero`: horizontal telescoping and
  complete `N = 6` decoupling of the second cumulative dipole.
-/

@[expose] public section

open scoped BigOperators

private lemma cot_pi_div_six_six :
    Real.cos (Real.pi / 6) / Real.sin (Real.pi / 6) = Real.sqrt 3 := by
  rw [Real.cos_pi_div_six, Real.sin_pi_div_six]; ring

private lemma cot_pi_div_three_six :
    Real.cos (Real.pi / 3) / Real.sin (Real.pi / 3) = 1 / Real.sqrt 3 := by
  rw [Real.cos_pi_div_three, Real.sin_pi_div_three]
  field_simp [(Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 3)).ne']

private lemma cot_pi_div_four_six :
    Real.cos (Real.pi / 4) / Real.sin (Real.pi / 4) = 1 := by
  rw [Real.cos_pi_div_four, Real.sin_pi_div_four]
  field_simp [(Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)).ne']

private lemma vasyuninCotSum_two_six_aux (b : ℕ) : vasyuninCotSum 2 b = 0 := by
  unfold vasyuninCotSum
  rw [show Finset.Ico 1 2 = ({1} : Finset ℕ) by ext x; simp, Finset.sum_singleton,
    show Real.pi * ((1 : ℕ) : ℝ) / ((2 : ℕ) : ℝ) = Real.pi / 2 by push_cast; ring,
    Real.cos_pi_div_two, zero_div, mul_zero]

private lemma vasyuninCotSum_three_six_aux (b : ℕ) :
    vasyuninCotSum 3 b =
      (Int.fract ((b : ℝ) / 3) - Int.fract (2 * (b : ℝ) / 3)) * (1 / Real.sqrt 3) := by
  have hc2 : Real.cos (2 * Real.pi / 3) / Real.sin (2 * Real.pi / 3) = -(1 / Real.sqrt 3) := by
    rw [show 2 * Real.pi / 3 = Real.pi - Real.pi / 3 by ring, Real.cos_pi_sub, Real.sin_pi_sub,
      neg_div, cot_pi_div_three_six]
  unfold vasyuninCotSum
  rw [show Finset.Ico 1 3 = ({1, 2} : Finset ℕ) by ext x; simp; omega,
    Finset.sum_insert (by decide), Finset.sum_singleton]
  push_cast
  rw [show (1 : ℝ) * b / 3 = b / 3 by ring, show Real.pi * 1 / 3 = Real.pi / 3 by ring,
    show Real.pi * 2 / 3 = 2 * Real.pi / 3 by ring, cot_pi_div_three_six, hc2]
  ring

private lemma vasyuninCotSum_four_six_aux (b : ℕ) :
    vasyuninCotSum 4 b = Int.fract ((b : ℝ) / 4) - Int.fract (3 * (b : ℝ) / 4) := by
  have hc3 : Real.cos (3 * Real.pi / 4) / Real.sin (3 * Real.pi / 4) = -1 := by
    rw [show 3 * Real.pi / 4 = Real.pi - Real.pi / 4 by ring, Real.cos_pi_sub, Real.sin_pi_sub,
      neg_div, cot_pi_div_four_six]
  unfold vasyuninCotSum
  rw [show Finset.Ico 1 4 = ({1, 2, 3} : Finset ℕ) by ext x; simp; omega,
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  push_cast
  rw [show (1 : ℝ) * b / 4 = b / 4 by ring, show Real.pi * 1 / 4 = Real.pi / 4 by ring,
    show Real.pi * 2 / 4 = Real.pi / 2 by ring, Real.cos_pi_div_two, zero_div, mul_zero,
    show Real.pi * 3 / 4 = 3 * Real.pi / 4 by ring, cot_pi_div_four_six, hc3]
  ring

private lemma vasyuninCotSum_six_formula (b : ℕ) :
    vasyuninCotSum 6 b =
      (Int.fract ((b : ℝ) / 6) - Int.fract (5 * (b : ℝ) / 6)) * Real.sqrt 3 +
        (Int.fract (2 * (b : ℝ) / 6) - Int.fract (4 * (b : ℝ) / 6)) * (1 / Real.sqrt 3) := by
  have hc4 : Real.cos (4 * Real.pi / 6) / Real.sin (4 * Real.pi / 6) = -(1 / Real.sqrt 3) := by
    rw [show 4 * Real.pi / 6 = Real.pi - Real.pi / 3 by ring, Real.cos_pi_sub, Real.sin_pi_sub,
      neg_div, cot_pi_div_three_six]
  have hc5 : Real.cos (5 * Real.pi / 6) / Real.sin (5 * Real.pi / 6) = -Real.sqrt 3 := by
    rw [show 5 * Real.pi / 6 = Real.pi - Real.pi / 6 by ring, Real.cos_pi_sub, Real.sin_pi_sub,
      neg_div, cot_pi_div_six_six]
  unfold vasyuninCotSum
  rw [show Finset.Ico 1 6 = ({1, 2, 3, 4, 5} : Finset ℕ) by ext x; simp; omega,
    Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  push_cast
  rw [show (1 : ℝ) * b / 6 = b / 6 by ring, show Real.pi * 1 / 6 = Real.pi / 6 by ring,
    show Real.pi * 2 / 6 = Real.pi / 3 by ring, show Real.pi * 3 / 6 = Real.pi / 2 by ring,
    show Real.pi * 4 / 6 = 4 * Real.pi / 6 by ring, show Real.pi * 5 / 6 = 5 * Real.pi / 6 by ring,
    cot_pi_div_six_six, cot_pi_div_three_six, Real.cos_pi_div_two, zero_div, mul_zero, hc4, hc5]
  ring

/-- Exact Vasyunin cotangent row evaluations at `a = 6` in `ℚ(√3)`. -/
theorem vasyuninCotSum_six_eval :
    vasyuninCotSum 6 1 = -(7 / (3 * Real.sqrt 3)) ∧
      vasyuninCotSum 6 2 = -(2 / (3 * Real.sqrt 3)) ∧
      vasyuninCotSum 6 3 = 0 ∧
      vasyuninCotSum 6 4 = 2 / (3 * Real.sqrt 3) ∧
      vasyuninCotSum 6 5 = 7 / (3 * Real.sqrt 3) := by
  have hsq3 : Real.sqrt 3 ≠ 0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    (rw [vasyuninCotSum_six_formula]; norm_num; try (field_simp [hsq3]; norm_num))

/-- Exact boundary drive evaluation at `k = 6`: `deltaCot 6 = 5 / (3 * √3)`. -/
theorem deltaCot_six_eq : deltaCot 6 = 5 / (3 * Real.sqrt 3) := by
  have hsq3 : Real.sqrt 3 ≠ 0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  unfold deltaCot
  rw [vasyuninCotSum_six_eval.2.1, vasyuninCotSum_six_eval.1]
  field_simp [hsq3]; ring

/-- Divisibility vanishing at `b = 6`: `vasyuninCotSum 2 6 = 0`. -/
theorem vasyuninCotSum_two_six_eq_zero : vasyuninCotSum 2 6 = 0 :=
  vasyuninCotSum_two_six_aux 6

/-- Divisibility vanishing at `b = 6`: `vasyuninCotSum 3 6 = 0`. -/
theorem vasyuninCotSum_three_six_eq_zero : vasyuninCotSum 3 6 = 0 := by
  rw [vasyuninCotSum_three_six_aux]; norm_num

/-- Divisibility vanishing at `b = 6`: `vasyuninCotSum 4 6 = 0`. -/
theorem vasyuninCotSum_four_six_eq_zero : vasyuninCotSum 4 6 = 0 := by
  rw [vasyuninCotSum_four_six_aux]; norm_num

/-- Exact unweighted kernel evaluation `unweightedKCot 2 6 = π / (3 * √3)`. -/
theorem unweightedKCot_two_six_eq :
    unweightedKCot 2 6 = Real.pi / (3 * Real.sqrt 3) := by
  have hsq3 : Real.sqrt 3 ≠ 0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  unfold unweightedKCot vasyuninGCot
  rw [vasyuninCotSum_two_six_eq_zero, vasyuninCotSum_six_eval.2.1]
  push_cast; field_simp [hsq3]; ring

/-- Divisibility orthogonality of the `(3, 6)` unweighted kernel pair: `unweightedKCot 3 6 = 0`. -/
theorem unweightedKCot_three_six_eq_zero : unweightedKCot 3 6 = 0 := by
  unfold unweightedKCot vasyuninGCot
  rw [vasyuninCotSum_three_six_eq_zero, vasyuninCotSum_six_eval.2.2.1]; norm_num

/-- Exact unweighted kernel evaluation `unweightedKCot 4 6 = -π / (3 * √3)`. -/
theorem unweightedKCot_four_six_eq :
    unweightedKCot 4 6 = -(Real.pi / (3 * Real.sqrt 3)) := by
  have hsq3 : Real.sqrt 3 ≠ 0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  unfold unweightedKCot vasyuninGCot
  rw [vasyuninCotSum_four_six_eq_zero, vasyuninCotSum_six_eval.2.2.2.1]
  push_cast; field_simp [hsq3]; ring

private lemma deltaCot_three_six_aux : deltaCot 3 = 2 / (3 * Real.sqrt 3) := by
  unfold deltaCot
  rw [vasyuninCotSum_three_six_aux, vasyuninCotSum_three_six_aux]; norm_num; ring

private lemma deltaCot_four_six_aux : deltaCot 4 = 1 / 2 := by
  unfold deltaCot; rw [vasyuninCotSum_four_six_aux, vasyuninCotSum_four_six_aux]; norm_num

private lemma unweightedKCot_three_four_six_aux :
    unweightedKCot 3 4 = Real.pi / (6 * Real.sqrt 3) - Real.pi / 4 := by
  have hsq3 : Real.sqrt 3 ≠ 0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  unfold unweightedKCot vasyuninGCot
  rw [vasyuninCotSum_three_six_aux, vasyuninCotSum_four_six_aux]; norm_num
  field_simp [hsq3]; ring

/-- Universal horizontal adjacent sum telescoping for `dipoleGramEntry`. -/
theorem dipoleGramEntry_add_succ_right (a b : ℕ) :
    dipoleGramEntry a b + dipoleGramEntry a (b + 1) =
      Real.pi * (deltaCot (a + 2) - deltaCot (a + 1)) +
        (Real.pi / 2) * (deltaCot (b + 3) - deltaCot (b + 1)) +
        (unweightedKCot (a + 1) (b + 1) - unweightedKCot (a + 1) (b + 3) -
          unweightedKCot (a + 2) (b + 1) + unweightedKCot (a + 2) (b + 3)) := by
  unfold dipoleGramEntry; ring

/-- Exact `N = 6` adjacent coupling sum: `dipoleGramEntry 1 3 + dipoleGramEntry 1 4 = π / √3`. -/
theorem dipoleGramEntry_one_three_add_one_four_eq :
    dipoleGramEntry 1 3 + dipoleGramEntry 1 4 = Real.pi / Real.sqrt 3 := by
  have hsq3 : Real.sqrt 3 ≠ 0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  have htel := dipoleGramEntry_add_succ_right 1 3
  simp only [Nat.reduceAdd] at htel
  have hd2 : deltaCot 2 = 0 := by
    unfold deltaCot; rw [vasyuninCotSum_two_six_aux, vasyuninCotSum_two_six_aux, sub_self]
  have hk24 : unweightedKCot 2 4 = 0 := by
    unfold unweightedKCot vasyuninGCot
    rw [vasyuninCotSum_two_six_aux, vasyuninCotSum_four_six_aux]; norm_num
  rw [htel, hd2, deltaCot_three_six_aux, deltaCot_four_six_aux, deltaCot_six_eq, hk24,
    unweightedKCot_three_four_six_aux, unweightedKCot_two_six_eq, unweightedKCot_three_six_eq_zero]
  field_simp [hsq3]; ring

/-- Exact closed-form `N = 6` off-diagonal entry
`dipoleGramEntry 1 4 = π / √3 - π * cot(2π / 5)`. -/
theorem dipoleGramEntry_one_four_eq :
    dipoleGramEntry 1 4 =
      Real.pi / Real.sqrt 3 -
        Real.pi * (Real.cos (2 * Real.pi / 5) / Real.sin (2 * Real.pi / 5)) := by
  linarith [dipoleGramEntry_one_three_add_one_four_eq, dipoleGramEntry_one_three_eq]

/-- Complete `N = 6` decoupling of `cumulativeDipole 2` and `cumulativeDipole 4`:
`dipoleGramEntry 2 4 = 0` and `dipoleGramEntry 4 2 = 0`. -/
theorem dipoleGramEntry_two_four_eq_zero :
    dipoleGramEntry 2 4 = 0 ∧ dipoleGramEntry 4 2 = 0 := by
  have hsq3 : Real.sqrt 3 ≠ 0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  have htel := dipoleGramEntry_add_succ_right 2 3
  simp only [Nat.reduceAdd] at htel
  have hsum : dipoleGramEntry 2 3 + dipoleGramEntry 2 4 = 0 := by
    rw [htel, deltaCot_three_six_aux, deltaCot_four_six_aux, deltaCot_six_eq,
      unweightedKCot_three_four_six_aux, unweightedKCot_diag 4,
      unweightedKCot_three_six_eq_zero, unweightedKCot_four_six_eq]
    field_simp [hsq3]; ring
  have h24 : dipoleGramEntry 2 4 = 0 := by linarith [dipoleGramEntry_two_three_eq_zero.1]
  exact ⟨h24, by rw [dipoleGramEntry_comm 4 2, h24]⟩
