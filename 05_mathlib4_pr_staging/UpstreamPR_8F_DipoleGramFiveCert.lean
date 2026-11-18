/-
Copyright (c) 2026 Qamar Munawer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qamar Munawer
-/
module

public import RiemannBlueprint.UpstreamPRs.UpstreamPR_8E_DirichletOptFourCert

/-!
# Exact Closed-Form `N = 5` Dipole Gram Entries and Reciprocity Orthogonality

This module lifts the `N = 5` `(ℤ/5ℤ)×` reciprocity orthogonality of `cumulativeDipole 2` and
`cumulativeDipole 3` to closed-form values on `dipoleGramEntry` and `dipolePlaqueEntry`:

* `dipoleGramEntry_two_three_eq_zero`: exact vanishing `dipoleGramEntry 2 3 = 0` and
  `dipoleGramEntry 3 2 = 0`.
* `vasyuninCotSum_five_one_eq`, `vasyuninCotSum_five_two_eq`: exact `(cot(π/5), cot(2π/5))`
  reductions of `vasyuninCotSum 5 b` for `b ∈ {1, 2}`.
* `dipoleGramEntry_one_three_eq`: `dipoleGramEntry 1 3 = π * cot(2π / 5)`.
* `dipoleGramEntry_three_three_eq`: `dipoleGramEntry 3 3 = π * (cot(π / 5) + cot(2π / 5) - 1)`.
* `dipolePlaqueEntry_two_three_eq`: exact boundary-cancellation form for `dipolePlaqueEntry 2 3`.
-/

@[expose] public section

open scoped BigOperators

private lemma cot_three_pi_div_five_five :
    Real.cos (Real.pi * 3 / 5) / Real.sin (Real.pi * 3 / 5) =
      -(Real.cos (2 * Real.pi / 5) / Real.sin (2 * Real.pi / 5)) := by
  rw [show Real.pi * 3 / 5 = Real.pi - 2 * Real.pi / 5 by ring,
    Real.cos_pi_sub, Real.sin_pi_sub, neg_div]

private lemma cot_four_pi_div_five_five :
    Real.cos (Real.pi * 4 / 5) / Real.sin (Real.pi * 4 / 5) =
      -(Real.cos (Real.pi / 5) / Real.sin (Real.pi / 5)) := by
  rw [show Real.pi * 4 / 5 = Real.pi - Real.pi / 5 by ring,
    Real.cos_pi_sub, Real.sin_pi_sub, neg_div]

private lemma sum_Ico_one_five_five (f : ℕ → ℝ) :
    ∑ m ∈ Finset.Ico 1 5, f m = f 1 + f 2 + f 3 + f 4 := by
  rw [show Finset.Ico 1 5 = ({1, 2, 3, 4} : Finset ℕ) by ext x; simp; omega,
    Finset.sum_insert (by decide : (1 : ℕ) ∉ ({2, 3, 4} : Finset ℕ)),
    Finset.sum_insert (by decide : (2 : ℕ) ∉ ({3, 4} : Finset ℕ)),
    Finset.sum_insert (by decide : (3 : ℕ) ∉ ({4} : Finset ℕ)), Finset.sum_singleton]
  ring

private lemma vasyuninCotSum_two_five (b : ℕ) : vasyuninCotSum 2 b = 0 := by
  unfold vasyuninCotSum
  rw [show Finset.Ico 1 2 = ({1} : Finset ℕ) by ext x; simp, Finset.sum_singleton,
    show Real.pi * ((1 : ℕ) : ℝ) / ((2 : ℕ) : ℝ) = Real.pi / 2 by push_cast; ring,
    Real.cos_pi_div_two, zero_div, mul_zero]

private lemma vasyuninCotSum_three_five (b : ℕ) :
    vasyuninCotSum 3 b =
      (Int.fract ((b : ℝ) / 3) - Int.fract (2 * (b : ℝ) / 3)) * (1 / Real.sqrt 3) := by
  have hsq3 : Real.sqrt 3 ≠ 0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  have hc1 : Real.cos (Real.pi / 3) / Real.sin (Real.pi / 3) = 1 / Real.sqrt 3 := by
    rw [Real.cos_pi_div_three, Real.sin_pi_div_three]; field_simp [hsq3]
  have hc2 : Real.cos (2 * Real.pi / 3) / Real.sin (2 * Real.pi / 3) = -(1 / Real.sqrt 3) := by
    rw [show 2 * Real.pi / 3 = Real.pi - Real.pi / 3 by ring, Real.cos_pi_sub, Real.sin_pi_sub,
      neg_div, hc1]
  unfold vasyuninCotSum
  rw [show Finset.Ico 1 3 = ({1, 2} : Finset ℕ) by ext x; simp; omega,
    Finset.sum_insert (by decide), Finset.sum_singleton]
  push_cast
  rw [show (1 : ℝ) * b / 3 = b / 3 by ring, show Real.pi * 1 / 3 = Real.pi / 3 by ring,
    show Real.pi * 2 / 3 = 2 * Real.pi / 3 by ring, hc1, hc2]
  ring

private lemma vasyuninCotSum_four_five (b : ℕ) :
    vasyuninCotSum 4 b = Int.fract ((b : ℝ) / 4) - Int.fract (3 * (b : ℝ) / 4) := by
  have hc1 : Real.cos (Real.pi / 4) / Real.sin (Real.pi / 4) = 1 := by
    rw [Real.cos_pi_div_four, Real.sin_pi_div_four]
    field_simp [(Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)).ne']
  have hc3 : Real.cos (3 * Real.pi / 4) / Real.sin (3 * Real.pi / 4) = -1 := by
    rw [show 3 * Real.pi / 4 = Real.pi - Real.pi / 4 by ring, Real.cos_pi_sub, Real.sin_pi_sub,
      neg_div, hc1]
  unfold vasyuninCotSum
  rw [show Finset.Ico 1 4 = ({1, 2, 3} : Finset ℕ) by ext x; simp; omega,
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  push_cast
  rw [show (1 : ℝ) * b / 4 = b / 4 by ring, show Real.pi * 1 / 4 = Real.pi / 4 by ring,
    show Real.pi * 2 / 4 = Real.pi / 2 by ring, Real.cos_pi_div_two, zero_div, mul_zero,
    show Real.pi * 3 / 4 = 3 * Real.pi / 4 by ring, hc1, hc3]
  ring

/-- Exact closed-form evaluation `vasyuninCotSum 5 1`. -/
theorem vasyuninCotSum_five_one_eq :
    vasyuninCotSum 5 1 =
      -(3 / 5 : ℝ) * (Real.cos (Real.pi / 5) / Real.sin (Real.pi / 5)) -
        (1 / 5 : ℝ) * (Real.cos (2 * Real.pi / 5) / Real.sin (2 * Real.pi / 5)) := by
  unfold vasyuninCotSum
  rw [sum_Ico_one_five_five]
  push_cast
  rw [show Real.pi * 1 / 5 = Real.pi / 5 by ring,
    show Real.pi * 2 / 5 = 2 * Real.pi / 5 by ring,
    cot_three_pi_div_five_five, cot_four_pi_div_five_five]
  norm_num
  ring

/-- Exact closed-form evaluation `vasyuninCotSum 5 2`. -/
theorem vasyuninCotSum_five_two_eq :
    vasyuninCotSum 5 2 =
      -(1 / 5 : ℝ) * (Real.cos (Real.pi / 5) / Real.sin (Real.pi / 5)) +
        (3 / 5 : ℝ) * (Real.cos (2 * Real.pi / 5) / Real.sin (2 * Real.pi / 5)) := by
  unfold vasyuninCotSum
  rw [sum_Ico_one_five_five]
  push_cast
  rw [show Real.pi * 1 / 5 = Real.pi / 5 by ring,
    show Real.pi * 2 / 5 = 2 * Real.pi / 5 by ring,
    cot_three_pi_div_five_five, cot_four_pi_div_five_five]
  norm_num
  ring

private lemma vasyuninCotSum_five_three_eq :
    vasyuninCotSum 5 3 = -vasyuninCotSum 5 2 := by
  linarith [vasyuninCotSum_five_two_add_three]

private lemma vasyuninCotSum_five_four_eq :
    vasyuninCotSum 5 4 = -vasyuninCotSum 5 1 := by
  linarith [vasyuninCotSum_five_one_add_four]

/-- Exact vanishing of the off-diagonal `N = 5` dipole Gram entry `dipoleGramEntry 2 3` and its
transpose `dipoleGramEntry 3 2`. -/
theorem dipoleGramEntry_two_three_eq_zero :
    dipoleGramEntry 2 3 = 0 ∧ dipoleGramEntry 3 2 = 0 := by
  have hfp := sum_cumulativeDipole_vasyuninGCot_eq_four_point (a := 2) (b := 3) (N := 5)
    (by omega) (by omega) (by omega) (by omega)
  change _ = dipoleGramEntry 2 3 at hfp
  have h23 : dipoleGramEntry 2 3 = 0 := by
    rw [← hfp]
    exact sum_cumulativeDipole_two_three_vasyuninGCot_five_eq_zero
  exact ⟨h23, by rw [dipoleGramEntry_comm 3 2, h23]⟩

/-- Exact off-diagonal `N = 5` dipole Gram entry `dipoleGramEntry 1 3 = π * cot(2π / 5)`. -/
theorem dipoleGramEntry_one_three_eq :
    dipoleGramEntry 1 3 =
      Real.pi * (Real.cos (2 * Real.pi / 5) / Real.sin (2 * Real.pi / 5)) := by
  have hsq3 : Real.sqrt 3 ≠ 0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  unfold dipoleGramEntry deltaCot unweightedKCot vasyuninGCot
  simp only [Nat.reduceAdd, Nat.cast_ofNat]
  simp_rw [vasyuninCotSum_two_five, vasyuninCotSum_three_five, vasyuninCotSum_four_five,
    vasyuninCotSum_five_three_eq, vasyuninCotSum_five_one_eq, vasyuninCotSum_five_two_eq]
  norm_num
  field_simp [hsq3]
  ring

/-- Exact closed-form diagonal `N = 5` dipole Gram entry
`dipoleGramEntry 3 3 = π * (cot(π / 5) + cot(2π / 5) - 1)`. -/
theorem dipoleGramEntry_three_three_eq :
    dipoleGramEntry 3 3 =
      Real.pi *
        (Real.cos (Real.pi / 5) / Real.sin (Real.pi / 5) +
          Real.cos (2 * Real.pi / 5) / Real.sin (2 * Real.pi / 5) - 1) := by
  rw [dipoleGramEntry_diag_eq 3]
  unfold deltaCot unweightedKCot vasyuninGCot
  simp only [Nat.reduceAdd, Nat.cast_ofNat]
  simp_rw [vasyuninCotSum_four_five, vasyuninCotSum_five_four_eq, vasyuninCotSum_five_one_eq,
    vasyuninCotSum_five_two_eq]
  norm_num
  ring

/-- Exact plaque-vs-boundary identity at `(2, 3)` forced by `dipoleGramEntry 2 3 = 0`. -/
theorem dipolePlaqueEntry_two_three_eq :
    dipolePlaqueEntry 2 3 =
      -(Real.pi / 2) * (deltaCot 4 - deltaCot 3 + deltaCot 5 - deltaCot 4) := by
  have hsplit := dipoleGramEntry_eq_boundary_add_plaque 2 3
  have hz : dipoleGramEntry 2 3 = 0 := dipoleGramEntry_two_three_eq_zero.1
  simp only [Nat.reduceAdd] at hsplit
  linarith
