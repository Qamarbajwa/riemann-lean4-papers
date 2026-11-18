/-
Copyright (c) 2026 Qamar Munawer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qamar Munawer
-/
module

public import RiemannBlueprint.UpstreamPRs.UpstreamPR_4H_WaveletRayleighRHCriterion

/-!
# Cumulative Wavelet Dipole Basis, First-Difference Telescoping, and Exact `N = 4, 5` Orthogonality

This file introduces the cumulative harmonic dipole basis
`cumulativeDipole m k = ∑ r ∈ Finset.Icc 1 m, harmonicWavelet r k` on `A_N⁰`:

* `cumulativeDipole_mem_tangent`: every dipole lies in `A_N⁰` for `1 ≤ m` and `m + 2 ≤ N`.
* `linearCotDrive_cumulativeDipole_eq`: summing the 3-point second-difference stencils over
  `1..m` telescopes identically into `deltaCot (m + 2) - deltaCot (m + 1)`.
* `QCot_cumulativeDipole_two_eq` and `sum_cumulativeDipole_one_two_vasyuninGCot_eq_zero`: exact
  cotangent energy `(1 - 1 / √3) * π` and exact `N = 4` orthogonality `d₁ ⊥ d₂`.
* `vasyuninCotSum_five_one_add_four`, `vasyuninCotSum_five_two_add_three`, and
  `sum_cumulativeDipole_two_three_vasyuninGCot_five_eq_zero`: reciprocity cancellation on `Z/5Z`
  and exact `N = 5` orthogonality `d₂ ⊥ d₃` without evaluating `cot (π / 5)`.
-/

@[expose] public section

open scoped BigOperators
open MeasureTheory Finset

/-- Cumulative sum of the first `m` harmonic wavelets on `A_N⁰`. -/
def cumulativeDipole (m k : ℕ) : ℝ :=
  ∑ r ∈ Finset.Icc 1 m, harmonicWavelet r k

private lemma cumulativeDipole_eq_sum_one_mul (m : ℕ) :
    cumulativeDipole m = fun k => ∑ r ∈ Finset.Icc 1 m, (1 : ℝ) * harmonicWavelet r k :=
  funext fun k => by simp [cumulativeDipole]

/-- Every cumulative dipole `cumulativeDipole m` lies unconditionally in `A_N⁰` for
`1 ≤ m` and `m + 2 ≤ N`. -/
theorem cumulativeDipole_mem_tangent {m N : ℕ} (hm : 1 ≤ m) (hN : m + 2 ≤ N) :
    D1 (cumulativeDipole m) N = 0 ∧ D0 (cumulativeDipole m) N = 0 := by
  let _ := hm
  have hs : ∀ r ∈ Finset.Icc 1 m, 1 ≤ r ∧ r + 2 ≤ N := fun r hr =>
    ⟨(Finset.mem_Icc.mp hr).1, by have := (Finset.mem_Icc.mp hr).2; omega⟩
  rw [cumulativeDipole_eq_sum_one_mul]
  exact sum_smul_harmonicWavelet_mem_tangent (Finset.Icc 1 m) hs (fun _ => 1)

private lemma cot_pi_div_three_dip : Real.cos (Real.pi / 3) / Real.sin (Real.pi / 3) = 1 / √3 := by
  rw [Real.cos_pi_div_three, Real.sin_pi_div_three]
  field_simp [(Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 3)).ne']
private lemma cot_two_pi_div_three_dip :
    Real.cos (2 * Real.pi / 3) / Real.sin (2 * Real.pi / 3) = -(1 / √3) := by
  rw [show 2 * Real.pi / 3 = Real.pi - Real.pi / 3 by ring, Real.cos_pi_sub, Real.sin_pi_sub,
    neg_div, cot_pi_div_three_dip]
private lemma cot_pi_div_four_dip : Real.cos (Real.pi / 4) / Real.sin (Real.pi / 4) = 1 := by
  rw [Real.cos_pi_div_four, Real.sin_pi_div_four]
  field_simp [(Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)).ne']
private lemma vasyuninCotSum_two_dip (b : ℕ) : vasyuninCotSum 2 b = 0 := by
  unfold vasyuninCotSum
  rw [show Finset.Ico 1 2 = ({1} : Finset ℕ) by ext x; simp, Finset.sum_singleton,
    show Real.pi * ((1 : ℕ) : ℝ) / ((2 : ℕ) : ℝ) = Real.pi / 2 by push_cast; ring,
    Real.cos_pi_div_two, zero_div, mul_zero]
private lemma vasyuninCotSum_three_dip (b : ℕ) :
    vasyuninCotSum 3 b =
      (Int.fract ((b : ℝ) / 3) - Int.fract (2 * (b : ℝ) / 3)) * (1 / √3) := by
  unfold vasyuninCotSum
  rw [show Finset.Ico 1 3 = ({1, 2} : Finset ℕ) by ext x; simp; omega,
    Finset.sum_insert (by decide), Finset.sum_singleton]
  push_cast
  rw [show (1 : ℝ) * b / 3 = b / 3 by ring, show Real.pi * 1 / 3 = Real.pi / 3 by ring,
    show Real.pi * 2 / 3 = 2 * Real.pi / 3 by ring, cot_pi_div_three_dip, cot_two_pi_div_three_dip]
  ring
private lemma vasyuninCotSum_four_dip (b : ℕ) :
    vasyuninCotSum 4 b = Int.fract ((b : ℝ) / 4) - Int.fract (3 * (b : ℝ) / 4) := by
  unfold vasyuninCotSum
  rw [show Finset.Ico 1 4 = ({1, 2, 3} : Finset ℕ) by ext x; simp; omega,
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  push_cast
  rw [show (1 : ℝ) * b / 4 = b / 4 by ring, show Real.pi * 1 / 4 = Real.pi / 4 by ring,
    show Real.pi * 2 / 4 = Real.pi / 2 by ring, Real.cos_pi_div_two, zero_div, mul_zero,
    show Real.pi * 3 / 4 = 3 * Real.pi / 4 by ring, cot_pi_div_four_dip,
    show Real.cos (3 * Real.pi / 4) / Real.sin (3 * Real.pi / 4) = -1 by
      rw [show 3 * Real.pi / 4 = Real.pi - Real.pi / 4 by ring, Real.cos_pi_sub, Real.sin_pi_sub,
        neg_div, cot_pi_div_four_dip]]
  ring

/-- Universal telescoping first-difference law for `linearCotDrive` on cumulative dipoles:
summing the second-difference stencils over `1..m` yields `deltaCot (m + 2) - deltaCot (m + 1)`
for all `1 ≤ m` and `m + 2 ≤ N`. -/
theorem linearCotDrive_cumulativeDipole_eq {m N : ℕ} (hm : 1 ≤ m) (hN : m + 2 ≤ N) :
    linearCotDrive (cumulativeDipole m) N = deltaCot (m + 2) - deltaCot (m + 1) := by
  have hs : ∀ r ∈ Finset.Icc 1 m, 1 ≤ r ∧ r + 2 ≤ N := fun r hr =>
    ⟨(Finset.mem_Icc.mp hr).1, by have := (Finset.mem_Icc.mp hr).2; omega⟩
  rw [cumulativeDipole_eq_sum_one_mul,
    linearCotDrive_sum_harmonicWavelet_eq (Finset.Icc 1 m) hs (fun _ => 1)]
  simp_rw [one_mul]
  clear hs hN
  induction m, hm using Nat.le_induction with
  | base =>
    have hd1 : deltaCot 1 = 0 := by simp [deltaCot, vasyuninCotSum]
    have hd2 : deltaCot 2 = 0 := by
      dsimp [deltaCot]; rw [vasyuninCotSum_two_dip, vasyuninCotSum_two_dip, sub_self]
    simp [hd1, hd2]
  | succ k hk ih =>
    rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ k + 1), ih]
    ring

private lemma vasyuninGCot_one_two_dip : vasyuninGCot 1 2 = 0 := by
  have hV1 : vasyuninCotSum 1 2 = 0 := by simp [vasyuninCotSum]
  unfold vasyuninGCot; rw [hV1, vasyuninCotSum_two_dip]; ring
private lemma vasyuninGCot_one_three_dip : vasyuninGCot 1 3 = Real.pi / (18 * √3) := by
  have hV1 : vasyuninCotSum 1 3 = 0 := by simp [vasyuninCotSum]
  unfold vasyuninGCot; rw [hV1, vasyuninCotSum_three_dip]; norm_num; ring
private lemma vasyuninGCot_one_four_dip : vasyuninGCot 1 4 = Real.pi / 16 := by
  have hV1 : vasyuninCotSum 1 4 = 0 := by simp [vasyuninCotSum]
  unfold vasyuninGCot; rw [hV1, vasyuninCotSum_four_dip]; norm_num; ring
private lemma vasyuninGCot_two_three_dip : vasyuninGCot 2 3 = -(Real.pi / (36 * √3)) := by
  unfold vasyuninGCot; rw [vasyuninCotSum_two_dip, vasyuninCotSum_three_dip]; norm_num; ring
private lemma vasyuninGCot_two_four_dip : vasyuninGCot 2 4 = 0 := by
  unfold vasyuninGCot; rw [vasyuninCotSum_two_dip, vasyuninCotSum_four_dip]; norm_num
private lemma vasyuninGCot_three_four_dip :
    vasyuninGCot 3 4 = Real.pi / (72 * √3) - Real.pi / 48 := by
  unfold vasyuninGCot; rw [vasyuninCotSum_three_dip, vasyuninCotSum_four_dip]; norm_num; ring

private lemma sum_Icc_one_four_dip (f : ℕ → ℝ) :
    ∑ k ∈ Finset.Icc 1 4, f k = f 1 + f 2 + f 3 + f 4 := by
  rw [show Finset.Icc 1 4 = ({1, 2, 3, 4} : Finset ℕ) by
    ext x; simp only [Finset.mem_Icc, Finset.mem_insert, Finset.mem_singleton]; omega]
  norm_num [Finset.sum_insert, add_assoc]

private lemma sum_Icc_one_five_dip (f : ℕ → ℝ) :
    ∑ k ∈ Finset.Icc 1 5, f k = f 1 + f 2 + f 3 + f 4 + f 5 := by
  rw [show Finset.Icc 1 5 = ({1, 2, 3, 4, 5} : Finset ℕ) by
    ext x; simp only [Finset.mem_Icc, Finset.mem_insert, Finset.mem_singleton]; omega]
  norm_num [Finset.sum_insert, add_assoc]

private lemma cumulativeDipole_two_eq (k : ℕ) :
    cumulativeDipole 2 k = harmonicWavelet 1 k + harmonicWavelet 2 k := by
  unfold cumulativeDipole
  rw [show Finset.Icc 1 2 = ({1, 2} : Finset ℕ) by ext x; simp; omega,
    Finset.sum_insert (by decide), Finset.sum_singleton]

private lemma cumulativeDipole_three_eq (k : ℕ) :
    cumulativeDipole 3 k = harmonicWavelet 1 k + harmonicWavelet 2 k + harmonicWavelet 3 k := by
  unfold cumulativeDipole
  rw [show Finset.Icc 1 3 = ({1, 2, 3} : Finset ℕ) by ext x; simp; omega,
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton, add_assoc]

/-- Exact cotangent energy of the second cumulative dipole `cumulativeDipole 2` at `N = 4`:
`(1 - 1 / √3) * π`. -/
theorem QCot_cumulativeDipole_two_eq :
    QCot vasyuninGCot (cumulativeDipole 2) 4 = (1 - 1 / Real.sqrt 3) * Real.pi := by
  unfold QCot
  simp_rw [sum_Icc_one_four_dip, cumulativeDipole_two_eq]
  rw [vasyuninGCot_diag 1, vasyuninGCot_diag 2, vasyuninGCot_diag 3, vasyuninGCot_diag 4,
    vasyuninGCot_comm 2 1, vasyuninGCot_comm 3 1, vasyuninGCot_comm 4 1,
    vasyuninGCot_comm 3 2, vasyuninGCot_comm 4 2, vasyuninGCot_comm 4 3,
    vasyuninGCot_one_two_dip, vasyuninGCot_one_three_dip, vasyuninGCot_one_four_dip,
    vasyuninGCot_two_three_dip, vasyuninGCot_two_four_dip, vasyuninGCot_three_four_dip]
  simp [harmonicWavelet]
  ring

/-- Exact `N = 4` `vasyuninGCot`-orthogonality of `cumulativeDipole 1` and `cumulativeDipole 2`. -/
theorem sum_cumulativeDipole_one_two_vasyuninGCot_eq_zero :
    ∑ j ∈ Finset.Icc 1 4, ∑ k ∈ Finset.Icc 1 4,
      cumulativeDipole 1 j * cumulativeDipole 2 k * vasyuninGCot j k = 0 := by
  have h1 : ∀ k, cumulativeDipole 1 k = harmonicWavelet 1 k := fun _ => by simp [cumulativeDipole]
  simp_rw [sum_Icc_one_four_dip, h1, cumulativeDipole_two_eq]
  rw [vasyuninGCot_diag 1, vasyuninGCot_diag 2, vasyuninGCot_diag 3, vasyuninGCot_diag 4,
    vasyuninGCot_comm 2 1, vasyuninGCot_comm 3 1, vasyuninGCot_comm 4 1,
    vasyuninGCot_comm 3 2, vasyuninGCot_comm 4 2, vasyuninGCot_comm 4 3,
    vasyuninGCot_one_two_dip, vasyuninGCot_one_three_dip, vasyuninGCot_one_four_dip,
    vasyuninGCot_two_three_dip, vasyuninGCot_two_four_dip, vasyuninGCot_three_four_dip]
  simp [harmonicWavelet]
  ring

private lemma vasyuninCotSum_five_add_eq_zero (b₁ b₂ : ℕ)
    (hb : ∀ m ∈ Finset.Ico (1 : ℕ) 5,
      Int.fract ((m : ℝ) * (b₁ : ℝ) / 5) + Int.fract ((m : ℝ) * (b₂ : ℝ) / 5) = 1) :
    vasyuninCotSum 5 b₁ + vasyuninCotSum 5 b₂ = 0 := by
  unfold vasyuninCotSum
  push_cast
  rw [← Finset.sum_add_distrib]
  have hrew :
      (∑ m ∈ Finset.Ico (1 : ℕ) 5,
        (Int.fract ((m : ℝ) * (b₁ : ℝ) / 5) *
            (Real.cos (Real.pi * (m : ℝ) / 5) / Real.sin (Real.pi * (m : ℝ) / 5)) +
          Int.fract ((m : ℝ) * (b₂ : ℝ) / 5) *
            (Real.cos (Real.pi * (m : ℝ) / 5) / Real.sin (Real.pi * (m : ℝ) / 5)))) =
        ∑ m ∈ Finset.Ico (1 : ℕ) 5,
          Real.cos (Real.pi * (m : ℝ) / 5) / Real.sin (Real.pi * (m : ℝ) / 5) :=
    Finset.sum_congr rfl fun m hm => by rw [← add_mul, hb m hm, one_mul]
  rw [hrew, show Finset.Ico 1 5 = ({1, 2, 3, 4} : Finset ℕ) by ext x; simp; omega,
    Finset.sum_insert (by decide : (1 : ℕ) ∉ ({2, 3, 4} : Finset ℕ)),
    Finset.sum_insert (by decide : (2 : ℕ) ∉ ({3, 4} : Finset ℕ)),
    Finset.sum_insert (by decide : (3 : ℕ) ∉ ({4} : Finset ℕ)), Finset.sum_singleton]
  push_cast
  have h3 : Real.cos (Real.pi * 3 / 5) / Real.sin (Real.pi * 3 / 5) =
      -(Real.cos (Real.pi * 2 / 5) / Real.sin (Real.pi * 2 / 5)) := by
    rw [show Real.pi * 3 / 5 = Real.pi - Real.pi * 2 / 5 by ring,
      Real.cos_pi_sub, Real.sin_pi_sub, neg_div]
  have h4 : Real.cos (Real.pi * 4 / 5) / Real.sin (Real.pi * 4 / 5) =
      -(Real.cos (Real.pi * 1 / 5) / Real.sin (Real.pi * 1 / 5)) := by
    rw [show Real.pi * 4 / 5 = Real.pi - Real.pi * 1 / 5 by ring,
      Real.cos_pi_sub, Real.sin_pi_sub, neg_div]
  rw [h3, h4]
  ring

/-- Reciprocity cancellation on `(ℤ/5ℤ)×`: `vasyuninCotSum 5 1 + vasyuninCotSum 5 4 = 0`. -/
theorem vasyuninCotSum_five_one_add_four : vasyuninCotSum 5 1 + vasyuninCotSum 5 4 = 0 := by
  refine vasyuninCotSum_five_add_eq_zero 1 4 fun m hm => ?_
  rcases Finset.mem_Ico.mp hm with ⟨hm1, hm5⟩; interval_cases m <;> norm_num

/-- Reciprocity cancellation on `(ℤ/5ℤ)×`: `vasyuninCotSum 5 2 + vasyuninCotSum 5 3 = 0`. -/
theorem vasyuninCotSum_five_two_add_three : vasyuninCotSum 5 2 + vasyuninCotSum 5 3 = 0 := by
  refine vasyuninCotSum_five_add_eq_zero 2 3 fun m hm => ?_
  rcases Finset.mem_Ico.mp hm with ⟨hm1, hm5⟩; interval_cases m <;> norm_num

/-- Exact `N = 5` `vasyuninGCot`-orthogonality of `cumulativeDipole 2` and `cumulativeDipole 3`,
proved algebraically via reciprocity without evaluating `cot (π / 5)`. -/
theorem sum_cumulativeDipole_two_three_vasyuninGCot_five_eq_zero :
    ∑ j ∈ Finset.Icc 1 5, ∑ k ∈ Finset.Icc 1 5,
      cumulativeDipole 2 j * cumulativeDipole 3 k * vasyuninGCot j k = 0 := by
  have h15 : vasyuninGCot 1 5 = -(Real.pi / 10) * vasyuninCotSum 5 1 := by
    have hV1 : vasyuninCotSum 1 5 = 0 := by simp [vasyuninCotSum]
    unfold vasyuninGCot; rw [hV1]; norm_num
  have h25 : vasyuninGCot 2 5 = -(Real.pi / 20) * vasyuninCotSum 5 2 := by
    unfold vasyuninGCot; rw [vasyuninCotSum_two_dip]; norm_num
  have h35 :
      vasyuninGCot 3 5 = -(Real.pi / (90 * √3)) - (Real.pi / 30) * vasyuninCotSum 5 3 := by
    unfold vasyuninGCot; rw [vasyuninCotSum_three_dip]; norm_num; ring
  have h45 : vasyuninGCot 4 5 = Real.pi / 80 - (Real.pi / 40) * vasyuninCotSum 5 4 := by
    unfold vasyuninGCot; rw [vasyuninCotSum_four_dip]; norm_num; ring
  have h54 : vasyuninCotSum 5 4 = -vasyuninCotSum 5 1 := by
    linarith [vasyuninCotSum_five_one_add_four]
  have h53 : vasyuninCotSum 5 3 = -vasyuninCotSum 5 2 := by
    linarith [vasyuninCotSum_five_two_add_three]
  simp_rw [sum_Icc_one_five_dip, cumulativeDipole_two_eq, cumulativeDipole_three_eq]
  rw [vasyuninGCot_diag 1, vasyuninGCot_diag 2, vasyuninGCot_diag 3, vasyuninGCot_diag 4,
    vasyuninGCot_comm 2 1, vasyuninGCot_comm 3 1, vasyuninGCot_comm 4 1,
    vasyuninGCot_comm 3 2, vasyuninGCot_comm 4 2, vasyuninGCot_comm 4 3,
    vasyuninGCot_comm 5 1, vasyuninGCot_comm 5 2, vasyuninGCot_comm 5 3, vasyuninGCot_comm 5 4,
    vasyuninGCot_one_two_dip, vasyuninGCot_one_three_dip, vasyuninGCot_one_four_dip,
    vasyuninGCot_two_three_dip, vasyuninGCot_two_four_dip, vasyuninGCot_three_four_dip,
    h15, h25, h35, h45, h54, h53]
  simp [harmonicWavelet]
  ring
