/-
Copyright (c) 2026 Qamar Munawer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qamar Munawer
-/
module

public import RiemannBlueprint.UpstreamPRs.UpstreamPR_4F_TangentRayleighQuotient

/-!
# Two-Wavelet Completeness on `A_4`, Orthogonal Diagonalization, and Exact Global KKT Optimum

This file settles the exact global variational optimization problem on the `N = 4` Báez-Duarte
affine manifold `A_4 = {c | D1 c 4 = 0 ∧ D0 c 4 = 2}`:

* `eq_cBaseAnchor_add_wavelets_of_mem_A_four`: every `c ∈ A_4` splits uniquely on `{1, 2, 3, 4}`
  as `cBaseAnchor + (c 1 + 2) • harmonicWavelet 1 + (c 4 / 4) • harmonicWavelet 2`.
* `QCot_harmonicWavelet_two_eq`: the second harmonic wavelet `(0, 2, -6, 4)` has exact
  cotangent energy `QCot vasyuninGCot (harmonicWavelet 2) 4 = π`.
* `SCot_cBaseAnchor_add_two_wavelets_eq`: completing two orthogonal squares in `t₁ - t₂` and `t₂`
  yields `SCot = ((19 + √3) / 72) * π - (π / √3) * (t₁ - t₂ - 2 / 3)^2 - π * (1 - 1 / √3) * ...`.
* `cGlobalOptFour`, `cGlobalOptFour_mem_A_N`, `SCot_cGlobalOptFour_eq`,
  `SCot_le_cGlobalOptFour_of_mem_A_four`, `l2_dist_cGlobalOptFour_le_of_mem_A_four`: exact global
  KKT optimizer `(19 + √3) / 72 * π` over all of `A_4`.
-/

@[expose] public section

open scoped BigOperators
open MeasureTheory Finset

private lemma sum_Icc_one_four_opt (f : ℕ → ℝ) :
    ∑ k ∈ Finset.Icc 1 4, f k = f 1 + f 2 + f 3 + f 4 := by
  rw [show Finset.Icc 1 4 = ({1, 2, 3, 4} : Finset ℕ) by
    ext x; simp only [Finset.mem_Icc, Finset.mem_insert, Finset.mem_singleton]; omega]
  norm_num [Finset.sum_insert, add_assoc]

/-- Exact 2-wavelet completeness on `A_4`: every vector `c ∈ A_4` agrees on `{1, 2, 3, 4}` with
`cBaseAnchor + (c 1 + 2) • harmonicWavelet 1 + (c 4 / 4) • harmonicWavelet 2`. -/
theorem eq_cBaseAnchor_add_wavelets_of_mem_A_four (c : ℕ → ℝ)
    (hc1 : D1 c 4 = 0) (hc0 : D0 c 4 = 2) {k : ℕ} (hk : k ∈ Finset.Icc 1 4) :
    c k = cBaseAnchor k + (c 1 + 2) * harmonicWavelet 1 k +
      (c 4 / 4) * harmonicWavelet 2 k := by
  unfold D1 at hc1
  unfold D0 at hc0
  rw [sum_Icc_one_four_opt] at hc1 hc0
  norm_num at hc1 hc0
  rcases Finset.mem_Icc.mp hk with ⟨hk1, hk4⟩
  interval_cases k <;> simp [cBaseAnchor, harmonicWavelet] <;> linarith

private lemma cot_pi_div_three_opt : Real.cos (Real.pi / 3) / Real.sin (Real.pi / 3) = 1 / √3 := by
  rw [Real.cos_pi_div_three, Real.sin_pi_div_three]
  field_simp [(Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 3)).ne']

private lemma cot_two_pi_div_three_opt :
    Real.cos (2 * Real.pi / 3) / Real.sin (2 * Real.pi / 3) = -(1 / √3) := by
  rw [show 2 * Real.pi / 3 = Real.pi - Real.pi / 3 by ring, Real.cos_pi_sub, Real.sin_pi_sub,
    neg_div, cot_pi_div_three_opt]

private lemma cot_pi_div_four_opt : Real.cos (Real.pi / 4) / Real.sin (Real.pi / 4) = 1 := by
  rw [Real.cos_pi_div_four, Real.sin_pi_div_four]
  field_simp [(Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)).ne']

private lemma vasyuninCotSum_two_opt (b : ℕ) : vasyuninCotSum 2 b = 0 := by
  unfold vasyuninCotSum
  rw [show Finset.Ico 1 2 = ({1} : Finset ℕ) by ext x; simp, Finset.sum_singleton,
    show Real.pi * ((1 : ℕ) : ℝ) / ((2 : ℕ) : ℝ) = Real.pi / 2 by push_cast; ring,
    Real.cos_pi_div_two, zero_div, mul_zero]

private lemma vasyuninCotSum_three_opt (b : ℕ) :
    vasyuninCotSum 3 b =
      (Int.fract ((b : ℝ) / 3) - Int.fract (2 * (b : ℝ) / 3)) * (1 / √3) := by
  unfold vasyuninCotSum
  rw [show Finset.Ico 1 3 = ({1, 2} : Finset ℕ) by ext x; simp; omega,
    Finset.sum_insert (by decide), Finset.sum_singleton]
  push_cast
  rw [show (1 : ℝ) * b / 3 = b / 3 by ring, show Real.pi * 1 / 3 = Real.pi / 3 by ring,
    show Real.pi * 2 / 3 = 2 * Real.pi / 3 by ring, cot_pi_div_three_opt, cot_two_pi_div_three_opt]
  ring

private lemma vasyuninCotSum_four_opt (b : ℕ) :
    vasyuninCotSum 4 b = Int.fract ((b : ℝ) / 4) - Int.fract (3 * (b : ℝ) / 4) := by
  unfold vasyuninCotSum
  rw [show Finset.Ico 1 4 = ({1, 2, 3} : Finset ℕ) by ext x; simp; omega,
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  push_cast
  rw [show (1 : ℝ) * b / 4 = b / 4 by ring, show Real.pi * 1 / 4 = Real.pi / 4 by ring,
    show Real.pi * 2 / 4 = Real.pi / 2 by ring, Real.cos_pi_div_two, zero_div, mul_zero,
    show Real.pi * 3 / 4 = 3 * Real.pi / 4 by ring, cot_pi_div_four_opt,
    show Real.cos (3 * Real.pi / 4) / Real.sin (3 * Real.pi / 4) = -1 by
      rw [show 3 * Real.pi / 4 = Real.pi - Real.pi / 4 by ring, Real.cos_pi_sub, Real.sin_pi_sub,
        neg_div, cot_pi_div_four_opt]]
  ring

private lemma vasyuninGCot_one_two_opt : vasyuninGCot 1 2 = 0 := by
  have hV1 : vasyuninCotSum 1 2 = 0 := by simp [vasyuninCotSum]
  unfold vasyuninGCot; rw [hV1, vasyuninCotSum_two_opt]; ring

private lemma vasyuninGCot_one_three_opt : vasyuninGCot 1 3 = Real.pi / (18 * √3) := by
  have hV1 : vasyuninCotSum 1 3 = 0 := by simp [vasyuninCotSum]
  unfold vasyuninGCot; rw [hV1, vasyuninCotSum_three_opt]; norm_num; ring

private lemma vasyuninGCot_one_four_opt : vasyuninGCot 1 4 = Real.pi / 16 := by
  have hV1 : vasyuninCotSum 1 4 = 0 := by simp [vasyuninCotSum]
  unfold vasyuninGCot; rw [hV1, vasyuninCotSum_four_opt]; norm_num; ring

private lemma vasyuninGCot_two_three_opt : vasyuninGCot 2 3 = -(Real.pi / (36 * √3)) := by
  unfold vasyuninGCot; rw [vasyuninCotSum_two_opt, vasyuninCotSum_three_opt]; norm_num; ring

private lemma vasyuninGCot_two_four_opt : vasyuninGCot 2 4 = 0 := by
  unfold vasyuninGCot; rw [vasyuninCotSum_two_opt, vasyuninCotSum_four_opt]; norm_num

private lemma vasyuninGCot_three_four_opt :
    vasyuninGCot 3 4 = Real.pi / (72 * √3) - Real.pi / 48 := by
  unfold vasyuninGCot; rw [vasyuninCotSum_three_opt, vasyuninCotSum_four_opt]; norm_num; ring

/-- Exact cotangent quadratic energy of the second harmonic wavelet `(0, 2, -6, 4)` at `N = 4`:
`QCot vasyuninGCot (harmonicWavelet 2) 4 = π`. -/
theorem QCot_harmonicWavelet_two_eq :
    QCot vasyuninGCot (harmonicWavelet 2) 4 = Real.pi := by
  unfold QCot
  simp_rw [sum_Icc_one_four_opt]
  rw [vasyuninGCot_diag 1, vasyuninGCot_diag 2, vasyuninGCot_diag 3, vasyuninGCot_diag 4,
    vasyuninGCot_comm 2 1, vasyuninGCot_comm 3 1, vasyuninGCot_comm 4 1,
    vasyuninGCot_comm 3 2, vasyuninGCot_comm 4 2, vasyuninGCot_comm 4 3,
    vasyuninGCot_one_two_opt, vasyuninGCot_one_three_opt, vasyuninGCot_one_four_opt,
    vasyuninGCot_two_three_opt, vasyuninGCot_two_four_opt, vasyuninGCot_three_four_opt]
  simp [harmonicWavelet]
  ring

/-- Exact 2-wavelet orthogonal diagonalization of `SCot` on `A_4`: completing the two squares in
`t₁ - t₂` and `t₂` around the global KKT optimum `((19 + √3) / 72) * π`. -/
theorem SCot_cBaseAnchor_add_two_wavelets_eq (t₁ t₂ : ℝ) :
    SCot vasyuninGCot
        (fun k => cBaseAnchor k + t₁ * harmonicWavelet 1 k + t₂ * harmonicWavelet 2 k) 4 =
      ((19 + Real.sqrt 3) / 72) * Real.pi -
        (Real.pi / Real.sqrt 3) * ((t₁ - t₂) - 2 / 3) ^ 2 -
          Real.pi * (1 - 1 / Real.sqrt 3) * (t₂ - (5 - Real.sqrt 3) / 12) ^ 2 := by
  have hsq3_ne : Real.sqrt 3 ≠ 0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  have hsq3_sq : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  unfold SCot QCot
  simp_rw [sum_Icc_one_four_opt]
  rw [vasyuninGCot_diag 1, vasyuninGCot_diag 2, vasyuninGCot_diag 3, vasyuninGCot_diag 4,
    vasyuninGCot_comm 2 1, vasyuninGCot_comm 3 1, vasyuninGCot_comm 4 1,
    vasyuninGCot_comm 3 2, vasyuninGCot_comm 4 2, vasyuninGCot_comm 4 3,
    vasyuninGCot_one_two_opt, vasyuninGCot_one_three_opt, vasyuninGCot_one_four_opt,
    vasyuninGCot_two_three_opt, vasyuninGCot_two_four_opt, vasyuninGCot_three_four_opt]
  simp [cBaseAnchor, harmonicWavelet]
  field_simp [hsq3_ne]
  ring_nf
  have hsq3_3 : Real.sqrt 3 ^ 3 = 3 * Real.sqrt 3 := by rw [pow_succ, hsq3_sq]
  simp only [hsq3_sq, hsq3_3]
  ring

/-- Exact closed-form global KKT optimizer on `A_4` in `2`-wavelet coordinates. -/
noncomputable def cGlobalOptFour (k : ℕ) : ℝ :=
  cBaseAnchor k + ((13 - Real.sqrt 3) / 12) * harmonicWavelet 1 k +
    ((5 - Real.sqrt 3) / 12) * harmonicWavelet 2 k

/-- Exact verification that the global KKT optimizer `cGlobalOptFour` lies in `A_4`. -/
theorem cGlobalOptFour_mem_A_N : D1 cGlobalOptFour 4 = 0 ∧ D0 cGlobalOptFour 4 = 2 := by
  unfold D1 D0
  rw [sum_Icc_one_four_opt, sum_Icc_one_four_opt]
  norm_num [cGlobalOptFour, cBaseAnchor, harmonicWavelet]
  constructor <;> ring

/-- Exact closed-form maximum of `SCot` on `A_4`: `((19 + √3) / 72) * π`. -/
theorem SCot_cGlobalOptFour_eq :
    SCot vasyuninGCot cGlobalOptFour 4 = ((19 + Real.sqrt 3) / 72) * Real.pi := by
  have h := SCot_cBaseAnchor_add_two_wavelets_eq
    ((13 - Real.sqrt 3) / 12) ((5 - Real.sqrt 3) / 12)
  have hfn :
      (fun k => cBaseAnchor k + ((13 - Real.sqrt 3) / 12) * harmonicWavelet 1 k +
        ((5 - Real.sqrt 3) / 12) * harmonicWavelet 2 k) = cGlobalOptFour := rfl
  rw [hfn] at h
  rw [h]
  ring

/-- Global optimality upper bound for `SCot` over all of `A_4`: every vector `c ∈ A_4` satisfies
`SCot vasyuninGCot c 4 ≤ ((19 + √3) / 72) * π`. -/
theorem SCot_le_cGlobalOptFour_of_mem_A_four (c : ℕ → ℝ)
    (hc1 : D1 c 4 = 0) (hc0 : D0 c 4 = 2) :
    SCot vasyuninGCot c 4 ≤ ((19 + Real.sqrt 3) / 72) * Real.pi := by
  let t₁ := c 1 + 2
  let t₂ := c 4 / 4
  have heq :
      SCot vasyuninGCot c 4 =
        SCot vasyuninGCot
          (fun k => cBaseAnchor k + t₁ * harmonicWavelet 1 k + t₂ * harmonicWavelet 2 k) 4 := by
    unfold SCot QCot
    congr 1
    refine Finset.sum_congr rfl fun j hj => Finset.sum_congr rfl fun k hk => ?_
    rw [eq_cBaseAnchor_add_wavelets_of_mem_A_four c hc1 hc0 hj,
      eq_cBaseAnchor_add_wavelets_of_mem_A_four c hc1 hc0 hk]
  rw [heq, SCot_cBaseAnchor_add_two_wavelets_eq t₁ t₂]
  have hsq3_gt : (1 : ℝ) < Real.sqrt 3 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3), Real.sqrt_nonneg 3]
  have h1_nn : 0 ≤ (Real.pi / Real.sqrt 3) * ((t₁ - t₂) - 2 / 3) ^ 2 := by positivity
  have h2_nn :
      0 ≤ Real.pi * (1 - 1 / Real.sqrt 3) * (t₂ - (5 - Real.sqrt 3) / 12) ^ 2 := by
    have hcoeff : 0 ≤ 1 - 1 / Real.sqrt 3 := by
      have : 1 / Real.sqrt 3 < 1 := (div_lt_one (by linarith)).mpr hsq3_gt
      linarith
    have hpi : 0 ≤ Real.pi := Real.pi_pos.le
    positivity
  linarith

/-- Global Nyman–Beurling `L²(0, 1)` lower bound over all of `A_4`: no vector in `A_4` achieves an
`L²(0, 1)` distance below `1 - ((19 + √3) / 72) * π`. -/
theorem l2_dist_cGlobalOptFour_le_of_mem_A_four (c : ℕ → ℝ)
    (hc1 : D1 c 4 = 0) (hc0 : D0 c 4 = 2) :
    1 - ((19 + Real.sqrt 3) / 72) * Real.pi ≤
      ∫ x in (0 : ℝ)..1, (1 - ∑ k ∈ Finset.Icc 1 4, c k * recipFractScaled k x) ^ 2 := by
  rw [affine_l2_dist_eq_one_sub_scot c hc1 hc0]
  exact sub_le_sub_left (SCot_le_cGlobalOptFour_of_mem_A_four c hc1 hc0) 1
