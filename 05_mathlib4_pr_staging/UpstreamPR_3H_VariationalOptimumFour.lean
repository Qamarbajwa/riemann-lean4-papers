/-
Copyright (c) 2026 Qamar Munawer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qamar Munawer
-/
module

public import RiemannBlueprint.UpstreamPRs.UpstreamPR_3G_MobiusCandidateFourCert

/-!
# Constructive Variational Improvement Over Mollified Möbius on `A_4`

This file proves the general **Affine Cotangent Improvement Identity** on the Báez-Duarte affine
manifold `A_N = {c | D1 c N = 0 ∧ D0 c N = 2}` (`l2_dist_sub_eq_scot_sub` and
`l2_dist_lt_iff_scot_gt`) and exhibits an explicit rational vector `cVariationalFour` near the
exact KKT optimum on `A_4`:
  `(-21 / 20, 3 / 4, 6 / 5, 11 / 10)`.
Evaluating `SCot vasyuninGCot cVariationalFour 4` in closed form proves unconditionally that
`cCandidateMobius 4` is strictly suboptimal on `A_4` while `cVariationalFour` retains a strictly
positive `L²(0, 1)` Nyman–Beurling distance.
-/

@[expose] public section

/-- Exact `L²(0, 1)` difference identity for any two vectors `c, c' ∈ A_N`. -/
theorem l2_dist_sub_eq_scot_sub {N : ℕ} (c c' : ℕ → ℝ)
    (hc1 : D1 c N = 0) (hc0 : D0 c N = 2) (hc1' : D1 c' N = 0) (hc0' : D0 c' N = 2) :
    (∫ x in (0 : ℝ)..1, (1 - ∑ k ∈ Finset.Icc 1 N, c' k * recipFractScaled k x) ^ 2) -
      (∫ x in (0 : ℝ)..1, (1 - ∑ k ∈ Finset.Icc 1 N, c k * recipFractScaled k x) ^ 2) =
      SCot vasyuninGCot c N - SCot vasyuninGCot c' N := by
  rw [affine_l2_dist_eq_one_sub_scot c' hc1' hc0', affine_l2_dist_eq_one_sub_scot c hc1 hc0]
  ring

/-- Strictly smaller `L²(0, 1)` Nyman–Beurling distance on `A_N` holds iff `SCot` is strictly
larger. -/
theorem l2_dist_lt_iff_scot_gt {N : ℕ} (c c' : ℕ → ℝ)
    (hc1 : D1 c N = 0) (hc0 : D0 c N = 2) (hc1' : D1 c' N = 0) (hc0' : D0 c' N = 2) :
    (∫ x in (0 : ℝ)..1, (1 - ∑ k ∈ Finset.Icc 1 N, c' k * recipFractScaled k x) ^ 2) <
      (∫ x in (0 : ℝ)..1, (1 - ∑ k ∈ Finset.Icc 1 N, c k * recipFractScaled k x) ^ 2) ↔
      SCot vasyuninGCot c N < SCot vasyuninGCot c' N := by
  rw [affine_l2_dist_eq_one_sub_scot c' hc1' hc0', affine_l2_dist_eq_one_sub_scot c hc1 hc0]
  exact sub_lt_sub_iff_left 1

/-- Explicit rational variational improvement vector on `{1, 2, 3, 4}` approximating the exact
KKT optimum on `A_4`. -/
noncomputable def cVariationalFour : ℕ → ℝ
  | 1 => -21 / 20
  | 2 => 3 / 4
  | 3 => 6 / 5
  | 4 => 11 / 10
  | _ => 0

private lemma sum_Icc_one_four_var (f : ℕ → ℝ) :
    ∑ k ∈ Finset.Icc 1 4, f k = f 1 + f 2 + f 3 + f 4 := by
  rw [show Finset.Icc 1 4 = ({1, 2, 3, 4} : Finset ℕ) by
    ext x; simp only [Finset.mem_Icc, Finset.mem_insert, Finset.mem_singleton]; omega]
  norm_num [Finset.sum_insert, add_assoc]

/-- Exact rational verification that `cVariationalFour` lies in `A_4`. -/
theorem cVariationalFour_mem_A_N :
    D1 cVariationalFour 4 = 0 ∧ D0 cVariationalFour 4 = 2 := by
  unfold D1 D0
  rw [sum_Icc_one_four_var, sum_Icc_one_four_var]
  norm_num [cVariationalFour]

private lemma cot_pi_div_three_var : Real.cos (Real.pi / 3) / Real.sin (Real.pi / 3) = 1 / √3 := by
  rw [Real.cos_pi_div_three, Real.sin_pi_div_three]
  field_simp [(Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 3)).ne']

private lemma cot_two_pi_div_three_var :
    Real.cos (2 * Real.pi / 3) / Real.sin (2 * Real.pi / 3) = -(1 / √3) := by
  rw [show 2 * Real.pi / 3 = Real.pi - Real.pi / 3 by ring, Real.cos_pi_sub, Real.sin_pi_sub,
    neg_div, cot_pi_div_three_var]

private lemma cot_pi_div_four_var : Real.cos (Real.pi / 4) / Real.sin (Real.pi / 4) = 1 := by
  rw [Real.cos_pi_div_four, Real.sin_pi_div_four]
  field_simp [(Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)).ne']

private lemma vasyuninCotSum_two_var (b : ℕ) : vasyuninCotSum 2 b = 0 := by
  unfold vasyuninCotSum
  rw [show Finset.Ico 1 2 = ({1} : Finset ℕ) by ext x; simp, Finset.sum_singleton,
    show Real.pi * ((1 : ℕ) : ℝ) / ((2 : ℕ) : ℝ) = Real.pi / 2 by push_cast; ring,
    Real.cos_pi_div_two, zero_div, mul_zero]

private lemma vasyuninCotSum_three_var (b : ℕ) :
    vasyuninCotSum 3 b =
      (Int.fract ((b : ℝ) / 3) - Int.fract (2 * (b : ℝ) / 3)) * (1 / √3) := by
  unfold vasyuninCotSum
  rw [show Finset.Ico 1 3 = ({1, 2} : Finset ℕ) by ext x; simp; omega,
    Finset.sum_insert (by decide), Finset.sum_singleton]
  push_cast
  rw [show (1 : ℝ) * b / 3 = b / 3 by ring, show Real.pi * 1 / 3 = Real.pi / 3 by ring,
    show Real.pi * 2 / 3 = 2 * Real.pi / 3 by ring, cot_pi_div_three_var, cot_two_pi_div_three_var]
  ring

private lemma vasyuninCotSum_four_var (b : ℕ) :
    vasyuninCotSum 4 b = Int.fract ((b : ℝ) / 4) - Int.fract (3 * (b : ℝ) / 4) := by
  unfold vasyuninCotSum
  rw [show Finset.Ico 1 4 = ({1, 2, 3} : Finset ℕ) by ext x; simp; omega,
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  push_cast
  rw [show (1 : ℝ) * b / 4 = b / 4 by ring, show Real.pi * 1 / 4 = Real.pi / 4 by ring,
    show Real.pi * 2 / 4 = Real.pi / 2 by ring, Real.cos_pi_div_two, zero_div, mul_zero,
    show Real.pi * 3 / 4 = 3 * Real.pi / 4 by ring, cot_pi_div_four_var,
    show Real.cos (3 * Real.pi / 4) / Real.sin (3 * Real.pi / 4) = -1 by
      rw [show 3 * Real.pi / 4 = Real.pi - Real.pi / 4 by ring, Real.cos_pi_sub, Real.sin_pi_sub,
        neg_div, cot_pi_div_four_var]]
  ring

/-- Exact closed-form evaluation of `SCot vasyuninGCot cVariationalFour 4` in terms of `π` and
`√3`. -/
theorem SCot_cVariationalFour_eq :
    SCot vasyuninGCot cVariationalFour 4 =
      ((319 : ℝ) / 1600 + 23 / (150 * Real.sqrt 3)) * Real.pi := by
  have hV1 : ∀ b : ℕ, vasyuninCotSum 1 b = 0 := fun _ => by simp [vasyuninCotSum]
  have hG12 : vasyuninGCot 1 2 = 0 := by
    unfold vasyuninGCot; rw [hV1, vasyuninCotSum_two_var]; ring
  have hG13 : vasyuninGCot 1 3 = Real.pi / (18 * √3) := by
    unfold vasyuninGCot; rw [hV1, vasyuninCotSum_three_var]; norm_num; ring
  have hG14 : vasyuninGCot 1 4 = Real.pi / 16 := by
    unfold vasyuninGCot; rw [hV1, vasyuninCotSum_four_var]; norm_num; ring
  have hG23 : vasyuninGCot 2 3 = -(Real.pi / (36 * √3)) := by
    unfold vasyuninGCot; rw [vasyuninCotSum_two_var, vasyuninCotSum_three_var]; norm_num; ring
  have hG24 : vasyuninGCot 2 4 = 0 := by
    unfold vasyuninGCot; rw [vasyuninCotSum_two_var, vasyuninCotSum_four_var]; norm_num
  have hG34 : vasyuninGCot 3 4 = Real.pi / (72 * √3) - Real.pi / 48 := by
    unfold vasyuninGCot; rw [vasyuninCotSum_three_var, vasyuninCotSum_four_var]; norm_num; ring
  unfold SCot QCot
  simp_rw [sum_Icc_one_four_var]
  rw [vasyuninGCot_diag 1, vasyuninGCot_diag 2, vasyuninGCot_diag 3, vasyuninGCot_diag 4,
    vasyuninGCot_comm 2 1, vasyuninGCot_comm 3 1, vasyuninGCot_comm 4 1,
    vasyuninGCot_comm 3 2, vasyuninGCot_comm 4 2, vasyuninGCot_comm 4 3,
    hG12, hG13, hG14, hG23, hG24, hG34]
  norm_num [cVariationalFour]
  ring

/-- Unconditional strict suboptimality of `cCandidateMobius 4`: `cVariationalFour` achieves a
strictly larger cotangent score on `A_4`. -/
theorem SCot_cCandidateMobius_four_lt_cVariationalFour :
    SCot vasyuninGCot (cCandidateMobius 4) 4 < SCot vasyuninGCot cVariationalFour 4 := by
  rw [SCot_cCandidateMobius_four_eq, SCot_cVariationalFour_eq]
  refine mul_lt_mul_of_pos_right ?_ Real.pi_pos
  have hsq : Real.sqrt 3 * Real.sqrt 3 = 3 := Real.mul_self_sqrt (by norm_num)
  have hsq3_lo : (1.732 : ℝ) < Real.sqrt 3 := by
    have hnn := Real.sqrt_nonneg 3; nlinarith
  have hsq3_hi : Real.sqrt 3 < 1.7321 := by nlinarith
  have h_inv_hi : (1 : ℝ) / Real.sqrt 3 < 1 / 1.732 :=
    (one_div_lt_one_div (Real.sqrt_pos.mpr (by norm_num)) (by norm_num)).mpr hsq3_lo
  have h_inv_lo : (1 : ℝ) / 1.7321 < 1 / Real.sqrt 3 :=
    (one_div_lt_one_div (by norm_num) (Real.sqrt_pos.mpr (by norm_num))).mpr hsq3_hi
  have h1 : (119 : ℝ) / 576 + 54467 / (389376 * Real.sqrt 3) <
      (119 : ℝ) / 576 + 54467 / (389376 * 1.732) := by
    have := mul_lt_mul_of_pos_left h_inv_hi (by norm_num : (0 : ℝ) < 54467 / 389376)
    linarith [show (54467 : ℝ) / (389376 * Real.sqrt 3) = (54467 / 389376) * (1 / Real.sqrt 3) by
      ring, show (54467 : ℝ) / (389376 * 1.732) = (54467 / 389376) * (1 / 1.732) by ring]
  have h2 : (319 : ℝ) / 1600 + 23 / (150 * 1.7321) <
      (319 : ℝ) / 1600 + 23 / (150 * Real.sqrt 3) := by
    have := mul_lt_mul_of_pos_left h_inv_lo (by norm_num : (0 : ℝ) < 23 / 150)
    linarith [show (23 : ℝ) / (150 * Real.sqrt 3) = (23 / 150) * (1 / Real.sqrt 3) by ring,
      show (23 : ℝ) / (150 * 1.7321) = (23 / 150) * (1 / 1.7321) by ring]
  have h_num : (119 : ℝ) / 576 + 54467 / (389376 * 1.732) <
      (319 : ℝ) / 1600 + 23 / (150 * 1.7321) := by norm_num
  linarith

/-- Strict `L²(0, 1)` Nyman–Beurling distance improvement of `cVariationalFour` over
`cCandidateMobius 4` on `A_4`. -/
theorem l2_dist_cVariationalFour_lt_cCandidateMobius_four :
    (∫ x in (0 : ℝ)..1,
      (1 - ∑ k ∈ Finset.Icc 1 4, cVariationalFour k * recipFractScaled k x) ^ 2) <
      (∫ x in (0 : ℝ)..1,
        (1 - ∑ k ∈ Finset.Icc 1 4, cCandidateMobius 4 k * recipFractScaled k x) ^ 2) := by
  have hm := cCandidateMobius_mem_A_N_uncond (by decide : 2 ≤ 4)
  have hv := cVariationalFour_mem_A_N
  exact (l2_dist_lt_iff_scot_gt (cCandidateMobius 4) cVariationalFour hm.1 hm.2 hv.1 hv.2).mpr
    SCot_cCandidateMobius_four_lt_cVariationalFour

/-- Strictly positive finite-`N` `L²(0, 1)` Nyman–Beurling error certificate for
`cVariationalFour` on `A_4`. -/
theorem cVariationalFour_l2_dist_pos :
    0 < (∫ x in (0 : ℝ)..1,
      (1 - ∑ k ∈ Finset.Icc 1 4, cVariationalFour k * recipFractScaled k x) ^ 2) := by
  have hv := cVariationalFour_mem_A_N
  rw [affine_l2_dist_eq_one_sub_scot cVariationalFour hv.1 hv.2, SCot_cVariationalFour_eq]
  have hsq3_lo : (1.732 : ℝ) < Real.sqrt 3 := by
    have hnn := Real.sqrt_nonneg 3
    have hsq : Real.sqrt 3 * Real.sqrt 3 = 3 := Real.mul_self_sqrt (by norm_num)
    nlinarith
  have h_inv_hi : (1 : ℝ) / Real.sqrt 3 < 1 / 1.732 :=
    (one_div_lt_one_div (Real.sqrt_pos.mpr (by norm_num)) (by norm_num)).mpr hsq3_lo
  have h_inner : (319 : ℝ) / 1600 + 23 / (150 * Real.sqrt 3) <
      (319 : ℝ) / 1600 + 23 / (150 * 1.732) := by
    have := mul_lt_mul_of_pos_left h_inv_hi (by norm_num : (0 : ℝ) < 23 / 150)
    linarith [show (23 : ℝ) / (150 * Real.sqrt 3) = (23 / 150) * (1 / Real.sqrt 3) by ring,
      show (23 : ℝ) / (150 * 1.732) = (23 / 150) * (1 / 1.732) by ring]
  have h_term : ((319 : ℝ) / 1600 + 23 / (150 * Real.sqrt 3)) * Real.pi <
      ((319 : ℝ) / 1600 + 23 / (150 * 1.732)) * 3.1416 :=
    mul_lt_mul h_inner (le_of_lt Real.pi_lt_d4) Real.pi_pos (by positivity)
  have h_num : ((319 : ℝ) / 1600 + 23 / (150 * 1.732)) * 3.1416 < 1 := by norm_num
  linarith
