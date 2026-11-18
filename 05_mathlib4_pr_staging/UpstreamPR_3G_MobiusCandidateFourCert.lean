/-
Copyright (c) 2026 Qamar Munawer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qamar Munawer
-/
module

public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.NumberTheory.ArithmeticFunction.Moebius
public import RiemannBlueprint.UpstreamPRs.UpstreamPR_3F_VasyuninCrossIntegral

/-!
# Constructive Mollified Möbius Candidate and Exact `N = 4` `L²(0, 1)` Certificate

This file defines the canonical Báez-Duarte / Nyman–Beurling projected Möbius candidate
`cCandidateMobius N = projectAffine (mollifiedMobius N) N`, proves unconditional affine
manifold membership for `2 ≤ N`, and establishes the exact closed-form `N = 4` evaluation
and strict positivity certificate `0 < ∫₀¹ (1 - ∑_{k=1}^4 c_k {1/(kx)})² dx`.
-/

@[expose] public section

/-- Quadratic mollified Möbius weights `u_mob(k, N) = -μ(k) * (1 - k / N) ^ 2`. -/
noncomputable def mollifiedMobius (N : ℕ) (k : ℕ) : ℝ :=
  -(ArithmeticFunction.moebius k : ℝ) * (1 - (k : ℝ) / (N : ℝ)) ^ 2

/-- Canonical constructive Báez-Duarte candidate `c_mob(N) = projectAffine (mollifiedMobius N) N`.
-/
noncomputable def cCandidateMobius (N : ℕ) : ℕ → ℝ :=
  projectAffine (mollifiedMobius N) N

/-- Unconditional Báez-Duarte affine manifold membership for `cCandidateMobius N` (`2 ≤ N`). -/
theorem cCandidateMobius_mem_A_N_uncond {N : ℕ} (hN : 2 ≤ N) :
    D1 (cCandidateMobius N) N = 0 ∧ D0 (cCandidateMobius N) N = 2 :=
  projectAffine_mem_A_N_uncond (mollifiedMobius N) hN

private lemma sum_Icc_one_four (f : ℕ → ℝ) :
    ∑ k ∈ Finset.Icc 1 4, f k = f 1 + f 2 + f 3 + f 4 := by
  rw [show Finset.Icc 1 4 = ({1, 2, 3, 4} : Finset ℕ) by
    ext x; simp only [Finset.mem_Icc, Finset.mem_insert, Finset.mem_singleton]; omega]
  norm_num [Finset.sum_insert, add_assoc]

/-- Exact rational evaluation of `mollifiedMobius 4` on `{1, 2, 3, 4}`. -/
theorem mollifiedMobius_four_eval :
    mollifiedMobius 4 1 = -9 / 16 ∧
    mollifiedMobius 4 2 = 1 / 4 ∧
    mollifiedMobius 4 3 = 1 / 16 ∧
    mollifiedMobius 4 4 = 0 := by
  have hm1 : ArithmeticFunction.moebius 1 = 1 := ArithmeticFunction.moebius_apply_one
  have hm2 : ArithmeticFunction.moebius 2 = -1 :=
    ArithmeticFunction.moebius_apply_prime Nat.prime_two
  have hm3 : ArithmeticFunction.moebius 3 = -1 :=
    ArithmeticFunction.moebius_apply_prime Nat.prime_three
  have hm4 : ArithmeticFunction.moebius 4 = 0 := by
    rw [show (4 : ℕ) = 2 ^ 2 by norm_num,
      ArithmeticFunction.moebius_apply_prime_pow Nat.prime_two (by norm_num)]
    simp
  refine ⟨?_, ?_, ?_, ?_⟩ <;> dsimp [mollifiedMobius]
  · rw [hm1]; norm_num
  · rw [hm2]; norm_num
  · rw [hm3]; norm_num
  · rw [hm4]; norm_num

/-- Exact rational evaluation of `cCandidateMobius 4` on `{1, 2, 3, 4}`. -/
theorem cCandidateMobius_four_eval :
    cCandidateMobius 4 1 = -667 / 624 ∧
    cCandidateMobius 4 2 = 67 / 78 ∧
    cCandidateMobius 4 3 = 217 / 208 ∧
    cCandidateMobius 4 4 = 7 / 6 := by
  rcases mollifiedMobius_four_eval with ⟨hu1, hu2, hu3, hu4⟩
  have hU1 : (∑ k ∈ Finset.Icc 1 4, mollifiedMobius 4 k / (k : ℝ)) = -5 / 12 := by
    rw [sum_Icc_one_four, hu1, hu2, hu3, hu4]; norm_num
  have hU0 : (∑ k ∈ Finset.Icc 1 4, mollifiedMobius 4 k) = -1 / 4 := by
    rw [sum_Icc_one_four, hu1, hu2, hu3, hu4]; norm_num
  have hlam1 : lambda1 (mollifiedMobius 4) 4 = 29 / 13 := by
    unfold lambda1; rw [hU1, hU0, HSum_four, DeltaDet_four]; norm_num
  have hlam0 : lambda0 (mollifiedMobius 4) 4 = -269 / 156 := by
    unfold lambda0; rw [hU1, hU0, HSum_four, S2Sum_four, DeltaDet_four]; norm_num
  refine ⟨?_, ?_, ?_, ?_⟩ <;> dsimp [cCandidateMobius, projectAffine]
  · rw [hu1, hlam1, hlam0]; norm_num
  · rw [hu2, hlam1, hlam0]; norm_num
  · rw [hu3, hlam1, hlam0]; norm_num
  · rw [hu4, hlam1, hlam0]; norm_num

private lemma vasyuninCotSum_two (b : ℕ) : vasyuninCotSum 2 b = 0 := by
  unfold vasyuninCotSum
  rw [show Finset.Ico 1 2 = ({1} : Finset ℕ) by ext x; simp, Finset.sum_singleton,
    show Real.pi * ((1 : ℕ) : ℝ) / ((2 : ℕ) : ℝ) = Real.pi / 2 by push_cast; ring,
    Real.cos_pi_div_two, zero_div, mul_zero]

private lemma cot_pi_div_three : Real.cos (Real.pi / 3) / Real.sin (Real.pi / 3) = 1 / √3 := by
  rw [Real.cos_pi_div_three, Real.sin_pi_div_three]
  field_simp [(Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 3)).ne']

private lemma cot_two_pi_div_three :
    Real.cos (2 * Real.pi / 3) / Real.sin (2 * Real.pi / 3) = -(1 / √3) := by
  rw [show 2 * Real.pi / 3 = Real.pi - Real.pi / 3 by ring, Real.cos_pi_sub, Real.sin_pi_sub,
    neg_div, cot_pi_div_three]

private lemma cot_pi_div_four : Real.cos (Real.pi / 4) / Real.sin (Real.pi / 4) = 1 := by
  rw [Real.cos_pi_div_four, Real.sin_pi_div_four]
  field_simp [(Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)).ne']

private lemma cot_three_pi_div_four :
    Real.cos (3 * Real.pi / 4) / Real.sin (3 * Real.pi / 4) = -1 := by
  rw [show 3 * Real.pi / 4 = Real.pi - Real.pi / 4 by ring, Real.cos_pi_sub, Real.sin_pi_sub,
    neg_div, cot_pi_div_four]

private lemma vasyuninCotSum_three (b : ℕ) :
    vasyuninCotSum 3 b =
      (Int.fract ((b : ℝ) / 3) - Int.fract (2 * (b : ℝ) / 3)) * (1 / √3) := by
  unfold vasyuninCotSum
  rw [show Finset.Ico 1 3 = ({1, 2} : Finset ℕ) by ext x; simp; omega,
    Finset.sum_insert (by decide), Finset.sum_singleton]
  push_cast
  rw [show (1 : ℝ) * b / 3 = b / 3 by ring, show Real.pi * 1 / 3 = Real.pi / 3 by ring,
    show Real.pi * 2 / 3 = 2 * Real.pi / 3 by ring, cot_pi_div_three, cot_two_pi_div_three]
  ring

private lemma vasyuninCotSum_four (b : ℕ) :
    vasyuninCotSum 4 b = Int.fract ((b : ℝ) / 4) - Int.fract (3 * (b : ℝ) / 4) := by
  unfold vasyuninCotSum
  rw [show Finset.Ico 1 4 = ({1, 2, 3} : Finset ℕ) by ext x; simp; omega,
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  push_cast
  rw [show (1 : ℝ) * b / 4 = b / 4 by ring, show Real.pi * 1 / 4 = Real.pi / 4 by ring,
    show Real.pi * 2 / 4 = Real.pi / 2 by ring, Real.cos_pi_div_two, zero_div, mul_zero,
    show Real.pi * 3 / 4 = 3 * Real.pi / 4 by ring, cot_pi_div_four, cot_three_pi_div_four]
  ring

/-- Exact closed-form formula for `SCot vasyuninGCot (cCandidateMobius 4) 4`. -/
theorem SCot_cCandidateMobius_four_eq :
    SCot vasyuninGCot (cCandidateMobius 4) 4 =
      ((119 : ℝ) / 576 + 54467 / (389376 * Real.sqrt 3)) * Real.pi := by
  rcases cCandidateMobius_four_eval with ⟨hc1, hc2, hc3, hc4⟩
  have hV1 : ∀ b : ℕ, vasyuninCotSum 1 b = 0 := fun _ => by simp [vasyuninCotSum]
  have hG12 : vasyuninGCot 1 2 = 0 := by unfold vasyuninGCot; rw [hV1, vasyuninCotSum_two]; ring
  have hG13 : vasyuninGCot 1 3 = Real.pi / (18 * √3) := by
    unfold vasyuninGCot; rw [hV1, vasyuninCotSum_three]; norm_num; ring
  have hG14 : vasyuninGCot 1 4 = Real.pi / 16 := by
    unfold vasyuninGCot; rw [hV1, vasyuninCotSum_four]; norm_num; ring
  have hG23 : vasyuninGCot 2 3 = -(Real.pi / (36 * √3)) := by
    unfold vasyuninGCot; rw [vasyuninCotSum_two, vasyuninCotSum_three]; norm_num; ring
  have hG24 : vasyuninGCot 2 4 = 0 := by
    unfold vasyuninGCot; rw [vasyuninCotSum_two, vasyuninCotSum_four]; norm_num
  have hG34 : vasyuninGCot 3 4 = Real.pi / (72 * √3) - Real.pi / 48 := by
    unfold vasyuninGCot; rw [vasyuninCotSum_three, vasyuninCotSum_four]; norm_num; ring
  unfold SCot QCot
  simp_rw [sum_Icc_one_four]
  rw [vasyuninGCot_diag 1, vasyuninGCot_diag 2, vasyuninGCot_diag 3, vasyuninGCot_diag 4,
    vasyuninGCot_comm 2 1, vasyuninGCot_comm 3 1, vasyuninGCot_comm 4 1,
    vasyuninGCot_comm 3 2, vasyuninGCot_comm 4 2, vasyuninGCot_comm 4 3,
    hG12, hG13, hG14, hG23, hG24, hG34, hc1, hc2, hc3, hc4]
  ring

/-- Exact continuous `L²(0, 1)` distance formula for `cCandidateMobius 4`. -/
theorem cCandidateMobius_four_l2_dist_eq :
    (∫ x in (0 : ℝ)..1,
      (1 - ∑ k ∈ Finset.Icc 1 4, cCandidateMobius 4 k * recipFractScaled k x) ^ 2) =
      1 - ((119 : ℝ) / 576 + 54467 / (389376 * Real.sqrt 3)) * Real.pi := by
  have hmem := cCandidateMobius_mem_A_N_uncond (by decide : 2 ≤ 4)
  rw [affine_l2_dist_eq_one_sub_scot (cCandidateMobius 4) hmem.1 hmem.2,
    SCot_cCandidateMobius_four_eq]

/-- Strictly positive finite-`N` Nyman–Beurling `L²(0, 1)` error certificate at `N = 4` for
`cCandidateMobius 4`. -/
theorem cCandidateMobius_four_l2_dist_pos :
    0 < (∫ x in (0 : ℝ)..1,
      (1 - ∑ k ∈ Finset.Icc 1 4, cCandidateMobius 4 k * recipFractScaled k x) ^ 2) := by
  rw [cCandidateMobius_four_l2_dist_eq]
  have hsq3_lo : (1.732 : ℝ) < Real.sqrt 3 := by
    have hnn := Real.sqrt_nonneg 3
    have hsq : Real.sqrt 3 * Real.sqrt 3 = 3 := Real.mul_self_sqrt (by norm_num)
    nlinarith
  have h_inv_hi : (1 : ℝ) / Real.sqrt 3 < 1 / 1.732 :=
    (one_div_lt_one_div (Real.sqrt_pos.mpr (by norm_num)) (by norm_num)).mpr hsq3_lo
  have h_inner : (119 : ℝ) / 576 + 54467 / (389376 * Real.sqrt 3) <
      (119 : ℝ) / 576 + 54467 / (389376 * 1.732) := by
    have hdiv : 54467 / (389376 * Real.sqrt 3) < 54467 / (389376 * 1.732) := by
      calc 54467 / (389376 * Real.sqrt 3) = (54467 / 389376) * (1 / Real.sqrt 3) := by ring
        _ < (54467 / 389376) * (1 / 1.732) := mul_lt_mul_of_pos_left h_inv_hi (by norm_num)
        _ = 54467 / (389376 * 1.732) := by ring
    linarith
  have h_term : ((119 : ℝ) / 576 + 54467 / (389376 * Real.sqrt 3)) * Real.pi <
      ((119 : ℝ) / 576 + 54467 / (389376 * 1.732)) * 3.1416 :=
    mul_lt_mul h_inner (le_of_lt Real.pi_lt_d4) Real.pi_pos (by positivity)
  have h_num : ((119 : ℝ) / 576 + 54467 / (389376 * 1.732)) * 3.1416 < 1 := by norm_num
  linarith
