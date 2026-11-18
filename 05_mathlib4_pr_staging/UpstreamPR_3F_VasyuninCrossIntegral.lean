/-
Copyright (c) 2026 Qamar Munawer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qamar Munawer
-/
module

public import RiemannBlueprint.UpstreamPRs.UpstreamPR_3C_HarmonicCellAndAbelSum
public import RiemannBlueprint.UpstreamPRs.UpstreamPR_3D_StirlingAndHarmonicAsymptotics
public import RiemannBlueprint.UpstreamPRs.UpstreamPR_3E_CotangentMittagLefflerLimit

/-!
# Vasyunin Cross-Integral and Unconditional Affine L² Pure Cotangent Bridge

This file combines the discrete Abel partial identity (`cross_partial_exact_identity`),
Stirling/harmonic asymptotics (`tendsto_stirling_log_term`, `tendsto_harmonic_Ico_sub_log`),
and the Mittag-Leffler cotangent limit (`tendsto_cotApproxSum`) to prove:
1. `intervalIntegral_recipFractScaled_cross`: the unconditional Vasyunin cross-integral for all
   `1 ≤ j, k`.
2. `affine_l2_pure_cotangent_bridge`: exact reduction of the Nyman–Beurling `L²(0, 1)` error to
   `1 + QCot vasyuninGCot c N` on `{c | D1 c N = 0 ∧ D0 c N = 2}`.
3. `affine_l2_dist_eq_one_sub_scot` and `projectAffine_l2_dist_eq_one_sub_scot`.
-/

@[expose] public section

open Filter MeasureTheory Finset

/-- **Vasyunin (1995) Cross-Integral Theorem** (unconditional): for all `1 ≤ j, k`,
`∫₀¹ {1/(j x)} {1/(k x)} dx = GSmooth Real.eulerMascheroniConstant j k + vasyuninGCot j k`. -/
theorem intervalIntegral_recipFractScaled_cross {j k : ℕ} (hj : 1 ≤ j) (hk : 1 ≤ k) :
    (∫ x in (0 : ℝ)..1, recipFractScaled j x * recipFractScaled k x) =
      GSmooth Real.eulerMascheroniConstant j k + vasyuninGCot j k := by
  have hj_pos : (0 : ℝ) < (j : ℝ) := Nat.cast_pos.mpr hj
  have hk_pos : (0 : ℝ) < (k : ℝ) := Nat.cast_pos.mpr hk
  have h_inv_L : Tendsto (fun M : ℕ => 1 / ((M : ℝ) * (j : ℝ) * (k : ℝ))) atTop (nhds 0) := by
    have h_top : Tendsto (fun M : ℕ => (M : ℝ) * (j : ℝ) * (k : ℝ)) atTop atTop :=
      (tendsto_natCast_atTop_atTop.atTop_mul_const hj_pos).atTop_mul_const hk_pos
    simpa [Function.comp_def, one_div, mul_inv] using tendsto_inv_atTop_zero.comp h_top
  let L_rhs : ℝ :=
    (1 / (k : ℝ)) * ((1 / 2 : ℝ) * Real.log (2 * Real.pi)) +
    (1 / (j : ℝ)) * ((1 / 2 : ℝ) * Real.log (2 * Real.pi)) -
    (1 / (2 * (j : ℝ))) * Real.eulerMascheroniConstant -
    (1 / (2 * (k : ℝ))) * Real.eulerMascheroniConstant +
    (((j : ℝ) - (k : ℝ)) * Real.log ((k : ℝ) / (j : ℝ)) - 2) / (2 * (j : ℝ) * (k : ℝ)) - 0 -
    (1 / (2 * (j : ℝ))) * ((Real.pi / (k : ℝ)) * vasyuninCotSum k j) -
    (1 / (2 * (k : ℝ))) * ((Real.pi / (j : ℝ)) * vasyuninCotSum j k)
  have h_main_lim : Tendsto (fun M : ℕ =>
        ∫ x in (1 / ((M * j * k : ℕ) : ℝ))..1, recipFractScaled j x * recipFractScaled k x)
      atTop (nhds L_rhs) := by
    have h_comb := (((((((((tendsto_stirling_log_term hk).const_mul (1 / (k : ℝ))).add
      ((tendsto_stirling_log_term hj).const_mul (1 / (j : ℝ)))).sub
      ((tendsto_harmonic_Ico_sub_log hk).const_mul (1 / (2 * (j : ℝ))))).sub
      ((tendsto_harmonic_Ico_sub_log hj).const_mul (1 / (2 * (k : ℝ))))).add
      (tendsto_const_nhds (x := (((j : ℝ) - (k : ℝ)) * Real.log ((k : ℝ) / (j : ℝ)) - 2) /
        (2 * (j : ℝ) * (k : ℝ))))).sub h_inv_L).sub
      ((tendsto_cotApproxSum j k).const_mul (1 / (2 * (j : ℝ))))).sub
      ((tendsto_cotApproxSum k j).const_mul (1 / (2 * (k : ℝ)))))
    refine h_comb.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with M hM
    rw [← sum_Ico_fract_diff_div_eq_cotApproxSum hk, ← sum_Ico_fract_diff_div_eq_cotApproxSum hj]
    exact (cross_partial_exact_identity hM hj hk).symm
  have h_lim_tail : Tendsto (fun M : ℕ => 1 / ((M * j * k : ℕ) : ℝ)) atTop (nhds 0) := by
    push_cast; exact h_inv_L
  have h_zero_lim : Tendsto (fun M : ℕ => ∫ x in (0 : ℝ)..(1 / ((M * j * k : ℕ) : ℝ)),
        recipFractScaled j x * recipFractScaled k x) atTop (nhds 0) := by
    refine squeeze_zero_norm' (Eventually.of_forall fun M => ?_) h_lim_tail
    have hbd : ∀ x ∈ Set.uIoc (0 : ℝ) (1 / ((M * j * k : ℕ) : ℝ)),
        ‖recipFractScaled j x * recipFractScaled k x‖ ≤ (1 : ℝ) := fun x _ => by
      dsimp only [recipFractScaled]
      have h1 := Int.fract_nonneg (1 / ((j : ℝ) * x))
      have h2 := Int.fract_lt_one (1 / ((j : ℝ) * x))
      have h3 := Int.fract_nonneg (1 / ((k : ℝ) * x))
      have h4 := Int.fract_lt_one (1 / ((k : ℝ) * x))
      rw [Real.norm_of_nonneg (mul_nonneg h1 h3)]; nlinarith
    simpa [abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / ((M * j * k : ℕ) : ℝ)),
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ ((M * j * k : ℕ) : ℝ))] using
      intervalIntegral.norm_integral_le_of_norm_le_const hbd
  have h_sum : ∀ M : ℕ, (∫ x in (0 : ℝ)..1, recipFractScaled j x * recipFractScaled k x) =
      (∫ x in (0 : ℝ)..(1 / ((M * j * k : ℕ) : ℝ)), recipFractScaled j x * recipFractScaled k x) +
      (∫ x in (1 / ((M * j * k : ℕ) : ℝ))..1, recipFractScaled j x * recipFractScaled k x) :=
    fun M => (intervalIntegral.integral_add_adjacent_intervals
      (intervalIntegrable_recipFractScaled_mul j k 0 _)
      (intervalIntegrable_recipFractScaled_mul j k _ 1)).symm
  have h_tot : Tendsto (fun _ : ℕ => ∫ x in (0 : ℝ)..1, recipFractScaled j x * recipFractScaled k x)
      atTop (nhds (0 + L_rhs)) :=
    (h_zero_lim.add h_main_lim).congr' (Eventually.of_forall fun M => (h_sum M).symm)
  rw [show (∫ x in (0 : ℝ)..1, recipFractScaled j x * recipFractScaled k x) = L_rhs by
    simpa using tendsto_nhds_unique tendsto_const_nhds h_tot]
  dsimp [L_rhs, GSmooth, vasyuninGCot]; field_simp [hj_pos.ne', hk_pos.ne']; ring

private lemma intervalIntegrable_recipFractScaled (k : ℕ) (a b : ℝ) :
    IntervalIntegrable (recipFractScaled k) volume a b := by
  have hm : Measurable (recipFractScaled k) :=
    measurable_fract.comp (measurable_const.div (measurable_const.mul measurable_id))
  refine (intervalIntegrable_const (c := (1 : ℝ))).mono_fun' hm.aestronglyMeasurable
    (ae_of_all _ fun x => ?_)
  dsimp only [recipFractScaled]
  rw [Real.norm_of_nonneg (Int.fract_nonneg _)]
  exact (Int.fract_lt_one _).le

/-- Full quadratic expansion of the Lebesgue `L²(0, 1)` Nyman–Beurling distance. -/
theorem intervalIntegral_sq_sub_sum {N : ℕ} (c : ℕ → ℝ) :
    (∫ x in (0 : ℝ)..1, (1 - ∑ k ∈ Finset.Icc 1 N, c k * recipFractScaled k x) ^ 2) =
      1 - 2 * (∑ k ∈ Finset.Icc 1 N, c k * ∫ x in (0 : ℝ)..1, recipFractScaled k x) +
        ∑ j ∈ Finset.Icc 1 N, ∑ k ∈ Finset.Icc 1 N, c j * c k *
          ∫ x in (0 : ℝ)..1, recipFractScaled j x * recipFractScaled k x := by
  have h_eq : (∫ x in (0 : ℝ)..1, (1 - ∑ k ∈ Finset.Icc 1 N, c k * recipFractScaled k x) ^ 2) =
      ∫ x in (0 : ℝ)..1, (1 - 2 * (∑ k ∈ Finset.Icc 1 N, c k * recipFractScaled k x) +
        ∑ j ∈ Finset.Icc 1 N, ∑ k ∈ Finset.Icc 1 N,
          c j * c k * (recipFractScaled j x * recipFractScaled k x)) :=
    intervalIntegral.integral_congr fun x _ => by
      rw [sub_sq, one_pow, mul_one, show (∑ k ∈ Finset.Icc 1 N, c k * recipFractScaled k x) ^ 2 =
        ∑ j ∈ Finset.Icc 1 N, ∑ k ∈ Finset.Icc 1 N,
          c j * c k * (recipFractScaled j x * recipFractScaled k x) by
        rw [sq, sum_mul_sum]; exact sum_congr rfl fun _ _ => sum_congr rfl fun _ _ => by ring]
  have hint1 : IntervalIntegrable (fun _ : ℝ => (1 : ℝ)) volume 0 1 := intervalIntegrable_const
  have hint2_term : ∀ k ∈ Finset.Icc 1 N,
      IntervalIntegrable (fun x => c k * recipFractScaled k x) volume 0 1 :=
    fun k _ => (intervalIntegrable_recipFractScaled k 0 1).const_mul (c k)
  have hint2_sum : IntervalIntegrable
      (fun x => ∑ k ∈ Finset.Icc 1 N, c k * recipFractScaled k x) volume 0 1 := by
    rw [show (fun x => ∑ k ∈ Finset.Icc 1 N, c k * recipFractScaled k x) =
      ∑ k ∈ Finset.Icc 1 N, fun x => c k * recipFractScaled k x by funext x; rw [Finset.sum_apply]]
    exact IntervalIntegrable.sum (Finset.Icc 1 N) hint2_term
  have hint3_term : ∀ j ∈ Finset.Icc 1 N, ∀ k ∈ Finset.Icc 1 N,
      IntervalIntegrable (fun x => c j * c k * (recipFractScaled j x * recipFractScaled k x))
        volume 0 1 := fun j _ k _ => (intervalIntegrable_recipFractScaled_mul j k 0 1).const_mul _
  have hint3_inner : ∀ j ∈ Finset.Icc 1 N, IntervalIntegrable
      (fun x => ∑ k ∈ Finset.Icc 1 N, c j * c k * (recipFractScaled j x * recipFractScaled k x))
      volume 0 1 := fun j hj => by
    rw [show (fun x => ∑ k ∈ Finset.Icc 1 N,
        c j * c k * (recipFractScaled j x * recipFractScaled k x)) =
      ∑ k ∈ Finset.Icc 1 N, fun x => c j * c k * (recipFractScaled j x * recipFractScaled k x) by
      funext x; rw [Finset.sum_apply]]
    exact IntervalIntegrable.sum (Finset.Icc 1 N) (hint3_term j hj)
  have hint3 : IntervalIntegrable (fun x => ∑ j ∈ Finset.Icc 1 N, ∑ k ∈ Finset.Icc 1 N,
      c j * c k * (recipFractScaled j x * recipFractScaled k x)) volume 0 1 := by
    rw [show (fun x => ∑ j ∈ Finset.Icc 1 N, ∑ k ∈ Finset.Icc 1 N,
        c j * c k * (recipFractScaled j x * recipFractScaled k x)) =
      ∑ j ∈ Finset.Icc 1 N, fun x => ∑ k ∈ Finset.Icc 1 N,
        c j * c k * (recipFractScaled j x * recipFractScaled k x) by
      funext x; rw [Finset.sum_apply]]
    exact IntervalIntegrable.sum (Finset.Icc 1 N) hint3_inner
  rw [h_eq, intervalIntegral.integral_add (hint1.sub (hint2_sum.const_mul 2)) hint3,
    intervalIntegral.integral_sub hint1 (hint2_sum.const_mul 2), intervalIntegral.integral_const,
    sub_zero, smul_eq_mul, mul_one, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_finsetSum hint2_term, intervalIntegral.integral_finsetSum hint3_inner]
  simp_rw [intervalIntegral.integral_const_mul]
  refine congr_arg₂ _ rfl (sum_congr rfl fun j hj => ?_)
  rw [intervalIntegral.integral_finsetSum (hint3_term j hj)]
  simp_rw [intervalIntegral.integral_const_mul]

/-- Unconditional Affine `L²(0, 1)` Pure Cotangent Bridge: for any `c` satisfying `D1 c N = 0`
and `D0 c N = 2`, the `L²(0, 1)` distance reduces to `1 + QCot vasyuninGCot c N`. -/
theorem affine_l2_pure_cotangent_bridge {N : ℕ} (c : ℕ → ℝ)
    (hD1 : D1 c N = 0) (hD0 : D0 c N = 2) :
    (∫ x in (0 : ℝ)..1, (1 - ∑ k ∈ Finset.Icc 1 N, c k * recipFractScaled k x) ^ 2) =
      1 + QCot vasyuninGCot c N := by
  rw [intervalIntegral_sq_sub_sum c,
    show (∑ k ∈ Finset.Icc 1 N, c k * ∫ x in (0 : ℝ)..1, recipFractScaled k x) =
      ∑ k ∈ Finset.Icc 1 N, c k * bVasyunin k Real.eulerMascheroniConstant from
      sum_congr rfl fun k hk => by
        rw [intervalIntegral_recipFractScaled_eq_bVasyunin (Finset.mem_Icc.mp hk).1],
    show (∑ j ∈ Finset.Icc 1 N, ∑ k ∈ Finset.Icc 1 N, c j * c k *
        ∫ x in (0 : ℝ)..1, recipFractScaled j x * recipFractScaled k x) =
      (∑ j ∈ Finset.Icc 1 N, ∑ k ∈ Finset.Icc 1 N,
        c j * c k * GSmooth Real.eulerMascheroniConstant j k) + QCot vasyuninGCot c N by
      unfold QCot
      rw [sum_congr rfl fun j hj => sum_congr rfl fun k hk => by
        rw [intervalIntegral_recipFractScaled_cross
          (Finset.mem_Icc.mp hj).1 (Finset.mem_Icc.mp hk).1, mul_add]]
      simp only [Finset.sum_add_distrib],
    ← add_assoc]
  exact affine_bdr_pure_cotangent_identity c N Real.eulerMascheroniConstant
    (QCot vasyuninGCot c N) hD1 hD0

/-- Exact `L²(0, 1)` distance formula in terms of `SCot` on `{c | D1 c N = 0 ∧ D0 c N = 2}`. -/
theorem affine_l2_dist_eq_one_sub_scot {N : ℕ} (c : ℕ → ℝ)
    (hD1 : D1 c N = 0) (hD0 : D0 c N = 2) :
    (∫ x in (0 : ℝ)..1, (1 - ∑ k ∈ Finset.Icc 1 N, c k * recipFractScaled k x) ^ 2) =
      1 - SCot vasyuninGCot c N := by
  dsimp [SCot]
  linarith [affine_l2_pure_cotangent_bridge c hD1 hD0]

/-- Unconditional `L²(0, 1)` cotangent distance formula for `projectAffine u N` when
`DeltaDet N ≠ 0`. -/
theorem projectAffine_l2_dist_eq_one_sub_scot (u : ℕ → ℝ) (N : ℕ) (hΔ : DeltaDet N ≠ 0) :
    (∫ x in (0 : ℝ)..1,
      (1 - ∑ k ∈ Finset.Icc 1 N, projectAffine u N k * recipFractScaled k x) ^ 2) =
      1 - SCot vasyuninGCot (projectAffine u N) N :=
  affine_l2_dist_eq_one_sub_scot (projectAffine u N)
    (projectAffine_D1 u N hΔ) (projectAffine_D0 u N hΔ)
