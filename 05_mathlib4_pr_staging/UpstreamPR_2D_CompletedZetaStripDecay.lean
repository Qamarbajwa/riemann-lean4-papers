/-
Copyright (c) 2026 Qamar Munawer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qamar Munawer
-/
module

public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.NumberTheory.LSeries.RiemannZeta
public import RiemannBlueprint.UpstreamPRs.UpstreamPR_2B_HardyPsiAndThetaKernel

/-!
# Mellin Inversion and Contour Shift for `completedRiemannZeta (1 / 2 + I * t)`

This file bridges the Mellin transform representation of `completedRiemannZeta` in Mathlib
(`completedRiemannZeta_eq`) to the horizontal Fourier integral of `hardyPsi` and shifts the line
of integration across the holomorphicity strip `|Im(z)| < π / 4`:
1. `completedRiemannZeta_half_add_mul_I_eq_fourier`: unshifted Fourier identity on `ℝ`.
2. `integrable_hardyPsi_shift_mul_cexp` and `completedRiemannZeta_half_add_mul_I_eq_shift`:
   Cauchy rectangular contour shift to `Im(z) = α` for any `|α| < π / 4`.
-/

@[expose] public section

open Complex Set Filter MeasureTheory HurwitzZeta

private lemma integral_Ioi_cexp_mul_of_re_neg {c : ℂ} (hc : c.re < 0) :
    ∫ u in Ioi (0 : ℝ), Complex.exp (c * u) = -1 / c := by
  have hc_ne : c ≠ 0 := fun h => by rw [h] at hc; simp at hc
  have h_ten := intervalIntegral_tendsto_integral_Ioi (a := (0 : ℝ))
    (f := fun u : ℝ => Complex.exp (c * u)) (integrableOn_exp_mul_complex_Ioi hc 0) tendsto_id
  simp only [id_eq] at h_ten
  rw [show (fun b : ℝ => ∫ u in (0 : ℝ)..b, Complex.exp (c * u)) =
      fun b : ℝ => (Complex.exp (c * b) - 1) / c from funext fun b => by
    rw [integral_exp_mul_complex hc_ne, Complex.ofReal_zero, mul_zero, Complex.exp_zero]] at h_ten
  have h_lim : Tendsto (fun b : ℝ => (Complex.exp (c * b) - 1) / c) atTop (nhds (-1 / c)) := by
    have ht0 : Tendsto (fun b : ℝ => Complex.exp (c * b)) atTop (nhds 0) := by
      rw [tendsto_zero_iff_norm_tendsto_zero]
      simp_rw [Complex.norm_exp, show ∀ b : ℝ, (c * (b : ℂ)).re = c.re * b by
        intro b; simp [Complex.mul_re]]
      exact Real.tendsto_exp_atBot.comp (tendsto_id.const_mul_atTop_of_neg hc)
    simpa [zero_sub] using (ht0.sub tendsto_const_nhds).div_const c
  exact tendsto_nhds_unique h_ten h_lim

private lemma integrable_and_integral_cexp_neg_half_abs_mul (t : ℝ) :
    Integrable (fun u : ℝ => Complex.exp (-((|u| : ℝ) : ℂ) / 2) * Complex.exp ((t : ℂ) * u * I)) ∧
      ∫ u : ℝ, Complex.exp (-((|u| : ℝ) : ℂ) / 2) * Complex.exp ((t : ℂ) * u * I) =
        1 / (1 / 2 + (t : ℂ) * I) + 1 / (1 - (1 / 2 + (t : ℂ) * I)) := by
  let c₁ : ℂ := -(1 / 2 : ℂ) + (t : ℂ) * I
  let c₂ : ℂ := -(1 / 2 : ℂ) - (t : ℂ) * I
  have hc₁_re : c₁.re < 0 := by simp [c₁]
  have hc₂_re : c₂.re < 0 := by simp [c₂]
  have hint_Iic : ∫ u in Iic (0 : ℝ), Complex.exp (-c₂ * u) = -1 / c₂ := by
    rw [show (fun u : ℝ => Complex.exp (-c₂ * u)) = fun u => Complex.exp (c₂ * ((-u : ℝ) : ℂ)) from
        funext fun u => by push_cast; congr 1; ring,
      integral_comp_neg_Iic 0 (fun x : ℝ => Complex.exp (c₂ * (x : ℂ))), neg_zero]
    exact integral_Ioi_cexp_mul_of_re_neg hc₂_re
  have hi1 : IntegrableOn (fun u : ℝ =>
      Complex.exp (-((|u| : ℝ) : ℂ) / 2) * Complex.exp ((t : ℂ) * u * I)) (Iic 0) :=
    (integrableOn_exp_mul_complex_Iic (by simp [c₂] : 0 < (-c₂).re) 0).congr_fun (fun u hu => by
      rw [← Complex.exp_add, abs_of_nonpos (mem_Iic.mp hu)]; dsimp [c₂]; push_cast; ring_nf)
      measurableSet_Iic
  have hi2 : IntegrableOn (fun u : ℝ =>
      Complex.exp (-((|u| : ℝ) : ℂ) / 2) * Complex.exp ((t : ℂ) * u * I)) (Ioi 0) :=
    (integrableOn_exp_mul_complex_Ioi hc₁_re 0).congr_fun (fun u hu => by
      rw [← Complex.exp_add, abs_of_pos (mem_Ioi.mp hu)]; dsimp [c₁]; ring_nf)
      measurableSet_Ioi
  refine ⟨by rw [← integrableOn_univ, ← Iic_union_Ioi (a := (0 : ℝ)), integrableOn_union]
             exact ⟨hi1, hi2⟩, ?_⟩
  have h1_eq : ∫ u in Iic (0 : ℝ), Complex.exp (-((|u| : ℝ) : ℂ) / 2) *
      Complex.exp ((t : ℂ) * u * I) = ∫ u in Iic (0 : ℝ), Complex.exp (-c₂ * u) :=
    setIntegral_congr_fun measurableSet_Iic fun u hu => by
      rw [← Complex.exp_add, abs_of_nonpos (mem_Iic.mp hu)]; congr 1; dsimp [c₂]; push_cast; ring
  have h2_eq : ∫ u in Ioi (0 : ℝ), Complex.exp (-((|u| : ℝ) : ℂ) / 2) *
      Complex.exp ((t : ℂ) * u * I) = ∫ u in Ioi (0 : ℝ), Complex.exp (c₁ * u) :=
    setIntegral_congr_fun measurableSet_Ioi fun u hu => by
      rw [← Complex.exp_add, abs_of_pos (mem_Ioi.mp hu)]; congr 1; dsimp [c₁]; ring
  rw [← setIntegral_univ, ← Iic_union_Ioi (a := (0 : ℝ)),
    setIntegral_union (Iic_disjoint_Ioi le_rfl) measurableSet_Ioi hi1 hi2,
    h1_eq, h2_eq, hint_Iic, integral_Ioi_cexp_mul_of_re_neg hc₁_re,
    show -1 / c₂ = 1 / (1 / 2 + (t : ℂ) * I) by
      dsimp [c₂]
      rw [show -(1 / 2 : ℂ) - (t : ℂ) * I = -(1 / 2 + (t : ℂ) * I) by ring, neg_div_neg_eq],
    show -1 / c₁ = 1 / (1 - (1 / 2 + (t : ℂ) * I)) by
      dsimp [c₁]
      rw [show -(1 / 2 : ℂ) + (t : ℂ) * I = -(1 - (1 / 2 + (t : ℂ) * I)) by ring, neg_div_neg_eq]]

/-- Unshifted Fourier integral formula for `completedRiemannZeta (1 / 2 + I * t)`. -/
theorem completedRiemannZeta_half_add_mul_I_eq_fourier (t : ℝ) :
    completedRiemannZeta (1 / 2 + (t : ℂ) * I) =
      ∫ u : ℝ, hardyPsi (u : ℂ) * Complex.exp ((t : ℂ) * u * I) := by
  have h_zeta_eq := completedRiemannZeta_eq (1 / 2 + (t : ℂ) * I)
  have h_Λ₀ : completedRiemannZeta₀ (1 / 2 + (t : ℂ) * I) =
      (mellin (hurwitzEvenFEPair 0).f_modif ((1 / 2 + (t : ℂ) * I) / 2)) / 2 := by
    rw [completedRiemannZeta₀, HurwitzZeta.completedHurwitzZetaEven₀, WeakFEPair.Λ₀]
  have h_mellin : (mellin (hurwitzEvenFEPair 0).f_modif ((1 / 2 + (t : ℂ) * I) / 2)) / 2 =
      ∫ u : ℝ, (hardyPsi (u : ℂ) + Complex.exp (-((|u| : ℝ) : ℂ) / 2)) *
        Complex.exp ((t : ℂ) * u * I) := by
    rw [mellin, show ∫ y in Ioi (0 : ℝ), (y : ℂ) ^ ((1 / 2 + (t : ℂ) * I) / 2 - 1) •
          (hurwitzEvenFEPair 0).f_modif y = ∫ x : ℝ, (Real.exp x : ℂ) *
          ((Real.exp x : ℂ) ^ ((1 / 2 + (t : ℂ) * I) / 2 - 1) •
            (hurwitzEvenFEPair 0).f_modif (Real.exp x)) from by
        symm; simpa [Complex.real_smul] using integral_comp_exp (fun y : ℝ =>
          (y : ℂ) ^ ((1 / 2 + (t : ℂ) * I) / 2 - 1) • (hurwitzEvenFEPair 0).f_modif y),
      show (∫ x : ℝ, (Real.exp x : ℂ) * ((Real.exp x : ℂ) ^ ((1 / 2 + (t : ℂ) * I) / 2 - 1) •
          (hurwitzEvenFEPair 0).f_modif (Real.exp x))) / 2 = ∫ u : ℝ, (Real.exp (2 * u) : ℂ) *
          ((Real.exp (2 * u) : ℂ) ^ ((1 / 2 + (t : ℂ) * I) / 2 - 1) •
            (hurwitzEvenFEPair 0).f_modif (Real.exp (2 * u))) from by
        rw [Measure.integral_comp_mul_left (fun x : ℝ => (Real.exp x : ℂ) *
            ((Real.exp x : ℂ) ^ ((1 / 2 + (t : ℂ) * I) / 2 - 1) •
              (hurwitzEvenFEPair 0).f_modif (Real.exp x))) (2 : ℝ),
          abs_of_pos (inv_pos.mpr (by norm_num : (0 : ℝ) < 2)), Complex.real_smul]; push_cast; ring]
    refine integral_congr_ae ?_
    filter_upwards [compl_mem_ae_iff.mpr (Subsingleton.measure_zero (s := {(0 : ℝ)}) (by simp) _)]
      with u hu
    have h_pow : (Real.exp (2 * u) : ℂ) *
        ((Real.exp (2 * u) : ℂ) ^ ((1 / 2 + (t : ℂ) * I) / 2 - 1)) =
        Complex.exp ((u : ℂ) / 2) * Complex.exp ((t : ℂ) * u * I) := by
      rw [Complex.ofReal_exp, Complex.cpow_def_of_ne_zero (Complex.exp_ne_zero _),
        Complex.log_exp (by simp [Real.pi_pos]) (by simp [Real.pi_pos.le]),
        ← Complex.exp_add, ← Complex.exp_add]
      congr 1; push_cast; ring
    have hek : ((evenKernel 0 (Real.exp (2 * u)) : ℝ) : ℂ) =
        jacobiTheta (I * Complex.exp (2 * u)) := by
      rw [evenKernel_eq_cosKernel_of_zero, ← QuotientAddGroup.mk_zero, cosKernel_def,
        Complex.ofReal_zero, Complex.ofReal_exp, ← jacobiTheta_eq_jacobiTheta₂]; simp
    simp only [smul_eq_mul]; rw [← mul_assoc, h_pow]
    have h_f_modif : (hurwitzEvenFEPair 0).f_modif (Real.exp (2 * u)) =
        if 0 < u then jacobiTheta (I * Complex.exp (2 * u)) - 1
        else jacobiTheta (I * Complex.exp (2 * u)) - Complex.exp (-(u : ℂ)) := by
      dsimp [WeakFEPair.f_modif, hurwitzEvenFEPair]
      rcases lt_or_gt_of_ne hu with hlt | hgt
      · have hexp_lt1 : Real.exp (2 * u) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
        have h_in : Real.exp (2 * u) ∈ Ioo (0 : ℝ) 1 := ⟨Real.exp_pos _, hexp_lt1⟩
        have h_not : Real.exp (2 * u) ∉ Ioi (1 : ℝ) := fun h => absurd h (not_lt.mpr hexp_lt1.le)
        have h_rpow : ((Real.exp (2 * u) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) = Complex.exp (-(u : ℂ)) := by
          rw [← Real.exp_mul, show (2 * u) * -(1 / 2 : ℝ) = -u by ring, Complex.ofReal_exp,
            Complex.ofReal_neg]
        simp only [hlt.not_gt, ite_false, indicator_of_notMem h_not, indicator_of_mem h_in,
          zero_add, one_mul, mul_one]
        rw [hek, h_rpow]
      · have hexp_gt1 : 1 < Real.exp (2 * u) := Real.one_lt_exp_iff.mpr (by linarith)
        have h_in : Real.exp (2 * u) ∈ Ioi (1 : ℝ) := hexp_gt1
        have h_not : Real.exp (2 * u) ∉ Ioo (0 : ℝ) 1 := fun h =>
          absurd h.2 (not_lt.mpr hexp_gt1.le)
        simp only [hgt, ite_true, indicator_of_mem h_in, indicator_of_notMem h_not, add_zero]
        exact congrArg (· - 1) hek
    rw [h_f_modif]
    rcases lt_or_gt_of_ne hu with hlt | hgt
    · simp only [hlt.not_gt, ite_false]; rw [abs_of_neg hlt]; unfold hardyPsi
      rw [show -(((-u : ℝ) : ℂ)) / 2 = (u : ℂ) / 2 by push_cast; ring]
      have h_id1 : Complex.exp ((u : ℂ) / 2) * Complex.exp (-(u : ℂ)) =
          Complex.exp (-(u : ℂ) / 2) := by rw [← Complex.exp_add]; congr 1; ring
      rw [show (Complex.exp ((u : ℂ) / 2) * Complex.exp ((t : ℂ) * u * I)) *
            (jacobiTheta (I * Complex.exp (2 * (u : ℂ))) - Complex.exp (-(u : ℂ))) =
          (Complex.exp ((u : ℂ) / 2) * jacobiTheta (I * Complex.exp (2 * (u : ℂ))) -
            Complex.exp ((u : ℂ) / 2) * Complex.exp (-(u : ℂ))) * Complex.exp ((t : ℂ) * u * I)
          by ring, h_id1]; ring
    · simp only [hgt, ite_true]; rw [abs_of_pos hgt]; unfold hardyPsi; ring
  have hint_psi : Integrable (fun u : ℝ => hardyPsi (u : ℂ) * Complex.exp ((t : ℂ) * u * I)) :=
    (integrable_hardyPsi_shift (α := 0) (by simpa using Real.pi_pos)).mono
      (((continuous_iff_continuousAt.mpr fun u => (differentiableAt_hardyPsi
        (by simpa using Real.pi_pos)).continuousAt.comp Complex.continuous_ofReal.continuousAt).mul
          (by fun_prop)).aestronglyMeasurable)
      (ae_of_all _ fun u => by rw [norm_mul, show ‖Complex.exp ((t : ℂ) * u * I)‖ = 1 by
        rw [Complex.norm_exp]; simp [Complex.mul_re]]; simp)
  have ⟨hint_exp, hint_exp_val⟩ := integrable_and_integral_cexp_neg_half_abs_mul t
  have h_add : ∫ u : ℝ, (hardyPsi (u : ℂ) + Complex.exp (-((|u| : ℝ) : ℂ) / 2)) *
        Complex.exp ((t : ℂ) * u * I) =
      (∫ u : ℝ, hardyPsi (u : ℂ) * Complex.exp ((t : ℂ) * u * I)) +
      (∫ u : ℝ, Complex.exp (-((|u| : ℝ) : ℂ) / 2) * Complex.exp ((t : ℂ) * u * I)) := by
    simp_rw [add_mul]; exact integral_add hint_psi hint_exp
  rw [h_zeta_eq, h_Λ₀, h_mellin, h_add, hint_exp_val]; ring

/-- Integrability of `u ↦ hardyPsi (u + α * I) * exp (t * (u + α * I) * I)` for `|α| < π / 4`.
-/
theorem integrable_hardyPsi_shift_mul_cexp (t : ℝ) {α : ℝ} (hα : |α| < Real.pi / 4) :
    Integrable (fun u : ℝ => hardyPsi ((u : ℂ) + (α : ℂ) * I) *
      Complex.exp ((t : ℂ) * ((u : ℂ) + (α : ℂ) * I) * I)) := by
  have hcont : Continuous (fun u : ℝ => hardyPsi ((u : ℂ) + (α : ℂ) * I) *
      Complex.exp ((t : ℂ) * ((u : ℂ) + (α : ℂ) * I) * I)) :=
    (continuous_iff_continuousAt.mpr fun u => (differentiableAt_hardyPsi
      (by simpa using hα)).continuousAt.comp (f := fun v : ℝ => (v : ℂ) + (α : ℂ) * I)
        (Complex.continuous_ofReal.add continuous_const).continuousAt).mul (by fun_prop)
  refine ((integrable_hardyPsi_shift hα).norm.const_mul (Real.exp (-t * α))).mono
    hcont.aestronglyMeasurable (ae_of_all _ fun u => ?_)
  have hnorm : ‖Complex.exp ((t : ℂ) * ((u : ℂ) + (α : ℂ) * I) * I)‖ = Real.exp (-t * α) := by
    rw [Complex.norm_exp, show ((t : ℂ) * ((u : ℂ) + (α : ℂ) * I) * I).re = -t * α by
      simp [Complex.mul_re, Complex.mul_im]]
  rw [norm_mul, hnorm, mul_comm (α : ℂ) I, mul_comm _ (Real.exp (-t * α))]
  exact (le_abs_self _).trans_eq (Real.norm_eq_abs _).symm

/-- Contour-shifted Fourier representation of `completedRiemannZeta (1 / 2 + I * t)` along
`Im(z) = α` for `|α| < π / 4`. -/
theorem completedRiemannZeta_half_add_mul_I_eq_shift (t : ℝ) {α : ℝ} (hα : |α| < Real.pi / 4) :
    completedRiemannZeta (1 / 2 + (t : ℂ) * I) = ∫ u : ℝ,
      hardyPsi ((u : ℂ) + (α : ℂ) * I) * Complex.exp ((t : ℂ) * ((u : ℂ) + (α : ℂ) * I) * I) := by
  let F : ℂ → ℂ := fun z => hardyPsi z * Complex.exp ((t : ℂ) * z * I)
  have h_uIcc_abs : ∀ y ∈ uIcc (0 : ℝ) α, |y| ≤ |α| := fun y hy => by
    rcases mem_uIcc.mp hy with ⟨_, h2⟩ | ⟨_, h2⟩ <;> exact abs_le.mpr
      ⟨by linarith [abs_nonneg α, neg_le_abs α],
        h2.trans (by first | exact le_abs_self α | exact abs_nonneg α)⟩
  have hrect : ∀ R : ℝ, (∫ x in (-R)..R, F (x : ℂ)) - (∫ x in (-R)..R, F ((x : ℂ) + (α : ℂ) * I)) +
      I • (∫ y in (0 : ℝ)..α, F ((R : ℂ) + (y : ℂ) * I)) -
      I • (∫ y in (0 : ℝ)..α, F ((-R : ℂ) + (y : ℂ) * I)) = 0 := fun R => by
    have hdiff : DifferentiableOn ℂ F (uIcc (-(R : ℂ)).re ((R : ℂ) + (α : ℂ) * I).re ×ℂ
        uIcc (-(R : ℂ)).im ((R : ℂ) + (α : ℂ) * I).im) := fun z hz =>
      ((differentiableAt_hardyPsi (lt_of_le_of_lt (h_uIcc_abs z.im (by simpa using hz.2)) hα)).mul
        (((differentiableAt_const _).mul differentiableAt_id).mul
          (differentiableAt_const _)).cexp).differentiableWithinAt
    simpa [Complex.ofReal_neg, Complex.neg_re, Complex.ofReal_re, Complex.ofReal_im, Complex.add_re,
      Complex.add_im, Complex.mul_re, Complex.mul_im] using
      Complex.integral_boundary_rect_eq_zero_of_differentiableOn
        F (-(R : ℂ)) ((R : ℂ) + α * I) hdiff
  obtain ⟨M, hM_pos, hM⟩ := norm_hardyPsi_le (abs_nonneg α) hα
  have hV_lim : ∀ s : ℝ, s = 1 ∨ s = -1 →
      Tendsto (fun R : ℝ => I • ∫ y in (0 : ℝ)..α, F (((s * R : ℝ) : ℂ) + (y : ℂ) * I))
        atTop (nhds 0) := fun s hs => by
    have hV_bd : ∀ R : ℝ, 0 ≤ R →
        ‖I • ∫ y in (0 : ℝ)..α, F (((s * R : ℝ) : ℂ) + (y : ℂ) * I)‖ ≤
          M * Real.exp (|t| * |α|) * |α| * Real.exp (-R / 2) := fun R hR => by
      have h_side : ∀ y ∈ uIoc (0 : ℝ) α,
          ‖F (((s * R : ℝ) : ℂ) + (y : ℂ) * I)‖ ≤ M * Real.exp (|t| * |α|) * Real.exp (-R / 2) :=
        fun y hy => by
        have hy_abs : |y| ≤ |α| := h_uIcc_abs y (uIoc_subset_uIcc hy)
        have hψ := hM (((s * R : ℝ) : ℂ) + (y : ℂ) * I) (by simpa using hy_abs)
        have hs_abs : |s * R| = R := by rcases hs with rfl | rfl <;> simp [abs_of_nonneg hR]
        rw [show |(((s * R : ℝ) : ℂ) + (y : ℂ) * I).re| = R by simpa using hs_abs] at hψ
        have h_exp : ‖Complex.exp ((t : ℂ) * (((s * R : ℝ) : ℂ) + (y : ℂ) * I) * I)‖ ≤
            Real.exp (|t| * |α|) := by
          rw [Complex.norm_exp, show ((t : ℂ) * (((s * R : ℝ) : ℂ) + (y : ℂ) * I) * I).re =
            -t * y by simp [Complex.mul_re, Complex.mul_im], Real.exp_le_exp]
          exact ((le_abs_self (-t * y)).trans_eq (by rw [abs_mul, abs_neg])).trans
            (mul_le_mul_of_nonneg_left hy_abs (abs_nonneg t))
        dsimp [F]; rw [norm_mul]; exact (mul_le_mul hψ h_exp (norm_nonneg _)
          (mul_nonneg hM_pos.le (Real.exp_pos _).le)).trans_eq (by ring)
      have hint := intervalIntegral.norm_integral_le_of_norm_le_const h_side
      rw [sub_zero] at hint; rw [norm_smul, Complex.norm_I, one_mul]; exact hint.trans_eq (by ring)
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine squeeze_zero' (g := fun R : ℝ => M * Real.exp (|t| * |α|) * |α| * Real.exp (-R / 2))
      (Eventually.of_forall fun _ => norm_nonneg _)
      (eventually_ge_atTop 0 |>.mono fun R hR => hV_bd R hR)
      (by simpa [mul_zero] using ((Real.tendsto_exp_atBot.comp
        (tendsto_id.const_mul_atTop_of_neg (by norm_num : -(1 / 2 : ℝ) < 0))).congr
          fun R => by dsimp; congr 1; ring).const_mul (M * Real.exp (|t| * |α|) * |α|))
  have hVR := hV_lim 1 (Or.inl rfl); have hVL := hV_lim (-1) (Or.inr rfl)
  simp only [one_mul, neg_one_mul, Complex.ofReal_neg] at hVR hVL
  have hbot_ten := intervalIntegral_tendsto_integral
    (by simpa [F] using integrable_hardyPsi_shift_mul_cexp t (α := 0) (by simpa using Real.pi_pos))
    tendsto_neg_atTop_atBot tendsto_id
  have htop_ten := intervalIntegral_tendsto_integral
    (integrable_hardyPsi_shift_mul_cexp t hα) tendsto_neg_atTop_atBot tendsto_id
  simp only [id_eq] at hbot_ten htop_ten
  have hcomb : Tendsto (fun R : ℝ => ∫ x in (-R)..R, F ((x : ℂ) + (α : ℂ) * I)) atTop
      (nhds (∫ u : ℝ, hardyPsi (u : ℂ) * Complex.exp ((t : ℂ) * u * I))) := by
    rw [← add_zero (∫ u : ℝ, hardyPsi (u : ℂ) * Complex.exp ((t : ℂ) * u * I)), ← sub_self (0 : ℂ)]
    refine (hbot_ten.add (hVR.sub hVL)).congr fun R => ?_
    have hr := hrect R; dsimp [F] at hr ⊢; linear_combination hr
  rw [completedRiemannZeta_half_add_mul_I_eq_fourier t]; exact tendsto_nhds_unique hcomb htop_ten
