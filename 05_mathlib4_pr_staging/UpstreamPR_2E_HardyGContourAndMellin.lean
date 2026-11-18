/-
Copyright (c) 2026 Qamar Munawer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qamar Munawer
-/
module

public import Mathlib.Analysis.Analytic.Uniqueness
public import Mathlib.Analysis.Fourier.Inversion
public import RiemannBlueprint.UpstreamPRs.UpstreamPR_2D_CompletedZetaStripDecay

/-!
# Critical-Line Strip Decay and `hardyG = hardyPsi` Analytic Continuation

This file establishes rapid exponential decay and weighted integrability of
`completedRiemannZeta (1 / 2 + I * t)`, defines Hardy's Fourier integral representation `hardyG`,
and proves `hardyG z = hardyPsi z` throughout the strip `|z.im| < π / 4`:
1. `norm_completedRiemannZeta_criticalLine_le` and `continuous_completedRiemannZeta_criticalLine`.
2. `integrable_abs_pow_mul_exp_mul_completedRiemannZeta`.
3. `hardyG`, `hardyG_ofReal` (via Fourier inversion), `hasDerivAt_hardyG`, and `hardyG_eq_hardyPsi`.
-/

@[expose] public section

open Complex Set Filter MeasureTheory Real
open scoped FourierTransform RealInnerProductSpace Topology

/-- Exponential strip decay `‖Λ(1 / 2 + I * t)‖ ≤ C * exp (-α₀ * |t|)` for `0 ≤ α₀ < π / 4`. -/
theorem norm_completedRiemannZeta_criticalLine_le {α₀ : ℝ} (hα₀ : 0 ≤ α₀) (hα : α₀ < Real.pi / 4) :
    ∃ C > 0, ∀ t : ℝ, ‖completedRiemannZeta (1 / 2 + (t : ℂ) * I)‖ ≤ C * Real.exp (-α₀ * |t|) := by
  let I_int : ℝ := ∫ u : ℝ, ‖hardyPsi ((u : ℂ) + I * (α₀ : ℂ))‖
  have hI_nonneg : 0 ≤ I_int := integral_nonneg fun _ => norm_nonneg _
  refine ⟨I_int + 1, by linarith, fun t => ?_⟩
  by_cases ht : 0 ≤ t
  · rw [completedRiemannZeta_half_add_mul_I_eq_shift t (by rwa [abs_of_nonneg hα₀]),
      abs_of_nonneg ht]
    have hint := norm_integral_le_integral_norm (μ := volume) (fun u : ℝ =>
      hardyPsi ((u : ℂ) + (α₀ : ℂ) * I) * Complex.exp ((t : ℂ) * ((u : ℂ) + (α₀ : ℂ) * I) * I))
    have h_eq : ∫ u : ℝ, ‖hardyPsi ((u : ℂ) + (α₀ : ℂ) * I) *
        Complex.exp ((t : ℂ) * ((u : ℂ) + (α₀ : ℂ) * I) * I)‖ = Real.exp (-α₀ * t) * I_int := by
      rw [← integral_const_mul]; refine integral_congr_ae (ae_of_all _ fun u => ?_)
      dsimp only
      rw [norm_mul, Complex.norm_exp, show ((t : ℂ) * ((u : ℂ) + (α₀ : ℂ) * I) * I).re =
        -t * α₀ by simp [Complex.mul_re, Complex.mul_im], mul_comm (α₀ : ℂ) I,
        mul_comm _ (Real.exp (-t * α₀)), show -t * α₀ = -α₀ * t by ring]
    exact (hint.trans_eq h_eq).trans (by rw [mul_comm (Real.exp (-α₀ * t)) I_int]
                                         exact mul_le_mul_of_nonneg_right (by linarith)
                                           (Real.exp_pos _).le)
  · have ht_neg : t < 0 := lt_of_not_ge ht
    rw [completedRiemannZeta_half_add_mul_I_eq_shift t
      (by rwa [abs_neg, abs_of_nonneg hα₀]), abs_of_neg ht_neg]
    have hint := norm_integral_le_integral_norm (μ := volume) (fun u : ℝ =>
      hardyPsi ((u : ℂ) + ((-α₀ : ℝ) : ℂ) * I) *
        Complex.exp ((t : ℂ) * ((u : ℂ) + ((-α₀ : ℝ) : ℂ) * I) * I))
    have h_sym : ∫ u : ℝ, ‖hardyPsi ((u : ℂ) + ((-α₀ : ℝ) : ℂ) * I)‖ = I_int := by
      rw [show (fun u : ℝ => ‖hardyPsi ((u : ℂ) + ((-α₀ : ℝ) : ℂ) * I)‖) =
          fun u : ℝ => ‖hardyPsi (((-u : ℝ) : ℂ) + I * (α₀ : ℂ))‖ from funext fun u => by
        rw [← hardyPsi_neg (by simpa [abs_of_nonneg hα₀] using hα :
            |(((-u : ℝ) : ℂ) + I * (α₀ : ℂ)).im| < Real.pi / 4),
          show -(((-u : ℝ) : ℂ) + I * (α₀ : ℂ)) = (u : ℂ) + ((-α₀ : ℝ) : ℂ) * I by push_cast; ring]]
      simpa using Measure.integral_comp_mul_left
        (fun x : ℝ => ‖hardyPsi ((x : ℂ) + I * (α₀ : ℂ))‖) (-1 : ℝ)
    have h_eq : ∫ u : ℝ, ‖hardyPsi ((u : ℂ) + ((-α₀ : ℝ) : ℂ) * I) *
        Complex.exp ((t : ℂ) * ((u : ℂ) + ((-α₀ : ℝ) : ℂ) * I) * I)‖ =
        Real.exp (-α₀ * -t) * I_int := by
      rw [← h_sym, ← integral_const_mul]; refine integral_congr_ae (ae_of_all _ fun u => ?_)
      dsimp only
      rw [norm_mul, Complex.norm_exp, show ((t : ℂ) * ((u : ℂ) + ((-α₀ : ℝ) : ℂ) * I) * I).re =
        -t * -α₀ by simp [Complex.mul_re, Complex.mul_im], mul_comm _ (Real.exp _)]
      congr 2; ring
    exact (hint.trans_eq h_eq).trans (by rw [mul_comm (Real.exp (-α₀ * -t)) I_int]
                                         exact mul_le_mul_of_nonneg_right (by linarith)
                                           (Real.exp_pos _).le)

/-- Continuity of `t ↦ completedRiemannZeta (1 / 2 + I * t)` on `ℝ`. -/
theorem continuous_completedRiemannZeta_criticalLine :
    Continuous (fun t : ℝ => completedRiemannZeta (1 / 2 + (t : ℂ) * I)) :=
  continuous_iff_continuousAt.mpr fun t =>
    (differentiableAt_completedZeta (fun h => by have := congrArg Complex.re h; norm_num at this)
      (fun h => by have := congrArg Complex.re h; norm_num at this)).continuousAt.comp
      (f := fun x : ℝ => (1 / 2 : ℂ) + (x : ℂ) * I)
      (continuous_const.add (Complex.continuous_ofReal.mul continuous_const)).continuousAt

/-- Weighted integrability of `|t| ^ m * exp (β * |t|) * ‖Λ(1 / 2 + I * t)‖` for `0 ≤ β < π / 4`.
-/
theorem integrable_abs_pow_mul_exp_mul_completedRiemannZeta (m : ℕ) {β : ℝ}
    (hβ₀ : 0 ≤ β) (hβ : β < Real.pi / 4) :
    Integrable (fun t : ℝ =>
      |t| ^ m * Real.exp (β * |t|) * ‖completedRiemannZeta (1 / 2 + (t : ℂ) * I)‖) := by
  let α₁ : ℝ := (β + Real.pi / 4) / 2
  have hα₁_gt : β < α₁ := by dsimp [α₁]; linarith
  let δ : ℝ := α₁ - β
  have hδ : 0 < δ := sub_pos.mpr hα₁_gt
  obtain ⟨C, hC, hΛ⟩ := norm_completedRiemannZeta_criticalLine_le (hβ₀.trans hα₁_gt.le)
    (by dsimp [α₁]; linarith)
  let K : ℝ := C * (m.factorial : ℝ) / (δ / 2) ^ m
  have hK : 0 ≤ K := by positivity
  have hdom : Integrable (fun t : ℝ => K * Real.exp (-(δ / 2) * |t|)) := by
    have h1 : IntegrableOn (fun t : ℝ => K * Real.exp (-(δ / 2) * t)) (Ioi 0) :=
      (integrableOn_exp_mul_Ioi (by linarith : -(δ / 2) < 0) 0).const_mul K
    have h2 : IntegrableOn (fun t : ℝ => K * Real.exp (δ / 2 * t)) (Iic 0) :=
      (integrableOn_exp_mul_Iic (by linarith : 0 < δ / 2) 0).const_mul K
    rw [← integrableOn_univ, ← Iic_union_Ioi (a := (0 : ℝ)), integrableOn_union]
    exact ⟨h2.congr_fun (fun t ht => by simp only [abs_of_nonpos (mem_Iic.mp ht)]; ring_nf)
        measurableSet_Iic,
      h1.congr_fun (fun t ht => by simp only [abs_of_pos (mem_Ioi.mp ht)]) measurableSet_Ioi⟩
  have hmeas : AEStronglyMeasurable (fun t : ℝ => |t| ^ m * Real.exp (β * |t|) *
      ‖completedRiemannZeta (1 / 2 + (t : ℂ) * I)‖) volume :=
    ((continuous_abs.pow m).mul (Real.continuous_exp.comp (continuous_const.mul continuous_abs))
      |>.mul continuous_completedRiemannZeta_criticalLine.norm).aestronglyMeasurable
  refine hdom.mono hmeas (ae_of_all _ fun t => ?_)
  have hpow : |t| ^ m ≤ (m.factorial : ℝ) / (δ / 2) ^ m * Real.exp ((δ / 2) * |t|) := by
    have hexp := Real.pow_div_factorial_le_exp ((δ / 2) * |t|) (mul_nonneg (by positivity)
      (abs_nonneg t)) m
    rw [mul_pow, div_le_iff₀ (Nat.cast_pos.mpr m.factorial_pos),
      ← le_div_iff₀' (pow_pos (by linarith : 0 < δ / 2) m)] at hexp
    exact hexp.trans_eq (by ring)
  rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity)]
  calc |t| ^ m * Real.exp (β * |t|) * ‖completedRiemannZeta (1 / 2 + (t : ℂ) * I)‖
      ≤ ((m.factorial : ℝ) / (δ / 2) ^ m * Real.exp ((δ / 2) * |t|)) * Real.exp (β * |t|) *
          (C * Real.exp (-α₁ * |t|)) :=
        mul_le_mul (mul_le_mul_of_nonneg_right hpow (Real.exp_pos _).le) (hΛ t) (norm_nonneg _)
          (by positivity)
    _ = K * Real.exp (-(δ / 2) * |t|) := by
        rw [show ((m.factorial : ℝ) / (δ / 2) ^ m * Real.exp ((δ / 2) * |t|)) * Real.exp (β * |t|) *
          (C * Real.exp (-α₁ * |t|)) = K * (Real.exp ((δ / 2) * |t|) * Real.exp (β * |t|) *
            Real.exp (-α₁ * |t|)) by dsimp [K]; ring, ← Real.exp_add, ← Real.exp_add]
        congr 2; dsimp [δ]; ring

/-- Analytic strip representation `G(z) = (2π)⁻¹ ∫ exp (-z * t * I) * Λ(1 / 2 + t * I) dt` on
`|z.im| < π / 4`. -/
noncomputable def hardyG (z : ℂ) : ℂ :=
  ((2 * Real.pi : ℝ) : ℂ)⁻¹ *
    ∫ t : ℝ, Complex.exp (-z * (t : ℂ) * I) * completedRiemannZeta (1 / 2 + (t : ℂ) * I)

private lemma hardyG_ofReal (u : ℝ) : hardyG (u : ℂ) = hardyPsi (u : ℂ) := by
  let f : ℝ → ℂ := fun v => hardyPsi (v : ℂ)
  have hf_cont : Continuous f := continuous_iff_continuousAt.mpr fun v =>
    (differentiableAt_hardyPsi (by simpa using Real.pi_pos)).continuousAt.comp
      Complex.continuous_ofReal.continuousAt
  have hf_int : Integrable f := by
    simpa [f] using integrable_hardyPsi_shift (α := 0) (by simpa using Real.pi_pos)
  have h_four : ∀ ξ : ℝ, 𝓕 f ξ =
      completedRiemannZeta (1 / 2 + ((-(2 * Real.pi) * ξ : ℝ) : ℂ) * I) := fun ξ => by
    rw [Real.fourier_eq', completedRiemannZeta_half_add_mul_I_eq_fourier (-(2 * Real.pi) * ξ)]
    refine integral_congr_ae (ae_of_all _ fun v => ?_)
    dsimp only [f]; rw [smul_eq_mul, mul_comm _ (hardyPsi (v : ℂ)), RCLike.inner_apply]
    simp only [starRingEnd_apply, star_trivial]; congr 2; push_cast; ring
  have h_raw_int : Integrable (fun t : ℝ => ‖completedRiemannZeta (1 / 2 + (t : ℂ) * I)‖) := by
    simpa using integrable_abs_pow_mul_exp_mul_completedRiemannZeta 0 le_rfl
      (by linarith [Real.pi_pos] : (0 : ℝ) < Real.pi / 4)
  have hf_four_int : Integrable (𝓕 f) := ((integrable_comp_mul_left_iff
    (fun t : ℝ => completedRiemannZeta (1 / 2 + (t : ℂ) * I))
    (neg_ne_zero.mpr (by positivity : 2 * Real.pi ≠ 0))).mpr
    (h_raw_int.mono continuous_completedRiemannZeta_criticalLine.aestronglyMeasurable
      (ae_of_all _ fun _ => by simp))).congr (ae_of_all _ fun ξ => (h_four ξ).symm)
  have hinv := congrFun (hf_cont.fourierInv_fourier_eq hf_int hf_four_int) u
  dsimp [f] at hinv; rw [← hinv, Real.fourierInv_eq']
  rw [show (fun ξ : ℝ => Complex.exp (((2 * Real.pi * ⟪ξ, u⟫ : ℝ) : ℂ) * I) • (𝓕 f ξ)) =
      fun ξ : ℝ => Complex.exp (-(u : ℂ) * ((-(2 * Real.pi) * ξ : ℝ) : ℂ) * I) *
        completedRiemannZeta (1 / 2 + ((-(2 * Real.pi) * ξ : ℝ) : ℂ) * I) from funext fun ξ => by
    rw [h_four ξ, smul_eq_mul, RCLike.inner_apply]; simp only [starRingEnd_apply, star_trivial]
    congr 2; push_cast; ring,
    Measure.integral_comp_mul_left (fun t : ℝ => Complex.exp (-(u : ℂ) * (t : ℂ) * I) *
      completedRiemannZeta (1 / 2 + (t : ℂ) * I)) (-(2 * Real.pi)),
    abs_inv, abs_neg, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi), Complex.real_smul]
  dsimp [hardyG]; push_cast; ring

private lemma hasDerivAt_hardyG {z : ℂ} (hz : |z.im| < Real.pi / 4) :
    HasDerivAt hardyG (((2 * Real.pi : ℝ) : ℂ)⁻¹ *
      ∫ t : ℝ, (-((t : ℂ) * I) * Complex.exp (-z * (t : ℂ) * I)) *
        completedRiemannZeta (1 / 2 + (t : ℂ) * I)) z := by
  let α₀ : ℝ := (|z.im| + Real.pi / 4) / 2
  have hα₀_gt : |z.im| < α₀ := by dsimp [α₀]; linarith
  have hα₀_pos : 0 ≤ α₀ := (abs_nonneg _).trans hα₀_gt.le
  have hα₀_lt : α₀ < Real.pi / 4 := by dsimp [α₀]; linarith
  let ε : ℝ := α₀ - |z.im|
  let F : ℂ → ℝ → ℂ := fun w t =>
    Complex.exp (-w * (t : ℂ) * I) * completedRiemannZeta (1 / 2 + (t : ℂ) * I)
  let F' : ℂ → ℝ → ℂ := fun w t =>
    (-((t : ℂ) * I) * Complex.exp (-w * (t : ℂ) * I)) * completedRiemannZeta (1 / 2 + (t : ℂ) * I)
  let bound : ℝ → ℝ := fun t =>
    |t| * Real.exp (α₀ * |t|) * ‖completedRiemannZeta (1 / 2 + (t : ℂ) * I)‖
  have h_meas : ∀ᶠ w in 𝓝 z, AEStronglyMeasurable (F w) volume := Eventually.of_forall fun w =>
    ((Complex.continuous_exp.comp ((continuous_const.mul Complex.continuous_ofReal).mul
      continuous_const)).mul continuous_completedRiemannZeta_criticalLine).aestronglyMeasurable
  have h_int_z : Integrable (F z) := by
    refine (integrable_abs_pow_mul_exp_mul_completedRiemannZeta 0 hα₀_pos hα₀_lt).mono
      (((Complex.continuous_exp.comp ((continuous_const.mul Complex.continuous_ofReal).mul
        continuous_const)).mul continuous_completedRiemannZeta_criticalLine).aestronglyMeasurable)
      (ae_of_all _ fun t => ?_)
    dsimp [F]; rw [norm_mul, Complex.norm_exp, show (-z * (t : ℂ) * I).re = z.im * t by
        simp [Complex.mul_re, Complex.mul_im], pow_zero, one_mul, abs_of_nonneg (by positivity)]
    exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr ((le_abs_self (z.im * t)).trans
      (by rw [abs_mul]; gcongr))) (norm_nonneg _)
  have h_F'_meas : AEStronglyMeasurable (F' z) volume := (((Complex.continuous_ofReal.mul
    continuous_const).neg.mul (Complex.continuous_exp.comp ((continuous_const.mul
      Complex.continuous_ofReal).mul continuous_const))).mul
        continuous_completedRiemannZeta_criticalLine).aestronglyMeasurable
  have h_bound : ∀ᵐ t ∂volume, ∀ w ∈ Metric.ball z ε, ‖F' w t‖ ≤ bound t :=
    ae_of_all _ fun t w hw => by
      have him_diff : |w.im - z.im| ≤ ‖w - z‖ := by
        simpa [Complex.sub_im] using Complex.abs_im_le_norm (w - z)
      have htri : |w.im| ≤ |z.im| + |w.im - z.im| := by simpa using abs_add_le z.im (w.im - z.im)
      have hw_im : |w.im| ≤ α₀ := by linarith [mem_ball_iff_norm.mp hw]
      dsimp [F', bound]
      rw [norm_mul, norm_mul, norm_neg, norm_mul, Complex.norm_real, Complex.norm_I, mul_one,
        Real.norm_eq_abs, Complex.norm_exp,
        show (-w * (t : ℂ) * I).re = w.im * t by simp [Complex.mul_re, Complex.mul_im]]
      have h_le : w.im * t ≤ α₀ * |t| := (le_abs_self (w.im * t)).trans
        (by rw [abs_mul]; exact mul_le_mul hw_im le_rfl (abs_nonneg t) hα₀_pos)
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr h_le) (abs_nonneg t)) (norm_nonneg _)
  have h_diff : ∀ᵐ t ∂volume, ∀ w ∈ Metric.ball z ε, HasDerivAt (fun x => F x t) (F' w t) w :=
    ae_of_all _ fun t w _ => by
      have h_inner : HasDerivAt (fun x : ℂ => -x * (t : ℂ) * I) (-((t : ℂ) * I)) w := by
        simpa [neg_mul, mul_assoc, one_mul] using (hasDerivAt_id w).neg.mul_const ((t : ℂ) * I)
      convert h_inner.cexp.mul_const (completedRiemannZeta (1 / 2 + (t : ℂ) * I)) using 1
      dsimp [F']; ring
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le (Metric.ball_mem_nhds z (sub_pos.mpr
    hα₀_gt)) h_meas h_int_z h_F'_meas h_bound (by simpa [bound] using
      integrable_abs_pow_mul_exp_mul_completedRiemannZeta 1 hα₀_pos hα₀_lt) h_diff).2.const_mul _

/-- Equality of Hardy's Fourier integral `hardyG z` and Jacobi theta kernel `hardyPsi z`
throughout the strip `|z.im| < π / 4`. -/
theorem hardyG_eq_hardyPsi {z : ℂ} (hz : |z.im| < Real.pi / 4) :
    hardyG z = hardyPsi z := by
  let S : Set ℂ := {w : ℂ | |w.im| < Real.pi / 4}
  have hS_open : IsOpen S := isOpen_lt continuous_im.abs continuous_const
  have hS_conv : Convex ℝ S := fun x hx y hy a b ha hb hab => by
    change |((a • x + b • y : ℂ)).im| < Real.pi / 4
    have him : ((a • x + b • y : ℂ)).im = a * x.im + b * y.im := by simp
    rw [him]
    calc |a * x.im + b * y.im| ≤ a * |x.im| + b * |y.im| :=
          (abs_add_le _ _).trans_eq (by rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hb])
      _ < a * (Real.pi / 4) + b * (Real.pi / 4) := by
          rcases eq_or_lt_of_le ha with rfl | ha_pos
          · have hb1 : b = 1 := by linarith
            subst hb1; simpa [S] using hy
          · linarith [mul_lt_mul_of_pos_left hx ha_pos, mul_le_mul_of_nonneg_left (le_of_lt hy) hb]
      _ = Real.pi / 4 := by rw [← add_mul, hab, one_mul]
  have hG_ana : AnalyticOnNhd ℂ hardyG S := DifferentiableOn.analyticOnNhd
    (fun w hw => (hasDerivAt_hardyG hw).differentiableAt.differentiableWithinAt) hS_open
  have hPsi_ana : AnalyticOnNhd ℂ hardyPsi S := DifferentiableOn.analyticOnNhd
    (fun w hw => (differentiableAt_hardyPsi hw).differentiableWithinAt) hS_open
  have h_freq : ∃ᶠ w in 𝓝[≠] (0 : ℂ), hardyG w = hardyPsi w := by
    rw [Metric.nhdsWithin_basis_ball.frequently_iff]
    intro δ hδ
    let u : ℝ := min (δ / 2) 1
    have hu_pos : 0 < u := lt_min (half_pos hδ) one_pos
    refine ⟨(u : ℂ), ⟨?_, Complex.ofReal_ne_zero.mpr hu_pos.ne'⟩, hardyG_ofReal u⟩
    rw [Metric.mem_ball, dist_zero_right, Complex.norm_real, Real.norm_of_nonneg hu_pos.le]
    exact lt_of_le_of_lt (min_le_left _ _) (half_lt_self hδ)
  exact hG_ana.eqOn_of_preconnected_of_frequently_eq hPsi_ana hS_conv.isPreconnected
    (by simp [S, Real.pi_pos]) h_freq hz
