/-
Copyright (c) 2026 Qamar Munawer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qamar Munawer
-/
module

public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.NumberTheory.LSeries.HardyZ
public import RiemannBlueprint.UpstreamPRs.UpstreamPR_2B_HardyPsiAndThetaKernel
public import RiemannBlueprint.UpstreamPRs.UpstreamPR_2E_HardyGContourAndMellin

/-!
# Moment Identities for Hardy's Kernel and Derivatives Along the Imaginary Axis

For `|α| < π / 4`, the rotated Mellin transform `w ↦ hardyG (I * w)` has iterated derivatives
`hardyGn n w` obtained by differentiating under the integral sign, matching
`iteratedDeriv n (fun z => hardyPsi (I * z)) (α : ℂ)` and pairing with even cosine moments of
`(completedRiemannZeta (1 / 2 + t * I)).re`.
-/

@[expose] public section

open Complex MeasureTheory Filter Set Topology

private lemma iteratedDeriv_cexp_const_mul' (c : ℂ) (n : ℕ) (w : ℂ) :
    iteratedDeriv n (fun z : ℂ => Complex.exp (c * z)) w = c ^ n * Complex.exp (c * w) := by
  induction n generalizing w with
  | zero => simp
  | succ n ih =>
    rw [iteratedDeriv_succ']
    have hderiv_fn : deriv (fun x : ℂ => Complex.exp (c * x)) =
        fun z : ℂ => c * Complex.exp (c * z) := by
      ext z
      have h : HasDerivAt (fun x : ℂ => Complex.exp (c * x)) (c * Complex.exp (c * z)) z := by
        simpa [mul_comm, mul_one] using ((hasDerivAt_id' z).const_mul c).cexp
      exact h.deriv
    rw [hderiv_fn, iteratedDeriv_const_mul, ih, pow_succ]
    · ring
    · exact (contDiffAt_const.mul contDiffAt_id).cexp

/-- The `n`-th derivative of `w ↦ exp (I * w / 2) + exp (-(I * w) / 2)` at a real point `α`
has norm at most `2`. -/
theorem norm_iteratedDeriv_hardyCoshTerm_le (n : ℕ) (α : ℝ) :
    ‖iteratedDeriv n
      (fun w : ℂ => Complex.exp ((I * w) / 2) + Complex.exp (-(I * w) / 2)) (α : ℂ)‖ ≤ 2 := by
  have h1 : ContDiffAt ℂ n (fun w : ℂ => Complex.exp ((I * w) / 2)) (α : ℂ) :=
    ((contDiffAt_const.mul contDiffAt_id).div_const 2).cexp
  have h2 : ContDiffAt ℂ n (fun w : ℂ => Complex.exp (-(I * w) / 2)) (α : ℂ) :=
    ((contDiffAt_const.mul contDiffAt_id).neg.div_const 2).cexp
  change ‖iteratedDeriv n
    ((fun w : ℂ => Complex.exp ((I * w) / 2)) + (fun w : ℂ => Complex.exp (-(I * w) / 2)))
    (α : ℂ)‖ ≤ 2
  rw [iteratedDeriv_add h1 h2]
  have hf1 : (fun w : ℂ => Complex.exp ((I * w) / 2)) =
      fun w : ℂ => Complex.exp ((I / 2) * w) := by ext w; ring_nf
  have hf2 : (fun w : ℂ => Complex.exp (-(I * w) / 2)) =
      fun w : ℂ => Complex.exp ((-I / 2) * w) := by ext w; ring_nf
  rw [hf1, hf2, iteratedDeriv_cexp_const_mul', iteratedDeriv_cexp_const_mul']
  have hn1 : ‖(I / 2) ^ n * Complex.exp ((I / 2) * (α : ℂ))‖ ≤ 1 := by
    rw [norm_mul, norm_pow, norm_div, Complex.norm_I, Complex.norm_two,
      Complex.norm_exp, show ((I / 2) * (α : ℂ)).re = 0 by simp [Complex.mul_re],
      Real.exp_zero, mul_one]
    exact pow_le_one₀ (by positivity) (by norm_num)
  have hn2 : ‖(-I / 2) ^ n * Complex.exp ((-I / 2) * (α : ℂ))‖ ≤ 1 := by
    rw [norm_mul, norm_pow, norm_div, norm_neg, Complex.norm_I, Complex.norm_two,
      Complex.norm_exp, show ((-I / 2) * (α : ℂ)).re = 0 by simp [Complex.mul_re],
      Real.exp_zero, mul_one]
    exact pow_le_one₀ (by positivity) (by norm_num)
  exact ((norm_add_le _ _).trans (add_le_add hn1 hn2)).trans_eq (by norm_num)

/-- The `n`-th formal derivative of `w ↦ hardyG (I * w)` inside the strip `|w.re| < π / 4`. -/
noncomputable def hardyGn (n : ℕ) (w : ℂ) : ℂ :=
  ((2 * Real.pi : ℝ) : ℂ)⁻¹ *
    ∫ t : ℝ, (t : ℂ) ^ n * Complex.exp (w * (t : ℂ)) * completedRiemannZeta (1 / 2 + (t : ℂ) * I)

private lemma hasDerivAt_hardyGn (n : ℕ) {w : ℂ} (hw : |w.re| < Real.pi / 4) :
    HasDerivAt (hardyGn n) (hardyGn (n + 1) w) w := by
  let α₀ : ℝ := (|w.re| + Real.pi / 4) / 2
  have hα₀_gt : |w.re| < α₀ := by dsimp [α₀]; linarith
  have hα₀_pos : 0 ≤ α₀ := (abs_nonneg _).trans hα₀_gt.le
  have hα₀_lt : α₀ < Real.pi / 4 := by dsimp [α₀]; linarith
  let F : ℂ → ℝ → ℂ := fun z t =>
    (t : ℂ) ^ n * Complex.exp (z * (t : ℂ)) * completedRiemannZeta (1 / 2 + (t : ℂ) * I)
  let F' : ℂ → ℝ → ℂ := fun z t =>
    (t : ℂ) ^ (n + 1) * Complex.exp (z * (t : ℂ)) * completedRiemannZeta (1 / 2 + (t : ℂ) * I)
  let bound : ℝ → ℝ := fun t =>
    |t| ^ (n + 1) * Real.exp (α₀ * |t|) * ‖completedRiemannZeta (1 / 2 + (t : ℂ) * I)‖
  have h_bound_int : Integrable bound :=
    integrable_abs_pow_mul_exp_mul_completedRiemannZeta (n + 1) hα₀_pos hα₀_lt
  have h_meas_fn : ∀ (m : ℕ) (z : ℂ), AEStronglyMeasurable (fun t : ℝ => (t : ℂ) ^ m *
      Complex.exp (z * (t : ℂ)) * completedRiemannZeta (1 / 2 + (t : ℂ) * I)) volume := fun m z =>
    (((Complex.continuous_ofReal.pow m).mul
      (Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal))).mul
      continuous_completedRiemannZeta_criticalLine).aestronglyMeasurable
  have h_int_w : Integrable (F w) := by
    refine (integrable_abs_pow_mul_exp_mul_completedRiemannZeta n hα₀_pos hα₀_lt).mono
      (h_meas_fn n w) (ae_of_all _ fun t => ?_)
    dsimp [F]
    rw [norm_mul, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
      Complex.norm_exp, show (w * (t : ℂ)).re = w.re * t by simp [Complex.mul_re],
      abs_of_nonneg (mul_nonneg (mul_nonneg (pow_nonneg (abs_nonneg t) n) (Real.exp_pos _).le)
        (norm_nonneg _))]
    refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ?_ (pow_nonneg (abs_nonneg t) n))
      (norm_nonneg _)
    rw [Real.exp_le_exp]
    exact (le_abs_self (w.re * t)).trans (by rw [abs_mul]; gcongr)
  have h_bound : ∀ᵐ t ∂volume, ∀ z ∈ Metric.ball w (α₀ - |w.re|), ‖F' z t‖ ≤ bound t :=
    ae_of_all _ fun t z hz => by
      have hz_re : |z.re| ≤ α₀ := by
        have hre_diff : |z.re - w.re| ≤ ‖z - w‖ := by
          simpa [Complex.sub_re] using Complex.abs_re_le_norm (z - w)
        have htri : |z.re| ≤ |w.re| + |z.re - w.re| := by simpa using abs_add_le w.re (z.re - w.re)
        linarith [mem_ball_iff_norm.mp hz]
      dsimp [F', bound]
      rw [norm_mul, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
        Complex.norm_exp, show (z * (t : ℂ)).re = z.re * t by simp [Complex.mul_re]]
      refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ?_
        (pow_nonneg (abs_nonneg t) (n + 1))) (norm_nonneg _)
      rw [Real.exp_le_exp]
      exact (le_abs_self (z.re * t)).trans
        (by rw [abs_mul]; exact mul_le_mul hz_re le_rfl (abs_nonneg t) hα₀_pos)
  have h_diff : ∀ᵐ t ∂volume, ∀ z ∈ Metric.ball w (α₀ - |w.re|),
      HasDerivAt (fun x => F x t) (F' z t) z := ae_of_all _ fun t z _ => by
    have h_inner : HasDerivAt (fun x : ℂ => x * (t : ℂ)) (t : ℂ) z := by
      simpa using (hasDerivAt_id z).mul_const (t : ℂ)
    have h_all := (h_inner.cexp.const_mul ((t : ℂ) ^ n)).mul_const
      (completedRiemannZeta (1 / 2 + (t : ℂ) * I))
    convert h_all using 1; dsimp [F']; rw [pow_succ]; ring
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (Metric.ball_mem_nhds w (sub_pos.mpr hα₀_gt)) (Eventually.of_forall fun z => h_meas_fn n z)
    h_int_w (h_meas_fn (n + 1) w) h_bound h_bound_int h_diff).2.const_mul
    (((2 * Real.pi : ℝ) : ℂ)⁻¹)

private lemma iteratedDeriv_hardyG_mul_I (n : ℕ) {w : ℂ} (hw : |w.re| < Real.pi / 4) :
    iteratedDeriv n (fun z : ℂ => hardyG (I * z)) w = hardyGn n w := by
  induction n generalizing w with
  | zero =>
    rw [iteratedDeriv_zero]
    dsimp [hardyG, hardyGn]
    congr 2; ext t; congr 1
    rw [pow_zero, one_mul]
    congr 1
    calc -(I * w) * (t : ℂ) * I = -(I * I) * w * (t : ℂ) := by ring
      _ = w * (t : ℂ) := by rw [I_mul_I]; ring
  | succ n ih =>
    rw [iteratedDeriv_succ]
    have h_ev : iteratedDeriv n (fun z : ℂ => hardyG (I * z)) =ᶠ[𝓝 w] hardyGn n := by
      filter_upwards [(isOpen_lt continuous_re.abs continuous_const).mem_nhds hw] with z hz
      exact ih hz
    rw [h_ev.deriv_eq, (hasDerivAt_hardyGn n hw).deriv]

/-- The `n`-th derivative of `z ↦ hardyPsi (I * z)` at a real point `α` with `|α| < π / 4`
equals `hardyGn n α`. -/
theorem iteratedDeriv_hardyPsi_mul_I_eq (n : ℕ) {α : ℝ} (hα : |α| < Real.pi / 4) :
    iteratedDeriv n (fun z : ℂ => hardyPsi (I * z)) (α : ℂ) = hardyGn n (α : ℂ) := by
  have h_ev : (fun z : ℂ => hardyPsi (I * z)) =ᶠ[𝓝 (α : ℂ)] fun z : ℂ => hardyG (I * z) := by
    filter_upwards [(isOpen_lt continuous_re.abs continuous_const).mem_nhds (by simpa using hα)]
      with z hz
    exact (hardyG_eq_hardyPsi (by simpa using hz)).symm
  rw [h_ev.iteratedDeriv_eq n, iteratedDeriv_hardyG_mul_I n (by simpa using hα)]

/-- Even moment identity expressing `2π * Re(hardyGn (2k) α)` as an integral over `(0, ∞)` of
`t^(2k) * (exp(αt) + exp(-αt)) * Re(Λ(1/2 + it))`. -/
theorem hardyGn_even_re (k : ℕ) {α : ℝ} (hα : |α| < Real.pi / 4) :
    (2 * Real.pi) * (hardyGn (2 * k) (α : ℂ)).re =
      ∫ t in Ioi (0 : ℝ),
        t ^ (2 * k) * (Real.exp (α * t) + Real.exp (-α * t)) *
          (completedRiemannZeta (1 / 2 + (t : ℂ) * I)).re := by
  let Λre : ℝ → ℝ := fun t => (completedRiemannZeta (1 / 2 + (t : ℂ) * I)).re
  have hΛ_even : ∀ t : ℝ, Λre (-t) = Λre t := fun t => by
    have h1 := completedRiemannZeta_one_sub (1 / 2 + (t : ℂ) * I)
    rw [show 1 - (1 / 2 + (t : ℂ) * I) = 1 / 2 + ((-t : ℝ) : ℂ) * I by push_cast; ring] at h1
    dsimp [Λre]; rw [h1]
  have h_integrand_eq : (fun t : ℝ => (t : ℂ) ^ (2 * k) * Complex.exp ((α : ℂ) * (t : ℂ)) *
      completedRiemannZeta (1 / 2 + (t : ℂ) * I)) =
      fun t : ℝ => ((t ^ (2 * k) * Real.exp (α * t) * Λre t : ℝ) : ℂ) := by
    ext t
    have h_conj : ((Λre t : ℝ) : ℂ) = completedRiemannZeta (1 / 2 + (t : ℂ) * I) :=
      Complex.conj_eq_iff_re.mp (by
        rw [Complex.conj_eq_iff_im]; exact completedRiemannZeta_half_add_mul_I_im t)
    rw [← h_conj]; push_cast; ring
  have h_int_bound : ∀ (c : ℝ), |c| < Real.pi / 4 →
      Integrable (fun t : ℝ => t ^ (2 * k) * Real.exp (c * t) * Λre t) := fun c hc => by
    refine (integrable_abs_pow_mul_exp_mul_completedRiemannZeta (2 * k) (abs_nonneg c) hc).mono
      ((((continuous_id.pow (2 * k)).mul
        (Real.continuous_exp.comp (continuous_const.mul continuous_id))).mul
        (Complex.continuous_re.comp
          continuous_completedRiemannZeta_criticalLine)).aestronglyMeasurable)
      (ae_of_all _ fun t => ?_)
    have hΛ_norm : |Λre t| = ‖completedRiemannZeta (1 / 2 + (t : ℂ) * I)‖ := by
      rw [Complex.norm_def, Complex.normSq_apply, completedRiemannZeta_half_add_mul_I_im t,
        mul_zero, add_zero, Real.sqrt_mul_self_eq_abs]
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_pow, abs_of_pos (Real.exp_pos _), hΛ_norm,
      Real.norm_of_nonneg (by positivity)]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
      ((le_abs_self (c * t)).trans (by rw [abs_mul]))) (pow_nonneg (abs_nonneg t) _))
      (norm_nonneg _)
  have h_int_full := h_int_bound α hα
  have h_int_re : (hardyGn (2 * k) (α : ℂ)).re =
      (2 * Real.pi)⁻¹ * ∫ t : ℝ, t ^ (2 * k) * Real.exp (α * t) * Λre t := by
    dsimp [hardyGn]
    have h_int_c : Integrable (fun t : ℝ => ((t ^ (2 * k) * Real.exp (α * t) * Λre t : ℝ) : ℂ)) :=
      Complex.ofRealCLM.integrable_comp h_int_full
    have h_re_int : (∫ t : ℝ, ((t ^ (2 * k) * Real.exp (α * t) * Λre t : ℝ) : ℂ)).re =
        ∫ t : ℝ, t ^ (2 * k) * Real.exp (α * t) * Λre t := by
      change Complex.reCLM (∫ t : ℝ, ((t ^ (2 * k) * Real.exp (α * t) * Λre t : ℝ) : ℂ)) = _
      rw [← Complex.reCLM.integral_comp_comm h_int_c]
      simp only [Complex.reCLM_apply, Complex.ofReal_re]
    rw [h_integrand_eq, ← Complex.ofReal_inv (2 * Real.pi), Complex.re_ofReal_mul, h_re_int]
  rw [h_int_re, ← mul_assoc, mul_inv_cancel₀ (by positivity : 2 * Real.pi ≠ 0), one_mul]
  have h_split : ∫ t : ℝ, t ^ (2 * k) * Real.exp (α * t) * Λre t =
      (∫ t in Iic (0 : ℝ), t ^ (2 * k) * Real.exp (α * t) * Λre t) +
      (∫ t in Ioi (0 : ℝ), t ^ (2 * k) * Real.exp (α * t) * Λre t) := by
    rw [← MeasureTheory.setIntegral_union (Iic_disjoint_Ioi (le_refl (0 : ℝ))) measurableSet_Ioi
      h_int_full.integrableOn h_int_full.integrableOn, Iic_union_Ioi, setIntegral_univ]
  have h_Iic : ∫ t in Iic (0 : ℝ), t ^ (2 * k) * Real.exp (α * t) * Λre t =
      ∫ t in Ioi (0 : ℝ), t ^ (2 * k) * Real.exp (-α * t) * Λre t := by
    have h_fn : (fun t : ℝ => t ^ (2 * k) * Real.exp (α * t) * Λre t) =
        fun t : ℝ => (fun x : ℝ => x ^ (2 * k) * Real.exp (-α * x) * Λre x) (-t) := by
      ext t; dsimp only
      have h_even_pow : (-t) ^ (2 * k) = t ^ (2 * k) := by rw [pow_mul, neg_sq, ← pow_mul]
      rw [h_even_pow, hΛ_even t, neg_mul]; ring_nf
    rw [h_fn, integral_comp_neg_Iic 0 (fun x : ℝ => x ^ (2 * k) * Real.exp (-α * x) * Λre x),
      neg_zero]
  rw [h_split, h_Iic, ← integral_add (h_int_bound (-α) (by simpa using hα)).integrableOn
    h_int_full.integrableOn]
  exact setIntegral_congr_fun measurableSet_Ioi fun t _ => by ring
