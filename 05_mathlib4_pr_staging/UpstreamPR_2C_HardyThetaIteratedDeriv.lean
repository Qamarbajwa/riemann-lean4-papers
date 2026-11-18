/-
Copyright (c) 2026 Qamar Munawer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qamar Munawer
-/
module

public import Mathlib.Analysis.Complex.Liouville
public import RiemannBlueprint.UpstreamPRs.UpstreamPR_2B_HardyPsiAndThetaKernel

/-!
# Exponential Boundary Vanishing of Higher Derivatives of `hardyThetaTerm`

Using Jacobi's modular inversion `jacobiTheta_S_smul` and Cauchy's iterated derivative estimate
on circles tangent to the boundary `Re(w) = π / 4`, this file establishes:
1. `norm_jacobiTheta_neg_one_add_le`: super-exponential boundary bound at `-1 + η`.
2. `tendsto_iteratedDeriv_hardyThetaTerm`:
   `‖iteratedDeriv (2 * k) (fun w => hardyThetaTerm (I * w)) (π / 4 - δ)‖ → 0` as `δ → 0⁺`.
-/

@[expose] public section

open Complex Filter Set
open scoped Topology UpperHalfPlane

private lemma cpow_neg_half_four_mul {z : ℂ} (hz : 0 < z.re) :
    ((4 : ℂ) * z) ^ (-(1 / 2 : ℂ)) = (1 / 2 : ℂ) * z ^ (-(1 / 2 : ℂ)) := by
  have hz0 : z ≠ 0 := fun h => by rw [h] at hz; simp at hz
  have hargz : |z.arg| < Real.pi / 2 := Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hz)
  have hlog : Complex.log ((4 : ℂ) * z) = Complex.log (4 : ℂ) + Complex.log z := by
    refine Complex.log_mul (by norm_num) hz0 ?_
    rw [show (4 : ℂ) = ((4 : ℝ) : ℂ) by norm_num, Complex.arg_ofReal_of_nonneg (by norm_num),
      zero_add]
    have h1 := (abs_lt.mp hargz).1; have h2 := (abs_lt.mp hargz).2
    constructor <;> linarith [Real.pi_pos]
  rw [Complex.cpow_def_of_ne_zero (mul_ne_zero (by norm_num) hz0), Complex.cpow_def_of_ne_zero hz0,
    hlog, add_mul, Complex.exp_add]
  congr 1
  have hreal : Real.exp (-(1 / 2 : ℝ) * Real.log 4) = 1 / 2 := by
    rw [mul_comm, ← Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 4), Real.rpow_neg (by norm_num),
      show (4 : ℝ) ^ (1 / 2 : ℝ) = 2 by
        rw [← Real.sqrt_eq_rpow, show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    norm_num
  rw [mul_comm, show (4 : ℂ) = ((4 : ℝ) : ℂ) by norm_num, ← Complex.ofReal_log (by norm_num),
    show -(1 / 2 : ℂ) * ((Real.log 4 : ℝ) : ℂ) = ((-(1 / 2) * Real.log 4 : ℝ) : ℂ) by
      push_cast; ring, ← Complex.ofReal_exp, hreal]
  norm_num

private lemma jacobiTheta_sub_one_le_four_exp {s : ℂ} (hs : 0 < s.im) (hbig : 1 ≤ Real.pi * s.im) :
    ‖jacobiTheta s - 1‖ ≤ 4 * Real.exp (-Real.pi * s.im) := by
  have h_exp_half : Real.exp (-Real.pi * s.im) ≤ 1 / 2 := by
    have := Real.add_one_le_exp (1 : ℝ)
    calc Real.exp (-Real.pi * s.im) ≤ Real.exp (-1) := Real.exp_le_exp.mpr (by linarith)
      _ ≤ 1 / 2 := by rw [Real.exp_neg, inv_le_iff_one_le_mul₀ (by linarith)]; linarith
  have h_den : 2 / (1 - Real.exp (-Real.pi * s.im)) ≤ 4 := by
    rw [div_le_iff₀ (by linarith)]; linarith
  exact (norm_jacobiTheta_sub_one_le hs).trans
    (mul_le_mul_of_nonneg_right h_den (Real.exp_pos _).le)

private lemma jacobiTheta_inv_formula {w : ℂ} (hw : 0 < w.im) :
    let σ : ℂ := -w⁻¹
    0 < σ.im ∧ jacobiTheta w = (-I * w) ^ (-(1 / 2 : ℂ)) * jacobiTheta σ := by
  have hσ_im : 0 < (-w⁻¹).im := by
    have : (-w⁻¹).im = w.im / ‖w‖ ^ 2 := by
      simp [Complex.inv_im, Complex.normSq_eq_norm_sq, div_eq_mul_inv]
    have hw0 : 0 < ‖w‖ := norm_pos_iff.mpr fun h => by rw [h] at hw; simp at hw
    rw [this]; exact div_pos hw (sq_pos_of_pos hw0)
  refine ⟨hσ_im, ?_⟩
  let τ : ℍ := ⟨-w⁻¹, hσ_im⟩
  have hS := jacobiTheta_S_smul τ
  have h_mod : ((ModularGroup.S • τ : ℍ) : ℂ) = w := by
    rw [UpperHalfPlane.modular_S_smul]; change (-(τ : ℂ))⁻¹ = w; simp [τ]
  have h_arg : (-I * w).arg ≠ Real.pi := by
    have hlt := Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl (by simp [hw] : 0 < (-I * w).re))
    intro h; rw [h, abs_of_pos Real.pi_pos] at hlt; linarith [Real.pi_pos]
  have h_pow : (-I * (τ : ℂ)) ^ (1 / 2 : ℂ) = (-I * w) ^ (-(1 / 2 : ℂ)) := by
    rw [show -I * (τ : ℂ) = (-I * w)⁻¹ by
        dsimp [τ]; rw [mul_neg, neg_mul, neg_neg, mul_inv, inv_neg, inv_I, neg_neg],
      Complex.inv_cpow (-I * w) (1 / 2 : ℂ) h_arg, Complex.cpow_neg]
  change jacobiTheta ((ModularGroup.S • τ : ℍ) : ℂ) =
    (-I * (τ : ℂ)) ^ (1 / 2 : ℂ) * jacobiTheta (τ : ℂ) at hS
  rwa [h_mod, h_pow] at hS

/-- Boundary exponential decay for `jacobiTheta (-1 + η)` when `π * η.im / (4 * ‖η‖ ^ 2) ≥ 1`. -/
theorem norm_jacobiTheta_neg_one_add_le {η : ℂ} (hη_im : 0 < η.im)
    (h_big : 1 ≤ Real.pi * (η.im / (4 * ‖η‖ ^ 2))) :
    ‖jacobiTheta (-1 + η)‖ ≤
      8 * Real.sqrt (η.im⁻¹) * Real.exp (-Real.pi * (η.im / (4 * ‖η‖ ^ 2))) := by
  have hη0 : η ≠ 0 := fun h => by rw [h] at hη_im; simp at hη_im
  obtain ⟨hσ_pos, hS1⟩ := jacobiTheta_inv_formula hη_im
  obtain ⟨hσ₄_pos, hS4⟩ := jacobiTheta_inv_formula (by simp [hη_im] : 0 < (4 * η).im)
  have hσ_im : (-η⁻¹).im = η.im / ‖η‖ ^ 2 := by
    simp [Complex.inv_im, Complex.normSq_eq_norm_sq, div_eq_mul_inv]
  have hσ₄_im : (-(4 * η)⁻¹).im = η.im / (4 * ‖η‖ ^ 2) := by
    simp [Complex.inv_im, Complex.normSq_eq_norm_sq]; ring
  have hσ_ge : (-(4 * η)⁻¹).im ≤ (-η⁻¹).im := by
    rw [hσ_im, hσ₄_im]; gcongr; linarith [sq_nonneg ‖η‖]
  have hS4' : jacobiTheta (4 * η) =
      (1 / 2 : ℂ) * (-I * η) ^ (-(1 / 2 : ℂ)) * jacobiTheta (-(4 * η)⁻¹) := by
    rwa [show (-I * (4 * η)) ^ (-(1 / 2 : ℂ)) = (1 / 2 : ℂ) * (-I * η) ^ (-(1 / 2 : ℂ)) by
      rw [show -I * (4 * η) = (4 : ℂ) * (-I * η) by ring,
        cpow_neg_half_four_mul (by simp [hη_im])]] at hS4
  have h_e1 : ‖jacobiTheta (-η⁻¹) - 1‖ ≤ 4 * Real.exp (-Real.pi * (-(4 * η)⁻¹).im) :=
    (jacobiTheta_sub_one_le_four_exp hσ_pos (by
      calc 1 ≤ Real.pi * (-(4 * η)⁻¹).im := by rwa [hσ₄_im]
        _ ≤ Real.pi * (-η⁻¹).im := mul_le_mul_of_nonneg_left hσ_ge Real.pi_pos.le)).trans
      (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
        (mul_le_mul_of_nonpos_left hσ_ge (neg_nonpos.mpr Real.pi_pos.le))) (by norm_num))
  have h_e4 : ‖jacobiTheta (-(4 * η)⁻¹) - 1‖ ≤ 4 * Real.exp (-Real.pi * (-(4 * η)⁻¹).im) :=
    jacobiTheta_sub_one_le_four_exp hσ₄_pos (by rwa [hσ₄_im])
  have h_pow_norm : ‖(-I * η) ^ (-(1 / 2 : ℂ))‖ ≤ Real.sqrt (η.im⁻¹) := by
    have hnz := mul_ne_zero (neg_ne_zero.mpr I_ne_zero) hη0
    rw [Complex.cpow_def_of_ne_zero hnz, Complex.norm_exp,
      show (Complex.log (-I * η) * -(1 / 2 : ℂ)).re =
        (Complex.log (-I * η)).re * -(1 / 2 : ℝ) by simp [Complex.mul_re],
      Complex.log_re, ← Real.rpow_def_of_pos (norm_pos_iff.mpr hnz),
      Real.rpow_neg (norm_nonneg _), Real.sqrt_eq_rpow, ← Real.inv_rpow (norm_nonneg _),
      norm_mul, norm_neg, Complex.norm_I, one_mul]
    simpa only [Real.sqrt_eq_rpow] using Real.sqrt_le_sqrt (inv_anti₀ hη_im (Complex.im_le_norm η))
  rw [jacobiTheta_neg_one_add hη_im, show 2 * jacobiTheta (4 * η) - jacobiTheta η =
      (-I * η) ^ (-(1 / 2 : ℂ)) * ((jacobiTheta (-(4 * η)⁻¹) - 1) - (jacobiTheta (-η⁻¹) - 1)) by
      rw [hS4', hS1]; ring, norm_mul]
  refine (mul_le_mul h_pow_norm (norm_sub_le _ _) (norm_nonneg _) (Real.sqrt_nonneg _)).trans ?_
  rw [← hσ₄_im]; linarith [mul_le_mul_of_nonneg_left (add_le_add h_e4 h_e1)
    (Real.sqrt_nonneg (η.im⁻¹))]

/-- Vanishing of the `2 * k`-th derivative of `w ↦ hardyThetaTerm (I * w)` as `w → (π / 4)⁻`. -/
theorem tendsto_iteratedDeriv_hardyThetaTerm (k : ℕ) :
    Tendsto (fun δ : ℝ => ‖iteratedDeriv (2 * k) (fun w : ℂ => hardyThetaTerm (I * w))
        ((Real.pi / 4 - δ : ℝ) : ℂ)‖) (𝓝[>] (0 : ℝ)) (nhds 0) := by
  let c_im : ℝ := Real.exp (-1) * (2 / Real.pi)
  have hc_im : 0 < c_im := by positivity
  let c_decay : ℝ := Real.pi * c_im / 256
  have hc_decay : 0 < c_decay := by positivity
  let δ₀ : ℝ := min (Real.pi / 16) (min (1 / 4) c_decay)
  have hδ₀ : 0 < δ₀ := by positivity
  have h_bound_ev : ∀ᶠ δ in 𝓝[>] (0 : ℝ),
      ‖iteratedDeriv (2 * k) (fun w : ℂ => hardyThetaTerm (I * w))
        ((Real.pi / 4 - δ : ℝ) : ℂ)‖ ≤
        ((2 * k).factorial : ℝ) * (Real.exp 1 * 8 * (c_im⁻¹ + 1)) * (2 : ℝ) ^ (2 * k) *
          (δ⁻¹) ^ (2 * k + 1) * Real.exp (-c_decay * δ⁻¹) := by
    filter_upwards [Ioo_mem_nhdsGT hδ₀] with δ hδ
    have hδ_pos : 0 < δ := hδ.1
    have hδ_le_pi16 : δ ≤ Real.pi / 16 := hδ.2.le.trans (min_le_left _ _)
    have hδ_le_1 : δ ≤ 1 := hδ.2.le.trans ((min_le_right _ _).trans
      ((min_le_left _ _).trans (by norm_num)))
    have hδ_le_dec : δ ≤ c_decay := hδ.2.le.trans ((min_le_right _ _).trans (min_le_right _ _))
    let center : ℂ := ((Real.pi / 4 - δ : ℝ) : ℂ)
    let R : ℝ := δ / 2
    have hR : R = δ / 2 := rfl
    have hcr : center.re = Real.pi / 4 - δ := by simp [center]
    have hci : center.im = 0 := by simp [center]
    have h_diff_ball : DiffContOnCl ℂ (fun w : ℂ => hardyThetaTerm (I * w))
        (Metric.ball center R) := by
      have h_sub : Metric.closedBall center R ⊆ {w : ℂ | |w.re| < Real.pi / 4} := fun w hw => by
        have hre_diff : |w.re - (Real.pi / 4 - δ)| ≤ R := by
          simpa [Complex.sub_re, hcr] using
            (Complex.abs_re_le_norm (w - center)).trans (mem_closedBall_iff_norm.mp hw)
        have h1 : Real.pi / 4 - 3 * δ / 2 ≤ w.re := by linarith [(abs_le.mp hre_diff).1, hR]
        have h2 : w.re ≤ Real.pi / 4 - δ / 2 := by linarith [(abs_le.mp hre_diff).2, hR]
        refine abs_lt.mpr ⟨?_, h2.trans_lt (sub_lt_self _ (half_pos hδ_pos))⟩
        have h_lo : -(Real.pi / 4) < Real.pi / 4 - 3 * (Real.pi / 16) / 2 := by
          linarith [Real.pi_pos]
        exact h_lo.trans_le (by linarith [show 3 * δ / 2 ≤ 3 * (Real.pi / 16) / 2 by gcongr])
      exact ⟨differentiableOn_hardyThetaTerm_mul_I.mono (Metric.ball_subset_closedBall.trans h_sub),
        (differentiableOn_hardyThetaTerm_mul_I.mono
          (Metric.closure_ball_subset_closedBall.trans h_sub)).continuousOn⟩
    have h_sphere : ∀ w ∈ Metric.sphere center R, ‖hardyThetaTerm (I * w)‖ ≤
        Real.exp 1 * 8 * (c_im⁻¹ + 1) * δ⁻¹ * Real.exp (-c_decay * δ⁻¹) := fun w hw => by
      have hw_dist : ‖w - center‖ = R := mem_sphere_iff_norm.mp hw
      have hre_diff : |w.re - (Real.pi / 4 - δ)| ≤ R := by
        simpa [Complex.sub_re, hcr, hw_dist] using Complex.abs_re_le_norm (w - center)
      have him_diff : |w.im| ≤ R := by
        simpa [Complex.sub_im, hci, hw_dist] using Complex.abs_im_le_norm (w - center)
      let u : ℂ := (Real.pi / 4 : ℂ) - w
      have hu_re_lo : δ / 2 ≤ u.re := by simp [u]; linarith [(abs_le.mp hre_diff).2, hR]
      have hu_re_hi : u.re ≤ 3 * δ / 2 := by simp [u]; linarith [(abs_le.mp hre_diff).1, hR]
      have hu_im : |u.im| ≤ δ / 2 := by
        have : u.im = -w.im := by simp [u]
        rw [this, abs_neg]; linarith [him_diff, hR]
      let η : ℂ := 1 - Complex.exp (-2 * I * u)
      have h_tau : I * Complex.exp (2 * (I * w)) = -1 + η := by
        rw [show 2 * (I * w) = (Real.pi / 2 : ℂ) * I + (-2 * I * u) by dsimp [u]; ring,
          Complex.exp_add, Complex.exp_pi_div_two_mul_I]
        dsimp [η]; rw [← mul_assoc, I_mul_I]; ring
      have hη_im : c_im * δ ≤ η.im := by
        have him_eq : η.im = Real.exp (2 * u.im) * Real.sin (2 * u.re) := by
          dsimp [η]; simp only [zero_sub, Complex.exp_im]
          rw [show (-2 * I * u).re = 2 * u.im by simp [Complex.mul_re, Complex.mul_im],
            show (-2 * I * u).im = -2 * u.re by simp [Complex.mul_re, Complex.mul_im],
            show (-2 * u.re : ℝ) = -(2 * u.re) by ring, Real.sin_neg]; ring
        have hsin : (2 / Real.pi) * δ ≤ Real.sin (2 * u.re) :=
          (mul_le_mul_of_nonneg_left (by linarith) (by positivity)).trans
            (Real.mul_le_sin (by linarith) (by linarith [Real.pi_pos, hδ_le_pi16]))
        have hexp_im : Real.exp (-1) ≤ Real.exp (2 * u.im) := by
          rw [Real.exp_le_exp]; linarith [(abs_le.mp hu_im).1, hδ_le_1]
        rw [him_eq]; exact (mul_le_mul hexp_im hsin (by positivity) (Real.exp_pos _).le).trans_eq'
          (by dsimp [c_im]; ring)
      have hη_im_pos : 0 < η.im := lt_of_lt_of_le (mul_pos hc_im hδ_pos) hη_im
      have hη_norm : ‖η‖ ≤ 8 * δ := by
        have hδ_le_4 : δ ≤ 1 / 4 := hδ.2.le.trans ((min_le_right _ _).trans (min_le_left _ _))
        have hu_norm : ‖u‖ ≤ 2 * δ := by
          have := Complex.norm_le_abs_re_add_abs_im u
          rw [abs_of_nonneg (by linarith)] at this; linarith [hu_im]
        have h_arg_norm : ‖-2 * I * u‖ ≤ 1 := by
          rw [norm_mul, norm_mul, norm_neg, Complex.norm_two, Complex.norm_I, mul_one]; linarith
        rw [show η = -(Complex.exp (-2 * I * u) - 1) by dsimp [η]; ring, norm_neg]
        exact (Complex.norm_exp_sub_one_le h_arg_norm).trans (by
          rw [norm_mul, norm_mul, norm_neg, Complex.norm_two, Complex.norm_I, mul_one]; linarith)
      have hη_norm_pos : 0 < ‖η‖ :=
        norm_pos_iff.mpr fun h => by rw [h] at hη_im_pos; simp at hη_im_pos
      have h_ratio_lo : c_decay * δ⁻¹ ≤ Real.pi * (η.im / (4 * ‖η‖ ^ 2)) :=
        calc c_decay * δ⁻¹ = Real.pi * (c_im * δ / (4 * (8 * δ) ^ 2)) := by
              dsimp [c_decay]; field_simp [hδ_pos.ne']; ring
          _ ≤ Real.pi * (η.im / (4 * ‖η‖ ^ 2)) := by gcongr
      have h_big : 1 ≤ Real.pi * (η.im / (4 * ‖η‖ ^ 2)) :=
        ((mul_inv_cancel₀ hδ_pos.ne').symm.trans_le
          (mul_le_mul_of_nonneg_right hδ_le_dec (inv_nonneg.mpr hδ_pos.le))).trans h_ratio_lo
      have h_sqrt_bd : Real.sqrt (η.im⁻¹) ≤ (c_im⁻¹ + 1) * δ⁻¹ := by
        have h2 := inv_anti₀ (mul_pos hc_im hδ_pos) hη_im
        rw [mul_inv] at h2
        nlinarith [Real.sq_sqrt (inv_nonneg.mpr hη_im_pos.le), (one_le_inv₀ hδ_pos).mpr hδ_le_1]
      have h_pref_bd : ‖Complex.exp ((I * w) / 2)‖ ≤ Real.exp 1 := by
        rw [Complex.norm_exp, show ((I * w) / 2).re = -w.im / 2 by simp [Complex.mul_re],
          Real.exp_le_exp]
        linarith [(abs_le.mp him_diff).1, hδ_le_1, hR]
      dsimp [hardyThetaTerm]; rw [h_tau, norm_mul]
      refine (mul_le_mul h_pref_bd (norm_jacobiTheta_neg_one_add_le hη_im_pos h_big)
        (norm_nonneg _) (Real.exp_pos _).le).trans ?_
      have h_exp_bd : Real.exp (-Real.pi * (η.im / (4 * ‖η‖ ^ 2))) ≤
          Real.exp (-c_decay * δ⁻¹) := Real.exp_le_exp.mpr (by linarith)
      nlinarith [mul_le_mul_of_nonneg_left (mul_le_mul h_sqrt_bd h_exp_bd (Real.exp_pos _).le
        (by positivity)) (mul_pos (Real.exp_pos 1) (by norm_num : (0 : ℝ) < 8)).le]
    calc ‖iteratedDeriv (2 * k) (fun w : ℂ => hardyThetaTerm (I * w)) center‖
        ≤ (2 * k).factorial * (Real.exp 1 * 8 * (c_im⁻¹ + 1) * δ⁻¹ * Real.exp (-c_decay * δ⁻¹)) /
            R ^ (2 * k) := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le
            (2 * k) (half_pos hδ_pos) h_diff_ball h_sphere
      _ = ((2 * k).factorial : ℝ) * (Real.exp 1 * 8 * (c_im⁻¹ + 1)) * (2 : ℝ) ^ (2 * k) *
            (δ⁻¹) ^ (2 * k + 1) * Real.exp (-c_decay * δ⁻¹) := by
          dsimp [R]; rw [div_pow, inv_pow, pow_succ]; field_simp [hδ_pos.ne']
  have h_top : Tendsto (fun x : ℝ => x ^ (2 * k + 1) * Real.exp (-c_decay * x)) atTop (nhds 0) := by
    let C_k : ℝ := ((2 * k + 1).factorial : ℝ) / (c_decay / 2) ^ (2 * k + 1)
    refine squeeze_zero' (g := fun x : ℝ => C_k * Real.exp (-(c_decay / 2) * x))
      ((eventually_ge_atTop (0 : ℝ)).mono fun _ _ => by positivity) ?_ (by
        simpa [mul_zero] using (Real.tendsto_exp_atBot.comp
          (tendsto_id.const_mul_atTop_of_neg (by linarith : -(c_decay / 2) < 0))).const_mul C_k)
    filter_upwards [eventually_ge_atTop 0] with x hx
    have hexp := Real.pow_div_factorial_le_exp ((c_decay / 2) * x)
      (mul_nonneg (half_pos hc_decay).le hx) (2 * k + 1)
    rw [mul_pow, div_le_iff₀ (Nat.cast_pos.mpr (2 * k + 1).factorial_pos),
      ← le_div_iff₀' (pow_pos (half_pos hc_decay) (2 * k + 1))] at hexp
    refine (mul_le_mul_of_nonneg_right hexp (Real.exp_pos _).le).trans_eq ?_
    calc (Real.exp ((c_decay / 2) * x) * ((2 * k + 1).factorial : ℝ)) /
          (c_decay / 2) ^ (2 * k + 1) * Real.exp (-c_decay * x)
        = C_k * (Real.exp ((c_decay / 2) * x) * Real.exp (-c_decay * x)) := by dsimp [C_k]; ring
      _ = C_k * Real.exp (-(c_decay / 2) * x) := by rw [← Real.exp_add]; congr 2; ring
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds ?_
    (Eventually.of_forall fun _ => norm_nonneg _) h_bound_ev
  simpa [mul_zero, mul_assoc] using (h_top.comp tendsto_inv_nhdsGT_zero).const_mul
    (((2 * k).factorial : ℝ) * (Real.exp 1 * 8 * (c_im⁻¹ + 1)) * (2 : ℝ) ^ (2 * k))
