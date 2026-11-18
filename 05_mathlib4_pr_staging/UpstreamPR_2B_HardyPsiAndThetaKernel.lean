/-
Copyright (c) 2026 Qamar Munawer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qamar Munawer
-/
module

public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.NumberTheory.ModularForms.JacobiTheta.OneVariable
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-!
# Hardy Psi and Jacobi Theta Kernel on the Strip `|z.im| < π / 4`

This file defines Hardy's theta kernel `hardyPsi` and `hardyThetaTerm` and proves:
1. Strip holomorphicity (`differentiableAt_hardyPsi`, `differentiableOn_hardyThetaTerm_mul_I`).
2. Modular symmetry `hardyPsi (-z) = hardyPsi z` (`hardyPsi_neg`) via `jacobiTheta_S_smul`.
3. Rapid horizontal Gaussian decay (`norm_hardyPsi_le`, `integrable_hardyPsi_shift`).
4. Parity decomposition `jacobiTheta (-1 + η) = 2 * jacobiTheta (4 * η) - jacobiTheta η`.
-/

@[expose] public section

open Complex Set Filter MeasureTheory
open scoped UpperHalfPlane

/-- Hardy's theta-remainder kernel
`exp (z / 2) * jacobiTheta (I * exp (2 * z)) - (exp (z / 2) + exp (-z / 2))`. -/
noncomputable def hardyPsi (z : ℂ) : ℂ :=
  Complex.exp (z / 2) * jacobiTheta (I * Complex.exp (2 * z)) -
    (Complex.exp (z / 2) + Complex.exp (-z / 2))

/-- The theta component of `hardyPsi z`: `exp (z / 2) * jacobiTheta (I * exp (2 * z))`. -/
noncomputable def hardyThetaTerm (z : ℂ) : ℂ :=
  Complex.exp (z / 2) * jacobiTheta (I * Complex.exp (2 * z))

/-- Positivity of `(I * exp (2 * z)).im` in the horizontal strip `|z.im| < π / 4`. -/
theorem im_I_mul_exp_two_mul_pos {z : ℂ} (hz : |z.im| < Real.pi / 4) :
    0 < (I * Complex.exp (2 * z)).im := by
  have him : (I * Complex.exp (2 * z)).im = Real.exp (2 * z.re) * Real.cos (2 * z.im) := by
    rw [Complex.mul_im, Complex.I_re, Complex.I_im, zero_mul, one_mul, zero_add, Complex.exp_re]
    simp
  rw [him]
  have hcos : 0 < Real.cos (2 * z.im) := by
    apply Real.cos_pos_of_mem_Ioo
    have h1 := (abs_lt.mp hz).1
    have h2 := (abs_lt.mp hz).2
    constructor <;> linarith
  exact mul_pos (Real.exp_pos _) hcos

/-- Complex differentiability of `hardyPsi` on the strip `|z.im| < π / 4`. -/
theorem differentiableAt_hardyPsi {z : ℂ} (hz : |z.im| < Real.pi / 4) :
    DifferentiableAt ℂ hardyPsi z := by
  have hθ := differentiableAt_jacobiTheta (im_I_mul_exp_two_mul_pos hz)
  have hτ : DifferentiableAt ℂ (fun w : ℂ => I * Complex.exp (2 * w)) z :=
    (differentiableAt_const _).mul ((differentiableAt_const (2 : ℂ)).mul differentiableAt_id).cexp
  have h1 : DifferentiableAt ℂ (fun w : ℂ => Complex.exp (w / 2)) z :=
    (differentiableAt_id.div_const 2).cexp
  have h2 : DifferentiableAt ℂ (fun w : ℂ => Complex.exp (-w / 2)) z :=
    (differentiableAt_id.neg.div_const 2).cexp
  have h3 : DifferentiableAt ℂ (jacobiTheta ∘ fun w : ℂ => I * Complex.exp (2 * w)) z :=
    hθ.comp z hτ
  change DifferentiableAt ℂ (fun w : ℂ => Complex.exp (w / 2) *
    jacobiTheta (I * Complex.exp (2 * w)) - (Complex.exp (w / 2) + Complex.exp (-w / 2))) z
  exact (h1.mul h3).sub (h1.add h2)

/-- Complex differentiability of `w ↦ hardyThetaTerm (I * w)` on `{w | |w.re| < π / 4}`. -/
theorem differentiableOn_hardyThetaTerm_mul_I :
    DifferentiableOn ℂ (fun w : ℂ => hardyThetaTerm (I * w)) {w : ℂ | |w.re| < Real.pi / 4} := by
  intro w hw
  have him : |(I * w).im| < Real.pi / 4 := by simpa using hw
  have hθ := differentiableAt_jacobiTheta (im_I_mul_exp_two_mul_pos him)
  have h_cexp : DifferentiableAt ℂ (fun x : ℂ => Complex.exp (2 * (I * x))) w :=
    ((differentiableAt_const (2 : ℂ)).mul ((differentiableAt_const I).mul differentiableAt_id)).cexp
  have h_jac : DifferentiableAt ℂ
      (jacobiTheta ∘ fun x : ℂ => I * Complex.exp (2 * (I * x))) w :=
    hθ.comp w ((differentiableAt_const I).mul h_cexp)
  have h_left : DifferentiableAt ℂ (fun x : ℂ => Complex.exp ((I * x) / 2)) w :=
    (((differentiableAt_const I).mul differentiableAt_id).div_const 2).cexp
  change DifferentiableWithinAt ℂ
    (fun x : ℂ => Complex.exp ((I * x) / 2) * jacobiTheta (I * Complex.exp (2 * (I * x)))) _ w
  exact (h_left.mul h_jac).differentiableWithinAt

/-- Functional reflection symmetry `hardyPsi (-z) = hardyPsi z` for `|z.im| < π / 4`. -/
theorem hardyPsi_neg {z : ℂ} (hz : |z.im| < Real.pi / 4) :
    hardyPsi (-z) = hardyPsi z := by
  let τ : ℍ := ⟨I * Complex.exp (2 * z), im_I_mul_exp_two_mul_pos hz⟩
  have hS := jacobiTheta_S_smul τ
  have h_mod : ((ModularGroup.S • τ : ℍ) : ℂ) = I * Complex.exp (-2 * z) := by
    rw [UpperHalfPlane.modular_S_smul]
    change (-(I * Complex.exp (2 * z)))⁻¹ = I * Complex.exp (-2 * z)
    rw [inv_neg, mul_inv, inv_I, show -2 * z = -(2 * z) by ring, Complex.exp_neg]
    ring
  have h_cpow : (-I * (τ : ℂ)) ^ (1 / 2 : ℂ) = Complex.exp z := by
    change (-I * (I * Complex.exp (2 * z))) ^ (1 / 2 : ℂ) = Complex.exp z
    rw [show -I * (I * Complex.exp (2 * z)) = Complex.exp (2 * z) by
      rw [← mul_assoc, neg_mul, I_mul_I, neg_neg, one_mul],
      Complex.cpow_def_of_ne_zero (Complex.exp_ne_zero _)]
    have him2 : -(Real.pi) < (2 * z).im ∧ (2 * z).im ≤ Real.pi := by
      have h1 := (abs_lt.mp hz).1; have h2 := (abs_lt.mp hz).2
      simp only [Complex.mul_im, Complex.re_ofNat, Complex.im_ofNat, zero_mul, add_zero]
      constructor <;> linarith [Real.pi_pos]
    rw [Complex.log_exp him2.1 him2.2]; congr 1; ring
  change jacobiTheta ((ModularGroup.S • τ : ℍ) : ℂ) =
    (-I * (τ : ℂ)) ^ (1 / 2 : ℂ) * jacobiTheta τ at hS
  rw [h_mod, h_cpow] at hS
  unfold hardyPsi
  rw [show 2 * -z = -2 * z by ring, hS, ← mul_assoc, ← Complex.exp_add,
    show -z / 2 + z = z / 2 by ring, neg_neg, add_comm (Complex.exp (-z / 2))]

/-- Uniform exponential decay of `hardyPsi` on closed horizontal sub-strips `|z.im| ≤ α₀ < π / 4`.
-/
theorem norm_hardyPsi_le {α₀ : ℝ} (hα₀ : 0 ≤ α₀) (hα : α₀ < Real.pi / 4) :
    ∃ M > 0, ∀ z : ℂ, |z.im| ≤ α₀ → ‖hardyPsi z‖ ≤ M * Real.exp (-|z.re| / 2) := by
  have hc₀ : 0 < Real.cos (2 * α₀) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
  let c₀ : ℝ := Real.cos (2 * α₀)
  let c : ℝ := Real.pi * c₀
  have hc : 0 < c := mul_pos Real.pi_pos hc₀
  let Cθ : ℝ := 2 / (1 - Real.exp (-c))
  have hCθ : 0 < Cθ := div_pos (by norm_num) (sub_pos.mpr (Real.exp_lt_one_iff.mpr (by linarith)))
  let M : ℝ := Cθ * Real.exp (1 / (4 * c)) + 1
  refine ⟨M, by positivity, fun z hz => ?_⟩
  have h_nonneg : ∀ w : ℂ, 0 ≤ w.re → |w.im| ≤ α₀ →
      ‖hardyPsi w‖ ≤ M * Real.exp (-w.re / 2) := fun w hw_re hw_im => by
    let τ : ℂ := I * Complex.exp (2 * w)
    have him_eq : τ.im = Real.exp (2 * w.re) * Real.cos (2 * w.im) := by
      dsimp [τ]; rw [Complex.mul_im, Complex.I_re, Complex.I_im, zero_mul, one_mul, zero_add,
        Complex.exp_re]; simp
    have h_two_w : |2 * w.im| ≤ 2 * α₀ := by
      rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]; linarith
    have h_cos_le : c₀ ≤ Real.cos (2 * w.im) := by
      rw [← Real.cos_abs (2 * w.im)]
      exact Real.strictAntiOn_cos.antitoneOn ⟨abs_nonneg _, by linarith [Real.pi_pos, h_two_w, hα]⟩
        ⟨by linarith, by linarith [Real.pi_pos, hα]⟩ h_two_w
    have hτ_im_exp : c₀ * Real.exp (2 * w.re) ≤ τ.im := by
      rw [him_eq, mul_comm]; exact mul_le_mul_of_nonneg_left h_cos_le (Real.exp_pos _).le
    have hτ_pos : 0 < τ.im := lt_of_lt_of_le (mul_pos hc₀ (Real.exp_pos _)) hτ_im_exp
    have h_pi_τ_exp : c * Real.exp (2 * w.re) ≤ Real.pi * τ.im := by
      dsimp [c]; rw [mul_assoc]; exact mul_le_mul_of_nonneg_left hτ_im_exp Real.pi_pos.le
    have h_pi_τ : c ≤ Real.pi * τ.im :=
      (le_mul_of_one_le_right hc.le (Real.one_le_exp (by linarith))).trans h_pi_τ_exp
    have h_den_le : 2 / (1 - Real.exp (-Real.pi * τ.im)) ≤ Cθ := by
      have h_pos1 : 0 < 1 - Real.exp (-Real.pi * τ.im) :=
        sub_pos.mpr (Real.exp_lt_one_iff.mpr (by linarith [Real.pi_pos, hτ_pos]))
      have h_pos2 : 0 < 1 - Real.exp (-c) :=
        sub_pos.mpr (Real.exp_lt_one_iff.mpr (by linarith))
      have h1 : Real.exp (-Real.pi * τ.im) ≤ Real.exp (-c) := Real.exp_le_exp.mpr (by linarith)
      dsimp [Cθ]; exact div_le_div_of_nonneg_left (by norm_num) h_pos2 (by linarith)
    have h_theta_bound : ‖jacobiTheta τ - 1‖ ≤ Cθ * Real.exp (-c * Real.exp (2 * w.re)) :=
      (norm_jacobiTheta_sub_one_le hτ_pos).trans
        (mul_le_mul h_den_le (Real.exp_le_exp.mpr (by linarith)) (Real.exp_pos _).le hCθ.le)
    have h_norm1 : ‖Complex.exp (w / 2) * (jacobiTheta τ - 1)‖ ≤
        Cθ * Real.exp (1 / (4 * c)) * Real.exp (-w.re / 2) := by
      rw [norm_mul, Complex.norm_exp, show (w / 2).re = w.re / 2 by simp]
      have h_sq_exp : w.re ^ 2 ≤ Real.exp (2 * w.re) := by
        have h1 : w.re + 1 ≤ Real.exp w.re := Real.add_one_le_exp w.re
        have h2 : (w.re + 1) ^ 2 ≤ Real.exp w.re ^ 2 := by nlinarith
        rw [sq (Real.exp w.re), ← Real.exp_add, ← two_mul] at h2; nlinarith
      have h_quad : w.re - c * Real.exp (2 * w.re) ≤ 1 / (4 * c) := by
        have h_nn : 0 ≤ c * (w.re - 1 / (2 * c)) ^ 2 := mul_nonneg hc.le (sq_nonneg _)
        have h_comp : c * w.re ^ 2 - w.re + 1 / (4 * c) = c * (w.re - 1 / (2 * c)) ^ 2 := by
          field_simp [hc.ne']; ring
        linarith [mul_le_mul_of_nonneg_left h_sq_exp hc.le]
      calc Real.exp (w.re / 2) * ‖jacobiTheta τ - 1‖
          ≤ Real.exp (w.re / 2) * (Cθ * Real.exp (-c * Real.exp (2 * w.re))) :=
            mul_le_mul_of_nonneg_left h_theta_bound (Real.exp_pos _).le
        _ = Cθ * Real.exp (w.re / 2 + -c * Real.exp (2 * w.re)) := by
            rw [mul_left_comm, ← Real.exp_add]
        _ ≤ Cθ * Real.exp (1 / (4 * c) - w.re / 2) := by gcongr; linarith
        _ = Cθ * Real.exp (1 / (4 * c)) * Real.exp (-w.re / 2) := by
            rw [sub_eq_add_neg, show -(w.re / 2) = -w.re / 2 by ring, Real.exp_add, mul_assoc]
    have h_norm2 : ‖Complex.exp (-w / 2)‖ = Real.exp (-w.re / 2) := by
      rw [Complex.norm_exp, show (-w / 2).re = -w.re / 2 by simp]
    rw [show hardyPsi w = Complex.exp (w / 2) * (jacobiTheta τ - 1) - Complex.exp (-w / 2) by
      unfold hardyPsi; dsimp [τ]; ring]
    calc ‖Complex.exp (w / 2) * (jacobiTheta τ - 1) - Complex.exp (-w / 2)‖
        ≤ ‖Complex.exp (w / 2) * (jacobiTheta τ - 1)‖ + ‖Complex.exp (-w / 2)‖ := norm_sub_le _ _
      _ ≤ M * Real.exp (-w.re / 2) := by dsimp [M]; linarith [h_norm1, h_norm2]
  by_cases hre : 0 ≤ z.re
  · rw [abs_of_nonneg hre]; exact h_nonneg z hre hz
  · rw [← hardyPsi_neg (lt_of_le_of_lt hz hα), show |z.re| = (-z).re by
      simp [abs_of_neg (lt_of_not_ge hre)]]
    exact h_nonneg (-z) (by simp; linarith) (by simpa using hz)

/-- Lebesgue integrability of `u ↦ hardyPsi (u + I * α)` on `ℝ` for `|α| < π / 4`. -/
theorem integrable_hardyPsi_shift {α : ℝ} (hα : |α| < Real.pi / 4) :
    Integrable (fun u : ℝ => hardyPsi ((u : ℂ) + I * (α : ℂ))) := by
  obtain ⟨M, hM_pos, hM⟩ := norm_hardyPsi_le (abs_nonneg α) hα
  have hcont : Continuous (fun u : ℝ => hardyPsi ((u : ℂ) + I * (α : ℂ))) :=
    continuous_iff_continuousAt.mpr fun u => (differentiableAt_hardyPsi (by simpa using hα))
      |>.continuousAt.comp (f := fun v : ℝ => (v : ℂ) + I * (α : ℂ))
        ((Complex.continuous_ofReal.add continuous_const).continuousAt)
  have hdom : Integrable (fun u : ℝ => M * Real.exp (-|u| / 2)) := by
    have h1 : IntegrableOn (fun u : ℝ => M * Real.exp (-(1 / 2) * u)) (Ioi 0) :=
      (integrableOn_exp_mul_Ioi (by norm_num : -(1 / 2 : ℝ) < 0) 0).const_mul M
    have h2 : IntegrableOn (fun u : ℝ => M * Real.exp (1 / 2 * u)) (Iic 0) :=
      (integrableOn_exp_mul_Iic (by norm_num : (0 : ℝ) < 1 / 2) 0).const_mul M
    rw [← integrableOn_univ, ← Iic_union_Ioi (a := (0 : ℝ)), integrableOn_union]
    exact ⟨h2.congr_fun (fun u hu => by rw [abs_of_nonpos (mem_Iic.mp hu)]; ring_nf)
      measurableSet_Iic, h1.congr_fun (fun u hu => by rw [abs_of_pos (mem_Ioi.mp hu)]; ring_nf)
      measurableSet_Ioi⟩
  refine hdom.mono hcont.aestronglyMeasurable (ae_of_all _ fun u => ?_)
  calc ‖hardyPsi ((u : ℂ) + I * (α : ℂ))‖
      ≤ M * Real.exp (-|((u : ℂ) + I * (α : ℂ)).re| / 2) := hM _ (by simp)
    _ = ‖M * Real.exp (-|u| / 2)‖ := by
        simp [Real.norm_of_nonneg (mul_nonneg hM_pos.le (Real.exp_pos _).le)]

/-- Jacobi theta parity relation: `jacobiTheta (-1 + η) = 2 * jacobiTheta (4 * η) - jacobiTheta η`.
-/
theorem jacobiTheta_neg_one_add {η : ℂ} (hη : 0 < η.im) :
    jacobiTheta (-1 + η) = 2 * jacobiTheta (4 * η) - jacobiTheta η := by
  have hη1 : 0 < (-1 + η).im := by simpa using hη
  have hη4 : 0 < (4 * η).im := by simp [hη]
  rw [jacobiTheta_eq_tsum_nat hη1, jacobiTheta_eq_tsum_nat hη4, jacobiTheta_eq_tsum_nat hη]
  let f : ℕ → ℂ := fun n => Complex.exp (Real.pi * I * ((n : ℂ) + 1) ^ 2 * (-1 + η))
  let g : ℕ → ℂ := fun n => Complex.exp (Real.pi * I * ((n : ℂ) + 1) ^ 2 * η)
  let h4 : ℕ → ℂ := fun m => Complex.exp (Real.pi * I * ((m : ℂ) + 1) ^ 2 * (4 * η))
  have hf := (hasSum_nat_jacobiTheta hη1).summable
  have hg := (hasSum_nat_jacobiTheta hη).summable
  have hh4 := (hasSum_nat_jacobiTheta hη4).summable
  have h_even_odd : ∀ m : ℕ, f (2 * m) + g (2 * m) = 0 ∧
      f (2 * m + 1) + g (2 * m + 1) = 2 * h4 m := fun m => by
    have h_mul : ∀ n, f n = Complex.exp (Real.pi * I * ((n : ℂ) + 1) ^ 2 * (-1)) * g n :=
      fun n => by dsimp [f, g]; rw [← Complex.exp_add]; congr 1; ring
    have h_even : Complex.exp (Real.pi * I * (((2 * m : ℕ) : ℂ) + 1) ^ 2 * (-1)) = -1 := by
      rw [show Real.pi * I * (((2 * m : ℕ) : ℂ) + 1) ^ 2 * (-1) =
          (((m : ℤ) ^ 2 + m : ℤ) * (-2 : ℤ) : ℤ) * (2 * Real.pi * I) - Real.pi * I by
          push_cast; ring, sub_eq_add_neg, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I,
        one_mul, Complex.exp_neg, Complex.exp_pi_mul_I]; norm_num
    have h_odd : Complex.exp (Real.pi * I * (((2 * m + 1 : ℕ) : ℂ) + 1) ^ 2 * (-1)) = 1 := by
      rw [show Real.pi * I * (((2 * m + 1 : ℕ) : ℂ) + 1) ^ 2 * (-1) =
          (-(((m : ℤ) + 1) ^ 2 * 2 : ℤ) : ℤ) * (2 * Real.pi * I) by push_cast; ring,
        Complex.exp_int_mul_two_pi_mul_I]
    constructor
    · rw [h_mul (2 * m), h_even]; ring
    · have hg_odd : g (2 * m + 1) = h4 m := by dsimp [g, h4]; congr 1; push_cast; ring
      rw [h_mul (2 * m + 1), h_odd, one_mul, hg_odd]; ring
  have h_sum_2N : ∀ N : ℕ, (∑ n ∈ Finset.range (2 * N), (f n + g n)) =
      2 * ∑ m ∈ Finset.range N, h4 m := fun N => by
    induction N with
    | zero => simp
    | succ N ih =>
      rw [show 2 * (N + 1) = (2 * N + 1) + 1 by ring, Finset.sum_range_succ,
        Finset.sum_range_succ, ih, Finset.sum_range_succ, (h_even_odd N).1, (h_even_odd N).2]
      ring
  have h_ten_L := (hf.add hg).hasSum.tendsto_sum_nat.comp
    (Filter.tendsto_atTop_atTop.mpr fun b => ⟨b, fun n hn => by omega⟩ :
      Tendsto (fun N : ℕ => 2 * N) atTop atTop)
  dsimp only [Function.comp_def] at h_ten_L
  rw [show (fun N : ℕ => ∑ n ∈ Finset.range (2 * N), (f n + g n)) =
    fun N : ℕ => 2 * ∑ m ∈ Finset.range N, h4 m from funext h_sum_2N] at h_ten_L
  have h_tsum := tendsto_nhds_unique h_ten_L (tendsto_const_nhds.mul hh4.hasSum.tendsto_sum_nat)
  rw [hf.tsum_add hg] at h_tsum
  have h_sub : ∑' n : ℕ, f n = 2 * ∑' m : ℕ, h4 m - ∑' n : ℕ, g n := eq_sub_of_add_eq h_tsum
  change 1 + 2 * ∑' n : ℕ, f n = 2 * (1 + 2 * ∑' m : ℕ, h4 m) - (1 + 2 * ∑' n : ℕ, g n)
  rw [h_sub]; ring
