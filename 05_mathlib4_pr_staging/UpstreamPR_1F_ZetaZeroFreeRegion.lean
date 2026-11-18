/-
Copyright (c) 2026 Qamar Munawer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qamar Munawer
-/
module

public import Mathlib.Analysis.Complex.CauchyIntegral
public import RiemannBlueprint.UpstreamPRs.UpstreamPR_1B_ZetaPoleAndRepulsion
public import RiemannBlueprint.UpstreamPRs.UpstreamPR_1E_ZetaLogStripBound

/-!
# De la Vallée Poussin's Unconditional Zero-Free Region for the Riemann Zeta Function

This file combines the pole bound (`exists_pole_bound_one_add`), the logarithmic strip growth
bound (`norm_riemannZeta_le_of_log_strip`), Cauchy's derivative estimate for horizontal Lipschitz
control (`riemannZeta_horizontal_lipschitz_of_zero`), and the 3-4-1 zero repulsion contradiction to
prove de la Vallée Poussin's (1899) unconditional zero-free region:
`∃ c > 0, ∀ s : ℂ, 2 ≤ |s.im| → 1 - c / Real.log (|s.im| + 2) ^ 9 < s.re → riemannZeta s ≠ 0`.
-/

@[expose] public section

open Complex Set

private lemma log_add_two_le_two_log {a b : ℝ} (ha : 2 ≤ a) (hb0 : 0 ≤ b)
    (hb : b + 2 ≤ 2 * (a + 2)) :
    Real.log (b + 2) ≤ 2 * Real.log (a + 2) := by
  have h3 : Real.log (2 * (a + 2)) = Real.log 2 + Real.log (a + 2) :=
    Real.log_mul (by norm_num) (by linarith)
  have h4 : Real.log 2 ≤ Real.log (a + 2) := Real.log_le_log (by norm_num) (by linarith)
  exact (Real.log_le_log (by linarith) hb).trans (by linarith)

/-- Unconditional horizontal Lipschitz bound for `riemannZeta` from Cauchy's integral estimate
and the strip logarithmic growth bound, when `riemannZeta (1 - δ + I * y) = 0` with
`0 < δ ≤ 1 / (8 * log (|y| + 2))` and `2 ≤ |y|`. -/
theorem riemannZeta_horizontal_lipschitz_of_zero {δ y : ℝ} (hy : 2 ≤ |y|)
    (hδ_pos : 0 < δ) (hδ_le : δ ≤ 1 / (8 * Real.log (|y| + 2)))
    (hz : riemannZeta (1 - (δ : ℂ) + I * (y : ℂ)) = 0) :
    ‖riemannZeta (1 + (3 * δ : ℂ) + I * (y : ℂ))‖ ≤
      (16 * (10 * Real.exp 1 + 3)) * Real.log (|y| + 2) ^ 2 * (4 * δ) := by
  have hlog_gt_one : 1 < Real.log (|y| + 2) := by
    rw [← Real.log_exp 1]
    exact Real.log_lt_log (Real.exp_pos 1) (lt_of_lt_of_le Real.exp_one_lt_three (by linarith))
  have hlog_pos : 0 < Real.log (|y| + 2) := by linarith
  let R : ℝ := 1 / (8 * Real.log (|y| + 2))
  have hR_pos : 0 < R := by dsimp [R]; positivity
  have hR_lt : R < 1 / 8 := by
    dsimp [R]; rw [div_lt_div_iff₀ (by positivity) (by norm_num)]; linarith
  let C_strip : ℝ := 10 * Real.exp 1 + 3
  let C_lip : ℝ := 16 * C_strip
  let z₁ : ℂ := 1 - (δ : ℂ) + I * (y : ℂ)
  let z₂ : ℂ := 1 + ((3 * δ : ℝ) : ℂ) + I * (y : ℂ)
  let S_seg : Set ℂ := {z : ℂ | 1 - δ ≤ z.re ∧ z.re ≤ 1 + 3 * δ ∧ z.im = y}
  have hS_conv : Convex ℝ S_seg := by
    intro a ha b hb u v hu hv huv
    simp only [S_seg, Set.mem_ofPred_eq, Complex.add_re, Complex.real_smul, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, Complex.add_im, Complex.mul_im] at ha hb ⊢
    refine ⟨?_, ?_, ?_⟩
    · have h1 : u * (1 - δ) + v * (1 - δ) = 1 - δ := by rw [← add_mul, huv, one_mul]
      nlinarith [ha.1, hb.1]
    · have h2 : u * (1 + 3 * δ) + v * (1 + 3 * δ) = 1 + 3 * δ := by rw [← add_mul, huv, one_mul]
      nlinarith [ha.2.1, hb.2.1]
    · simp only [ha.2.2, hb.2.2, zero_mul, add_zero]
      rw [← add_mul, huv, one_mul]
  have hw_log_bound : ∀ z ∈ S_seg, ∀ w ∈ Metric.closedBall z R,
      (3 / 2 ≤ |w.im| ∧ 1 - 1 / (2 * Real.log (|w.im| + 2)) ≤ w.re ∧ w.re ≤ 2) ∧
        Real.log (|w.im| + 2) ≤ 2 * Real.log (|y| + 2) := by
    intro z hzS w hw
    have hw_dist : ‖w - z‖ ≤ R := by rwa [Metric.mem_closedBall, dist_eq_norm] at hw
    have hw_re_diff : |w.re - z.re| ≤ R :=
      (by simp : |w.re - z.re| = |(w - z).re|) ▸ (Complex.abs_re_le_norm (w - z)).trans hw_dist
    have hw_im_eq : |w.im - y| ≤ R := by
      have h1 : |w.im - z.im| ≤ R :=
        (by simp : |w.im - z.im| = |(w - z).im|) ▸ (Complex.abs_im_le_norm (w - z)).trans hw_dist
      rwa [hzS.2.2] at h1
    have hw_im_lo : 3 / 2 ≤ |w.im| := by
      have h1 : |y| - |w.im| ≤ |w.im - y| := by
        simpa [abs_sub_comm] using abs_sub_abs_le_abs_sub y w.im
      linarith
    have hw_im_hi : |w.im| ≤ |y| + 1 / 4 := by
      have h1 : |w.im| - |y| ≤ |w.im - y| := abs_sub_abs_le_abs_sub w.im y
      linarith
    have hlog_w_le := log_add_two_le_two_log hy (abs_nonneg w.im) (by linarith)
    have hlog_w_pos : 0 < Real.log (|w.im| + 2) := Real.log_pos (by linarith)
    have hre_lo : 1 - 1 / (2 * Real.log (|w.im| + 2)) ≤ w.re := by
      have hw_re_ge : z.re - R ≤ w.re := by linarith [(abs_sub_le_iff.mp hw_re_diff).2]
      have h_inv_le : 1 / (4 * Real.log (|y| + 2)) ≤ 1 / (2 * Real.log (|w.im| + 2)) := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]; linarith
      have hR_sum : 1 / (8 * Real.log (|y| + 2)) + R = 1 / (4 * Real.log (|y| + 2)) := by
        dsimp [R]; ring
      linarith [hzS.1]
    have hre_hi : w.re ≤ 2 := by
      have hw_re_le : w.re ≤ z.re + R := by linarith [(abs_sub_le_iff.mp hw_re_diff).1]
      have hδ_small : δ ≤ 1 / 8 := hδ_le.trans (by
        rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith)
      linarith [hzS.2.1]
    exact ⟨⟨hw_im_lo, hre_lo, hre_hi⟩, hlog_w_le⟩
  have hz_diff : ∀ z ∈ S_seg, DifferentiableAt ℂ riemannZeta z := fun z hzS => by
    apply differentiableAt_riemannZeta
    intro h1; have him := hzS.2.2; rw [h1, Complex.one_im] at him
    rw [← him, abs_zero] at hy; linarith
  have hz_deriv_bound : ∀ z ∈ S_seg, ‖deriv riemannZeta z‖ ≤ C_lip * Real.log (|y| + 2) ^ 2 := by
    intro z hzS
    have h_diff_cl : DiffContOnCl ℂ riemannZeta (Metric.ball z R) := by
      refine DifferentiableOn.diffContOnCl fun w hw => ?_
      rw [closure_ball z hR_pos.ne'] at hw
      have hw_im := (hw_log_bound z hzS w hw).1.1
      refine (differentiableAt_riemannZeta ?_).differentiableWithinAt
      intro h1; rw [h1] at hw_im; simp at hw_im; linarith
    have h_sphere : ∀ w ∈ Metric.sphere z R,
        ‖riemannZeta w‖ ≤ (2 * C_strip) * Real.log (|y| + 2) := by
      intro w hw
      obtain ⟨⟨hw_im, hw_lo, hw_hi⟩, hlog_w_le⟩ :=
        hw_log_bound z hzS w (Metric.sphere_subset_closedBall hw)
      have h_bound := norm_riemannZeta_le_of_log_strip hw_im hw_lo hw_hi
      have h_mul := mul_le_mul_of_nonneg_left hlog_w_le
        (show 0 ≤ C_strip by dsimp [C_strip]; positivity)
      dsimp [C_strip] at h_bound h_mul ⊢; linarith
    have h_cauchy := norm_deriv_le_of_forall_mem_sphere_norm_le hR_pos h_diff_cl h_sphere
    have h_eq_rhs : (2 * C_strip) * Real.log (|y| + 2) / R = C_lip * Real.log (|y| + 2) ^ 2 := by
      dsimp [R, C_lip]; field_simp [hlog_pos.ne']; ring
    rwa [h_eq_rhs] at h_cauchy
  have h_mvt := hS_conv.norm_image_sub_le_of_norm_deriv_le hz_diff hz_deriv_bound
    (show z₁ ∈ S_seg by simp [S_seg, z₁]; linarith)
    (show z₂ ∈ S_seg by simp [S_seg, z₂]; linarith)
  have h_diff_eq : z₂ - z₁ = ((4 * δ : ℝ) : ℂ) := by dsimp [z₁, z₂]; push_cast; ring
  rw [hz, sub_zero, h_diff_eq, norm_real, Real.norm_of_nonneg (by positivity)] at h_mvt
  rwa [show z₂ = 1 + (3 * δ : ℂ) + I * (y : ℂ) by dsimp [z₂]; push_cast; ring] at h_mvt

/-- **De la Vallée Poussin's (1899) Unconditional Zero-Free Region Theorem**:
There exists an absolute constant `c > 0` such that `riemannZeta s ≠ 0` for all `s : ℂ` with
`2 ≤ |s.im|` and `1 - c / log (|s.im| + 2) ^ 9 < s.re`. -/
theorem deLaValleePoussin_zero_free_region_unconditional :
    ∃ c > 0, ∀ s : ℂ, 2 ≤ |s.im| →
      1 - c / Real.log (|s.im| + 2) ^ 9 < s.re → riemannZeta s ≠ 0 := by
  obtain ⟨C_pole, hC_pole, h_pole_all⟩ := exists_pole_bound_one_add
  let C_strip : ℝ := 10 * Real.exp 1 + 3
  let C_lip : ℝ := 16 * C_strip
  let C_growth : ℝ := 2 * C_strip
  have hC_strip : 0 < C_strip := by dsimp [C_strip]; positivity
  have hC_lip : 0 < C_lip := by dsimp [C_lip]; positivity
  have hC_growth : 0 < C_growth := by dsimp [C_growth]; positivity
  let c₀ : ℝ := 27 / (256 * C_pole ^ 3 * C_lip ^ 4 * C_growth)
  have hc₀ : 0 < c₀ := by dsimp [c₀]; positivity
  let c : ℝ := min (1 / 8) c₀
  refine ⟨c, lt_min (by norm_num) hc₀, fun s ht h_reg h_zero => ?_⟩
  by_cases h_ge : 1 ≤ s.re
  · exact riemannZeta_ne_zero_of_one_le_re h_ge h_zero
  · let δ : ℝ := 1 - s.re
    have hδ_pos : 0 < δ := sub_pos.mpr (lt_of_not_ge h_ge)
    have hlog_gt_one : 1 < Real.log (|s.im| + 2) := by
      rw [← Real.log_exp 1]
      exact Real.log_lt_log (Real.exp_pos 1) (lt_of_lt_of_le Real.exp_one_lt_three (by linarith))
    have hlog_pos : 0 < Real.log (|s.im| + 2) := by linarith
    have h_pow_ge : Real.log (|s.im| + 2) ≤ Real.log (|s.im| + 2) ^ 9 := by
      simpa using pow_le_pow_right₀ hlog_gt_one.le (by norm_num : 1 ≤ 9)
    have hδ_lt_c : δ < c / Real.log (|s.im| + 2) ^ 9 := by dsimp [δ]; linarith
    have hδ_lt_c₀ : δ < c₀ / Real.log (|s.im| + 2) ^ 9 :=
      hδ_lt_c.trans_le (div_le_div_of_nonneg_right (min_le_right _ _) (by positivity))
    have hδ_le_log : δ ≤ 1 / (8 * Real.log (|s.im| + 2)) := by
      calc δ ≤ c / Real.log (|s.im| + 2) ^ 9 := hδ_lt_c.le
        _ ≤ (1 / 8) / Real.log (|s.im| + 2) ^ 9 :=
            div_le_div_of_nonneg_right (min_le_left _ _) (by positivity)
        _ ≤ (1 / 8) / Real.log (|s.im| + 2) :=
            div_le_div_of_nonneg_left (by norm_num) hlog_pos h_pow_ge
        _ = 1 / (8 * Real.log (|s.im| + 2)) := by ring
    have h3δ_le_one : 3 * δ ≤ 1 := by
      have h_le18 : δ ≤ 1 / 8 := hδ_le_log.trans (by
        rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith)
      linarith
    have h_pole : ‖riemannZeta (1 + (3 * δ : ℂ))‖ ≤ C_pole / (3 * δ) := by
      have h_raw := h_pole_all (3 * δ) (by linarith) h3δ_le_one
      rwa [← show (1 : ℂ) + ((3 * δ : ℝ) : ℂ) = 1 + (3 * δ : ℂ) by push_cast; rfl]
    have h_lip : ‖riemannZeta (1 + (3 * δ : ℂ) + I * s.im)‖ ≤
        C_lip * Real.log (|s.im| + 2) ^ 2 * (4 * δ) := by
      have hs_eq : (1 : ℂ) - (δ : ℂ) + I * (s.im : ℂ) = s := by apply Complex.ext <;> simp [δ]
      exact riemannZeta_horizontal_lipschitz_of_zero ht hδ_pos hδ_le_log (by rwa [hs_eq])
    have h_growth : ‖riemannZeta (1 + (3 * δ : ℂ) + 2 * I * s.im)‖ ≤
        C_growth * Real.log (|s.im| + 2) := by
      let w : ℂ := 1 + (3 * δ : ℂ) + 2 * I * s.im
      have hw_im_eq : |w.im| = 2 * |s.im| := by
        rw [show w.im = 2 * s.im by simp [w], abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      have hw_im : 3 / 2 ≤ |w.im| := by linarith
      have hw_re_lo : 1 - 1 / (2 * Real.log (|w.im| + 2)) ≤ w.re := by
        have hre : w.re = 1 + 3 * δ := by simp [w]
        have hlogw_pos : 0 < Real.log (|w.im| + 2) := Real.log_pos (by linarith)
        rw [hre]; linarith [show 0 ≤ 1 / (2 * Real.log (|w.im| + 2)) by positivity]
      have hw_re_hi : w.re ≤ 2 := by
        have hre : w.re = 1 + 3 * δ := by simp [w]
        linarith
      have h_raw := norm_riemannZeta_le_of_log_strip hw_im hw_re_lo hw_re_hi
      have hlog_2y := log_add_two_le_two_log ht (abs_nonneg w.im) (by linarith)
      have h_mul := mul_le_mul_of_nonneg_left hlog_2y
        (show 0 ≤ C_strip by dsimp [C_strip]; positivity)
      dsimp [C_growth, C_strip] at h_raw h_mul ⊢
      linarith
    have hδ_lt_full : δ < (27 : ℝ) /
        (256 * C_pole ^ 3 * C_lip ^ 4 * C_growth * Real.log (|s.im| + 2) ^ 9) := by
      have heq : c₀ / Real.log (|s.im| + 2) ^ 9 = (27 : ℝ) /
          (256 * C_pole ^ 3 * C_lip ^ 4 * C_growth * Real.log (|s.im| + 2) ^ 9) := by
        dsimp [c₀]; field_simp
      rwa [← heq]
    exact deLaValleePoussin_contradiction hδ_pos ht hC_pole hC_lip hC_growth
      h_pole h_lip h_growth hδ_lt_full
