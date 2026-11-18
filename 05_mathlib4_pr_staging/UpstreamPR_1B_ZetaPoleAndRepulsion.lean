/-
Copyright (c) 2026 Qamar Munawer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qamar Munawer
-/
module

public import Mathlib.NumberTheory.LSeries.Nonvanishing
public import Mathlib.NumberTheory.LSeries.RiemannZeta
public import RiemannBlueprint.UpstreamPRs.UpstreamPR_1A_CriticalLineZeros

/-!
# Riemann Zeta Pole Bound and De la Vallée Poussin Repulsion

This file builds the quantitative pole bound near `s = 1` and the algebraic zero-repulsion
mechanism of de la Vallée Poussin (1899) on top of `norm_riemannZeta_product_ge_one`:
1. `riemannZeta_norm_cubed_fourth_mul_ge_one`: separated norm form of the 3-4-1 product bound.
2. `exists_pole_bound_one_add`: unconditional `O(x⁻¹)` upper bound on `(1, 2]` via compactness
   of the entire regular part `riemannZeta₀`.
3. `valleePoussin_cubic_opt_identity`: `(3δ + δ)⁴ / (3δ)³ = (256 / 27) δ`.
4. `deLaValleePoussin_zero_free_region`: parametric zero-free region assuming local pole,
   Lipschitz, and vertical strip growth bounds.
-/

@[expose] public section

open Complex Set

/-- Separated-norm form of the 3-4-1 product inequality:
`1 ≤ ‖ζ(1 + x)‖ ^ 3 * ‖ζ(1 + x + I * y)‖ ^ 4 * ‖ζ(1 + x + 2 * I * y)‖` for `0 < x`. -/
theorem riemannZeta_norm_cubed_fourth_mul_ge_one {x : ℝ} (hx : 0 < x) (y : ℝ) :
    1 ≤ ‖riemannZeta (1 + x)‖ ^ 3 * ‖riemannZeta (1 + x + I * y)‖ ^ 4 *
      ‖riemannZeta (1 + x + 2 * I * y)‖ := by
  simpa only [norm_mul, norm_pow] using norm_riemannZeta_product_ge_one hx y

/-- Laurent decomposition near `s = 1`: for real `x ≠ 0`, `ζ(1 + x) = x⁻¹ + ζ₀(1 + x)` where
`riemannZeta₀` is the entire regular part. -/
theorem riemannZeta_one_add_eq {x : ℝ} (hx : x ≠ 0) :
    riemannZeta (1 + (x : ℂ)) = (x : ℂ)⁻¹ + riemannZeta₀ (1 + (x : ℂ)) := by
  have hne : 1 + (x : ℂ) ≠ 1 := by
    intro h
    exact hx (Complex.ofReal_eq_zero.mp (by linear_combination h))
  simpa [add_sub_cancel_left] using riemannZeta_eq_inv_sub_add hne

/-- Quantitative pole bound near `s = 1`: for `0 < x ≤ 1`, if `‖riemannZeta₀ (1 + x)‖ ≤ M`
with `0 ≤ M`, then `‖ζ(1 + x)‖ ≤ (1 + M) / x`. -/
theorem norm_riemannZeta_one_add_le {x M : ℝ} (hx_pos : 0 < x) (hx_le : x ≤ 1)
    (hM_nonneg : 0 ≤ M) (hM : ‖riemannZeta₀ (1 + (x : ℂ))‖ ≤ M) :
    ‖riemannZeta (1 + (x : ℂ))‖ ≤ (1 + M) / x := by
  rw [riemannZeta_one_add_eq hx_pos.ne']
  have h_inv : ‖(x : ℂ)⁻¹‖ = 1 / x := by
    rw [norm_inv, Complex.norm_real, Real.norm_of_nonneg hx_pos.le, one_div]
  have h_tri : ‖(x : ℂ)⁻¹ + riemannZeta₀ (1 + (x : ℂ))‖ ≤ 1 / x + M := by
    calc ‖(x : ℂ)⁻¹ + riemannZeta₀ (1 + (x : ℂ))‖
        ≤ ‖(x : ℂ)⁻¹‖ + ‖riemannZeta₀ (1 + (x : ℂ))‖ := norm_add_le _ _
      _ ≤ 1 / x + M := by linarith
  have h_le : 1 / x + M ≤ (1 + M) / x := by
    rw [show 1 / x + M = (1 + M * x) / x by field_simp]
    exact div_le_div_of_nonneg_right (by nlinarith) hx_pos.le
  exact h_tri.trans h_le

/-- Unconditional constructive pole bound near `s = 1`: there exists `C_pole > 0` such that
`‖ζ(1 + x)‖ ≤ C_pole / x` for all `0 < x ≤ 1`. -/
theorem exists_pole_bound_one_add :
    ∃ C_pole > 0, ∀ x : ℝ, 0 < x → x ≤ 1 →
      ‖riemannZeta (1 + (x : ℂ))‖ ≤ C_pole / x := by
  have hcont : ContinuousOn (fun x : ℝ => ‖riemannZeta₀ (1 + (x : ℂ))‖) (Icc (0 : ℝ) 1) :=
    ((differentiable_riemannZeta₀.continuous.comp
      (continuous_const.add Complex.continuous_ofReal)).norm).continuousOn
  obtain ⟨x_max, _, hx_max⟩ :=
    isCompact_Icc.exists_isMaxOn ⟨(0 : ℝ), left_mem_Icc.mpr zero_le_one⟩ hcont
  let M : ℝ := ‖riemannZeta₀ (1 + (x_max : ℂ))‖
  refine ⟨1 + M, by positivity, fun x hx_pos hx_le =>
    norm_riemannZeta_one_add_le hx_pos hx_le (norm_nonneg _) (hx_max ⟨hx_pos.le, hx_le⟩)⟩

/-- De la Vallée Poussin's cubic optimization identity:
`(3 * δ + δ) ^ 4 / (3 * δ) ^ 3 = (256 / 27) * δ`. -/
theorem valleePoussin_cubic_opt_identity (δ : ℝ) :
    (3 * δ + δ) ^ 4 / (3 * δ) ^ 3 = (256 / 27 : ℝ) * δ := by
  by_cases hδ : δ = 0
  · simp [hδ]
  · field_simp; ring

private lemma valleePoussin_product_eq {δ y C_pole C_lip C_growth : ℝ}
    (hδ_pos : 0 < δ) (hy : 2 ≤ |y|) :
    (C_pole / (3 * δ)) ^ 3 * (C_lip * Real.log (|y| + 2) ^ 2 * (4 * δ)) ^ 4 *
        (C_growth * Real.log (|y| + 2)) =
      δ * ((256 / 27 : ℝ) * C_pole ^ 3 * C_lip ^ 4 * C_growth * Real.log (|y| + 2) ^ 9) := by
  have hlog_ne : Real.log (|y| + 2) ≠ 0 := (Real.log_pos (by linarith)).ne'
  have hδ_ne : δ ≠ 0 := hδ_pos.ne'
  field_simp
  ring

/-- Analytical zero repulsion theorem (de la Vallée Poussin 1899): any `δ > 0` satisfying the
combined 3-4-1 upper bound `1 ≤ (C_pole / (3 * δ)) ^ 3 * ...` obeys the lower bound
`27 / (256 * C_pole ^ 3 * C_lip ^ 4 * C_growth * log (|y| + 2) ^ 9) ≤ δ`. -/
theorem deLaValleePoussin_zero_repulsion {δ y C_pole C_lip C_growth : ℝ}
    (hδ_pos : 0 < δ) (hy : 2 ≤ |y|)
    (hC_pole : 0 < C_pole) (hC_lip : 0 < C_lip) (hC_growth : 0 < C_growth)
    (h_prod : 1 ≤ (C_pole / (3 * δ)) ^ 3 * (C_lip * Real.log (|y| + 2) ^ 2 * (4 * δ)) ^ 4 *
      (C_growth * Real.log (|y| + 2))) :
    (27 : ℝ) / (256 * C_pole ^ 3 * C_lip ^ 4 * C_growth * Real.log (|y| + 2) ^ 9) ≤ δ := by
  have hlog_pos : 0 < Real.log (|y| + 2) := Real.log_pos (by linarith)
  have hcoeff_pos :
      0 < (256 / 27 : ℝ) * C_pole ^ 3 * C_lip ^ 4 * C_growth * Real.log (|y| + 2) ^ 9 := by
    positivity
  rw [valleePoussin_product_eq hδ_pos hy] at h_prod
  have hdiv : 1 / ((256 / 27 : ℝ) * C_pole ^ 3 * C_lip ^ 4 * C_growth * Real.log (|y| + 2) ^ 9) ≤
      δ := (div_le_iff₀ hcoeff_pos).mpr h_prod
  rwa [show (1 : ℝ) / ((256 / 27 : ℝ) * C_pole ^ 3 * C_lip ^ 4 * C_growth *
      Real.log (|y| + 2) ^ 9) =
    (27 : ℝ) / (256 * C_pole ^ 3 * C_lip ^ 4 * C_growth * Real.log (|y| + 2) ^ 9) by
      field_simp] at hdiv

/-- If `δ` lies strictly below the repulsion radius, the combined 3-4-1 upper bound product is
strictly less than `1`. -/
theorem deLaValleePoussin_product_lt_one_of_lt_repulsion {δ y C_pole C_lip C_growth : ℝ}
    (hδ_pos : 0 < δ) (hy : 2 ≤ |y|)
    (hC_pole : 0 < C_pole) (hC_lip : 0 < C_lip) (hC_growth : 0 < C_growth)
    (hδ_lt :
      δ < (27 : ℝ) / (256 * C_pole ^ 3 * C_lip ^ 4 * C_growth * Real.log (|y| + 2) ^ 9)) :
    (C_pole / (3 * δ)) ^ 3 * (C_lip * Real.log (|y| + 2) ^ 2 * (4 * δ)) ^ 4 *
      (C_growth * Real.log (|y| + 2)) < 1 := by
  have hlog_pos : 0 < Real.log (|y| + 2) := Real.log_pos (by linarith)
  have hcoeff_pos :
      0 < (256 / 27 : ℝ) * C_pole ^ 3 * C_lip ^ 4 * C_growth * Real.log (|y| + 2) ^ 9 := by
    positivity
  rw [valleePoussin_product_eq hδ_pos hy]
  rw [show (27 : ℝ) / (256 * C_pole ^ 3 * C_lip ^ 4 * C_growth * Real.log (|y| + 2) ^ 9) =
      1 / ((256 / 27 : ℝ) * C_pole ^ 3 * C_lip ^ 4 * C_growth * Real.log (|y| + 2) ^ 9) by
    field_simp] at hδ_lt
  exact (lt_div_iff₀ hcoeff_pos).mp hδ_lt

/-- Contradiction step of de la Vallée Poussin's argument: no `δ > 0` below the repulsion radius can
simultaneously satisfy the local pole, Lipschitz, and strip growth estimates. -/
theorem deLaValleePoussin_contradiction {δ y C_pole C_lip C_growth : ℝ}
    (hδ_pos : 0 < δ) (hy : 2 ≤ |y|)
    (hC_pole : 0 < C_pole) (hC_lip : 0 < C_lip) (hC_growth : 0 < C_growth)
    (h_pole : ‖riemannZeta (1 + (3 * δ : ℂ))‖ ≤ C_pole / (3 * δ))
    (h_lip : ‖riemannZeta (1 + (3 * δ : ℂ) + I * y)‖ ≤ C_lip * Real.log (|y| + 2) ^ 2 * (4 * δ))
    (h_growth : ‖riemannZeta (1 + (3 * δ : ℂ) + 2 * I * y)‖ ≤ C_growth * Real.log (|y| + 2))
    (hδ_lt :
      δ < (27 : ℝ) / (256 * C_pole ^ 3 * C_lip ^ 4 * C_growth * Real.log (|y| + 2) ^ 9)) :
    False := by
  have h_ge := riemannZeta_norm_cubed_fourth_mul_ge_one (show 0 < 3 * δ by positivity) y
  have hcast : (1 : ℂ) + (↑(3 * δ) : ℂ) = 1 + (3 * δ : ℂ) := by push_cast; rfl
  rw [hcast] at h_ge
  have h_lt_one := deLaValleePoussin_product_lt_one_of_lt_repulsion
    hδ_pos hy hC_pole hC_lip hC_growth hδ_lt
  have h_prod_le : ‖riemannZeta (1 + (3 * δ : ℂ))‖ ^ 3 *
      ‖riemannZeta (1 + (3 * δ : ℂ) + I * y)‖ ^ 4 *
      ‖riemannZeta (1 + (3 * δ : ℂ) + 2 * I * y)‖ ≤
      (C_pole / (3 * δ)) ^ 3 * (C_lip * Real.log (|y| + 2) ^ 2 * (4 * δ)) ^ 4 *
      (C_growth * Real.log (|y| + 2)) := by
    gcongr
  exact lt_irrefl _ (h_ge.trans_lt (h_prod_le.trans_lt h_lt_one))

/-- Parametric zero-free region for `riemannZeta`: for `2 ≤ |s.im|` and
`1 - 27 / (256 * C_pole ^ 3 * C_lip ^ 4 * C_growth * log (|s.im| + 2) ^ 9) < s.re`,
any point satisfying the local pole, horizontal Lipschitz, and vertical strip growth estimates
cannot be a zero of `riemannZeta`. -/
theorem deLaValleePoussin_zero_free_region {s : ℂ} {C_pole C_lip C_growth : ℝ}
    (ht : 2 ≤ |s.im|)
    (hC_pole : 0 < C_pole) (hC_lip : 0 < C_lip) (hC_growth : 0 < C_growth)
    (h_reg : 1 - (27 : ℝ) /
      (256 * C_pole ^ 3 * C_lip ^ 4 * C_growth * Real.log (|s.im| + 2) ^ 9) < s.re)
    (h_pole : ‖riemannZeta (1 + (3 * (1 - s.re : ℝ) : ℂ))‖ ≤ C_pole / (3 * (1 - s.re)))
    (h_lip : ‖riemannZeta (1 + (3 * (1 - s.re : ℝ) : ℂ) + I * s.im)‖ ≤
      C_lip * Real.log (|s.im| + 2) ^ 2 * (4 * (1 - s.re)))
    (h_growth : ‖riemannZeta (1 + (3 * (1 - s.re : ℝ) : ℂ) + 2 * I * s.im)‖ ≤
      C_growth * Real.log (|s.im| + 2)) :
    riemannZeta s ≠ 0 := by
  intro h_zero
  by_cases h_ge : 1 ≤ s.re
  · exact riemannZeta_ne_zero_of_one_le_re h_ge h_zero
  · have hδ_pos : 0 < 1 - s.re := sub_pos.mpr (lt_of_not_ge h_ge)
    have hδ_lt : 1 - s.re < (27 : ℝ) /
        (256 * C_pole ^ 3 * C_lip ^ 4 * C_growth * Real.log (|s.im| + 2) ^ 9) := by linarith
    exact deLaValleePoussin_contradiction
      hδ_pos ht hC_pole hC_lip hC_growth h_pole h_lip h_growth hδ_lt
