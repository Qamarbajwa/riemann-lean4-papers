/-
Copyright (c) 2026 Qamar Munawer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qamar Munawer
-/
module

public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-!
# Mellin Weight Kernel Energy Identity and Weighted `L²(0, 1)` Bound

This module formalizes the unconditional `L²(0, 1)` Mellin weight kernel
`mellinWeight σ x = x ^ (σ - 1)` for abscissae `σ > 1 / 2`:

* `mellinWeight`: real Mellin power kernel `x ↦ x ^ (σ - 1)`.
* `integrableOn_sq_mellinWeight`: integrability of `(mellinWeight σ x) ^ 2` on `Ioc 0 1` for
  `1 / 2 < σ`.
* `integral_Ioc_sq_mellinWeight`: exact identity
  `∫ x in Ioc 0 1, x ^ (2 * σ - 2) = 1 / (2 * σ - 1)` for `1 / 2 < σ`.
* `sq_mellin_weighted_le_div_two_mul_sub_one`: pointwise weighted Cauchy–Schwarz inequality
  `2 * (f x * x ^ (σ - 1)) ≤ (2 * σ - 1) * (f x) ^ 2 + x ^ (2 * σ - 2) / (2 * σ - 1)`.
* `integral_Ioc_two_mul_mellin_le`: integrated `L²(0, 1)` Mellin energy domination bound.
-/

@[expose] public section

open MeasureTheory Set

/-- Real Mellin weight kernel `mellinWeight σ x = x ^ (σ - 1)`. -/
noncomputable def mellinWeight (σ x : ℝ) : ℝ :=
  x ^ (σ - 1)

lemma intervalIntegrable_sq_mellinWeight {σ : ℝ} (hσ : 1 / 2 < σ) :
    IntervalIntegrable (fun x : ℝ => x ^ (2 * σ - 2)) volume 0 1 :=
  intervalIntegral.intervalIntegrable_rpow' (by linarith : (-1 : ℝ) < 2 * σ - 2)

/-- For `1 / 2 < σ`, `(mellinWeight σ) ^ 2` is integrable on `Set.Ioc 0 1`. -/
theorem integrableOn_sq_mellinWeight {σ : ℝ} (hσ : 1 / 2 < σ) :
    IntegrableOn (fun x : ℝ => (mellinWeight σ x) ^ 2) (Ioc (0 : ℝ) 1) := by
  have hint : IntegrableOn (fun x : ℝ => x ^ (2 * σ - 2)) (Ioc (0 : ℝ) 1) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0 : ℝ) ≤ 1)).mp
      (intervalIntegrable_sq_mellinWeight hσ)
  refine hint.congr_fun (fun x hx => ?_) measurableSet_Ioc
  dsimp only [mellinWeight]
  rw [← Real.rpow_natCast (x ^ (σ - 1)) 2, ← Real.rpow_mul hx.1.le]
  congr 1
  push_cast
  ring

/-- Exact `L²(0, 1)` energy of `mellinWeight σ` for `1 / 2 < σ`:
`∫ x in Ioc 0 1, x ^ (2 * σ - 2) = 1 / (2 * σ - 1)`. -/
theorem integral_Ioc_sq_mellinWeight {σ : ℝ} (hσ : 1 / 2 < σ) :
    ∫ x in Ioc (0 : ℝ) 1, x ^ (2 * σ - 2) = 1 / (2 * σ - 1) := by
  have hw : 0 < 2 * σ - 1 := by linarith
  have hexp : 2 * σ - 2 + 1 = 2 * σ - 1 := by ring
  rw [← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
    integral_rpow (Or.inl (by linarith : (-1 : ℝ) < 2 * σ - 2)), hexp,
    Real.one_rpow, Real.zero_rpow hw.ne', sub_zero]

/-- Equivalent form in terms of `(mellinWeight σ x) ^ 2`:
`∫ x in Ioc 0 1, (mellinWeight σ x) ^ 2 = 1 / (2 * σ - 1)`. -/
theorem integral_Ioc_mellinWeight_sq {σ : ℝ} (hσ : 1 / 2 < σ) :
    ∫ x in Ioc (0 : ℝ) 1, (mellinWeight σ x) ^ 2 = 1 / (2 * σ - 1) := by
  rw [← integral_Ioc_sq_mellinWeight hσ]
  refine setIntegral_congr_fun measurableSet_Ioc fun x hx => ?_
  dsimp only [mellinWeight]
  rw [← Real.rpow_natCast (x ^ (σ - 1)) 2, ← Real.rpow_mul hx.1.le]
  congr 1
  push_cast
  ring

/-- Unconditional pointwise weighted AM-GM / Cauchy–Schwarz inequality for `1 / 2 < σ` and
`0 < x`:
`2 * (f x * x ^ (σ - 1)) ≤ (2 * σ - 1) * (f x) ^ 2 + x ^ (2 * σ - 2) / (2 * σ - 1)`. -/
theorem sq_mellin_weighted_le_div_two_mul_sub_one (f : ℝ → ℝ) {σ x : ℝ}
    (hσ : 1 / 2 < σ) (hx : 0 < x) :
    2 * (f x * x ^ (σ - 1)) ≤
      (2 * σ - 1) * (f x) ^ 2 + x ^ (2 * σ - 2) / (2 * σ - 1) := by
  have hw : 0 < 2 * σ - 1 := by linarith
  have hsq_exp : (x ^ (σ - 1)) ^ 2 = x ^ (2 * σ - 2) := by
    rw [← Real.rpow_natCast (x ^ (σ - 1)) 2, ← Real.rpow_mul hx.le]
    congr 1
    push_cast
    ring
  have hnonneg : 0 ≤ ((2 * σ - 1) * f x - x ^ (σ - 1)) ^ 2 / (2 * σ - 1) :=
    div_nonneg (sq_nonneg _) hw.le
  rw [← hsq_exp]
  have hid : (2 * σ - 1) * (f x) ^ 2 + (x ^ (σ - 1)) ^ 2 / (2 * σ - 1) -
      2 * (f x * x ^ (σ - 1)) =
      ((2 * σ - 1) * f x - x ^ (σ - 1)) ^ 2 / (2 * σ - 1) := by
    field_simp [hw.ne']
    ring
  linarith

/-- Integrated `L²(0, 1)` Mellin domination inequality: for `1 / 2 < σ` and `f` with `f ^ 2` and
`f x * x ^ (σ - 1)` integrable on `Ioc 0 1`,
`2 * ∫ x in Ioc 0 1, f x * x ^ (σ - 1) ≤ ((2 * σ - 1) * ∫ x in Ioc 0 1, f x ^ 2) +`
`1 / (2 * σ - 1) ^ 2`. -/
theorem integral_Ioc_two_mul_mellin_le (f : ℝ → ℝ) {σ : ℝ} (hσ : 1 / 2 < σ)
    (hf2 : IntegrableOn (fun x : ℝ => (f x) ^ 2) (Ioc (0 : ℝ) 1))
    (hfm : IntegrableOn (fun x : ℝ => f x * x ^ (σ - 1)) (Ioc (0 : ℝ) 1)) :
    2 * ∫ x in Ioc (0 : ℝ) 1, f x * x ^ (σ - 1) ≤
      ((2 * σ - 1) * ∫ x in Ioc (0 : ℝ) 1, (f x) ^ 2) + 1 / (2 * σ - 1) ^ 2 := by
  have hint_m : IntegrableOn (fun x : ℝ => x ^ (2 * σ - 2)) (Ioc (0 : ℝ) 1) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0 : ℝ) ≤ 1)).mp
      (intervalIntegrable_sq_mellinWeight hσ)
  have hint_rhs : IntegrableOn
      (fun x : ℝ => (2 * σ - 1) * (f x) ^ 2 + x ^ (2 * σ - 2) / (2 * σ - 1))
      (Ioc (0 : ℝ) 1) :=
    (hf2.const_mul (2 * σ - 1)).add (hint_m.div_const (2 * σ - 1))
  have hle : ∫ x in Ioc (0 : ℝ) 1, 2 * (f x * x ^ (σ - 1)) ≤
      ∫ x in Ioc (0 : ℝ) 1,
        ((2 * σ - 1) * (f x) ^ 2 + x ^ (2 * σ - 2) / (2 * σ - 1)) :=
    setIntegral_mono_on (hfm.const_mul 2) hint_rhs measurableSet_Ioc fun x hx =>
      sq_mellin_weighted_le_div_two_mul_sub_one f hσ hx.1
  rw [integral_const_mul, integral_add (hf2.const_mul _) (hint_m.div_const _),
    integral_const_mul, integral_div, integral_Ioc_sq_mellinWeight hσ] at hle
  have hw : (1 / (2 * σ - 1)) / (2 * σ - 1) = 1 / (2 * σ - 1) ^ 2 := by rw [div_div, sq]
  linarith
