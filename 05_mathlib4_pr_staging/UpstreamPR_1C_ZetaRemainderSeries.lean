/-
Copyright (c) 2026 Qamar Munawer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qamar Munawer
-/
module

public import Mathlib.Analysis.Complex.LocallyUniformLimit
public import Mathlib.Analysis.PSeriesComplex
public import Mathlib.NumberTheory.LSeries.RiemannZeta

/-!
# Euler–Maclaurin Remainder Series for the Riemann Zeta Function

This file introduces the first-order Euler–Maclaurin remainder term for `riemannZeta` on
`{s : ℂ | 0 < s.re ∧ s ≠ 1}`:
1. `zetaRemainderTerm`: `(n + 1) ^ (-s) - ((n + 1) ^ (1 - s) - (n + 2) ^ (1 - s)) / (s - 1)`.
2. `zetaRemainderTerm_eq_integral`: integral identity on `[n + 1, n + 2]`.
3. `norm_zetaRemainderTerm_le`: decay bound `‖zetaRemainderTerm s n‖ ≤ B * (n + 1) ^ (-d₀ - 1)`.
4. `analyticOnNhd_tsum_zetaRemainderTerm`: analyticity of `∑' n, zetaRemainderTerm s n` on
   `{s : ℂ | 0 < s.re ∧ s ≠ 1}` via normal convergence.
-/

@[expose] public section

open Complex Set

/-- First-order Euler–Maclaurin remainder term on `[n + 1, n + 2]` for `riemannZeta s`. -/
noncomputable def zetaRemainderTerm (s : ℂ) (n : ℕ) : ℂ :=
  ((n + 1 : ℕ) : ℂ) ^ (-s) -
    (((n + 1 : ℕ) : ℂ) ^ (1 - s) - ((n + 2 : ℕ) : ℂ) ^ (1 - s)) / (s - 1)

/-- Integral representation of the Euler–Maclaurin remainder term:
`zetaRemainderTerm s n = ∫ x in (n + 1)..(n + 2), ((n + 1) ^ (-s) - x ^ (-s))`. -/
theorem zetaRemainderTerm_eq_integral (n : ℕ) {s : ℂ} (hs : s ≠ 1) :
    zetaRemainderTerm s n =
      ∫ x in ((n + 1 : ℕ) : ℝ)..((n + 2 : ℕ) : ℝ),
        (((n + 1 : ℕ) : ℂ) ^ (-s) - (x : ℂ) ^ (-s)) := by
  have ha_pos : (0 : ℝ) < (n + 1 : ℕ) := by positivity
  have hab : ((n + 1 : ℕ) : ℝ) ≤ ((n + 2 : ℕ) : ℝ) := by push_cast; linarith
  have hint_cpow : IntervalIntegrable (fun x : ℝ => (x : ℂ) ^ (-s))
      MeasureTheory.volume ((n + 1 : ℕ) : ℝ) ((n + 2 : ℕ) : ℝ) := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hab]
    exact ContinuousOn.integrableOn_Icc fun x hx =>
      (Complex.continuousAt_ofReal_cpow_const x (-s)
        (Or.inr (lt_of_lt_of_le ha_pos hx.1).ne')).continuousWithinAt
  rw [intervalIntegral.integral_sub intervalIntegrable_const hint_cpow,
    intervalIntegral.integral_const,
    show ((n + 2 : ℕ) : ℝ) - ((n + 1 : ℕ) : ℝ) = 1 by push_cast; ring, one_smul]
  have hs_ne : (-s : ℂ) ≠ -1 := fun h => hs (by linear_combination -h)
  have h0_not : (0 : ℝ) ∉ uIcc ((n + 1 : ℕ) : ℝ) ((n + 2 : ℕ) : ℝ) := by
    rw [uIcc_of_le hab, mem_Icc]
    intro h0; linarith [h0.1]
  rw [integral_cpow (Or.inr ⟨hs_ne, h0_not⟩), show -s + 1 = 1 - s by ring]
  unfold zetaRemainderTerm
  push_cast
  field_simp [sub_ne_zero.mpr hs]
  ring

/-- Uniform upper bound on the Euler–Maclaurin remainder term: for `0 < d₀ ≤ s.re`,
`‖s‖ ≤ B`, and `s ≠ 1`, we have `‖zetaRemainderTerm s n‖ ≤ B * (n + 1) ^ (-d₀ - 1)`. -/
theorem norm_zetaRemainderTerm_le (n : ℕ) {s : ℂ} {d₀ B : ℝ}
    (hd₀ : 0 < d₀) (hs_re : d₀ ≤ s.re) (hs_norm : ‖s‖ ≤ B) (hs1 : s ≠ 1) :
    ‖zetaRemainderTerm s n‖ ≤ B * ((n + 1 : ℝ) ^ (-d₀ - 1)) := by
  rw [zetaRemainderTerm_eq_integral n hs1]
  have ha_pos : (0 : ℝ) < (n + 1 : ℕ) := by positivity
  have hab : ((n + 1 : ℕ) : ℝ) ≤ ((n + 2 : ℕ) : ℝ) := by push_cast; linarith
  have h_diff_len : |((n + 2 : ℕ) : ℝ) - ((n + 1 : ℕ) : ℝ)| = 1 := by push_cast; norm_num
  have hs_ne0 : -s ≠ 0 := fun h0 => by
    have hre : s.re = 0 := by simpa using congrArg Complex.re h0
    linarith
  have h_mvt : ∀ x ∈ Icc ((n + 1 : ℕ) : ℝ) ((n + 2 : ℕ) : ℝ),
      ‖((n + 1 : ℕ) : ℂ) ^ (-s) - (x : ℂ) ^ (-s)‖ ≤ B * ((n + 1 : ℝ) ^ (-d₀ - 1)) := by
    intro x hx
    let f : ℝ → ℂ := fun t => (t : ℂ) ^ (-s)
    let f' : ℝ → ℂ := fun t => (-s) * (t : ℂ) ^ (-s - 1)
    have hderiv : ∀ t ∈ Icc ((n + 1 : ℕ) : ℝ) ((n + 2 : ℕ) : ℝ),
        HasDerivWithinAt f (f' t) (Icc ((n + 1 : ℕ) : ℝ) ((n + 2 : ℕ) : ℝ)) t := fun t ht =>
      (hasDerivAt_ofReal_cpow_const (lt_of_lt_of_le ha_pos ht.1).ne' hs_ne0).hasDerivWithinAt
    have hbound : ∀ t ∈ Icc ((n + 1 : ℕ) : ℝ) ((n + 2 : ℕ) : ℝ),
        ‖f' t‖ ≤ B * ((n + 1 : ℝ) ^ (-d₀ - 1)) := by
      intro t ht
      have ht_pos : (0 : ℝ) < t := lt_of_lt_of_le ha_pos ht.1
      have hna_le : (n + 1 : ℝ) ≤ t := by exact_mod_cast ht.1
      have h1_le : (1 : ℝ) ≤ (n + 1 : ℝ) := by exact_mod_cast Nat.succ_pos n
      dsimp [f']
      rw [norm_mul, norm_neg, Complex.norm_cpow_eq_rpow_re_of_pos ht_pos,
        show (-s - 1).re = -s.re - 1 by simp]
      have h_pow_le1 : t ^ (-s.re - 1) ≤ t ^ (-d₀ - 1) :=
        Real.rpow_le_rpow_of_exponent_le (le_trans h1_le hna_le) (by linarith)
      have h_pow_le2 : t ^ (-d₀ - 1) ≤ (n + 1 : ℝ) ^ (-d₀ - 1) :=
        Real.rpow_le_rpow_of_nonpos (by positivity) hna_le (by linarith)
      exact mul_le_mul hs_norm (h_pow_le1.trans h_pow_le2) (by positivity)
        ((norm_nonneg s).trans hs_norm)
    have h_diff :=
      (convex_Icc ((n + 1 : ℕ) : ℝ) ((n + 2 : ℕ) : ℝ)).norm_image_sub_le_of_norm_hasDerivWithin_le
        hderiv hbound (left_mem_Icc.mpr hab) hx
    have h_dist : ‖x - ((n + 1 : ℕ) : ℝ)‖ ≤ 1 := by
      rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hx.1)]
      have hx2 : x ≤ ((n + 2 : ℕ) : ℝ) := hx.2
      push_cast at hx2 ⊢; linarith
    have hC_nn : 0 ≤ B * ((n + 1 : ℝ) ^ (-d₀ - 1)) :=
      mul_nonneg ((norm_nonneg s).trans hs_norm) (by positivity)
    simpa [f, norm_sub_rev] using h_diff.trans (mul_le_of_le_one_right hC_nn h_dist)
  have h_int :
      ‖∫ x in ((n + 1 : ℕ) : ℝ)..((n + 2 : ℕ) : ℝ),
          (((n + 1 : ℕ) : ℂ) ^ (-s) - (x : ℂ) ^ (-s))‖ ≤
        B * ((n + 1 : ℝ) ^ (-d₀ - 1)) * |((n + 2 : ℕ) : ℝ) - ((n + 1 : ℕ) : ℝ)| :=
    intervalIntegral.norm_integral_le_of_norm_le_const fun x hx => by
      rw [uIoc_of_le hab] at hx
      exact h_mvt x (Ioc_subset_Icc_self hx)
  rwa [h_diff_len, mul_one] at h_int

/-- Summability of the majorant `n ↦ B * (n + 1) ^ (-d₀ - 1)` for `0 < d₀`. -/
theorem summable_zetaRemainderTerm_majorant (d₀ B : ℝ) (hd₀ : 0 < d₀) :
    Summable (fun n : ℕ => B * ((n + 1 : ℝ) ^ (-d₀ - 1))) := by
  have h1 : 1 < d₀ + 1 := by linarith
  have hs : Summable (fun n : ℕ => ((n + 1 : ℝ) ^ (-(d₀ + 1)))) := by
    refine ((summable_nat_add_iff 1).mpr (Real.summable_nat_rpow_inv.mpr h1)).congr fun n => ?_
    rw [Nat.cast_add, Nat.cast_one, Real.rpow_neg (by positivity)]
  refine (hs.mul_left B).congr fun n => ?_
  congr 1; congr 1; ring

/-- Summability of `zetaRemainderTerm s` on `{s : ℂ | 0 < s.re ∧ s ≠ 1}`. -/
theorem summable_zetaRemainderTerm {s : ℂ} (hs_pos : 0 < s.re) (hs1 : s ≠ 1) :
    Summable (zetaRemainderTerm s) :=
  ((summable_zetaRemainderTerm_majorant s.re ‖s‖ hs_pos).of_nonneg_of_le
    (fun _ => norm_nonneg _)
    (fun n => norm_zetaRemainderTerm_le n hs_pos le_rfl le_rfl hs1)).of_norm

/-- Analyticity of the Euler–Maclaurin remainder sum `∑' n, zetaRemainderTerm s n` on
`{s : ℂ | 0 < s.re ∧ s ≠ 1}`. -/
theorem analyticOnNhd_tsum_zetaRemainderTerm :
    AnalyticOnNhd ℂ (fun s : ℂ => ∑' n : ℕ, zetaRemainderTerm s n)
      {s : ℂ | 0 < s.re ∧ s ≠ 1} := by
  have hS_open : IsOpen {s : ℂ | 0 < s.re ∧ s ≠ 1} :=
    (isOpen_lt continuous_const Complex.continuous_re).inter isOpen_ne
  refine DifferentiableOn.analyticOnNhd (fun s hs => ?_) hS_open
  let d₀ : ℝ := s.re / 2
  let B : ℝ := ‖s‖ + 1
  have hd₀ : 0 < d₀ := by dsimp [d₀]; linarith [hs.1]
  let U : Set ℂ := {w : ℂ | d₀ < w.re ∧ ‖w‖ < B ∧ w ≠ 1}
  have hU_open : IsOpen U :=
    (isOpen_lt (continuous_const : Continuous fun _ : ℂ => d₀) Complex.continuous_re).inter
      ((isOpen_lt continuous_norm (continuous_const : Continuous fun _ : ℂ => B)).inter
        isOpen_ne)
  have h_diff_term : ∀ n : ℕ, DifferentiableOn ℂ (fun w : ℂ => zetaRemainderTerm w n) U := by
    intro n w hw
    have hn1 : ((n + 1 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have hn2 : ((n + 2 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have h1 : DifferentiableAt ℂ (fun z : ℂ => ((n + 1 : ℕ) : ℂ) ^ (-z)) w :=
      differentiableAt_id.neg.const_cpow (Or.inl hn1)
    have h2 : DifferentiableAt ℂ (fun z : ℂ => ((n + 1 : ℕ) : ℂ) ^ (1 - z)) w :=
      ((differentiableAt_const (1 : ℂ)).sub differentiableAt_id).const_cpow (Or.inl hn1)
    have h3 : DifferentiableAt ℂ (fun z : ℂ => ((n + 2 : ℕ) : ℂ) ^ (1 - z)) w :=
      ((differentiableAt_const (1 : ℂ)).sub differentiableAt_id).const_cpow (Or.inl hn2)
    have h_all : DifferentiableAt ℂ (fun z : ℂ => zetaRemainderTerm z n) w := by
      unfold zetaRemainderTerm
      exact h1.sub ((h2.sub h3).div (differentiableAt_id.sub (differentiableAt_const 1))
        (sub_ne_zero.mpr hw.2.2))
    exact h_all.differentiableWithinAt
  have h_diff_U := Complex.differentiableOn_tsum_of_summable_norm
    (summable_zetaRemainderTerm_majorant d₀ B hd₀) h_diff_term hU_open
    fun n w hw => norm_zetaRemainderTerm_le n hd₀ hw.1.le hw.2.1.le hw.2.2
  have hs_mem : s ∈ U := ⟨by dsimp [d₀]; linarith [hs.1], by dsimp [B]; linarith, hs.2⟩
  exact (h_diff_U.differentiableAt (hU_open.mem_nhds hs_mem)).differentiableWithinAt
