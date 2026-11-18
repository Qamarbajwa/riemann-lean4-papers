/-
Copyright (c) 2026 Qamar Munawer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qamar Munawer
-/
module

public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.NumberTheory.Harmonic.Bounds
public import RiemannBlueprint.UpstreamPRs.UpstreamPR_1D_ZetaPartialSummation

/-!
# Unconditional Logarithmic Strip Growth Bound for the Riemann Zeta Function

Using Euler–Maclaurin partial summation up to `M = ⌊|s.im|⌋ + 1` and an integral comparison tail
bound, this file proves the classical logarithmic upper bound for `‖riemannZeta s‖` in the
boundary strip `1 - 1 / (2 * log (|s.im| + 2)) ≤ s.re ≤ 2` when `3 / 2 ≤ |s.im|`.
-/

@[expose] public section

open Complex Set

/-- Integral-comparison upper bound on the tail power sum
`∑' n, (n + M + 1) ^ (-σ - 1) ≤ (M + 1) ^ (-σ - 1) + (M + 1) ^ (-σ) / σ`. -/
theorem tsum_rpow_neg_sub_one_le (M : ℕ) {σ : ℝ} (hσ : 0 < σ) :
    ∑' n : ℕ, ((n + M + 1 : ℝ) ^ (-σ - 1)) ≤
      (M + 1 : ℝ) ^ (-σ - 1) + (M + 1 : ℝ) ^ (-σ) / σ := by
  have h_summ : Summable (fun n : ℕ => ((n + M + 1 : ℝ) ^ (-σ - 1))) := by
    refine ((summable_nat_add_iff (M + 1)).mpr
      (Real.summable_nat_rpow_inv.mpr (by linarith : 1 < σ + 1))).congr fun n => ?_
    push_cast; rw [← Real.rpow_neg (by positivity)]; ring_nf
  refine h_summ.tsum_le_of_sum_range_le fun N => ?_
  cases N with
  | zero => simp only [Finset.range_zero, Finset.sum_empty]; positivity
  | succ N =>
    rw [Finset.sum_range_eq_add_Ico _ (Nat.succ_pos N)]
    simp only [Nat.cast_zero, zero_add]
    gcongr
    have h_step : ∀ k ∈ Finset.Ico 1 (N + 1),
        ((k + M + 1 : ℝ) ^ (-σ - 1)) ≤
          ∫ x in ((k + M : ℕ) : ℝ)..((k + M + 1 : ℕ) : ℝ), x ^ (-σ - 1) := by
      intro k hk
      have ha_pos : (0 : ℝ) < (k + M : ℕ) := by
        have hk1 : 1 ≤ k := (Finset.mem_Ico.mp hk).1; positivity
      have hab : ((k + M : ℕ) : ℝ) ≤ ((k + M + 1 : ℕ) : ℝ) := by push_cast; linarith
      have hint : IntervalIntegrable (fun x : ℝ => x ^ (-σ - 1))
          MeasureTheory.volume ((k + M : ℕ) : ℝ) ((k + M + 1 : ℕ) : ℝ) := by
        rw [intervalIntegrable_iff_integrableOn_Icc_of_le hab]
        exact (ContinuousOn.rpow_const continuousOn_id fun x hx =>
          Or.inl (lt_of_lt_of_le ha_pos hx.1).ne').integrableOn_Icc
      have h_int := intervalIntegral.integral_mono_on hab intervalIntegrable_const hint
        fun x hx => Real.rpow_le_rpow_of_nonpos (lt_of_lt_of_le ha_pos hx.1)
          (by exact_mod_cast hx.2) (by linarith)
      simpa [intervalIntegral.integral_const, Nat.cast_add, Nat.cast_one] using h_int
    calc ∑ k ∈ Finset.Ico 1 (N + 1), ((k + M + 1 : ℝ) ^ (-σ - 1))
        ≤ ∑ k ∈ Finset.Ico 1 (N + 1),
            ∫ x in ((k + M : ℕ) : ℝ)..((k + M + 1 : ℕ) : ℝ), x ^ (-σ - 1) :=
          Finset.sum_le_sum h_step
      _ = ∑ k ∈ Finset.Ico 1 (N + 1),
            ∫ x in (M + (k : ℕ) : ℝ)..(M + ((k + 1 : ℕ) : ℝ)), x ^ (-σ - 1) := by
          refine Finset.sum_congr rfl fun k _ => ?_; push_cast; ring_nf
      _ = ∫ x in (M + (1 : ℕ) : ℝ)..(M + ((N + 1 : ℕ) : ℝ)), x ^ (-σ - 1) := by
          refine intervalIntegral.sum_integral_adjacent_intervals_Ico (Nat.le_add_left 1 N) ?_
          intro k hk
          have ha_pos : (0 : ℝ) < (M : ℝ) + k := by
            have hk1 : 1 ≤ k := (Set.mem_Ico.mp hk).1; positivity
          rw [intervalIntegrable_iff_integrableOn_Icc_of_le (by push_cast; linarith)]
          exact (ContinuousOn.rpow_const continuousOn_id fun x hx =>
            Or.inl (lt_of_lt_of_le ha_pos hx.1).ne').integrableOn_Icc
      _ ≤ (M + 1 : ℝ) ^ (-σ) / σ := by
          have ha_pos : (0 : ℝ) < (M : ℝ) + (1 : ℕ) := by positivity
          have hab : (M : ℝ) + (1 : ℕ) ≤ (M : ℝ) + (N + 1 : ℕ) := by push_cast; linarith
          have h0_not : (0 : ℝ) ∉ uIcc ((M : ℝ) + (1 : ℕ)) ((M : ℝ) + (N + 1 : ℕ)) := by
            rw [uIcc_of_le hab, mem_Icc]; intro h0; linarith [h0.1, ha_pos]
          rw [integral_rpow (Or.inr ⟨by linarith, h0_not⟩), show -σ - 1 + 1 = -σ by ring]
          have h_eq1 : ((((M : ℝ) + (N + 1 : ℕ)) ^ (-σ) - ((M : ℝ) + (1 : ℕ)) ^ (-σ)) / (-σ)) =
              (((M + 1 : ℝ) ^ (-σ) - ((M : ℝ) + (N + 1 : ℕ)) ^ (-σ)) / σ) := by
            push_cast; field_simp; ring
          rw [h_eq1]
          exact div_le_div_of_nonneg_right (sub_le_self _ (by positivity)) hσ.le

/-- Unconditional logarithmic growth bound in the boundary strip
`1 - 1 / (2 * log (|s.im| + 2)) ≤ s.re ≤ 2` for `3 / 2 ≤ |s.im|`. -/
theorem norm_riemannZeta_le_of_log_strip {s : ℂ} (ht : 3 / 2 ≤ |s.im|)
    (hre_lo : 1 - 1 / (2 * Real.log (|s.im| + 2)) ≤ s.re) (hre_hi : s.re ≤ 2) :
    ‖riemannZeta s‖ ≤ (10 * Real.exp 1 + 3) * Real.log (|s.im| + 2) := by
  have hlog_gt_one : 1 < Real.log (|s.im| + 2) := by
    rw [← Real.log_exp 1]
    exact Real.log_lt_log (Real.exp_pos 1) (lt_of_lt_of_le Real.exp_one_lt_three (by linarith))
  have hlog_pos : 0 < Real.log (|s.im| + 2) := by linarith
  have hs_re_gt_half : 1 / 2 < s.re := by
    have h1 : 1 / (2 * Real.log (|s.im| + 2)) < 1 / 2 := by
      rw [div_lt_div_iff₀ (by positivity) (by norm_num)]; linarith
    linarith
  have hs_pos : 0 < s.re := by linarith
  have hs_im : s.im ≠ 0 := fun h0 => by rw [h0, abs_zero] at ht; linarith
  have hs1 : s ≠ 1 := fun h => hs_im (by rw [h]; simp)
  let M : ℕ := Nat.floor |s.im| + 1
  have hM_ge : 1 ≤ M := by omega
  have hM_le : (M : ℝ) ≤ |s.im| + 1 := by
    dsimp [M]; push_cast; linarith [Nat.floor_le (abs_nonneg s.im)]
  have hM_gt : |s.im| < (M : ℝ) := by dsimp [M]; push_cast; exact Nat.lt_floor_add_one |s.im|
  have hM1_le : (M + 1 : ℝ) ≤ |s.im| + 2 := by linarith
  have h_pow_exp : ∀ x : ℝ, 1 ≤ x → x ≤ |s.im| + 2 → x ^ (1 - s.re) ≤ Real.exp 1 := by
    intro x hx1 hx_le
    by_cases hs_ge1 : 1 ≤ s.re
    · exact (Real.rpow_le_one_of_one_le_of_nonpos hx1 (by linarith)).trans
        (Real.one_le_exp (by norm_num))
    · have hexp_nn : 0 ≤ 1 - s.re := by linarith
      have hx_pos : 0 < x := by linarith
      rw [Real.rpow_def_of_pos hx_pos, Real.exp_le_exp]
      have hlogx : Real.log x ≤ Real.log (|s.im| + 2) := Real.log_le_log hx_pos hx_le
      have hhalf : 1 / (2 * Real.log (|s.im| + 2)) ≤ 1 / Real.log (|s.im| + 2) :=
        div_le_div_of_nonneg_left zero_le_one hlog_pos (by linarith)
      calc Real.log x * (1 - s.re)
          ≤ Real.log (|s.im| + 2) * (1 - s.re) := mul_le_mul_of_nonneg_right hlogx hexp_nn
        _ ≤ Real.log (|s.im| + 2) * (1 / Real.log (|s.im| + 2)) :=
            mul_le_mul_of_nonneg_left (by linarith) hlog_pos.le
        _ = 1 := mul_one_div_cancel hlog_pos.ne'
  rw [riemannZeta_partial_summation M hs_pos hs_im]
  have h_sum_bound : ‖∑ n ∈ Finset.range M, ((n + 1 : ℕ) : ℂ) ^ (-s)‖ ≤
      Real.exp 1 * (2 * Real.log (|s.im| + 2)) := by
    have h1 := norm_sum_le (Finset.range M) fun n => ((n + 1 : ℕ) : ℂ) ^ (-s)
    have h2 : ∑ n ∈ Finset.range M, ‖((n + 1 : ℕ) : ℂ) ^ (-s)‖ ≤
        Real.exp 1 * ∑ n ∈ Finset.range M, ((n + 1 : ℝ)⁻¹) := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun n hn => ?_
      have hn1_pos : (0 : ℝ) < (n + 1 : ℝ) := by positivity
      have hn1_ge1 : (1 : ℝ) ≤ (n + 1 : ℝ) := by exact_mod_cast Nat.succ_pos n
      have hn1_le : (n + 1 : ℝ) ≤ |s.im| + 2 := by
        have h_nat : (n + 1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast Finset.mem_range.mp hn
        linarith
      rw [Nat.cast_add, Nat.cast_one, ← Complex.ofReal_natCast, ← Complex.ofReal_one,
        ← Complex.ofReal_add, Complex.norm_cpow_eq_rpow_re_of_pos hn1_pos, Complex.neg_re,
        show (n + 1 : ℝ) ^ (-s.re) = (n + 1 : ℝ) ^ (1 - s.re) * (n + 1 : ℝ)⁻¹ by
          rw [show -s.re = (1 - s.re) + (-1) by ring, Real.rpow_add hn1_pos, Real.rpow_neg_one]]
      exact mul_le_mul_of_nonneg_right (h_pow_exp (n + 1) hn1_ge1 hn1_le) (by positivity)
    have h_harm : ∑ n ∈ Finset.range M, ((n + 1 : ℝ)⁻¹) ≤ 2 * Real.log (|s.im| + 2) := by
      rw [show ∑ n ∈ Finset.range M, ((n + 1 : ℝ)⁻¹) = (harmonic M : ℝ) by
        simp [harmonic, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]]
      have h_le1 : (harmonic M : ℝ) ≤ 1 + Real.log M := harmonic_le_one_add_log M
      have h_le2 : Real.log (M : ℝ) ≤ Real.log (|s.im| + 2) :=
        Real.log_le_log (by exact_mod_cast hM_ge) (by linarith)
      linarith
    exact h1.trans (h2.trans (mul_le_mul_of_nonneg_left h_harm (Real.exp_pos 1).le))
  have h_bdry_bound : ‖((M + 1 : ℕ) : ℂ) ^ (1 - s) / (s - 1)‖ ≤ Real.exp 1 := by
    have hM1_pos : (0 : ℝ) < (M + 1 : ℝ) := by positivity
    rw [norm_div, show (((M + 1 : ℕ) : ℂ)) = ((M + 1 : ℝ) : ℂ) by push_cast; rfl,
      Complex.norm_cpow_eq_rpow_re_of_pos hM1_pos, Complex.sub_re, Complex.one_re]
    have h_den : 1 ≤ ‖s - 1‖ := by
      calc (1 : ℝ) ≤ 3 / 2 := by norm_num
        _ ≤ |s.im| := ht
        _ = |(s - 1).im| := by simp
        _ ≤ ‖s - 1‖ := Complex.abs_im_le_norm (s - 1)
    exact (div_le_self (by positivity) h_den).trans (h_pow_exp (M + 1) (by linarith) hM1_le)
  have h_tail_bound : ‖∑' n : ℕ, zetaRemainderTerm s (n + M)‖ ≤ 3 + 6 * Real.exp 1 := by
    have h_summ : Summable (fun n : ℕ => zetaRemainderTerm s (n + M)) :=
      (summable_zetaRemainderTerm hs_pos hs1).comp_injective (add_left_injective M)
    have h1 := norm_tsum_le_tsum_norm h_summ.norm
    have h_rhs_summ : Summable (fun n : ℕ => ‖s‖ * ((n + M + 1 : ℝ) ^ (-s.re - 1))) := by
      refine (((summable_nat_add_iff (M + 1)).mpr
        (Real.summable_nat_rpow_inv.mpr (by linarith : 1 < s.re + 1))).congr fun n => ?_).mul_left
          ‖s‖
      push_cast; rw [← Real.rpow_neg (by positivity)]; ring_nf
    have h2 : ∑' n : ℕ, ‖zetaRemainderTerm s (n + M)‖ ≤
        ‖s‖ * ∑' n : ℕ, ((n + M + 1 : ℝ) ^ (-s.re - 1)) := by
      rw [← tsum_mul_left]
      exact h_summ.norm.tsum_le_tsum (fun n => by
        simpa [Nat.cast_add, Nat.cast_one, add_assoc] using
          norm_zetaRemainderTerm_le (n + M) hs_pos le_rfl le_rfl hs1) h_rhs_summ
    have h3 := tsum_rpow_neg_sub_one_le M hs_pos
    have h_norm_s : ‖s‖ ≤ 3 * (M + 1 : ℝ) := by
      calc ‖s‖ ≤ |s.re| + |s.im| := Complex.norm_le_abs_re_add_abs_im s
        _ = s.re + |s.im| := by rw [abs_of_pos hs_pos]
        _ ≤ 3 * (M + 1 : ℝ) := by linarith
    have hM1_pos : (0 : ℝ) < (M + 1 : ℝ) := by positivity
    have h_prod1 : ‖s‖ * ((M + 1 : ℝ) ^ (-s.re - 1)) ≤ 3 := by
      have h_step := mul_le_mul_of_nonneg_right h_norm_s
        (by positivity : 0 ≤ (M + 1 : ℝ) ^ (-s.re - 1))
      have heq : (M + 1 : ℝ) * ((M + 1 : ℝ) ^ (-s.re - 1)) = (M + 1 : ℝ) ^ (-s.re) := by
        conv_lhs => arg 1; rw [← Real.rpow_one (M + 1 : ℝ)]
        rw [← Real.rpow_add hM1_pos]; congr 1; ring
      have h_le_one : (M + 1 : ℝ) ^ (-s.re) ≤ 1 :=
        Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by linarith)
      linarith [h_step, show (3 * (M + 1 : ℝ)) * ((M + 1 : ℝ) ^ (-s.re - 1)) =
        3 * ((M + 1 : ℝ) ^ (-s.re)) by rw [mul_assoc, heq]]
    have h_prod2 : ‖s‖ * ((M + 1 : ℝ) ^ (-s.re) / s.re) ≤ 6 * Real.exp 1 := by
      have h_step : ‖s‖ * ((M + 1 : ℝ) ^ (-s.re) / s.re) ≤
          (3 * (M + 1 : ℝ)) * ((M + 1 : ℝ) ^ (-s.re) / (1 / 2)) :=
        mul_le_mul h_norm_s (div_le_div_of_nonneg_left (by positivity) (by norm_num)
          hs_re_gt_half.le) (by positivity) (by positivity)
      have heq : (M + 1 : ℝ) * ((M + 1 : ℝ) ^ (-s.re)) = (M + 1 : ℝ) ^ (1 - s.re) := by
        conv_lhs => arg 1; rw [← Real.rpow_one (M + 1 : ℝ)]
        rw [← Real.rpow_add hM1_pos, sub_eq_add_neg]
      have h_exp := h_pow_exp (M + 1) (by linarith) hM1_le
      linarith [h_step, show (3 * (M + 1 : ℝ)) * ((M + 1 : ℝ) ^ (-s.re) / (1 / 2)) =
        6 * ((M + 1 : ℝ) ^ (1 - s.re)) by rw [← heq]; ring]
    calc ‖∑' n : ℕ, zetaRemainderTerm s (n + M)‖
        ≤ ‖s‖ * ∑' n : ℕ, ((n + M + 1 : ℝ) ^ (-s.re - 1)) := h1.trans h2
      _ ≤ ‖s‖ * ((M + 1 : ℝ) ^ (-s.re - 1) + (M + 1 : ℝ) ^ (-s.re) / s.re) :=
          mul_le_mul_of_nonneg_left h3 (norm_nonneg s)
      _ = ‖s‖ * ((M + 1 : ℝ) ^ (-s.re - 1)) + ‖s‖ * ((M + 1 : ℝ) ^ (-s.re) / s.re) := mul_add _ _ _
      _ ≤ 3 + 6 * Real.exp 1 := add_le_add h_prod1 h_prod2
  have h_tri1 := norm_add_le
    ((∑ n ∈ Finset.range M, ((n + 1 : ℕ) : ℂ) ^ (-s)) + ((M + 1 : ℕ) : ℂ) ^ (1 - s) / (s - 1))
    (∑' n : ℕ, zetaRemainderTerm s (n + M))
  have h_tri2 := norm_add_le
    (∑ n ∈ Finset.range M, ((n + 1 : ℕ) : ℂ) ^ (-s)) (((M + 1 : ℕ) : ℂ) ^ (1 - s) / (s - 1))
  have h_log_one : (7 * Real.exp 1 + 3) ≤ (8 * Real.exp 1 + 3) * Real.log (|s.im| + 2) :=
    (le_mul_of_one_le_right (by positivity) hlog_gt_one.le).trans
      (mul_le_mul_of_nonneg_right (by linarith [Real.exp_pos 1]) hlog_pos.le)
  linarith
