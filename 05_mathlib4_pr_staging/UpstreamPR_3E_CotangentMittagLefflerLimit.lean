/-
Copyright (c) 2026 Qamar Munawer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qamar Munawer
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Cotangent
public import Mathlib.Tactic.Linarith
public import RiemannBlueprint.UpstreamPRs.UpstreamPR_3B_VasyuninSmoothAndCotDefs

/-!
# Residue-Class Cotangent Pairing and Mittag-Leffler Limit

This file pairs opposite fractional-part terms modulo `b` into `cotApproxSum` and evaluates
their limit via Mathlib's Mittag-Leffler series `cot_series_rep'`:
1. `cotApproxSum`: residue-class cotangent partial sum mod `b`.
2. `sum_Ico_fract_diff_div_eq_cotApproxSum`: exact equivalence with the odd fractional-part sum.
3. `tendsto_cotApproxSum_term`, `tendsto_cotApproxSum`: limit `(π / b) * vasyuninCotSum b a`.
-/

@[expose] public section

open Filter

/-- Residue-class cotangent partial sum approximating `(π / b) * vasyuninCotSum b a`. -/
noncomputable def cotApproxSum (a b M : ℕ) : ℝ :=
  ∑ r ∈ Finset.Ico 1 b,
    Int.fract ((r : ℝ) * (a : ℝ) / (b : ℝ)) *
      ∑ q ∈ Finset.range M,
        (1 / ((q : ℝ) * (b : ℝ) + (r : ℝ)) -
          1 / (((q + 1 : ℕ) : ℝ) * (b : ℝ) - (r : ℝ)))

private lemma sum_Ico_eq_sum_Ico_sum_range (f : ℕ → ℝ) (b M : ℕ) (hb : 1 ≤ b)
    (hf0 : ∀ q : ℕ, f (q * b) = 0) :
    ∑ m ∈ Finset.Ico 1 (M * b), f m =
      ∑ r ∈ Finset.Ico 1 b, ∑ q ∈ Finset.range M, f (q * b + r) := by
  have h2 : ∑ m ∈ Finset.range (M * b), f m =
      ∑ q ∈ Finset.range M, ∑ r ∈ Finset.range b, f (q * b + r) := by
    induction M with
    | zero => simp
    | succ M ih => rw [Nat.succ_mul, Finset.sum_range_add, ih, Finset.sum_range_succ]
  have h1 : ∑ m ∈ Finset.Ico 1 (M * b), f m = ∑ m ∈ Finset.range (M * b), f m := by
    by_cases hM : M = 0
    · subst hM; simp
    · have hMb : 1 ≤ M * b := Nat.mul_pos (Nat.pos_of_ne_zero hM) hb
      have hsplit : Finset.range (M * b) = insert 0 (Finset.Ico 1 (M * b)) := by
        ext m; simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Ico]; omega
      rw [hsplit, Finset.sum_insert (by simp), show f 0 = 0 by simpa using hf0 0, zero_add]
  rw [h1, h2, Finset.sum_comm]
  have h0b : Finset.range b = insert 0 (Finset.Ico 1 b) := by
    ext r; simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Ico]; omega
  rw [h0b, Finset.sum_insert (by simp),
    Finset.sum_eq_zero fun q _ => by simpa using hf0 q, zero_add]

/-- Exact residue-class pairing equating the antisymmetric fractional-part harmonic sum on
`Finset.Ico 1 (M * b)` to `cotApproxSum a b M`. -/
theorem sum_Ico_fract_diff_div_eq_cotApproxSum {a b M : ℕ} (hb : 1 ≤ b) :
    ∑ m ∈ Finset.Ico 1 (M * b),
        (Int.fract ((m : ℝ) * (a : ℝ) / (b : ℝ)) -
          Int.fract (-((m : ℝ) * (a : ℝ) / (b : ℝ)))) / (m : ℝ) =
      cotApproxSum a b M := by
  have hb_pos : (0 : ℝ) < (b : ℝ) := Nat.cast_pos.mpr hb
  let f : ℕ → ℝ := fun m => (Int.fract ((m : ℝ) * (a : ℝ) / (b : ℝ)) -
    Int.fract (-((m : ℝ) * (a : ℝ) / (b : ℝ)))) / (m : ℝ)
  have hf0 : ∀ q : ℕ, f (q * b) = 0 := fun q => by
    have hpos : Int.fract (((q * b : ℕ) : ℝ) * (a : ℝ) / (b : ℝ)) = 0 := by
      rw [show (((q * b : ℕ) : ℝ) * (a : ℝ) / (b : ℝ)) = ((q * a : ℕ) : ℝ) by
        push_cast; field_simp [hb_pos.ne'], Int.fract_natCast]
    have hneg : Int.fract (-(((q * b : ℕ) : ℝ) * (a : ℝ) / (b : ℝ))) = 0 := by
      rw [show -(((q * b : ℕ) : ℝ) * (a : ℝ) / (b : ℝ)) = ((-(q * a : ℤ) : ℤ) : ℝ) by
        push_cast; field_simp [hb_pos.ne'], Int.fract_intCast]
    dsimp [f]; rw [hpos, hneg, sub_self, zero_div]
  change ∑ m ∈ Finset.Ico 1 (M * b), f m = cotApproxSum a b M
  rw [sum_Ico_eq_sum_Ico_sum_range f b M hb hf0]
  have hper_pos : ∀ q r : ℕ, Int.fract (((q * b + r : ℕ) : ℝ) * (a : ℝ) / (b : ℝ)) =
      Int.fract ((r : ℝ) * (a : ℝ) / (b : ℝ)) := fun q r => by
    rw [show ((q * b + r : ℕ) : ℝ) * (a : ℝ) / (b : ℝ) =
      (r : ℝ) * (a : ℝ) / (b : ℝ) + ((q * a : ℕ) : ℝ) by push_cast; field_simp [hb_pos.ne']; ring,
      Int.fract_add_natCast]
  have hper_neg : ∀ q r : ℕ, Int.fract (-(((q * b + r : ℕ) : ℝ) * (a : ℝ) / (b : ℝ))) =
      Int.fract (-((r : ℝ) * (a : ℝ) / (b : ℝ))) := fun q r => by
    rw [show -(((q * b + r : ℕ) : ℝ) * (a : ℝ) / (b : ℝ)) =
      -((r : ℝ) * (a : ℝ) / (b : ℝ)) + (-(q * a : ℤ) : ℤ) by
        push_cast; field_simp [hb_pos.ne']; ring, Int.fract_add_intCast]
  have hsplit_inner : ∀ r ∈ Finset.Ico 1 b, ∑ q ∈ Finset.range M, f (q * b + r) =
      Int.fract ((r : ℝ) * (a : ℝ) / (b : ℝ)) *
          ∑ q ∈ Finset.range M, (1 / ((q : ℝ) * (b : ℝ) + (r : ℝ))) -
        Int.fract (-((r : ℝ) * (a : ℝ) / (b : ℝ))) *
          ∑ q ∈ Finset.range M, (1 / ((q : ℝ) * (b : ℝ) + (r : ℝ))) := fun r _ => by
    have hsplit1 : ∀ q : ℕ, f (q * b + r) =
        Int.fract ((r : ℝ) * (a : ℝ) / (b : ℝ)) * (1 / ((q : ℝ) * (b : ℝ) + (r : ℝ))) -
        Int.fract (-((r : ℝ) * (a : ℝ) / (b : ℝ))) *
          (1 / ((q : ℝ) * (b : ℝ) + (r : ℝ))) := fun q => by
      dsimp [f]; rw [hper_pos, hper_neg, sub_div]; push_cast; ring
    simp_rw [hsplit1, Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [Finset.sum_congr rfl hsplit_inner, Finset.sum_sub_distrib]
  have hreflect :
      ∑ r ∈ Finset.Ico 1 b, Int.fract (-((r : ℝ) * (a : ℝ) / (b : ℝ))) *
          ∑ q ∈ Finset.range M, (1 / ((q : ℝ) * (b : ℝ) + (r : ℝ))) =
        ∑ r ∈ Finset.Ico 1 b, Int.fract ((r : ℝ) * (a : ℝ) / (b : ℝ)) *
          ∑ q ∈ Finset.range M, (1 / (((q + 1 : ℕ) : ℝ) * (b : ℝ) - (r : ℝ))) := by
    refine Finset.sum_bij (fun r _ => b - r)
      (fun r hr => by rw [Finset.mem_Ico] at hr ⊢; omega)
      (fun r₁ hr₁ r₂ hr₂ heq => by rw [Finset.mem_Ico] at hr₁ hr₂; omega)
      (fun r hr => by
        rw [Finset.mem_Ico] at hr; exact ⟨b - r, Finset.mem_Ico.mpr ⟨by omega, by omega⟩, by omega⟩)
      (fun r hr => ?_)
    have hr' := Finset.mem_Ico.mp hr
    have hbr : ((b - r : ℕ) : ℝ) = (b : ℝ) - (r : ℝ) := Nat.cast_sub hr'.2.le
    rw [show (((b - r : ℕ) : ℝ) * (a : ℝ) / (b : ℝ)) =
          -((r : ℝ) * (a : ℝ) / (b : ℝ)) + ((a : ℤ) : ℝ) by
          rw [hbr]; push_cast; field_simp [hb_pos.ne']; ring, Int.fract_add_intCast]
    congr 1; refine Finset.sum_congr rfl fun q _ => ?_; rw [hbr]; push_cast; ring_nf
  rw [hreflect, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun r _ => by rw [← mul_sub, ← Finset.sum_sub_distrib]

/-- Mittag-Leffler limit for each residue class `1 ≤ r < b` via `cot_series_rep'`. -/
theorem tendsto_cotApproxSum_term {b r : ℕ} (hr : 1 ≤ r) (hrb : r < b) :
    Tendsto (fun M : ℕ => ∑ q ∈ Finset.range M, (1 / ((q : ℝ) * (b : ℝ) + (r : ℝ)) -
        1 / (((q + 1 : ℕ) : ℝ) * (b : ℝ) - (r : ℝ)))) atTop
      (nhds ((Real.pi / (b : ℝ)) *
        (Real.cos (Real.pi * (r : ℝ) / (b : ℝ)) / Real.sin (Real.pi * (r : ℝ) / (b : ℝ))))) := by
  have hr_pos : (0 : ℝ) < (r : ℝ) := Nat.cast_pos.mpr hr
  have hb_pos : (0 : ℝ) < (b : ℝ) := Nat.cast_pos.mpr (lt_trans hr hrb)
  let x : ℂ := (r : ℂ) / (b : ℂ)
  have hx_mem : x ∈ Complex.integerComplement := by
    rintro ⟨n, hn⟩
    have hre : (n : ℝ) = (r : ℝ) / (b : ℝ) := by
      simpa [x, Complex.div_ofReal_re] using congr_arg Complex.re hn
    have hlt1 : (0 : ℝ) < (r : ℝ) / (b : ℝ) := div_pos hr_pos hb_pos
    have hlt2 : (r : ℝ) / (b : ℝ) < 1 := (div_lt_one hb_pos).mpr (by exact_mod_cast hrb)
    have hn0 : (0 : ℤ) < n := by exact_mod_cast hre ▸ hlt1
    have hn1 : n < (1 : ℤ) := by exact_mod_cast hre ▸ hlt2
    omega
  have h_sum_c := (summable_cotTerm hx_mem).hasSum.tendsto_sum_nat
  rw [← cot_series_rep' hx_mem] at h_sum_c
  have h_re_lim := Complex.reCLM.continuous.continuousAt.tendsto.comp h_sum_c
  have h_cot_re : ((Complex.reCLM : ℂ →L[ℝ] ℝ)
      ((Real.pi : ℂ) * Complex.cot ((Real.pi : ℂ) * x) - 1 / x)) / (b : ℝ) =
      (Real.pi / (b : ℝ)) *
        (Real.cos (Real.pi * (r : ℝ) / (b : ℝ)) / Real.sin (Real.pi * (r : ℝ) / (b : ℝ))) -
        1 / (r : ℝ) := by
    have hdiv : (1 / x) = (((b : ℝ) / (r : ℝ) : ℝ) : ℂ) := by
      dsimp [x]; rw [one_div_div]; push_cast; rfl
    rw [Complex.reCLM_apply, Complex.sub_re,
      show ((Real.pi : ℂ) * x) = ((Real.pi * (r : ℝ) / (b : ℝ) : ℝ) : ℂ) by
        dsimp [x]; push_cast; ring,
      show Complex.cot ((Real.pi * (r : ℝ) / (b : ℝ) : ℝ) : ℂ) =
        ((Real.cos (Real.pi * (r : ℝ) / (b : ℝ)) /
          Real.sin (Real.pi * (r : ℝ) / (b : ℝ)) : ℝ) : ℂ) by
        rw [Complex.cot, ← Complex.ofReal_cos, ← Complex.ofReal_sin, Complex.ofReal_div],
      ← Complex.ofReal_mul, Complex.ofReal_re, hdiv, Complex.ofReal_re]
    field_simp [hb_pos.ne', hr_pos.ne']
  have h_re_div : Tendsto (fun N : ℕ => ((Complex.reCLM : ℂ →L[ℝ] ℝ)
        (∑ n ∈ Finset.range N, cotTerm x n)) / (b : ℝ)) atTop
      (nhds ((Real.pi / (b : ℝ)) * (Real.cos (Real.pi * (r : ℝ) / (b : ℝ)) /
        Real.sin (Real.pi * (r : ℝ) / (b : ℝ))) - 1 / (r : ℝ))) :=
    h_cot_re ▸ h_re_lim.div_const (b : ℝ)
  have h_sum_real : ∀ N : ℕ, ((Complex.reCLM : ℂ →L[ℝ] ℝ)
        (∑ n ∈ Finset.range N, cotTerm x n)) / (b : ℝ) =
      ∑ n ∈ Finset.range N, (1 / (((n + 1 : ℕ) : ℝ) * (b : ℝ) + (r : ℝ)) -
        1 / (((n + 1 : ℕ) : ℝ) * (b : ℝ) - (r : ℝ))) := fun N => by
    rw [map_sum, Finset.sum_div]
    refine Finset.sum_congr rfl fun n _ => ?_
    have hnb1 : ((n + 1 : ℕ) : ℝ) * (b : ℝ) + (r : ℝ) ≠ 0 := by positivity
    have hnb2 : ((n + 1 : ℕ) : ℝ) * (b : ℝ) - (r : ℝ) ≠ 0 := by
      have h1 : (r : ℝ) < (b : ℝ) := by exact_mod_cast hrb
      have h2 : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos n
      nlinarith
    have h_real_term : (1 / ((r : ℝ) / (b : ℝ) - ((n : ℝ) + 1)) +
        1 / ((r : ℝ) / (b : ℝ) + ((n : ℝ) + 1))) =
        (1 / (((n + 1 : ℕ) : ℝ) * (b : ℝ) + (r : ℝ)) -
          1 / (((n + 1 : ℕ) : ℝ) * (b : ℝ) - (r : ℝ))) * (b : ℝ) := by
      rw [show (r : ℝ) / (b : ℝ) - ((n : ℝ) + 1) =
          -((((n + 1 : ℕ) : ℝ) * (b : ℝ) - (r : ℝ)) / (b : ℝ)) by
          push_cast; field_simp [hb_pos.ne']; ring,
        show (r : ℝ) / (b : ℝ) + ((n : ℝ) + 1) =
          (((n + 1 : ℕ) : ℝ) * (b : ℝ) + (r : ℝ)) / (b : ℝ) by
          push_cast; field_simp [hb_pos.ne']; ring]
      field_simp [hb_pos.ne', hnb1, hnb2]; ring
    have hterm_c : cotTerm x n = ((((1 : ℝ) / (((n + 1 : ℕ) : ℝ) * (b : ℝ) + (r : ℝ)) -
        1 / (((n + 1 : ℕ) : ℝ) * (b : ℝ) - (r : ℝ))) * (b : ℝ) : ℝ) : ℂ) := by
      rw [← h_real_term]; dsimp [cotTerm, x]; push_cast; rfl
    rw [hterm_c, Complex.reCLM_apply, Complex.ofReal_re, mul_div_cancel_right₀ _ hb_pos.ne']
  have h_shifted : Tendsto
      (fun M : ℕ => 1 / (r : ℝ) + ∑ n ∈ Finset.range (M - 1),
        (1 / (((n + 1 : ℕ) : ℝ) * (b : ℝ) + (r : ℝ)) -
          1 / (((n + 1 : ℕ) : ℝ) * (b : ℝ) - (r : ℝ))))
      atTop (nhds ((Real.pi / (b : ℝ)) *
        (Real.cos (Real.pi * (r : ℝ) / (b : ℝ)) / Real.sin (Real.pi * (r : ℝ) / (b : ℝ))))) := by
    simpa [add_sub_cancel] using
      ((h_re_div.congr h_sum_real).comp (tendsto_sub_atTop_nat 1)).const_add (1 / (r : ℝ))
  have h_tail : Tendsto (fun M : ℕ => 1 / ((M : ℝ) * (b : ℝ) - (r : ℝ))) atTop (nhds 0) := by
    have h_top : Tendsto (fun M : ℕ => (M : ℝ) * (b : ℝ) - (r : ℝ)) atTop atTop := by
      rw [Filter.tendsto_atTop_atTop]
      intro B
      obtain ⟨M0, hM0⟩ := exists_nat_gt ((B + (r : ℝ)) / (b : ℝ))
      exact ⟨M0, fun M hM => by
        have : (M0 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
        nlinarith [(div_lt_iff₀ hb_pos).mp hM0]⟩
    simpa [Function.comp_def, one_div] using tendsto_inv_atTop_zero.comp h_top
  simpa only [sub_zero] using (h_shifted.sub h_tail).congr' (by
    filter_upwards [eventually_ge_atTop 1] with M hM
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hM
    simp only [Nat.add_sub_cancel]
    induction m with
    | zero => simp
    | succ k ih =>
      rw [Finset.sum_range_succ, Finset.sum_range_succ (n := k + 1), ← ih (Nat.succ_pos k)]
      push_cast; ring)

/-- Convergence of `cotApproxSum a b` to `(π / b) * vasyuninCotSum b a`. -/
theorem tendsto_cotApproxSum (a b : ℕ) :
    Tendsto (cotApproxSum a b) atTop (nhds ((Real.pi / (b : ℝ)) * vasyuninCotSum b a)) := by
  dsimp [cotApproxSum, vasyuninCotSum]
  rw [Finset.mul_sum]
  refine tendsto_finsetSum (Finset.Ico 1 b) fun r hr => ?_
  have hrb := Finset.mem_Ico.mp hr
  simpa [mul_left_comm, mul_assoc, mul_comm] using
    (tendsto_cotApproxSum_term hrb.1 hrb.2).const_mul (Int.fract ((r : ℝ) * (a : ℝ) / (b : ℝ)))
