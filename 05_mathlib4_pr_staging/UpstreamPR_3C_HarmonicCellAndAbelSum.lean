/-
Copyright (c) 2026 Qamar Munawer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qamar Munawer
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import RiemannBlueprint.UpstreamPRs.UpstreamPR_3B_VasyuninSmoothAndCotDefs
public import RiemannBlueprint.UpstreamPRs.UpstreamPR_3D_StirlingAndHarmonicAsymptotics

/-!
# Harmonic Cell Integrals and Discrete Abel Summation for Cross-Integrals

This file evaluates the unit-interval cross integral `intervalIntegral_recipFractScaled_mul_unit`
and performs discrete Abel summation on `Finset.Ico 1 (M * j * k)` to establish:
1. `sum_Ico_abel`: discrete summation by parts on `Finset.Ico 1 L`.
2. `abel_log_sum_exact`: Abel evaluation of `∑ (n / j) * (log (n + 1) - log n)`.
3. `abel_cross_sum_exact`: symmetric Abel evaluation of `(n / j) * (n / k) * (1/n - 1/(n+1))`.
4. `cross_partial_exact_identity`: exact partial cross-integral on `[1 / (M * j * k), 1]`.
-/

@[expose] public section

open MeasureTheory Set

private lemma intervalIntegral_recipFractScaled_mul_unit {j k n : ℕ}
    (hj : 1 ≤ j) (hk : 1 ≤ k) (hn : 1 ≤ n) :
    let p : ℝ := ((n / j : ℕ) : ℝ)
    let q : ℝ := ((n / k : ℕ) : ℝ)
    (∫ x in (1 / ((n : ℝ) + 1))..(1 / (n : ℝ)), recipFractScaled j x * recipFractScaled k x) =
      1 / ((j : ℝ) * (k : ℝ)) -
        (p / (k : ℝ) + q / (j : ℝ)) * (Real.log ((n : ℝ) + 1) - Real.log (n : ℝ)) +
        p * q * (1 / (n : ℝ) - 1 / ((n : ℝ) + 1)) := by
  intro p q
  have hj_pos : (0 : ℝ) < (j : ℝ) := Nat.cast_pos.mpr hj
  have hk_pos : (0 : ℝ) < (k : ℝ) := Nat.cast_pos.mpr hk
  have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
  have hle : 1 / ((n : ℝ) + 1) ≤ 1 / (n : ℝ) := one_div_le_one_div_of_le hn_pos (by linarith)
  have h_ae : (∫ x in (1 / ((n : ℝ) + 1))..(1 / (n : ℝ)),
        recipFractScaled j x * recipFractScaled k x) =
      ∫ x in (1 / ((n : ℝ) + 1))..(1 / (n : ℝ)),
        (1 / ((j : ℝ) * (k : ℝ) * x ^ 2) - (p / (k : ℝ) + q / (j : ℝ)) * (1 / x) + p * q) := by
    rw [intervalIntegral.integral_of_le hle, intervalIntegral.integral_of_le hle,
      integral_Ioc_eq_integral_Ioo, integral_Ioc_eq_integral_Ioo]
    refine setIntegral_congr_fun measurableSet_Ioo fun x hx => ?_
    rw [recipFractScaled_eq_of_mem_Ioo hj hn hx, recipFractScaled_eq_of_mem_Ioo hk hn hx]
    have hx_ne : x ≠ 0 := (lt_trans (by positivity) hx.1).ne'
    field_simp [hj_pos.ne', hk_pos.ne', hx_ne]; ring
  have h_deriv : ∀ x ∈ Set.uIcc (1 / ((n : ℝ) + 1)) (1 / (n : ℝ)),
      HasDerivAt (fun y : ℝ => -(1 : ℝ) / ((j : ℝ) * (k : ℝ) * y) -
          (p / (k : ℝ) + q / (j : ℝ)) * Real.log y + p * q * y)
        (1 / ((j : ℝ) * (k : ℝ) * x ^ 2) - (p / (k : ℝ) + q / (j : ℝ)) * (1 / x) + p * q) x := by
    intro x hx
    rw [Set.uIcc_of_le hle] at hx
    have hx_pos : 0 < x := lt_of_lt_of_le (by positivity) hx.1
    have h1 : HasDerivAt (fun y : ℝ => -(1 : ℝ) / ((j : ℝ) * (k : ℝ) * y))
        (1 / ((j : ℝ) * (k : ℝ) * x ^ 2)) x := by
      have hinv := (hasDerivAt_inv hx_pos.ne').const_mul (-(1 : ℝ) / ((j : ℝ) * (k : ℝ)))
      rw [show (fun y : ℝ => (-(1 : ℝ) / ((j : ℝ) * (k : ℝ))) * y⁻¹) =
        fun y : ℝ => -(1 : ℝ) / ((j : ℝ) * (k : ℝ) * y) by funext y; ring] at hinv
      convert hinv using 1; field_simp [hj_pos.ne', hk_pos.ne', hx_pos.ne']
    have h2 : HasDerivAt (fun y : ℝ => (p / (k : ℝ) + q / (j : ℝ)) * Real.log y)
        ((p / (k : ℝ) + q / (j : ℝ)) * (1 / x)) x := by
      simpa [one_div] using (Real.hasDerivAt_log hx_pos.ne').const_mul _
    exact (h1.sub h2).add (by simpa using (hasDerivAt_id' x).const_mul (p * q))
  have h_cont : ContinuousOn (fun x : ℝ => 1 / ((j : ℝ) * (k : ℝ) * x ^ 2) -
        (p / (k : ℝ) + q / (j : ℝ)) * (1 / x) + p * q)
      (Set.uIcc (1 / ((n : ℝ) + 1)) (1 / (n : ℝ))) := fun x hx => by
    rw [Set.uIcc_of_le hle] at hx
    have hx_pos : 0 < x := lt_of_lt_of_le (by positivity) hx.1
    have hjkx : (j : ℝ) * (k : ℝ) * x ^ 2 ≠ 0 :=
      mul_ne_zero (mul_ne_zero hj_pos.ne' hk_pos.ne') (pow_ne_zero 2 hx_pos.ne')
    exact (((continuousAt_const.div (continuousAt_const.mul (continuousAt_id.pow 2)) hjkx).sub
      (continuousAt_const.mul (continuousAt_const.div continuousAt_id hx_pos.ne'))).add
      continuousAt_const).continuousWithinAt
  rw [h_ae, intervalIntegral.integral_eq_sub_of_hasDerivAt h_deriv h_cont.intervalIntegrable,
    one_div, Real.log_inv, one_div, Real.log_inv]
  field_simp [hj_pos.ne', hk_pos.ne', hn_pos.ne', (by positivity : (n : ℝ) + 1 ≠ 0)]; ring

/-- Discrete Abel summation by parts on `Finset.Ico 1 L` for `a 0 = 0` and `1 ≤ L`. -/
theorem sum_Ico_abel (a b : ℕ → ℝ) (ha0 : a 0 = 0) {L : ℕ} (hL : 1 ≤ L) :
    ∑ n ∈ Finset.Ico 1 L, a n * (b (n + 1) - b n) =
      a (L - 1) * b L - ∑ n ∈ Finset.Ico 1 L, (a n - a (n - 1)) * b n := by
  induction L, hL using Nat.le_induction with
  | base => simp [ha0]
  | succ k hk ih =>
    rw [Finset.sum_Ico_succ_top hk, Finset.sum_Ico_succ_top hk, ih]
    simp only [Nat.add_sub_cancel]; ring

/-- Exact Abel summation evaluation of the logarithmic floor sum on `Finset.Ico 1 (M * j * k)`. -/
theorem abel_log_sum_exact {M j k : ℕ} (hM : 1 ≤ M) (hj : 1 ≤ j) (hk : 1 ≤ k) :
    (-(1 : ℝ) / (k : ℝ)) * ∑ n ∈ Finset.Ico 1 (M * j * k),
        ((n / j : ℕ) : ℝ) * (Real.log ((n : ℝ) + 1) - Real.log (n : ℝ)) =
      (Real.log ((Nat.factorial (M * k) : ℕ) : ℝ) -
        (M * k : ℝ) * Real.log ((M * k : ℕ) : ℝ)) / (k : ℝ) := by
  have hj_pos : (0 : ℝ) < (j : ℝ) := Nat.cast_pos.mpr hj
  have hk_pos : (0 : ℝ) < (k : ℝ) := Nat.cast_pos.mpr hk
  have hM_pos : (0 : ℝ) < (M : ℝ) := Nat.cast_pos.mpr hM
  have hL : 1 ≤ M * j * k := Nat.mul_pos (Nat.mul_pos hM hj) hk
  have hMk : 1 ≤ M * k := Nat.mul_pos hM hk
  have h_top_j : (M * j * k - 1) / j = M * k - 1 := by
    rw [show M * j * k = j * (M * k) by ring]; exact mul_sub_one_div hj hMk
  rw [show ∑ n ∈ Finset.Ico 1 (M * j * k),
        ((n / j : ℕ) : ℝ) * (Real.log ((n : ℝ) + 1) - Real.log (n : ℝ)) =
      ∑ n ∈ Finset.Ico 1 (M * j * k),
        ((n / j : ℕ) : ℝ) * (Real.log (((n + 1 : ℕ) : ℝ)) - Real.log (n : ℝ)) from
      Finset.sum_congr rfl fun _ _ => by push_cast; rfl,
    sum_Ico_abel (fun n => ((n / j : ℕ) : ℝ)) (fun n => Real.log (n : ℝ)) (by simp) hL, h_top_j]
  have h_diff_congr : ∑ n ∈ Finset.Ico 1 (M * j * k),
      (((n / j : ℕ) : ℝ) - (((n - 1) / j : ℕ) : ℝ)) * Real.log (n : ℝ) =
      ∑ n ∈ Finset.Ico 1 (j * (M * k)), if j ∣ n then Real.log (n : ℝ) else 0 := by
    rw [show M * j * k = j * (M * k) by ring]
    refine Finset.sum_congr rfl fun n hn => ?_
    rw [nat_div_sub_pred_div hj (Finset.mem_Ico.mp hn).1]; split_ifs <;> simp
  have h_log_prod : ∀ A : ℕ, 1 ≤ A → ∑ m ∈ Finset.Ico 1 A, Real.log ((m * j : ℕ) : ℝ) =
      ((A : ℝ) - 1) * Real.log (j : ℝ) + Real.log ((Nat.factorial (A - 1) : ℕ) : ℝ) := by
    intro A hA
    induction A, hA using Nat.le_induction with
    | base => simp
    | succ t ht ih =>
      rw [Finset.sum_Ico_succ_top ht, ih, Nat.add_sub_cancel]
      have ht_pos : (0 : ℝ) < (t : ℝ) := Nat.cast_pos.mpr ht
      have hfact_eq : ((Nat.factorial t : ℕ) : ℝ) =
          (t : ℝ) * ((Nat.factorial (t - 1) : ℕ) : ℝ) := by
        exact_mod_cast (Nat.mul_factorial_pred (by omega : t ≠ 0)).symm
      rw [Nat.cast_mul, Real.log_mul ht_pos.ne' hj_pos.ne', hfact_eq,
        Real.log_mul ht_pos.ne' (Nat.cast_pos.mpr (Nat.factorial_pos (t - 1))).ne']
      push_cast; ring
  rw [h_diff_congr, sum_Ico_ite_dvd (fun n => Real.log (n : ℝ)) hj hMk, h_log_prod (M * k) hMk]
  have hMk_pos : (0 : ℝ) < ((M * k : ℕ) : ℝ) := Nat.cast_pos.mpr hMk
  have hfact_top : ((Nat.factorial (M * k) : ℕ) : ℝ) =
      ((M * k : ℕ) : ℝ) * ((Nat.factorial (M * k - 1) : ℕ) : ℝ) := by
    exact_mod_cast (Nat.mul_factorial_pred (by omega : M * k ≠ 0)).symm
  rw [hfact_top, Real.log_mul hMk_pos.ne' (Nat.cast_pos.mpr (Nat.factorial_pos _)).ne',
    Nat.cast_sub hMk, Nat.cast_one, show Real.log ((M * j * k : ℕ) : ℝ) =
      Real.log ((M : ℝ) * (k : ℝ)) + Real.log (j : ℝ) by
      push_cast
      rw [show (M : ℝ) * (j : ℝ) * (k : ℝ) = ((M : ℝ) * (k : ℝ)) * (j : ℝ) by ring,
        Real.log_mul (mul_pos hM_pos hk_pos).ne' hj_pos.ne']]
  push_cast; ring

/-- Symmetric Abel summation of the discrete cross term `(n / j) * (n / k) * (1/n - 1/(n+1))`. -/
theorem abel_cross_sum_exact {M j k : ℕ} (hM : 1 ≤ M) (hj : 1 ≤ j) (hk : 1 ≤ k) :
    ∑ n ∈ Finset.Ico 1 (M * j * k),
        ((n / j : ℕ) : ℝ) * ((n / k : ℕ) : ℝ) * (1 / (n : ℝ) - 1 / ((n : ℝ) + 1)) =
      -((M : ℝ) * (k : ℝ) - 1) * ((M : ℝ) * (j : ℝ) - 1) / ((M : ℝ) * (j : ℝ) * (k : ℝ)) +
        ((M : ℝ) - 1 / (k : ℝ) - (1 / (2 * (j : ℝ))) *
          ∑ m ∈ Finset.Ico 1 (M * k), (1 : ℝ) / (m : ℝ) -
          (1 / (2 * (j : ℝ))) * ∑ m ∈ Finset.Ico 1 (M * k), (Int.fract ((m : ℝ) * j / k) -
            Int.fract (-((m : ℝ) * j / k))) / (m : ℝ)) +
        ((M : ℝ) - 1 / (j : ℝ) - (1 / (2 * (k : ℝ))) *
          ∑ m ∈ Finset.Ico 1 (M * j), (1 : ℝ) / (m : ℝ) -
          (1 / (2 * (k : ℝ))) * ∑ m ∈ Finset.Ico 1 (M * j), (Int.fract ((m : ℝ) * k / j) -
            Int.fract (-((m : ℝ) * k / j))) / (m : ℝ)) := by
  have hL : 1 ≤ M * j * k := Nat.mul_pos (Nat.mul_pos hM hj) hk
  have hMk : 1 ≤ M * k := Nat.mul_pos hM hk
  have hMj : 1 ≤ M * j := Nat.mul_pos hM hj
  have h_top_j : (M * j * k - 1) / j = M * k - 1 := by
    rw [show M * j * k = j * (M * k) by ring]; exact mul_sub_one_div hj hMk
  have h_top_k : (M * j * k - 1) / k = M * j - 1 := by
    rw [show M * j * k = k * (M * j) by ring]; exact mul_sub_one_div hk hMj
  rw [show ∑ n ∈ Finset.Ico 1 (M * j * k),
        ((n / j : ℕ) : ℝ) * ((n / k : ℕ) : ℝ) * (1 / (n : ℝ) - 1 / ((n : ℝ) + 1)) =
      ∑ n ∈ Finset.Ico 1 (M * j * k), ((n / j : ℕ) : ℝ) * ((n / k : ℕ) : ℝ) *
        (-(1 : ℝ) / ((n + 1 : ℕ) : ℝ) - -(1 : ℝ) / (n : ℝ)) from
      Finset.sum_congr rfl fun _ _ => by push_cast; ring,
    sum_Ico_abel (fun n => ((n / j : ℕ) : ℝ) * ((n / k : ℕ) : ℝ))
      (fun n => -(1 : ℝ) / (n : ℝ)) (by simp) hL, h_top_j, h_top_k]
  have h_symm : -∑ n ∈ Finset.Ico 1 (M * j * k),
      (((n / j : ℕ) : ℝ) * ((n / k : ℕ) : ℝ) -
        (((n - 1) / j : ℕ) : ℝ) * (((n - 1) / k : ℕ) : ℝ)) * (-(1 : ℝ) / (n : ℝ)) =
      (∑ n ∈ Finset.Ico 1 (j * (M * k)),
        if j ∣ n then (((n / k : ℕ) : ℝ) + (((n - 1) / k : ℕ) : ℝ)) / (2 * (n : ℝ)) else 0) +
      (∑ n ∈ Finset.Ico 1 (k * (M * j)),
        if k ∣ n then (((n / j : ℕ) : ℝ) + (((n - 1) / j : ℕ) : ℝ)) / (2 * (n : ℝ)) else 0) := by
    rw [show j * (M * k) = M * j * k by ring, show k * (M * j) = M * j * k by ring,
      ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun n hn => ?_
    have hn1 : 1 ≤ n := (Finset.mem_Ico.mp hn).1
    let p := ((n / j : ℕ) : ℝ); let p' := (((n - 1) / j : ℕ) : ℝ)
    let q := ((n / k : ℕ) : ℝ); let q' := (((n - 1) / k : ℕ) : ℝ)
    have hid : 2 * (p * q - p' * q') = (p - p') * (q + q') + (q - q') * (p + p') := by ring
    rw [nat_div_sub_pred_div hj hn1, nat_div_sub_pred_div hk hn1] at hid
    split_ifs at hid ⊢ <;> field_simp [(Nat.cast_pos.mpr hn1).ne'] at hid ⊢ <;> linarith
  rw [sub_eq_add_neg, h_symm, sum_Ico_ite_dvd _ hj hMk, sum_Ico_ite_dvd _ hk hMj,
    show ∑ m ∈ Finset.Ico 1 (M * k),
      ((((m * j) / k : ℕ) : ℝ) + (((m * j - 1) / k : ℕ) : ℝ)) / (2 * ((m * j : ℕ) : ℝ)) =
      ∑ m ∈ Finset.Ico 1 (M * k), (((m * j / k : ℕ) : ℝ) + (((m * j - 1) / k : ℕ) : ℝ)) /
        (2 * (m : ℝ) * (j : ℝ)) from Finset.sum_congr rfl fun _ _ => by push_cast; ring,
    show ∑ m ∈ Finset.Ico 1 (M * j),
      ((((m * k) / j : ℕ) : ℝ) + (((m * k - 1) / j : ℕ) : ℝ)) / (2 * ((m * k : ℕ) : ℝ)) =
      ∑ m ∈ Finset.Ico 1 (M * j), (((m * k / j : ℕ) : ℝ) + (((m * k - 1) / j : ℕ) : ℝ)) /
        (2 * (m : ℝ) * (k : ℝ)) from Finset.sum_congr rfl fun _ _ => by push_cast; ring,
    halfSum_exact hj hk hM, halfSum_exact hk hj hM, Nat.cast_sub hMk, Nat.cast_sub hMj]
  push_cast; ring

/-- Exact identity for the truncated cross-integral on `[1 / (M * j * k), 1]`. -/
theorem cross_partial_exact_identity {M j k : ℕ} (hM : 1 ≤ M) (hj : 1 ≤ j) (hk : 1 ≤ k) :
    (∫ x in (1 / ((M * j * k : ℕ) : ℝ))..1, recipFractScaled j x * recipFractScaled k x) =
      (1 / (k : ℝ)) * (Real.log ((Nat.factorial (M * k) : ℕ) : ℝ) -
        (M * k : ℝ) * Real.log ((M * k : ℕ) : ℝ) + (M * k : ℝ) -
        (1 / 2 : ℝ) * Real.log ((M * k : ℕ) : ℝ)) +
      (1 / (j : ℝ)) * (Real.log ((Nat.factorial (M * j) : ℕ) : ℝ) -
        (M * j : ℝ) * Real.log ((M * j : ℕ) : ℝ) + (M * j : ℝ) -
        (1 / 2 : ℝ) * Real.log ((M * j : ℕ) : ℝ)) -
      (1 / (2 * (j : ℝ))) * ((∑ m ∈ Finset.Ico 1 (M * k), (1 : ℝ) / m) - Real.log (M * k : ℕ)) -
      (1 / (2 * (k : ℝ))) * ((∑ m ∈ Finset.Ico 1 (M * j), (1 : ℝ) / m) - Real.log (M * j : ℕ)) +
      (((j : ℝ) - (k : ℝ)) * Real.log ((k : ℝ) / (j : ℝ)) - 2) / (2 * (j : ℝ) * (k : ℝ)) -
      1 / ((M : ℝ) * (j : ℝ) * (k : ℝ)) -
      (1 / (2 * (j : ℝ))) * ∑ m ∈ Finset.Ico 1 (M * k),
        (Int.fract ((m : ℝ) * j / k) - Int.fract (-((m : ℝ) * j / k))) / m -
      (1 / (2 * (k : ℝ))) * ∑ m ∈ Finset.Ico 1 (M * j),
        (Int.fract ((m : ℝ) * k / j) - Int.fract (-((m : ℝ) * k / j))) / m := by
  have hj_pos : (0 : ℝ) < (j : ℝ) := Nat.cast_pos.mpr hj
  have hk_pos : (0 : ℝ) < (k : ℝ) := Nat.cast_pos.mpr hk
  have hM_pos : (0 : ℝ) < (M : ℝ) := Nat.cast_pos.mpr hM
  have hL : 1 ≤ M * j * k := Nat.mul_pos (Nat.mul_pos hM hj) hk
  rw [intervalIntegral_split_recip (fun x => recipFractScaled j x * recipFractScaled k x)
    (intervalIntegrable_recipFractScaled_mul j k) (M * j * k) hL,
    Finset.sum_congr rfl fun n hn => intervalIntegral_recipFractScaled_mul_unit hj hk
      (Finset.mem_Ico.mp hn).1, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  have hS1 : ∑ _n ∈ Finset.Ico 1 (M * j * k), (1 : ℝ) / ((j : ℝ) * (k : ℝ)) =
      (M : ℝ) - 1 / ((j : ℝ) * (k : ℝ)) := by
    rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul, Nat.cast_sub hL, Nat.cast_one]
    push_cast; field_simp [hj_pos.ne', hk_pos.ne']
  have hS2 : ∑ n ∈ Finset.Ico 1 (M * j * k), (((n / j : ℕ) : ℝ) / k + ((n / k : ℕ) : ℝ) / j) *
        (Real.log ((n : ℝ) + 1) - Real.log n) =
      (1 / k) * ∑ n ∈ Finset.Ico 1 (M * j * k),
        ((n / j : ℕ) : ℝ) * (Real.log (n + 1) - Real.log n) +
      (1 / j) * ∑ n ∈ Finset.Ico 1 (M * j * k),
        ((n / k : ℕ) : ℝ) * (Real.log (n + 1) - Real.log n) := by
    have hsplit_s2 : ∀ n : ℕ, (((n / j : ℕ) : ℝ) / k + ((n / k : ℕ) : ℝ) / j) *
          (Real.log ((n : ℝ) + 1) - Real.log n) =
        (1 / k) * (((n / j : ℕ) : ℝ) * (Real.log (n + 1) - Real.log n)) +
        (1 / j) * (((n / k : ℕ) : ℝ) * (Real.log (n + 1) - Real.log n)) := fun _ => by ring
    simp_rw [hsplit_s2, Finset.sum_add_distrib, ← Finset.mul_sum]
  have ha1_pos : (1 / k) * ∑ n ∈ Finset.Ico 1 (M * j * k),
      ((n / j : ℕ) : ℝ) * (Real.log (n + 1) - Real.log n) =
      -((Real.log (Nat.factorial (M * k) : ℕ) - (M * k : ℝ) * Real.log (M * k : ℕ)) / k) := by
    rw [← abel_log_sum_exact hM hj hk]; ring
  have ha2_pos : (1 / j) * ∑ n ∈ Finset.Ico 1 (M * j * k),
      ((n / k : ℕ) : ℝ) * (Real.log (n + 1) - Real.log n) =
      -((Real.log (Nat.factorial (M * j) : ℕ) - (M * j : ℝ) * Real.log (M * j : ℕ)) / j) := by
    have ha2 := abel_log_sum_exact hM hk hj
    rw [show M * k * j = M * j * k by ring] at ha2
    rw [← ha2]; ring
  rw [hS1, hS2, ha1_pos, ha2_pos, abel_cross_sum_exact hM hj hk, Real.log_div hk_pos.ne' hj_pos.ne']
  have h_log_cancel : (1 / k) * ((1 / 2 : ℝ) * Real.log (M * k : ℕ)) +
        (1 / j) * ((1 / 2 : ℝ) * Real.log (M * j : ℕ)) -
        (1 / (2 * j)) * Real.log (M * k : ℕ) - (1 / (2 * k)) * Real.log (M * j : ℕ) -
        2 / (2 * j * k) =
      (((j : ℝ) - k) * (Real.log k - Real.log j) - 2) / (2 * j * k) := by
    rw [show Real.log (M * k : ℕ) = Real.log M + Real.log k by
        push_cast; exact Real.log_mul hM_pos.ne' hk_pos.ne',
      show Real.log (M * j : ℕ) = Real.log M + Real.log j by
        push_cast; exact Real.log_mul hM_pos.ne' hj_pos.ne']
    field_simp [hj_pos.ne', hk_pos.ne']; ring
  rw [← h_log_cancel]; field_simp [hM_pos.ne', hj_pos.ne', hk_pos.ne']; ring
