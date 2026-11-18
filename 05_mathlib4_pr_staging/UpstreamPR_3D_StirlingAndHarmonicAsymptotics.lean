/-
Copyright (c) 2026 Qamar Munawer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qamar Munawer
-/
module

public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.SpecialFunctions.Stirling
public import Mathlib.NumberTheory.Harmonic.EulerMascheroni
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-!
# Stirling Logarithm, Harmonic Asymptotics, and Discrete Divisor Floor Identities

This file isolates the classical asymptotic limits and discrete divisor/harmonic sum identities
used in Vasyunin's cross-integral:
1. `tendsto_stirling_log_term`: Stirling factorial log asymptotics along `M * k`.
2. `tendsto_harmonic_Ico_sub_log`: dilated Euler–Mascheroni harmonic asymptotics along `M * b`.
3. `mul_sub_one_div`, `nat_div_sub_pred_div`, `sum_Ico_ite_dvd`, `nat_div_add_pred_div_identity`,
   and `halfSum_exact`: discrete quotient-step and antisymmetric fractional-part harmonic sums.
-/

@[expose] public section

open Filter

private lemma tendsto_mul_nat_atTop {k : ℕ} (hk : 1 ≤ k) :
    Tendsto (fun M : ℕ => M * k) atTop atTop :=
  Filter.tendsto_atTop_atTop.mpr fun N =>
    ⟨N, fun M hM => le_trans hM (Nat.le_mul_of_pos_right M hk)⟩

/-- Stirling factorial logarithm limit along dilated multiples `M * k` (`1 ≤ k`). -/
theorem tendsto_stirling_log_term {k : ℕ} (hk : 1 ≤ k) :
    Tendsto (fun M : ℕ =>
        Real.log ((Nat.factorial (M * k) : ℕ) : ℝ) -
          (M * k : ℝ) * Real.log ((M * k : ℕ) : ℝ) + (M * k : ℝ) -
          (1 / 2 : ℝ) * Real.log ((M * k : ℕ) : ℝ))
      atTop (nhds ((1 / 2 : ℝ) * Real.log (2 * Real.pi))) := by
  have h_log_st : Tendsto (fun n : ℕ => Real.log (Stirling.stirlingSeq n))
      atTop (nhds (Real.log √Real.pi)) :=
    (Real.continuousAt_log (Real.sqrt_pos.mpr Real.pi_pos).ne').tendsto.comp
      Stirling.tendsto_stirlingSeq_sqrt_pi
  have h_lim_eq : Real.log √Real.pi + (1 / 2 : ℝ) * Real.log 2 =
      (1 / 2 : ℝ) * Real.log (2 * Real.pi) := by
    rw [Real.sqrt_eq_rpow, Real.log_rpow Real.pi_pos, Real.log_mul (by norm_num) Real.pi_pos.ne']
    ring
  rw [← h_lim_eq]
  refine ((h_log_st.comp (tendsto_mul_nat_atTop hk)).add tendsto_const_nhds).congr' ?_
  filter_upwards [eventually_ge_atTop 1] with M hM
  have hMk : 1 ≤ M * k := Nat.mul_pos hM hk
  have hMk_pos : (0 : ℝ) < ((M * k : ℕ) : ℝ) := Nat.cast_pos.mpr hMk
  dsimp [Function.comp_def, Stirling.stirlingSeq]
  have hfact_pos : (0 : ℝ) < ((Nat.factorial (M * k) : ℕ) : ℝ) :=
    Nat.cast_pos.mpr (Nat.factorial_pos _)
  have hden_pos :
      (0 : ℝ) < √(2 * ((M * k : ℕ) : ℝ)) * (((M * k : ℕ) : ℝ) / Real.exp 1) ^ (M * k) :=
    mul_pos (Real.sqrt_pos.mpr (by positivity)) (pow_pos (div_pos hMk_pos (Real.exp_pos 1)) _)
  rw [Real.log_div hfact_pos.ne' hden_pos.ne',
    Real.log_mul (Real.sqrt_pos.mpr (by positivity)).ne'
      (pow_pos (div_pos hMk_pos (Real.exp_pos 1)) _).ne',
    Real.log_pow, Real.log_div hMk_pos.ne' (Real.exp_pos 1).ne', Real.log_exp,
    Real.sqrt_eq_rpow, Real.log_rpow (by positivity : 0 < 2 * ((M * k : ℕ) : ℝ)),
    Real.log_mul (by norm_num) hMk_pos.ne']
  push_cast
  ring

private lemma harmonic_eq_sum_Icc (N : ℕ) :
    (harmonic N : ℝ) = ∑ m ∈ Finset.Icc 1 N, (1 : ℝ) / (m : ℝ) := by
  induction N with
  | zero => simp [harmonic_zero]
  | succ n ih =>
    rw [Finset.sum_Icc_succ_top (Nat.succ_pos n), harmonic_succ, Rat.cast_add, ih]
    simp [one_div]

/-- Dilated Euler–Mascheroni harmonic asymptotics: along `M * b` (`1 ≤ b`),
`∑ m ∈ Finset.Ico 1 (M * b), (1 : ℝ) / m - log (M * b) → γ`. -/
theorem tendsto_harmonic_Ico_sub_log {b : ℕ} (hb : 1 ≤ b) :
    Tendsto (fun M : ℕ =>
        (∑ m ∈ Finset.Ico 1 (M * b), (1 : ℝ) / (m : ℝ)) - Real.log ((M * b : ℕ) : ℝ))
      atTop (nhds Real.eulerMascheroniConstant) := by
  have ht := Real.tendsto_eulerMascheroniSeq'.comp (tendsto_mul_nat_atTop hb)
  have h0 : Tendsto (fun M : ℕ => (1 : ℝ) / ((M * b : ℕ) : ℝ)) atTop (nhds 0) := by
    simpa [Function.comp_def, one_div] using
      tendsto_inv_atTop_zero.comp
        ((tendsto_natCast_atTop_atTop (R := ℝ)).comp (tendsto_mul_nat_atTop hb))
  simpa only [sub_zero] using (ht.sub h0).congr' (by
    filter_upwards [eventually_ge_atTop 1] with M hM
    have hMb : 1 ≤ M * b := Nat.mul_pos hM hb
    have hMb_ne : M * b ≠ 0 := by omega
    dsimp [Function.comp_def, Real.eulerMascheroniSeq']
    rw [harmonic_eq_sum_Icc, ← Finset.Ico_succ_right_eq_Icc]
    simp only [hMb_ne, ↓reduceIte]
    have hsplit : Finset.Ico 1 (Order.succ (M * b)) = insert (M * b) (Finset.Ico 1 (M * b)) := by
      ext m; simp [Finset.mem_Ico]; omega
    rw [hsplit, Finset.sum_insert (by simp [Finset.mem_Ico])]
    ring)

/-- Exact quotient predecessor at a multiple: `(a * b - 1) / a = b - 1` for `1 ≤ a, b`. -/
theorem mul_sub_one_div {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) :
    (a * b - 1) / a = b - 1 := by
  have h : a * b - 1 = a * (b - 1) + (a - 1) := by
    calc a * b - 1 = a * (b - 1 + 1) - 1 := by congr 2; omega
      _ = a * (b - 1) + a - 1 := by rw [mul_add, mul_one]
      _ = a * (b - 1) + (a - 1) := by omega
  rw [h, Nat.mul_add_div ha, Nat.div_eq_of_lt (by omega : a - 1 < a), add_zero]

/-- Indicator jump of `⌊n / j⌋ - ⌊(n - 1) / j⌋` on `1 ≤ j, n`. -/
theorem nat_div_sub_pred_div {j n : ℕ} (hj : 1 ≤ j) (hn : 1 ≤ n) :
    ((n / j : ℕ) : ℝ) - (((n - 1) / j : ℕ) : ℝ) = if j ∣ n then 1 else 0 := by
  by_cases hdvd : j ∣ n
  · rcases hdvd with ⟨m, rfl⟩
    have hm : 1 ≤ m := Nat.pos_of_ne_zero fun h0 => by simp [h0] at hn
    rw [Nat.mul_div_right m hj, mul_sub_one_div hj hm, Nat.cast_sub hm, Nat.cast_one]; simp
  · have hmod : 1 ≤ n % j := Nat.pos_of_ne_zero fun h0 => hdvd (Nat.dvd_of_mod_eq_zero h0)
    have hmlt : n % j < j := Nat.mod_lt n hj
    have hpred : n - 1 = j * (n / j) + (n % j - 1) := by
      conv_lhs => rw [(Nat.div_add_mod n j).symm]
      exact Nat.add_sub_assoc hmod (j * (n / j))
    rw [hpred, Nat.mul_add_div hj, Nat.div_eq_of_lt (by omega : n % j - 1 < j), add_zero, sub_self]
    simp [hdvd]

/-- Re-indexing a divisibility-filtered sum on `Finset.Ico 1 (a * B)` onto `Finset.Ico 1 B`. -/
theorem sum_Ico_ite_dvd (g : ℕ → ℝ) {a B : ℕ} (ha : 1 ≤ a) (_hB : 1 ≤ B) :
    ∑ n ∈ Finset.Ico 1 (a * B), (if a ∣ n then g n else 0) =
      ∑ m ∈ Finset.Ico 1 B, g (m * a) := by
  rw [← Finset.sum_filter]
  exact Finset.sum_bij (fun n _ => n / a)
    (fun n hn => by
      obtain ⟨hI, hd⟩ := Finset.mem_filter.mp hn
      rw [Finset.mem_Ico] at hI ⊢
      exact ⟨Nat.div_pos (Nat.le_of_dvd hI.1 hd) ha,
        (Nat.div_lt_iff_lt_mul ha).mpr (by rw [mul_comm]; exact hI.2)⟩)
    (fun x hx y hy hxy => by
      have hx' := (Finset.mem_filter.mp hx).2
      have hy' := (Finset.mem_filter.mp hy).2
      have := congrArg (· * a) hxy
      rwa [Nat.div_mul_cancel hx', Nat.div_mul_cancel hy'] at this)
    (fun m hm => by
      rw [Finset.mem_Ico] at hm
      exact ⟨m * a, Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨Nat.mul_pos hm.1 ha,
        by rw [mul_comm a B]; exact Nat.mul_lt_mul_of_pos_right hm.2 ha⟩, dvd_mul_left a m⟩,
        Nat.mul_div_cancel m ha⟩)
    (fun n hn => by rw [(Finset.mem_filter.mp hn).2 |> Nat.div_mul_cancel])

/-- Antisymmetric fractional-part identity relating `⌊n / b⌋ + ⌊(n - 1) / b⌋` to
`{n / b} - {-(n / b)}`. -/
theorem nat_div_add_pred_div_identity {n b : ℕ} (hn : 1 ≤ n) (hb : 1 ≤ b) :
    ((n / b : ℕ) : ℝ) + (((n - 1) / b : ℕ) : ℝ) =
      2 * ((n : ℝ) / (b : ℝ)) - 1 -
        (Int.fract ((n : ℝ) / (b : ℝ)) - Int.fract (-(n : ℝ) / (b : ℝ))) := by
  have hb_pos : (0 : ℝ) < (b : ℝ) := Nat.cast_pos.mpr hb
  by_cases hdvd : b ∣ n
  · rcases hdvd with ⟨q, rfl⟩
    have hq : 1 ≤ q := Nat.pos_of_ne_zero fun h0 => by simp [h0] at hn
    rw [Nat.mul_div_right q hb, mul_sub_one_div hb hq, Nat.cast_mul, mul_div_cancel_left₀ _
      hb_pos.ne', Int.fract_natCast, show -((b : ℝ) * (q : ℝ)) / (b : ℝ) =
      ((-(q : ℤ) : ℤ) : ℝ) by field_simp [hb_pos.ne']; push_cast; ring, Int.fract_intCast,
      Nat.cast_sub hq]
    push_cast; ring
  · have hmod_pos : 1 ≤ n % b := Nat.pos_of_ne_zero fun h0 => hdvd (Nat.dvd_of_mod_eq_zero h0)
    have hmlt : n % b < b := Nat.mod_lt n hb
    let q : ℕ := n / b; let r : ℕ := n % b
    have hdiv : n = b * q + r := (Nat.div_add_mod n b).symm
    have h2 : (n - 1) / b = q := by
      rw [show n - 1 = b * q + (r - 1) by omega, Nat.mul_add_div hb,
        Nat.div_eq_of_lt (by omega : r - 1 < b), add_zero]
    have hr_pos : (0 : ℝ) < (r : ℝ) := Nat.cast_pos.mpr hmod_pos
    have hr_lt : (r : ℝ) < (b : ℝ) := by exact_mod_cast hmlt
    have h_pos_div : (n : ℝ) / (b : ℝ) = (q : ℝ) + (r : ℝ) / (b : ℝ) := by
      rw [hdiv]; push_cast; field_simp [hb_pos.ne']
    have hf1 : Int.fract ((n : ℝ) / (b : ℝ)) = (r : ℝ) / (b : ℝ) := by
      rw [h_pos_div, add_comm, Int.fract_add_natCast, Int.fract_eq_self]
      exact ⟨by positivity, (div_lt_one hb_pos).mpr hr_lt⟩
    have hf2 : Int.fract (-(n : ℝ) / (b : ℝ)) = ((b : ℝ) - (r : ℝ)) / (b : ℝ) := by
      rw [show -(n : ℝ) / (b : ℝ) = ((b : ℝ) - (r : ℝ)) / (b : ℝ) + (-(q + 1 : ℤ) : ℤ) by
          rw [hdiv]; push_cast; field_simp [hb_pos.ne']; ring,
        Int.fract_add_intCast, Int.fract_eq_self]
      exact ⟨div_nonneg (by linarith) hb_pos.le, (div_lt_one hb_pos).mpr (by linarith)⟩
    rw [h2, hf1, hf2, h_pos_div]; change (q : ℝ) + (q : ℝ) = _; field_simp [hb_pos.ne']; ring

/-- Exact decomposition of the averaged quotient sum `halfSum` into harmonic and antisymmetric
fractional-part harmonic sums on `Finset.Ico 1 (M * b)`. -/
theorem halfSum_exact {a b M : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) (hM : 1 ≤ M) :
    ∑ m ∈ Finset.Ico 1 (M * b),
        (((m * a / b : ℕ) : ℝ) + (((m * a - 1) / b : ℕ) : ℝ)) / (2 * (m : ℝ) * (a : ℝ)) =
      (M : ℝ) - 1 / (b : ℝ) -
        (1 / (2 * (a : ℝ))) * ∑ m ∈ Finset.Ico 1 (M * b), (1 : ℝ) / (m : ℝ) -
        (1 / (2 * (a : ℝ))) * ∑ m ∈ Finset.Ico 1 (M * b),
          (Int.fract ((m : ℝ) * (a : ℝ) / (b : ℝ)) -
            Int.fract (-((m : ℝ) * (a : ℝ) / (b : ℝ)))) / (m : ℝ) := by
  have ha_pos : (0 : ℝ) < (a : ℝ) := Nat.cast_pos.mpr ha
  have hb_pos : (0 : ℝ) < (b : ℝ) := Nat.cast_pos.mpr hb
  have hpt : ∀ m ∈ Finset.Ico 1 (M * b),
      (((m * a / b : ℕ) : ℝ) + (((m * a - 1) / b : ℕ) : ℝ)) / (2 * (m : ℝ) * (a : ℝ)) =
        (1 / (b : ℝ) - 1 / (2 * (a : ℝ)) * (1 / (m : ℝ))) -
          (1 / (2 * (a : ℝ))) * ((Int.fract ((m : ℝ) * (a : ℝ) / (b : ℝ)) -
            Int.fract (-((m : ℝ) * (a : ℝ) / (b : ℝ)))) / (m : ℝ)) := fun m hm => by
    have hm_pos : 1 ≤ m := (Finset.mem_Ico.mp hm).1
    have hid := nat_div_add_pred_div_identity (Nat.mul_pos hm_pos ha) hb
    push_cast at hid; rw [hid]
    field_simp [ha_pos.ne', hb_pos.ne', (Nat.cast_pos.mpr hm_pos).ne']
  rw [Finset.sum_congr rfl hpt, Finset.sum_sub_distrib, Finset.sum_sub_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_const, Nat.card_Ico, nsmul_eq_mul,
    Nat.cast_sub (Nat.mul_pos hM hb), Nat.cast_one]
  push_cast; field_simp [hb_pos.ne']
