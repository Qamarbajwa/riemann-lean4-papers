/-
Copyright (c) 2026 Qamar Munawer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qamar Munawer
-/
module

public import RiemannBlueprint.UpstreamPRs.UpstreamPR_8M_PointwiseContinuityAndPeriodicity

/-!
# Prime-Harmonic Cell Plateaus, Palindromic Mirror Cells, and Selberg Mobius Bridge

This module proves:
* `rawSelbergMobiusWeight_one`, `rawSelbergMobiusWeight_succ_self`: exact normalization at
  `k = 1` and horizon vanishing at `k = N + 1` (`1 ≤ N`).
* `filter_dvd_prime_eq_pair`, `divisorStepJump_prime`, `divisorStepJump_prime_of_anchored`: exact
  two-term divisor step isolation `c 1 + c p` (and `c p - 1` under `IsDirichletAnchored`) at every
  prime `p ≤ N`.
* `discreteCellResidual_two_eq`, `continuousNymanResidual_eq_c_two_on_dyadic_cell`,
  `discreteCellResidual_three_eq`, `discreteCellResidual_three_sub_two_eq_divisorStepJump`:
  dyadic (`c 2 - 1`) & ternary (`c 2 + c 3 - 2`) plateaus and jump `A_c(3) - A_c(2) = c 3 - 1`.
* `modularCellResidual_palindromic_two_eq_neg_c_two`, `modularCellResidual_palindromic_three_eq`,
  `selberg_continuousNymanResidual_palindromic_bridge`: palindromic mirror readout on `A_N^{dir}`.
-/

@[expose] public section

open scoped BigOperators

/-- Selberg logarithmic horizon-damped Mobius weight `-μ k * (1 - log k / log (N + 1))`. -/
noncomputable def rawSelbergMobiusWeight (μ : ℕ → ℝ) (N k : ℕ) : ℝ :=
  -μ k * (1 - Real.log (k : ℝ) / Real.log ((N : ℝ) + 1))

/-- At `k = 1`, `rawSelbergMobiusWeight μ N 1 = -μ 1`. -/
theorem rawSelbergMobiusWeight_one (μ : ℕ → ℝ) (N : ℕ) :
    rawSelbergMobiusWeight μ N 1 = -μ 1 := by
  simp [rawSelbergMobiusWeight]

/-- At the horizon `k = N + 1` (`1 ≤ N`), `rawSelbergMobiusWeight μ N (N + 1) = 0`. -/
theorem rawSelbergMobiusWeight_succ_self (μ : ℕ → ℝ) {N : ℕ} (hN : 1 ≤ N) :
    rawSelbergMobiusWeight μ N (N + 1) = 0 := by
  have hgt : (1 : ℝ) < (N : ℝ) + 1 := by
    have : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    linarith
  have hlog : Real.log ((N : ℝ) + 1) ≠ 0 := Real.log_ne_zero_of_pos_of_ne_one (by linarith) hgt.ne'
  unfold rawSelbergMobiusWeight
  push_cast
  rw [div_self hlog, sub_self, mul_zero]

/-- Sum of `c k` over divisors `k ∈ Icc 1 N` dividing `n`. -/
def divisorStepJump (c : ℕ → ℝ) (N n : ℕ) : ℝ :=
  ∑ k ∈ (Finset.Icc 1 N).filter (· ∣ n), c k

/-- For any prime `p ≤ N`, the divisors of `p` in `Icc 1 N` are `{1, p}`. -/
theorem filter_dvd_prime_eq_pair {N p : ℕ} (hp : Nat.Prime p) (hpN : p ≤ N) :
    (Finset.Icc 1 N).filter (· ∣ p) = {1, p} := by
  ext k
  simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨_, hkd⟩
    exact hp.eq_one_or_self_of_dvd k hkd
  · rintro (hk1 | hkp)
    · subst hk1; exact ⟨⟨le_rfl, hp.one_lt.le.trans hpN⟩, one_dvd p⟩
    · subst hkp; exact ⟨⟨hp.one_lt.le, hpN⟩, dvd_refl _⟩

/-- At any prime `p ≤ N`, `divisorStepJump c N p = c 1 + c p`. -/
theorem divisorStepJump_prime (c : ℕ → ℝ) {N p : ℕ} (hp : Nat.Prime p) (hpN : p ≤ N) :
    divisorStepJump c N p = c 1 + c p := by
  unfold divisorStepJump
  rw [filter_dvd_prime_eq_pair hp hpN, Finset.sum_pair hp.ne_one.symm]

/-- Under `IsDirichletAnchored c N` (`c 1 = -1`), `divisorStepJump c N p = c p - 1` at every prime
`p ≤ N`. -/
theorem divisorStepJump_prime_of_anchored {c : ℕ → ℝ} {N p : ℕ} (hc : IsDirichletAnchored c N)
    (hp : Nat.Prime p) (hpN : p ≤ N) : divisorStepJump c N p = c p - 1 := by
  rw [divisorStepJump_prime c hp hpN, hc.2.2]; ring

/-- On the dyadic cell `n = 2` (`2 ≤ N`), Dirichlet anchoring gives `discreteCellResidual c N 2 =
c 2 - 1`. -/
theorem discreteCellResidual_two_eq {c : ℕ → ℝ} {N : ℕ} (hN : 2 ≤ N)
    (hc : IsDirichletAnchored c N) : discreteCellResidual c N 2 = c 2 - 1 := by
  have h1 : (1 : ℕ) ∈ Finset.Icc 1 N := Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩
  have h2 : (2 : ℕ) ∈ Finset.Icc 1 N := Finset.mem_Icc.mpr ⟨by omega, hN⟩
  have hterm : ∀ k ∈ Finset.Icc 1 N, c k * ((2 / k : ℕ) : ℝ) =
      (if k = 1 then 2 * c 1 else 0) + (if k = 2 then c 2 else 0) := fun k _ => by
    rcases eq_or_ne k 1 with rfl | hk1
    · simp; ring
    · rcases eq_or_ne k 2 with rfl | hk2
      · simp
      · rcases k with _ | _ | _ | k <;> simp at hk1 hk2 ⊢
  unfold discreteCellResidual
  rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq']
  simp only [h1, h2, ↓reduceIte, hc.2.2]
  ring

/-- Across the continuous dyadic interval `x ∈ (1 / 3, 1 / 2]`, `continuousNymanResidual c N x =
c 2 - 1` whenever `2 ≤ N` and `IsDirichletAnchored c N`. -/
theorem continuousNymanResidual_eq_c_two_on_dyadic_cell {c : ℕ → ℝ} {N : ℕ} (hN : 2 ≤ N)
    (hc : IsDirichletAnchored c N) {x : ℝ} (hx1 : (1 / 3 : ℝ) < x) (hx2 : x ≤ 1 / 2) :
    continuousNymanResidual c N x = c 2 - 1 := by
  have hx_pos : 0 < x := lt_trans (by norm_num) hx1
  have hlo : ((2 : ℕ) : ℝ) ≤ 1 / x := (le_div_iff₀ hx_pos).mpr (by norm_num; linarith)
  have hhi : 1 / x < ((2 : ℕ) : ℝ) + 1 := (div_lt_iff₀ hx_pos).mpr (by norm_num; linarith)
  rw [continuousNymanResidual_eq_discreteCellResidual c N (by omega : 1 ≤ 2) hlo hhi hc.1,
    discreteCellResidual_two_eq hN hc]

/-- On the ternary cell `n = 3` (`3 ≤ N`), Dirichlet anchoring gives `discreteCellResidual c N 3 =
c 2 + c 3 - 2`. -/
theorem discreteCellResidual_three_eq {c : ℕ → ℝ} {N : ℕ} (hN : 3 ≤ N)
    (hc : IsDirichletAnchored c N) : discreteCellResidual c N 3 = c 2 + c 3 - 2 := by
  have h1 : (1 : ℕ) ∈ Finset.Icc 1 N := Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩
  have h2 : (2 : ℕ) ∈ Finset.Icc 1 N := Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  have h3 : (3 : ℕ) ∈ Finset.Icc 1 N := Finset.mem_Icc.mpr ⟨by omega, hN⟩
  have hterm : ∀ k ∈ Finset.Icc 1 N, c k * ((3 / k : ℕ) : ℝ) =
      (if k = 1 then 3 * c 1 else 0) + (if k = 2 then c 2 else 0) +
        (if k = 3 then c 3 else 0) := fun k _ => by
    rcases eq_or_ne k 1 with rfl | hk1
    · simp; ring
    · rcases eq_or_ne k 2 with rfl | hk2
      · simp
      · rcases eq_or_ne k 3 with rfl | hk3
        · simp
        · rcases k with _ | _ | _ | _ | k <;> simp at hk1 hk2 hk3 ⊢
  unfold discreteCellResidual
  rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib, Finset.sum_add_distrib,
    Finset.sum_ite_eq', Finset.sum_ite_eq', Finset.sum_ite_eq']
  simp only [h1, h2, h3, ↓reduceIte, hc.2.2]
  ring

/-- Exact prime jump between the ternary and dyadic cells: `discreteCellResidual c N 3 -
discreteCellResidual c N 2 = divisorStepJump c N 3` (`3 ≤ N`, `IsDirichletAnchored c N`). -/
theorem discreteCellResidual_three_sub_two_eq_divisorStepJump {c : ℕ → ℝ} {N : ℕ} (hN : 3 ≤ N)
    (hc : IsDirichletAnchored c N) :
    discreteCellResidual c N 3 - discreteCellResidual c N 2 = divisorStepJump c N 3 := by
  rw [discreteCellResidual_three_eq hN hc, discreteCellResidual_two_eq (by omega : 2 ≤ N) hc,
    divisorStepJump_prime_of_anchored hc (by decide : Nat.Prime 3) hN]
  ring

/-- Palindromic dyadic mirror readout: `modularCellResidual c N (L - 1 - 2) = 1 - c 2`. -/
theorem modularCellResidual_palindromic_two_eq_neg_c_two {c : ℕ → ℝ} {N L : ℕ} (hN : 2 ≤ N)
    (hc : IsDirichletAnchored c N) (hL : ∀ k ∈ Finset.Icc 1 N, k ∣ L) (hL2 : 2 < L) :
    modularCellResidual c N (L - 1 - 2) = 1 - c 2 := by
  rw [modularCellResidual_palindromic_neg c N L 2 hc.1 hc.2.1 hL hL2,
    ← discreteCellResidual_eq_modularCellResidual_of_D1_eq_zero c N 2 hc.1,
    discreteCellResidual_two_eq hN hc]
  ring

/-- Palindromic ternary mirror readout: `modularCellResidual c N (L - 1 - 3) = 2 - c 2 - c 3`. -/
theorem modularCellResidual_palindromic_three_eq {c : ℕ → ℝ} {N L : ℕ} (hN : 3 ≤ N)
    (hc : IsDirichletAnchored c N) (hL : ∀ k ∈ Finset.Icc 1 N, k ∣ L) (hL3 : 3 < L) :
    modularCellResidual c N (L - 1 - 3) = 2 - c 2 - c 3 := by
  rw [modularCellResidual_palindromic_neg c N L 3 hc.1 hc.2.1 hL hL3,
    ← discreteCellResidual_eq_modularCellResidual_of_D1_eq_zero c N 3 hc.1,
    discreteCellResidual_three_eq hN hc]
  ring

/-- **Selberg-Mobius Continuity and Palindromic Bridge**: combines horizon vanishing at `N + 1`,
dyadic continuous plateau `(1 / 3, 1 / 2]`, ternary prime jump, and palindromic mirror cells. -/
theorem selberg_continuousNymanResidual_palindromic_bridge (μ c : ℕ → ℝ) {N L : ℕ} (hN : 3 ≤ N)
    (hc : IsDirichletAnchored c N) (hL : ∀ k ∈ Finset.Icc 1 N, k ∣ L) (hL3 : 3 < L)
    {x : ℝ} (hx1 : (1 / 3 : ℝ) < x) (hx2 : x ≤ 1 / 2) :
    rawSelbergMobiusWeight μ N (N + 1) = 0 ∧
      continuousNymanResidual c N x = c 2 - 1 ∧
      discreteCellResidual c N 3 - discreteCellResidual c N 2 = divisorStepJump c N 3 ∧
      modularCellResidual c N (L - 1 - 2) = 1 - c 2 ∧
      modularCellResidual c N (L - 1 - 3) = 2 - c 2 - c 3 :=
  ⟨rawSelbergMobiusWeight_succ_self μ (by omega : 1 ≤ N),
    continuousNymanResidual_eq_c_two_on_dyadic_cell (by omega : 2 ≤ N) hc hx1 hx2,
    discreteCellResidual_three_sub_two_eq_divisorStepJump hN hc,
    modularCellResidual_palindromic_two_eq_neg_c_two (by omega : 2 ≤ N) hc hL (by omega),
    modularCellResidual_palindromic_three_eq hN hc hL hL3⟩
