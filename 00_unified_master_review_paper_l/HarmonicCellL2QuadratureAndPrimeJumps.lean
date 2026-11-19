/-
Copyright (c) 2026 Qamar Munawer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qamar Munawer
-/
module

public import RiemannBlueprint.Modules.PointwiseContinuityAndPeriodicity

/-!
# Harmonic-Cell L² Quadrature, Exact Cell Partial Sums, and Prime Divisor Jumps

This module proves:
* `harmonicCellWidth`, `harmonicCellWidth_eq_sub`, and `sum_Icc_harmonicCellWidth`: exact
  partial-fraction and telescoping cell-width identities over `Finset.Icc 2 M`.
* `continuousNymanResidual_sq_mul_width_eq`: exact L² quadrature on each cell `(1/(n+1), 1/n]`.
* `harmonicCellL2PartialSum`, `harmonicCellL2PartialSum_eq_sum_Icc_two`,
  `harmonicCellL2PartialSum_two_eq`, `harmonicCellL2PartialSum_three_eq`: cell-by-cell L²
  quadrature collapsing `n = 1` under `IsDirichletAnchored` and evaluating `M = 2, 3`.
* `divisorStepJump_prime_of_anchored`, `discreteCellResidual_three_sub_two_eq_divisorStepJump`,
  and `rawSelbergMobiusWeight_succ_self`: prime-step jump isolation and Selberg cutoff vanishing.
-/

@[expose] public section

open scoped BigOperators

/-- Width `(1 / n - 1 / (n + 1)) = 1 / (n * (n + 1))` of the `n`-th harmonic cell. -/
noncomputable def harmonicCellWidth (n : ℕ) : ℝ :=
  1 / ((n : ℝ) * ((n : ℝ) + 1))

/-- Partial-fraction expansion of `harmonicCellWidth n` for `n ≠ 0`. -/
theorem harmonicCellWidth_eq_sub {n : ℕ} (hn : n ≠ 0) :
    harmonicCellWidth n = 1 / (n : ℝ) - 1 / ((n : ℝ) + 1) := by
  have hn_ne : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  have hn1_ne : (n : ℝ) + 1 ≠ 0 := by positivity
  unfold harmonicCellWidth
  field_simp [hn_ne, hn1_ne]
  ring

/-- Telescoping sum of cell widths on `Icc 2 M`: `∑ n ∈ Icc 2 M, harmonicCellWidth n =
1 / 2 - 1 / (M + 1)`. -/
theorem sum_Icc_harmonicCellWidth {M : ℕ} (hM : 2 ≤ M) :
    ∑ n ∈ Finset.Icc 2 M, harmonicCellWidth n = 1 / 2 - 1 / ((M : ℝ) + 1) := by
  induction M, hM using Nat.le_induction with
  | base =>
    simp [harmonicCellWidth]
    norm_num
  | succ k hk ih =>
    have hnot : k + 1 ∉ Finset.Icc 2 k := by simp
    have hIcc : Finset.Icc 2 (k + 1) = insert (k + 1) (Finset.Icc 2 k) := by
      ext x
      simp only [Finset.mem_Icc, Finset.mem_insert]
      omega
    rw [hIcc, Finset.sum_insert hnot, ih, harmonicCellWidth_eq_sub (by omega)]
    push_cast
    ring

/-- **Cell L² Quadrature**: under `D1 c N = 0` and `1 ≤ n`, integrating
`(continuousNymanResidual c N x)^2` over `(1 / (n + 1))..(1 / n)` gives
`(discreteCellResidual c N n)^2 * harmonicCellWidth n`. -/
theorem continuousNymanResidual_sq_mul_width_eq (c : ℕ → ℝ) (N : ℕ) {n : ℕ} (hn : 1 ≤ n)
    (hD1 : D1 c N = 0) :
    ∫ x in (1 / ((n : ℝ) + 1))..(1 / (n : ℝ)), (continuousNymanResidual c N x) ^ 2 =
      (discreteCellResidual c N n) ^ 2 * harmonicCellWidth n := by
  have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr (by omega)
  have hle : 1 / ((n : ℝ) + 1) ≤ 1 / (n : ℝ) :=
    one_div_le_one_div_of_le hn_pos (by linarith)
  rw [intervalIntegral.integral_of_le hle]
  have hcongr : ∀ x ∈ Set.Ioc (1 / ((n : ℝ) + 1)) (1 / (n : ℝ)),
      (continuousNymanResidual c N x) ^ 2 = (discreteCellResidual c N n) ^ 2 := by
    intro x ⟨hx1, hx2⟩
    have hx_pos : 0 < x := lt_trans (by positivity) hx1
    have hlo : (n : ℝ) ≤ 1 / x := (le_div_iff₀ hx_pos).mpr (by
      have := mul_le_mul_of_nonneg_left hx2 hn_pos.le
      rw [one_div, mul_inv_cancel₀ hn_pos.ne'] at this
      linarith)
    have hhi : 1 / x < (n : ℝ) + 1 := (div_lt_iff₀ hx_pos).mpr (by
      have h1 : (n : ℝ) + 1 > 0 := by positivity
      have := mul_lt_mul_of_pos_left hx1 h1
      rw [one_div, mul_inv_cancel₀ h1.ne'] at this
      linarith)
    rw [continuousNymanResidual_eq_discreteCellResidual c N hn hlo hhi hD1]
  rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioc hcongr,
    MeasureTheory.setIntegral_const, smul_eq_mul, Real.volume_real_Ioc_of_le hle,
    ← harmonicCellWidth_eq_sub (by omega), mul_comm]

/-- Partial L² harmonic-cell quadrature sum up to cutoff `M`. -/
noncomputable def harmonicCellL2PartialSum (c : ℕ → ℝ) (N M : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 M, (discreteCellResidual c N n) ^ 2 * harmonicCellWidth n

/-- Under `IsDirichletAnchored c N` (`1 ≤ N`, `2 ≤ M`), the top cell `n = 1` vanishes identically,
leaving only `n ∈ Icc 2 M`. -/
theorem harmonicCellL2PartialSum_eq_sum_Icc_two {c : ℕ → ℝ} {N M : ℕ} (hN : 1 ≤ N)
    (hM : 2 ≤ M) (hc : IsDirichletAnchored c N) :
    harmonicCellL2PartialSum c N M =
      ∑ n ∈ Finset.Icc 2 M, (discreteCellResidual c N n) ^ 2 * harmonicCellWidth n := by
  have h1 : (1 : ℕ) ∉ Finset.Icc 2 M := by simp
  have hIcc : Finset.Icc 1 M = insert 1 (Finset.Icc 2 M) := by
    ext n; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
  unfold harmonicCellL2PartialSum
  rw [hIcc, Finset.sum_insert h1, discreteCellResidual_one_eq c hN, hc.2.2]
  ring

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

/-- Exact `M = 2` harmonic-cell L² quadrature under `IsDirichletAnchored` (`2 ≤ N`):
`(c 2 - 1)^2 / 6`. -/
theorem harmonicCellL2PartialSum_two_eq {c : ℕ → ℝ} {N : ℕ} (hN : 2 ≤ N)
    (hc : IsDirichletAnchored c N) : harmonicCellL2PartialSum c N 2 = (c 2 - 1) ^ 2 / 6 := by
  rw [harmonicCellL2PartialSum_eq_sum_Icc_two (by omega : 1 ≤ N) le_rfl hc,
    Finset.Icc_self, Finset.sum_singleton, discreteCellResidual_two_eq hN hc]
  unfold harmonicCellWidth; norm_num; ring

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

/-- Exact `M = 3` harmonic-cell L² quadrature under `IsDirichletAnchored` (`3 ≤ N`):
`(c 2 - 1)^2 / 6 + (c 2 + c 3 - 2)^2 / 12`. -/
theorem harmonicCellL2PartialSum_three_eq {c : ℕ → ℝ} {N : ℕ} (hN : 3 ≤ N)
    (hc : IsDirichletAnchored c N) :
    harmonicCellL2PartialSum c N 3 = (c 2 - 1) ^ 2 / 6 + (c 2 + c 3 - 2) ^ 2 / 12 := by
  have hnot : (3 : ℕ) ∉ Finset.Icc 2 2 := by simp
  have hIcc : Finset.Icc 2 3 = insert 3 (Finset.Icc 2 2) := by
    ext n; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
  rw [harmonicCellL2PartialSum_eq_sum_Icc_two (by omega : 1 ≤ N) (by omega) hc,
    hIcc, Finset.sum_insert hnot, Finset.Icc_self, Finset.sum_singleton,
    discreteCellResidual_two_eq (by omega) hc, discreteCellResidual_three_eq hN hc]
  unfold harmonicCellWidth; norm_num; ring

/-- Sum of `c k` over divisors `k ∈ Icc 1 N` dividing `n`. -/
def divisorStepJump (c : ℕ → ℝ) (N n : ℕ) : ℝ :=
  ∑ k ∈ (Finset.Icc 1 N).filter (· ∣ n), c k

/-- For every prime `p ≤ N` under `IsDirichletAnchored c N`, `divisorStepJump c N p = c p - 1`. -/
theorem divisorStepJump_prime_of_anchored {c : ℕ → ℝ} {N p : ℕ} (hc : IsDirichletAnchored c N)
    (hp : Nat.Prime p) (hpN : p ≤ N) : divisorStepJump c N p = c p - 1 := by
  have hdiv : (Finset.Icc 1 N).filter (· ∣ p) = {1, p} := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨_, hkd⟩; exact hp.eq_one_or_self_of_dvd k hkd
    · rintro (rfl | rfl)
      · exact ⟨⟨le_rfl, hp.one_lt.le.trans hpN⟩, one_dvd p⟩
      · exact ⟨⟨hp.one_lt.le, hpN⟩, dvd_refl _⟩
  unfold divisorStepJump
  rw [hdiv, Finset.sum_pair hp.ne_one.symm, hc.2.2]; ring

/-- Prime-3 step jump: `discreteCellResidual c N 3 - discreteCellResidual c N 2 =
divisorStepJump c N 3` (`3 ≤ N`, `IsDirichletAnchored c N`). -/
theorem discreteCellResidual_three_sub_two_eq_divisorStepJump {c : ℕ → ℝ} {N : ℕ} (hN : 3 ≤ N)
    (hc : IsDirichletAnchored c N) :
    discreteCellResidual c N 3 - discreteCellResidual c N 2 = divisorStepJump c N 3 := by
  rw [discreteCellResidual_three_eq hN hc, discreteCellResidual_two_eq (by omega : 2 ≤ N) hc,
    divisorStepJump_prime_of_anchored hc (by decide : Nat.Prime 3) hN]
  ring

/-- Selberg logarithmic horizon-damped Mobius weight `-μ k * (1 - log k / log (N + 1))`. -/
noncomputable def rawSelbergMobiusWeight (μ : ℕ → ℝ) (N k : ℕ) : ℝ :=
  -μ k * (1 - Real.log (k : ℝ) / Real.log ((N : ℝ) + 1))

/-- At the cutoff `k = N + 1` (`1 ≤ N`), `rawSelbergMobiusWeight μ N (N + 1) = 0`. -/
theorem rawSelbergMobiusWeight_succ_self (μ : ℕ → ℝ) {N : ℕ} (hN : 1 ≤ N) :
    rawSelbergMobiusWeight μ N (N + 1) = 0 := by
  have hgt : (1 : ℝ) < (N : ℝ) + 1 := by
    have : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    linarith
  have hlog : Real.log ((N : ℝ) + 1) ≠ 0 := Real.log_ne_zero_of_pos_of_ne_one (by linarith) hgt.ne'
  unfold rawSelbergMobiusWeight
  push_cast
  rw [div_self hlog, sub_self, mul_zero]
