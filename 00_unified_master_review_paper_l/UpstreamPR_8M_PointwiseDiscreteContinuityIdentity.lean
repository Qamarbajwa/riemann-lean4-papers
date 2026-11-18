/-
Copyright (c) 2026 Qamar Munawer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qamar Munawer
-/
module

public import RiemannBlueprint.UpstreamPRs.UpstreamPR_8L_PlaqueRowTelescopingAndSimplex

/-!
# Pointwise Discrete-Equals-Continuous Identity and Top-Half Continuum Annihilation

This module proves:
* `continuousNymanResidual_eq_floor_sum_of_D1_eq_zero`: whenever `D1 c N = 0`, the continuous
  slope `1 / x` cancels identically from `continuousNymanResidual c N x`.
* `floor_one_div_mul_eq_nat_div`, `continuousNymanResidual_eq_discreteCellResidual`: on every
  interval `(1 / (n + 1), 1 / n]` (`n ≥ 1`), the continuous residual equals the discrete integer-
  cell residual `discreteCellResidual c N n = 1 + ∑ k ∈ Icc 1 N, c k * (n / k : ℕ)`.
* `discreteCellResidual_eq_sum_min`: causal triangular truncation of `discreteCellResidual` at
  `min n N`.
* `continuousNymanResidual_eq_zero_of_cell_vanishing`,
  `continuousNymanResidual_eq_zero_on_top_half`: progressive cell vanishing across
  `(1 / (M + 1), 1]` and unconditional top-half `(1 / 2, 1]` annihilation for every
  Dirichlet-anchored vector (`c 1 = -1`) and dipole vertex `cBaseAnchor + cumulativeDipole m`.
-/

@[expose] public section

open scoped BigOperators

/-- Pointwise continuous Nyman-Beurling residual `1 - ∑ k ∈ Icc 1 N, c k * fract(1 / (k * x))`. -/
noncomputable def continuousNymanResidual (c : ℕ → ℝ) (N : ℕ) (x : ℝ) : ℝ :=
  1 - ∑ k ∈ Finset.Icc 1 N, c k * Int.fract (1 / ((k : ℝ) * x))

/-- Discrete integer-cell residual `1 + ∑ k ∈ Icc 1 N, c k * (n / k : ℕ)`. -/
noncomputable def discreteCellResidual (c : ℕ → ℝ) (N n : ℕ) : ℝ :=
  1 + ∑ k ∈ Finset.Icc 1 N, c k * ((n / k : ℕ) : ℝ)

/-- Under `D1 c N = 0`, the continuous term `1 / x` cancels pointwise, reducing
`continuousNymanResidual c N x` to `1 + ∑ k ∈ Icc 1 N, c k * ⌊1 / (k * x)⌋`. -/
theorem continuousNymanResidual_eq_floor_sum_of_D1_eq_zero (c : ℕ → ℝ) (N : ℕ) (x : ℝ)
    (hD1 : D1 c N = 0) :
    continuousNymanResidual c N x =
      1 + ∑ k ∈ Finset.Icc 1 N, c k * (⌊1 / ((k : ℝ) * x)⌋ : ℝ) := by
  have hterm : ∀ k ∈ Finset.Icc 1 N,
      c k * Int.fract (1 / ((k : ℝ) * x)) =
        (c k / (k : ℝ)) * (1 / x) - c k * (⌊1 / ((k : ℝ) * x)⌋ : ℝ) := fun k _ => by
    rw [Int.fract, mul_sub, div_eq_mul_inv, mul_inv]
    ring
  unfold continuousNymanResidual
  rw [Finset.sum_congr rfl hterm, Finset.sum_sub_distrib, ← Finset.sum_mul]
  change 1 - (D1 c N * (1 / x) - ∑ k ∈ Finset.Icc 1 N, c k * (⌊1 / ((k : ℝ) * x)⌋ : ℝ)) = _
  rw [hD1, zero_mul, zero_sub, sub_neg_eq_add]

/-- On every elementary cell `(1 / (n + 1), 1 / n]` (`n ≥ 1`), `⌊1 / (k * x)⌋ = n / k` pointwise
for every continuous `x` in the interval and every `k ≥ 1`. -/
theorem floor_one_div_mul_eq_nat_div {n k : ℕ} (hn : 1 ≤ n) (hk : 1 ≤ k) {x : ℝ}
    (hx1 : 1 / ((n : ℝ) + 1) < x) (hx2 : x ≤ 1 / (n : ℝ)) :
    ⌊1 / ((k : ℝ) * x)⌋ = ((n / k : ℕ) : ℤ) := by
  have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr (by omega)
  have hn1_pos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hk_pos : (0 : ℝ) < (k : ℝ) := Nat.cast_pos.mpr (by omega)
  have hx_pos : 0 < x := lt_trans (one_div_pos.mpr hn1_pos) hx1
  have hlo : (n : ℝ) ≤ 1 / x := (le_div_iff₀ hx_pos).mpr (by
    have h := (le_div_iff₀ hn_pos).mp hx2; linarith)
  have hhi : 1 / x < (n : ℝ) + 1 := (div_lt_iff₀ hx_pos).mpr (by
    have h := (div_lt_iff₀ hn1_pos).mp hx1; linarith)
  have hsplit : 1 / ((k : ℝ) * x) = (1 / x) / (k : ℝ) := by rw [div_div, mul_comm]
  have hlo_div : (n : ℝ) / (k : ℝ) ≤ 1 / ((k : ℝ) * x) := by
    rw [hsplit]; exact div_le_div_of_nonneg_right hlo hk_pos.le
  have hhi_div : 1 / ((k : ℝ) * x) < ((n : ℝ) + 1) / (k : ℝ) := by
    rw [hsplit]; exact div_lt_div_of_pos_right hhi hk_pos
  have hnat_lo : ((n / k : ℕ) : ℝ) ≤ (n : ℝ) / (k : ℝ) := by
    rw [le_div_iff₀ hk_pos]; exact_mod_cast Nat.div_mul_le_self n k
  have hnat_hi : ((n : ℝ) + 1) / (k : ℝ) ≤ ((n / k : ℕ) : ℝ) + 1 := by
    rw [div_le_iff₀ hk_pos]
    have hlt : n + 1 ≤ (n / k + 1) * k := by
      have h := Nat.lt_div_mul_add (a := n) (by omega : 0 < k)
      linarith
    exact_mod_cast hlt
  refine Int.floor_eq_iff.mpr ⟨?_, ?_⟩
  · push_cast; exact le_trans hnat_lo hlo_div
  · push_cast; exact lt_of_lt_of_le hhi_div hnat_hi

/-- **Pointwise Discrete-Equals-Continuous Theorem**: whenever `D1 c N = 0`, `n ≥ 1`, and
`1 / (n + 1) < x ≤ 1 / n`, `continuousNymanResidual c N x = discreteCellResidual c N n`. -/
theorem continuousNymanResidual_eq_discreteCellResidual (c : ℕ → ℝ) (N : ℕ) {n : ℕ} (hn : 1 ≤ n)
    {x : ℝ} (hx1 : 1 / ((n : ℝ) + 1) < x) (hx2 : x ≤ 1 / (n : ℝ)) (hD1 : D1 c N = 0) :
    continuousNymanResidual c N x = discreteCellResidual c N n := by
  rw [continuousNymanResidual_eq_floor_sum_of_D1_eq_zero c N x hD1]
  unfold discreteCellResidual
  congr 1
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [floor_one_div_mul_eq_nat_div hn (Finset.mem_Icc.mp hk).1 hx1 hx2, Int.cast_natCast]

/-- Causal triangular truncation of `discreteCellResidual` at `min n N` (since `n / k = 0` for
`k > n`). -/
theorem discreteCellResidual_eq_sum_min (c : ℕ → ℝ) (N n : ℕ) :
    discreteCellResidual c N n =
      1 + ∑ k ∈ Finset.Icc 1 (min n N), c k * ((n / k : ℕ) : ℝ) := by
  unfold discreteCellResidual
  congr 1
  symm
  refine Finset.sum_subset (Finset.Icc_subset_Icc_right (min_le_right n N)) fun k hk hkn => ?_
  simp only [Finset.mem_Icc, not_and, not_le] at hk hkn
  have hlt : n < k := by have := hkn hk.1; omega
  rw [Nat.div_eq_of_lt hlt, Nat.cast_zero, mul_zero]

/-- On the first cell `n = 1` (`1 ≤ N`), `discreteCellResidual c N 1 = 1 + c 1`. -/
theorem discreteCellResidual_one_eq (c : ℕ → ℝ) {N : ℕ} (hN : 1 ≤ N) :
    discreteCellResidual c N 1 = 1 + c 1 := by
  rw [discreteCellResidual_eq_sum_min, min_eq_left hN, Finset.Icc_self, Finset.sum_singleton,
    Nat.div_self (by omega), Nat.cast_one, mul_one]

/-- **Progressive Continuum Annihilation**: if `D1 c N = 0` and `discreteCellResidual c N n = 0`
for all `1 ≤ n ≤ M` (`1 ≤ M`), then `continuousNymanResidual c N x = 0` pointwise everywhere on
`(1 / (M + 1), 1]`. -/
theorem continuousNymanResidual_eq_zero_of_cell_vanishing (c : ℕ → ℝ) (N : ℕ) {M : ℕ}
    (hM : 1 ≤ M) (hD1 : D1 c N = 0)
    (hcell : ∀ n ∈ Finset.Icc 1 M, discreteCellResidual c N n = 0)
    {x : ℝ} (hx1 : 1 / ((M : ℝ) + 1) < x) (hx2 : x ≤ 1) :
    continuousNymanResidual c N x = 0 := by
  let _ := hM
  have hM1_pos : (0 : ℝ) < (M : ℝ) + 1 := by positivity
  have hx_pos : 0 < x := lt_trans (one_div_pos.mpr hM1_pos) hx1
  have h1_le : 1 ≤ 1 / x := (one_le_div hx_pos).mpr hx2
  have hlt_M1 : 1 / x < (M : ℝ) + 1 := (div_lt_iff₀ hx_pos).mpr (by
    have h := (div_lt_iff₀ hM1_pos).mp hx1; linarith)
  set n : ℕ := Nat.floor (1 / x)
  have hn_le_inv : (n : ℝ) ≤ 1 / x := Nat.floor_le (div_nonneg zero_le_one hx_pos.le)
  have hinv_lt_n1 : 1 / x < (n : ℝ) + 1 := Nat.lt_floor_add_one (1 / x)
  have hn1 : 1 ≤ n := Nat.le_floor (by exact_mod_cast h1_le)
  have hnM : n ≤ M := by
    have hlt_nat : (n : ℝ) < (M : ℝ) + 1 := lt_of_le_of_lt hn_le_inv hlt_M1
    exact Nat.lt_succ_iff.mp (by exact_mod_cast hlt_nat)
  have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr (by omega)
  have hn1_pos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hx_cell1 : 1 / ((n : ℝ) + 1) < x := (div_lt_iff₀ hn1_pos).mpr (by
    have h := (div_lt_iff₀ hx_pos).mp hinv_lt_n1; linarith)
  have hx_cell2 : x ≤ 1 / (n : ℝ) := (le_div_iff₀ hn_pos).mpr (by
    have h := (le_div_iff₀ hx_pos).mp hn_le_inv; linarith)
  rw [continuousNymanResidual_eq_discreteCellResidual c N hn1 hx_cell1 hx_cell2 hD1]
  exact hcell n (Finset.mem_Icc.mpr ⟨hn1, hnM⟩)

/-- **Top-Half Continuum Annihilation Theorem**: for every `N ≥ 2` and every Dirichlet-anchored
vector `c` (`IsDirichletAnchored c N`), `continuousNymanResidual c N x = 0` for every continuous
real point `x ∈ (1 / 2, 1]`. -/
theorem continuousNymanResidual_eq_zero_on_top_half {N : ℕ} (hN : 2 ≤ N) {c : ℕ → ℝ}
    (hc : IsDirichletAnchored c N) {x : ℝ} (hx1 : (1 / 2 : ℝ) < x) (hx2 : x ≤ 1) :
    continuousNymanResidual c N x = 0 := by
  have hx1' : 1 / (((1 : ℕ) : ℝ) + 1) < x := by norm_num; exact hx1
  have hx2' : x ≤ 1 / ((1 : ℕ) : ℝ) := by norm_num; exact hx2
  rw [continuousNymanResidual_eq_discreteCellResidual c N (by omega : 1 ≤ 1) hx1' hx2' hc.1,
    discreteCellResidual_one_eq c (by omega : 1 ≤ N), hc.2.2]
  ring

private lemma cumulativeDipole_one_eq {m : ℕ} (hm : 1 ≤ m) : cumulativeDipole m 1 = 1 := by
  unfold cumulativeDipole
  have h1 : (1 : ℕ) ∈ Finset.Icc 1 m := Finset.mem_Icc.mpr ⟨le_rfl, hm⟩
  have hval : ∀ r ∈ Finset.Icc 1 m, harmonicWavelet r 1 = if r = 1 then 1 else 0 := fun r hr => by
    have hr1 : 1 ≤ r := (Finset.mem_Icc.mp hr).1
    rcases eq_or_ne r 1 with rfl | hne
    · simp [harmonicWavelet]
    · simp only [harmonicWavelet, hne, ↓reduceIte]
      split_ifs <;> first | rfl | omega
  rw [Finset.sum_congr rfl hval, Finset.sum_ite_eq']
  simp [h1]

/-- Every elementary Dirichlet-anchored dipole vertex `cBaseAnchor + cumulativeDipole m` satisfies
`IsDirichletAnchored` for all `N ≥ m + 2` (`m ≥ 1`). -/
theorem cBaseAnchor_add_cumulativeDipole_isDirichletAnchored {m N : ℕ} (hm : 1 ≤ m)
    (hN : m + 2 ≤ N) :
    IsDirichletAnchored (fun k => cBaseAnchor k + cumulativeDipole m k) N := by
  have ha := cBaseAnchor_mem_A_N (by omega : 2 ≤ N)
  have hd := cumulativeDipole_mem_tangent hm hN
  refine ⟨?_, ?_, ?_⟩
  · unfold D1 at ha hd ⊢
    have hpt : ∀ k ∈ Finset.Icc 1 N,
        (cBaseAnchor k + cumulativeDipole m k) / (k : ℝ) =
          cBaseAnchor k / (k : ℝ) + cumulativeDipole m k / (k : ℝ) := fun k _ => by ring
    rw [Finset.sum_congr rfl hpt, Finset.sum_add_distrib, ha.1, hd.1, add_zero]
  · unfold D0 at ha hd ⊢
    rw [Finset.sum_add_distrib, ha.2, hd.2, add_zero]
  · simp [cBaseAnchor, cumulativeDipole_one_eq hm]; norm_num

/-- Every elementary dipole vertex `cBaseAnchor + cumulativeDipole m` (`1 ≤ m`, `m + 2 ≤ N`)
annihilates `continuousNymanResidual` identically on the top half `(1 / 2, 1]`. -/
theorem continuousNymanResidual_cBase_add_dipole_eq_zero_on_top_half {m N : ℕ} (hm : 1 ≤ m)
    (hN : m + 2 ≤ N) {x : ℝ} (hx1 : (1 / 2 : ℝ) < x) (hx2 : x ≤ 1) :
    continuousNymanResidual (fun k => cBaseAnchor k + cumulativeDipole m k) N x = 0 :=
  continuousNymanResidual_eq_zero_on_top_half (by omega : 2 ≤ N)
    (cBaseAnchor_add_cumulativeDipole_isDirichletAnchored hm hN) hx1 hx2
