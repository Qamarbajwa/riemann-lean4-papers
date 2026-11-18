/-
Copyright (c) 2026 Qamar Munawer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qamar Munawer
-/
module

public import RiemannBlueprint.UpstreamPRs.UpstreamPR_8L_PlaqueRowTelescopingAndSimplex

/-!
# Pointwise Continuity, Modular Duality, and Palindromic Periodicity

This module proves:
* `fract_nat_div_eq_sub_nat_div`, `discreteCellResidual_eq_modularCellResidual_of_D1_eq_zero`:
  exact equivalence between floor-cell and modular-cell residuals whenever `D1 c N = 0`.
* `floor_one_div_mul_eq_nat_div`, `continuousNymanResidual_eq_discreteCellResidual`,
  `continuousNymanResidual_eq_modularCellResidual`: pointwise collapse of `continuousNymanResidual`
  onto `discreteCellResidual` and `modularCellResidual` on `n ≤ 1 / x < n + 1` (`n ≥ 1`).
* `discreteCellResidual_one_eq`, `continuousNymanResidual_eq_zero_on_top_half`: exact top-half
  `(1 / 2, 1]` continuum annihilation for every `IsDirichletAnchored` vector (`c 1 = -1`).
* `modularCellResidual_periodic`, `fract_palindromic_add_eq`,
  `modularCellResidual_palindromic_neg`, `sum_Ico_modularCellResidual_eq_zero`: exact `L`-period
  folding, palindromic antisymmetry `A_c(L - 1 - m) = -A_c(m)` on `A_N`, and zero period mean.
-/

@[expose] public section

open scoped BigOperators

/-- Pointwise continuous Nyman-Beurling residual `1 - ∑ k ∈ Icc 1 N, c k * fract(1 / (k * x))`. -/
noncomputable def continuousNymanResidual (c : ℕ → ℝ) (N : ℕ) (x : ℝ) : ℝ :=
  1 - ∑ k ∈ Finset.Icc 1 N, c k * Int.fract (1 / ((k : ℝ) * x))

/-- Discrete integer floor-cell residual `1 + ∑ k ∈ Icc 1 N, c k * (n / k : ℕ)`. -/
noncomputable def discreteCellResidual (c : ℕ → ℝ) (N n : ℕ) : ℝ :=
  1 + ∑ k ∈ Finset.Icc 1 N, c k * ((n / k : ℕ) : ℝ)

/-- Discrete modular-cell residual `1 - ∑ k ∈ Icc 1 N, c k * fract(n / k)`. -/
noncomputable def modularCellResidual (c : ℕ → ℝ) (N n : ℕ) : ℝ :=
  1 - ∑ k ∈ Finset.Icc 1 N, c k * Int.fract ((n : ℝ) / (k : ℝ))

private lemma floor_div_nat_eq_nat_div {n k : ℕ} (hk : 1 ≤ k) :
    ⌊(n : ℝ) / (k : ℝ)⌋ = ((n / k : ℕ) : ℤ) := by
  have hk_pos : (0 : ℝ) < (k : ℝ) := Nat.cast_pos.mpr (by omega)
  have hlo : ((n / k : ℕ) : ℝ) ≤ (n : ℝ) / (k : ℝ) := by
    rw [le_div_iff₀ hk_pos]; exact_mod_cast Nat.div_mul_le_self n k
  have hhi : (n : ℝ) / (k : ℝ) < ((n / k : ℕ) : ℝ) + 1 := by
    rw [div_lt_iff₀ hk_pos]
    exact_mod_cast (by have := Nat.lt_div_mul_add (a := n) (by omega : 0 < k); linarith)
  exact Int.floor_eq_iff.mpr ⟨by push_cast; exact hlo, by push_cast; exact hhi⟩

/-- For `k ≥ 1` and `n : ℕ`, `Int.fract (n / k) = n / k - (n / k : ℕ)`. -/
theorem fract_nat_div_eq_sub_nat_div (n : ℕ) {k : ℕ} (hk : 1 ≤ k) :
    Int.fract ((n : ℝ) / (k : ℝ)) = (n : ℝ) / (k : ℝ) - ((n / k : ℕ) : ℝ) := by
  rw [Int.fract, floor_div_nat_eq_nat_div hk, Int.cast_natCast]

/-- Whenever `D1 c N = 0`, `discreteCellResidual c N n = modularCellResidual c N n` for all
`n : ℕ`. -/
theorem discreteCellResidual_eq_modularCellResidual_of_D1_eq_zero (c : ℕ → ℝ) (N n : ℕ)
    (hD1 : D1 c N = 0) :
    discreteCellResidual c N n = modularCellResidual c N n := by
  have hterm : ∀ k ∈ Finset.Icc 1 N,
      c k * Int.fract ((n : ℝ) / (k : ℝ)) =
        (n : ℝ) * (c k / (k : ℝ)) - c k * ((n / k : ℕ) : ℝ) := fun k hk => by
    rw [fract_nat_div_eq_sub_nat_div n (Finset.mem_Icc.mp hk).1]; ring
  unfold modularCellResidual discreteCellResidual
  rw [Finset.sum_congr rfl hterm, Finset.sum_sub_distrib, ← Finset.mul_sum]
  change _ = 1 - ((n : ℝ) * D1 c N - ∑ k ∈ Finset.Icc 1 N, c k * ((n / k : ℕ) : ℝ))
  rw [hD1, mul_zero, zero_sub, sub_neg_eq_add]

/-- On every harmonic cell `n ≤ 1 / x < n + 1` (`n ≥ 1`), `⌊1 / (k * x)⌋ = n / k` pointwise for
every `k ≥ 1`. -/
theorem floor_one_div_mul_eq_nat_div {n k : ℕ} (hn : 1 ≤ n) (hk : 1 ≤ k) {x : ℝ}
    (hx1 : (n : ℝ) ≤ 1 / x) (hx2 : 1 / x < (n : ℝ) + 1) :
    ⌊1 / ((k : ℝ) * x)⌋ = ((n / k : ℕ) : ℤ) := by
  let _ := hn
  have hk_pos : (0 : ℝ) < (k : ℝ) := Nat.cast_pos.mpr (by omega)
  have hsplit : 1 / ((k : ℝ) * x) = (1 / x) / (k : ℝ) := by rw [div_div, mul_comm]
  have hlo : (n : ℝ) / (k : ℝ) ≤ 1 / ((k : ℝ) * x) := by
    rw [hsplit]; exact div_le_div_of_nonneg_right hx1 hk_pos.le
  have hhi : 1 / ((k : ℝ) * x) < ((n : ℝ) + 1) / (k : ℝ) := by
    rw [hsplit]; exact div_lt_div_of_pos_right hx2 hk_pos
  have hnat_lo : ((n / k : ℕ) : ℝ) ≤ (n : ℝ) / (k : ℝ) := by
    rw [le_div_iff₀ hk_pos]; exact_mod_cast Nat.div_mul_le_self n k
  have hnat_hi : ((n : ℝ) + 1) / (k : ℝ) ≤ ((n / k : ℕ) : ℝ) + 1 := by
    rw [div_le_iff₀ hk_pos]
    exact_mod_cast (by have := Nat.lt_div_mul_add (a := n) (by omega : 0 < k); linarith)
  exact Int.floor_eq_iff.mpr
    ⟨by push_cast; exact le_trans hnat_lo hlo, by push_cast; exact lt_of_lt_of_le hhi hnat_hi⟩

/-- **Pointwise Discrete-Equals-Continuous Theorem**: under `D1 c N = 0`, `n ≥ 1`, and
`n ≤ 1 / x < n + 1`, `continuousNymanResidual c N x = discreteCellResidual c N n`. -/
theorem continuousNymanResidual_eq_discreteCellResidual (c : ℕ → ℝ) (N : ℕ) {n : ℕ} (hn : 1 ≤ n)
    {x : ℝ} (hx1 : (n : ℝ) ≤ 1 / x) (hx2 : 1 / x < (n : ℝ) + 1) (hD1 : D1 c N = 0) :
    continuousNymanResidual c N x = discreteCellResidual c N n := by
  have hterm : ∀ k ∈ Finset.Icc 1 N,
      c k * Int.fract (1 / ((k : ℝ) * x)) =
        (c k / (k : ℝ)) * (1 / x) - c k * ((n / k : ℕ) : ℝ) := fun k hk => by
    rw [Int.fract, floor_one_div_mul_eq_nat_div hn (Finset.mem_Icc.mp hk).1 hx1 hx2,
      Int.cast_natCast, mul_sub, div_eq_mul_inv, mul_inv]; ring
  unfold continuousNymanResidual discreteCellResidual
  rw [Finset.sum_congr rfl hterm, Finset.sum_sub_distrib, ← Finset.sum_mul]
  change 1 - (D1 c N * (1 / x) - ∑ k ∈ Finset.Icc 1 N, c k * ((n / k : ℕ) : ℝ)) = _
  rw [hD1, zero_mul, zero_sub, sub_neg_eq_add]

/-- **Pointwise Continuous-to-Modular Duality**: under `D1 c N = 0`, `n ≥ 1`, and
`n ≤ 1 / x < n + 1`, `continuousNymanResidual c N x` equals both `discreteCellResidual c N n` and
`modularCellResidual c N n`. -/
theorem continuousNymanResidual_eq_modularCellResidual (c : ℕ → ℝ) (N : ℕ) {n : ℕ} (hn : 1 ≤ n)
    {x : ℝ} (hx1 : (n : ℝ) ≤ 1 / x) (hx2 : 1 / x < (n : ℝ) + 1) (hD1 : D1 c N = 0) :
    continuousNymanResidual c N x = discreteCellResidual c N n ∧
      continuousNymanResidual c N x = modularCellResidual c N n := by
  have hd := continuousNymanResidual_eq_discreteCellResidual c N hn hx1 hx2 hD1
  exact ⟨hd, hd.trans (discreteCellResidual_eq_modularCellResidual_of_D1_eq_zero c N n hD1)⟩

/-- On the top cell `n = 1` (`1 ≤ N`), `discreteCellResidual c N 1 = 1 + c 1`. -/
theorem discreteCellResidual_one_eq (c : ℕ → ℝ) {N : ℕ} (hN : 1 ≤ N) :
    discreteCellResidual c N 1 = 1 + c 1 := by
  have h1 : (1 : ℕ) ∈ Finset.Icc 1 N := Finset.mem_Icc.mpr ⟨le_rfl, hN⟩
  have hterm : ∀ k ∈ Finset.Icc 1 N,
      c k * ((1 / k : ℕ) : ℝ) = if k = 1 then c 1 else 0 := fun k hk => by
    rcases eq_or_ne k 1 with rfl | hne
    · simp
    · simp [hne, Nat.div_eq_of_lt (by have := (Finset.mem_Icc.mp hk).1; omega : 1 < k)]
  unfold discreteCellResidual
  rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq']; simp [h1]

/-- **Top-Half Continuum Annihilation Theorem**: for every `N ≥ 2` and every Dirichlet-anchored
vector `c` (`IsDirichletAnchored c N`), `continuousNymanResidual c N x = 0` everywhere on
`x ∈ (1 / 2, 1]`. -/
theorem continuousNymanResidual_eq_zero_on_top_half {N : ℕ} (hN : 2 ≤ N) {c : ℕ → ℝ}
    (hc : IsDirichletAnchored c N) {x : ℝ} (hx1 : (1 / 2 : ℝ) < x) (hx2 : x ≤ 1) :
    continuousNymanResidual c N x = 0 := by
  have hx_pos : 0 < x := lt_trans (by norm_num) hx1
  have hlo : ((1 : ℕ) : ℝ) ≤ 1 / x := by simpa using (one_le_div hx_pos).mpr hx2
  have hhi : 1 / x < ((1 : ℕ) : ℝ) + 1 := (div_lt_iff₀ hx_pos).mpr (by norm_num; linarith)
  rw [continuousNymanResidual_eq_discreteCellResidual c N (by omega : 1 ≤ 1) hlo hhi hc.1,
    discreteCellResidual_one_eq c (by omega : 1 ≤ N), hc.2.2]
  ring

/-- **Periodic Folding**: if `L` is a common multiple of all `k ∈ Icc 1 N`, then
`modularCellResidual c N (n + L) = modularCellResidual c N n` for every `n : ℕ`. -/
theorem modularCellResidual_periodic (c : ℕ → ℝ) (N L n : ℕ)
    (hL : ∀ k ∈ Finset.Icc 1 N, k ∣ L) :
    modularCellResidual c N (n + L) = modularCellResidual c N n := by
  unfold modularCellResidual
  congr 1
  refine Finset.sum_congr rfl fun k hk => ?_
  obtain ⟨q, rfl⟩ := hL k hk
  have hk_ne : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by have := (Finset.mem_Icc.mp hk).1; omega)
  rw [show (((n + k * q : ℕ) : ℝ) / (k : ℝ)) = (n : ℝ) / (k : ℝ) + ((q : ℤ) : ℝ) by
    push_cast; field_simp [hk_ne], Int.fract_add_intCast]

/-- **Palindromic Fractional-Part Sum**: for `1 ≤ k`, `k ∣ L`, and `m < L`,
`fract((L - 1 - m) / k) + fract(m / k) = 1 - 1 / k`. -/
theorem fract_palindromic_add_eq {k L m : ℕ} (hk : 1 ≤ k) (hdiv : k ∣ L) (hm : m < L) :
    Int.fract (((L - 1 - m : ℕ) : ℝ) / (k : ℝ)) + Int.fract ((m : ℝ) / (k : ℝ)) =
      1 - 1 / (k : ℝ) := by
  obtain ⟨q, rfl⟩ := hdiv
  set s := m / k
  set r := m % k
  have hr_lt : r < k := Nat.mod_lt m (by omega)
  have hm_eq : m = k * s + r := (Nat.div_add_mod m k).symm
  have hs1 : s + 1 ≤ q := by nlinarith
  have hk_pos : (0 : ℝ) < (k : ℝ) := Nat.cast_pos.mpr (by omega)
  have hk_ne : (k : ℝ) ≠ 0 := hk_pos.ne'
  have hm_split : (m : ℝ) / (k : ℝ) = ((s : ℤ) : ℝ) + (r : ℝ) / (k : ℝ) := by
    rw [hm_eq]; push_cast; field_simp [hk_ne]
  have hrev_real : ((k * q - 1 - m : ℕ) : ℝ) =
      (k : ℝ) * ((q - s - 1 : ℕ) : ℝ) + ((k - 1 - r : ℕ) : ℝ) := by
    rw [Nat.cast_sub (by omega : m ≤ k * q - 1), Nat.cast_sub (by nlinarith : 1 ≤ k * q),
      Nat.cast_sub (by omega : 1 ≤ q - s), Nat.cast_sub (by omega : s ≤ q),
      Nat.cast_sub (by omega : r ≤ k - 1), Nat.cast_sub hk, hm_eq]
    push_cast; ring
  have hrev_split : ((k * q - 1 - m : ℕ) : ℝ) / (k : ℝ) =
      (((q - s - 1 : ℕ) : ℤ) : ℝ) + ((k - 1 - r : ℕ) : ℝ) / (k : ℝ) := by
    rw [hrev_real]; push_cast; field_simp [hk_ne]
  have hfm : Int.fract ((m : ℝ) / (k : ℝ)) = (r : ℝ) / (k : ℝ) := by
    rw [hm_split, Int.fract_intCast_add, Int.fract_eq_self]
    exact ⟨div_nonneg (Nat.cast_nonneg _) hk_pos.le,
      (div_lt_one hk_pos).mpr (Nat.cast_lt.mpr hr_lt)⟩
  have hfr : Int.fract (((k * q - 1 - m : ℕ) : ℝ) / (k : ℝ)) =
      ((k - 1 - r : ℕ) : ℝ) / (k : ℝ) := by
    rw [hrev_split, Int.fract_intCast_add, Int.fract_eq_self]
    exact ⟨div_nonneg (Nat.cast_nonneg _) hk_pos.le,
      (div_lt_one hk_pos).mpr (by exact_mod_cast (by omega : k - 1 - r < k))⟩
  rw [hfr, hfm, Nat.cast_sub (by omega : r ≤ k - 1), Nat.cast_sub hk]
  push_cast; field_simp [hk_ne]; ring

/-- **Palindromic Antisymmetry on `A_N`**: under `D1 c N = 0` and `D0 c N = 2`, if `L` is a common
multiple of `1..N`, then `modularCellResidual c N (L - 1 - m) = -modularCellResidual c N m` for all
`m < L`. -/
theorem modularCellResidual_palindromic_neg (c : ℕ → ℝ) (N L m : ℕ) (hD1 : D1 c N = 0)
    (hD0 : D0 c N = 2) (hL : ∀ k ∈ Finset.Icc 1 N, k ∣ L) (hm : m < L) :
    modularCellResidual c N (L - 1 - m) = -modularCellResidual c N m := by
  have hsum : modularCellResidual c N (L - 1 - m) + modularCellResidual c N m = 0 := by
    have hpt : ∀ k ∈ Finset.Icc 1 N,
        c k * Int.fract (((L - 1 - m : ℕ) : ℝ) / (k : ℝ)) +
          c k * Int.fract ((m : ℝ) / (k : ℝ)) = c k - c k / (k : ℝ) := fun k hk => by
      rw [← mul_add, fract_palindromic_add_eq (Finset.mem_Icc.mp hk).1 (hL k hk) hm]; ring
    unfold modularCellResidual
    have hcomb :
        (1 - ∑ k ∈ Finset.Icc 1 N, c k * Int.fract (((L - 1 - m : ℕ) : ℝ) / (k : ℝ))) +
          (1 - ∑ k ∈ Finset.Icc 1 N, c k * Int.fract ((m : ℝ) / (k : ℝ))) =
          2 - ∑ k ∈ Finset.Icc 1 N, (c k - c k / (k : ℝ)) := by
      rw [← Finset.sum_congr rfl hpt, Finset.sum_add_distrib]; ring
    rw [hcomb, Finset.sum_sub_distrib]
    change 2 - (D0 c N - D1 c N) = 0
    rw [hD0, hD1]; ring
  linarith

/-- **Zero Mean Over Every Period**: under `D1 c N = 0` and `D0 c N = 2`, the sum of
`modularCellResidual c N m` over `m ∈ Ico 0 L` vanishes identically. -/
theorem sum_Ico_modularCellResidual_eq_zero (c : ℕ → ℝ) (N L : ℕ) (hD1 : D1 c N = 0)
    (hD0 : D0 c N = 2) (hL : ∀ k ∈ Finset.Icc 1 N, k ∣ L) :
    ∑ m ∈ Finset.Ico 0 L, modularCellResidual c N m = 0 := by
  have href : ∑ m ∈ Finset.Ico 0 L, modularCellResidual c N (L - 1 - m) =
      ∑ m ∈ Finset.Ico 0 L, modularCellResidual c N m :=
    Finset.sum_bij (fun m _ => L - 1 - m)
      (fun m hm => Finset.mem_Ico.mpr ⟨Nat.zero_le _, by have := (Finset.mem_Ico.mp hm).2; omega⟩)
      (fun a ha b hb hab => by
        have := (Finset.mem_Ico.mp ha).2; have := (Finset.mem_Ico.mp hb).2; omega)
      (fun b hb => ⟨L - 1 - b, Finset.mem_Ico.mpr ⟨Nat.zero_le _, by
        have := (Finset.mem_Ico.mp hb).2; omega⟩, by
        have := (Finset.mem_Ico.mp hb).2; omega⟩)
      (fun _ _ => rfl)
  have hneg : ∑ m ∈ Finset.Ico 0 L, modularCellResidual c N (L - 1 - m) =
      -∑ m ∈ Finset.Ico 0 L, modularCellResidual c N m := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun m hm =>
      modularCellResidual_palindromic_neg c N L m hD1 hD0 hL (Finset.mem_Ico.mp hm).2
  linarith
