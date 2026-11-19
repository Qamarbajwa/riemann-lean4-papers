/-
Copyright (c) 2026 Qamar Munawer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qamar Munawer
-/
module

public import RiemannBlueprint.Modules.HarmonicCellL2QuadratureAndPrimeJumps

/-!
# Periodic L² Cell-Sum Compression Across Residue Classes Modulo L_N

This module proves iterated periodicity, full-period finite-sum factorization over `Finset.range`
and `Finset.Ico`, and exact chunking of weighted squared `modularCellResidual` sums across `K`
consecutive LCM periods `L`, collapsing `(K * L)`-cell sums onto a single fundamental period
`m ∈ [0, L)`.
-/

@[expose] public section

namespace BaezDuarte

open scoped BigOperators

/-- Iterated periodicity: if `f (n + L) = f n` for all `n`, then `f (n + k * L) = f n` for every
`k : ℕ`. -/
theorem f_add_mul_period_eq {α : Type*} (f : ℕ → α) (L : ℕ)
    (h_per : ∀ n, f (n + L) = f n) (n k : ℕ) : f (n + k * L) = f n := by
  induction k with
  | zero => simp
  | succ i ih =>
    rw [show n + (i + 1) * L = (n + i * L) + L by ring, h_per, ih]

/-- Double-sum chunking identity: any sum over `range (K * L)` splits into `K` blocks of length
`L`, `∑ i ∈ range (K * L), g i = ∑ k ∈ range K, ∑ m ∈ range L, g (m + k * L)`. -/
theorem sum_range_mul_chunk {α : Type*} [AddCommMonoid α] (g : ℕ → α) (L K : ℕ) :
    ∑ i ∈ Finset.range (K * L), g i =
      ∑ k ∈ Finset.range K, ∑ m ∈ Finset.range L, g (m + k * L) := by
  induction K with
  | zero => simp
  | succ k ih =>
    rw [Nat.succ_mul, Finset.sum_range_add, ih, Finset.sum_range_succ]
    congr 1
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [Nat.add_comm (k * L) m]

/-- Sum of an `L`-periodic function over `K * L` terms equals `K` times its single-period sum
over `Finset.range L`. -/
theorem sum_range_mul_period_eq_mul_sum_range {α : Type*} [Semiring α] (f : ℕ → α) (L K : ℕ)
    (h_per : ∀ n, f (n + L) = f n) :
    ∑ i ∈ Finset.range (K * L), f i = (K : α) * ∑ m ∈ Finset.range L, f m := by
  induction K with
  | zero => simp
  | succ k ih =>
    have hterm : ∑ m ∈ Finset.range L, f (k * L + m) = ∑ m ∈ Finset.range L, f m := by
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [Nat.add_comm (k * L) m]
      exact f_add_mul_period_eq f L h_per m k
    rw [Nat.succ_mul, Finset.sum_range_add, ih, hterm, Nat.cast_succ, add_mul, one_mul]

/-- Extension of periodic sum factorization to any shifted interval `Ico (a * L) ((a + K) * L)`. -/
theorem sum_Ico_mul_period_eq_mul_sum_Ico {α : Type*} [Semiring α] (f : ℕ → α) (L a K : ℕ)
    (h_per : ∀ n, f (n + L) = f n) :
    ∑ i ∈ Finset.Ico (a * L) ((a + K) * L), f i = (K : α) * ∑ m ∈ Finset.Ico 0 L, f m := by
  have hsub : (a + K) * L - a * L = K * L := by rw [Nat.add_mul, Nat.add_sub_cancel_left]
  rw [Finset.sum_Ico_eq_sum_range, hsub, Nat.Ico_zero_eq_range]
  have hterm : ∑ i ∈ Finset.range (K * L), f (a * L + i) = ∑ i ∈ Finset.range (K * L), f i := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Nat.add_comm (a * L) i]
    exact f_add_mul_period_eq f L h_per i a
  rw [hterm]
  exact sum_range_mul_period_eq_mul_sum_range f L K h_per

/-- Iterated LCM periodicity of `modularCellResidual`:
`modularCellResidual c N (n + k * L) = modularCellResidual c N n`. -/
theorem modularCellResidual_periodic_iter (c : ℕ → ℝ) (N n L k : ℕ)
    (hL : ∀ d ∈ Finset.Icc 1 N, d ∣ L) :
    modularCellResidual c N (n + k * L) = modularCellResidual c N n :=
  f_add_mul_period_eq (modularCellResidual c N) L
    (fun m => modularCellResidual_periodic c N L m hL) n k

/-- **Multi-Period Weighted L² Cell Compression**: summing squared modular residuals with weight
`1 / (i * (i + 1))` over `K * L` indices groups cleanly onto fundamental residue classes
`m ∈ [0, L)` with constant numerator `modularCellResidual c N m ^ 2`. -/
theorem modularCellResidual_sum_multi_period (c : ℕ → ℝ) (N L K : ℕ)
    (hL : ∀ d ∈ Finset.Icc 1 N, d ∣ L) :
    ∑ i ∈ Finset.range (K * L), (modularCellResidual c N i) ^ 2 / ((i : ℝ) * ((i : ℝ) + 1)) =
      ∑ k ∈ Finset.range K, ∑ m ∈ Finset.range L,
        (modularCellResidual c N m) ^ 2 /
          (((m + k * L : ℕ) : ℝ) * (((m + k * L : ℕ) : ℝ) + 1)) := by
  rw [sum_range_mul_chunk (fun i =>
    (modularCellResidual c N i) ^ 2 / ((i : ℝ) * ((i : ℝ) + 1))) L K]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun m _ => ?_
  rw [modularCellResidual_periodic_iter c N m L k hL]

/-- Shifted multi-period quadrature identity in terms of `harmonicCellWidth`: for positive offset
`a ≥ 1` and `D1 c N = 0`, integrating/summing `(discreteCellResidual c N i)^2 * harmonicCellWidth i`
over `Ico (a * L) ((a + K) * L)` compresses to fundamental modular classes `m ∈ [0, L)`. -/
theorem discreteCellResidual_sq_width_sum_Ico (c : ℕ → ℝ) (N L a K : ℕ)
    (hL : ∀ d ∈ Finset.Icc 1 N, d ∣ L) (hD1 : D1 c N = 0) :
    ∑ i ∈ Finset.Ico (a * L) ((a + K) * L),
        (discreteCellResidual c N i) ^ 2 * harmonicCellWidth i =
      ∑ k ∈ Finset.range K, ∑ m ∈ Finset.range L,
        (modularCellResidual c N m) ^ 2 * harmonicCellWidth (m + (a + k) * L) := by
  have hsub : (a + K) * L - a * L = K * L := by rw [Nat.add_mul, Nat.add_sub_cancel_left]
  rw [Finset.sum_Ico_eq_sum_range, hsub]
  rw [sum_range_mul_chunk (fun i =>
    (discreteCellResidual c N (a * L + i)) ^ 2 * harmonicCellWidth (a * L + i)) L K]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun m _ => ?_
  have hidx : a * L + (m + k * L) = m + (a + k) * L := by ring
  rw [hidx, discreteCellResidual_eq_modularCellResidual_of_D1_eq_zero c N _ hD1,
    modularCellResidual_periodic_iter c N m L (a + k) hL]

end BaezDuarte
