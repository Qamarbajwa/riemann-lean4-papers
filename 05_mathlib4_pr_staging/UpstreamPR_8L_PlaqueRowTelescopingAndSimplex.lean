/-
Copyright (c) 2026 Qamar Munawer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qamar Munawer
-/
module

public import RiemannBlueprint.UpstreamPRs.UpstreamPR_8K_SuperdiagonalAndOrthogonalTriple

/-!
# 1D Plaque Row-Sum Telescoping and Graph-Laplacian Simplex Decomposition

This module proves:
* `sum_Icc_deltaCot_diff_eq`: telescoping of linear cotangent drive steps to `deltaCot N`.
* `sum_Icc_dipolePlaqueEntry_right_eq`, `sum_Icc_dipolePlaqueEntry_self_eq`: 1D row-sum and 2D
  total plaque telescoping to `-2 * unweightedKCot N 2 = π * vasyuninCotSum N 2`.
* `sum_Icc_unitDefectEntry_right_eq`: exact row sum of `unitDefectEntry`.
* `sum_mul_mul_eq_row_sum_sub_half_sq_sub`,
  `one_sub_SCot_eq_row_sum_sub_half_sq_sub_of_isDirichletAnchored`: symmetric Graph-Laplacian /
  pairwise-difference decomposition of `1 - SCot vasyuninGCot c N` on `IsDirichletAnchored c N`.
-/

@[expose] public section

open scoped BigOperators

private lemma sum_Icc_sub_succ (f : ℕ → ℝ) (k : ℕ) :
    ∑ m ∈ Finset.Icc 1 k, (f (m + 1) - f m) = f (k + 1) - f 1 := by
  induction k with
  | zero => simp
  | succ n ih =>
    rw [show Finset.Icc 1 (n + 1) = insert (n + 1) (Finset.Icc 1 n) by
      ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega,
      Finset.sum_insert (by simp), ih]
    ring

private lemma vasyuninCotSum_two_8l (b : ℕ) : vasyuninCotSum 2 b = 0 := by
  unfold vasyuninCotSum
  rw [show Finset.Ico 1 2 = ({1} : Finset ℕ) by ext x; simp, Finset.sum_singleton,
    show Real.pi * ((1 : ℕ) : ℝ) / ((2 : ℕ) : ℝ) = Real.pi / 2 by push_cast; ring,
    Real.cos_pi_div_two, zero_div, mul_zero]

private lemma deltaCot_two_eq_zero_8l : deltaCot 2 = 0 := by
  unfold deltaCot; rw [vasyuninCotSum_two_8l, vasyuninCotSum_two_8l, sub_self]

/-- **1D Linear-Drive Telescoping**: `∑ m ∈ Icc 1 (N - 2), (δ(m + 2) - δ(m + 1)) = δ(N)`. -/
theorem sum_Icc_deltaCot_diff_eq {N : ℕ} (hN : 2 ≤ N) :
    ∑ m ∈ Finset.Icc 1 (N - 2), (deltaCot (m + 2) - deltaCot (m + 1)) = deltaCot N := by
  have h := sum_Icc_sub_succ (fun k => deltaCot (k + 1)) (N - 2)
  rw [show N - 2 + 1 = N - 1 by omega, show (1 : ℕ) + 1 = 2 by decide, deltaCot_two_eq_zero_8l,
    sub_zero] at h
  rcases eq_or_lt_of_le hN with rfl | hN3
  · simp [deltaCot_two_eq_zero_8l]
  · rw [show N - 1 + 1 = N by omega] at h; simpa [Nat.add_assoc] using h

/-- **1D Plaque Row-Sum Telescoping** across `b ∈ Icc 1 (N - 2)` for `3 ≤ N`. -/
theorem sum_Icc_dipolePlaqueEntry_right_eq (a : ℕ) {N : ℕ} (hN : 3 ≤ N) :
    ∑ b ∈ Finset.Icc 1 (N - 2), dipolePlaqueEntry a b =
      (unweightedKCot (a + 1) 2 - unweightedKCot (a + 2) 2) -
        (unweightedKCot (a + 1) N - unweightedKCot (a + 2) N) := by
  let g : ℕ → ℝ := fun k => unweightedKCot (a + 1) k - unweightedKCot (a + 2) k
  have hp : ∀ b, dipolePlaqueEntry a b = -(g (b + 2) - g (b + 1)) := fun b => by
    dsimp [g]; unfold dipolePlaqueEntry; ring
  simp_rw [hp, Finset.sum_neg_distrib]
  have h := sum_Icc_sub_succ (fun k => g (k + 1)) (N - 2)
  rw [show N - 2 + 1 + 1 = N by omega, show (1 : ℕ) + 1 = 2 by decide] at h
  dsimp [g] at h; linarith

/-- **2D Total Plaque Sum Identity**: `∑ a, ∑ b, P(a, b) = -2 * K(N, 2) = π * V(N, 2)`. -/
theorem sum_Icc_dipolePlaqueEntry_self_eq {N : ℕ} (hN : 3 ≤ N) :
    (∑ a ∈ Finset.Icc 1 (N - 2), ∑ b ∈ Finset.Icc 1 (N - 2), dipolePlaqueEntry a b =
      -2 * unweightedKCot N 2) ∧
    (∑ a ∈ Finset.Icc 1 (N - 2), ∑ b ∈ Finset.Icc 1 (N - 2), dipolePlaqueEntry a b =
      Real.pi * vasyuninCotSum N 2) := by
  have hrow : ∀ a ∈ Finset.Icc 1 (N - 2),
      ∑ b ∈ Finset.Icc 1 (N - 2), dipolePlaqueEntry a b =
        (-(unweightedKCot (a + 2) 2 - unweightedKCot (a + 1) 2)) +
          (unweightedKCot (a + 2) N - unweightedKCot (a + 1) N) := fun a _ => by
    rw [sum_Icc_dipolePlaqueEntry_right_eq a hN]; ring
  have h2 := sum_Icc_sub_succ (fun k => unweightedKCot (k + 1) 2) (N - 2)
  have hNsum := sum_Icc_sub_succ (fun k => unweightedKCot (k + 1) N) (N - 2)
  rw [show N - 2 + 1 + 1 = N by omega, show (1 : ℕ) + 1 = 2 by decide] at h2 hNsum
  simp only [show ∀ x : ℕ, x + 1 + 1 = x + 2 from fun _ => rfl] at h2 hNsum
  have hS : ∑ a ∈ Finset.Icc 1 (N - 2), ∑ b ∈ Finset.Icc 1 (N - 2), dipolePlaqueEntry a b =
      -2 * unweightedKCot N 2 := by
    rw [Finset.sum_congr rfl hrow, Finset.sum_add_distrib, Finset.sum_neg_distrib, h2, hNsum,
      unweightedKCot_two_two_eq_zero, unweightedKCot_diag N, unweightedKCot_comm 2 N]; ring
  have hK : unweightedKCot N 2 = -(Real.pi / 2) * vasyuninCotSum N 2 := by
    have hNpos : ((N : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    unfold unweightedKCot vasyuninGCot
    rw [vasyuninCotSum_two_8l N, add_zero]; push_cast; field_simp [hNpos]
  exact ⟨hS, by rw [hS, hK]; ring⟩

/-- Exact row sum of `unitDefectEntry` across `b ∈ Icc 1 (N - 2)` for `3 ≤ N`. -/
theorem sum_Icc_unitDefectEntry_right_eq (a : ℕ) {N : ℕ} (hN : 3 ≤ N) :
    ∑ b ∈ Finset.Icc 1 (N - 2), unitDefectEntry a b =
      ((N - 2 : ℕ) : ℝ) * (1 - (Real.pi / 2) * (deltaCot (a + 2) - deltaCot (a + 1))) -
        (Real.pi / 2) * deltaCot N +
        ∑ b ∈ Finset.Icc 1 (N - 2), dipolePlaqueEntry a b := by
  have hu : ∀ b, unitDefectEntry a b =
      (1 - (Real.pi / 2) * (deltaCot (a + 2) - deltaCot (a + 1))) -
        (Real.pi / 2) * (deltaCot (b + 2) - deltaCot (b + 1)) + dipolePlaqueEntry a b := fun b => by
    unfold unitDefectEntry; ring
  simp_rw [hu, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const, Nat.card_Icc,
    show N - 2 + 1 - 1 = N - 2 by omega, nsmul_eq_mul, ← Finset.mul_sum,
    sum_Icc_deltaCot_diff_eq (by omega : 2 ≤ N)]; ring

/-- **Symmetric Graph-Laplacian Quadratic Identity** on any `S : Finset ℕ`. -/
theorem sum_mul_mul_eq_row_sum_sub_half_sq_sub (S : Finset ℕ) (α : ℕ → ℝ)
    (M : ℕ → ℕ → ℝ) (hM : ∀ a b, M a b = M b a) :
    ∑ a ∈ S, ∑ b ∈ S, α a * α b * M a b =
      ∑ a ∈ S, (α a) ^ 2 * (∑ b ∈ S, M a b) -
        (1 / 2 : ℝ) * ∑ a ∈ S, ∑ b ∈ S, (α a - α b) ^ 2 * M a b := by
  have hexp : ∀ a b, (α a - α b) ^ 2 * M a b =
      (α a) ^ 2 * M a b + (α b) ^ 2 * M a b - 2 * (α a * α b * M a b) := fun a b => by ring
  have hswap : ∑ a ∈ S, ∑ b ∈ S, (α b) ^ 2 * M a b =
      ∑ a ∈ S, ∑ b ∈ S, (α a) ^ 2 * M a b := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by rw [hM b a]
  simp_rw [hexp, Finset.sum_sub_distrib, Finset.sum_add_distrib, hswap, ← Finset.mul_sum]
  ring

/-- **Graph-Laplacian Simplex Decomposition** of `1 - SCot(c, N)` on `IsDirichletAnchored c N`. -/
theorem one_sub_SCot_eq_row_sum_sub_half_sq_sub_of_isDirichletAnchored {N : ℕ} (hN : 2 ≤ N)
    {c : ℕ → ℝ} (hc : IsDirichletAnchored c N) :
    1 - SCot vasyuninGCot c N =
      ∑ a ∈ Finset.Icc 1 (N - 2), (dipoleCoord c N a) ^ 2 *
          (∑ b ∈ Finset.Icc 1 (N - 2), unitDefectEntry a b) -
        (1 / 2 : ℝ) * ∑ a ∈ Finset.Icc 1 (N - 2), ∑ b ∈ Finset.Icc 1 (N - 2),
          (dipoleCoord c N a - dipoleCoord c N b) ^ 2 * unitDefectEntry a b := by
  rw [one_sub_SCot_eq_sum_unitDefectEntry_of_isDirichletAnchored hN hc]
  exact sum_mul_mul_eq_row_sum_sub_half_sq_sub (Finset.Icc 1 (N - 2)) (dipoleCoord c N)
    unitDefectEntry unitDefectEntry_comm
