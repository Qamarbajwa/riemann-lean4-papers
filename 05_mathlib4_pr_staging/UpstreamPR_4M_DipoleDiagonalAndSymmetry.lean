/-
Copyright (c) 2026 Qamar Munawer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qamar Munawer
-/
module

public import RiemannBlueprint.UpstreamPRs.UpstreamPR_4L_DipoleQuadraticReduction

/-!
# Symmetry, Single-Pair Diagonal Collapse, and Unconditional Non-Negativity of `dipoleGramEntry`

This file develops the symmetry, diagonal sparsity, and positivity theory of the `N`-independent
4-point dipole Gram kernel `dipoleGramEntry`:

* `dipoleGramEntry_comm`: exact symmetry `dipoleGramEntry a b = dipoleGramEntry b a`.
* `dipoleGramEntry_diag_eq`: collapse of the diagonal 4-point plaque to the single adjacent
  pair `(m + 1, m + 2)`: `π * (deltaCot (m + 2) - deltaCot (m + 1)) - 2 * K (m + 1) (m + 2)`.
* `QCot_cumulativeDipole_eq_dipoleGramEntry_diag` and `dipoleGramEntry_diag_nonneg`: identification
  with `QCot vasyuninGCot (cumulativeDipole m) N` and unconditional positivity
  `0 ≤ dipoleGramEntry m m` for all `1 ≤ m`.
* `dipoleGramEntry_one_one_eq`, `dipoleGramEntry_two_two_eq`, `dipoleGramEntry_one_two_eq_zero`:
  exact values `π / √3`, `(1 - 1 / √3) * π`, and `0` on `m, n ∈ {1, 2}`.
-/

@[expose] public section

open scoped BigOperators

/-- Symmetry of the 4-point dipole Gram kernel entry:
`dipoleGramEntry a b = dipoleGramEntry b a`. -/
theorem dipoleGramEntry_comm (a b : ℕ) : dipoleGramEntry a b = dipoleGramEntry b a := by
  unfold dipoleGramEntry
  rw [unweightedKCot_comm (a + 1) (b + 1), unweightedKCot_comm (a + 1) (b + 2),
    unweightedKCot_comm (a + 2) (b + 1), unweightedKCot_comm (a + 2) (b + 2)]
  ring

/-- Single-pair diagonal collapse of `dipoleGramEntry`: on the diagonal `a = b = m`, the
4-point plaque reduces to `π * (deltaCot (m + 2) - deltaCot (m + 1)) - 2 * K (m + 1) (m + 2)`. -/
theorem dipoleGramEntry_diag_eq (m : ℕ) :
    dipoleGramEntry m m =
      Real.pi * (deltaCot (m + 2) - deltaCot (m + 1)) - 2 * unweightedKCot (m + 1) (m + 2) := by
  unfold dipoleGramEntry
  rw [unweightedKCot_diag (m + 1), unweightedKCot_diag (m + 2),
    unweightedKCot_comm (m + 2) (m + 1)]
  ring

/-- Exact bridge equating the cotangent quadratic energy of `cumulativeDipole m` at any truncation
`N ≥ m + 2` to the `N`-independent diagonal entry `dipoleGramEntry m m`. -/
theorem QCot_cumulativeDipole_eq_dipoleGramEntry_diag {m N : ℕ} (hm : 1 ≤ m) (hN : m + 2 ≤ N) :
    QCot vasyuninGCot (cumulativeDipole m) N = dipoleGramEntry m m := by
  unfold QCot
  exact sum_cumulativeDipole_vasyuninGCot_eq_four_point hm hm hN hN

/-- Unconditional diagonal non-negativity of the dipole Gram kernel for every `1 ≤ m`, proved
by choosing `N = m + 2` and invoking `QCot_nonneg_of_mem_tangent`. -/
theorem dipoleGramEntry_diag_nonneg {m : ℕ} (hm : 1 ≤ m) : 0 ≤ dipoleGramEntry m m := by
  have ht := cumulativeDipole_mem_tangent hm (le_rfl : m + 2 ≤ m + 2)
  rw [← QCot_cumulativeDipole_eq_dipoleGramEntry_diag hm (le_rfl : m + 2 ≤ m + 2)]
  exact QCot_nonneg_of_mem_tangent (cumulativeDipole m) ht.1 ht.2

/-- Exact value of the first diagonal dipole Gram entry: `dipoleGramEntry 1 1 = π / √3`. -/
theorem dipoleGramEntry_one_one_eq : dipoleGramEntry 1 1 = Real.pi / Real.sqrt 3 := by
  have h1 : cumulativeDipole 1 = harmonicWavelet 1 := by
    funext k
    simp [cumulativeDipole]
  rw [← QCot_cumulativeDipole_eq_dipoleGramEntry_diag (by omega : 1 ≤ 1) (by omega : 1 + 2 ≤ 3),
    h1, QCot_harmonicWavelet_one_eq]

/-- Exact value of the second diagonal dipole Gram entry:
`dipoleGramEntry 2 2 = (1 - 1 / √3) * π`. -/
theorem dipoleGramEntry_two_two_eq :
    dipoleGramEntry 2 2 = (1 - 1 / Real.sqrt 3) * Real.pi := by
  rw [← QCot_cumulativeDipole_eq_dipoleGramEntry_diag (by omega : 1 ≤ 2) (by omega : 2 + 2 ≤ 4),
    QCot_cumulativeDipole_two_eq]

/-- Exact off-diagonal vanishing `dipoleGramEntry 1 2 = 0` reflecting `d₁ ⊥ d₂` under `G`. -/
theorem dipoleGramEntry_one_two_eq_zero : dipoleGramEntry 1 2 = 0 := by
  have h := sum_cumulativeDipole_vasyuninGCot_eq_four_point (by omega : 1 ≤ 1)
    (by omega : 1 ≤ 2) (by omega : 1 + 2 ≤ 4) (by omega : 2 + 2 ≤ 4)
  change _ = dipoleGramEntry 1 2 at h
  rw [← h, sum_cumulativeDipole_one_two_vasyuninGCot_eq_zero]
