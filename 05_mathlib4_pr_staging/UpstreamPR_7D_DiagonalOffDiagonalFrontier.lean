/-
Copyright (c) 2026 Qamar Munawer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qamar Munawer
-/
module

public import RiemannBlueprint.UpstreamPRs.UpstreamPR_7C_PurePlaqueReduction

/-!
# Diagonal Positivity and Off-Diagonal Cancellation Frontier on `A_N`

This module decomposes the dipole Gram quadratic energy `QCot vasyuninGCot h N` cleanly into its
strictly non-negative diagonal dipole energy and its off-diagonal cross-interaction energy:

* `dipoleDiagEnergy`: positive diagonal energy of `dipoleCoord` against `dipoleGramEntry m m`.
* `dipoleOffDiagEnergy`: off-diagonal interaction energy
  `∑ a, ∑ b ∈ (Icc 1 (N - 2)).erase a, α a * α b * dipoleGramEntry a b`.
* `dipoleDiagEnergy_nonneg`: unconditional non-negativity of `dipoleDiagEnergy` via
  `dipoleGramEntry_diag_nonneg`.
* `QCot_eq_dipoleDiagEnergy_add_dipoleOffDiagEnergy`: exact diagonal + off-diagonal splitting of
  `QCot` on `A_N⁰` for all `N ≥ 2`.
* `dipoleOffDiagEnergy_le_one_sub_dipoleDiagEnergy_of_mem_A_N`: necessary off-diagonal
  cancellation inequality whenever `SCot vasyuninGCot c N ≥ 0` on `A_N`.
-/

@[expose] public section

open scoped BigOperators

/-- Positive diagonal dipole energy `∑ m ∈ Icc 1 (N - 2), αₘ² * dipoleGramEntry m m`. -/
noncomputable def dipoleDiagEnergy (h : ℕ → ℝ) (N : ℕ) : ℝ :=
  ∑ m ∈ Finset.Icc 1 (N - 2), (dipoleCoord h N m) ^ 2 * dipoleGramEntry m m

/-- Off-diagonal dipole cross-energy over ordered pairs `a ≠ b` in `Icc 1 (N - 2)`. -/
noncomputable def dipoleOffDiagEnergy (h : ℕ → ℝ) (N : ℕ) : ℝ :=
  ∑ a ∈ Finset.Icc 1 (N - 2), ∑ b ∈ (Finset.Icc 1 (N - 2)).erase a,
    dipoleCoord h N a * dipoleCoord h N b * dipoleGramEntry a b

/-- Unconditional non-negativity of `dipoleDiagEnergy h N` for every vector `h` and cutoff `N`. -/
theorem dipoleDiagEnergy_nonneg {N : ℕ} (h : ℕ → ℝ) : 0 ≤ dipoleDiagEnergy h N := by
  unfold dipoleDiagEnergy
  refine Finset.sum_nonneg fun m hm => ?_
  exact mul_nonneg (sq_nonneg _) (dipoleGramEntry_diag_nonneg (Finset.mem_Icc.mp hm).1)

/-- Exact diagonal + off-diagonal splitting of `QCot vasyuninGCot h N` on `A_N⁰` for all
`N ≥ 2`. -/
theorem QCot_eq_dipoleDiagEnergy_add_dipoleOffDiagEnergy {N : ℕ} (hN : 2 ≤ N) (h : ℕ → ℝ)
    (hh1 : D1 h N = 0) (hh0 : D0 h N = 0) :
    QCot vasyuninGCot h N = dipoleDiagEnergy h N + dipoleOffDiagEnergy h N := by
  rw [QCot_eq_sum_dipoleGramEntry hN h hh1 hh0]
  unfold dipoleDiagEnergy dipoleOffDiagEnergy
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a ha => ?_
  have hsplit := Finset.add_sum_erase (Finset.Icc 1 (N - 2))
    (fun b => dipoleCoord h N a * dipoleCoord h N b * dipoleGramEntry a b) ha
  rw [← hsplit]
  ring

/-- Off-diagonal cancellation frontier on `A_N`: for `N ≥ 2`, `c ∈ A_N` (`h = c - cBaseAnchor`),
non-negativity `0 ≤ SCot vasyuninGCot c N` forces
`dipoleOffDiagEnergy h N ≤ 2 * π * linearCotDrive h N - dipoleDiagEnergy h N`. -/
theorem dipoleOffDiagEnergy_le_one_sub_dipoleDiagEnergy_of_mem_A_N {N : ℕ} (hN : 2 ≤ N)
    (c : ℕ → ℝ) (hc1 : D1 c N = 0) (hc0 : D0 c N = 2)
    (hS : 0 ≤ SCot vasyuninGCot c N) :
    let h : ℕ → ℝ := fun k => c k - cBaseAnchor k
    dipoleOffDiagEnergy h N ≤ 2 * Real.pi * linearCotDrive h N - dipoleDiagEnergy h N := by
  intro h
  have ht := sub_cBaseAnchor_mem_tangent hN c hc1 hc0
  have hc_eq : c = fun k => cBaseAnchor k + h k := funext fun k => by dsimp [h]; ring
  have hS_eq : SCot vasyuninGCot c N =
      -QCot vasyuninGCot h N + 2 * Real.pi * linearCotDrive h N := by
    conv_lhs => rw [hc_eq]
    rw [SCot_cBaseAnchor_add_eq hN h]
    unfold SCot linearCotDrive
    rfl
  rw [hS_eq, QCot_eq_dipoleDiagEnergy_add_dipoleOffDiagEnergy hN h ht.1 ht.2] at hS
  linarith

/-- Symmetric corollary on the total cotangent discrepancy:
`SCot vasyuninGCot c N = 2 * π * L - (D + O)` for every `N ≥ 2` and `c ∈ A_N`. -/
theorem SCot_eq_drive_sub_diag_sub_offDiag {N : ℕ} (hN : 2 ≤ N) (c : ℕ → ℝ)
    (hc1 : D1 c N = 0) (hc0 : D0 c N = 2) :
    let h : ℕ → ℝ := fun k => c k - cBaseAnchor k
    SCot vasyuninGCot c N =
      2 * Real.pi * linearCotDrive h N - dipoleDiagEnergy h N - dipoleOffDiagEnergy h N := by
  intro h
  have ht := sub_cBaseAnchor_mem_tangent hN c hc1 hc0
  have hc_eq : c = fun k => cBaseAnchor k + h k := funext fun k => by dsimp [h]; ring
  have hS_eq : SCot vasyuninGCot c N =
      -QCot vasyuninGCot h N + 2 * Real.pi * linearCotDrive h N := by
    conv_lhs => rw [hc_eq]
    rw [SCot_cBaseAnchor_add_eq hN h]
    unfold SCot linearCotDrive
    rfl
  rw [hS_eq, QCot_eq_dipoleDiagEnergy_add_dipoleOffDiagEnergy hN h ht.1 ht.2]
  ring
