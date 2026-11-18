/-
Copyright (c) 2026 Qamar Munawer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qamar Munawer
-/
module

public import RiemannBlueprint.UpstreamPRs.UpstreamPR_4H_WaveletRayleighRHCriterion
public import RiemannBlueprint.UpstreamPRs.UpstreamPR_7D_DiagonalOffDiagonalFrontier

/-!
# Pure Plaque Quadratic Form and Cauchy–Schwarz Lower Bound on `A_N⁰`

This module defines the total pure plaque quadratic form `dipolePlaqueForm` on `A_N⁰` and
derives its unconditional Cauchy–Schwarz lower bound from `sq_linearCotDrive_le_qcot`:

* `dipolePlaqueForm`: bilinear form `∑ a, ∑ b ∈ Icc 1 (N - 2), η_a η_b P_cot(a, b)`.
* `QCot_eq_h_one_mul_drive_add_dipolePlaqueForm` and
  `SCot_eq_neg_c_one_mul_drive_sub_dipolePlaqueForm`: boundary-plus-plaque decompositions.
* `sq_linearCotDrive_sub_le_dipolePlaqueForm`: unconditional plaque Cauchy–Schwarz inequality
  `(π * L_cot(h, N)) ^ 2 - π * h 1 * L_cot(h, N) ≤ dipolePlaqueForm h N`.
* `neg_h_one_sq_div_four_le_dipolePlaqueForm`: universal plaque floor
  `-(h 1) ^ 2 / 4 ≤ dipolePlaqueForm h N` for every `h ∈ A_N⁰`.
* `one_sub_h_one_le_dipolePlaqueForm_of_unit_drive`: unit-drive (`π * L_cot(h, N) = 1`) bound
  `1 - h 1 ≤ dipolePlaqueForm h N`.
-/

@[expose] public section

open scoped BigOperators
open Finset

/-- Total pure plaque quadratic form `∑ a, ∑ b ∈ Icc 1 (N - 2), η_a η_b P_cot(a, b)` on
dipole coordinates `η_a = dipoleCoord h N a`. -/
noncomputable def dipolePlaqueForm (h : ℕ → ℝ) (N : ℕ) : ℝ :=
  ∑ a ∈ Finset.Icc 1 (N - 2), ∑ b ∈ Finset.Icc 1 (N - 2),
    dipoleCoord h N a * dipoleCoord h N b * dipolePlaqueEntry a b

/-- Boundary-plus-plaque split of `QCot` on the tangent space `A_N⁰`. -/
theorem QCot_eq_h_one_mul_drive_add_dipolePlaqueForm {N : ℕ} (hN : 2 ≤ N) (h : ℕ → ℝ)
    (hh1 : D1 h N = 0) (hh0 : D0 h N = 0) :
    QCot vasyuninGCot h N =
      Real.pi * h 1 * linearCotDrive h N + dipolePlaqueForm h N :=
  QCot_eq_h_one_mul_linearCotDrive_add_plaque hN h hh1 hh0

/-- Shifting by `cBaseAnchor` leaves `dipoleCoord` invariant for every `m ≥ 1`. -/
theorem dipoleCoord_sub_cBaseAnchor_eq {c : ℕ → ℝ} {N m : ℕ} (hm : 1 ≤ m) :
    dipoleCoord (fun k => c k - cBaseAnchor k) N m = dipoleCoord c N m := by
  unfold dipoleCoord
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj3 : 3 ≤ j := by have := (Finset.mem_Icc.mp hj).1; omega
  have hcb : cBaseAnchor j = 0 := by
    rcases j with _ | _ | _ | j <;> simp [cBaseAnchor] <;> omega
  dsimp only
  rw [hcb, sub_zero]

/-- Shifting by `cBaseAnchor` leaves `dipolePlaqueForm` invariant. -/
theorem dipolePlaqueForm_sub_cBaseAnchor_eq (c : ℕ → ℝ) (N : ℕ) :
    dipolePlaqueForm (fun k => c k - cBaseAnchor k) N = dipolePlaqueForm c N := by
  unfold dipolePlaqueForm
  refine Finset.sum_congr rfl fun a ha => Finset.sum_congr rfl fun b hb => ?_
  rw [dipoleCoord_sub_cBaseAnchor_eq (Finset.mem_Icc.mp ha).1,
    dipoleCoord_sub_cBaseAnchor_eq (Finset.mem_Icc.mp hb).1]

/-- Boundary-minus-plaque formula for `SCot` on the affine manifold `A_N`. -/
theorem SCot_eq_neg_c_one_mul_drive_sub_dipolePlaqueForm {N : ℕ} (hN : 2 ≤ N) (c : ℕ → ℝ)
    (hc1 : D1 c N = 0) (hc0 : D0 c N = 2) :
    SCot vasyuninGCot c N =
      -(c 1) * Real.pi * linearCotDrive (fun k => c k - cBaseAnchor k) N -
        dipolePlaqueForm (fun k => c k - cBaseAnchor k) N := by
  have ht := sub_cBaseAnchor_mem_tangent hN c hc1 hc0
  rw [SCot_eq_neg_c_one_mul_linearCotDrive_sub_plaque hN c hc1 hc0,
    linearCotDrive_eq_sum_dipoleCoord hN _ ht.1 ht.2]
  have hsum :
      (∑ m ∈ Finset.Icc 1 (N - 2), dipoleCoord c N m * (deltaCot (m + 2) - deltaCot (m + 1))) =
        ∑ m ∈ Finset.Icc 1 (N - 2),
          dipoleCoord (fun k => c k - cBaseAnchor k) N m *
            (deltaCot (m + 2) - deltaCot (m + 1)) :=
    Finset.sum_congr rfl fun m hm => by
      rw [dipoleCoord_sub_cBaseAnchor_eq (Finset.mem_Icc.mp hm).1]
  rw [hsum, show (dipolePlaqueForm (fun k => c k - cBaseAnchor k) N) = dipolePlaqueForm c N from
    dipolePlaqueForm_sub_cBaseAnchor_eq c N]
  unfold dipolePlaqueForm
  ring

/-- Exact `L²(0, 1)` Nyman–Beurling residual identity in terms of `c 1`, `linearCotDrive`, and
`dipolePlaqueForm` on `A_N`. -/
theorem l2_dist_eq_one_add_c_one_mul_drive_add_dipolePlaqueForm {N : ℕ} (hN : 2 ≤ N)
    (c : ℕ → ℝ) (hc1 : D1 c N = 0) (hc0 : D0 c N = 2) :
    (∫ x in (0 : ℝ)..1, (1 - ∑ k ∈ Finset.Icc 1 N, c k * recipFractScaled k x) ^ 2) =
      1 + c 1 * Real.pi * linearCotDrive (fun k => c k - cBaseAnchor k) N +
        dipolePlaqueForm (fun k => c k - cBaseAnchor k) N := by
  rw [affine_l2_dist_eq_one_sub_scot c hc1 hc0,
    SCot_eq_neg_c_one_mul_drive_sub_dipolePlaqueForm hN c hc1 hc0]
  ring

/-- **Unconditional Pure Plaque Cauchy–Schwarz Lower Bound**: on `A_N⁰`,
`(π * linearCotDrive h N) ^ 2 - π * h 1 * linearCotDrive h N ≤ dipolePlaqueForm h N`. -/
theorem sq_linearCotDrive_sub_le_dipolePlaqueForm {N : ℕ} (hN : 2 ≤ N) (h : ℕ → ℝ)
    (hh1 : D1 h N = 0) (hh0 : D0 h N = 0) :
    (Real.pi * linearCotDrive h N) ^ 2 - Real.pi * h 1 * linearCotDrive h N ≤
      dipolePlaqueForm h N := by
  have hcs := sq_linearCotDrive_le_qcot hN h hh1 hh0
  rw [QCot_eq_h_one_mul_drive_add_dipolePlaqueForm hN h hh1 hh0] at hcs
  linarith

/-- Completing-the-square form of the pure plaque Cauchy–Schwarz lower bound. -/
theorem completed_sq_sub_div_four_le_dipolePlaqueForm {N : ℕ} (hN : 2 ≤ N) (h : ℕ → ℝ)
    (hh1 : D1 h N = 0) (hh0 : D0 h N = 0) :
    (Real.pi * linearCotDrive h N - h 1 / 2) ^ 2 - (h 1) ^ 2 / 4 ≤
      dipolePlaqueForm h N := by
  have hcs := sq_linearCotDrive_sub_le_dipolePlaqueForm hN h hh1 hh0
  linarith

/-- Universal lower bound `-(h 1) ^ 2 / 4 ≤ dipolePlaqueForm h N` for every `h ∈ A_N⁰`. -/
theorem neg_h_one_sq_div_four_le_dipolePlaqueForm {N : ℕ} (hN : 2 ≤ N) (h : ℕ → ℝ)
    (hh1 : D1 h N = 0) (hh0 : D0 h N = 0) :
    -(h 1) ^ 2 / 4 ≤ dipolePlaqueForm h N := by
  have hcs := completed_sq_sub_div_four_le_dipolePlaqueForm hN h hh1 hh0
  have hsq : 0 ≤ (Real.pi * linearCotDrive h N - h 1 / 2) ^ 2 := sq_nonneg _
  linarith

/-- Under unit-drive normalization `π * linearCotDrive h N = 1` on `A_N⁰`,
`1 - h 1 ≤ dipolePlaqueForm h N`. -/
theorem one_sub_h_one_le_dipolePlaqueForm_of_unit_drive {N : ℕ} (hN : 2 ≤ N) (h : ℕ → ℝ)
    (hh1 : D1 h N = 0) (hh0 : D0 h N = 0) (hd : Real.pi * linearCotDrive h N = 1) :
    1 - h 1 ≤ dipolePlaqueForm h N := by
  have hcs := sq_linearCotDrive_sub_le_dipolePlaqueForm hN h hh1 hh0
  rw [show Real.pi * h 1 * linearCotDrive h N = h 1 * (Real.pi * linearCotDrive h N) by ring,
    hd, one_pow, mul_one] at hcs
  exact hcs

/-- Symmetry of `dipolePlaqueEntry` makes `dipolePlaqueForm` symmetric bilinear. -/
theorem dipolePlaqueForm_neg {N : ℕ} (h : ℕ → ℝ) :
    dipolePlaqueForm (fun k => -h k) N = dipolePlaqueForm h N := by
  unfold dipolePlaqueForm
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  have hneg (m : ℕ) : dipoleCoord (fun k => -h k) N m = -dipoleCoord h N m := by
    unfold dipoleCoord
    have hpt : ∀ j ∈ Finset.Icc (m + 2) N, -h j / (j : ℝ) = -(h j / (j : ℝ)) :=
      fun _ _ => by ring
    rw [Finset.sum_congr rfl hpt, Finset.sum_neg_distrib]
  rw [hneg a, hneg b]
  ring
