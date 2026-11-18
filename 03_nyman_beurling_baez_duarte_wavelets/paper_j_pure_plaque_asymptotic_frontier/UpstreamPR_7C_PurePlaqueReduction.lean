/-
Copyright (c) 2026 Qamar Munawer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qamar Munawer
-/
module

public import RiemannBlueprint.UpstreamPRs.UpstreamPR_4M_DipoleDiagonalAndSymmetry

/-!
# Pure 4-Point Plaque Kernel and Global Anchor-Drive Cancellation on `A_N`

This module strips the Rank-2 boundary terms from `dipoleGramEntry` to isolate the pure
4-point plaque kernel `dipolePlaqueEntry` and establishes exact global anchor-drive
cancellation across the full affine Báez-Duarte manifold `A_N`:

* `dipolePlaqueEntry`: symmetric pure 4-point cotangent difference kernel.
* `dipolePlaqueEntry_comm`, `dipolePlaqueEntry_diag_eq`: exact symmetry and collapse of the
  diagonal plaque to `-2 * unweightedKCot (m + 1) (m + 2)`.
* `QCot_eq_h_one_mul_linearCotDrive_add_plaque`: global Rank-2 boundary factorization on `A_N⁰`.
* `SCot_eq_neg_c_one_mul_linearCotDrive_sub_plaque`: global anchor-drive cancellation on `A_N`,
  eliminating the `2 * π` linear prefactor cleanly in favor of `-π * c 1 * linearCotDrive`.
-/

@[expose] public section

open scoped BigOperators

/-- Pure 4-point cotangent plaque kernel obtained by stripping the Rank-2 boundary terms from
`dipoleGramEntry`. -/
noncomputable def dipolePlaqueEntry (a b : ℕ) : ℝ :=
  unweightedKCot (a + 1) (b + 1) - unweightedKCot (a + 1) (b + 2) -
    unweightedKCot (a + 2) (b + 1) + unweightedKCot (a + 2) (b + 2)

/-- Symmetry of the pure plaque kernel: `dipolePlaqueEntry a b = dipolePlaqueEntry b a`. -/
theorem dipolePlaqueEntry_comm (a b : ℕ) : dipolePlaqueEntry a b = dipolePlaqueEntry b a := by
  unfold dipolePlaqueEntry
  rw [unweightedKCot_comm (a + 1) (b + 1), unweightedKCot_comm (a + 1) (b + 2),
    unweightedKCot_comm (a + 2) (b + 1), unweightedKCot_comm (a + 2) (b + 2)]
  ring

/-- Single-pair diagonal collapse of the pure plaque kernel:
`dipolePlaqueEntry m m = -2 * unweightedKCot (m + 1) (m + 2)`. -/
theorem dipolePlaqueEntry_diag_eq (m : ℕ) :
    dipolePlaqueEntry m m = -2 * unweightedKCot (m + 1) (m + 2) := by
  unfold dipolePlaqueEntry
  rw [unweightedKCot_diag (m + 1), unweightedKCot_diag (m + 2),
    unweightedKCot_comm (m + 2) (m + 1)]
  ring

/-- Decomposition of `dipoleGramEntry a b` into Rank-2 boundary differences plus
`dipolePlaqueEntry a b`. -/
theorem dipoleGramEntry_eq_boundary_add_plaque (a b : ℕ) :
    dipoleGramEntry a b =
      (Real.pi / 2) * (deltaCot (a + 2) - deltaCot (a + 1)) +
        (Real.pi / 2) * (deltaCot (b + 2) - deltaCot (b + 1)) +
        dipolePlaqueEntry a b := by
  unfold dipoleGramEntry dipolePlaqueEntry
  ring

private lemma sum_dipoleCoord_eq_head {N : ℕ} (hN : 2 ≤ N) (h : ℕ → ℝ)
    (hh1 : D1 h N = 0) (hh0 : D0 h N = 0) :
    ∑ m ∈ Finset.Icc 1 (N - 2), dipoleCoord h N m = h 1 := by
  have h1 : (1 : ℕ) ∈ Finset.Icc 1 N := Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩
  have hrep := eq_sum_cumulativeDipole_of_mem_tangent hN h hh1 hh0 h1
  have hterm : ∀ m ∈ Finset.Icc 1 (N - 2),
      dipoleCoord h N m * cumulativeDipole m 1 = dipoleCoord h N m := fun m hm => by
    have hm1 : 1 ≤ m := (Finset.mem_Icc.mp hm).1
    have hfour := cumulativeDipole_eq_four_term hm1 1
    have hn2 : (1 : ℕ) ≠ 2 := by omega
    have hnm1 : (1 : ℕ) ≠ m + 1 := by omega
    have hnm2 : (1 : ℕ) ≠ m + 2 := by omega
    simp only [hfour, ↓reduceIte, hn2, hnm1, hnm2]
    ring
  rw [Finset.sum_congr rfl hterm] at hrep
  exact hrep.symm

/-- Global Rank-2 boundary factorization on `A_N⁰`: for every `N ≥ 2` and `h ∈ A_N⁰`,
`QCot` splits into `π * h 1 * linearCotDrive h N` plus the pure 4-point plaque quadratic form. -/
theorem QCot_eq_h_one_mul_linearCotDrive_add_plaque {N : ℕ} (hN : 2 ≤ N) (h : ℕ → ℝ)
    (hh1 : D1 h N = 0) (hh0 : D0 h N = 0) :
    QCot vasyuninGCot h N =
      Real.pi * h 1 * linearCotDrive h N +
        ∑ a ∈ Finset.Icc 1 (N - 2), ∑ b ∈ Finset.Icc 1 (N - 2),
          dipoleCoord h N a * dipoleCoord h N b * dipolePlaqueEntry a b := by
  have hsplit : ∀ a b : ℕ,
      dipoleCoord h N a * dipoleCoord h N b * dipoleGramEntry a b =
        (Real.pi / 2) * (dipoleCoord h N b * (dipoleCoord h N a * (deltaCot (a + 2) -
            deltaCot (a + 1)))) +
          (Real.pi / 2) * (dipoleCoord h N a * (dipoleCoord h N b * (deltaCot (b + 2) -
            deltaCot (b + 1)))) +
          dipoleCoord h N a * dipoleCoord h N b * dipolePlaqueEntry a b := fun a b => by
    rw [dipoleGramEntry_eq_boundary_add_plaque]; ring
  rw [QCot_eq_sum_dipoleGramEntry hN h hh1 hh0]
  simp_rw [hsplit, Finset.sum_add_distrib, ← Finset.mul_sum]
  have ha_part :
      (∑ a ∈ Finset.Icc 1 (N - 2), ∑ b ∈ Finset.Icc 1 (N - 2),
          dipoleCoord h N b * (dipoleCoord h N a * (deltaCot (a + 2) - deltaCot (a + 1)))) =
        h 1 * linearCotDrive h N := by
    have hswap :
        (∑ a ∈ Finset.Icc 1 (N - 2), ∑ b ∈ Finset.Icc 1 (N - 2),
          dipoleCoord h N b * (dipoleCoord h N a * (deltaCot (a + 2) - deltaCot (a + 1)))) =
          (∑ b ∈ Finset.Icc 1 (N - 2), dipoleCoord h N b) *
            ∑ a ∈ Finset.Icc 1 (N - 2),
              dipoleCoord h N a * (deltaCot (a + 2) - deltaCot (a + 1)) := by
      rw [Finset.sum_mul_sum, Finset.sum_comm]
    rw [hswap, sum_dipoleCoord_eq_head hN h hh1 hh0,
      ← linearCotDrive_eq_sum_dipoleCoord hN h hh1 hh0]
  have hb_part :
      (∑ a ∈ Finset.Icc 1 (N - 2), dipoleCoord h N a * ∑ b ∈ Finset.Icc 1 (N - 2),
          dipoleCoord h N b * (deltaCot (b + 2) - deltaCot (b + 1))) =
        h 1 * linearCotDrive h N := by
    rw [← Finset.sum_mul, sum_dipoleCoord_eq_head hN h hh1 hh0,
      ← linearCotDrive_eq_sum_dipoleCoord hN h hh1 hh0]
  rw [ha_part, hb_part]
  ring

private lemma dipoleCoord_sub_cBase_pure (c : ℕ → ℝ) {N m : ℕ} (hm : 1 ≤ m) :
    dipoleCoord (fun k => c k - cBaseAnchor k) N m = dipoleCoord c N m := by
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj3 : 3 ≤ j := by have := (Finset.mem_Icc.mp hj).1; omega
  have hanch : cBaseAnchor j = 0 := by rcases j with _ | _ | _ | j <;> [omega; omega; omega; rfl]
  dsimp only; rw [hanch, sub_zero]

/-- Global anchor-drive cancellation theorem on `A_N`: for every `N ≥ 2` and `c ∈ A_N`, shifting
`h = c - cBaseAnchor` cancels the `2 * π` prefactor identically via `h 1 = c 1 + 2`. -/
theorem SCot_eq_neg_c_one_mul_linearCotDrive_sub_plaque {N : ℕ} (hN : 2 ≤ N) (c : ℕ → ℝ)
    (hc1 : D1 c N = 0) (hc0 : D0 c N = 2) :
    SCot vasyuninGCot c N =
      -Real.pi * c 1 *
          (∑ m ∈ Finset.Icc 1 (N - 2),
            dipoleCoord c N m * (deltaCot (m + 2) - deltaCot (m + 1))) -
        ∑ a ∈ Finset.Icc 1 (N - 2), ∑ b ∈ Finset.Icc 1 (N - 2),
          dipoleCoord c N a * dipoleCoord c N b * dipolePlaqueEntry a b := by
  let h : ℕ → ℝ := fun k => c k - cBaseAnchor k
  have ht := sub_cBaseAnchor_mem_tangent hN c hc1 hc0
  have hc_eq : c = fun k => cBaseAnchor k + h k := funext fun k => by dsimp [h]; ring
  have hS : SCot vasyuninGCot c N = -QCot vasyuninGCot h N + 2 * Real.pi * linearCotDrive h N := by
    conv_lhs => rw [hc_eq]
    rw [SCot_cBaseAnchor_add_eq hN h]
    unfold SCot linearCotDrive
    rfl
  have hh1_val : h 1 = c 1 + 2 := by change c 1 - cBaseAnchor 1 = c 1 + 2; norm_num [cBaseAnchor]
  rw [hS, QCot_eq_h_one_mul_linearCotDrive_add_plaque hN h ht.1 ht.2, hh1_val,
    linearCotDrive_eq_sum_dipoleCoord hN h ht.1 ht.2]
  have hL :
      (∑ m ∈ Finset.Icc 1 (N - 2),
          dipoleCoord h N m * (deltaCot (m + 2) - deltaCot (m + 1))) =
        ∑ m ∈ Finset.Icc 1 (N - 2),
          dipoleCoord c N m * (deltaCot (m + 2) - deltaCot (m + 1)) :=
    Finset.sum_congr rfl fun m hm => by
      rw [dipoleCoord_sub_cBase_pure c (Finset.mem_Icc.mp hm).1]
  have hP :
      (∑ a ∈ Finset.Icc 1 (N - 2), ∑ b ∈ Finset.Icc 1 (N - 2),
          dipoleCoord h N a * dipoleCoord h N b * dipolePlaqueEntry a b) =
        ∑ a ∈ Finset.Icc 1 (N - 2), ∑ b ∈ Finset.Icc 1 (N - 2),
          dipoleCoord c N a * dipoleCoord c N b * dipolePlaqueEntry a b :=
    Finset.sum_congr rfl fun a ha => Finset.sum_congr rfl fun b hb => by
      rw [dipoleCoord_sub_cBase_pure c (Finset.mem_Icc.mp ha).1,
        dipoleCoord_sub_cBase_pure c (Finset.mem_Icc.mp hb).1]
  rw [hL, hP]
  ring
