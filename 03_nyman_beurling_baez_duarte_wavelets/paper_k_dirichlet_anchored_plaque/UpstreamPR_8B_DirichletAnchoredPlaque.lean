/-
Copyright (c) 2026 Qamar Munawer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qamar Munawer
-/
module

public import RiemannBlueprint.UpstreamPRs.UpstreamPR_8A_PurePlaqueCauchySchwarz

/-!
# Dirichlet-Anchored (`c₁ = -1`) Pure Plaque Positivity and `L²` Energy Law

When an affine candidate `c ∈ A_N` satisfies the Dirichlet-pole anchoring `c 1 = -1` (i.e.,
`h 1 = c 1 - cBaseAnchor 1 = 1`), the boundary term in `SCot` cancels against the unit drive,
yielding unconditional positivity of `dipolePlaqueForm` whenever `1 ≤ π * L_cot(h, N)`:

* `IsDirichletAnchored`: predicate `D1 c N = 0 ∧ D0 c N = 2 ∧ c 1 = -1`.
* `cDirichletAnchor`: explicit `N ≥ 3` anchor `(-1, 0, 3, 0, ...)` with
  `cDirichletAnchor = cBaseAnchor + harmonicWavelet 1`.
* `dipolePlaqueForm_nonneg_of_dirichlet_of_one_le_drive`: `0 ≤ dipolePlaqueForm h N` whenever
  `h ∈ A_N⁰`, `h 1 = 1`, and `1 ≤ π * linearCotDrive h N`.
* `neg_one_div_four_le_dipolePlaqueForm_of_dirichlet`: universal floor `-1 / 4 ≤ dipolePlaqueForm`.
* `unit_drive_dirichlet_plaque_eq_l2_dist` and `unit_drive_dirichlet_plaque_nonneg`: under unit
  drive `π * linearCotDrive h N = 1` and `c 1 = -1`,
  `dipolePlaqueForm h N = ‖1 - ∑ c_k {1 / (k x)}‖₂² ≥ 0`.
-/

@[expose] public section

open scoped BigOperators
open Finset

/-- Affine Báez-Duarte constraint together with Dirichlet pole anchoring `c 1 = -1`. -/
def IsDirichletAnchored (c : ℕ → ℝ) (N : ℕ) : Prop :=
  D1 c N = 0 ∧ D0 c N = 2 ∧ c 1 = -1

/-- Minimal Dirichlet-anchored point `(-1, 0, 3, 0, ...)` lying in `A_N` for all `N ≥ 3`. -/
def cDirichletAnchor (k : ℕ) : ℝ :=
  if k = 1 then -1 else if k = 2 then 0 else if k = 3 then 3 else 0

/-- `cDirichletAnchor` equals `cBaseAnchor + harmonicWavelet 1` everywhere on `ℕ`. -/
theorem cDirichletAnchor_eq_cBaseAnchor_add_wavelet_one (k : ℕ) :
    cDirichletAnchor k = cBaseAnchor k + harmonicWavelet 1 k := by
  unfold cDirichletAnchor cBaseAnchor harmonicWavelet
  rcases k with _ | _ | _ | _ | k <;> norm_num

/-- For `N ≥ 3`, `cDirichletAnchor` is Dirichlet-anchored in `A_N`. -/
theorem cDirichletAnchor_isDirichletAnchored {N : ℕ} (hN : 3 ≤ N) :
    IsDirichletAnchored cDirichletAnchor N := by
  have ha := cBaseAnchor_mem_A_N (by omega : 2 ≤ N)
  have hw := harmonicWavelet_mem_tangent (m := 1) (N := N) (by omega) hN
  refine ⟨?_, ?_, ?_⟩
  · unfold D1 at ha hw ⊢
    have hpt : ∀ k ∈ Finset.Icc 1 N,
        cDirichletAnchor k / (k : ℝ) =
          cBaseAnchor k / (k : ℝ) + harmonicWavelet 1 k / (k : ℝ) := fun k _ => by
      rw [cDirichletAnchor_eq_cBaseAnchor_add_wavelet_one]; ring
    rw [Finset.sum_congr rfl hpt, Finset.sum_add_distrib, ha.1, hw.1, add_zero]
  · unfold D0 at ha hw ⊢
    have hpt : ∀ k ∈ Finset.Icc 1 N,
        cDirichletAnchor k = cBaseAnchor k + harmonicWavelet 1 k := fun k _ =>
      cDirichletAnchor_eq_cBaseAnchor_add_wavelet_one k
    rw [Finset.sum_congr rfl hpt, Finset.sum_add_distrib, ha.2, hw.2, add_zero]
  · simp [cDirichletAnchor]

/-- Shifting a Dirichlet-anchored vector `c` by `cBaseAnchor` produces a tangent vector `h ∈ A_N⁰`
with `h 1 = 1`. -/
theorem IsDirichletAnchored.sub_mem_tangent {N : ℕ} (hN : 2 ≤ N) {c : ℕ → ℝ}
    (hc : IsDirichletAnchored c N) :
    D1 (fun k => c k - cBaseAnchor k) N = 0 ∧
      D0 (fun k => c k - cBaseAnchor k) N = 0 ∧
      (c 1 - cBaseAnchor 1) = 1 := by
  have ht := sub_cBaseAnchor_mem_tangent hN c hc.1 hc.2.1
  refine ⟨ht.1, ht.2, ?_⟩
  rw [hc.2.2]
  simp [cBaseAnchor]
  norm_num

/-- Dirichlet-anchored plaque Cauchy–Schwarz lower bound: if `h ∈ A_N⁰` and `h 1 = 1`, then
`(π * L) ^ 2 - π * L ≤ dipolePlaqueForm h N`. -/
theorem dipolePlaqueForm_ge_of_dirichlet {N : ℕ} (hN : 2 ≤ N) (h : ℕ → ℝ)
    (hh1 : D1 h N = 0) (hh0 : D0 h N = 0) (h_one : h 1 = 1) :
    (Real.pi * linearCotDrive h N) ^ 2 - Real.pi * linearCotDrive h N ≤
      dipolePlaqueForm h N := by
  have hcs := sq_linearCotDrive_sub_le_dipolePlaqueForm hN h hh1 hh0
  rw [h_one] at hcs
  linarith

/-- **Dirichlet-Anchored Plaque Positivity**: whenever `h ∈ A_N⁰`, `h 1 = 1`, and
`1 ≤ π * linearCotDrive h N`, the pure plaque quadratic form is nonnegative. -/
theorem dipolePlaqueForm_nonneg_of_dirichlet_of_one_le_drive {N : ℕ} (hN : 2 ≤ N) (h : ℕ → ℝ)
    (hh1 : D1 h N = 0) (hh0 : D0 h N = 0) (h_one : h 1 = 1)
    (hd : 1 ≤ Real.pi * linearCotDrive h N) :
    0 ≤ dipolePlaqueForm h N := by
  have hge := dipolePlaqueForm_ge_of_dirichlet hN h hh1 hh0 h_one
  have hfac : (Real.pi * linearCotDrive h N) ^ 2 - Real.pi * linearCotDrive h N =
      (Real.pi * linearCotDrive h N) * (Real.pi * linearCotDrive h N - 1) := by ring
  have hprod : 0 ≤ (Real.pi * linearCotDrive h N) * (Real.pi * linearCotDrive h N - 1) :=
    mul_nonneg (by linarith) (by linarith)
  linarith

/-- Universal Dirichlet-anchored plaque floor `-1 / 4 ≤ dipolePlaqueForm h N` when `h 1 = 1`. -/
theorem neg_one_div_four_le_dipolePlaqueForm_of_dirichlet {N : ℕ} (hN : 2 ≤ N) (h : ℕ → ℝ)
    (hh1 : D1 h N = 0) (hh0 : D0 h N = 0) (h_one : h 1 = 1) :
    -(1 / 4 : ℝ) ≤ dipolePlaqueForm h N := by
  have hcs := neg_h_one_sq_div_four_le_dipolePlaqueForm hN h hh1 hh0
  rw [h_one] at hcs
  linarith

/-- Exact `SCot` identity on the Dirichlet-anchored locus (`c 1 = -1`):
`SCot vasyuninGCot c N =`
`π * linearCotDrive (c - cBaseAnchor) N - dipolePlaqueForm (c - cBaseAnchor) N`. -/
theorem SCot_eq_drive_sub_dipolePlaqueForm_of_dirichlet {N : ℕ} (hN : 2 ≤ N) {c : ℕ → ℝ}
    (hc : IsDirichletAnchored c N) :
    SCot vasyuninGCot c N =
      Real.pi * linearCotDrive (fun k => c k - cBaseAnchor k) N -
        dipolePlaqueForm (fun k => c k - cBaseAnchor k) N := by
  rw [SCot_eq_neg_c_one_mul_drive_sub_dipolePlaqueForm hN c hc.1 hc.2.1, hc.2.2]
  ring

/-- Exact `L²(0, 1)` residual identity on the Dirichlet-anchored locus (`c 1 = -1`). -/
theorem l2_dist_eq_one_sub_drive_add_dipolePlaqueForm_of_dirichlet {N : ℕ} (hN : 2 ≤ N)
    {c : ℕ → ℝ} (hc : IsDirichletAnchored c N) :
    (∫ x in (0 : ℝ)..1, (1 - ∑ k ∈ Finset.Icc 1 N, c k * recipFractScaled k x) ^ 2) =
      1 - Real.pi * linearCotDrive (fun k => c k - cBaseAnchor k) N +
        dipolePlaqueForm (fun k => c k - cBaseAnchor k) N := by
  rw [l2_dist_eq_one_add_c_one_mul_drive_add_dipolePlaqueForm hN c hc.1 hc.2.1, hc.2.2]
  ring

/-- Under Dirichlet anchoring (`c 1 = -1`) and unit drive (`π * L_cot = 1`), the `L²(0, 1)`
Nyman–Beurling residual equals the pure plaque quadratic form `dipolePlaqueForm`. -/
theorem unit_drive_dirichlet_plaque_eq_l2_dist {N : ℕ} (hN : 2 ≤ N) {c : ℕ → ℝ}
    (hc : IsDirichletAnchored c N)
    (hd : Real.pi * linearCotDrive (fun k => c k - cBaseAnchor k) N = 1) :
    dipolePlaqueForm (fun k => c k - cBaseAnchor k) N =
      ∫ x in (0 : ℝ)..1, (1 - ∑ k ∈ Finset.Icc 1 N, c k * recipFractScaled k x) ^ 2 := by
  rw [l2_dist_eq_one_sub_drive_add_dipolePlaqueForm_of_dirichlet hN hc, hd]
  ring

/-- Under Dirichlet anchoring (`c 1 = -1`) and unit drive (`π * L_cot = 1`),
`0 ≤ dipolePlaqueForm (c - cBaseAnchor) N`. -/
theorem unit_drive_dirichlet_plaque_nonneg {N : ℕ} (hN : 2 ≤ N) {c : ℕ → ℝ}
    (hc : IsDirichletAnchored c N)
    (hd : Real.pi * linearCotDrive (fun k => c k - cBaseAnchor k) N = 1) :
    0 ≤ dipolePlaqueForm (fun k => c k - cBaseAnchor k) N := by
  have ht := hc.sub_mem_tangent hN
  exact dipolePlaqueForm_nonneg_of_dirichlet_of_one_le_drive hN _ ht.1 ht.2.1 ht.2.2 hd.ge
