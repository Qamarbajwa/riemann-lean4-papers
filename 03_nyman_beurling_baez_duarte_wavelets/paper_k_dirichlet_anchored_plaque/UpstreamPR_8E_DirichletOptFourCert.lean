/-
Copyright (c) 2026 Qamar Munawer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qamar Munawer
-/
module

public import RiemannBlueprint.UpstreamPRs.UpstreamPR_8D_PurePlaqueRHCriterion

/-!
# Exact Closed-Form Dirichlet-Anchored (`c₁ = -1`) Optimum on `A_4`: `(31 / 108) * π`

This module resolves the finite optimization problem on the Dirichlet-anchored slice
`A_4^{dir} = {c | D1 c 4 = 0 ∧ D0 c 4 = 2 ∧ c 1 = -1}`:

* `cDirichletOptFour`: explicit optimizer at dipole coordinates `α₁ = 1 / 2 + 1 / (3 * √3)` and
  `α₂ = 1 / 2 - 1 / (3 * √3)`.
* `cDirichletOptFour_isDirichletAnchored`: proof that `cDirichletOptFour` satisfies `D1 = 0`,
  `D0 = 2`, and `cDirichletOptFour 1 = -1`.
* `SCot_eq_dirichlet_four_sub_sq`: exact completing-the-square identity over all Dirichlet-anchored
  `c` at `N = 4`,
  `SCot vasyuninGCot c 4 = (31 / 108) * π - π * (dipoleCoord c 4 1 - (1 / 2 + 1 / (3 * √3))) ^ 2`.
* `SCot_cDirichletOptFour_eq`: exact rational-times-`π` value `(31 / 108) * π` (all `√3` radicals
  cancel identically).
* `SCot_le_cDirichletOptFour_of_isDirichletAnchored_four`: global optimality over all
  Dirichlet-anchored candidates at `N = 4`.
-/

@[expose] public section

open scoped BigOperators
open Finset

/-- Exact closed-form optimizer on the Dirichlet-anchored (`c₁ = -1`) slice of `A_4`, evaluated
at `α₁ = 1 / 2 + 1 / (3 * √3)` and `α₂ = 1 / 2 - 1 / (3 * √3)`. -/
noncomputable def cDirichletOptFour (k : ℕ) : ℝ :=
  cBaseAnchor k + (1 / 2 + 1 / (3 * Real.sqrt 3)) * cumulativeDipole 1 k +
    (1 / 2 - 1 / (3 * Real.sqrt 3)) * cumulativeDipole 2 k

private lemma cumulativeDipole_one_eq_hw (k : ℕ) :
    cumulativeDipole 1 k = harmonicWavelet 1 k := by
  simp [cumulativeDipole]

private lemma cumulativeDipole_two_eq_hw (k : ℕ) :
    cumulativeDipole 2 k = harmonicWavelet 1 k + harmonicWavelet 2 k := by
  unfold cumulativeDipole
  rw [show Finset.Icc 1 2 = ({1, 2} : Finset ℕ) by ext x; simp; omega,
    Finset.sum_insert (by decide), Finset.sum_singleton]

private lemma sum_Icc_one_four_dopt (f : ℕ → ℝ) :
    ∑ k ∈ Finset.Icc 1 4, f k = f 1 + f 2 + f 3 + f 4 := by
  rw [show Finset.Icc 1 4 = ({1, 2, 3, 4} : Finset ℕ) by
    ext x; simp only [Finset.mem_Icc, Finset.mem_insert, Finset.mem_singleton]; omega]
  norm_num [Finset.sum_insert, add_assoc]

/-- Exact verification that `cDirichletOptFour` lies on `A_4` with `c₁ = -1`. -/
theorem cDirichletOptFour_isDirichletAnchored : IsDirichletAnchored cDirichletOptFour 4 := by
  refine ⟨?_, ?_, ?_⟩
  · unfold D1
    rw [sum_Icc_one_four_dopt]
    simp [cDirichletOptFour, cumulativeDipole_one_eq_hw, cumulativeDipole_two_eq_hw,
      cBaseAnchor, harmonicWavelet]
    ring
  · unfold D0
    rw [sum_Icc_one_four_dopt]
    simp [cDirichletOptFour, cumulativeDipole_one_eq_hw, cumulativeDipole_two_eq_hw,
      cBaseAnchor, harmonicWavelet]
    ring
  · simp [cDirichletOptFour, cumulativeDipole_one_eq_hw, cumulativeDipole_two_eq_hw,
      cBaseAnchor, harmonicWavelet]
    ring

private lemma scot_two_wavelets_dirichlet (t₂ : ℝ) :
    SCot vasyuninGCot
        (fun k => cBaseAnchor k + harmonicWavelet 1 k + t₂ * harmonicWavelet 2 k) 4 =
      (31 / 108 : ℝ) * Real.pi -
        Real.pi * ((1 - t₂) - (1 / 2 + 1 / (3 * Real.sqrt 3))) ^ 2 := by
  have hsq3_ne : Real.sqrt 3 ≠ 0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  have hsq3_sq : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hbase := SCot_cBaseAnchor_add_two_wavelets_eq 1 t₂
  simp only [one_mul] at hbase
  rw [hbase]
  field_simp [hsq3_ne]
  ring_nf
  have hsq3_3 : Real.sqrt 3 ^ 3 = 3 * Real.sqrt 3 := by rw [pow_succ, hsq3_sq]
  have hsq3_4 : Real.sqrt 3 ^ 4 = 9 := by
    rw [show (4 : ℕ) = 2 * 2 by decide, pow_mul, hsq3_sq]; norm_num
  simp only [hsq3_sq, hsq3_3, hsq3_4]
  ring

private lemma dipoleCoord_four_dirichlet {c : ℕ → ℝ} (hc : IsDirichletAnchored c 4) :
    dipoleCoord c 4 1 = 1 - c 4 / 4 := by
  have hc_eq : ∀ k ∈ Finset.Icc 1 4,
      c k = cBaseAnchor k + 1 * harmonicWavelet 1 k + (c 4 / 4) * harmonicWavelet 2 k := by
    intro k hk
    have h := eq_cBaseAnchor_add_wavelets_of_mem_A_four c hc.1 hc.2.1 hk
    rw [hc.2.2] at h
    linarith
  unfold dipoleCoord
  rw [show Finset.Icc 3 4 = ({3, 4} : Finset ℕ) by ext x; simp; omega,
    Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [hc_eq 3 (by decide)]
  simp [cBaseAnchor, harmonicWavelet]
  ring

/-- **Exact Dirichlet-Anchored Completing-the-Square Law at `N = 4`**: for every `c ∈ A_4` with
`c 1 = -1`, `SCot vasyuninGCot c 4 = (31 / 108) * π - π * (η₁ - (1 / 2 + 1 / (3 * √3))) ^ 2`. -/
theorem SCot_eq_dirichlet_four_sub_sq {c : ℕ → ℝ} (hc : IsDirichletAnchored c 4) :
    SCot vasyuninGCot c 4 =
      (31 / 108 : ℝ) * Real.pi -
        Real.pi * (dipoleCoord c 4 1 - (1 / 2 + 1 / (3 * Real.sqrt 3))) ^ 2 := by
  let t₂ : ℝ := c 4 / 4
  have heq :
      SCot vasyuninGCot c 4 =
        SCot vasyuninGCot
          (fun k => cBaseAnchor k + harmonicWavelet 1 k + t₂ * harmonicWavelet 2 k) 4 := by
    unfold SCot QCot
    congr 1
    refine Finset.sum_congr rfl fun j hj => Finset.sum_congr rfl fun k hk => ?_
    have hj' := eq_cBaseAnchor_add_wavelets_of_mem_A_four c hc.1 hc.2.1 hj
    have hk' := eq_cBaseAnchor_add_wavelets_of_mem_A_four c hc.1 hc.2.1 hk
    rw [hc.2.2] at hj' hk'
    have hj'' : c j = cBaseAnchor j + harmonicWavelet 1 j + t₂ * harmonicWavelet 2 j := by
      dsimp only [t₂]; linarith
    have hk'' : c k = cBaseAnchor k + harmonicWavelet 1 k + t₂ * harmonicWavelet 2 k := by
      dsimp only [t₂]; linarith
    rw [hj'', hk'']
  rw [heq, scot_two_wavelets_dirichlet t₂, dipoleCoord_four_dirichlet hc]

/-- **Exact Closed-Form Value at `N = 4`**: all `√3` radicals cancel identically to yield
`SCot vasyuninGCot cDirichletOptFour 4 = (31 / 108) * π`. -/
theorem SCot_cDirichletOptFour_eq :
    SCot vasyuninGCot cDirichletOptFour 4 = (31 / 108 : ℝ) * Real.pi := by
  have heq :
      cDirichletOptFour =
        fun k => cBaseAnchor k + harmonicWavelet 1 k +
          (1 / 2 - 1 / (3 * Real.sqrt 3)) * harmonicWavelet 2 k := by
    ext k
    simp only [cDirichletOptFour, cumulativeDipole_one_eq_hw, cumulativeDipole_two_eq_hw]
    ring
  rw [heq, scot_two_wavelets_dirichlet]
  ring

/-- Global optimality of `cDirichletOptFour` across all Dirichlet-anchored vectors on `A_4`. -/
theorem SCot_le_cDirichletOptFour_of_isDirichletAnchored_four {c : ℕ → ℝ}
    (hc : IsDirichletAnchored c 4) :
    SCot vasyuninGCot c 4 ≤ SCot vasyuninGCot cDirichletOptFour 4 := by
  rw [SCot_eq_dirichlet_four_sub_sq hc, SCot_cDirichletOptFour_eq]
  have hnn : 0 ≤ Real.pi * (dipoleCoord c 4 1 - (1 / 2 + 1 / (3 * Real.sqrt 3))) ^ 2 :=
    by positivity
  linarith

/-- Residual `L²(0, 1)` lower bound on the Dirichlet-anchored slice of `A_4`: every `c` satisfying
`IsDirichletAnchored c 4` has `1 - (31 / 108) * π ≤ ‖1 - ∑ c_k {1 / (k x)}‖₂²`. -/
theorem one_sub_31_div_108_pi_le_l2_dist_of_isDirichletAnchored_four {c : ℕ → ℝ}
    (hc : IsDirichletAnchored c 4) :
    1 - (31 / 108 : ℝ) * Real.pi ≤
      ∫ x in (0 : ℝ)..1, (1 - ∑ k ∈ Finset.Icc 1 4, c k * recipFractScaled k x) ^ 2 := by
  rw [affine_l2_dist_eq_one_sub_scot c hc.1 hc.2.1]
  have hle := SCot_le_cDirichletOptFour_of_isDirichletAnchored_four hc
  rw [SCot_cDirichletOptFour_eq] at hle
  linarith
