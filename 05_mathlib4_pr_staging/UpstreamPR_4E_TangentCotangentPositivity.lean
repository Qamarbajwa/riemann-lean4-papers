/-
Copyright (c) 2026 Qamar Munawer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qamar Munawer
-/
module

public import RiemannBlueprint.UpstreamPRs.UpstreamPR_4D_WaveletCotangentStencil

/-!
# Tangent-Space `L²`-to-Cotangent Isometry, Positive Semidefiniteness of `QCot`, and `N = 3` Optimum

This file establishes the Hilbert-space positivity structure of Vasyunin's cotangent quadratic form
on the Báez-Duarte tangent hyperplane `A_N⁰ = {h | D1 h N = 0 ∧ D0 h N = 0}`:

* `sum_GSmooth_eq_zero_of_mem_tangent`: the smooth Vasyunin kernel `GSmooth` vanishes identically
  as a bilinear form on `A_N⁰`.
* `tangent_l2_norm_sq_eq_qcot`: exact isometry
  `∫₀¹ (∑ k, h k * {1 / (k x)})^2 dx = QCot vasyuninGCot h N` for every `h ∈ A_N⁰`.
* `QCot_nonneg_of_mem_tangent` and `SCot_nonpos_of_mem_tangent`: unconditional positive
  semidefiniteness of `QCot` (and negative semidefiniteness of `SCot`) on `A_N⁰`.
* `QCot_harmonicWavelet_one_eq`, `harmonicWavelet_one_l2_norm_sq_eq`, and
  `SCot_cBaseAnchor_add_two_thirds_wavelet_one_eq`: exact `L²` energy `π / √3` of the first
  harmonic wavelet `(1, -4, 3)` and exact `N = 3` variational optimum `4 * π / (9 * √3)` at
  `t = 2 / 3`.
-/

@[expose] public section

open scoped BigOperators
open MeasureTheory Finset

/-- The smooth Vasyunin kernel `GSmooth` vanishes identically as a quadratic form on `A_N⁰`. -/
theorem sum_GSmooth_eq_zero_of_mem_tangent (N : ℕ) (gamma_E : ℝ) (h : ℕ → ℝ)
    (hh1 : D1 h N = 0) (hh0 : D0 h N = 0) :
    ∑ j ∈ Finset.Icc 1 N, ∑ k ∈ Finset.Icc 1 N, h j * h k * GSmooth gamma_E j k = 0 := by
  have h_sum :
      (∑ j ∈ Finset.Icc 1 N, ∑ k ∈ Finset.Icc 1 N, h j * h k * GSmooth gamma_E j k) =
        ∑ j ∈ Finset.Icc 1 N, ∑ k ∈ Finset.Icc 1 N,
          (((Real.log (2 * Real.pi) - gamma_E) / 2) *
              ((h j * vecE j) * (h k * vecH k) + (h j * vecH j) * (h k * vecE k)) +
            (1 / 2) * ((h j * vecE j) * (h k * vecM k) + (h j * vecM j) * (h k * vecE k)) -
            (1 / 2) * ((h j * vecL j) * (h k * vecH k) + (h j * vecH j) * (h k * vecL k)) -
            (h j * vecH j) * (h k * vecH k)) := by
    refine Finset.sum_congr rfl fun j hj => Finset.sum_congr rfl fun k hk => ?_
    rw [GSmooth_eq_rank4 gamma_E (Finset.mem_Icc.mp hj).1 (Finset.mem_Icc.mp hk).1]
    dsimp [GSmoothRank4]
    ring
  have hE : ∑ k ∈ Finset.Icc 1 N, h k * vecE k = 0 := by
    simpa [vecE, D0] using hh0
  have hH : ∑ k ∈ Finset.Icc 1 N, h k * vecH k = 0 := by
    have hEq : (∑ k ∈ Finset.Icc 1 N, h k * vecH k) = D1 h N :=
      Finset.sum_congr rfl fun _ _ => by dsimp [vecH, D1]; ring
    rw [hEq, hh1]
  have h_const : ∀ (a : ℝ) (F : ℕ → ℕ → ℝ),
      ∑ j ∈ Finset.Icc 1 N, ∑ k ∈ Finset.Icc 1 N, a * F j k =
        a * ∑ j ∈ Finset.Icc 1 N, ∑ k ∈ Finset.Icc 1 N, F j k := fun _ _ => by
    simp only [← Finset.mul_sum]
  have h_outer : ∀ f g : ℕ → ℝ,
      ∑ j ∈ Finset.Icc 1 N, ∑ k ∈ Finset.Icc 1 N, f j * g k =
        (∑ j ∈ Finset.Icc 1 N, f j) * (∑ k ∈ Finset.Icc 1 N, g k) := fun _ _ => by
    simp only [← Finset.mul_sum, ← Finset.sum_mul]
  rw [h_sum]
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, h_const]
  simp_rw [h_outer, hE, hH]
  ring

/-- **Tangent-Space `L²`-to-Cotangent Isometry**: for any `h ∈ A_N⁰`, the `L²(0, 1)` squared norm
of `∑ k, h k * {1 / (k * x)}` equals `QCot vasyuninGCot h N`. -/
theorem tangent_l2_norm_sq_eq_qcot {N : ℕ} (h : ℕ → ℝ)
    (hh1 : D1 h N = 0) (hh0 : D0 h N = 0) :
    (∫ x in (0 : ℝ)..1, (∑ k ∈ Finset.Icc 1 N, h k * recipFractScaled k x) ^ 2) =
      QCot vasyuninGCot h N := by
  have h_eq :
      (∫ x in (0 : ℝ)..1, (∑ k ∈ Finset.Icc 1 N, h k * recipFractScaled k x) ^ 2) =
        ∫ x in (0 : ℝ)..1,
          ∑ j ∈ Finset.Icc 1 N, ∑ k ∈ Finset.Icc 1 N,
            h j * h k * (recipFractScaled j x * recipFractScaled k x) := by
    refine intervalIntegral.integral_congr fun x _ => ?_
    rw [sq, Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  have hint_term : ∀ j ∈ Finset.Icc 1 N, ∀ k ∈ Finset.Icc 1 N,
      IntervalIntegrable (fun x => h j * h k * (recipFractScaled j x * recipFractScaled k x))
        volume 0 1 := fun j _ k _ => (intervalIntegrable_recipFractScaled_mul j k 0 1).const_mul _
  have hint_inner : ∀ j ∈ Finset.Icc 1 N, IntervalIntegrable
      (fun x => ∑ k ∈ Finset.Icc 1 N, h j * h k * (recipFractScaled j x * recipFractScaled k x))
      volume 0 1 := fun j hj => by
    rw [show (fun x => ∑ k ∈ Finset.Icc 1 N,
        h j * h k * (recipFractScaled j x * recipFractScaled k x)) =
      ∑ k ∈ Finset.Icc 1 N, fun x => h j * h k * (recipFractScaled j x * recipFractScaled k x) by
      funext x; rw [Finset.sum_apply]]
    exact IntervalIntegrable.sum (Finset.Icc 1 N) (hint_term j hj)
  have h_sum_int :
      (∫ x in (0 : ℝ)..1, ∑ j ∈ Finset.Icc 1 N, ∑ k ∈ Finset.Icc 1 N,
          h j * h k * (recipFractScaled j x * recipFractScaled k x)) =
        ∑ j ∈ Finset.Icc 1 N, ∑ k ∈ Finset.Icc 1 N,
          h j * h k * ∫ x in (0 : ℝ)..1, recipFractScaled j x * recipFractScaled k x := by
    rw [intervalIntegral.integral_finsetSum hint_inner]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [intervalIntegral.integral_finsetSum (hint_term j hj)]
    simp_rw [intervalIntegral.integral_const_mul]
  rw [h_eq, h_sum_int]
  have h_cross :
      (∑ j ∈ Finset.Icc 1 N, ∑ k ∈ Finset.Icc 1 N,
          h j * h k * ∫ x in (0 : ℝ)..1, recipFractScaled j x * recipFractScaled k x) =
        (∑ j ∈ Finset.Icc 1 N, ∑ k ∈ Finset.Icc 1 N,
            h j * h k * GSmooth Real.eulerMascheroniConstant j k) +
          QCot vasyuninGCot h N := by
    unfold QCot
    rw [Finset.sum_congr rfl fun j hj => Finset.sum_congr rfl fun k hk => by
      rw [intervalIntegral_recipFractScaled_cross
        (Finset.mem_Icc.mp hj).1 (Finset.mem_Icc.mp hk).1, mul_add]]
    simp only [Finset.sum_add_distrib]
  rw [h_cross, sum_GSmooth_eq_zero_of_mem_tangent N Real.eulerMascheroniConstant h hh1 hh0,
    zero_add]

/-- Unconditional positive semidefiniteness of `QCot vasyuninGCot` on `A_N⁰`. -/
theorem QCot_nonneg_of_mem_tangent {N : ℕ} (h : ℕ → ℝ) (hh1 : D1 h N = 0) (hh0 : D0 h N = 0) :
    0 ≤ QCot vasyuninGCot h N := by
  rw [← tangent_l2_norm_sq_eq_qcot h hh1 hh0]
  exact intervalIntegral.integral_nonneg (by norm_num) fun _ _ => sq_nonneg _

/-- Unconditional negative semidefiniteness of `SCot vasyuninGCot` on `A_N⁰`. -/
theorem SCot_nonpos_of_mem_tangent {N : ℕ} (h : ℕ → ℝ) (hh1 : D1 h N = 0) (hh0 : D0 h N = 0) :
    SCot vasyuninGCot h N ≤ 0 := by
  unfold SCot
  exact neg_nonpos.mpr (QCot_nonneg_of_mem_tangent h hh1 hh0)

private lemma cot_pi_div_three_tan : Real.cos (Real.pi / 3) / Real.sin (Real.pi / 3) = 1 / √3 := by
  rw [Real.cos_pi_div_three, Real.sin_pi_div_three]
  field_simp [(Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 3)).ne']

private lemma cot_two_pi_div_three_tan :
    Real.cos (2 * Real.pi / 3) / Real.sin (2 * Real.pi / 3) = -(1 / √3) := by
  rw [show 2 * Real.pi / 3 = Real.pi - Real.pi / 3 by ring, Real.cos_pi_sub, Real.sin_pi_sub,
    neg_div, cot_pi_div_three_tan]

private lemma vasyuninCotSum_two_tan (b : ℕ) : vasyuninCotSum 2 b = 0 := by
  unfold vasyuninCotSum
  rw [show Finset.Ico 1 2 = ({1} : Finset ℕ) by ext x; simp, Finset.sum_singleton,
    show Real.pi * ((1 : ℕ) : ℝ) / ((2 : ℕ) : ℝ) = Real.pi / 2 by push_cast; ring,
    Real.cos_pi_div_two, zero_div, mul_zero]

private lemma vasyuninCotSum_three_tan (b : ℕ) :
    vasyuninCotSum 3 b =
      (Int.fract ((b : ℝ) / 3) - Int.fract (2 * (b : ℝ) / 3)) * (1 / √3) := by
  unfold vasyuninCotSum
  rw [show Finset.Ico 1 3 = ({1, 2} : Finset ℕ) by ext x; simp; omega,
    Finset.sum_insert (by decide), Finset.sum_singleton]
  push_cast
  rw [show (1 : ℝ) * b / 3 = b / 3 by ring, show Real.pi * 1 / 3 = Real.pi / 3 by ring,
    show Real.pi * 2 / 3 = 2 * Real.pi / 3 by ring, cot_pi_div_three_tan, cot_two_pi_div_three_tan]
  ring

private lemma vasyuninGCot_one_three_tan : vasyuninGCot 1 3 = Real.pi / (18 * √3) := by
  have hV1 : vasyuninCotSum 1 3 = 0 := by simp [vasyuninCotSum]
  unfold vasyuninGCot
  rw [hV1, vasyuninCotSum_three_tan]
  norm_num
  ring

private lemma vasyuninGCot_two_three_tan : vasyuninGCot 2 3 = -(Real.pi / (36 * √3)) := by
  unfold vasyuninGCot
  rw [vasyuninCotSum_two_tan, vasyuninCotSum_three_tan]
  norm_num
  ring

private lemma vasyuninGCot_one_two_tan : vasyuninGCot 1 2 = 0 := by
  have hV1 : vasyuninCotSum 1 2 = 0 := by simp [vasyuninCotSum]
  unfold vasyuninGCot
  rw [hV1, vasyuninCotSum_two_tan]
  ring

private lemma sum_Icc_one_three_tan (f : ℕ → ℝ) :
    ∑ k ∈ Finset.Icc 1 3, f k = f 1 + f 2 + f 3 := by
  have hI : Finset.Icc 1 3 = ({1, 2, 3} : Finset ℕ) := by
    ext x; simp only [Finset.mem_Icc, Finset.mem_insert, Finset.mem_singleton]; omega
  rw [hI]
  norm_num [Finset.sum_insert, add_assoc]

/-- Exact cotangent quadratic energy of the first harmonic wavelet `(1, -4, 3)` at `N = 3`. -/
theorem QCot_harmonicWavelet_one_eq :
    QCot vasyuninGCot (harmonicWavelet 1) 3 = Real.pi / Real.sqrt 3 := by
  unfold QCot
  simp_rw [sum_Icc_one_three_tan]
  rw [vasyuninGCot_diag 1, vasyuninGCot_diag 2, vasyuninGCot_diag 3,
    vasyuninGCot_comm 2 1, vasyuninGCot_comm 3 1, vasyuninGCot_comm 3 2,
    vasyuninGCot_one_two_tan, vasyuninGCot_one_three_tan, vasyuninGCot_two_three_tan]
  simp [harmonicWavelet]
  ring

/-- Exact `L²(0, 1)` squared norm of the first harmonic wavelet `(1, -4, 3)`: `π / √3`. -/
theorem harmonicWavelet_one_l2_norm_sq_eq :
    (∫ x in (0 : ℝ)..1,
      (∑ k ∈ Finset.Icc 1 3, harmonicWavelet 1 k * recipFractScaled k x) ^ 2) =
      Real.pi / Real.sqrt 3 := by
  have ht := harmonicWavelet_mem_tangent (m := 1) (N := 3) (by decide) (by decide)
  rw [tangent_l2_norm_sq_eq_qcot (harmonicWavelet 1) ht.1 ht.2, QCot_harmonicWavelet_one_eq]

/-- Exact `N = 3` variational optimum `SCot` at step size `t = 2 / 3`: `4 * π / (9 * √3)`. -/
theorem SCot_cBaseAnchor_add_two_thirds_wavelet_one_eq :
    SCot vasyuninGCot (fun k => cBaseAnchor k + (2 / 3 : ℝ) * harmonicWavelet 1 k) 3 =
      4 * Real.pi / (9 * Real.sqrt 3) := by
  rw [SCot_cBaseAnchor_add_smul_wavelet_eq (m := 1) (N := 3) (by decide) (by decide) (2 / 3)]
  have hS : SCot vasyuninGCot (harmonicWavelet 1) 3 = -(Real.pi / Real.sqrt 3) := by
    unfold SCot
    rw [QCot_harmonicWavelet_one_eq]
  have hd1 : deltaCot 1 = 0 := by simp [deltaCot, vasyuninCotSum]
  have hd2 : deltaCot 2 = 0 := by
    dsimp [deltaCot]
    rw [vasyuninCotSum_two_tan, vasyuninCotSum_two_tan, sub_self]
  have hd3 : deltaCot 3 = 2 / (3 * Real.sqrt 3) := by
    dsimp [deltaCot]
    rw [vasyuninCotSum_three_tan, vasyuninCotSum_three_tan]
    norm_num
    ring
  rw [hS, hd1, hd2, hd3]
  ring
