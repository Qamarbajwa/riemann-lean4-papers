/-
Copyright (c) 2026 Qamar Munawer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qamar Munawer
-/
module

public import RiemannBlueprint.UpstreamPRs.UpstreamPR_4E_TangentCotangentPositivity

/-!
# Scale-Invariant Tangent Rayleigh Quotient and Unconditional Cotangent Cauchy–Schwarz Inequality

This file derives the exact closed-form ray optimization law along any tangent direction
`h ∈ A_N⁰ = {h | D1 h N = 0 ∧ D0 h N = 0}` anchored at `cBaseAnchor = (-2, 4, 0, ...)`:

* `linearCotDrive h N`: `1 / k`-weighted cotangent drive `∑ k ∈ Icc 1 N, (h k / k) * δ_k`.
* `optTangentStep h N` and `tangentRayleighQuotient h N`: the exact optimal step `t*` and
  achievable ray score `ℛ_cot(h, N) = (π * linearCotDrive h N)^2 / QCot vasyuninGCot h N`.
* `SCot_cBaseAnchor_add_smul_eq_rayleigh_sub_sq` and `SCot_cBaseAnchor_add_optTangentStep_eq`:
  exact completing-the-square ray formula along `cBaseAnchor + t • h`.
* `sq_linearCotDrive_le_qcot` and `tangentRayleighQuotient_le_one`: unconditional cotangent
  Cauchy–Schwarz inequality `(π * linearCotDrive h N)^2 ≤ QCot vasyuninGCot h N` and
  scale-invariant ceiling `tangentRayleighQuotient h N ≤ 1` for all `h ∈ A_N⁰`.
* `SCot_cBaseAnchor_add_smul_wavelet_one_eq_completing_sq` and
  `SCot_cBaseAnchor_add_smul_wavelet_one_le`: global variational optimality of `t* = 2 / 3`
  along `harmonicWavelet 1` at `N = 3`, achieving `4 * π / (9 * √3)`.
-/

@[expose] public section

open scoped BigOperators
open MeasureTheory Finset

/-- Linear `1 / k`-weighted cotangent drive `∑ k ∈ Icc 1 N, (h k / k) * deltaCot k`. -/
noncomputable def linearCotDrive (h : ℕ → ℝ) (N : ℕ) : ℝ :=
  ∑ k ∈ Finset.Icc 1 N, (h k / (k : ℝ)) * deltaCot k

/-- Optimal scalar step size along a tangent direction `h` anchored at `cBaseAnchor`. -/
noncomputable def optTangentStep (h : ℕ → ℝ) (N : ℕ) : ℝ :=
  Real.pi * linearCotDrive h N / QCot vasyuninGCot h N

/-- Scale-invariant tangent Rayleigh quotient
`(π * linearCotDrive h N)^2 / QCot vasyuninGCot h N`. -/
noncomputable def tangentRayleighQuotient (h : ℕ → ℝ) (N : ℕ) : ℝ :=
  (Real.pi * linearCotDrive h N) ^ 2 / QCot vasyuninGCot h N

private lemma SCot_smul_rayleigh (t : ℝ) (h : ℕ → ℝ) (N : ℕ) :
    SCot vasyuninGCot (fun k => t * h k) N = -(t ^ 2 * QCot vasyuninGCot h N) := by
  unfold SCot QCot
  have hpt : ∀ j k : ℕ,
      (t * h j) * (t * h k) * vasyuninGCot j k = t ^ 2 * (h j * h k * vasyuninGCot j k) :=
    fun _ _ => by ring
  simp_rw [hpt, ← Finset.mul_sum]

private lemma SCot_cBaseAnchor_add_smul_linear {N : ℕ} (hN : 2 ≤ N) (h : ℕ → ℝ) (t : ℝ) :
    SCot vasyuninGCot (fun k => cBaseAnchor k + t * h k) N =
      -(t ^ 2 * QCot vasyuninGCot h N) + 2 * Real.pi * t * linearCotDrive h N := by
  rw [SCot_cBaseAnchor_add_eq hN (fun k => t * h k), SCot_smul_rayleigh]
  have hsum :
      (∑ k ∈ Finset.Icc 1 N,
        (t * h k / (k : ℝ)) * (vasyuninCotSum k 2 - vasyuninCotSum k 1)) =
        t * linearCotDrive h N := by
    have hpt : ∀ k ∈ Finset.Icc 1 N,
        (t * h k / (k : ℝ)) * (vasyuninCotSum k 2 - vasyuninCotSum k 1) =
          t * ((h k / (k : ℝ)) * deltaCot k) := fun k _ => by
      dsimp [deltaCot]
      ring
    rw [Finset.sum_congr rfl hpt, ← Finset.mul_sum]
    rfl
  rw [hsum]
  ring

/-- Exact completing-the-square identity along any tangent ray `cBaseAnchor + t • h` whenever
`QCot vasyuninGCot h N ≠ 0`. -/
theorem SCot_cBaseAnchor_add_smul_eq_rayleigh_sub_sq {N : ℕ} (hN : 2 ≤ N) (h : ℕ → ℝ)
    (hq : QCot vasyuninGCot h N ≠ 0) (t : ℝ) :
    SCot vasyuninGCot (fun k => cBaseAnchor k + t * h k) N =
      tangentRayleighQuotient h N -
        QCot vasyuninGCot h N * (t - optTangentStep h N) ^ 2 := by
  rw [SCot_cBaseAnchor_add_smul_linear hN h t]
  dsimp [tangentRayleighQuotient, optTangentStep]
  field_simp [hq]
  ring

/-- Optimal ray achievement at `t = optTangentStep h N`:
`SCot vasyuninGCot (cBaseAnchor + optTangentStep h N • h) N = tangentRayleighQuotient h N`. -/
theorem SCot_cBaseAnchor_add_optTangentStep_eq {N : ℕ} (hN : 2 ≤ N) (h : ℕ → ℝ)
    (hq : QCot vasyuninGCot h N ≠ 0) :
    SCot vasyuninGCot (fun k => cBaseAnchor k + optTangentStep h N * h k) N =
      tangentRayleighQuotient h N := by
  rw [SCot_cBaseAnchor_add_smul_eq_rayleigh_sub_sq hN h hq (optTangentStep h N), sub_self,
    zero_pow (by decide), mul_zero, sub_zero]

private lemma cBaseAnchor_add_tangent_mem_A_N {N : ℕ} (hN : 2 ≤ N) {h : ℕ → ℝ}
    (hh1 : D1 h N = 0) (hh0 : D0 h N = 0) (t : ℝ) :
    D1 (fun k => cBaseAnchor k + t * h k) N = 0 ∧
      D0 (fun k => cBaseAnchor k + t * h k) N = 2 := by
  have ha := cBaseAnchor_mem_A_N hN
  constructor
  · have hsplit : D1 (fun k => cBaseAnchor k + t * h k) N = D1 cBaseAnchor N + t * D1 h N := by
      unfold D1
      have hpt : ∀ k ∈ Finset.Icc 1 N,
          (cBaseAnchor k + t * h k) / (k : ℝ) = cBaseAnchor k / (k : ℝ) + t * (h k / (k : ℝ)) :=
        fun _ _ => by ring
      rw [Finset.sum_congr rfl hpt, Finset.sum_add_distrib, ← Finset.mul_sum]
    rw [hsplit, ha.1, hh1, mul_zero, add_zero]
  · have hsplit : D0 (fun k => cBaseAnchor k + t * h k) N = D0 cBaseAnchor N + t * D0 h N := by
      unfold D0
      simp_rw [Finset.sum_add_distrib, ← Finset.mul_sum]
    rw [hsplit, ha.2, hh0, mul_zero, add_zero]

private lemma SCot_cBaseAnchor_add_smul_le_one {N : ℕ} (hN : 2 ≤ N) {h : ℕ → ℝ}
    (hh1 : D1 h N = 0) (hh0 : D0 h N = 0) (t : ℝ) :
    SCot vasyuninGCot (fun k => cBaseAnchor k + t * h k) N ≤ 1 := by
  have hc := cBaseAnchor_add_tangent_mem_A_N hN hh1 hh0 t
  have hnonneg :
      0 ≤ ∫ x in (0 : ℝ)..1,
        (1 - ∑ k ∈ Finset.Icc 1 N, (cBaseAnchor k + t * h k) * recipFractScaled k x) ^ 2 :=
    intervalIntegral.integral_nonneg (by norm_num) fun _ _ => sq_nonneg _
  rw [affine_l2_dist_eq_one_sub_scot (fun k => cBaseAnchor k + t * h k) hc.1 hc.2] at hnonneg
  linarith

/-- **Unconditional Cotangent Cauchy–Schwarz Inequality on `A_N⁰`**: for every `N ≥ 2` and every
tangent vector `h ∈ A_N⁰`, `(π * linearCotDrive h N)^2 ≤ QCot vasyuninGCot h N`. -/
theorem sq_linearCotDrive_le_qcot {N : ℕ} (hN : 2 ≤ N) (h : ℕ → ℝ)
    (hh1 : D1 h N = 0) (hh0 : D0 h N = 0) :
    (Real.pi * linearCotDrive h N) ^ 2 ≤ QCot vasyuninGCot h N := by
  have hQ_nn : 0 ≤ QCot vasyuninGCot h N := QCot_nonneg_of_mem_tangent h hh1 hh0
  rcases lt_or_eq_of_le hQ_nn with hQ_pos | hQ_zero
  · have hle : tangentRayleighQuotient h N ≤ 1 := by
      rw [← SCot_cBaseAnchor_add_optTangentStep_eq hN h hQ_pos.ne']
      exact SCot_cBaseAnchor_add_smul_le_one hN hh1 hh0 (optTangentStep h N)
    exact (div_le_one hQ_pos).mp hle
  · rw [← hQ_zero]
    by_cases hL : Real.pi * linearCotDrive h N = 0
    · rw [hL, zero_pow (by decide)]
    · exfalso
      have hsc := SCot_cBaseAnchor_add_smul_le_one hN hh1 hh0 (1 / (Real.pi * linearCotDrive h N))
      rw [SCot_cBaseAnchor_add_smul_linear hN h (1 / (Real.pi * linearCotDrive h N)), ← hQ_zero,
        mul_zero, neg_zero, zero_add] at hsc
      have h2 : 2 * Real.pi * (1 / (Real.pi * linearCotDrive h N)) * linearCotDrive h N = 2 := by
        rw [show 2 * Real.pi * (1 / (Real.pi * linearCotDrive h N)) * linearCotDrive h N =
          2 * ((Real.pi * linearCotDrive h N) * (1 / (Real.pi * linearCotDrive h N))) by ring,
          mul_one_div_cancel hL, mul_one]
      linarith

/-- Unconditional scale-invariant ceiling `tangentRayleighQuotient h N ≤ 1` for all `N ≥ 2` and
every tangent vector `h ∈ A_N⁰`. -/
theorem tangentRayleighQuotient_le_one {N : ℕ} (hN : 2 ≤ N) (h : ℕ → ℝ)
    (hh1 : D1 h N = 0) (hh0 : D0 h N = 0) :
    tangentRayleighQuotient h N ≤ 1 := by
  have hQ_nn : 0 ≤ QCot vasyuninGCot h N := QCot_nonneg_of_mem_tangent h hh1 hh0
  rcases lt_or_eq_of_le hQ_nn with hQ_pos | hQ_zero
  · exact (div_le_one hQ_pos).mpr (sq_linearCotDrive_le_qcot hN h hh1 hh0)
  · dsimp [tangentRayleighQuotient]
    rw [← hQ_zero, div_zero]
    norm_num

private lemma cot_pi_div_three_ray : Real.cos (Real.pi / 3) / Real.sin (Real.pi / 3) = 1 / √3 := by
  rw [Real.cos_pi_div_three, Real.sin_pi_div_three]
  field_simp [(Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 3)).ne']

private lemma cot_two_pi_div_three_ray :
    Real.cos (2 * Real.pi / 3) / Real.sin (2 * Real.pi / 3) = -(1 / √3) := by
  rw [show 2 * Real.pi / 3 = Real.pi - Real.pi / 3 by ring, Real.cos_pi_sub, Real.sin_pi_sub,
    neg_div, cot_pi_div_three_ray]

private lemma vasyuninCotSum_two_ray (b : ℕ) : vasyuninCotSum 2 b = 0 := by
  unfold vasyuninCotSum
  rw [show Finset.Ico 1 2 = ({1} : Finset ℕ) by ext x; simp, Finset.sum_singleton,
    show Real.pi * ((1 : ℕ) : ℝ) / ((2 : ℕ) : ℝ) = Real.pi / 2 by push_cast; ring,
    Real.cos_pi_div_two, zero_div, mul_zero]

private lemma vasyuninCotSum_three_ray (b : ℕ) :
    vasyuninCotSum 3 b =
      (Int.fract ((b : ℝ) / 3) - Int.fract (2 * (b : ℝ) / 3)) * (1 / √3) := by
  unfold vasyuninCotSum
  rw [show Finset.Ico 1 3 = ({1, 2} : Finset ℕ) by ext x; simp; omega,
    Finset.sum_insert (by decide), Finset.sum_singleton]
  push_cast
  rw [show (1 : ℝ) * b / 3 = b / 3 by ring, show Real.pi * 1 / 3 = Real.pi / 3 by ring,
    show Real.pi * 2 / 3 = 2 * Real.pi / 3 by ring, cot_pi_div_three_ray, cot_two_pi_div_three_ray]
  ring

private lemma linearCotDrive_wavelet_one_eq :
    linearCotDrive (harmonicWavelet 1) 3 = 2 / (3 * Real.sqrt 3) := by
  have hrew : linearCotDrive (harmonicWavelet 1) 3 =
      ∑ k ∈ Finset.Icc 1 3, harmonicWavelet 1 k * (deltaCot k / (k : ℝ)) :=
    Finset.sum_congr rfl fun k _ => by ring
  have hdrv : linearCotDrive (harmonicWavelet 1) 3 =
      deltaCot 1 - 2 * deltaCot 2 + deltaCot 3 := by
    rw [hrew]
    exact harmonicWavelet_div_sum_eq_second_diff deltaCot
      (by decide : 1 ≤ 1) (by decide : 1 + 2 ≤ 3)
  have hd1 : deltaCot 1 = 0 := by simp [deltaCot, vasyuninCotSum]
  have hd2 : deltaCot 2 = 0 := by
    dsimp [deltaCot]; rw [vasyuninCotSum_two_ray, vasyuninCotSum_two_ray, sub_self]
  have hd3 : deltaCot 3 = 2 / (3 * Real.sqrt 3) := by
    dsimp [deltaCot]; rw [vasyuninCotSum_three_ray, vasyuninCotSum_three_ray]; norm_num; ring
  rw [hdrv, hd1, hd2, hd3]
  ring

/-- Exact completing-the-square ray formula along `cBaseAnchor + t • harmonicWavelet 1` at `N = 3`.
-/
theorem SCot_cBaseAnchor_add_smul_wavelet_one_eq_completing_sq (t : ℝ) :
    SCot vasyuninGCot (fun k => cBaseAnchor k + t * harmonicWavelet 1 k) 3 =
      4 * Real.pi / (9 * Real.sqrt 3) - (Real.pi / Real.sqrt 3) * (t - 2 / 3) ^ 2 := by
  have hQ_ne : QCot vasyuninGCot (harmonicWavelet 1) 3 ≠ 0 := by
    rw [QCot_harmonicWavelet_one_eq]; positivity
  rw [SCot_cBaseAnchor_add_smul_eq_rayleigh_sub_sq (by decide : 2 ≤ 3) (harmonicWavelet 1) hQ_ne t]
  have hsq3_ne : Real.sqrt 3 ≠ 0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  have hpi_ne : Real.pi ≠ 0 := Real.pi_pos.ne'
  have hopt : optTangentStep (harmonicWavelet 1) 3 = 2 / 3 := by
    dsimp [optTangentStep]
    rw [linearCotDrive_wavelet_one_eq, QCot_harmonicWavelet_one_eq]
    field_simp [hsq3_ne, hpi_ne]
  have hray : tangentRayleighQuotient (harmonicWavelet 1) 3 = 4 * Real.pi / (9 * Real.sqrt 3) := by
    dsimp [tangentRayleighQuotient]
    rw [linearCotDrive_wavelet_one_eq, QCot_harmonicWavelet_one_eq]
    field_simp [hsq3_ne, hpi_ne]
    ring
  rw [hopt, hray, QCot_harmonicWavelet_one_eq]

/-- Global variational optimality on `A_3`: along `cBaseAnchor + t • harmonicWavelet 1`,
`SCot` is globally bounded above by `4 * π / (9 * √3)` for every `t : ℝ`. -/
theorem SCot_cBaseAnchor_add_smul_wavelet_one_le (t : ℝ) :
    SCot vasyuninGCot (fun k => cBaseAnchor k + t * harmonicWavelet 1 k) 3 ≤
      4 * Real.pi / (9 * Real.sqrt 3) := by
  rw [SCot_cBaseAnchor_add_smul_wavelet_one_eq_completing_sq t]
  have hsq_nn : 0 ≤ (Real.pi / Real.sqrt 3) * (t - 2 / 3) ^ 2 := by positivity
  linarith
