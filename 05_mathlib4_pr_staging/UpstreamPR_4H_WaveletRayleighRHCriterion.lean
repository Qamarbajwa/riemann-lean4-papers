/-
Copyright (c) 2026 Qamar Munawer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qamar Munawer
-/
module

public import RiemannBlueprint.UpstreamPRs.UpstreamPR_4G_GlobalOptimumFour

/-!
# Universal Affine-to-Rayleigh Duality and Multi-Wavelet Linearity for General `N ≥ 2`

This file extends the tangent Rayleigh quotient and wavelet basis framework on
`A_N = {c | D1 c N = 0 ∧ D0 c N = 2}` to arbitrary dimension `N ≥ 2`:

* `tangentRayleighQuotient_smul`: exact scale invariance
  `tangentRayleighQuotient (a • h) N = tangentRayleighQuotient h N` for all `a ≠ 0`.
* `sum_smul_harmonicWavelet_mem_tangent` and `linearCotDrive_sum_harmonicWavelet_eq`: arbitrary
  linear combinations of local 3-point harmonic wavelets lie in the tangent space `A_N⁰` and
  decompose `linearCotDrive` linearly into unweighted second differences of `deltaCot`.
* `sub_cBaseAnchor_mem_tangent`, `SCot_le_tangentRayleighQuotient_sub_cBaseAnchor`, and
  `one_sub_tangentRayleighQuotient_le_l2_dist`: universal affine-to-Rayleigh duality showing that
  every `c ∈ A_N` satisfies `SCot vasyuninGCot c N ≤ tangentRayleighQuotient (c - cBaseAnchor) N`
  and `1 - tangentRayleighQuotient (c - cBaseAnchor) N ≤ ‖1 - ∑ c_k {1/(kx)}‖₂²`.
-/

@[expose] public section

open scoped BigOperators
open MeasureTheory Finset

private lemma linearCotDrive_smul (a : ℝ) (h : ℕ → ℝ) (N : ℕ) :
    linearCotDrive (fun k => a * h k) N = a * linearCotDrive h N := by
  unfold linearCotDrive
  have hpt : ∀ k ∈ Finset.Icc 1 N,
      (a * h k / (k : ℝ)) * deltaCot k = a * ((h k / (k : ℝ)) * deltaCot k) :=
    fun _ _ => by ring
  rw [Finset.sum_congr rfl hpt, ← Finset.mul_sum]

private lemma QCot_smul (a : ℝ) (h : ℕ → ℝ) (N : ℕ) :
    QCot vasyuninGCot (fun k => a * h k) N = a ^ 2 * QCot vasyuninGCot h N := by
  unfold QCot
  have hpt : ∀ j ∈ Finset.Icc 1 N, ∀ k ∈ Finset.Icc 1 N,
      (a * h j) * (a * h k) * vasyuninGCot j k =
        a ^ 2 * (h j * h k * vasyuninGCot j k) := fun _ _ _ _ => by ring
  rw [Finset.sum_congr rfl fun j hj => Finset.sum_congr rfl fun k hk => hpt j hj k hk]
  simp_rw [← Finset.mul_sum]

/-- Exact scale invariance of the tangent Rayleigh quotient: for any `a ≠ 0`, rescaling a
direction `h` leaves `tangentRayleighQuotient` unchanged. -/
theorem tangentRayleighQuotient_smul (a : ℝ) (ha : a ≠ 0) (h : ℕ → ℝ) (N : ℕ) :
    tangentRayleighQuotient (fun k => a * h k) N = tangentRayleighQuotient h N := by
  unfold tangentRayleighQuotient
  rw [linearCotDrive_smul, QCot_smul,
    show (Real.pi * (a * linearCotDrive h N)) ^ 2 =
      a ^ 2 * (Real.pi * linearCotDrive h N) ^ 2 by ring,
    mul_div_mul_left _ _ (pow_ne_zero 2 ha)]

/-- Multi-wavelet tangent membership: any finite linear combination of 3-point harmonic wavelets
supported inside `Icc 1 N` satisfies `D1 h N = 0 ∧ D0 h N = 0`. -/
theorem sum_smul_harmonicWavelet_mem_tangent {N : ℕ} (s : Finset ℕ)
    (hs : ∀ m ∈ s, 1 ≤ m ∧ m + 2 ≤ N) (w : ℕ → ℝ) :
    D1 (fun k => ∑ m ∈ s, w m * harmonicWavelet m k) N = 0 ∧
      D0 (fun k => ∑ m ∈ s, w m * harmonicWavelet m k) N = 0 := by
  constructor
  · unfold D1
    have hpt : ∀ k ∈ Finset.Icc 1 N,
        (∑ m ∈ s, w m * harmonicWavelet m k) / (k : ℝ) =
          ∑ m ∈ s, w m * (harmonicWavelet m k / (k : ℝ)) := by
      intro k _
      rw [Finset.sum_div]
      exact Finset.sum_congr rfl fun m _ => by ring
    rw [Finset.sum_congr rfl hpt, Finset.sum_comm]
    refine Finset.sum_eq_zero fun m hm => ?_
    rw [← Finset.mul_sum]
    have hmem := (harmonicWavelet_mem_tangent (hs m hm).1 (hs m hm).2).1
    unfold D1 at hmem
    rw [hmem, mul_zero]
  · unfold D0
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun m hm => ?_
    rw [← Finset.mul_sum]
    have hmem := (harmonicWavelet_mem_tangent (hs m hm).1 (hs m hm).2).2
    unfold D0 at hmem
    rw [hmem, mul_zero]

/-- Linear decomposition of `linearCotDrive` on any multi-wavelet tangent vector into unweighted
second differences of `deltaCot`. -/
theorem linearCotDrive_sum_harmonicWavelet_eq {N : ℕ} (s : Finset ℕ)
    (hs : ∀ m ∈ s, 1 ≤ m ∧ m + 2 ≤ N) (w : ℕ → ℝ) :
    linearCotDrive (fun k => ∑ m ∈ s, w m * harmonicWavelet m k) N =
      ∑ m ∈ s, w m * (deltaCot m - 2 * deltaCot (m + 1) + deltaCot (m + 2)) := by
  unfold linearCotDrive
  have hpt : ∀ k ∈ Finset.Icc 1 N,
      ((∑ m ∈ s, w m * harmonicWavelet m k) / (k : ℝ)) * deltaCot k =
        ∑ m ∈ s, w m * (harmonicWavelet m k * (deltaCot k / (k : ℝ))) := by
    intro k _
    rw [Finset.sum_div, Finset.sum_mul]
    exact Finset.sum_congr rfl fun m _ => by ring
  rw [Finset.sum_congr rfl hpt, Finset.sum_comm]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [← Finset.mul_sum,
    harmonicWavelet_div_sum_eq_second_diff deltaCot (hs m hm).1 (hs m hm).2]

/-- Subtracting `cBaseAnchor` maps every affine vector `c ∈ A_N` into the homogeneous tangent
subspace `A_N⁰ = {h | D1 h N = 0 ∧ D0 h N = 0}`. -/
theorem sub_cBaseAnchor_mem_tangent {N : ℕ} (hN : 2 ≤ N) (c : ℕ → ℝ)
    (hc1 : D1 c N = 0) (hc0 : D0 c N = 2) :
    D1 (fun k => c k - cBaseAnchor k) N = 0 ∧ D0 (fun k => c k - cBaseAnchor k) N = 0 := by
  have ha := cBaseAnchor_mem_A_N hN
  constructor
  · unfold D1 at hc1 ha ⊢
    have hpt : ∀ k ∈ Finset.Icc 1 N,
        (c k - cBaseAnchor k) / (k : ℝ) = c k / (k : ℝ) - cBaseAnchor k / (k : ℝ) :=
      fun _ _ => by ring
    rw [Finset.sum_congr rfl hpt, Finset.sum_sub_distrib, hc1, ha.1, sub_self]
  · unfold D0 at hc0 ha ⊢
    rw [Finset.sum_sub_distrib, hc0, ha.2, sub_self]

/-- Universal affine-to-Rayleigh upper bound: for every `N ≥ 2` and every `c ∈ A_N`,
`SCot vasyuninGCot c N ≤ tangentRayleighQuotient (c - cBaseAnchor) N`. -/
theorem SCot_le_tangentRayleighQuotient_sub_cBaseAnchor {N : ℕ} (hN : 2 ≤ N) (c : ℕ → ℝ)
    (hc1 : D1 c N = 0) (hc0 : D0 c N = 2) :
    SCot vasyuninGCot c N ≤ tangentRayleighQuotient (fun k => c k - cBaseAnchor k) N := by
  let h : ℕ → ℝ := fun k => c k - cBaseAnchor k
  have ht := sub_cBaseAnchor_mem_tangent hN c hc1 hc0
  have hQ_nn : 0 ≤ QCot vasyuninGCot h N := QCot_nonneg_of_mem_tangent h ht.1 ht.2
  by_cases hq : QCot vasyuninGCot h N = 0
  · have hsq_le : (Real.pi * linearCotDrive h N) ^ 2 ≤ 0 := by
      rw [← hq]
      exact sq_linearCotDrive_le_qcot hN h ht.1 ht.2
    have hsq_eq : (Real.pi * linearCotDrive h N) ^ 2 = 0 := le_antisymm hsq_le (sq_nonneg _)
    have hdrv : linearCotDrive h N = 0 := by
      rcases mul_eq_zero.mp (sq_eq_zero_iff.mp hsq_eq) with hpi | hlin
      · exact False.elim (Real.pi_ne_zero hpi)
      · exact hlin
    have hc_eq : c = fun k => cBaseAnchor k + h k := funext fun k => by dsimp [h]; ring
    have hcot_add := SCot_cBaseAnchor_add_eq hN h
    have hsum_eq :
        (∑ k ∈ Finset.Icc 1 N, (h k / (k : ℝ)) * (vasyuninCotSum k 2 - vasyuninCotSum k 1)) =
          linearCotDrive h N := by
      unfold linearCotDrive deltaCot
      rfl
    have hSh : SCot vasyuninGCot h N = 0 := by simp [SCot, hq]
    have hSc : SCot vasyuninGCot c N = 0 := by
      rw [hc_eq, hcot_add, hsum_eq, hSh, hdrv, mul_zero, add_zero]
    have hR : tangentRayleighQuotient h N = 0 := by
      dsimp [tangentRayleighQuotient]
      rw [hq, div_zero]
    rw [hSc, hR]
  · have hc_eq : c = fun k => cBaseAnchor k + 1 * h k := funext fun k => by dsimp [h]; ring
    conv_lhs => rw [hc_eq]
    rw [SCot_cBaseAnchor_add_smul_eq_rayleigh_sub_sq hN h hq 1]
    have hsub_nn : 0 ≤ QCot vasyuninGCot h N * (1 - optTangentStep h N) ^ 2 :=
      mul_nonneg hQ_nn (sq_nonneg _)
    linarith

/-- Universal affine-to-Rayleigh `L²(0, 1)` lower bound over all `c ∈ A_N` for `N ≥ 2`. -/
theorem one_sub_tangentRayleighQuotient_le_l2_dist {N : ℕ} (hN : 2 ≤ N) (c : ℕ → ℝ)
    (hc1 : D1 c N = 0) (hc0 : D0 c N = 2) :
    1 - tangentRayleighQuotient (fun k => c k - cBaseAnchor k) N ≤
      ∫ x in (0 : ℝ)..1, (1 - ∑ k ∈ Finset.Icc 1 N, c k * recipFractScaled k x) ^ 2 := by
  rw [affine_l2_dist_eq_one_sub_scot c hc1 hc0]
  exact sub_le_sub_left (SCot_le_tangentRayleighQuotient_sub_cBaseAnchor hN c hc1 hc0) 1
