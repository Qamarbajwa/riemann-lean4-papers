/-
Copyright (c) 2026 Qamar Munawer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qamar Munawer
-/
module

public import RiemannBlueprint.UpstreamPRs.UpstreamPR_3H_VariationalOptimumFour
public import RiemannBlueprint.UpstreamPRs.UpstreamPR_4B_AffineOrthogonalDecomp

/-!
# Determinant-Free 2-Point Base Anchor and 3-Point Harmonic Wavelet Basis of `A_N`

This file introduces a determinant-free parameterization of the Báez-Duarte affine manifold
`A_N = {c : D1 c N = 0 ∧ D0 c N = 2}`:

* `cBaseAnchor`: the zero-cotangent 2-point anchor `(-2, 4, 0, 0, ...)`, satisfying
  `cBaseAnchor ∈ A_N` (`cBaseAnchor_mem_A_N`), `SCot vasyuninGCot cBaseAnchor N = 0`
  (`SCot_cBaseAnchor_eq_zero`), and `L²(0, 1)` error `1` (`cBaseAnchor_l2_dist_eq_one`).
* `harmonicWavelet m`: local 3-point wavelet `(m, -2(m + 1), m + 2)` supported on
  `{m, m + 1, m + 2}` with zero determinants or divisions, lying in the tangent space
  `A_N⁰ = {h : D1 h N = 0 ∧ D0 h N = 0}` (`harmonicWavelet_mem_tangent`).
* `cBaseAnchor_add_smul_wavelet_mem_A_N`: any finite linear combination of harmonic wavelets
  added to `cBaseAnchor` remains in `A_N`.
* `cVariationalFour_eq_wavelet_decomp`: exact wavelet coordinate representation of
  `cVariationalFour` as `cBaseAnchor + (19 / 20) • harmonicWavelet 1 + (11 / 40) •
  harmonicWavelet 2`.
-/

@[expose] public section

open scoped BigOperators

/-- Zero-cotangent 2-point anchor `(-2, 4, 0, 0, ...)` on `A_N` (`N ≥ 2`). -/
def cBaseAnchor : ℕ → ℝ
  | 1 => -2
  | 2 => 4
  | _ => 0

private lemma sum_Icc_of_support_two (f : ℕ → ℝ) {N : ℕ} (hN : 2 ≤ N)
    (hf : ∀ k, k ≠ 1 → k ≠ 2 → f k = 0) :
    ∑ k ∈ Finset.Icc 1 N, f k = f 1 + f 2 := by
  have h1 : (1 : ℕ) ∈ Finset.Icc 1 N := Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  have h2 : (2 : ℕ) ∈ Finset.Icc 1 N := Finset.mem_Icc.mpr ⟨by omega, hN⟩
  have heq : ∀ k ∈ Finset.Icc 1 N,
      f k = (if k = 1 then f 1 else 0) + (if k = 2 then f 2 else 0) := by
    intro k _
    rcases eq_or_ne k 1 with rfl | hk1
    · simp
    · rcases eq_or_ne k 2 with rfl | hk2
      · simp
      · simp [hk1, hk2, hf k hk1 hk2]
  rw [Finset.sum_congr rfl heq, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq']
  simp [h1, h2]

/-- `cBaseAnchor` lies in `A_N` unconditionally for all `N ≥ 2`. -/
theorem cBaseAnchor_mem_A_N {N : ℕ} (hN : 2 ≤ N) :
    D1 cBaseAnchor N = 0 ∧ D0 cBaseAnchor N = 2 := by
  have hD1 : D1 cBaseAnchor N = cBaseAnchor 1 / (1 : ℝ) + cBaseAnchor 2 / (2 : ℝ) := by
    unfold D1
    simpa only [Nat.cast_one, Nat.cast_ofNat] using
      sum_Icc_of_support_two (fun k => cBaseAnchor k / (k : ℝ)) hN
        (fun k hk1 hk2 => by
          have hk : cBaseAnchor k = 0 := by rcases k with _ | _ | _ | k <;> simp [cBaseAnchor] at *
          rw [hk, zero_div])
  have hD0 : D0 cBaseAnchor N = cBaseAnchor 1 + cBaseAnchor 2 :=
    sum_Icc_of_support_two cBaseAnchor hN
      (fun k hk1 hk2 => by rcases k with _ | _ | _ | k <;> simp [cBaseAnchor] at *)
  constructor
  · rw [hD1]; norm_num [cBaseAnchor]
  · rw [hD0]; norm_num [cBaseAnchor]

private lemma vasyuninCotSum_two_anchor (b : ℕ) : vasyuninCotSum 2 b = 0 := by
  unfold vasyuninCotSum
  rw [show Finset.Ico 1 2 = ({1} : Finset ℕ) by ext x; simp, Finset.sum_singleton,
    show Real.pi * ((1 : ℕ) : ℝ) / ((2 : ℕ) : ℝ) = Real.pi / 2 by push_cast; ring,
    Real.cos_pi_div_two, zero_div, mul_zero]

/-- All Vasyunin cotangent interactions on `{1, 2}` vanish, so `SCot` of `cBaseAnchor` is `0`
for all `N`. -/
theorem SCot_cBaseAnchor_eq_zero (N : ℕ) : SCot vasyuninGCot cBaseAnchor N = 0 := by
  have hV1 : ∀ b : ℕ, vasyuninCotSum 1 b = 0 := fun _ => by simp [vasyuninCotSum]
  have hG12 : vasyuninGCot 1 2 = 0 := by
    unfold vasyuninGCot
    rw [hV1, vasyuninCotSum_two_anchor]
    ring
  unfold SCot QCot
  have hzero :
      (∑ j ∈ Finset.Icc 1 N, ∑ k ∈ Finset.Icc 1 N,
        cBaseAnchor j * cBaseAnchor k * vasyuninGCot j k) = 0 := by
    refine Finset.sum_eq_zero fun j _ => Finset.sum_eq_zero fun k _ => ?_
    rcases j with _ | _ | _ | j <;> rcases k with _ | _ | _ | k <;>
      simp [cBaseAnchor, vasyuninGCot_diag, vasyuninGCot_comm, hG12]
  rw [hzero, neg_zero]

/-- `cBaseAnchor` achieves exact baseline `L²(0, 1)` Nyman–Beurling distance `1` for `N ≥ 2`. -/
theorem cBaseAnchor_l2_dist_eq_one {N : ℕ} (hN : 2 ≤ N) :
    (∫ x in (0 : ℝ)..1,
      (1 - ∑ k ∈ Finset.Icc 1 N, cBaseAnchor k * recipFractScaled k x) ^ 2) = 1 := by
  have ha := cBaseAnchor_mem_A_N hN
  rw [affine_l2_dist_eq_one_sub_scot cBaseAnchor ha.1 ha.2, SCot_cBaseAnchor_eq_zero N, sub_zero]

/-- Local 3-point harmonic wavelet supported on `{m, m + 1, m + 2}` with entries
`(m, -2(m + 1), m + 2)`. -/
def harmonicWavelet (m k : ℕ) : ℝ :=
  if k = m then (m : ℝ)
  else if k = m + 1 then -2 * ((m : ℝ) + 1)
  else if k = m + 2 then (m : ℝ) + 2
  else 0

private lemma sum_Icc_of_support_three (m : ℕ) (f : ℕ → ℝ) {N : ℕ} (hm : 1 ≤ m)
    (hN : m + 2 ≤ N) (hf : ∀ k, k ≠ m → k ≠ m + 1 → k ≠ m + 2 → f k = 0) :
    ∑ k ∈ Finset.Icc 1 N, f k = f m + f (m + 1) + f (m + 2) := by
  have hm0 : m ∈ Finset.Icc 1 N := Finset.mem_Icc.mpr ⟨hm, by omega⟩
  have hm1 : m + 1 ∈ Finset.Icc 1 N := Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  have hm2 : m + 2 ∈ Finset.Icc 1 N := Finset.mem_Icc.mpr ⟨by omega, hN⟩
  have heq : ∀ k ∈ Finset.Icc 1 N,
      f k =
        (if k = m then f m else 0) + (if k = m + 1 then f (m + 1) else 0) +
          (if k = m + 2 then f (m + 2) else 0) := by
    intro k _
    by_cases h0 : k = m
    · subst h0; simp
    · by_cases h1 : k = m + 1
      · subst h1; simp
      · by_cases h2 : k = m + 2
        · subst h2; simp
        · simp [h0, h1, h2, hf k h0 h1 h2]
  rw [Finset.sum_congr rfl heq, Finset.sum_add_distrib, Finset.sum_add_distrib,
    Finset.sum_ite_eq', Finset.sum_ite_eq', Finset.sum_ite_eq']
  simp [hm0, hm1, hm2]

/-- Every local 3-point harmonic wavelet lies unconditionally in the tangent hyperplane
`A_N⁰ = {h | D1 h N = 0 ∧ D0 h N = 0}` whenever `1 ≤ m` and `m + 2 ≤ N`. -/
theorem harmonicWavelet_mem_tangent {m N : ℕ} (hm : 1 ≤ m) (hN : m + 2 ≤ N) :
    D1 (harmonicWavelet m) N = 0 ∧ D0 (harmonicWavelet m) N = 0 := by
  have hD1 :
      D1 (harmonicWavelet m) N =
        harmonicWavelet m m / (m : ℝ) +
          harmonicWavelet m (m + 1) / ((m + 1 : ℕ) : ℝ) +
            harmonicWavelet m (m + 2) / ((m + 2 : ℕ) : ℝ) :=
    sum_Icc_of_support_three m (fun k => harmonicWavelet m k / (k : ℝ)) hm hN
      (fun k h0 h1 h2 => by simp [harmonicWavelet, h0, h1, h2])
  have hD0 :
      D0 (harmonicWavelet m) N =
        harmonicWavelet m m + harmonicWavelet m (m + 1) + harmonicWavelet m (m + 2) :=
    sum_Icc_of_support_three m (harmonicWavelet m) hm hN
      (fun k h0 h1 h2 => by simp [harmonicWavelet, h0, h1, h2])
  have hw0 : harmonicWavelet m m = (m : ℝ) := by simp [harmonicWavelet]
  have hw1 : harmonicWavelet m (m + 1) = -2 * ((m : ℝ) + 1) := by simp [harmonicWavelet]
  have hw2 : harmonicWavelet m (m + 2) = (m : ℝ) + 2 := by simp [harmonicWavelet]
  have hm_ne : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hm1_ne : (m : ℝ) + 1 ≠ 0 := by positivity
  have hm2_ne : (m : ℝ) + 2 ≠ 0 := by positivity
  constructor
  · rw [hD1, hw0, hw1, hw2]
    push_cast
    have h1 : (m : ℝ) / (m : ℝ) = 1 := div_self hm_ne
    have h2 : (-2 * ((m : ℝ) + 1)) / ((m : ℝ) + 1) = -2 := by field_simp [hm1_ne]
    have h3 : ((m : ℝ) + 2) / ((m : ℝ) + 2) = 1 := div_self hm2_ne
    rw [h1, h2, h3]
    ring
  · rw [hD0, hw0, hw1, hw2]
    ring

/-- Adding any finite linear combination of harmonic wavelets to `cBaseAnchor` preserves
membership in `A_N` (`D1 = 0 ∧ D0 = 2`). -/
theorem cBaseAnchor_add_smul_wavelet_mem_A_N {N : ℕ} (hN : 2 ≤ N)
    (s : Finset ℕ) (w : ℕ → ℝ) (hs : ∀ m ∈ s, 1 ≤ m ∧ m + 2 ≤ N) :
    D1 (fun k => cBaseAnchor k + ∑ m ∈ s, w m * harmonicWavelet m k) N = 0 ∧
      D0 (fun k => cBaseAnchor k + ∑ m ∈ s, w m * harmonicWavelet m k) N = 2 := by
  have ha := cBaseAnchor_mem_A_N hN
  have hsum1 :
      D1 (fun k => ∑ m ∈ s, w m * harmonicWavelet m k) N =
        ∑ m ∈ s, w m * D1 (harmonicWavelet m) N := by
    unfold D1
    simp_rw [Finset.sum_div, Finset.sum_comm (s := Finset.Icc 1 N) (t := s),
      mul_div_assoc, ← Finset.mul_sum]
  have hsum0 :
      D0 (fun k => ∑ m ∈ s, w m * harmonicWavelet m k) N =
        ∑ m ∈ s, w m * D0 (harmonicWavelet m) N := by
    unfold D0
    simp_rw [Finset.sum_comm (s := Finset.Icc 1 N) (t := s), ← Finset.mul_sum]
  have ht1 : D1 (fun k => ∑ m ∈ s, w m * harmonicWavelet m k) N = 0 := by
    rw [hsum1]
    exact Finset.sum_eq_zero fun m hm => by
      rw [(harmonicWavelet_mem_tangent (hs m hm).1 (hs m hm).2).1, mul_zero]
  have ht0 : D0 (fun k => ∑ m ∈ s, w m * harmonicWavelet m k) N = 0 := by
    rw [hsum0]
    exact Finset.sum_eq_zero fun m hm => by
      rw [(harmonicWavelet_mem_tangent (hs m hm).1 (hs m hm).2).2, mul_zero]
  constructor
  · have hsplit :
        D1 (fun k => cBaseAnchor k + ∑ m ∈ s, w m * harmonicWavelet m k) N =
          D1 cBaseAnchor N + D1 (fun k => ∑ m ∈ s, w m * harmonicWavelet m k) N := by
      unfold D1
      simp_rw [add_div, Finset.sum_add_distrib]
    rw [hsplit, ha.1, ht1, add_zero]
  · have hsplit :
        D0 (fun k => cBaseAnchor k + ∑ m ∈ s, w m * harmonicWavelet m k) N =
          D0 cBaseAnchor N + D0 (fun k => ∑ m ∈ s, w m * harmonicWavelet m k) N := by
      unfold D0
      exact Finset.sum_add_distrib
    rw [hsplit, ha.2, ht0, add_zero]

/-- Exact determinant-free wavelet coordinate decomposition of `cVariationalFour`. -/
theorem cVariationalFour_eq_wavelet_decomp (k : ℕ) :
    cVariationalFour k =
      cBaseAnchor k + (19 / 20 : ℝ) * harmonicWavelet 1 k +
        (11 / 40 : ℝ) * harmonicWavelet 2 k := by
  rcases k with _ | _ | _ | _ | _ | k <;>
    simp [cVariationalFour, cBaseAnchor, harmonicWavelet] <;> norm_num
