/-
Copyright (c) 2026 Qamar Munawer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qamar Munawer
-/
module

public import RiemannBlueprint.UpstreamPRs.UpstreamPR_4C_HarmonicWaveletBasis

/-!
# Unconstrained Tangent-Space Shift and Wavelet Cotangent Stencil on `A_N`

This file combines the zero-cotangent anchor `cBaseAnchor` and 3-point harmonic wavelets
`harmonicWavelet m` from `BaezDuarteWaveletBasis` to eliminate both `1 / k` denominators and the
quadratic anchor-anchor interactions from the Vasyunin cotangent score `SCot`:

* `deltaCot k := vasyuninCotSum k 2 - vasyuninCotSum k 1`: first-level cotangent contrast.
* `harmonicWavelet_div_sum_eq_second_diff`: multiplying `F k / k` by `harmonicWavelet m k` yields
  the exact unweighted second difference `F m - 2 * F (m + 1) + F (m + 2)`.
* `sum_cBaseAnchor_vasyuninGCot_eq`: exact linear cross-cotangent action of `cBaseAnchor`.
* `SCot_cBaseAnchor_add_eq`: exact unconstrained tangent-space shift formula for `SCot`.
* `SCot_cBaseAnchor_add_smul_wavelet_eq`: exact single-wavelet ray quadratic-plus-stencil law.
-/

@[expose] public section

open scoped BigOperators

/-- First-level Vasyunin cotangent contrast `deltaCot k = vasyuninCotSum k 2 - vasyuninCotSum k 1`.
-/
noncomputable def deltaCot (k : ℕ) : ℝ :=
  vasyuninCotSum k 2 - vasyuninCotSum k 1

private lemma sum_Icc_support_two_stencil (f : ℕ → ℝ) {N : ℕ} (hN : 2 ≤ N)
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

private lemma sum_Icc_support_three_stencil (m : ℕ) (f : ℕ → ℝ) {N : ℕ} (hm : 1 ≤ m)
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

/-- Denominator-free wavelet second-difference identity: multiplying `F k / k` by
`harmonicWavelet m k` cancels `1 / k` identically and yields `F m - 2 * F (m + 1) + F (m + 2)`. -/
theorem harmonicWavelet_div_sum_eq_second_diff (F : ℕ → ℝ) {m N : ℕ}
    (hm : 1 ≤ m) (hN : m + 2 ≤ N) :
    ∑ k ∈ Finset.Icc 1 N, harmonicWavelet m k * (F k / (k : ℝ)) =
      F m - 2 * F (m + 1) + F (m + 2) := by
  have hsup : ∑ k ∈ Finset.Icc 1 N, harmonicWavelet m k * (F k / (k : ℝ)) =
      harmonicWavelet m m * (F m / (m : ℝ)) +
        harmonicWavelet m (m + 1) * (F (m + 1) / ((m + 1 : ℕ) : ℝ)) +
          harmonicWavelet m (m + 2) * (F (m + 2) / ((m + 2 : ℕ) : ℝ)) :=
    sum_Icc_support_three_stencil m (fun k => harmonicWavelet m k * (F k / (k : ℝ))) hm hN
      (fun k h0 h1 h2 => by simp [harmonicWavelet, h0, h1, h2])
  have hw0 : harmonicWavelet m m = (m : ℝ) := by simp [harmonicWavelet]
  have hw1 : harmonicWavelet m (m + 1) = -2 * ((m : ℝ) + 1) := by simp [harmonicWavelet]
  have hw2 : harmonicWavelet m (m + 2) = (m : ℝ) + 2 := by simp [harmonicWavelet]
  have hm_ne : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hm1_ne : (m : ℝ) + 1 ≠ 0 := by positivity
  have hm2_ne : (m : ℝ) + 2 ≠ 0 := by positivity
  rw [hsup, hw0, hw1, hw2]
  push_cast
  field_simp [hm_ne, hm1_ne, hm2_ne]
  ring

private lemma vasyuninCotSum_two_stencil (b : ℕ) : vasyuninCotSum 2 b = 0 := by
  unfold vasyuninCotSum
  rw [show Finset.Ico 1 2 = ({1} : Finset ℕ) by ext x; simp, Finset.sum_singleton,
    show Real.pi * ((1 : ℕ) : ℝ) / ((2 : ℕ) : ℝ) = Real.pi / 2 by push_cast; ring,
    Real.cos_pi_div_two, zero_div, mul_zero]

/-- Exact linear cross-cotangent action of the 2-point base anchor `cBaseAnchor`. -/
theorem sum_cBaseAnchor_vasyuninGCot_eq {N : ℕ} (hN : 2 ≤ N) {k : ℕ} (hk : 1 ≤ k) :
    ∑ j ∈ Finset.Icc 1 N, cBaseAnchor j * vasyuninGCot j k =
      (Real.pi / (k : ℝ)) * (vasyuninCotSum k 1 - vasyuninCotSum k 2) := by
  have hsup : ∑ j ∈ Finset.Icc 1 N, cBaseAnchor j * vasyuninGCot j k =
      cBaseAnchor 1 * vasyuninGCot 1 k + cBaseAnchor 2 * vasyuninGCot 2 k :=
    sum_Icc_support_two_stencil (fun j => cBaseAnchor j * vasyuninGCot j k) hN
      (fun j hj1 hj2 => by
        have hc : cBaseAnchor j = 0 := by rcases j with _ | _ | _ | j <;> simp [cBaseAnchor] at *
        rw [hc, zero_mul])
  have hV1 : vasyuninCotSum 1 k = 0 := by simp [vasyuninCotSum]
  have hk_ne : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  rw [hsup]
  unfold vasyuninGCot
  rw [hV1, vasyuninCotSum_two_stencil]
  simp only [cBaseAnchor, Nat.cast_one, Nat.cast_ofNat, zero_add]
  field_simp [hk_ne]
  ring

/-- Unconstrained tangent-space shift identity for `SCot`: expanding
`SCot vasyuninGCot (cBaseAnchor + h) N` eliminates `SCot cBaseAnchor` and isolates a linear
`1 / k`-weighted cotangent contrast sum. -/
theorem SCot_cBaseAnchor_add_eq {N : ℕ} (hN : 2 ≤ N) (h : ℕ → ℝ) :
    SCot vasyuninGCot (fun k => cBaseAnchor k + h k) N =
      SCot vasyuninGCot h N +
        2 * Real.pi * ∑ k ∈ Finset.Icc 1 N,
          (h k / (k : ℝ)) * (vasyuninCotSum k 2 - vasyuninCotSum k 1) := by
  have hterm : ∀ j k : ℕ,
      (cBaseAnchor j + h j) * (cBaseAnchor k + h k) * vasyuninGCot j k =
        (cBaseAnchor j * cBaseAnchor k * vasyuninGCot j k + h j * h k * vasyuninGCot j k) +
          (h k * (cBaseAnchor j * vasyuninGCot j k) +
            h j * (cBaseAnchor k * vasyuninGCot k j)) := by
    intro j k
    rw [vasyuninGCot_comm k j]
    ring
  have hcross_eq :
      (∑ j ∈ Finset.Icc 1 N, ∑ k ∈ Finset.Icc 1 N, h k * (cBaseAnchor j * vasyuninGCot j k)) =
        ∑ k ∈ Finset.Icc 1 N, h k *
          ((Real.pi / (k : ℝ)) * (vasyuninCotSum k 1 - vasyuninCotSum k 2)) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [← Finset.mul_sum, sum_cBaseAnchor_vasyuninGCot_eq hN (Finset.mem_Icc.mp hk).1]
  have hcross_eq2 :
      (∑ j ∈ Finset.Icc 1 N, ∑ k ∈ Finset.Icc 1 N, h j * (cBaseAnchor k * vasyuninGCot k j)) =
        ∑ k ∈ Finset.Icc 1 N, h k *
          ((Real.pi / (k : ℝ)) * (vasyuninCotSum k 1 - vasyuninCotSum k 2)) := by
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [← Finset.mul_sum, sum_cBaseAnchor_vasyuninGCot_eq hN (Finset.mem_Icc.mp hj).1]
  have hQCot :
      QCot vasyuninGCot (fun k => cBaseAnchor k + h k) N =
        QCot vasyuninGCot cBaseAnchor N + QCot vasyuninGCot h N +
          2 * ∑ k ∈ Finset.Icc 1 N, h k *
            ((Real.pi / (k : ℝ)) * (vasyuninCotSum k 1 - vasyuninCotSum k 2)) := by
    unfold QCot
    simp_rw [hterm, Finset.sum_add_distrib]
    rw [hcross_eq, hcross_eq2]
    ring
  have hneg :
      -(2 * ∑ k ∈ Finset.Icc 1 N, h k *
          ((Real.pi / (k : ℝ)) * (vasyuninCotSum k 1 - vasyuninCotSum k 2))) =
        2 * Real.pi * ∑ k ∈ Finset.Icc 1 N,
          (h k / (k : ℝ)) * (vasyuninCotSum k 2 - vasyuninCotSum k 1) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  have hbase : -QCot vasyuninGCot cBaseAnchor N = 0 := by
    simpa [SCot] using SCot_cBaseAnchor_eq_zero N
  unfold SCot
  rw [hQCot]
  linarith [hbase, hneg]

private lemma SCot_smul_wavelet (t : ℝ) (u : ℕ → ℝ) (N : ℕ) :
    SCot vasyuninGCot (fun k => t * u k) N = t ^ 2 * SCot vasyuninGCot u N := by
  unfold SCot QCot
  have hpt : ∀ j k : ℕ,
      (t * u j) * (t * u k) * vasyuninGCot j k = t ^ 2 * (u j * u k * vasyuninGCot j k) :=
    fun _ _ => by ring
  simp_rw [hpt, ← Finset.mul_sum]
  ring

/-- Single-wavelet ray cotangent formula: evaluating `SCot` along
`cBaseAnchor + t • harmonicWavelet m` gives a scalar quadratic polynomial in `t` whose linear term
is `2 * π * t` times the second difference of `deltaCot`. -/
theorem SCot_cBaseAnchor_add_smul_wavelet_eq {m N : ℕ} (hm : 1 ≤ m) (hN : m + 2 ≤ N)
    (t : ℝ) :
    SCot vasyuninGCot (fun k => cBaseAnchor k + t * harmonicWavelet m k) N =
      t ^ 2 * SCot vasyuninGCot (harmonicWavelet m) N +
        2 * Real.pi * t * (deltaCot m - 2 * deltaCot (m + 1) + deltaCot (m + 2)) := by
  rw [SCot_cBaseAnchor_add_eq (by omega : 2 ≤ N) (fun k => t * harmonicWavelet m k),
    SCot_smul_wavelet]
  have hsum :
      (∑ k ∈ Finset.Icc 1 N,
        (t * harmonicWavelet m k / (k : ℝ)) * (vasyuninCotSum k 2 - vasyuninCotSum k 1)) =
        t * (deltaCot m - 2 * deltaCot (m + 1) + deltaCot (m + 2)) := by
    have hpt : ∀ k ∈ Finset.Icc 1 N,
        (t * harmonicWavelet m k / (k : ℝ)) * (vasyuninCotSum k 2 - vasyuninCotSum k 1) =
          t * (harmonicWavelet m k * (deltaCot k / (k : ℝ))) := fun k _ => by
      dsimp [deltaCot]
      ring
    rw [Finset.sum_congr rfl hpt, ← Finset.mul_sum,
      harmonicWavelet_div_sum_eq_second_diff deltaCot hm hN]
  rw [hsum]
  ring
