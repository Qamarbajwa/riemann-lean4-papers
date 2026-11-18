/-
Copyright (c) 2026 Qamar Munawer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qamar Munawer
-/
module

public import RiemannBlueprint.UpstreamPRs.UpstreamPR_4A_AffineLagrangeProjection

/-!
# Orthogonal Tangent Decomposition of the Báez-Duarte Affine Manifold `A_N`

This file develops the Euclidean Hilbert-space geometry of the 2-constraint Báez-Duarte affine
manifold `A_N = {c : D1 c N = 0 ∧ D0 c N = 2}`:

* `cMinNorm N := projectAffine (fun _ => 0) N`: the unique minimum-`ℓ²`-norm element of `A_N`,
  given explicitly by `cMinNorm N k = (2 * S2Sum N - 2 * HSum N / k) / DeltaDet N`.
* `cMinNorm_mem_A_N_uncond`: unconditional membership `cMinNorm N ∈ A_N` for all `N ≥ 2`.
* `cMinNorm_inner_eq_zero`: orthogonality of `cMinNorm N` to the tangent hyperplane
  `A_N⁰ = {h : D1 h N = 0 ∧ D0 h N = 0}`.
* `cMinNorm_norm_sq_eq`: exact minimum squared `ℓ²`-norm `4 * S2Sum N / DeltaDet N`.
* `norm_sq_eq_cMinNorm_add_sub_sq` and `cMinNorm_le_norm_sq_on_A_N`: exact Pythagorean
  decomposition and lower bound on `A_N`.
* `cMinNorm_norm_sq_four`: exact rational value `164 / 39` at `N = 4`.
-/

@[expose] public section

open scoped BigOperators

/-- The minimum-`ℓ²`-norm base vector on the Báez-Duarte affine manifold `A_N`, defined by
projecting the zero vector via `projectAffine`. -/
noncomputable def cMinNorm (N : ℕ) : ℕ → ℝ :=
  projectAffine (fun _ => 0) N

/-- Closed-form formula `cMinNorm N k = (2 * S2Sum N - 2 * HSum N / k) / DeltaDet N`. -/
theorem cMinNorm_eq (N k : ℕ) :
    cMinNorm N k = (2 * S2Sum N - 2 * HSum N / (k : ℝ)) / DeltaDet N := by
  unfold cMinNorm projectAffine lambda1 lambda0
  simp only [zero_div, Finset.sum_const_zero, zero_sub, mul_neg, mul_zero, sub_zero]
  ring

/-- Unconditional membership of `cMinNorm N` in `A_N` for every `N ≥ 2`. -/
theorem cMinNorm_mem_A_N_uncond {N : ℕ} (hN : 2 ≤ N) :
    D1 (cMinNorm N) N = 0 ∧ D0 (cMinNorm N) N = 2 :=
  projectAffine_mem_A_N_uncond (fun _ => 0) hN

/-- Orthogonality of `cMinNorm N` to every vector `h` in the tangent hyperplane
`A_N⁰ = {h | D1 h N = 0 ∧ D0 h N = 0}`. -/
theorem cMinNorm_inner_eq_zero {N : ℕ} (h : ℕ → ℝ) (hh1 : D1 h N = 0) (hh0 : D0 h N = 0) :
    ∑ k ∈ Finset.Icc 1 N, cMinNorm N k * h k = 0 := by
  have hterm : ∀ k ∈ Finset.Icc 1 N,
      cMinNorm N k * h k =
        -(lambda0 (fun _ => 0) N) * h k + -(lambda1 (fun _ => 0) N) * (h k / (k : ℝ)) := by
    intro k _
    unfold cMinNorm projectAffine
    ring
  rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  change -(lambda0 (fun _ => 0) N) * D0 h N + -(lambda1 (fun _ => 0) N) * D1 h N = 0
  rw [hh0, hh1, mul_zero, mul_zero, add_zero]

/-- Exact minimum squared `ℓ²`-norm identity `∑ k ∈ Icc 1 N, (cMinNorm N k)^2 = 4 * S2 / Δ`. -/
theorem cMinNorm_norm_sq_eq {N : ℕ} (hΔ : DeltaDet N ≠ 0) :
    ∑ k ∈ Finset.Icc 1 N, cMinNorm N k ^ 2 = 4 * S2Sum N / DeltaDet N := by
  have h1 : D1 (cMinNorm N) N = 0 := projectAffine_D1 (fun _ => 0) N hΔ
  have h0 : D0 (cMinNorm N) N = 2 := projectAffine_D0 (fun _ => 0) N hΔ
  have hterm : ∀ k ∈ Finset.Icc 1 N,
      cMinNorm N k ^ 2 =
        (2 * S2Sum N / DeltaDet N) * cMinNorm N k -
          (2 * HSum N / DeltaDet N) * (cMinNorm N k / (k : ℝ)) := by
    intro k _
    have hc := cMinNorm_eq N k
    rw [sq, hc]
    ring
  rw [Finset.sum_congr rfl hterm, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  change (2 * S2Sum N / DeltaDet N) * D0 (cMinNorm N) N -
      (2 * HSum N / DeltaDet N) * D1 (cMinNorm N) N = 4 * S2Sum N / DeltaDet N
  rw [h0, h1]
  ring

private lemma tangent_sub_mem {N : ℕ} {c : ℕ → ℝ} (hΔ : DeltaDet N ≠ 0)
    (hc1 : D1 c N = 0) (hc0 : D0 c N = 2) :
    D1 (fun k => c k - cMinNorm N k) N = 0 ∧ D0 (fun k => c k - cMinNorm N k) N = 0 := by
  have hm1 : D1 (cMinNorm N) N = 0 := projectAffine_D1 (fun _ => 0) N hΔ
  have hm0 : D0 (cMinNorm N) N = 2 := projectAffine_D0 (fun _ => 0) N hΔ
  constructor
  · have hsplit :
        D1 (fun k => c k - cMinNorm N k) N = D1 c N - D1 (cMinNorm N) N := by
      unfold D1
      simp_rw [sub_div, Finset.sum_sub_distrib]
    rw [hsplit, hc1, hm1, sub_self]
  · have hsplit :
        D0 (fun k => c k - cMinNorm N k) N = D0 c N - D0 (cMinNorm N) N := by
      unfold D0
      exact Finset.sum_sub_distrib (f := c) (g := cMinNorm N)
    rw [hsplit, hc0, hm0, sub_self]

/-- Exact Pythagorean decomposition on `A_N` for `N ≥ 2`:
`∑_{k=1}^N c_k^2 = 4 * S2Sum N / DeltaDet N + ∑_{k=1}^N (c_k - cMinNorm N k)^2`. -/
theorem norm_sq_eq_cMinNorm_add_sub_sq {N : ℕ} (hN : 2 ≤ N) (c : ℕ → ℝ)
    (hc1 : D1 c N = 0) (hc0 : D0 c N = 2) :
    ∑ k ∈ Finset.Icc 1 N, c k ^ 2 =
      4 * S2Sum N / DeltaDet N + ∑ k ∈ Finset.Icc 1 N, (c k - cMinNorm N k) ^ 2 := by
  have hΔ : DeltaDet N ≠ 0 := DeltaDet_ne_zero hN
  have htan := tangent_sub_mem hΔ hc1 hc0
  have horth : ∑ k ∈ Finset.Icc 1 N, cMinNorm N k * (c k - cMinNorm N k) = 0 :=
    cMinNorm_inner_eq_zero (fun k => c k - cMinNorm N k) htan.1 htan.2
  have hterm : ∀ k ∈ Finset.Icc 1 N,
      c k ^ 2 =
        cMinNorm N k ^ 2 + 2 * (cMinNorm N k * (c k - cMinNorm N k)) +
          (c k - cMinNorm N k) ^ 2 := fun _ _ => by ring
  rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
    horth, mul_zero, add_zero, cMinNorm_norm_sq_eq hΔ]

/-- Unconditional minimum-`ℓ²`-norm lower bound on `A_N` (`N ≥ 2`):
`4 * S2Sum N / DeltaDet N ≤ ∑_{k=1}^N c_k^2`. -/
theorem cMinNorm_le_norm_sq_on_A_N {N : ℕ} (hN : 2 ≤ N) (c : ℕ → ℝ)
    (hc1 : D1 c N = 0) (hc0 : D0 c N = 2) :
    4 * S2Sum N / DeltaDet N ≤ ∑ k ∈ Finset.Icc 1 N, c k ^ 2 := by
  rw [norm_sq_eq_cMinNorm_add_sub_sq hN c hc1 hc0]
  exact le_add_of_nonneg_right (Finset.sum_nonneg fun _ _ => sq_nonneg _)

/-- Exact rational minimum squared `ℓ²`-norm benchmark at `N = 4`: `164 / 39`. -/
theorem cMinNorm_norm_sq_four :
    ∑ k ∈ Finset.Icc 1 4, cMinNorm 4 k ^ 2 = 164 / 39 := by
  rw [cMinNorm_norm_sq_eq (DeltaDet_ne_zero (by decide : 2 ≤ 4)), S2Sum_four, DeltaDet_four]
  norm_num
