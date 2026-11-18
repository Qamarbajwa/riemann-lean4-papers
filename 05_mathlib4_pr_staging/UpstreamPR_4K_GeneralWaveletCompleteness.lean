/-
Copyright (c) 2026 Qamar Munawer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qamar Munawer
-/
module

public import RiemannBlueprint.UpstreamPRs.UpstreamPR_4J_FourPointDipoleKernel

/-!
# General-`N` Completeness of the Cumulative Dipole and Harmonic Wavelet Bases

This file proves that for every `N ≥ 2`, the cumulative dipoles `{v⁽ᵐ⁾}_{m=1}^{N-2}` and the
3-point harmonic wavelets `{w⁽ʳ⁾}_{r=1}^{N-2}` span the full Báez-Duarte tangent hyperplane
`A_N⁰ = {h | D1 h N = 0 ∧ D0 h N = 0}` and affine manifold `A_N = {c | D1 c N = 0 ∧ D0 c N = 2}`:

* `cumulativeDipole_eq_four_term`: exact 4-term closed-form formula for `cumulativeDipole m k`.
* `dipoleCoord` and `waveletCoord`: explicit suffix harmonic coordinate maps reconstructing any
  tangent vector `h ∈ A_N⁰` and any affine vector `c ∈ A_N` (`c - cBaseAnchor`).
* `eq_sum_cumulativeDipole_of_mem_tangent`, `eq_sum_harmonicWavelet_of_mem_tangent`:
  general-`N` basis completeness on `A_N⁰` for all `N ≥ 2`.
* `eq_cBaseAnchor_add_sum_cumulativeDipole_of_mem_A_N`,
  `eq_cBaseAnchor_add_sum_harmonicWavelet_of_mem_A_N`:
  general-`N` affine completeness on `A_N` for all `N ≥ 2`.
-/

@[expose] public section

open scoped BigOperators

/-- Exact 4-term closed-form formula for `cumulativeDipole m k` (`1 ≤ m`). -/
theorem cumulativeDipole_eq_four_term {m : ℕ} (hm : 1 ≤ m) (k : ℕ) :
    cumulativeDipole m k =
      (if k = 1 then (1 : ℝ) else 0) + (if k = 2 then (-2 : ℝ) else 0) -
        (if k = m + 1 then ((m + 1 : ℕ) : ℝ) else 0) +
        (if k = m + 2 then ((m + 2 : ℕ) : ℝ) else 0) := by
  induction m, hm using Nat.le_induction with
  | base =>
    rcases k with _ | _ | _ | _ | k <;> simp [cumulativeDipole, harmonicWavelet] <;> ring
  | succ r hr ih =>
    unfold cumulativeDipole
    rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ r + 1)]
    have hprev : (∑ j ∈ Finset.Icc 1 r, harmonicWavelet j k) = cumulativeDipole r k := rfl
    rw [hprev, ih]
    unfold harmonicWavelet
    split_ifs <;> try omega
    all_goals push_cast; ring

/-- Suffix harmonic coordinate map for the cumulative dipole basis `{cumulativeDipole m}`. -/
noncomputable def dipoleCoord (c : ℕ → ℝ) (N m : ℕ) : ℝ :=
  ∑ j ∈ Finset.Icc (m + 2) N, c j / (j : ℝ)

/-- Cumulative wavelet coordinate map for the 3-point harmonic wavelet basis
`{harmonicWavelet r}`. -/
noncomputable def waveletCoord (c : ℕ → ℝ) (N r : ℕ) : ℝ :=
  ∑ m ∈ Finset.Icc r (N - 2), dipoleCoord c N m

private lemma sum_Icc_one_split (f : ℕ → ℝ) {N : ℕ} (hN : 2 ≤ N) :
    ∑ j ∈ Finset.Icc 1 N, f j = f 1 + f 2 + ∑ j ∈ Finset.Icc 3 N, f j := by
  have hpart : Finset.Icc 1 N = insert 1 (insert 2 (Finset.Icc 3 N)) := by
    ext j; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
  rw [hpart, Finset.sum_insert (by simp), Finset.sum_insert (by simp)]
  ring

private lemma sum_dipoleCoord_eq (h : ℕ → ℝ) {N : ℕ} (hN : 2 ≤ N)
    (hh1 : D1 h N = 0) (hh0 : D0 h N = 0) :
    ∑ m ∈ Finset.Icc 1 (N - 2), dipoleCoord h N m = h 1 := by
  have hD1 : h 1 / (1 : ℝ) + h 2 / (2 : ℝ) + ∑ j ∈ Finset.Icc 3 N, h j / (j : ℝ) = 0 := by
    simpa [D1, sum_Icc_one_split (fun j => h j / (j : ℝ)) hN] using hh1
  have hD0 : h 1 + h 2 + ∑ j ∈ Finset.Icc 3 N, h j = 0 := by
    simpa [D0, sum_Icc_one_split h hN] using hh0
  have hswap :
      (∑ m ∈ Finset.Icc 1 (N - 2), dipoleCoord h N m) =
        ∑ j ∈ Finset.Icc 3 N, ∑ m ∈ Finset.Icc 1 (N - 2),
          if m + 2 ≤ j then h j / (j : ℝ) else 0 := by
    rw [← Finset.sum_comm]
    refine Finset.sum_congr rfl fun m hm => ?_
    have hm1 : 1 ≤ m := (Finset.mem_Icc.mp hm).1
    have hsplit : Finset.Icc (m + 2) N = (Finset.Icc 3 N).filter (fun j => m + 2 ≤ j) := by
      ext j; simp only [Finset.mem_Icc, Finset.mem_filter]; omega
    unfold dipoleCoord
    rw [hsplit, Finset.sum_filter]
  have hinner :
      (∑ j ∈ Finset.Icc 3 N, ∑ m ∈ Finset.Icc 1 (N - 2),
          if m + 2 ≤ j then h j / (j : ℝ) else 0) =
        ∑ j ∈ Finset.Icc 3 N, (h j - 2 * (h j / (j : ℝ))) := by
    refine Finset.sum_congr rfl fun j hj => ?_
    have hj3 : 3 ≤ j := (Finset.mem_Icc.mp hj).1
    have hjN : j ≤ N := (Finset.mem_Icc.mp hj).2
    have hj_ne : (j : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have hfilt : (Finset.Icc 1 (N - 2)).filter (fun m => m + 2 ≤ j) = Finset.Icc 1 (j - 2) := by
      ext m; simp only [Finset.mem_filter, Finset.mem_Icc]; omega
    rw [← Finset.sum_filter, hfilt, Finset.sum_const, Nat.card_Icc, nsmul_eq_mul,
      show ((j - 2 + 1 - 1 : ℕ) : ℝ) = (j : ℝ) - 2 by
        rw [show j - 2 + 1 - 1 = j - 2 by omega, Nat.cast_sub (by omega : 2 ≤ j)]; norm_num]
    field_simp [hj_ne]
  rw [hswap, hinner, Finset.sum_sub_distrib, ← Finset.mul_sum]
  norm_num at hD1
  linarith

private lemma sum_dipoleCoord_mul_ite_add (c : ℕ → ℝ) (N d k : ℕ) :
    (∑ m ∈ Finset.Icc 1 (N - 2),
        dipoleCoord c N m * (if k = m + d then ((m + d : ℕ) : ℝ) else 0)) =
      if 1 + d ≤ k ∧ k ≤ N - 2 + d then (k : ℝ) * dipoleCoord c N (k - d) else 0 := by
  split_ifs with hk
  · have hmem : k - d ∈ Finset.Icc 1 (N - 2) := Finset.mem_Icc.mpr ⟨by omega, by omega⟩
    rw [Finset.sum_eq_single (k - d)]
    · have hkd : k - d + d = k := by omega
      simp [hkd, mul_comm]
    · intro m _ hm_ne
      simp [show k ≠ m + d by omega]
    · intro habs; exact False.elim (habs hmem)
  · refine Finset.sum_eq_zero fun m hm => ?_
    have := Finset.mem_Icc.mp hm
    simp [show k ≠ m + d by omega]

/-- General-`N` completeness of the cumulative dipole basis on `A_N⁰`: for every `N ≥ 2`, every
tangent vector `h ∈ A_N⁰`, and every `k ∈ Icc 1 N`, `h k` is the exact linear combination of
`cumulativeDipole m k` with coefficients `dipoleCoord h N m`. -/
theorem eq_sum_cumulativeDipole_of_mem_tangent {N : ℕ} (hN : 2 ≤ N) (h : ℕ → ℝ)
    (hh1 : D1 h N = 0) (hh0 : D0 h N = 0) {k : ℕ} (hk : k ∈ Finset.Icc 1 N) :
    h k = ∑ m ∈ Finset.Icc 1 (N - 2), dipoleCoord h N m * cumulativeDipole m k := by
  have hpt : ∀ m ∈ Finset.Icc 1 (N - 2),
      dipoleCoord h N m * cumulativeDipole m k =
        dipoleCoord h N m * (if k = 1 then (1 : ℝ) else 0) +
          dipoleCoord h N m * (if k = 2 then (-2 : ℝ) else 0) -
          dipoleCoord h N m * (if k = m + 1 then ((m + 1 : ℕ) : ℝ) else 0) +
          dipoleCoord h N m * (if k = m + 2 then ((m + 2 : ℕ) : ℝ) else 0) := by
    intro m hm; rw [cumulativeDipole_eq_four_term (Finset.mem_Icc.mp hm).1 k]; ring
  rw [Finset.sum_congr rfl hpt, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_mul,
    sum_dipoleCoord_eq h hN hh1 hh0,
    sum_dipoleCoord_mul_ite_add h N 1 k,
    sum_dipoleCoord_mul_ite_add h N 2 k]
  rcases Finset.mem_Icc.mp hk with ⟨hk1, hkN⟩
  rcases eq_or_ne k 1 with rfl | hk_ne1
  · simp
  · rcases eq_or_ne k 2 with rfl | hk_ne2
    · by_cases hN3 : 3 ≤ N
      · have hD1 : h 1 / (1 : ℝ) + h 2 / (2 : ℝ) + ∑ j ∈ Finset.Icc 3 N, h j / (j : ℝ) = 0 := by
          simpa [D1, sum_Icc_one_split (fun j => h j / (j : ℝ)) hN] using hh1
        have hd1 : dipoleCoord h N 1 = ∑ j ∈ Finset.Icc 3 N, h j / (j : ℝ) := rfl
        split_ifs <;> try omega
        norm_num at hD1 hd1 ⊢; linarith
      · have hN2 : N = 2 := by omega
        subst hN2
        have hD1 : h 1 / (1 : ℝ) + h 2 / (2 : ℝ) = 0 := by
          simpa [D1, sum_Icc_one_split (fun j => h j / (j : ℝ)) le_rfl] using hh1
        have hD0 : h 1 + h 2 = 0 := by
          simpa [D0, sum_Icc_one_split h le_rfl] using hh0
        split_ifs <;> try omega
        norm_num at hD1 hD0 ⊢; linarith
    · have hk3 : 3 ≤ k := by omega
      have hk_ne : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      have hc2 : dipoleCoord h N (k - 2) =
          h k / (k : ℝ) + ∑ j ∈ Finset.Icc (k + 1) N, h j / (j : ℝ) := by
        unfold dipoleCoord
        have hpart : Finset.Icc (k - 2 + 2) N = insert k (Finset.Icc (k + 1) N) := by
          ext j; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
        rw [hpart, Finset.sum_insert (by simp)]
      have ht4 : (k : ℝ) * dipoleCoord h N (k - 2) =
          h k + (k : ℝ) * ∑ j ∈ Finset.Icc (k + 1) N, h j / (j : ℝ) := by
        rw [hc2, mul_add, mul_div_cancel₀ _ hk_ne]
      by_cases hlast : k = N
      · subst hlast
        split_ifs <;> try omega
        rw [ht4, Finset.Icc_eq_empty (by omega : ¬k + 1 ≤ k), Finset.sum_empty]
        ring
      · have hc1 : dipoleCoord h N (k - 1) = ∑ j ∈ Finset.Icc (k + 1) N, h j / (j : ℝ) := by
          unfold dipoleCoord; rw [show k - 1 + 2 = k + 1 by omega]
        split_ifs <;> try omega
        rw [ht4, hc1]
        ring

/-- General-`N` completeness of the 3-point harmonic wavelet basis on `A_N⁰`: for every `N ≥ 2`,
every `h ∈ A_N⁰`, and every `k ∈ Icc 1 N`, `h k` is the exact linear combination of
`harmonicWavelet r k` with coefficients `waveletCoord h N r`. -/
theorem eq_sum_harmonicWavelet_of_mem_tangent {N : ℕ} (hN : 2 ≤ N) (h : ℕ → ℝ)
    (hh1 : D1 h N = 0) (hh0 : D0 h N = 0) {k : ℕ} (hk : k ∈ Finset.Icc 1 N) :
    h k = ∑ r ∈ Finset.Icc 1 (N - 2), waveletCoord h N r * harmonicWavelet r k := by
  rw [eq_sum_cumulativeDipole_of_mem_tangent hN h hh1 hh0 hk]
  have hexp :
      (∑ m ∈ Finset.Icc 1 (N - 2), dipoleCoord h N m * cumulativeDipole m k) =
        ∑ m ∈ Finset.Icc 1 (N - 2), ∑ r ∈ Finset.Icc 1 (N - 2),
          if r ≤ m then dipoleCoord h N m * harmonicWavelet r k else 0 := by
    refine Finset.sum_congr rfl fun m hm => ?_
    have hmN : m ≤ N - 2 := (Finset.mem_Icc.mp hm).2
    have hfilt : Finset.Icc 1 m = (Finset.Icc 1 (N - 2)).filter (fun r => r ≤ m) := by
      ext r; simp only [Finset.mem_Icc, Finset.mem_filter]; omega
    unfold cumulativeDipole
    rw [Finset.mul_sum, hfilt, Finset.sum_filter]
  rw [hexp, Finset.sum_comm]
  refine Finset.sum_congr rfl fun r hr => ?_
  have hr1 : 1 ≤ r := (Finset.mem_Icc.mp hr).1
  have hfilt : Finset.Icc r (N - 2) = (Finset.Icc 1 (N - 2)).filter (fun m => r ≤ m) := by
    ext m; simp only [Finset.mem_Icc, Finset.mem_filter]; omega
  unfold waveletCoord
  rw [Finset.sum_mul, hfilt, Finset.sum_filter]

private lemma dipoleCoord_sub_cBaseAnchor (c : ℕ → ℝ) {N m : ℕ} (hm : 1 ≤ m) :
    dipoleCoord (fun k => c k - cBaseAnchor k) N m = dipoleCoord c N m := by
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj3 : 3 ≤ j := by have := (Finset.mem_Icc.mp hj).1; omega
  have hanch : cBaseAnchor j = 0 := by
    rcases j with _ | _ | _ | j <;> [omega; omega; omega; rfl]
  dsimp only; rw [hanch, sub_zero]

private lemma waveletCoord_sub_cBaseAnchor (c : ℕ → ℝ) {N r : ℕ} (hr : 1 ≤ r) :
    waveletCoord (fun k => c k - cBaseAnchor k) N r = waveletCoord c N r := by
  refine Finset.sum_congr rfl fun m hm => ?_
  exact dipoleCoord_sub_cBaseAnchor c (by have := (Finset.mem_Icc.mp hm).1; omega)

/-- General-`N` completeness of the cumulative dipole basis on `A_N`: for every `N ≥ 2`, every
`c ∈ A_N`, and every `k ∈ Icc 1 N`, `c k` equals `cBaseAnchor k` plus the cumulative dipole
expansion with coordinates `dipoleCoord c N m`. -/
theorem eq_cBaseAnchor_add_sum_cumulativeDipole_of_mem_A_N {N : ℕ} (hN : 2 ≤ N) (c : ℕ → ℝ)
    (hc1 : D1 c N = 0) (hc0 : D0 c N = 2) {k : ℕ} (hk : k ∈ Finset.Icc 1 N) :
    c k = cBaseAnchor k +
      ∑ m ∈ Finset.Icc 1 (N - 2), dipoleCoord c N m * cumulativeDipole m k := by
  have ht := sub_cBaseAnchor_mem_tangent hN c hc1 hc0
  have hrec := eq_sum_cumulativeDipole_of_mem_tangent hN (fun j => c j - cBaseAnchor j) ht.1 ht.2 hk
  have hsum :
      (∑ m ∈ Finset.Icc 1 (N - 2),
          dipoleCoord (fun j => c j - cBaseAnchor j) N m * cumulativeDipole m k) =
        ∑ m ∈ Finset.Icc 1 (N - 2), dipoleCoord c N m * cumulativeDipole m k := by
    refine Finset.sum_congr rfl fun m hm => ?_
    rw [dipoleCoord_sub_cBaseAnchor c (Finset.mem_Icc.mp hm).1]
  rw [hsum] at hrec; linarith

/-- General-`N` completeness of the 3-point harmonic wavelet basis on `A_N`: for every `N ≥ 2`,
every `c ∈ A_N`, and every `k ∈ Icc 1 N`, `c k` equals `cBaseAnchor k` plus the harmonic wavelet
expansion with coordinates `waveletCoord c N r`. -/
theorem eq_cBaseAnchor_add_sum_harmonicWavelet_of_mem_A_N {N : ℕ} (hN : 2 ≤ N) (c : ℕ → ℝ)
    (hc1 : D1 c N = 0) (hc0 : D0 c N = 2) {k : ℕ} (hk : k ∈ Finset.Icc 1 N) :
    c k = cBaseAnchor k +
      ∑ r ∈ Finset.Icc 1 (N - 2), waveletCoord c N r * harmonicWavelet r k := by
  have ht := sub_cBaseAnchor_mem_tangent hN c hc1 hc0
  have hrec := eq_sum_harmonicWavelet_of_mem_tangent hN (fun j => c j - cBaseAnchor j) ht.1 ht.2 hk
  have hsum :
      (∑ r ∈ Finset.Icc 1 (N - 2),
          waveletCoord (fun j => c j - cBaseAnchor j) N r * harmonicWavelet r k) =
        ∑ r ∈ Finset.Icc 1 (N - 2), waveletCoord c N r * harmonicWavelet r k := by
    refine Finset.sum_congr rfl fun r hr => ?_
    rw [waveletCoord_sub_cBaseAnchor c (Finset.mem_Icc.mp hr).1]
  rw [hsum] at hrec; linarith
