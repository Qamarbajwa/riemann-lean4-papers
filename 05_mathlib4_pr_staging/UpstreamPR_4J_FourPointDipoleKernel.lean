/-
Copyright (c) 2026 Qamar Munawer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qamar Munawer
-/
module

public import RiemannBlueprint.UpstreamPRs.UpstreamPR_4I_CumulativeWaveletDipole

/-!
# Four-Point Support of `cumulativeDipole` and N-Independent Dipole Gram Matrix Law

This file establishes the exact 4-point dual telescoping support of the cumulative wavelet dipole
basis and collapses the `N × N` double sum of the dipole Gram matrix `⟨dₐ, d_b⟩_G` into an
explicit `N`-independent 4-point kernel difference:

* `cumulativeDipole_div_sum_eq_four_point`: for any `F : ℕ → ℝ`, `1 ≤ m`, and `m + 2 ≤ N`,
  `∑ k ∈ Icc 1 N, cumulativeDipole m k * (F k / k) = F 1 - F 2 - F (m + 1) + F (m + 2)`.
* `unweightedKCot`, `unweightedKCot_comm`, `unweightedKCot_diag`, `unweightedKCot_one_sub_two`:
  the unweighted symmetric cotangent kernel `(j : ℝ) * (k : ℝ) * vasyuninGCot j k` and its
  exact boundary contrast identity `unweightedKCot 1 k - unweightedKCot 2 k = (π / 2) * deltaCot k`.
* `sum_cumulativeDipole_vasyuninGCot_eq_four_point`: exact `N`-independent 4-point closed form
  collapsing `∑ j ∈ Icc 1 N, ∑ k ∈ Icc 1 N, cumulativeDipole a j * cumulativeDipole b k * G j k`
  to local boundary differences on `{1, 2, a + 1, a + 2} × {1, 2, b + 1, b + 2}`.
-/

@[expose] public section

open scoped BigOperators
open MeasureTheory Finset

/-- Exact 4-point telescoping support of `cumulativeDipole`: integrating any sequence `F k / k`
against `cumulativeDipole m k` over `1..N` collapses to `F 1 - F 2 - F (m + 1) + F (m + 2)`. -/
theorem cumulativeDipole_div_sum_eq_four_point (F : ℕ → ℝ) {m N : ℕ}
    (hm : 1 ≤ m) (hN : m + 2 ≤ N) :
    ∑ k ∈ Finset.Icc 1 N, cumulativeDipole m k * (F k / (k : ℝ)) =
      F 1 - F 2 - F (m + 1) + F (m + 2) := by
  have hterm : ∀ k ∈ Finset.Icc 1 N,
      cumulativeDipole m k * (F k / (k : ℝ)) =
        ∑ r ∈ Finset.Icc 1 m, harmonicWavelet r k * (F k / (k : ℝ)) := by
    intro k _
    unfold cumulativeDipole
    rw [Finset.sum_mul]
  rw [Finset.sum_congr rfl hterm, Finset.sum_comm]
  have hinner :
      (∑ r ∈ Finset.Icc 1 m, ∑ k ∈ Finset.Icc 1 N, harmonicWavelet r k * (F k / (k : ℝ))) =
        ∑ r ∈ Finset.Icc 1 m, (F r - 2 * F (r + 1) + F (r + 2)) := by
    refine Finset.sum_congr rfl fun r hr => ?_
    have hr1 : 1 ≤ r := (Finset.mem_Icc.mp hr).1
    have hr2 : r + 2 ≤ N := by have := (Finset.mem_Icc.mp hr).2; omega
    exact harmonicWavelet_div_sum_eq_second_diff F hr1 hr2
  rw [hinner]
  clear hterm hinner hN
  induction m, hm using Nat.le_induction with
  | base =>
    simp only [Finset.Icc_self, Finset.sum_singleton]
    ring
  | succ k hk ih =>
    rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ k + 1), ih]
    ring

/-- Unweighted symmetric cotangent kernel `K(j, k) = j * k * vasyuninGCot j k`. -/
noncomputable def unweightedKCot (j k : ℕ) : ℝ :=
  (j : ℝ) * (k : ℝ) * vasyuninGCot j k

/-- Symmetry of `unweightedKCot`: `unweightedKCot j k = unweightedKCot k j`. -/
theorem unweightedKCot_comm (j k : ℕ) : unweightedKCot j k = unweightedKCot k j := by
  unfold unweightedKCot
  rw [vasyuninGCot_comm j k]
  ring

/-- Vanishing of `unweightedKCot` on the diagonal: `unweightedKCot k k = 0`. -/
theorem unweightedKCot_diag (k : ℕ) : unweightedKCot k k = 0 := by
  unfold unweightedKCot
  rw [vasyuninGCot_diag k, mul_zero]

private lemma vasyuninCotSum_two_fp (b : ℕ) : vasyuninCotSum 2 b = 0 := by
  unfold vasyuninCotSum
  rw [show Finset.Ico 1 2 = ({1} : Finset ℕ) by ext x; simp, Finset.sum_singleton,
    show Real.pi * ((1 : ℕ) : ℝ) / ((2 : ℕ) : ℝ) = Real.pi / 2 by push_cast; ring,
    Real.cos_pi_div_two, zero_div, mul_zero]

/-- Exact boundary contrast of `unweightedKCot`: for every `1 ≤ k`,
`unweightedKCot 1 k - unweightedKCot 2 k = (π / 2) * deltaCot k`. -/
theorem unweightedKCot_one_sub_two {k : ℕ} (hk : 1 ≤ k) :
    unweightedKCot 1 k - unweightedKCot 2 k = (Real.pi / 2) * deltaCot k := by
  have hk_ne : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hV1 : vasyuninCotSum 1 k = 0 := by simp [vasyuninCotSum]
  unfold unweightedKCot vasyuninGCot deltaCot
  rw [hV1, vasyuninCotSum_two_fp]
  simp only [Nat.cast_one, Nat.cast_ofNat, zero_add]
  field_simp [hk_ne]
  ring

/-- Exact `N`-independent 4-point closed form for the cumulative dipole Gram matrix for all
`1 ≤ a`, `1 ≤ b`, `a + 2 ≤ N`, and `b + 2 ≤ N`. -/
theorem sum_cumulativeDipole_vasyuninGCot_eq_four_point {a b N : ℕ}
    (ha : 1 ≤ a) (hb : 1 ≤ b) (haN : a + 2 ≤ N) (hbN : b + 2 ≤ N) :
    ∑ j ∈ Finset.Icc 1 N, ∑ k ∈ Finset.Icc 1 N,
      cumulativeDipole a j * cumulativeDipole b k * vasyuninGCot j k =
        (Real.pi / 2) *
            (deltaCot (a + 2) - deltaCot (a + 1) + deltaCot (b + 2) - deltaCot (b + 1)) +
          (unweightedKCot (a + 1) (b + 1) - unweightedKCot (a + 1) (b + 2) -
            unweightedKCot (a + 2) (b + 1) + unweightedKCot (a + 2) (b + 2)) := by
  have hstep1 :
      (∑ j ∈ Finset.Icc 1 N, ∑ k ∈ Finset.Icc 1 N,
        cumulativeDipole a j * cumulativeDipole b k * vasyuninGCot j k) =
        ∑ k ∈ Finset.Icc 1 N,
          cumulativeDipole b k *
            ((∑ j ∈ Finset.Icc 1 N, cumulativeDipole a j * (unweightedKCot j k / (j : ℝ))) /
              (k : ℝ)) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk_ne : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by have := (Finset.mem_Icc.mp hk).1; omega)
    rw [Finset.sum_div, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hj_ne : (j : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by have := (Finset.mem_Icc.mp hj).1; omega)
    unfold unweightedKCot
    field_simp [hj_ne, hk_ne]
  have hstep2 :
      (∑ k ∈ Finset.Icc 1 N,
        cumulativeDipole b k *
          ((∑ j ∈ Finset.Icc 1 N, cumulativeDipole a j * (unweightedKCot j k / (j : ℝ))) /
            (k : ℝ))) =
        ∑ k ∈ Finset.Icc 1 N,
          cumulativeDipole b k *
            (((Real.pi / 2) * deltaCot k - unweightedKCot (a + 1) k +
              unweightedKCot (a + 2) k) / (k : ℝ)) := by
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hk).1
    rw [cumulativeDipole_div_sum_eq_four_point (fun j => unweightedKCot j k) ha haN]
    have hdiff := unweightedKCot_one_sub_two hk1
    have hlin :
        unweightedKCot 1 k - unweightedKCot 2 k - unweightedKCot (a + 1) k +
            unweightedKCot (a + 2) k =
          (Real.pi / 2) * deltaCot k - unweightedKCot (a + 1) k + unweightedKCot (a + 2) k := by
      linarith
    rw [hlin]
  let F : ℕ → ℝ := fun k =>
    (Real.pi / 2) * deltaCot k - unweightedKCot (a + 1) k + unweightedKCot (a + 2) k
  have hstep3 :
      (∑ k ∈ Finset.Icc 1 N, cumulativeDipole b k * (F k / (k : ℝ))) =
        F 1 - F 2 - F (b + 1) + F (b + 2) :=
    cumulativeDipole_div_sum_eq_four_point F hb hbN
  rw [hstep1, hstep2]
  change (∑ k ∈ Finset.Icc 1 N, cumulativeDipole b k * (F k / (k : ℝ))) = _
  rw [hstep3]
  dsimp [F]
  have hd1 : deltaCot 1 = 0 := by simp [deltaCot, vasyuninCotSum]
  have hd2 : deltaCot 2 = 0 := by
    dsimp [deltaCot]; rw [vasyuninCotSum_two_fp, vasyuninCotSum_two_fp, sub_self]
  have ha1 := unweightedKCot_one_sub_two (by omega : 1 ≤ a + 1)
  have ha2 := unweightedKCot_one_sub_two (by omega : 1 ≤ a + 2)
  rw [unweightedKCot_comm (a + 1) 1, unweightedKCot_comm (a + 1) 2,
    unweightedKCot_comm (a + 2) 1, unweightedKCot_comm (a + 2) 2]
  rw [hd1, hd2]
  linear_combination ha2 - ha1
