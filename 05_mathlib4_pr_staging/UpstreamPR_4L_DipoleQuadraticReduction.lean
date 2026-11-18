/-
Copyright (c) 2026 Qamar Munawer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qamar Munawer
-/
module

public import RiemannBlueprint.UpstreamPRs.UpstreamPR_4K_GeneralWaveletCompleteness

/-!
# Master `N`-Independent Dipole Quadratic Reduction of `SCot` and `N = 4` Overshoot Certificate

This file establishes the exact suffix–prefix coordinate duality and collapses `SCot vasyuninGCot`
on the Báez-Duarte affine manifold `A_N` (`N ≥ 2`) into an `N`-independent linear-quadratic form in
the suffix coordinates `dipoleCoord c N m`:

* `dipoleCoord_eq_neg_sum_Icc_of_D1_eq_zero`: exact suffix–prefix duality on `D1 c N = 0`.
* `dipoleGramEntry`: the `N`-independent 4-point dipole Gram kernel entry `⟨dₐ, d_b⟩_G`.
* `linearCotDrive_eq_sum_dipoleCoord`, `QCot_eq_sum_dipoleGramEntry`,
  `SCot_eq_dipoleCoord_quadratic_of_mem_A_N`: master linear-quadratic reductions on `A_N⁰` and
  `A_N` for every `N ≥ 2`.
* `dipoleCoord_cGlobalOptFour_eval`, `dipoleCoord_cCandidateMobius_four_eval`,
  `dipoleCoord_cGlobalOptFour_two_lt_cCandidateMobius_four`: exact `N = 4` dipole coordinates and
  strict `k = 4` overshoot witness `(5 - √3) / 12 < 7 / 24`.
-/

@[expose] public section

open scoped BigOperators

/-- Suffix–prefix duality: on `D1 c N = 0`, the suffix coordinate `dipoleCoord c N m` equals
the negated prefix sum `-∑ j ∈ Icc 1 (m + 1), c j / j` for every `m + 1 ≤ N`. -/
theorem dipoleCoord_eq_neg_sum_Icc_of_D1_eq_zero (c : ℕ → ℝ) {N m : ℕ}
    (hc1 : D1 c N = 0) (hm : m + 1 ≤ N) :
    dipoleCoord c N m = -∑ j ∈ Finset.Icc 1 (m + 1), c j / (j : ℝ) := by
  have hunion : Finset.Icc 1 N = Finset.Icc 1 (m + 1) ∪ Finset.Icc (m + 2) N := by
    ext j; simp only [Finset.mem_Icc, Finset.mem_union]; omega
  have hdisj : Disjoint (Finset.Icc 1 (m + 1)) (Finset.Icc (m + 2) N) :=
    Finset.disjoint_left.mpr fun j h1 h2 => by simp only [Finset.mem_Icc] at h1 h2; omega
  unfold D1 at hc1
  rw [hunion, Finset.sum_union hdisj] at hc1
  unfold dipoleCoord
  linarith

/-- `N`-independent 4-point dipole Gram kernel entry `⟨dₐ, d_b⟩_G`. -/
noncomputable def dipoleGramEntry (a b : ℕ) : ℝ :=
  (Real.pi / 2) * (deltaCot (a + 2) - deltaCot (a + 1) + deltaCot (b + 2) - deltaCot (b + 1)) +
    (unweightedKCot (a + 1) (b + 1) - unweightedKCot (a + 1) (b + 2) -
      unweightedKCot (a + 2) (b + 1) + unweightedKCot (a + 2) (b + 2))

/-- Exact reduction of `linearCotDrive h N` into `dipoleCoord h N m` on `A_N⁰` for all `N ≥ 2`. -/
theorem linearCotDrive_eq_sum_dipoleCoord {N : ℕ} (hN : 2 ≤ N) (h : ℕ → ℝ)
    (hh1 : D1 h N = 0) (hh0 : D0 h N = 0) :
    linearCotDrive h N =
      ∑ m ∈ Finset.Icc 1 (N - 2), dipoleCoord h N m * (deltaCot (m + 2) - deltaCot (m + 1)) := by
  unfold linearCotDrive
  have hpt : ∀ k ∈ Finset.Icc 1 N,
      (h k / (k : ℝ)) * deltaCot k =
        ∑ m ∈ Finset.Icc 1 (N - 2),
          dipoleCoord h N m * ((cumulativeDipole m k / (k : ℝ)) * deltaCot k) := by
    intro k hk
    rw [eq_sum_cumulativeDipole_of_mem_tangent hN h hh1 hh0 hk, Finset.sum_div, Finset.sum_mul]
    refine Finset.sum_congr rfl fun m _ => by ring
  rw [Finset.sum_congr rfl hpt, Finset.sum_comm]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [← Finset.mul_sum]
  have hdrv := linearCotDrive_cumulativeDipole_eq (Finset.mem_Icc.mp hm).1
    (by have := (Finset.mem_Icc.mp hm).2; omega : m + 2 ≤ N)
  unfold linearCotDrive at hdrv
  rw [hdrv]

/-- Exact `N`-independent 4-point dipole Gram reduction of `QCot` on `A_N⁰` for all `N ≥ 2`. -/
theorem QCot_eq_sum_dipoleGramEntry {N : ℕ} (hN : 2 ≤ N) (h : ℕ → ℝ)
    (hh1 : D1 h N = 0) (hh0 : D0 h N = 0) :
    QCot vasyuninGCot h N =
      ∑ a ∈ Finset.Icc 1 (N - 2), ∑ b ∈ Finset.Icc 1 (N - 2),
        dipoleCoord h N a * dipoleCoord h N b * dipoleGramEntry a b := by
  unfold QCot
  have hpt : ∀ j ∈ Finset.Icc 1 N, ∀ k ∈ Finset.Icc 1 N,
      h j * h k * vasyuninGCot j k =
        ∑ a ∈ Finset.Icc 1 (N - 2), ∑ b ∈ Finset.Icc 1 (N - 2),
          dipoleCoord h N a * dipoleCoord h N b *
            (cumulativeDipole a j * cumulativeDipole b k * vasyuninGCot j k) := by
    intro j hj k hk
    rw [eq_sum_cumulativeDipole_of_mem_tangent hN h hh1 hh0 hj,
      eq_sum_cumulativeDipole_of_mem_tangent hN h hh1 hh0 hk, Finset.sum_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun b _ => by ring
  have hswap1 :
      (∑ j ∈ Finset.Icc 1 N, ∑ k ∈ Finset.Icc 1 N, h j * h k * vasyuninGCot j k) =
        ∑ a ∈ Finset.Icc 1 (N - 2), ∑ j ∈ Finset.Icc 1 N, ∑ k ∈ Finset.Icc 1 N,
          ∑ b ∈ Finset.Icc 1 (N - 2), dipoleCoord h N a * dipoleCoord h N b *
            (cumulativeDipole a j * cumulativeDipole b k * vasyuninGCot j k) := by
    rw [Finset.sum_congr rfl fun j hj => Finset.sum_congr rfl fun k hk => hpt j hj k hk]
    rw [Finset.sum_congr rfl fun j _ => Finset.sum_comm, Finset.sum_comm]
  have hswap2 :
      (∑ a ∈ Finset.Icc 1 (N - 2), ∑ j ∈ Finset.Icc 1 N, ∑ k ∈ Finset.Icc 1 N,
        ∑ b ∈ Finset.Icc 1 (N - 2), dipoleCoord h N a * dipoleCoord h N b *
          (cumulativeDipole a j * cumulativeDipole b k * vasyuninGCot j k)) =
        ∑ a ∈ Finset.Icc 1 (N - 2), ∑ b ∈ Finset.Icc 1 (N - 2), ∑ j ∈ Finset.Icc 1 N,
          ∑ k ∈ Finset.Icc 1 N, dipoleCoord h N a * dipoleCoord h N b *
            (cumulativeDipole a j * cumulativeDipole b k * vasyuninGCot j k) := by
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_congr rfl fun j _ => Finset.sum_comm, Finset.sum_comm]
  rw [hswap1, hswap2]
  refine Finset.sum_congr rfl fun a ha => Finset.sum_congr rfl fun b hb => ?_
  have hfact :
      (∑ j ∈ Finset.Icc 1 N, ∑ k ∈ Finset.Icc 1 N,
        dipoleCoord h N a * dipoleCoord h N b *
          (cumulativeDipole a j * cumulativeDipole b k * vasyuninGCot j k)) =
        dipoleCoord h N a * dipoleCoord h N b *
          ∑ j ∈ Finset.Icc 1 N, ∑ k ∈ Finset.Icc 1 N,
            cumulativeDipole a j * cumulativeDipole b k * vasyuninGCot j k := by
    simp_rw [← Finset.mul_sum]
  rw [hfact, sum_cumulativeDipole_vasyuninGCot_eq_four_point (Finset.mem_Icc.mp ha).1
    (Finset.mem_Icc.mp hb).1 (by have := (Finset.mem_Icc.mp ha).2; omega)
    (by have := (Finset.mem_Icc.mp hb).2; omega)]
  rfl

private lemma dipoleCoord_sub_cBaseAnchor_red (c : ℕ → ℝ) {N m : ℕ} (hm : 1 ≤ m) :
    dipoleCoord (fun k => c k - cBaseAnchor k) N m = dipoleCoord c N m := by
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj3 : 3 ≤ j := by have := (Finset.mem_Icc.mp hj).1; omega
  have hanch : cBaseAnchor j = 0 := by rcases j with _ | _ | _ | j <;> [omega; omega; omega; rfl]
  dsimp only; rw [hanch, sub_zero]

/-- Master `N`-independent dipole quadratic reduction of `SCot vasyuninGCot c N` on `A_N`
for every `N ≥ 2`. -/
theorem SCot_eq_dipoleCoord_quadratic_of_mem_A_N {N : ℕ} (hN : 2 ≤ N) (c : ℕ → ℝ)
    (hc1 : D1 c N = 0) (hc0 : D0 c N = 2) :
    SCot vasyuninGCot c N =
      2 * Real.pi *
          (∑ m ∈ Finset.Icc 1 (N - 2),
            dipoleCoord c N m * (deltaCot (m + 2) - deltaCot (m + 1))) -
        ∑ a ∈ Finset.Icc 1 (N - 2), ∑ b ∈ Finset.Icc 1 (N - 2),
          dipoleCoord c N a * dipoleCoord c N b * dipoleGramEntry a b := by
  let h : ℕ → ℝ := fun k => c k - cBaseAnchor k
  have ht := sub_cBaseAnchor_mem_tangent hN c hc1 hc0
  have hc_eq : c = fun k => cBaseAnchor k + h k := funext fun k => by dsimp [h]; ring
  have hcot_add := SCot_cBaseAnchor_add_eq hN h
  have hlin_eq :
      (∑ k ∈ Finset.Icc 1 N, (h k / (k : ℝ)) * (vasyuninCotSum k 2 - vasyuninCotSum k 1)) =
        linearCotDrive h N := rfl
  have hS : SCot vasyuninGCot c N = -QCot vasyuninGCot h N + 2 * Real.pi * linearCotDrive h N := by
    conv_lhs => rw [hc_eq]
    rw [hcot_add, hlin_eq]
    unfold SCot
    rfl
  rw [hS, linearCotDrive_eq_sum_dipoleCoord hN h ht.1 ht.2,
    QCot_eq_sum_dipoleGramEntry hN h ht.1 ht.2]
  have hL :
      (∑ m ∈ Finset.Icc 1 (N - 2),
          dipoleCoord h N m * (deltaCot (m + 2) - deltaCot (m + 1))) =
        ∑ m ∈ Finset.Icc 1 (N - 2),
          dipoleCoord c N m * (deltaCot (m + 2) - deltaCot (m + 1)) := by
    refine Finset.sum_congr rfl fun m hm => ?_
    rw [dipoleCoord_sub_cBaseAnchor_red c (Finset.mem_Icc.mp hm).1]
  have hQ :
      (∑ a ∈ Finset.Icc 1 (N - 2), ∑ b ∈ Finset.Icc 1 (N - 2),
          dipoleCoord h N a * dipoleCoord h N b * dipoleGramEntry a b) =
        ∑ a ∈ Finset.Icc 1 (N - 2), ∑ b ∈ Finset.Icc 1 (N - 2),
          dipoleCoord c N a * dipoleCoord c N b * dipoleGramEntry a b := by
    refine Finset.sum_congr rfl fun a ha => Finset.sum_congr rfl fun b hb => ?_
    rw [dipoleCoord_sub_cBaseAnchor_red c (Finset.mem_Icc.mp ha).1,
      dipoleCoord_sub_cBaseAnchor_red c (Finset.mem_Icc.mp hb).1]
  rw [hL, hQ]
  ring

/-- Exact `N = 4` dipole coordinates of the global KKT optimizer `cGlobalOptFour`. -/
theorem dipoleCoord_cGlobalOptFour_eval :
    dipoleCoord cGlobalOptFour 4 1 = 2 / 3 ∧
      dipoleCoord cGlobalOptFour 4 2 = (5 - Real.sqrt 3) / 12 := by
  have h34 : Finset.Icc 3 4 = ({3, 4} : Finset ℕ) := by decide
  unfold dipoleCoord
  rw [h34, Finset.sum_insert (by decide), Finset.sum_singleton, Finset.Icc_self,
    Finset.sum_singleton]
  norm_num [cGlobalOptFour, cBaseAnchor, harmonicWavelet]
  ring

/-- Exact `N = 4` dipole coordinates of `cCandidateMobius 4`. -/
theorem dipoleCoord_cCandidateMobius_four_eval :
    dipoleCoord (cCandidateMobius 4) 4 1 = 133 / 208 ∧
      dipoleCoord (cCandidateMobius 4) 4 2 = 7 / 24 := by
  rcases cCandidateMobius_four_eval with ⟨_, _, hc3, hc4⟩
  have h34 : Finset.Icc 3 4 = ({3, 4} : Finset ℕ) := by decide
  unfold dipoleCoord
  rw [h34, Finset.sum_insert (by decide), Finset.sum_singleton, Finset.Icc_self,
    Finset.sum_singleton, hc3, hc4]
  constructor <;> norm_num

/-- Strict square-index `k = 4` overshoot certificate: the 2nd dipole coordinate of
`cGlobalOptFour` is strictly smaller than that of `cCandidateMobius 4`. -/
theorem dipoleCoord_cGlobalOptFour_two_lt_cCandidateMobius_four :
    dipoleCoord cGlobalOptFour 4 2 < dipoleCoord (cCandidateMobius 4) 4 2 := by
  rw [dipoleCoord_cGlobalOptFour_eval.2, dipoleCoord_cCandidateMobius_four_eval.2]
  have hsqrt : (3 / 2 : ℝ) < Real.sqrt 3 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3), Real.sqrt_nonneg 3]
  linarith
