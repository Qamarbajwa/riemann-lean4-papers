/-
Copyright (c) 2026 Qamar Munawer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qamar Munawer
-/
module

public import RiemannBlueprint.UpstreamPRs.UpstreamPR_8B_DirichletAnchoredPlaque

/-!
# Two-Dimensional Abel Telescoping Identity for the Pure Cotangent Plaque

This module proves the exact 2D discrete Abel telescoping reduction of `dipolePlaqueForm` into
the boundary-subtracted Vasyunin kernel on `{3, …, N} × {3, …, N}`:

* `sum_Icc_dipolePlaqueEntry_eq`: for `j, k ≥ 3`,
  `∑ a ∈ Icc 1 (j - 2), ∑ b ∈ Icc 1 (k - 2), dipolePlaqueEntry a b =`
  `unweightedKCot j k - unweightedKCot j 2 - unweightedKCot 2 k`.
* `dipolePlaqueForm_eq_telescoped_kernel`: for any `h : ℕ → ℝ` and `N : ℕ`,
  `dipolePlaqueForm h N = ∑ j ∈ Icc 3 N, ∑ k ∈ Icc 3 N, (h j / j) * (h k / k) *`
  `(unweightedKCot j k - unweightedKCot j 2 - unweightedKCot 2 k)`.
* `dipolePlaqueForm_sub_cBaseAnchor_eq_telescoped_kernel`: on `c - cBaseAnchor`, indices
  `j, k ≥ 3` recover `c j * c k / (j * k)`.
* `SCot_eq_drive_sub_telescoped_kernel_of_dirichlet`: closed-form `SCot` on `c₁ = -1`.
-/

@[expose] public section

open scoped BigOperators
open Finset

private lemma vasyuninCotSum_two_tel (b : ℕ) : vasyuninCotSum 2 b = 0 := by
  unfold vasyuninCotSum
  rw [show Finset.Ico 1 2 = ({1} : Finset ℕ) by ext x; simp, Finset.sum_singleton,
    show Real.pi * ((1 : ℕ) : ℝ) / ((2 : ℕ) : ℝ) = Real.pi / 2 by push_cast; ring,
    Real.cos_pi_div_two, zero_div, mul_zero]

/-- Exact vanishing `unweightedKCot 2 2 = 0` at the diagonal boundary node `(2, 2)`. -/
theorem unweightedKCot_two_two_eq_zero : unweightedKCot 2 2 = 0 := by
  unfold unweightedKCot vasyuninGCot
  rw [vasyuninCotSum_two_tel, add_zero, mul_zero, mul_zero]

private lemma sum_Icc_one_sub_succ (f : ℕ → ℝ) :
    ∀ n : ℕ, (∑ i ∈ Finset.Icc 1 n, (f (i + 1) - f (i + 2))) = f 2 - f (n + 2)
  | 0 => by simp
  | n + 1 => by
      have hsub : Finset.Icc 1 (n + 1) = insert (n + 1) (Finset.Icc 1 n) := by
        ext x; simp [Finset.mem_Icc]; omega
      have hnot : n + 1 ∉ Finset.Icc 1 n := by simp
      rw [hsub, Finset.sum_insert hnot, sum_Icc_one_sub_succ f n]
      ring

private lemma sum_Icc_dipolePlaqueEntry_inner (a k : ℕ) (hk : 3 ≤ k) :
    (∑ b ∈ Finset.Icc 1 (k - 2), dipolePlaqueEntry a b) =
      (unweightedKCot (a + 1) 2 - unweightedKCot (a + 1) k) -
        (unweightedKCot (a + 2) 2 - unweightedKCot (a + 2) k) := by
  let fa : ℕ → ℝ := fun b => unweightedKCot (a + 1) b - unweightedKCot (a + 2) b
  have hpt : ∀ b ∈ Finset.Icc 1 (k - 2), dipolePlaqueEntry a b = fa (b + 1) - fa (b + 2) :=
    fun b _ => by dsimp [fa, dipolePlaqueEntry]; ring
  rw [Finset.sum_congr rfl hpt, sum_Icc_one_sub_succ fa (k - 2),
    show k - 2 + 2 = k by omega]
  dsimp [fa]
  ring

/-- **2D Discrete Kernel Telescoping Identity**: for all `j, k ≥ 3`, the cumulative rectangle sum
of `dipolePlaqueEntry a b` over `[1, j - 2] × [1, k - 2]` telescopes to
`unweightedKCot j k - unweightedKCot j 2 - unweightedKCot 2 k`. -/
theorem sum_Icc_dipolePlaqueEntry_eq {j k : ℕ} (hj : 3 ≤ j) (hk : 3 ≤ k) :
    (∑ a ∈ Finset.Icc 1 (j - 2), ∑ b ∈ Finset.Icc 1 (k - 2), dipolePlaqueEntry a b) =
      unweightedKCot j k - unweightedKCot j 2 - unweightedKCot 2 k := by
  let g : ℕ → ℝ := fun a => unweightedKCot a 2 - unweightedKCot a k
  have hpt : ∀ a ∈ Finset.Icc 1 (j - 2),
      (∑ b ∈ Finset.Icc 1 (k - 2), dipolePlaqueEntry a b) = g (a + 1) - g (a + 2) :=
    fun a _ => sum_Icc_dipolePlaqueEntry_inner a k hk
  rw [Finset.sum_congr rfl hpt, sum_Icc_one_sub_succ g (j - 2),
    show j - 2 + 2 = j by omega]
  dsimp [g]
  rw [unweightedKCot_two_two_eq_zero]
  ring

private lemma sum_Icc_dipoleCoord_mul (h : ℕ → ℝ) (N : ℕ) (w : ℕ → ℝ) :
    (∑ a ∈ Finset.Icc 1 (N - 2), dipoleCoord h N a * w a) =
      ∑ j ∈ Finset.Icc 3 N, (h j / (j : ℝ)) * ∑ a ∈ Finset.Icc 1 (j - 2), w a := by
  have hstep1 :
      (∑ a ∈ Finset.Icc 1 (N - 2), dipoleCoord h N a * w a) =
        ∑ a ∈ Finset.Icc 1 (N - 2), ∑ j ∈ Finset.Icc 3 N,
          if a + 2 ≤ j then (h j / (j : ℝ)) * w a else 0 := by
    refine Finset.sum_congr rfl fun a ha => ?_
    have ha_mem := Finset.mem_Icc.mp ha
    unfold dipoleCoord
    rw [Finset.sum_mul, ← Finset.sum_filter]
    have hflt : Finset.filter (fun j => a + 2 ≤ j) (Finset.Icc 3 N) = Finset.Icc (a + 2) N := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_Icc]
      omega
    rw [hflt]
  rw [hstep1, Finset.sum_comm]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj_mem := Finset.mem_Icc.mp hj
  rw [← Finset.sum_filter]
  have hflt : Finset.filter (fun a => a + 2 ≤ j) (Finset.Icc 1 (N - 2)) = Finset.Icc 1 (j - 2) := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_Icc]
    omega
  rw [hflt, Finset.mul_sum]

/-- **2D Abel Telescoping Identity for `dipolePlaqueForm`**: on any sequence `h : ℕ → ℝ`, the
plaque double sum over `[1, N - 2]²` equals the `h_j h_k / (jk)`-weighted boundary-subtracted
kernel sum over `[3, N]²`. -/
theorem dipolePlaqueForm_eq_telescoped_kernel (h : ℕ → ℝ) (N : ℕ) :
    dipolePlaqueForm h N =
      ∑ j ∈ Finset.Icc 3 N, ∑ k ∈ Finset.Icc 3 N,
        (h j / (j : ℝ)) * (h k / (k : ℝ)) *
          (unweightedKCot j k - unweightedKCot j 2 - unweightedKCot 2 k) := by
  unfold dipolePlaqueForm
  have ha_swap :
      (∑ a ∈ Finset.Icc 1 (N - 2), ∑ b ∈ Finset.Icc 1 (N - 2),
        dipoleCoord h N a * dipoleCoord h N b * dipolePlaqueEntry a b) =
        ∑ a ∈ Finset.Icc 1 (N - 2), dipoleCoord h N a *
          (∑ b ∈ Finset.Icc 1 (N - 2), dipoleCoord h N b * dipolePlaqueEntry a b) := by
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => by ring
  rw [ha_swap, sum_Icc_dipoleCoord_mul h N]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj3 : 3 ≤ j := (Finset.mem_Icc.mp hj).1
  rw [Finset.sum_comm]
  have hb_inner :
      (∑ b ∈ Finset.Icc 1 (N - 2), ∑ a ∈ Finset.Icc 1 (j - 2),
        dipoleCoord h N b * dipolePlaqueEntry a b) =
        ∑ b ∈ Finset.Icc 1 (N - 2), dipoleCoord h N b *
          (∑ a ∈ Finset.Icc 1 (j - 2), dipolePlaqueEntry a b) :=
    Finset.sum_congr rfl fun b _ => (Finset.mul_sum _ _ _).symm
  rw [hb_inner, sum_Icc_dipoleCoord_mul h N, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk3 : 3 ≤ k := (Finset.mem_Icc.mp hk).1
  rw [Finset.sum_comm, sum_Icc_dipolePlaqueEntry_eq hj3 hk3]
  ring

/-- On `h = c - cBaseAnchor`, indices `j, k ≥ 3` have `cBaseAnchor j = 0`, simplifying
`dipolePlaqueForm (c - cBaseAnchor) N` directly to the `c_j c_k / (jk)` kernel bilinear form. -/
theorem dipolePlaqueForm_sub_cBaseAnchor_eq_telescoped_kernel (c : ℕ → ℝ) (N : ℕ) :
    dipolePlaqueForm (fun k => c k - cBaseAnchor k) N =
      ∑ j ∈ Finset.Icc 3 N, ∑ k ∈ Finset.Icc 3 N,
        (c j * c k / ((j : ℝ) * (k : ℝ))) *
          (unweightedKCot j k - unweightedKCot j 2 - unweightedKCot 2 k) := by
  rw [dipolePlaqueForm_eq_telescoped_kernel]
  refine Finset.sum_congr rfl fun j hj => Finset.sum_congr rfl fun k hk => ?_
  have hj3 : 3 ≤ j := (Finset.mem_Icc.mp hj).1
  have hk3 : 3 ≤ k := (Finset.mem_Icc.mp hk).1
  have hcbj : cBaseAnchor j = 0 := by
    rcases j with _ | _ | _ | j <;> simp [cBaseAnchor] <;> omega
  have hcbk : cBaseAnchor k = 0 := by
    rcases k with _ | _ | _ | k <;> simp [cBaseAnchor] <;> omega
  rw [hcbj, hcbk, sub_zero, sub_zero]
  ring

/-- Closed-form Dirichlet-anchored (`c 1 = -1`) `SCot` formula expressed via the 2D telescoped
plaque kernel on `{3, …, N}²`. -/
theorem SCot_eq_drive_sub_telescoped_kernel_of_dirichlet {N : ℕ} (hN : 2 ≤ N) {c : ℕ → ℝ}
    (hc : IsDirichletAnchored c N) :
    SCot vasyuninGCot c N =
      Real.pi * linearCotDrive (fun k => c k - cBaseAnchor k) N -
        ∑ j ∈ Finset.Icc 3 N, ∑ k ∈ Finset.Icc 3 N,
          (c j * c k / ((j : ℝ) * (k : ℝ))) *
            (unweightedKCot j k - unweightedKCot j 2 - unweightedKCot 2 k) := by
  rw [SCot_eq_drive_sub_dipolePlaqueForm_of_dirichlet hN hc,
    dipolePlaqueForm_sub_cBaseAnchor_eq_telescoped_kernel]
