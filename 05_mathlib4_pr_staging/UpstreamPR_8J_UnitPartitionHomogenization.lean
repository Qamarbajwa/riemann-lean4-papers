/-
Copyright (c) 2026 Qamar Munawer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qamar Munawer
-/
module

public import RiemannBlueprint.UpstreamPRs.UpstreamPR_8I_LogarithmicPlaqueDecayCriterion

/-!
# Unit-Partition Duality and Homogeneous Unit-Defect Kernel on the Dirichlet Simplex

On `IsDirichletAnchored` (`c₁ = -1`), pole weight `1` partitions across `k ≥ 2` and simplex
coordinates `∑ αₘ = 1`, absorbing `1` and `π * L_cot` into the `N`-independent kernel
`unitDefectEntry`, giving `one_sub_SCot_eq_sum_unitDefectEntry_of_isDirichletAnchored`,
`unitDefectEntry_one_two_eq`, `sum_unitDefectEntry_nonneg_of_isDirichletAnchored`, and
`riemannHypothesis_of_unitDefectEntry_simplex_vanishing`.
-/
@[expose] public section
open scoped BigOperators
private lemma insert_one_Icc_two (N : ℕ) (hN : 2 ≤ N) :
    Finset.Icc 1 N = insert 1 (Finset.Icc 2 N) := by
  ext k; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
/-- Partition of the `k = 1` unit pole weight across `k ≥ 2`. -/
theorem sum_Icc_two_div_eq_one_of_isDirichletAnchored {N : ℕ} (hN : 2 ≤ N) {c : ℕ → ℝ}
    (hc : IsDirichletAnchored c N) : ∑ k ∈ Finset.Icc 2 N, c k / (k : ℝ) = 1 := by
  have hd1 := hc.1; unfold D1 at hd1
  rw [insert_one_Icc_two N hN, Finset.sum_insert (by simp), hc.2.2] at hd1
  norm_num at hd1; linarith
/-- Partition of total weight across `k ≥ 2` on `IsDirichletAnchored c N`. -/
theorem sum_Icc_two_eq_three_of_isDirichletAnchored {N : ℕ} (hN : 2 ≤ N) {c : ℕ → ℝ}
    (hc : IsDirichletAnchored c N) : ∑ k ∈ Finset.Icc 2 N, c k = 3 := by
  have hd0 := hc.2.1; unfold D0 at hd0
  rw [insert_one_Icc_two N hN, Finset.sum_insert (by simp), hc.2.2] at hd0; linarith
private lemma cumulativeDipole_at_one (m : ℕ) (hm : 1 ≤ m) : cumulativeDipole m 1 = 1 := by
  unfold cumulativeDipole; rw [Finset.sum_eq_single 1]
  · simp [harmonicWavelet]
  · intro r hr hne; rcases r with _ | _ | r <;> [exact absurd (Finset.mem_Icc.mp hr).1 (by decide);
      exact absurd rfl hne; simp [harmonicWavelet]]
  · intro h; exact absurd (Finset.mem_Icc.mpr ⟨le_rfl, hm⟩) h
/-- Exact simplex duality: `∑ m ∈ Icc 1 (N - 2), dipoleCoord c N m = 1`. -/
theorem sum_dipoleCoord_eq_one_of_isDirichletAnchored {N : ℕ} (hN : 2 ≤ N) {c : ℕ → ℝ}
    (hc : IsDirichletAnchored c N) : ∑ m ∈ Finset.Icc 1 (N - 2), dipoleCoord c N m = 1 := by
  have h1 := eq_cBaseAnchor_add_sum_cumulativeDipole_of_mem_A_N hN c hc.1 hc.2.1
    (Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩)
  rw [Finset.sum_congr rfl fun m hm => by
    rw [cumulativeDipole_at_one m (Finset.mem_Icc.mp hm).1, mul_one], hc.2.2] at h1
  simp only [cBaseAnchor] at h1; linarith
/-- Symmetric `N`-independent unit-defect kernel absorbing `1` and `π * L_cot`. -/
noncomputable def unitDefectEntry (a b : ℕ) : ℝ :=
  1 - (Real.pi / 2) *
    (deltaCot (a + 2) - deltaCot (a + 1) + deltaCot (b + 2) - deltaCot (b + 1)) +
    dipolePlaqueEntry a b
/-- Symmetry: `unitDefectEntry a b = unitDefectEntry b a`. -/
theorem unitDefectEntry_comm (a b : ℕ) : unitDefectEntry a b = unitDefectEntry b a := by
  unfold unitDefectEntry; rw [dipolePlaqueEntry_comm a b]; ring
/-- Relation to `dipoleGramEntry`: `1 - π * (Δδₐ + Δδ_b) + dipoleGramEntry a b`. -/
theorem unitDefectEntry_eq_one_sub_drive_add_gram (a b : ℕ) :
    unitDefectEntry a b = 1 - Real.pi *
      (deltaCot (a + 2) - deltaCot (a + 1) + deltaCot (b + 2) - deltaCot (b + 1)) +
      dipoleGramEntry a b := by
  unfold unitDefectEntry; rw [dipoleGramEntry_eq_boundary_add_plaque a b]; ring

/-- Off-diagonal negativity witness on the simplex: `unitDefectEntry 1 2 = 1 - π / 2 < 0`. -/
theorem unitDefectEntry_one_two_eq :
    unitDefectEntry 1 2 = 1 - Real.pi / 2 ∧ unitDefectEntry 1 2 < 0 := by
  have hc1 : Real.cos (Real.pi / 4) / Real.sin (Real.pi / 4) = 1 := by
    rw [Real.cos_pi_div_four, Real.sin_pi_div_four]
    field_simp [(Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)).ne']
  have hv4 : ∀ b : ℕ, vasyuninCotSum 4 b =
      Int.fract ((b : ℝ) / 4) - Int.fract (3 * (b : ℝ) / 4) := fun b => by
    unfold vasyuninCotSum
    rw [show Finset.Ico 1 4 = ({1, 2, 3} : Finset ℕ) by ext x; simp; omega,
      Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]; push_cast
    rw [show (1 : ℝ) * b / 4 = b / 4 by ring, show Real.pi * 1 / 4 = Real.pi / 4 by ring,
      show Real.pi * 2 / 4 = Real.pi / 2 by ring, Real.cos_pi_div_two, zero_div, mul_zero,
      show Real.pi * 3 / 4 = Real.pi - Real.pi / 4 by ring, Real.cos_pi_sub, Real.sin_pi_sub,
      neg_div, hc1]; ring
  have hd2 : deltaCot 2 = 0 := by
    have hv2 : ∀ b : ℕ, vasyuninCotSum 2 b = 0 := fun b => by
      unfold vasyuninCotSum; rw [show Finset.Ico 1 2 = ({1} : Finset ℕ) by ext x; simp,
        Finset.sum_singleton, show Real.pi * ((1 : ℕ) : ℝ) / ((2 : ℕ) : ℝ) = Real.pi / 2 by
        push_cast; ring, Real.cos_pi_div_two, zero_div, mul_zero]
    unfold deltaCot; rw [hv2, hv2, sub_self]
  have hd4 : deltaCot 4 = 1 / 2 := by unfold deltaCot; rw [hv4, hv4]; norm_num
  have h12 : unitDefectEntry 1 2 = 1 - Real.pi / 2 := by
    rw [unitDefectEntry_eq_one_sub_drive_add_gram 1 2, dipoleGramEntry_one_two_eq_zero]
    simp only [Nat.reduceAdd, add_zero]
    rw [show deltaCot 3 - deltaCot 2 + deltaCot 4 - deltaCot 3 = deltaCot 4 - deltaCot 2 by ring,
      hd4, hd2]; ring
  exact ⟨h12, by linarith [Real.pi_gt_three]⟩
private lemma sum_unitDefect_aux (I : Finset ℕ) (α : ℕ → ℝ) (hS : ∑ m ∈ I, α m = 1) :
    ∑ a ∈ I, ∑ b ∈ I, α a * α b * (1 - (Real.pi / 2) *
      (deltaCot (a + 2) - deltaCot (a + 1) + deltaCot (b + 2) - deltaCot (b + 1))) =
      1 - Real.pi * ∑ m ∈ I, α m * (deltaCot (m + 2) - deltaCot (m + 1)) := by
  let Δ : ℕ → ℝ := fun m => deltaCot (m + 2) - deltaCot (m + 1)
  have hcon : ∀ a ∈ I, ∑ b ∈ I, α a * α b * (1 - Real.pi / 2 * (Δ a + Δ b)) =
      α a - Real.pi / 2 * (α a * Δ a) - (Real.pi / 2 * ∑ b ∈ I, α b * Δ b) * α a := by
    intro a _; simp_rw [show ∀ b, α a * α b * (1 - Real.pi / 2 * (Δ a + Δ b)) =
      α a * α b - Real.pi / 2 * (α a * Δ a) * α b - (Real.pi / 2 * α a) * (α b * Δ b)
      by intro b; ring, Finset.sum_sub_distrib, ← Finset.mul_sum, hS, mul_one]; ring
  rw [Finset.sum_congr rfl fun a ha => by simpa [Δ, add_sub_assoc] using hcon a ha]
  simp only [Finset.sum_sub_distrib, ← Finset.mul_sum, hS, mul_one]; ring
/-- **Homogeneous Unit-Defect Quadratic Reduction** on `IsDirichletAnchored c N`. -/
theorem one_sub_SCot_eq_sum_unitDefectEntry_of_isDirichletAnchored {N : ℕ} (hN : 2 ≤ N)
    {c : ℕ → ℝ} (hc : IsDirichletAnchored c N) : 1 - SCot vasyuninGCot c N =
      ∑ a ∈ Finset.Icc 1 (N - 2), ∑ b ∈ Finset.Icc 1 (N - 2),
        dipoleCoord c N a * dipoleCoord c N b * unitDefectEntry a b := by
  have ht := hc.sub_mem_tangent hN; have hS := sum_dipoleCoord_eq_one_of_isDirichletAnchored hN hc
  have hLr : (∑ m ∈ Finset.Icc 1 (N - 2), dipoleCoord (fun k => c k - cBaseAnchor k) N m *
      (deltaCot (m + 2) - deltaCot (m + 1))) = ∑ m ∈ Finset.Icc 1 (N - 2),
      dipoleCoord c N m * (deltaCot (m + 2) - deltaCot (m + 1)) := Finset.sum_congr rfl
    fun m hm => by rw [dipoleCoord_sub_cBaseAnchor_eq (Finset.mem_Icc.mp hm).1]
  rw [SCot_eq_drive_sub_dipolePlaqueForm_of_dirichlet hN hc,
    linearCotDrive_eq_sum_dipoleCoord hN _ ht.1 ht.2.1, hLr]
  have hU : ∑ a ∈ Finset.Icc 1 (N - 2), ∑ b ∈ Finset.Icc 1 (N - 2),
      dipoleCoord c N a * dipoleCoord c N b * unitDefectEntry a b =
      (∑ a ∈ Finset.Icc 1 (N - 2), ∑ b ∈ Finset.Icc 1 (N - 2),
        dipoleCoord c N a * dipoleCoord c N b * (1 - (Real.pi / 2) * (deltaCot (a + 2) -
          deltaCot (a + 1) + deltaCot (b + 2) - deltaCot (b + 1)))) +
      dipolePlaqueForm (fun k => c k - cBaseAnchor k) N := by
    rw [dipolePlaqueForm_sub_cBaseAnchor_eq c N]; unfold dipolePlaqueForm
    simp_rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by
      unfold unitDefectEntry; ring
  rw [hU, sum_unitDefect_aux _ _ hS]; ring
/-- Non-negativity of the homogeneous unit-defect form on `IsDirichletAnchored c N`. -/
theorem sum_unitDefectEntry_nonneg_of_isDirichletAnchored {N : ℕ} (hN : 2 ≤ N) {c : ℕ → ℝ}
    (hc : IsDirichletAnchored c N) :
    0 ≤ ∑ a ∈ Finset.Icc 1 (N - 2), ∑ b ∈ Finset.Icc 1 (N - 2),
      dipoleCoord c N a * dipoleCoord c N b * unitDefectEntry a b := by
  rw [← one_sub_SCot_eq_sum_unitDefectEntry_of_isDirichletAnchored hN hc,
    ← affine_l2_dist_eq_one_sub_scot c hc.1 hc.2.1]
  exact intervalIntegral.integral_nonneg (by norm_num) fun _ _ => sq_nonneg _
/-- **Homogeneous Unit-Defect Simplex Criterion for RH** under `TitchmarshMellinProperty`. -/
theorem riemannHypothesis_of_unitDefectEntry_simplex_vanishing (hT : TitchmarshMellinProperty)
    (h_vanish : ∀ ε : ℝ, 0 < ε → ∃ (N : ℕ) (α : ℕ → ℝ),
      2 ≤ N ∧ ∑ m ∈ Finset.Icc 1 (N - 2), α m = 1 ∧
      ∑ a ∈ Finset.Icc 1 (N - 2), ∑ b ∈ Finset.Icc 1 (N - 2),
        α a * α b * unitDefectEntry a b < ε) : _root_.RiemannHypothesis := by
  intro s₀ hz hnt h1; by_contra hne
  have hs_lt : s₀.re < 1 := by_contra fun g => riemannZeta_ne_zero_of_one_le_re (not_lt.mp g) hz
  obtain ⟨w, hwlo, hwhi, hwz⟩ :
      ∃ w : ℂ, 1 / 2 < w.re ∧ w.re < 1 ∧ riemannZeta w = 0 := by
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have hr := riemannZeta_zero_reflection_of_re_lt_half hz hnt h1 hlt
      exact ⟨1 - s₀, hr.2,
        by_contra fun g => riemannZeta_ne_zero_of_one_le_re (not_lt.mp g) hr.1, hr.1⟩
    · exact ⟨s₀, hgt, hs_lt, hz⟩
  have hδ : 0 < (2 * w.re - 1) / ‖w‖ ^ 2 := div_pos (by linarith)
    (sq_pos_of_pos (norm_pos_iff.mpr fun h => by rw [h] at hwlo; norm_num at hwlo))
  obtain ⟨N, α, hN, hα, hlt⟩ := h_vanish _ hδ
  let c : ℕ → ℝ := fun k =>
    cBaseAnchor k + ∑ m ∈ Finset.Icc 1 (N - 2), α m * cumulativeDipole m k
  have hbase := cBaseAnchor_mem_A_N hN
  have hs_m : ∀ m ∈ Finset.Icc 1 (N - 2), 1 ≤ m ∧ m + 2 ≤ N := fun m hm =>
    ⟨(Finset.mem_Icc.mp hm).1, by have := (Finset.mem_Icc.mp hm).2; omega⟩
  have hcD1 : D1 c N = 0 := by
    unfold D1 at hbase ⊢; simp_rw [c, add_div, Finset.sum_add_distrib, hbase.1, zero_add,
      Finset.sum_div]; rw [Finset.sum_comm]; refine Finset.sum_eq_zero fun m hm => ?_
    have hd := (cumulativeDipole_mem_tangent (hs_m m hm).1 (hs_m m hm).2).1; unfold D1 at hd
    simp_rw [mul_div_assoc, ← Finset.mul_sum, hd, mul_zero]
  have hcD0 : D0 c N = 2 := by
    unfold D0 at hbase ⊢; simp_rw [c, Finset.sum_add_distrib, hbase.2]; rw [add_eq_left,
      Finset.sum_comm]; refine Finset.sum_eq_zero fun m hm => ?_
    have hd := (cumulativeDipole_mem_tangent (hs_m m hm).1 (hs_m m hm).2).2; unfold D0 at hd
    rw [← Finset.mul_sum, hd, mul_zero]
  have hc1 : c 1 = -1 := by
    have h1 : ∑ m ∈ Finset.Icc 1 (N - 2), α m * cumulativeDipole m 1 = 1 := by
      rw [Finset.sum_congr rfl fun m hm => by
        rw [cumulativeDipole_at_one m (Finset.mem_Icc.mp hm).1, mul_one], hα]
    dsimp [c, cBaseAnchor]; rw [h1]; norm_num
  have hcoord : ∀ a ∈ Finset.Icc 1 (N - 2), dipoleCoord c N a = α a := fun a ha => by
    rw [← dipoleCoord_sub_cBaseAnchor_eq (Finset.mem_Icc.mp ha).1 (N := N) (c := c), show
      (fun k => c k - cBaseAnchor k) = fun k => ∑ m ∈ Finset.Icc 1 (N - 2),
        α m * cumulativeDipole m k by ext k; dsimp [c]; ring]
    unfold dipoleCoord; simp_rw [Finset.sum_div]; rw [Finset.sum_comm]
    have ht : ∀ m ∈ Finset.Icc 1 (N - 2), ∑ j ∈ Finset.Icc (a + 2) N,
        α m * cumulativeDipole m j / (j : ℝ) = if m = a then α a else 0 := fun m hm => by
      let F : ℕ → ℝ := fun k => if a + 2 ≤ k then 1 else 0
      have hs := cumulativeDipole_div_sum_eq_four_point F (hs_m m hm).1 (hs_m m hm).2
      rw [Finset.sum_congr rfl fun k _ => show cumulativeDipole m k * (F k / (k : ℝ)) =
        if a + 2 ≤ k then cumulativeDipole m k / (k : ℝ) else 0 from by
          dsimp [F]; split_ifs <;> ring] at hs
      simp_rw [mul_div_assoc, ← Finset.mul_sum]
      rw [show Finset.Icc (a + 2) N = (Finset.Icc 1 N).filter (fun k => a + 2 ≤ k) by
        ext k; simp only [Finset.mem_Icc, Finset.mem_filter]; omega, Finset.sum_filter, hs]
      have ha1 := (Finset.mem_Icc.mp ha).1
      by_cases hma : m = a <;> (dsimp [F]; split_ifs <;> norm_num <;> try omega)
      subst hma; simp
    rw [Finset.sum_congr rfl ht, Finset.sum_ite_eq']; simp [ha]
  have hfloor := mellin_l2_floor_of_zeta_zero hT c N hcD1 hwlo hwhi hwz
  rw [affine_l2_dist_eq_one_sub_scot c hcD1 hcD0,
    one_sub_SCot_eq_sum_unitDefectEntry_of_isDirichletAnchored hN ⟨hcD1, hcD0, hc1⟩] at hfloor
  rw [Finset.sum_congr rfl fun a ha => Finset.sum_congr rfl fun b hb => by
    rw [hcoord a ha, hcoord b hb]] at hfloor
  linarith
