/-
Copyright (c) 2026 Qamar Munawer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qamar Munawer
-/
module

public import RiemannBlueprint.UpstreamPRs.UpstreamPR_8I_LogarithmicPlaqueDecayCriterion

/-!
# Universal Superdiagonal Dipole Orthogonality and Homogeneous Kernel `unitDefectEntry`

This module establishes universal `N`-free cotangent shift/reflection laws, the all-`m`
superdiagonal orthogonality theorem `dipoleGramEntry m (m + 1) = 0`, exact `N = 6` block-trace
radical cancellation, and the unit-partition homogeneous kernel `unitDefectEntry` on the Dirichlet
simplex `IsDirichletAnchored` (`c₁ = -1`).
-/

@[expose] public section

open scoped BigOperators

/-- Universal shift periodicity of `vasyuninCotSum`: `V(a, a + r) = V(a, r)` for all `1 ≤ a`. -/
theorem vasyuninCotSum_add_self_right {a r : ℕ} (_ha : 1 ≤ a) :
    vasyuninCotSum a (a + r) = vasyuninCotSum a r := by
  rw [← vasyuninCotSum_mod_eq a (a + r), Nat.add_mod_left, vasyuninCotSum_mod_eq]

/-- Universal reflection for `vasyuninCotSum`: `V(a, a - r) = -V(a, r)` for `1 ≤ r ≤ a`. -/
theorem vasyuninCotSum_sub_self_right {a r : ℕ} (_ha : 1 ≤ a) (_hr : 1 ≤ r) (hra : r ≤ a) :
    vasyuninCotSum a (a - r) = -vasyuninCotSum a r :=
  vasyuninCotSum_sub_eq_neg hra

/-- **Universal Superdiagonal Dipole Orthogonality**: `∀ m ≥ 1, G̃(m, m+1) = G̃(m+1, m) = 0`. -/
theorem dipoleGramEntry_self_succ_eq_zero {m : ℕ} (hm : 1 ≤ m) :
    dipoleGramEntry m (m + 1) = 0 ∧ dipoleGramEntry (m + 1) m = 0 := by
  have h0 : dipoleGramEntry m (m + 1) = 0 := by
    have hm1 : ((m + 1 : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have hm2 : ((m + 2 : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have hm3 : ((m + 3 : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have hadd1 := vasyuninCotSum_add_self_right (a := m + 1) (r := 1) (by omega)
    have hadd2 := vasyuninCotSum_add_self_right (a := m + 1) (r := 2) (by omega)
    have hadd3 := vasyuninCotSum_add_self_right (a := m + 2) (r := 1) (by omega)
    have hsub1 :=
      vasyuninCotSum_sub_self_right (a := m + 2) (r := 1) (by omega) (by omega) (by omega)
    have hsub2 :=
      vasyuninCotSum_sub_self_right (a := m + 3) (r := 2) (by omega) (by omega) (by omega)
    have hsub3 :=
      vasyuninCotSum_sub_self_right (a := m + 3) (r := 1) (by omega) (by omega) (by omega)
    have hsimp1 : m + 1 + 1 = m + 2 := by omega
    have hsimp2 : m + 1 + 2 = m + 3 := by omega
    have hsimp3 : m + 2 - 1 = m + 1 := by omega
    have hsimp4 : m + 3 - 2 = m + 1 := by omega
    have hsimp5 : m + 3 - 1 = m + 2 := by omega
    rw [hsimp1] at hadd1; rw [hsimp2] at hadd2 hadd3
    rw [hsimp3] at hsub1; rw [hsimp4] at hsub2; rw [hsimp5] at hsub3
    unfold dipoleGramEntry unweightedKCot vasyuninGCot deltaCot
    rw [show m + 1 + 1 = m + 2 by omega, show m + 1 + 2 = m + 3 by omega,
      vasyuninCotSum_diag (m + 2), hadd1, hadd2, hadd3, hsub1, hsub2, hsub3]
    push_cast; field_simp [hm1, hm2, hm3]; ring
  exact ⟨h0, by rw [dipoleGramEntry_comm (m + 1) m, h0]⟩

/-- Superdiagonal plaque identity forced by `dipoleGramEntry_self_succ_eq_zero`. -/
theorem dipolePlaqueEntry_self_succ_eq {m : ℕ} (hm : 1 ≤ m) :
    dipolePlaqueEntry m (m + 1) = -(Real.pi / 2) * (deltaCot (m + 3) - deltaCot (m + 1)) := by
  have h := dipoleGramEntry_eq_boundary_add_plaque m (m + 1)
  rw [(dipoleGramEntry_self_succ_eq_zero hm).1, show m + 1 + 1 = m + 2 by omega,
    show m + 1 + 2 = m + 3 by omega] at h
  linarith

/-- Exact closed-form `N = 6` diagonal entry `dipoleGramEntry 4 4`. -/
theorem dipoleGramEntry_four_four_eq :
    dipoleGramEntry 4 4 = Real.pi * (4 / Real.sqrt 3 - Real.cos (Real.pi / 5) /
      Real.sin (Real.pi / 5) - Real.cos (2 * Real.pi / 5) / Real.sin (2 * Real.pi / 5)) := by
  have hsq3 : Real.sqrt 3 ≠ 0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  have hv56 : vasyuninCotSum 5 6 = vasyuninCotSum 5 1 :=
    vasyuninCotSum_add_self_right (a := 5) (r := 1) (by omega)
  rw [dipoleGramEntry_diag_eq 4]
  unfold unweightedKCot vasyuninGCot deltaCot
  simp only [Nat.reduceAdd, Nat.cast_ofNat]
  rw [hv56, vasyuninCotSum_five_one_eq, vasyuninCotSum_five_two_eq,
    vasyuninCotSum_six_eval.1, vasyuninCotSum_six_eval.2.1, vasyuninCotSum_six_eval.2.2.2.2]
  field_simp [hsq3]; ring

/-- Exact `N = 6` block trace cancelling all `ℚ(√5)` cotangents: `G̃₃₃ + G̃₄₄ = π(4/√3 - 1)`. -/
theorem dipoleGramEntry_three_three_add_four_four_eq :
    dipoleGramEntry 3 3 + dipoleGramEntry 4 4 = Real.pi * (4 / Real.sqrt 3 - 1) := by
  rw [dipoleGramEntry_three_three_eq, dipoleGramEntry_four_four_eq]; ring

private lemma insert_one_Icc_two (N : ℕ) (hN : 2 ≤ N) :
    Finset.Icc 1 N = insert 1 (Finset.Icc 2 N) := by
  ext k; simp only [Finset.mem_Icc, Finset.mem_insert]; omega

private lemma cumulativeDipole_at_one (m : ℕ) (hm : 1 ≤ m) : cumulativeDipole m 1 = 1 := by
  unfold cumulativeDipole; rw [Finset.sum_eq_single 1]
  · simp [harmonicWavelet]
  · intro r hr hne; rcases r with _ | _ | r <;> [exact absurd (Finset.mem_Icc.mp hr).1 (by decide);
      exact absurd rfl hne; simp [harmonicWavelet]]
  · intro h; exact absurd (Finset.mem_Icc.mpr ⟨le_rfl, hm⟩) h

/-- Unit-partition duality on `IsDirichletAnchored c N`: `∑_{k=2}^N c_k / k = 1 ∧ ∑ αₘ = 1`. -/
theorem isDirichletAnchored_unit_partition {N : ℕ} (hN : 2 ≤ N) {c : ℕ → ℝ}
    (hc : IsDirichletAnchored c N) :
    ∑ k ∈ Finset.Icc 2 N, c k / (k : ℝ) = 1 ∧
      ∑ m ∈ Finset.Icc 1 (N - 2), dipoleCoord c N m = 1 := by
  have hk : ∑ k ∈ Finset.Icc 2 N, c k / (k : ℝ) = 1 := by
    have hd1 := hc.1; unfold D1 at hd1
    rw [insert_one_Icc_two N hN, Finset.sum_insert (by simp), hc.2.2] at hd1
    norm_num at hd1; linarith
  have hm : ∑ m ∈ Finset.Icc 1 (N - 2), dipoleCoord c N m = 1 := by
    have h1 := eq_cBaseAnchor_add_sum_cumulativeDipole_of_mem_A_N hN c hc.1 hc.2.1
      (Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩)
    rw [Finset.sum_congr rfl fun m hm => by
      rw [cumulativeDipole_at_one m (Finset.mem_Icc.mp hm).1, mul_one], hc.2.2] at h1
    simp only [cBaseAnchor] at h1; linarith
  exact ⟨hk, hm⟩

/-- Symmetric `N`-independent unit-defect kernel absorbing `1` and `π * L_cot`. -/
noncomputable def unitDefectEntry (a b : ℕ) : ℝ :=
  1 - Real.pi * (deltaCot (a + 2) - deltaCot (a + 1) + deltaCot (b + 2) - deltaCot (b + 1)) +
    dipoleGramEntry a b

/-- Symmetry of `unitDefectEntry`. -/
theorem unitDefectEntry_comm (a b : ℕ) : unitDefectEntry a b = unitDefectEntry b a := by
  unfold unitDefectEntry; rw [dipoleGramEntry_comm a b]; ring

/-- Universal superdiagonal formula for `unitDefectEntry` forced by `G̃(m, m+1) = 0`. -/
theorem unitDefectEntry_self_succ_eq {m : ℕ} (hm : 1 ≤ m) :
    unitDefectEntry m (m + 1) = 1 - Real.pi * (deltaCot (m + 3) - deltaCot (m + 1)) := by
  unfold unitDefectEntry
  rw [(dipoleGramEntry_self_succ_eq_zero hm).1, show m + 1 + 1 = m + 2 by omega,
    show m + 1 + 2 = m + 3 by omega]; ring

private lemma deltaCot_two_four_eq : deltaCot 2 = 0 ∧ deltaCot 4 = 1 / 2 := by
  have hc1 : Real.cos (Real.pi / 4) / Real.sin (Real.pi / 4) = 1 := by
    rw [Real.cos_pi_div_four, Real.sin_pi_div_four]
    field_simp [(Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)).ne']
  have hv2 : ∀ b : ℕ, vasyuninCotSum 2 b = 0 := fun b => by
    unfold vasyuninCotSum; rw [show Finset.Ico 1 2 = ({1} : Finset ℕ) by ext x; simp,
      Finset.sum_singleton, show Real.pi * ((1 : ℕ) : ℝ) / ((2 : ℕ) : ℝ) = Real.pi / 2 by
      push_cast; ring, Real.cos_pi_div_two, zero_div, mul_zero]
  have hv4 : ∀ b : ℕ, vasyuninCotSum 4 b =
      Int.fract ((b : ℝ) / 4) - Int.fract (3 * (b : ℝ) / 4) := fun b => by
    unfold vasyuninCotSum
    rw [show Finset.Ico 1 4 = ({1, 2, 3} : Finset ℕ) by ext x; simp; omega,
      Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]; push_cast
    rw [show (1 : ℝ) * b / 4 = b / 4 by ring, show Real.pi * 1 / 4 = Real.pi / 4 by ring,
      show Real.pi * 2 / 4 = Real.pi / 2 by ring, Real.cos_pi_div_two, zero_div, mul_zero,
      show Real.pi * 3 / 4 = Real.pi - Real.pi / 4 by ring, Real.cos_pi_sub, Real.sin_pi_sub,
      neg_div, hc1]; ring
  exact ⟨by unfold deltaCot; rw [hv2, hv2, sub_self], by unfold deltaCot; rw [hv4, hv4]; norm_num⟩

/-- Exact `N = 4` unit-defect trace identity: `unitDefectEntry 1 1 + unitDefectEntry 2 2 = 2`. -/
theorem unitDefectEntry_one_one_add_two_two_eq :
    unitDefectEntry 1 1 + unitDefectEntry 2 2 = 2 := by
  have hsq3 : Real.sqrt 3 ≠ 0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  unfold unitDefectEntry; simp only [Nat.reduceAdd]
  rw [dipoleGramEntry_one_one_eq, dipoleGramEntry_two_two_eq, deltaCot_two_four_eq.1,
    deltaCot_two_four_eq.2]
  field_simp [hsq3]; ring

/-- Exact `N = 6` unit-defect trace identity: `M₃₃ + M₄₄ = 2 + 2π / (3√3)`. -/
theorem unitDefectEntry_three_three_add_four_four_eq :
    unitDefectEntry 3 3 + unitDefectEntry 4 4 = 2 + 2 * Real.pi / (3 * Real.sqrt 3) := by
  have hsq3 : Real.sqrt 3 ≠ 0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  unfold unitDefectEntry; simp only [Nat.reduceAdd]
  have htr : dipoleGramEntry 3 3 + dipoleGramEntry 4 4 = Real.pi * (4 / Real.sqrt 3 - 1) :=
    dipoleGramEntry_three_three_add_four_four_eq
  rw [deltaCot_two_four_eq.2, deltaCot_six_eq]
  rw [show 1 - Real.pi * (deltaCot 5 - 1 / 2 + deltaCot 5 - 1 / 2) + dipoleGramEntry 3 3 +
      (1 - Real.pi * (5 / (3 * Real.sqrt 3) - deltaCot 5 + 5 / (3 * Real.sqrt 3) - deltaCot 5) +
        dipoleGramEntry 4 4) =
      2 - 2 * Real.pi * (5 / (3 * Real.sqrt 3) - 1 / 2) +
        (dipoleGramEntry 3 3 + dipoleGramEntry 4 4) by ring, htr]
  field_simp [hsq3]; ring

/-- Negativity witness on the simplex: `unitDefectEntry 1 2 = 1 - π / 2 < 0`. -/
theorem unitDefectEntry_one_two_eq :
    unitDefectEntry 1 2 = 1 - Real.pi / 2 ∧ unitDefectEntry 1 2 < 0 := by
  have h : unitDefectEntry 1 2 = 1 - Real.pi / 2 := by
    unfold unitDefectEntry; rw [dipoleGramEntry_one_two_eq_zero]
    simp only [Nat.reduceAdd, add_zero]
    rw [show deltaCot 3 - deltaCot 2 + deltaCot 4 - deltaCot 3 = deltaCot 4 - deltaCot 2 by ring,
      deltaCot_two_four_eq.1, deltaCot_two_four_eq.2]; ring
  exact ⟨h, by linarith [Real.pi_gt_three]⟩

private lemma sum_unitDefect_aux (I : Finset ℕ) (α : ℕ → ℝ) (hS : ∑ m ∈ I, α m = 1) :
    ∑ a ∈ I, ∑ b ∈ I, α a * α b * (1 - (Real.pi / 2) *
      (deltaCot (a + 2) - deltaCot (a + 1) + deltaCot (b + 2) - deltaCot (b + 1))) =
      1 - Real.pi * ∑ m ∈ I, α m * (deltaCot (m + 2) - deltaCot (m + 1)) := by
  let Δ : ℕ → ℝ := fun m => deltaCot (m + 2) - deltaCot (m + 1)
  have hcon : ∀ a ∈ I, ∑ b ∈ I, α a * α b * (1 - Real.pi / 2 * (Δ a + Δ b)) =
      α a - Real.pi / 2 * (α a * Δ a) - (Real.pi / 2 * ∑ b ∈ I, α b * Δ b) * α a := fun a _ => by
    rw [Finset.sum_congr rfl fun b _ => show α a * α b * (1 - Real.pi / 2 * (Δ a + Δ b)) =
      α a * α b - Real.pi / 2 * (α a * Δ a) * α b - (Real.pi / 2 * α a) * (α b * Δ b) by ring]
    simp only [Finset.sum_sub_distrib, ← Finset.mul_sum, hS, mul_one]; ring
  rw [Finset.sum_congr rfl fun a ha => by simpa [Δ, add_sub_assoc] using hcon a ha]
  simp only [Finset.sum_sub_distrib, ← Finset.mul_sum, hS, mul_one]; ring

/-- **Master Homogeneous Unit-Defect Reduction**: for `IsDirichletAnchored c N`,
`1 - SCot vasyuninGCot c N = ∑ a, ∑ b, αₐ α_b unitDefectEntry a b`. -/
theorem one_sub_SCot_eq_sum_unitDefectEntry_of_isDirichletAnchored {N : ℕ} (hN : 2 ≤ N)
    {c : ℕ → ℝ} (hc : IsDirichletAnchored c N) : 1 - SCot vasyuninGCot c N =
      ∑ a ∈ Finset.Icc 1 (N - 2), ∑ b ∈ Finset.Icc 1 (N - 2),
        dipoleCoord c N a * dipoleCoord c N b * unitDefectEntry a b := by
  have ht := hc.sub_mem_tangent hN; have hS := (isDirichletAnchored_unit_partition hN hc).2
  have hLr : (∑ m ∈ Finset.Icc 1 (N - 2), dipoleCoord (fun k => c k - cBaseAnchor k) N m *
      (deltaCot (m + 2) - deltaCot (m + 1))) = ∑ m ∈ Finset.Icc 1 (N - 2),
      dipoleCoord c N m * (deltaCot (m + 2) - deltaCot (m + 1)) := Finset.sum_congr rfl
    fun m hm => by rw [dipoleCoord_sub_cBaseAnchor_eq (Finset.mem_Icc.mp hm).1]
  rw [SCot_eq_drive_sub_dipolePlaqueForm_of_dirichlet hN hc,
    linearCotDrive_eq_sum_dipoleCoord hN _ ht.1 ht.2.1, hLr]
  have hU : ∑ a ∈ Finset.Icc 1 (N - 2), ∑ b ∈ Finset.Icc 1 (N - 2),
      dipoleCoord c N a * dipoleCoord c N b * unitDefectEntry a b =
      (∑ a ∈ Finset.Icc 1 (N - 2), ∑ b ∈ Finset.Icc 1 (N - 2), dipoleCoord c N a * dipoleCoord c N b
        * (1 - (Real.pi / 2) * (deltaCot (a + 2) - deltaCot (a + 1) +
          deltaCot (b + 2) - deltaCot (b + 1)))) +
      dipolePlaqueForm (fun k => c k - cBaseAnchor k) N := by
    rw [dipolePlaqueForm_sub_cBaseAnchor_eq c N]; unfold dipolePlaqueForm
    simp_rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by
      unfold unitDefectEntry; rw [dipoleGramEntry_eq_boundary_add_plaque a b]; ring
  rw [hU, sum_unitDefect_aux _ _ hS]; ring

/-- Non-negativity of the homogeneous unit-defect form on `IsDirichletAnchored c N`. -/
theorem sum_unitDefectEntry_nonneg_of_isDirichletAnchored {N : ℕ} (hN : 2 ≤ N) {c : ℕ → ℝ}
    (hc : IsDirichletAnchored c N) : 0 ≤ ∑ a ∈ Finset.Icc 1 (N - 2),
      ∑ b ∈ Finset.Icc 1 (N - 2), dipoleCoord c N a * dipoleCoord c N b * unitDefectEntry a b := by
  rw [← one_sub_SCot_eq_sum_unitDefectEntry_of_isDirichletAnchored hN hc,
    ← affine_l2_dist_eq_one_sub_scot c hc.1 hc.2.1]
  exact intervalIntegral.integral_nonneg (by norm_num) fun _ _ => sq_nonneg _
