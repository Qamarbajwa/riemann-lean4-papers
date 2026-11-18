/-
Copyright (c) 2026 Qamar Munawer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qamar Munawer
-/
module

public import RiemannBlueprint.UpstreamPRs.UpstreamPR_8I_LogarithmicPlaqueDecayCriterion

/-!
# Superdiagonal Zeros `G̃(m, m+1) = 0`, Orthogonal Triple `{v₂, v₃, v₄}`, and `unitDefectEntry`

This module proves universal all-`m` superdiagonal dipole orthogonality, exact mutual orthogonality
of `{v₂, v₃, v₄}` with a 3-mode Pythagorean energy identity on `Finset.Icc 1 6`, `N = 6` trace
cancellation, and the unit-partition homogeneous kernel `unitDefectEntry` on `IsDirichletAnchored`.
-/

@[expose] public section
open scoped BigOperators
/-- **Universal Superdiagonal Dipole Orthogonality**: `∀ m ≥ 1, G̃(m, m+1) = G̃(m+1, m) = 0`. -/
theorem dipoleGramEntry_self_succ_eq_zero {m : ℕ} (hm : 1 ≤ m) :
    dipoleGramEntry m (m + 1) = 0 ∧ dipoleGramEntry (m + 1) m = 0 := by
  have h0 : dipoleGramEntry m (m + 1) = 0 := by
    have hm1 : ((m + 1 : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have hm2 : ((m + 2 : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have hm3 : ((m + 3 : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have hadd1 := vasyuninCotSum_add_self_right (m + 1) 1
    have hadd2 := vasyuninCotSum_add_self_right (m + 1) 2
    have hadd3 := vasyuninCotSum_add_self_right (m + 2) 1
    have hsub1 := vasyuninCotSum_sub_eq_neg (a := m + 2) (b := 1) (by omega)
    have hsub2 := vasyuninCotSum_sub_eq_neg (a := m + 3) (b := 2) (by omega)
    have hsub3 := vasyuninCotSum_sub_eq_neg (a := m + 3) (b := 1) (by omega)
    rw [show m + 1 + 1 = m + 2 by omega] at hadd1
    rw [show m + 1 + 2 = m + 3 by omega] at hadd2 hadd3
    rw [show m + 2 - 1 = m + 1 by omega] at hsub1
    rw [show m + 3 - 2 = m + 1 by omega] at hsub2
    rw [show m + 3 - 1 = m + 2 by omega] at hsub3
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
    show m + 1 + 2 = m + 3 by omega] at h; linarith
/-- **Exact Mutually Orthogonal Triple Theorem** on `{v₂, v₃, v₄}`. -/
theorem dipoleGramEntry_orthogonal_triple_two_three_four :
    dipoleGramEntry 2 3 = 0 ∧ dipoleGramEntry 3 4 = 0 ∧ dipoleGramEntry 2 4 = 0 :=
  ⟨dipoleGramEntry_two_three_eq_zero.1,
    (dipoleGramEntry_self_succ_eq_zero (by omega : 1 ≤ 3)).1,
    dipoleGramEntry_two_four_eq_zero.1⟩
private lemma cumulativeDipole_Icc_six_div {m a : ℕ} (hm : 1 ≤ m) (hm6 : m + 2 ≤ 6)
    (ha : 1 ≤ a) :
    ∑ j ∈ Finset.Icc (a + 2) 6, cumulativeDipole m j / (j : ℝ) = if m = a then 1 else 0 := by
  let F : ℕ → ℝ := fun k => if a + 2 ≤ k then 1 else 0
  have hs := cumulativeDipole_div_sum_eq_four_point F hm hm6
  rw [Finset.sum_congr rfl fun k _ => show cumulativeDipole m k * (F k / (k : ℝ)) =
    if a + 2 ≤ k then cumulativeDipole m k / (k : ℝ) else 0 by dsimp [F]; split_ifs <;> ring] at hs
  rw [show Finset.Icc (a + 2) 6 = (Finset.Icc 1 6).filter (fun k => a + 2 ≤ k) by
    ext k; simp only [Finset.mem_Icc, Finset.mem_filter]; omega, Finset.sum_filter, hs]
  by_cases hma : m = a <;> (dsimp [F]; split_ifs <;> norm_num <;> omega)
/-- **3-Mode Pythagorean Additive Energy Law on `span {v₂, v₃, v₄}`**. -/
theorem QCot_span_two_three_four_eq_sum_sq (α₂ α₃ α₄ : ℝ) :
    let h : ℕ → ℝ := fun k =>
      α₂ * cumulativeDipole 2 k + α₃ * cumulativeDipole 3 k + α₄ * cumulativeDipole 4 k
    QCot vasyuninGCot h 6 = α₂ ^ 2 * dipoleGramEntry 2 2 + α₃ ^ 2 * dipoleGramEntry 3 3 +
      α₄ ^ 2 * dipoleGramEntry 4 4 := by
  intro h
  have ht2 := cumulativeDipole_mem_tangent (by omega : 1 ≤ 2) (by omega : 2 + 2 ≤ 6)
  have ht3 := cumulativeDipole_mem_tangent (by omega : 1 ≤ 3) (by omega : 3 + 2 ≤ 6)
  have ht4 := cumulativeDipole_mem_tangent (by omega : 1 ≤ 4) (by omega : 4 + 2 ≤ 6)
  have hh1 : D1 h 6 = 0 := by
    have h2 := ht2.1; have h3 := ht3.1; have h4 := ht4.1; unfold D1 at h2 h3 h4 ⊢
    simp_rw [h, add_div, mul_div_assoc, Finset.sum_add_distrib, ← Finset.mul_sum, h2, h3, h4]; ring
  have hh0 : D0 h 6 = 0 := by
    have h2 := ht2.2; have h3 := ht3.2; have h4 := ht4.2; unfold D0 at h2 h3 h4 ⊢
    simp_rw [h, Finset.sum_add_distrib, ← Finset.mul_sum, h2, h3, h4]; ring
  have hc : ∀ a ∈ Finset.Icc 1 4, dipoleCoord h 6 a = α₂ * (if 2 = a then 1 else 0) +
      α₃ * (if 3 = a then 1 else 0) + α₄ * (if 4 = a then 1 else 0) := fun a ha => by
    have ha1 : 1 ≤ a := (Finset.mem_Icc.mp ha).1; unfold dipoleCoord
    simp_rw [h, add_div, mul_div_assoc, Finset.sum_add_distrib, ← Finset.mul_sum,
      cumulativeDipole_Icc_six_div (by omega : 1 ≤ 2) (by omega : 2 + 2 ≤ 6) ha1,
      cumulativeDipole_Icc_six_div (by omega : 1 ≤ 3) (by omega : 3 + 2 ≤ 6) ha1,
      cumulativeDipole_Icc_six_div (by omega : 1 ≤ 4) (by omega : 4 + 2 ≤ 6) ha1]
  rw [QCot_eq_sum_dipoleGramEntry (by omega : 2 ≤ 6) h hh1 hh0]
  have hsum4 : ∀ f : ℕ → ℝ, ∑ i ∈ Finset.Icc 1 (6 - 2), f i = f 1 + f 2 + f 3 + f 4 := fun f => by
    rw [show Finset.Icc 1 (6 - 2) = ({1, 2, 3, 4} : Finset ℕ) by ext x; simp; omega,
      Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_singleton]; ring
  simp_rw [hsum4]; rw [hc 1 (by decide), hc 2 (by decide), hc 3 (by decide), hc 4 (by decide)]
  norm_num; have ht := dipoleGramEntry_orthogonal_triple_two_three_four
  rw [dipoleGramEntry_comm 3 2, dipoleGramEntry_comm 4 3, dipoleGramEntry_comm 4 2,
    ht.1, ht.2.1, ht.2.2]; ring
/-- Exact closed-form `N = 6` diagonal entry `dipoleGramEntry 4 4`. -/
theorem dipoleGramEntry_four_four_eq :
    dipoleGramEntry 4 4 = Real.pi * (4 / Real.sqrt 3 - Real.cos (Real.pi / 5) /
      Real.sin (Real.pi / 5) - Real.cos (2 * Real.pi / 5) / Real.sin (2 * Real.pi / 5)) := by
  have hsq3 : Real.sqrt 3 ≠ 0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  rw [dipoleGramEntry_diag_eq 4]; unfold unweightedKCot vasyuninGCot deltaCot
  simp only [Nat.reduceAdd, Nat.cast_ofNat]
  rw [vasyuninCotSum_add_self_right 5 1, vasyuninCotSum_five_one_eq, vasyuninCotSum_five_two_eq,
    vasyuninCotSum_six_eval.1, vasyuninCotSum_six_eval.2.1, vasyuninCotSum_six_eval.2.2.2.2]
  field_simp [hsq3]; ring
/-- Exact `N = 6` block trace cancelling all `ℚ(√5)` cotangents: `G̃₃₃ + G̃₄₄ = π(4/√3 - 1)`. -/
theorem dipoleGramEntry_three_three_add_four_four_eq :
    dipoleGramEntry 3 3 + dipoleGramEntry 4 4 = Real.pi * (4 / Real.sqrt 3 - 1) := by
  rw [dipoleGramEntry_three_three_eq, dipoleGramEntry_four_four_eq]; ring
private lemma cumulativeDipole_at_one (m : ℕ) (hm : 1 ≤ m) : cumulativeDipole m 1 = 1 := by
  unfold cumulativeDipole; rw [Finset.sum_eq_single 1]
  · simp [harmonicWavelet]
  · intro r hr hne; rcases r with _ | _ | r <;> [exact absurd (Finset.mem_Icc.mp hr).1 (by decide);
      exact absurd rfl hne; simp [harmonicWavelet]]
  · intro h; exact absurd (Finset.mem_Icc.mpr ⟨le_rfl, hm⟩) h
/-- Unit-partition duality on `IsDirichletAnchored c N`: `∑_{k=2}^N c_k / k = 1 ∧ ∑ αₘ = 1`. -/
theorem isDirichletAnchored_unit_partition {N : ℕ} (hN : 2 ≤ N) {c : ℕ → ℝ}
    (hc : IsDirichletAnchored c N) : ∑ k ∈ Finset.Icc 2 N, c k / (k : ℝ) = 1 ∧
      ∑ m ∈ Finset.Icc 1 (N - 2), dipoleCoord c N m = 1 := by
  have hk : ∑ k ∈ Finset.Icc 2 N, c k / (k : ℝ) = 1 := by
    have hd1 := hc.1; unfold D1 at hd1
    rw [show Finset.Icc 1 N = insert 1 (Finset.Icc 2 N) by
      ext k; simp only [Finset.mem_Icc, Finset.mem_insert]; omega,
      Finset.sum_insert (by simp), hc.2.2] at hd1; norm_num at hd1; linarith
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

/-- Exact `N = 4, 6` unit-defect trace identities (`2` and `2 + 2π / (3√3)`) and `M₁₂ < 0`. -/
theorem unitDefectEntry_traces_and_one_two :
    (unitDefectEntry 1 1 + unitDefectEntry 2 2 = 2) ∧
      (unitDefectEntry 3 3 + unitDefectEntry 4 4 = 2 + 2 * Real.pi / (3 * Real.sqrt 3)) ∧
      (unitDefectEntry 1 2 = 1 - Real.pi / 2 ∧ unitDefectEntry 1 2 < 0) := by
  have hsq3 : Real.sqrt 3 ≠ 0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  refine ⟨?_, ?_, ?_⟩
  · unfold unitDefectEntry; simp only [Nat.reduceAdd]
    rw [dipoleGramEntry_one_one_eq, dipoleGramEntry_two_two_eq, deltaCot_two_four_eq.1,
      deltaCot_two_four_eq.2]; field_simp [hsq3]; ring
  · unfold unitDefectEntry; simp only [Nat.reduceAdd]
    rw [deltaCot_two_four_eq.2, deltaCot_six_eq, show 1 - Real.pi * (deltaCot 5 - 1 / 2 +
      deltaCot 5 - 1 / 2) + dipoleGramEntry 3 3 + (1 - Real.pi * (5 / (3 * Real.sqrt 3) -
      deltaCot 5 + 5 / (3 * Real.sqrt 3) - deltaCot 5) + dipoleGramEntry 4 4) = 2 - 2 * Real.pi *
      (5 / (3 * Real.sqrt 3) - 1 / 2) + (dipoleGramEntry 3 3 + dipoleGramEntry 4 4) by ring,
      dipoleGramEntry_three_three_add_four_four_eq]; field_simp [hsq3]; ring
  · have h : unitDefectEntry 1 2 = 1 - Real.pi / 2 := by
      unfold unitDefectEntry; rw [dipoleGramEntry_one_two_eq_zero]; simp only [Nat.reduceAdd,
        add_zero]
      rw [show deltaCot 3 - deltaCot 2 + deltaCot 4 - deltaCot 3 = deltaCot 4 - deltaCot 2 by ring,
        deltaCot_two_four_eq.1, deltaCot_two_four_eq.2]; ring
    exact ⟨h, by linarith [Real.pi_gt_three]⟩

/-- **Master Homogeneous Unit-Defect Reduction** and non-negativity on `IsDirichletAnchored c N`. -/
theorem one_sub_SCot_eq_sum_unitDefectEntry_of_isDirichletAnchored {N : ℕ} (hN : 2 ≤ N)
    {c : ℕ → ℝ} (hc : IsDirichletAnchored c N) : (1 - SCot vasyuninGCot c N =
      ∑ a ∈ Finset.Icc 1 (N - 2), ∑ b ∈ Finset.Icc 1 (N - 2),
        dipoleCoord c N a * dipoleCoord c N b * unitDefectEntry a b) ∧
      (0 ≤ ∑ a ∈ Finset.Icc 1 (N - 2), ∑ b ∈ Finset.Icc 1 (N - 2),
        dipoleCoord c N a * dipoleCoord c N b * unitDefectEntry a b) := by
  have ht := hc.sub_mem_tangent hN; have hS := (isDirichletAnchored_unit_partition hN hc).2
  have hLr : (∑ m ∈ Finset.Icc 1 (N - 2), dipoleCoord (fun k => c k - cBaseAnchor k) N m *
      (deltaCot (m + 2) - deltaCot (m + 1))) = ∑ m ∈ Finset.Icc 1 (N - 2),
      dipoleCoord c N m * (deltaCot (m + 2) - deltaCot (m + 1)) := Finset.sum_congr rfl
    fun m hm => by rw [dipoleCoord_sub_cBaseAnchor_eq (Finset.mem_Icc.mp hm).1]
  have hlin : ∑ a ∈ Finset.Icc 1 (N - 2), ∑ b ∈ Finset.Icc 1 (N - 2),
      dipoleCoord c N a * dipoleCoord c N b * (1 - Real.pi / 2 * (deltaCot (a + 2) -
        deltaCot (a + 1) + deltaCot (b + 2) - deltaCot (b + 1))) =
      1 - Real.pi * ∑ m ∈ Finset.Icc 1 (N - 2), dipoleCoord c N m *
        (deltaCot (m + 2) - deltaCot (m + 1)) := by
    let Δ : ℕ → ℝ := fun m => deltaCot (m + 2) - deltaCot (m + 1)
    have hcon : ∀ a ∈ Finset.Icc 1 (N - 2), ∑ b ∈ Finset.Icc 1 (N - 2),
        dipoleCoord c N a * dipoleCoord c N b * (1 - Real.pi / 2 * (Δ a + Δ b)) =
        dipoleCoord c N a - Real.pi / 2 * (dipoleCoord c N a * Δ a) -
          (Real.pi / 2 * ∑ b ∈ Finset.Icc 1 (N - 2), dipoleCoord c N b * Δ b) *
            dipoleCoord c N a := fun a _ => by
      rw [Finset.sum_congr rfl fun b _ => show dipoleCoord c N a * dipoleCoord c N b *
        (1 - Real.pi / 2 * (Δ a + Δ b)) = dipoleCoord c N a * dipoleCoord c N b - Real.pi / 2 *
        (dipoleCoord c N a * Δ a) * dipoleCoord c N b - (Real.pi / 2 * dipoleCoord c N a) *
        (dipoleCoord c N b * Δ b) by ring]
      simp only [Finset.sum_sub_distrib, ← Finset.mul_sum, hS, mul_one]; ring
    rw [Finset.sum_congr rfl fun a ha => by simpa [Δ, add_sub_assoc] using hcon a ha]
    simp only [Finset.sum_sub_distrib, ← Finset.mul_sum, hS, mul_one]; ring
  have hU : ∑ a ∈ Finset.Icc 1 (N - 2), ∑ b ∈ Finset.Icc 1 (N - 2),
      dipoleCoord c N a * dipoleCoord c N b * unitDefectEntry a b =
      (∑ a ∈ Finset.Icc 1 (N - 2), ∑ b ∈ Finset.Icc 1 (N - 2), dipoleCoord c N a * dipoleCoord c N b
        * (1 - Real.pi / 2 * (deltaCot (a + 2) - deltaCot (a + 1) + deltaCot (b + 2) -
          deltaCot (b + 1)))) + dipolePlaqueForm (fun k => c k - cBaseAnchor k) N := by
    rw [dipolePlaqueForm_sub_cBaseAnchor_eq c N]; unfold dipolePlaqueForm
    simp_rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by
      unfold unitDefectEntry; rw [dipoleGramEntry_eq_boundary_add_plaque a b]; ring
  have heq : 1 - SCot vasyuninGCot c N = ∑ a ∈ Finset.Icc 1 (N - 2), ∑ b ∈ Finset.Icc 1 (N - 2),
      dipoleCoord c N a * dipoleCoord c N b * unitDefectEntry a b := by
    rw [SCot_eq_drive_sub_dipolePlaqueForm_of_dirichlet hN hc,
      linearCotDrive_eq_sum_dipoleCoord hN _ ht.1 ht.2.1, hLr, hU, hlin]; ring
  refine ⟨heq, ?_⟩
  rw [← heq, ← affine_l2_dist_eq_one_sub_scot c hc.1 hc.2.1]
  exact intervalIntegral.integral_nonneg (by norm_num) fun _ _ => sq_nonneg _
