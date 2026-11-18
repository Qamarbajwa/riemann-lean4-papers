/-
Copyright (c) 2026 Qamar Munawer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qamar Munawer
-/
module

public import RiemannBlueprint.UpstreamPRs.UpstreamPR_8J_UnitPartitionHomogenization

/-!
# Superdiagonal Zeros `G̃(m, m+1) = 0`, Orthogonal Triple `{v₂, v₃, v₄}`, & `{1..9}` Folding

This module establishes:
* `vasyuninCotSum_le_nine_fold`: `{1..9}` fundamental horizon modulo folding into `[1, 8]`.
* `dipoleGramEntry_self_succ_eq_zero`, `dipolePlaqueEntry_self_succ_eq`,
  `unitDefectEntry_self_succ_eq`: universal all-`m` superdiagonal orthogonality.
* `dipoleGramEntry_orthogonal_triple_two_three_four`, `QCot_span_two_three_four_eq_sum_sq`:
  exact mutually orthogonal triple `{v₂, v₃, v₄}` and 3-mode Pythagorean energy law.
* `dipoleGramEntry_four_four_eq`, `dipoleGramEntry_three_three_add_four_four_eq`,
  `unitDefectEntry_one_one_add_two_two_eq`, `unitDefectEntry_three_three_add_four_four_eq`:
  exact `N = 4, 6` radical trace cancellations.
-/

@[expose] public section

open scoped BigOperators

/-- **`{1..9}` Fundamental Horizon Folding Theorem**: for `a ∈ [1, 9]` and every `b : ℕ`,
either `a ∣ b ∧ V(a, b) = 0` or `V(a, b) = V(a, r)` for `r = b % a ∈ [1, 8]`. -/
theorem vasyuninCotSum_le_nine_fold {a : ℕ} (ha : a ∈ Finset.Icc 1 9) (b : ℕ) :
    (a ∣ b ∧ vasyuninCotSum a b = 0) ∨
      ∃ r ∈ Finset.Icc 1 8, r = b % a ∧ vasyuninCotSum a b = vasyuninCotSum a r := by
  by_cases h : a ∣ b
  · exact Or.inl ⟨h, vasyuninCotSum_dvd_right_eq_zero h⟩
  · have ha1 : 1 ≤ a := (Finset.mem_Icc.mp ha).1
    have ha9 : a ≤ 9 := (Finset.mem_Icc.mp ha).2
    have hne0 : b % a ≠ 0 := fun hz => h (Nat.dvd_of_mod_eq_zero hz)
    have hlt : b % a < a := Nat.mod_lt b (by omega)
    exact Or.inr ⟨b % a, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, rfl,
      (vasyuninCotSum_mod_eq a b).symm⟩

/-- **Universal Superdiagonal Orthogonality**: `∀ m : ℕ, G̃(m, m+1) = G̃(m+1, m) = 0`. -/
theorem dipoleGramEntry_self_succ_eq_zero (m : ℕ) :
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
theorem dipolePlaqueEntry_self_succ_eq (m : ℕ) :
    dipolePlaqueEntry m (m + 1) = -(Real.pi / 2) * (deltaCot (m + 3) - deltaCot (m + 1)) := by
  have h := dipoleGramEntry_eq_boundary_add_plaque m (m + 1)
  rw [(dipoleGramEntry_self_succ_eq_zero m).1, show m + 1 + 1 = m + 2 by omega,
    show m + 1 + 2 = m + 3 by omega] at h; linarith

/-- Universal superdiagonal collapse of `unitDefectEntry` forced by `G̃(m, m+1) = 0`. -/
theorem unitDefectEntry_self_succ_eq (m : ℕ) :
    unitDefectEntry m (m + 1) = 1 - Real.pi * (deltaCot (m + 3) - deltaCot (m + 1)) := by
  rw [unitDefectEntry_eq_one_sub_drive_add_gram m (m + 1),
    (dipoleGramEntry_self_succ_eq_zero m).1, show m + 1 + 1 = m + 2 by omega,
    show m + 1 + 2 = m + 3 by omega]; ring

/-- **Exact Mutually Orthogonal Triple Theorem** on `{v₂, v₃, v₄}`. -/
theorem dipoleGramEntry_orthogonal_triple_two_three_four :
    dipoleGramEntry 2 3 = 0 ∧ dipoleGramEntry 3 4 = 0 ∧ dipoleGramEntry 2 4 = 0 :=
  ⟨dipoleGramEntry_two_three_eq_zero.1, (dipoleGramEntry_self_succ_eq_zero 3).1,
    dipoleGramEntry_two_four_eq_zero.1⟩

private lemma cumulativeDipole_Icc_six_div {m a : ℕ} (hm : 1 ≤ m) (hm6 : m + 2 ≤ 6)
    (ha : 1 ≤ a) :
    ∑ j ∈ Finset.Icc (a + 2) 6, cumulativeDipole m j / (j : ℝ) = if m = a then 1 else 0 := by
  let F : ℕ → ℝ := fun k => if a + 2 ≤ k then 1 else 0
  have hs := cumulativeDipole_div_sum_eq_four_point F hm hm6
  rw [Finset.sum_congr rfl fun k _ => show cumulativeDipole m k * (F k / (k : ℝ)) =
    if a + 2 ≤ k then cumulativeDipole m k / (k : ℝ) else 0 from by
      dsimp [F]; split_ifs <;> ring] at hs
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
    simp_rw [h, add_div, mul_div_assoc, Finset.sum_add_distrib, ← Finset.mul_sum, h2, h3, h4]
    ring
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
  have hsum4 : ∀ f : ℕ → ℝ,
      ∑ i ∈ Finset.Icc 1 (6 - 2), f i = f 1 + f 2 + f 3 + f 4 := fun f => by
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

/-- Exact `N = 6` trace cancelling `ℚ(√5)` terms: `G̃₃₃ + G̃₄₄ = π(4/√3 - 1)`. -/
theorem dipoleGramEntry_three_three_add_four_four_eq :
    dipoleGramEntry 3 3 + dipoleGramEntry 4 4 = Real.pi * (4 / Real.sqrt 3 - 1) := by
  rw [dipoleGramEntry_three_three_eq, dipoleGramEntry_four_four_eq]; ring

private lemma deltaCot_two_four_eq_8k : deltaCot 2 = 0 ∧ deltaCot 4 = 1 / 2 := by
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
  exact ⟨by unfold deltaCot; rw [hv2, hv2, sub_self],
    by unfold deltaCot; rw [hv4, hv4]; norm_num⟩

/-- Exact `N = 4` unit-defect trace identity: `unitDefectEntry 1 1 + unitDefectEntry 2 2 = 2`. -/
theorem unitDefectEntry_one_one_add_two_two_eq :
    unitDefectEntry 1 1 + unitDefectEntry 2 2 = 2 := by
  have hsq3 : Real.sqrt 3 ≠ 0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  rw [unitDefectEntry_eq_one_sub_drive_add_gram 1 1, unitDefectEntry_eq_one_sub_drive_add_gram 2 2]
  simp only [Nat.reduceAdd]
  rw [dipoleGramEntry_one_one_eq, dipoleGramEntry_two_two_eq, deltaCot_two_four_eq_8k.1,
    deltaCot_two_four_eq_8k.2]; field_simp [hsq3]; ring

/-- Exact `N = 6` unit-defect trace identity: `M₃₃ + M₄₄ = 2 + 2π / (3√3)`. -/
theorem unitDefectEntry_three_three_add_four_four_eq :
    unitDefectEntry 3 3 + unitDefectEntry 4 4 = 2 + 2 * Real.pi / (3 * Real.sqrt 3) := by
  have hsq3 : Real.sqrt 3 ≠ 0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  rw [unitDefectEntry_eq_one_sub_drive_add_gram 3 3, unitDefectEntry_eq_one_sub_drive_add_gram 4 4]
  simp only [Nat.reduceAdd]
  rw [deltaCot_two_four_eq_8k.2, deltaCot_six_eq, show 1 - Real.pi * (deltaCot 5 - 1 / 2 +
    deltaCot 5 - 1 / 2) + dipoleGramEntry 3 3 + (1 - Real.pi * (5 / (3 * Real.sqrt 3) -
    deltaCot 5 + 5 / (3 * Real.sqrt 3) - deltaCot 5) + dipoleGramEntry 4 4) = 2 - 2 * Real.pi *
    (5 / (3 * Real.sqrt 3) - 1 / 2) + (dipoleGramEntry 3 3 + dipoleGramEntry 4 4) by ring,
    dipoleGramEntry_three_three_add_four_four_eq]; field_simp [hsq3]; ring
