/-
Copyright (c) 2026 Qamar Munawer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qamar Munawer
-/
module

public import RiemannBlueprint.UpstreamPRs.UpstreamPR_8H_UniversalCotangentSymmetries

/-!
# Variational Plaque Majorant and BBLR Logarithmic Decay (`C / log N`) Bridge to RH

This module establishes explicit asymptotic test-sequence criteria sufficient to trigger
`PurePlaqueVanishingCriterion` and `_root_.RiemannHypothesis`:

* `purePlaqueVanishing_of_majorant_tendsto_zero`: any eventually Dirichlet-anchored, unit-drive
  tangent sequence `h N` whose pure plaque form is bounded by a majorant `B N → 0` satisfies
  `PurePlaqueVanishingCriterion`.
* `riemannHypothesis_of_plaque_majorant_tendsto_zero`: conditional implication to
  `_root_.RiemannHypothesis` assuming `TitchmarshMellinProperty`.
* `riemannHypothesis_of_logarithmic_plaque_bound`: specialization to BBLR logarithmic upper
  bounds `dipolePlaqueForm (h N) N ≤ C / Real.log N`.
-/

@[expose] public section

open scoped BigOperators
open Filter

/-- Any eventually Dirichlet-anchored, unit-drive tangent sequence whose `dipolePlaqueForm` is
dominated by a sequence `B N → 0` satisfies `PurePlaqueVanishingCriterion`. -/
theorem purePlaqueVanishing_of_majorant_tendsto_zero
    (h : ℕ → ℕ → ℝ) (B : ℕ → ℝ) (hB : Tendsto B atTop (nhds 0))
    (h_ev : ∀ᶠ N in atTop,
      2 ≤ N ∧ D1 (h N) N = 0 ∧ D0 (h N) N = 0 ∧ h N 1 = 1 ∧
        Real.pi * linearCotDrive (h N) N = 1 ∧ dipolePlaqueForm (h N) N ≤ B N) :
    PurePlaqueVanishingCriterion := by
  intro ε hε
  have hlt : ∀ᶠ N in atTop, B N < ε := hB.eventually (gt_mem_nhds hε)
  obtain ⟨N, ⟨hN2, hd1, hd0, hh1, hdrv, hbd⟩, hBε⟩ := (h_ev.and hlt).exists
  let c : ℕ → ℝ := fun k => cBaseAnchor k + h N k
  have hbase := cBaseAnchor_mem_A_N hN2
  have hsub : (fun k => c k - cBaseAnchor k) = h N := by
    ext k; dsimp [c]; ring
  have hcD1 : D1 c N = 0 := by
    unfold D1 at hbase hd1 ⊢
    have hpt : ∀ k ∈ Finset.Icc 1 N,
        c k / (k : ℝ) = cBaseAnchor k / (k : ℝ) + h N k / (k : ℝ) := fun k _ => by
      dsimp [c]; ring
    rw [Finset.sum_congr rfl hpt, Finset.sum_add_distrib, hbase.1, hd1, add_zero]
  have hcD0 : D0 c N = 2 := by
    unfold D0 at hbase hd0 ⊢
    have hpt : ∀ k ∈ Finset.Icc 1 N, c k = cBaseAnchor k + h N k := fun _ _ => rfl
    rw [Finset.sum_congr rfl hpt, Finset.sum_add_distrib, hbase.2, hd0, add_zero]
  have hc1 : c 1 = -1 := by
    dsimp [c, cBaseAnchor]
    rw [hh1]
    norm_num
  refine ⟨N, c, hN2, ⟨hcD1, hcD0, hc1⟩, ?_, ?_⟩
  · simpa [hsub] using hdrv
  · rw [hsub]; linarith

/-- Any variational test sequence whose pure plaque energy admits a vanishing majorant `B N → 0`
implies `_root_.RiemannHypothesis` under `TitchmarshMellinProperty`. -/
theorem riemannHypothesis_of_plaque_majorant_tendsto_zero
    (hT : TitchmarshMellinProperty) (h : ℕ → ℕ → ℝ) (B : ℕ → ℝ)
    (hB : Tendsto B atTop (nhds 0))
    (h_ev : ∀ᶠ N in atTop,
      2 ≤ N ∧ D1 (h N) N = 0 ∧ D0 (h N) N = 0 ∧ h N 1 = 1 ∧
        Real.pi * linearCotDrive (h N) N = 1 ∧ dipolePlaqueForm (h N) N ≤ B N) :
    _root_.RiemannHypothesis :=
  riemannHypothesis_of_purePlaque_vanishing hT
    (purePlaqueVanishing_of_majorant_tendsto_zero h B hB h_ev)

/-- Specialization of the variational majorant theorem to BBLR logarithmic upper bounds
`C / Real.log N`: proving a `C / log N` plaque bound along any unit-drive Dirichlet-anchored
tangent sequence implies `_root_.RiemannHypothesis` under `TitchmarshMellinProperty`. -/
theorem riemannHypothesis_of_logarithmic_plaque_bound
    (hT : TitchmarshMellinProperty) (h : ℕ → ℕ → ℝ) (C : ℝ)
    (h_ev : ∀ᶠ N in atTop,
      2 ≤ N ∧ D1 (h N) N = 0 ∧ D0 (h N) N = 0 ∧ h N 1 = 1 ∧
        Real.pi * linearCotDrive (h N) N = 1 ∧
        dipolePlaqueForm (h N) N ≤ C / Real.log (N : ℝ)) :
    _root_.RiemannHypothesis := by
  have hlog : Tendsto (fun N : ℕ => C / Real.log (N : ℝ)) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  exact riemannHypothesis_of_plaque_majorant_tendsto_zero hT h
    (fun N : ℕ => C / Real.log (N : ℝ)) hlog h_ev
