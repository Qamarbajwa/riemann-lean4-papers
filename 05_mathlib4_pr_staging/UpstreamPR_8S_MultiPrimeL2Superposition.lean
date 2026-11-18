/-
Copyright (c) 2026 Qamar Munawer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qamar Munawer
-/
module

public import RiemannBlueprint.UpstreamPRs.UpstreamPR_8R_MellinZeroObstructionFloor

/-!
# Arbitrary Finite Prime-Set L² Superposition and Unified Planar–Mellin Contradiction Capstone

This module lifts the two-prime energy floor of `UpstreamPR_8Q` to arbitrary finite sets of
primes `S ⊆ Icc (N + 1) M` (`N ≥ 2`) and bundles the coordinate-space and Mellin-space sides of
the finite-truncation contradiction into a single capstone theorem:

* `odd_prime_dist_ge_two` and `disjoint_prime_cell_pairs`: distinct primes `p, q ≥ 3` are odd,
  satisfy `p + 2 ≤ q ∨ q + 2 ≤ p`, and yield disjoint cell pairs `{p - 1, p}` and `{q - 1, q}`.
* `sum_harmonicPairEnergy_le_harmonicCellL2PartialSum` and
  `harmonicCellL2PartialSum_ge_sum_primes`: via `Finset.biUnion`, under `IsDirichletAnchored c N`
  (`N ≥ 2`), every finite prime set `S ⊆ Icc (N + 1) M` contributes at least
  `∑ p ∈ S, 1 / (2 * p ^ 2)` to `harmonicCellL2PartialSum c N M`.
* `planar_mellin_dual_contradiction_capstone`: unifies top-half `(1 / 2, 1]` annihilation,
  multi-prime `L²` energy superposition, unconditional `L²(0, 1]` positivity for finite `N`,
  Mellin zero non-vanishing `1 / s₀ ≠ 0`, and the uniform off-line Cauchy–Schwarz barrier.
-/

@[expose] public section

private lemma harmonicCellWidth_nonneg_8s (n : ℕ) : 0 ≤ harmonicCellWidth n := by
  unfold harmonicCellWidth; positivity

/-- Distinct odd primes `p, q ≥ 3` differ by at least `2`. -/
theorem odd_prime_dist_ge_two {p q : ℕ} (hp : Nat.Prime p) (hq : Nat.Prime q)
    (hp3 : 3 ≤ p) (hq3 : 3 ≤ q) (hpq : p ≠ q) : p + 2 ≤ q ∨ q + 2 ≤ p := by
  have hpo : p % 2 = 1 := Nat.odd_iff.mp (hp.odd_of_ne_two (by omega))
  have hqo : q % 2 = 1 := Nat.odd_iff.mp (hq.odd_of_ne_two (by omega))
  omega

/-- Distinct odd primes `p, q ≥ 3` produce strictly disjoint adjacent cell pairs `{p - 1, p}`
and `{q - 1, q}`. -/
theorem disjoint_prime_cell_pairs {p q : ℕ} (hp : Nat.Prime p) (hq : Nat.Prime q)
    (hp3 : 3 ≤ p) (hq3 : 3 ≤ q) (hpq : p ≠ q) :
    Disjoint ({p - 1, p} : Finset ℕ) {q - 1, q} := by
  have hdist := odd_prime_dist_ge_two hp hq hp3 hq3 hpq
  rw [Finset.disjoint_left]
  intro x hx1 hx2
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx1 hx2
  rcases hdist with h | h <;> rcases hx1 with rfl | rfl <;> rcases hx2 with h1 | h2 <;> omega

/-- For `N ≥ 2` and `S ⊆ Icc (N + 1) M`, the union `⋃ p ∈ S, {p - 1, p}` stays inside `Icc 1 M`. -/
theorem biUnion_prime_pairs_subset_Icc {N M : ℕ} (hN : 2 ≤ N) {S : Finset ℕ}
    (hS : S ⊆ Finset.Icc (N + 1) M) :
    (S.biUnion fun p => ({p - 1, p} : Finset ℕ)) ⊆ Finset.Icc 1 M := by
  intro n hn
  rw [Finset.mem_biUnion] at hn
  rcases hn with ⟨p, hpS, hnp⟩
  have hp_mem := Finset.mem_Icc.mp (hS hpS)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hnp
  simp only [Finset.mem_Icc]
  rcases hnp with rfl | rfl <;> omega

/-- **Finite Prime-Set Pair-Energy Superposition**: for `N ≥ 2` and any finite prime set
`S ⊆ Icc (N + 1) M`, the sum of adjacent pair energies `∑ p ∈ S, harmonicPairEnergy c N p` is
at most `harmonicCellL2PartialSum c N M`. -/
theorem sum_harmonicPairEnergy_le_harmonicCellL2PartialSum (c : ℕ → ℝ) {N M : ℕ} (hN : 2 ≤ N)
    {S : Finset ℕ} (hS : S ⊆ Finset.Icc (N + 1) M) (hprime : ∀ p ∈ S, Nat.Prime p) :
    ∑ p ∈ S, harmonicPairEnergy c N p ≤ harmonicCellL2PartialSum c N M := by
  have hsub := biUnion_prime_pairs_subset_Icc hN hS
  have hsum := Finset.sum_le_sum_of_subset_of_nonneg hsub
    (f := fun n => (discreteCellResidual c N n) ^ 2 * harmonicCellWidth n)
    (fun n _ _ => mul_nonneg (sq_nonneg _) (harmonicCellWidth_nonneg_8s n))
  have hdisj : Set.PairwiseDisjoint (S : Set ℕ) (fun p => ({p - 1, p} : Finset ℕ)) := by
    intro p hp q hq hpq
    have hp_mem := Finset.mem_Icc.mp (hS hp)
    have hq_mem := Finset.mem_Icc.mp (hS hq)
    exact disjoint_prime_cell_pairs (hprime p hp) (hprime q hq)
      (by omega) (by omega) hpq
  rw [Finset.sum_biUnion hdisj] at hsum
  have hcongr : ∑ p ∈ S, harmonicPairEnergy c N p =
      ∑ p ∈ S, ∑ n ∈ ({p - 1, p} : Finset ℕ),
        (discreteCellResidual c N n) ^ 2 * harmonicCellWidth n := by
    refine Finset.sum_congr rfl fun p hp => ?_
    have hp_mem := Finset.mem_Icc.mp (hS hp)
    have hp2 : 2 ≤ p := (hprime p hp).two_le
    rw [Finset.sum_pair (by omega : p - 1 ≠ p), harmonicPairEnergy_eq_width_sum c N hp2]
  exact hcongr ▸ hsum

/-- **Arbitrary Finite Prime-Set L² Horizon Floor**: under `IsDirichletAnchored c N` (`N ≥ 2`),
every finite set of primes `S ⊆ Icc (N + 1) M` forces
`∑ p ∈ S, 1 / (2 * p ^ 2) ≤ harmonicCellL2PartialSum c N M`. -/
theorem harmonicCellL2PartialSum_ge_sum_primes {c : ℕ → ℝ} {N M : ℕ} (hN : 2 ≤ N)
    (hc : IsDirichletAnchored c N) {S : Finset ℕ} (hS : S ⊆ Finset.Icc (N + 1) M)
    (hprime : ∀ p ∈ S, Nat.Prime p) :
    ∑ p ∈ S, (1 : ℝ) / (2 * (p : ℝ) ^ 2) ≤ harmonicCellL2PartialSum c N M := by
  have hterm : ∑ p ∈ S, (1 : ℝ) / (2 * (p : ℝ) ^ 2) ≤ ∑ p ∈ S, harmonicPairEnergy c N p := by
    refine Finset.sum_le_sum fun p hp => ?_
    have hp_mem := Finset.mem_Icc.mp (hS hp)
    exact (harmonicPairEnergy_prime_ge_inv_two_sq_of_anchored (by omega : 1 ≤ N) hc
      (hprime p hp) (by omega : N < p)).2
  exact le_trans hterm (sum_harmonicPairEnergy_le_harmonicCellL2PartialSum c hN hS hprime)

/-- **Unified Planar–Mellin Contradiction Capstone**: for every finite cutoff `N ≥ 2` and every
Dirichlet-anchored vector `IsDirichletAnchored c N`:
(1) `continuousNymanResidual c N` vanishes pointwise on the outer slab `(1 / 2, 1]`;
(2) every finite prime set `S ⊆ Icc (N + 1) M` forces `∑ p ∈ S, 1 / (2 * p^2)` into
`harmonicCellL2PartialSum c N M`, with `0 < ∫ x in Ioc 0 1, (continuousNymanResidual c N x)^2`;
(3) evaluating the Mellin residual quotient at any zero `ζ(s₀) = 0` (`s₀ ≠ 0`) yields `1 / s₀ ≠ 0`;
(4) any off-line zero `σ₀ > 1 / 2` imposes the uniform Cauchy–Schwarz barrier
`(2 * σ₀ - 1) / normSq_s₀ ≤ E_L2_sq`. -/
theorem planar_mellin_dual_contradiction_capstone {c : ℕ → ℝ} {N : ℕ} (hN : 2 ≤ N)
    (hc : IsDirichletAnchored c N) :
    (∀ x ∈ Set.Ioc (1 / 2 : ℝ) 1, continuousNymanResidual c N x = 0) ∧
    (∀ (M : ℕ) (S : Finset ℕ), S ⊆ Finset.Icc (N + 1) M → (∀ p ∈ S, Nat.Prime p) →
      ∑ p ∈ S, (1 : ℝ) / (2 * (p : ℝ) ^ 2) ≤ harmonicCellL2PartialSum c N M) ∧
    (0 < ∫ x in Set.Ioc (0 : ℝ) 1, (continuousNymanResidual c N x) ^ 2) ∧
    (∀ (dirichletPolyVal : ℂ) {s₀ : ℂ}, s₀ ≠ 0 →
      mellinResidualQuotient 0 dirichletPolyVal s₀ = 1 / s₀ ∧
        mellinResidualQuotient 0 dirichletPolyVal s₀ ≠ 0) ∧
    (∀ {σ₀ normSq_s₀ E_L2_sq mellinValSq : ℝ},
      (1 / 2 : ℝ) < σ₀ → 0 < normSq_s₀ →
      mellinValSq ≤ E_L2_sq * offlineKernelL2NormSq σ₀ →
      1 / normSq_s₀ ≤ mellinValSq →
      offlineEnergyFloor σ₀ normSq_s₀ ≤ E_L2_sq) := by
  refine ⟨fun x hx => continuousNymanResidual_eq_zero_on_top_half hN hc hx.1 hx.2, ?_, ?_, ?_, ?_⟩
  · intro M S hS hprime
    exact harmonicCellL2PartialSum_ge_sum_primes hN hc hS hprime
  · exact continuousNymanResidual_sq_integral_pos c (by omega : 1 ≤ N)
  · intro dirichletPolyVal s₀ hs₀
    exact ⟨mellinResidualQuotient_at_zeta_zero dirichletPolyVal s₀,
      mellinResidualQuotient_ne_zero_at_zeta_zero dirichletPolyVal hs₀⟩
  · intro σ₀ normSq_s₀ E_L2_sq mellinValSq hσ hs hcs hzero
    exact l2NormSq_ge_offlineEnergyFloor_of_cauchy_schwarz hσ hs hcs hzero
