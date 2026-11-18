/-
Copyright (c) 2026 Qamar Munawer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qamar Munawer
-/
module

public import RiemannBlueprint.UpstreamPRs.UpstreamPR_8S_MultiPrimeL2Superposition

/-!
# Palindromic Double-Cone L² Quadrature Folding and Counter-Rotating Signed Flux Identity

Pairing each forward harmonic cell `m` with its palindromic reflection `L - 1 - m` across a
common multiple period `L` (`1..N`) models two counter-rotating cones joined across the `x = 1/2`
mirror. Under `D1 c N = 0` and `D0 c N = 2`, palindromic sign reversal `A_c(L - 1 - m) = -A_c(m)`
forces squared-amplitude invariance and turns relative signed differences into constructive energy
doubling:

* `doubleConeSymmetricWidth`, `doubleConeAsymmetricWidth`, `counterRotatingCellFlux`,
  `weightedCounterRotatingFlux`: symmetric/antisymmetric width kernels and signed cell fluxes.
* `modularCellResidual_sq_palindromic_eq`, `counterRotatingCellFlux_eq_two_mul_sq`,
  `sum_Icc_counterRotatingCellFlux_eq`: `(A_c(L - 1 - m))^2 = (A_c(m))^2` and unweighted flux
  doubling `2 * (A_c(m))^2`.
* `modularCellResidual_one_eq_zero`, `modularCellResidual_period_sub_two_eq_zero`: exact
  double-cone annihilation at both endpoints `m = 1` and `m = L - 2` under `IsDirichletAnchored`.
* `weightedCounterRotatingFlux_eq_two_mul_doubleCone`,
  `harmonicCellL2PartialSum_period_sub_two_eq_doubleCone`,
  `sum_Icc_weightedCounterRotatingFlux_eq_two_mul_l2`: exact L² quadrature folding onto
  `doubleConeSymmetricWidth` and weighted flux conservation `2 * harmonicCellL2PartialSum`.
-/

@[expose] public section

open scoped BigOperators

/-- Symmetric double-cone width pairing cell `m` with its mirror `L - 1 - m`. -/
noncomputable def doubleConeSymmetricWidth (L m : ℕ) : ℝ :=
  (harmonicCellWidth m + harmonicCellWidth (L - 1 - m)) / 2

/-- Antisymmetric double-cone width difference pairing cell `m` with its mirror `L - 1 - m`. -/
noncomputable def doubleConeAsymmetricWidth (L m : ℕ) : ℝ :=
  (harmonicCellWidth m - harmonicCellWidth (L - 1 - m)) / 2

/-- Unweighted counter-rotating signed flux `A_c(m) * (A_c(m) - A_c(L - 1 - m))`. -/
noncomputable def counterRotatingCellFlux (c : ℕ → ℝ) (N L m : ℕ) : ℝ :=
  modularCellResidual c N m *
    (modularCellResidual c N m - modularCellResidual c N (L - 1 - m))

/-- Width-weighted counter-rotating signed flux between cells `m` and `L - 1 - m`. -/
noncomputable def weightedCounterRotatingFlux (c : ℕ → ℝ) (N L m : ℕ) : ℝ :=
  modularCellResidual c N m *
    (modularCellResidual c N m * harmonicCellWidth m -
      modularCellResidual c N (L - 1 - m) * harmonicCellWidth (L - 1 - m))

/-- **Palindromic Squared-Amplitude Invariance**: on `D1 c N = 0` and `D0 c N = 2`, the reflected
cell `L - 1 - m` carries the exact same squared amplitude `(A_c(L - 1 - m))^2 = (A_c(m))^2`. -/
theorem modularCellResidual_sq_palindromic_eq (c : ℕ → ℝ) (N L m : ℕ) (hD1 : D1 c N = 0)
    (hD0 : D0 c N = 2) (hL : ∀ k ∈ Finset.Icc 1 N, k ∣ L) (hm : m < L) :
    (modularCellResidual c N (L - 1 - m)) ^ 2 = (modularCellResidual c N m) ^ 2 := by
  rw [modularCellResidual_palindromic_neg c N L m hD1 hD0 hL hm, neg_sq]

/-- **Counter-Rotating Flux Reinforcement**: opposite signs turn subtraction into addition,
yielding `counterRotatingCellFlux c N L m = 2 * (modularCellResidual c N m)^2 ≥ 0`. -/
theorem counterRotatingCellFlux_eq_two_mul_sq (c : ℕ → ℝ) (N L m : ℕ) (hD1 : D1 c N = 0)
    (hD0 : D0 c N = 2) (hL : ∀ k ∈ Finset.Icc 1 N, k ∣ L) (hm : m < L) :
    counterRotatingCellFlux c N L m = 2 * (modularCellResidual c N m) ^ 2 ∧
      0 ≤ counterRotatingCellFlux c N L m := by
  unfold counterRotatingCellFlux
  rw [modularCellResidual_palindromic_neg c N L m hD1 hD0 hL hm]
  have hsq : modularCellResidual c N m *
      (modularCellResidual c N m - -modularCellResidual c N m) =
      2 * (modularCellResidual c N m) ^ 2 := by ring
  rw [hsq]
  exact ⟨rfl, by positivity⟩

/-- Summing `counterRotatingCellFlux` across the interior period `Icc 1 (L - 2)` equals twice
the interior squared residual sum. -/
theorem sum_Icc_counterRotatingCellFlux_eq (c : ℕ → ℝ) (N L : ℕ) (hD1 : D1 c N = 0)
    (hD0 : D0 c N = 2) (hL : ∀ k ∈ Finset.Icc 1 N, k ∣ L) :
    ∑ m ∈ Finset.Icc 1 (L - 2), counterRotatingCellFlux c N L m =
      2 * ∑ m ∈ Finset.Icc 1 (L - 2), (modularCellResidual c N m) ^ 2 := by
  have hcongr : ∀ m ∈ Finset.Icc 1 (L - 2),
      counterRotatingCellFlux c N L m = 2 * (modularCellResidual c N m) ^ 2 := fun m hm => by
    have hm_mem := Finset.mem_Icc.mp hm
    exact (counterRotatingCellFlux_eq_two_mul_sq c N L m hD1 hD0 hL (by omega)).1
  rw [Finset.sum_congr rfl hcongr, ← Finset.mul_sum]

/-- Under `IsDirichletAnchored c N` (`2 ≤ N`), the wide-mouth modular cell `m = 1` vanishes. -/
theorem modularCellResidual_one_eq_zero {c : ℕ → ℝ} {N : ℕ} (hN : 2 ≤ N)
    (hc : IsDirichletAnchored c N) : modularCellResidual c N 1 = 0 := by
  rw [← discreteCellResidual_eq_modularCellResidual_of_D1_eq_zero c N 1 hc.1,
    discreteCellResidual_one_eq c (by omega : 1 ≤ N), hc.2.2]
  ring

/-- Under `IsDirichletAnchored c N` (`2 ≤ N`) and `3 ≤ L` (`1..N ∣ L`), the narrow-tip mirror
cell `m = L - 2` vanishes identically. -/
theorem modularCellResidual_period_sub_two_eq_zero {c : ℕ → ℝ} {N L : ℕ} (hN : 2 ≤ N)
    (hL3 : 3 ≤ L) (hc : IsDirichletAnchored c N) (hL : ∀ k ∈ Finset.Icc 1 N, k ∣ L) :
    modularCellResidual c N (L - 2) = 0 := by
  have hsub : L - 2 = L - 1 - 1 := by omega
  rw [hsub, modularCellResidual_palindromic_neg c N L 1 hc.1 hc.2.1 hL (by omega),
    modularCellResidual_one_eq_zero hN hc, neg_zero]

/-- **Pointwise Double-Cone Weighted Flux Identity**: for `m < L` on `D1 = 0, D0 = 2`,
`weightedCounterRotatingFlux` equals both the sum of the two reflected cell L² energies and
`2 * (modularCellResidual c N m)^2 * doubleConeSymmetricWidth L m`. -/
theorem weightedCounterRotatingFlux_eq_two_mul_doubleCone (c : ℕ → ℝ) (N L m : ℕ)
    (hD1 : D1 c N = 0) (hD0 : D0 c N = 2) (hL : ∀ k ∈ Finset.Icc 1 N, k ∣ L) (hm : m < L) :
    weightedCounterRotatingFlux c N L m =
      (modularCellResidual c N m) ^ 2 * harmonicCellWidth m +
        (modularCellResidual c N (L - 1 - m)) ^ 2 * harmonicCellWidth (L - 1 - m) ∧
    (modularCellResidual c N m) ^ 2 * harmonicCellWidth m +
        (modularCellResidual c N (L - 1 - m)) ^ 2 * harmonicCellWidth (L - 1 - m) =
      2 * (modularCellResidual c N m) ^ 2 * doubleConeSymmetricWidth L m := by
  have hneg := modularCellResidual_palindromic_neg c N L m hD1 hD0 hL hm
  have hsq := modularCellResidual_sq_palindromic_eq c N L m hD1 hD0 hL hm
  constructor
  · unfold weightedCounterRotatingFlux
    rw [hneg]
    ring
  · unfold doubleConeSymmetricWidth
    rw [hsq]
    ring

private lemma harmonicCellL2PartialSum_eq_modular_sum (c : ℕ → ℝ) (N M : ℕ)
    (hD1 : D1 c N = 0) :
    harmonicCellL2PartialSum c N M =
      ∑ m ∈ Finset.Icc 1 M, (modularCellResidual c N m) ^ 2 * harmonicCellWidth m := by
  unfold harmonicCellL2PartialSum
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [discreteCellResidual_eq_modularCellResidual_of_D1_eq_zero c N m hD1]

private lemma sum_Icc_reflected_modular_l2 (c : ℕ → ℝ) (N L : ℕ) (hD1 : D1 c N = 0)
    (hD0 : D0 c N = 2) (hL : ∀ k ∈ Finset.Icc 1 N, k ∣ L) :
    ∑ m ∈ Finset.Icc 1 (L - 2),
        (modularCellResidual c N m) ^ 2 * harmonicCellWidth (L - 1 - m) =
      harmonicCellL2PartialSum c N (L - 2) := by
  have hcongr : ∀ m ∈ Finset.Icc 1 (L - 2),
      (modularCellResidual c N m) ^ 2 * harmonicCellWidth (L - 1 - m) =
        (modularCellResidual c N (L - 1 - m)) ^ 2 * harmonicCellWidth (L - 1 - m) := by
    intro m hm
    have hm_mem := Finset.mem_Icc.mp hm
    rw [modularCellResidual_sq_palindromic_eq c N L m hD1 hD0 hL (by omega)]
  have hbij : ∑ m ∈ Finset.Icc 1 (L - 2),
      (modularCellResidual c N (L - 1 - m)) ^ 2 * harmonicCellWidth (L - 1 - m) =
      ∑ m ∈ Finset.Icc 1 (L - 2), (modularCellResidual c N m) ^ 2 * harmonicCellWidth m :=
    Finset.sum_bij (fun m _ => L - 1 - m)
      (fun _ hm => by
        have ⟨hm1, hm2⟩ := Finset.mem_Icc.mp hm
        exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
      (fun _ ha _ hb hab => by
        have ⟨ha1, ha2⟩ := Finset.mem_Icc.mp ha
        have ⟨hb1, hb2⟩ := Finset.mem_Icc.mp hb
        omega)
      (fun b hb => by
        have ⟨hb1, hb2⟩ := Finset.mem_Icc.mp hb
        exact ⟨L - 1 - b, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, by omega⟩)
      (fun _ _ => rfl)
  rw [Finset.sum_congr rfl hcongr, hbij, ← harmonicCellL2PartialSum_eq_modular_sum c N (L - 2) hD1]

/-- **Palindromic Double-Cone L² Quadrature Folding Identity**: across `[1, L - 2]`,
`harmonicCellL2PartialSum c N (L - 2)` folds onto the symmetric double-cone width kernel
`doubleConeSymmetricWidth L m`. -/
theorem harmonicCellL2PartialSum_period_sub_two_eq_doubleCone (c : ℕ → ℝ) (N L : ℕ)
    (hD1 : D1 c N = 0) (hD0 : D0 c N = 2) (hL : ∀ k ∈ Finset.Icc 1 N, k ∣ L) :
    harmonicCellL2PartialSum c N (L - 2) =
      ∑ m ∈ Finset.Icc 1 (L - 2),
        (modularCellResidual c N m) ^ 2 * doubleConeSymmetricWidth L m := by
  have h1 := harmonicCellL2PartialSum_eq_modular_sum c N (L - 2) hD1
  have h2 := sum_Icc_reflected_modular_l2 c N L hD1 hD0 hL
  have hadd : ∑ m ∈ Finset.Icc 1 (L - 2),
      2 * ((modularCellResidual c N m) ^ 2 * doubleConeSymmetricWidth L m) =
      (∑ m ∈ Finset.Icc 1 (L - 2), (modularCellResidual c N m) ^ 2 * harmonicCellWidth m) +
        (∑ m ∈ Finset.Icc 1 (L - 2),
          (modularCellResidual c N m) ^ 2 * harmonicCellWidth (L - 1 - m)) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun m _ => ?_
    unfold doubleConeSymmetricWidth
    ring
  rw [← Finset.mul_sum, h2, ← h1] at hadd
  linarith

/-- **Counter-Rotating Weighted Flux Identity**: summing `weightedCounterRotatingFlux c N L m`
over `Icc 1 (L - 2)` equals `2 * harmonicCellL2PartialSum c N (L - 2)`. -/
theorem sum_Icc_weightedCounterRotatingFlux_eq_two_mul_l2 (c : ℕ → ℝ) (N L : ℕ)
    (hD1 : D1 c N = 0) (hD0 : D0 c N = 2) (hL : ∀ k ∈ Finset.Icc 1 N, k ∣ L) :
    ∑ m ∈ Finset.Icc 1 (L - 2), weightedCounterRotatingFlux c N L m =
      2 * harmonicCellL2PartialSum c N (L - 2) := by
  have hcongr : ∀ m ∈ Finset.Icc 1 (L - 2),
      weightedCounterRotatingFlux c N L m =
        2 * ((modularCellResidual c N m) ^ 2 * doubleConeSymmetricWidth L m) := fun m hm => by
    have hm_mem := Finset.mem_Icc.mp hm
    have hw := weightedCounterRotatingFlux_eq_two_mul_doubleCone c N L m hD1 hD0 hL (by omega)
    linarith [hw.1, hw.2]
  rw [Finset.sum_congr rfl hcongr, ← Finset.mul_sum,
    ← harmonicCellL2PartialSum_period_sub_two_eq_doubleCone c N L hD1 hD0 hL]
