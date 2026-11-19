/-
Copyright (c) 2026 Qamar Munawer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qamar Munawer
-/
module

public import RiemannBlueprint.Modules.PrimeCellL2EnergyFloor

/-!
# Mellin Zero-Obstruction and Off-Line Cauchy–Schwarz L² Energy Floor

This module formalizes the Mellin-space side of the finite-truncation obstruction across the
`Re(s) = 1 / 2` mirror and derives the uniform off-line Cauchy–Schwarz energy barrier:

* `mellinResidualQuotient`, `mellinResidualQuotient_at_zeta_zero`,
  `mellinResidualQuotient_ne_zero_at_zeta_zero`, `not_mellinResidualQuotient_eq_zero_of_zeta_zero`:
  evaluating `(1 - ζ(s) * D_N(s)) / s` at any zeta zero `s₀ ≠ 0` leaves `1 / s₀ ≠ 0`, proving
  finite closure (`M[E_N](s₀) = 0`) is impossible.
* `offlineKernelL2NormSq`, `offlineEnergyFloor`, `offlineKernelL2NormSq_pos`,
  `offlineEnergyFloor_pos`, `integral_rpow_eq_offlineKernelL2NormSq`: for `σ₀ > 1 / 2`, the test
  kernel `x^(2 * σ₀ - 2)` has L²(0, 1) norm squared `1 / (2 * σ₀ - 1) > 0`.
* `l2NormSq_ge_offlineEnergyFloor_of_cauchy_schwarz` and
  `no_offline_zero_of_l2_arbitrarily_small`: uniform `N`-independent energy barrier
  `(2 * σ₀ - 1) / ‖s₀‖² ≤ E_L2_sq` and its `ε → 0` contrapositive excluding off-line zeros under
  L² closure.
-/

@[expose] public section

/-- Algebraic Mellin quotient `(1 - zetaVal * dirichletPolyVal) / s` of the finite Nyman–Beurling
residual on `ℂ`. -/
noncomputable def mellinResidualQuotient (zetaVal dirichletPolyVal s : ℂ) : ℂ :=
  (1 - zetaVal * dirichletPolyVal) / s

/-- At any zeta zero (`zetaVal = 0`), a finite Dirichlet polynomial contributes `0`, leaving
`mellinResidualQuotient 0 dirichletPolyVal s₀ = 1 / s₀`. -/
theorem mellinResidualQuotient_at_zeta_zero (dirichletPolyVal s₀ : ℂ) :
    mellinResidualQuotient 0 dirichletPolyVal s₀ = 1 / s₀ := by
  simp [mellinResidualQuotient]

/-- For every `s₀ ≠ 0` and any finite Dirichlet polynomial evaluation `dirichletPolyVal`, the
Mellin residual quotient at `zetaVal = 0` is strictly non-zero. -/
theorem mellinResidualQuotient_ne_zero_at_zeta_zero (dirichletPolyVal : ℂ) {s₀ : ℂ}
    (hs₀ : s₀ ≠ 0) : mellinResidualQuotient 0 dirichletPolyVal s₀ ≠ 0 := by
  rw [mellinResidualQuotient_at_zeta_zero]
  exact one_div_ne_zero hs₀

/-- Squared modulus `‖mellinResidualQuotient 0 dirichletPolyVal s₀‖^2 = 1 / ‖s₀‖^2 > 0` for
`s₀ ≠ 0`. -/
theorem mellinResidualQuotient_normSq_at_zeta_zero (dirichletPolyVal : ℂ) {s₀ : ℂ}
    (hs₀ : s₀ ≠ 0) :
    0 < ‖mellinResidualQuotient 0 dirichletPolyVal s₀‖ ^ 2 ∧
      ‖mellinResidualQuotient 0 dirichletPolyVal s₀‖ ^ 2 = 1 / ‖s₀‖ ^ 2 := by
  rw [mellinResidualQuotient_at_zeta_zero, norm_div, norm_one, div_pow, one_pow]
  have hnorm : 0 < ‖s₀‖ := norm_pos_iff.mpr hs₀
  exact ⟨by positivity, rfl⟩

/-- **Mellin Finite-Closure Contradiction**: if `E_N = 0` a.e. forced
`mellinResidualQuotient 0 dirichletPolyVal s₀ = 0` at a zeta zero `s₀ ≠ 0`, `1 / s₀ ≠ 0` gives an
immediate contradiction. -/
theorem not_mellinResidualQuotient_eq_zero_of_zeta_zero (dirichletPolyVal : ℂ) {s₀ : ℂ}
    (hs₀ : s₀ ≠ 0) : ¬mellinResidualQuotient 0 dirichletPolyVal s₀ = 0 :=
  mellinResidualQuotient_ne_zero_at_zeta_zero dirichletPolyVal hs₀

/-- Exact L²(0, 1) norm squared `∫_0^1 x^(2 * σ₀ - 2) dx = 1 / (2 * σ₀ - 1)` of the Mellin test
kernel `x^(s₀ - 1)` for `σ₀ > 1 / 2`. -/
noncomputable def offlineKernelL2NormSq (σ₀ : ℝ) : ℝ :=
  1 / (2 * σ₀ - 1)

/-- Uniform `N`-independent Cauchy–Schwarz energy barrier `(2 * σ₀ - 1) / normSq_s₀` enforced by
an off-line zero at abscissa `σ₀ > 1 / 2`. -/
noncomputable def offlineEnergyFloor (σ₀ normSq_s₀ : ℝ) : ℝ :=
  (2 * σ₀ - 1) / normSq_s₀

/-- Positivity of `offlineKernelL2NormSq σ₀` for every off-line abscissa `σ₀ > 1 / 2`. -/
theorem offlineKernelL2NormSq_pos {σ₀ : ℝ} (hσ : (1 / 2 : ℝ) < σ₀) :
    0 < offlineKernelL2NormSq σ₀ := by
  have hden : 0 < 2 * σ₀ - 1 := by linarith
  unfold offlineKernelL2NormSq
  positivity

/-- Positivity of `offlineEnergyFloor σ₀ normSq_s₀` whenever `σ₀ > 1 / 2` and `normSq_s₀ > 0`. -/
theorem offlineEnergyFloor_pos {σ₀ normSq_s₀ : ℝ} (hσ : (1 / 2 : ℝ) < σ₀)
    (hs : 0 < normSq_s₀) : 0 < offlineEnergyFloor σ₀ normSq_s₀ := by
  have hnum : 0 < 2 * σ₀ - 1 := by linarith
  unfold offlineEnergyFloor
  exact div_pos hnum hs

/-- Analytic evaluation `∫ x in (0 : ℝ)..1, x ^ (2 * σ₀ - 2) = offlineKernelL2NormSq σ₀` for
every off-line abscissa `σ₀ > 1 / 2`. -/
theorem integral_rpow_eq_offlineKernelL2NormSq {σ₀ : ℝ} (hσ : (1 / 2 : ℝ) < σ₀) :
    ∫ x in (0 : ℝ)..1, x ^ (2 * σ₀ - 2) = offlineKernelL2NormSq σ₀ := by
  have hexp : (-1 : ℝ) < 2 * σ₀ - 2 := by linarith
  have hne : 2 * σ₀ - 2 + 1 ≠ 0 := by linarith
  rw [integral_rpow (Or.inl hexp), Real.one_rpow,
    Real.zero_rpow hne, sub_zero]
  unfold offlineKernelL2NormSq
  ring

/-- **Uniform Off-Line Cauchy–Schwarz Energy Barrier**: any residual L² energy `E_L2_sq` and
Mellin pairing `mellinValSq` satisfying Cauchy–Schwarz `mellinValSq ≤ E_L2_sq *
offlineKernelL2NormSq σ₀` and the zero-evaluation bound `1 / normSq_s₀ ≤ mellinValSq` forces
`offlineEnergyFloor σ₀ normSq_s₀ ≤ E_L2_sq`. -/
theorem l2NormSq_ge_offlineEnergyFloor_of_cauchy_schwarz
    {σ₀ normSq_s₀ E_L2_sq mellinValSq : ℝ}
    (hσ : (1 / 2 : ℝ) < σ₀) (_hs : 0 < normSq_s₀)
    (hcs : mellinValSq ≤ E_L2_sq * offlineKernelL2NormSq σ₀)
    (hzero : 1 / normSq_s₀ ≤ mellinValSq) :
    offlineEnergyFloor σ₀ normSq_s₀ ≤ E_L2_sq := by
  have hden : 0 < 2 * σ₀ - 1 := by linarith
  have htrans : 1 / normSq_s₀ ≤ E_L2_sq * (1 / (2 * σ₀ - 1)) := hzero.trans hcs
  have hmul : (1 / normSq_s₀) * (2 * σ₀ - 1) ≤ (E_L2_sq * (1 / (2 * σ₀ - 1))) * (2 * σ₀ - 1) :=
    mul_le_mul_of_nonneg_right htrans hden.le
  have hleft : (1 / normSq_s₀) * (2 * σ₀ - 1) = offlineEnergyFloor σ₀ normSq_s₀ := by
    unfold offlineEnergyFloor; ring
  have hright : (E_L2_sq * (1 / (2 * σ₀ - 1))) * (2 * σ₀ - 1) = E_L2_sq := by
    field_simp [hden.ne']
  linarith

/-- **Asymptotic Contrapositive (Nyman L² Closure Excludes Off-Line Zeros)**: if `E_L2_sq N`
can be made smaller than every positive `ε > 0`, no off-line zero `(σ₀ > 1 / 2, normSq_s₀ > 0)`
can satisfy the uniform Cauchy–Schwarz zero-obstruction bounds for all `N`. -/
theorem no_offline_zero_of_l2_arbitrarily_small
    (E_L2_sq mellinValSq : ℕ → ℝ)
    (hclose : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, E_L2_sq N < ε)
    {σ₀ normSq_s₀ : ℝ} (hσ : (1 / 2 : ℝ) < σ₀) (hs : 0 < normSq_s₀)
    (hcs : ∀ N : ℕ, mellinValSq N ≤ E_L2_sq N * offlineKernelL2NormSq σ₀)
    (hzero : ∀ N : ℕ, 1 / normSq_s₀ ≤ mellinValSq N) : False := by
  obtain ⟨N, hlt⟩ := hclose (offlineEnergyFloor σ₀ normSq_s₀) (offlineEnergyFloor_pos hσ hs)
  have hge := l2NormSq_ge_offlineEnergyFloor_of_cauchy_schwarz hσ hs (hcs N) (hzero N)
  linarith
