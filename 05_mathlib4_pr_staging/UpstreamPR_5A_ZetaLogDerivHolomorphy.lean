/-
Copyright (c) 2026 Qamar Munawer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qamar Munawer
-/
module

public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
public import Mathlib.NumberTheory.LSeries.Nonvanishing
public import Mathlib.NumberTheory.LSeries.RiemannZeta
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-!
# Reciprocal Zeta Holomorphy, Logarithmic Derivative Regularity, and Critical-Strip Equivalence

This module develops local analyticity of `(riemannZeta ·)⁻¹` and the logarithmic derivative
`-deriv riemannZeta / riemannZeta` away from `s = 1` and zeros of `riemannZeta`, together with
functional-equation zero reflection and the bidirectional holomorphy characterization of RH:

* `analyticAt_inv_riemannZeta_of_ne_zero`: `AnalyticAt ℂ (fun z => (riemannZeta z)⁻¹) s`
  whenever `s ≠ 1` and `riemannZeta s ≠ 0`.
* `analyticAt_neg_deriv_div_riemannZeta_of_ne_zero`: local analyticity of `-ζ'(s) / ζ(s)`.
* `differentiableOn_logDeriv_riemannZeta_of_riemannHypothesis`: holomorphy of `ζ' / ζ` on
  `{s : ℂ | 1 / 2 < s.re ∧ s ≠ 1}` under `RiemannHypothesis`.
* `riemannZeta_zero_reflection_of_re_lt_half`: functional-equation zero reflection across
  `Re(s) = 1 / 2`.
* `riemannHypothesis_iff_analyticAt_inv_riemannZeta`: equivalence between `RiemannHypothesis`
  and non-vanishing / analyticity of `(riemannZeta ·)⁻¹` on `{s : ℂ | 1 / 2 < s.re ∧ s ≠ 1}`.
-/

@[expose] public section

open scoped Topology
open Complex Filter Set

private lemma analyticAt_riemannZeta_of_ne_one {s : ℂ} (hs1 : s ≠ 1) :
    AnalyticAt ℂ riemannZeta s := by
  have hd : DifferentiableOn ℂ riemannZeta {z : ℂ | z ≠ 1} :=
    fun z hz => (differentiableAt_riemannZeta hz).differentiableWithinAt
  exact hd.analyticAt (isOpen_ne.mem_nhds hs1)

private lemma riemannZeta_ne_zero_of_rh (hRH : _root_.RiemannHypothesis) {s : ℂ}
    (hs : 1 / 2 < s.re) (hs1 : s ≠ 1) : riemannZeta s ≠ 0 := by
  intro hz
  have hnt : ¬∃ n : ℕ, s = -2 * (n + 1) := fun ⟨n, hn⟩ => by
    have := congr_arg Complex.re hn
    simp at this
    linarith [Nat.cast_nonneg (α := ℝ) n]
  have hhalf := hRH s hz hnt hs1
  linarith

/-- If `s ≠ 1` and `riemannZeta s ≠ 0`, then `z ↦ (riemannZeta z)⁻¹` is analytic at `s`. -/
theorem analyticAt_inv_riemannZeta_of_ne_zero {s : ℂ} (hs1 : s ≠ 1) (hz : riemannZeta s ≠ 0) :
    AnalyticAt ℂ (fun z => (riemannZeta z)⁻¹) s :=
  (analyticAt_riemannZeta_of_ne_one hs1).inv hz

/-- If `s ≠ 1` and `riemannZeta s ≠ 0`, then `z ↦ -deriv riemannZeta z / riemannZeta z` is
analytic at `s`. -/
theorem analyticAt_neg_deriv_div_riemannZeta_of_ne_zero {s : ℂ} (hs1 : s ≠ 1)
    (hz : riemannZeta s ≠ 0) :
    AnalyticAt ℂ (fun z => -deriv riemannZeta z / riemannZeta z) s := by
  have hζ := analyticAt_riemannZeta_of_ne_one hs1
  exact hζ.deriv.neg.div hζ hz

/-- Under `RiemannHypothesis`, the logarithmic derivative `s ↦ ζ'(s) / ζ(s)` is complex
differentiable throughout `{s : ℂ | 1 / 2 < s.re ∧ s ≠ 1}`. -/
theorem differentiableOn_logDeriv_riemannZeta_of_riemannHypothesis
    (hRH : _root_.RiemannHypothesis) :
    DifferentiableOn ℂ (fun s => deriv riemannZeta s / riemannZeta s)
      {s : ℂ | 1 / 2 < s.re ∧ s ≠ 1} := by
  let U : Set ℂ := {s : ℂ | 1 / 2 < s.re ∧ s ≠ 1}
  have hU_open : IsOpen U := (isOpen_lt continuous_const Complex.continuous_re).inter isOpen_ne
  have h_diff : DifferentiableOn ℂ riemannZeta U :=
    fun s hs => (differentiableAt_riemannZeta hs.2).differentiableWithinAt
  exact (h_diff.deriv hU_open).div h_diff fun s hs => riemannZeta_ne_zero_of_rh hRH hs.1 hs.2

/-- Reflection of non-trivial zeros of `riemannZeta` across `Re(s) = 1 / 2` via
`riemannZeta_one_sub`. -/
theorem riemannZeta_zero_reflection_of_re_lt_half {s : ℂ} (hz : riemannZeta s = 0)
    (h_not_triv : ¬∃ n : ℕ, s = -2 * (n + 1)) (h_not_one : s ≠ 1) (hs_lt : s.re < 1 / 2) :
    riemannZeta (1 - s) = 0 ∧ 1 / 2 < (1 - s).re := by
  refine ⟨?_, by rw [Complex.sub_re, Complex.one_re]; linarith⟩
  have h_not_neg_nat : ∀ n : ℕ, s ≠ -(n : ℂ) := by
    intro n hn
    subst hn
    rcases n with _ | n
    · simp [riemannZeta_zero] at hz
    · rcases Nat.even_or_odd (n + 1) with ⟨m, hm⟩ | ⟨m, hm⟩
      · refine h_not_triv ⟨m - 1, ?_⟩
        have h1 : n + 1 = 2 * ((m - 1) + 1) := by omega
        push_cast [h1]
        ring
      · let w : ℂ := ((2 * m + 2 : ℕ) : ℂ)
        have hw_not_neg : ∀ j : ℕ, w ≠ -(j : ℂ) := fun j h_eq => by
          have := congr_arg Complex.re h_eq
          simp [w] at this
          linarith
        have hw_ne_one : w ≠ 1 := fun h_eq => by
          have := congr_arg Complex.re h_eq
          simp [w] at this
          linarith
        have h_fe := riemannZeta_one_sub hw_not_neg hw_ne_one
        have h_1mw : 1 - w = -(↑(n + 1) : ℂ) := by dsimp [w]; push_cast [hm]; ring
        rw [h_1mw, hz] at h_fe
        have h_cpow_ne : (2 * (Real.pi : ℂ)) ^ (-w) ≠ 0 := by
          rw [Complex.cpow_ne_zero_iff]
          left
          exact_mod_cast (mul_ne_zero two_ne_zero Real.pi_ne_zero)
        have h_cos_ne : Complex.cos ((Real.pi : ℂ) * w / 2) ≠ 0 := by
          intro hcos
          rw [Complex.cos_eq_zero_iff] at hcos
          rcases hcos with ⟨k, hk⟩
          have hw2 : (Real.pi : ℂ) * w / 2 =
              ((((m + 1 : ℕ) : ℝ) * Real.pi : ℝ) : ℂ) := by dsimp [w]; push_cast; ring
          have hk2 : (2 * (k : ℂ) + 1) * (Real.pi : ℂ) / 2 =
              ((((2 * k + 1 : ℤ) / 2 : ℝ) * Real.pi : ℝ) : ℂ) := by push_cast; ring
          rw [hw2, hk2] at hk
          have hdiv : ((m + 1 : ℕ) : ℝ) = ((2 * k + 1 : ℤ) / 2 : ℝ) :=
            mul_right_cancel₀ Real.pi_ne_zero (Complex.ofReal_injective hk)
          have hdiv2 : (2 : ℝ) * ((m + 1 : ℕ) : ℝ) = ((2 * k + 1 : ℤ) : ℝ) := by linarith
          have hint : (2 * ((m : ℤ) + 1)) = 2 * k + 1 := by exact_mod_cast hdiv2
          omega
        have h_rhs_ne : 2 * (2 * (Real.pi : ℂ)) ^ (-w) * Complex.Gamma w *
            Complex.cos ((Real.pi : ℂ) * w / 2) * riemannZeta w ≠ 0 :=
          mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) h_cpow_ne)
            (Complex.Gamma_ne_zero hw_not_neg)) h_cos_ne)
            (riemannZeta_ne_zero_of_one_le_re (by dsimp [w]; norm_cast; omega))
        exact h_rhs_ne h_fe.symm
  rw [riemannZeta_one_sub h_not_neg_nat h_not_one, hz, mul_zero]

/-- `_root_.RiemannHypothesis` holds if and only if `(riemannZeta ·)⁻¹` is analytic and
`riemannZeta s ≠ 0` at every point `s : ℂ` with `1 / 2 < s.re` and `s ≠ 1`. -/
theorem riemannHypothesis_iff_analyticAt_inv_riemannZeta :
    _root_.RiemannHypothesis ↔
      ∀ s : ℂ, 1 / 2 < s.re → s ≠ 1 →
        AnalyticAt ℂ (fun z => (riemannZeta z)⁻¹) s ∧ riemannZeta s ≠ 0 := by
  constructor
  · intro hRH s hs hs1
    have hz := riemannZeta_ne_zero_of_rh hRH hs hs1
    exact ⟨analyticAt_inv_riemannZeta_of_ne_zero hs1 hz, hz⟩
  · intro h s hz h_not_triv h_not_one
    by_contra h_ne
    rcases lt_or_gt_of_ne h_ne with hlt | hgt
    · have hz_refl := riemannZeta_zero_reflection_of_re_lt_half hz h_not_triv h_not_one hlt
      have h1ms_ne : 1 - s ≠ 1 := fun h1 => by
        have : s = 0 := by linear_combination -h1
        subst this
        simp [riemannZeta_zero] at hz
      exact (h (1 - s) hz_refl.2 h1ms_ne).2 hz_refl.1
    · exact (h s hgt h_not_one).2 hz
