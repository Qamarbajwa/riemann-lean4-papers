/-
Copyright (c) 2026 Qamar Munawer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qamar Munawer
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.PSeriesComplex
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
public import Mathlib.NumberTheory.LSeries.Nonvanishing
public import Mathlib.NumberTheory.LSeries.RiemannZeta
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-!
# Completed Zeta Derivative Antisymmetry, Prime Equipartition, and Zero Dichotomy

This module formalizes unconditional symmetry properties of `completedRiemannZeta` and
the additive prime-composite partition of `riemannZeta` on `Re(s) > 1`:

* `completedRiemannZeta_deriv_one_sub`: derivative antisymmetry `Λ'(1 - s) = -Λ'(s)`
  for `s ≠ 0, 1`.
* `completedRiemannZeta_deriv_at_half`: vanishing of `Λ'(1/2) = 0` at the critical center.
* `completedRiemannZeta_deriv_critical_line_antisymm`: `Λ'(1/2 - i*t) = -Λ'(1/2 + i*t)`.
* `PrimeZeta`, `CompositeZeta`, `IsEquipartitionFulcrum`: additive partition `ζ = 1 + P + ζ_C`
  and the 50/50 equipartition identity `ζ(s) = 1 + 2 * P(s)` whenever `P(s) = ζ_C(s)`.
* `zero_reflection_dichotomy`: every non-trivial zero either has `Re(s) = 1/2` or pairs with a
  zero strictly inside `Re(w) > 1/2`.
-/

@[expose] public section

open Complex Filter

/-- Critical centerline predicate `Re(s) = 1 / 2`. -/
def IsOnCriticalLine (s : ℂ) : Prop :=
  s.re = 1 / 2

/-- Reflection `s ↦ 1 - s` preserves `IsOnCriticalLine`. -/
theorem reflection_preserves_critical_line (s : ℂ) :
    IsOnCriticalLine (1 - s) ↔ IsOnCriticalLine s := by
  unfold IsOnCriticalLine
  rw [Complex.sub_re, Complex.one_re]
  constructor <;> intro h <;> linarith

/-- Prime zeta series `P(s) = ∑' p, [Nat.Prime p] * p^(-s)`. -/
noncomputable def PrimeZeta (s : ℂ) : ℂ :=
  ∑' p : ℕ, if Nat.Prime p then (p : ℂ) ^ (-s) else 0

/-- Additive composite zeta series `ζ_C(s) = ∑' c, [1 < c ∧ ¬Nat.Prime c] * c^(-s)`. -/
noncomputable def CompositeZeta (s : ℂ) : ℂ :=
  ∑' c : ℕ, if 1 < c ∧ ¬Nat.Prime c then (c : ℂ) ^ (-s) else 0

/-- Equipartition fulcrum `Re(s) > 1` where `PrimeZeta s = CompositeZeta s`. -/
def IsEquipartitionFulcrum (s : ℂ) : Prop :=
  1 < s.re ∧ PrimeZeta s = CompositeZeta s

private lemma summable_cpow_neg_of_one_lt_re {s : ℂ} (hs : 1 < s.re) :
    Summable (fun n : ℕ => if n = 0 then (0 : ℂ) else (n : ℂ) ^ (-s)) := by
  refine (Complex.summable_one_div_nat_cpow.mpr hs).congr fun n => ?_
  rcases n with _ | n
  · simp [Complex.zero_cpow (Complex.ne_zero_of_one_lt_re hs)]
  · simp [Complex.cpow_neg, one_div]

private lemma summable_filter_cpow_neg (P : ℕ → Prop) [DecidablePred P] {s : ℂ}
    (hs : 1 < s.re) : Summable (fun n : ℕ => if P n then (n : ℂ) ^ (-s) else 0) := by
  refine (summable_cpow_neg_of_one_lt_re hs).norm.of_norm_bounded fun n => ?_
  by_cases hP : P n
  · rcases n with _ | n
    · simp [hP, Complex.zero_cpow (neg_ne_zero.mpr (Complex.ne_zero_of_one_lt_re hs))]
    · simp [hP]
  · simp [hP]

/-- Unconditional additive prime-composite partition `ζ(s) = 1 + P(s) + ζ_C(s)` on `Re(s) > 1`. -/
theorem riemannZeta_eq_one_add_primeZeta_add_compositeZeta {s : ℂ} (hs : 1 < s.re) :
    riemannZeta s = 1 + PrimeZeta s + CompositeZeta s := by
  classical
  rw [zeta_eq_tsum_one_div_nat_cpow hs]
  have h1 : (∑' n : ℕ, 1 / (n : ℂ) ^ s) =
      ∑' n : ℕ, (if n = 0 then (0 : ℂ) else (n : ℂ) ^ (-s)) := by
    refine tsum_congr fun n => ?_
    rcases n with _ | n
    · simp [Complex.zero_cpow (Complex.ne_zero_of_one_lt_re hs)]
    · simp [Complex.cpow_neg, one_div]
  have h2 : ∀ n : ℕ, (if n = 0 then (0 : ℂ) else (n : ℂ) ^ (-s)) =
      (if n = 1 then (1 : ℂ) else 0) + (if Nat.Prime n then (n : ℂ) ^ (-s) else 0) +
      (if 1 < n ∧ ¬Nat.Prime n then (n : ℂ) ^ (-s) else 0) := by
    intro n
    rcases n with _ | _ | n
    · simp [Nat.not_prime_zero]
    · simp [Nat.not_prime_one]
    · by_cases hp : Nat.Prime (n + 2) <;> simp [hp, show 1 < n + 2 by omega]
  have hU : Summable (fun n : ℕ => if n = 1 then (1 : ℂ) else 0) :=
    summable_of_ne_finset_zero (s := {1}) fun b hb => by simp_all
  have hP := summable_filter_cpow_neg Nat.Prime hs
  have hC := summable_filter_cpow_neg (fun n => 1 < n ∧ ¬Nat.Prime n) hs
  rw [h1, tsum_congr h2, hU.add hP |>.tsum_add hC, hU.tsum_add hP, tsum_ite_eq]
  rfl

/-- At any equipartition fulcrum `PrimeZeta s = CompositeZeta s`, `ζ(s) = 1 + 2 * PrimeZeta s`. -/
theorem zeta_at_equipartition_fulcrum {s : ℂ} (hf : IsEquipartitionFulcrum s) :
    riemannZeta s = 1 + 2 * PrimeZeta s := by
  rw [riemannZeta_eq_one_add_primeZeta_add_compositeZeta hf.1, hf.2]
  ring

/-- Every equipartition fulcrum splits `ζ(s) - 1` evenly between primes and composites. -/
theorem equipartition_fifty_fifty_split {s : ℂ} (hf : IsEquipartitionFulcrum s) :
    riemannZeta s - 1 = 2 * PrimeZeta s ∧ riemannZeta s - 1 = 2 * CompositeZeta s := by
  have hz := zeta_at_equipartition_fulcrum hf
  exact ⟨by rw [hz]; ring, by rw [hz, hf.2]; ring⟩

private lemma riemannZeta_zero_refl_lt {s : ℂ} (hz : riemannZeta s = 0)
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
        have hw_neg : ∀ j : ℕ, w ≠ -(j : ℂ) := fun j h => by
          have := congr_arg Complex.re h; simp [w] at this; linarith
        have hw_one : w ≠ 1 := fun h => by
          have := congr_arg Complex.re h; simp [w] at this; linarith
        have hfe := riemannZeta_one_sub hw_neg hw_one
        have h1w : 1 - w = -(↑(n + 1) : ℂ) := by dsimp [w]; push_cast [hm]; ring
        rw [h1w, hz] at hfe
        have hcpow : (2 * (Real.pi : ℂ)) ^ (-w) ≠ 0 := by
          rw [Complex.cpow_ne_zero_iff]
          exact Or.inl (by exact_mod_cast mul_ne_zero two_ne_zero Real.pi_ne_zero)
        have hcos : Complex.cos ((Real.pi : ℂ) * w / 2) ≠ 0 := by
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
        exact (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) hcpow)
          (Complex.Gamma_ne_zero hw_neg)) hcos)
          (riemannZeta_ne_zero_of_one_le_re (by dsimp [w]; norm_cast; omega))) hfe.symm
  rw [riemannZeta_one_sub h_not_neg_nat h_not_one, hz, mul_zero]

/-- Reflection dichotomy for non-trivial zeros of `riemannZeta`: every non-trivial zero
either lies on `Re(s) = 1/2` or pairs with a zero strictly in `Re(w) > 1/2`. -/
theorem zero_reflection_dichotomy {s : ℂ} (hz : riemannZeta s = 0)
    (h_not_triv : ¬∃ n : ℕ, s = -2 * (n + 1)) (h_not_one : s ≠ 1) :
    IsOnCriticalLine s ∨ ∃ w : ℂ, riemannZeta w = 0 ∧ 1 / 2 < w.re := by
  by_cases hcrit : s.re = 1 / 2
  · exact Or.inl hcrit
  · rcases lt_or_gt_of_ne hcrit with hs_lt | hs_gt
    · exact Or.inr ⟨1 - s, riemannZeta_zero_refl_lt hz h_not_triv h_not_one hs_lt⟩
    · exact Or.inr ⟨s, hz, hs_gt⟩

/-- Derivative antisymmetry of `completedRiemannZeta` under `s ↦ 1 - s` away from `{0, 1}`. -/
theorem completedRiemannZeta_deriv_one_sub {s : ℂ} (hs : s ≠ 0) (hs' : s ≠ 1) :
    deriv completedRiemannZeta (1 - s) = -deriv completedRiemannZeta s := by
  have hdiff : DifferentiableAt ℂ completedRiemannZeta (1 - s) :=
    differentiableAt_completedZeta (sub_ne_zero.mpr hs'.symm) fun h => hs (by linear_combination -h)
  have hcomp : HasDerivAt (fun z : ℂ => completedRiemannZeta (1 - z))
      (deriv completedRiemannZeta (1 - s) * (-1)) s :=
    hdiff.hasDerivAt.comp s (by simpa using (hasDerivAt_id s).const_sub (1 : ℂ))
  have hfun : (fun z : ℂ => completedRiemannZeta (1 - z)) = completedRiemannZeta := by
    ext z; exact completedRiemannZeta_one_sub z
  rw [hfun] at hcomp
  rw [hcomp.deriv]; ring

/-- At `s = 1 / 2`, the derivative of `completedRiemannZeta` vanishes: `Λ'(1 / 2) = 0`. -/
theorem completedRiemannZeta_deriv_at_half :
    deriv completedRiemannZeta (1 / 2 : ℂ) = 0 := by
  have hsym := completedRiemannZeta_deriv_one_sub (by norm_num : (1 / 2 : ℂ) ≠ 0) (by norm_num)
  rw [show (1 : ℂ) - 1 / 2 = 1 / 2 by norm_num] at hsym
  have h2 : (2 : ℂ) * deriv completedRiemannZeta (1 / 2 : ℂ) = 0 := by linear_combination hsym
  exact (mul_eq_zero.mp h2).resolve_left (by norm_num)

/-- Along `Re(s) = 1 / 2`, complex conjugation satisfies `Λ'(1/2 - i*t) = -Λ'(1/2 + i*t)`. -/
theorem completedRiemannZeta_deriv_critical_line_antisymm (t : ℝ) :
    deriv completedRiemannZeta ((1 / 2 : ℂ) - Complex.I * t) =
      -deriv completedRiemannZeta ((1 / 2 : ℂ) + Complex.I * t) := by
  have hre : ((1 / 2 : ℂ) + Complex.I * t).re = 1 / 2 := by
    simp [Complex.add_re, Complex.mul_re]
  have h0 : (1 / 2 : ℂ) + Complex.I * t ≠ 0 := fun h => by
    have := congr_arg Complex.re h; rw [hre] at this; norm_num at this
  have h1 : (1 / 2 : ℂ) + Complex.I * t ≠ 1 := fun h => by
    have := congr_arg Complex.re h; rw [hre] at this; norm_num at this
  have hsym := completedRiemannZeta_deriv_one_sub h0 h1
  rwa [show (1 : ℂ) - ((1 / 2 : ℂ) + Complex.I * t) = (1 / 2 : ℂ) - Complex.I * t by ring]
    at hsym
