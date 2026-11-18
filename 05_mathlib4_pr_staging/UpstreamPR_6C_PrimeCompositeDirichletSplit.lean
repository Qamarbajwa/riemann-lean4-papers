/-
Copyright (c) 2026 Qamar Munawer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qamar Munawer
-/
module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
public import Mathlib.Data.Nat.Prime.Basic
public import Mathlib.Data.ZMod.Basic
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.NumberTheory.LSeries.Nonvanishing
public import Mathlib.NumberTheory.LSeries.RiemannZeta
public import Mathlib.NumberTheory.Wilson
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-!
# Prime-Composite Natural Partition and Critical-Strip RH Quantifier Equivalence

This module formalizes unconditional natural-number prime/composite partition laws alongside
the critical-strip universal quantifier formulation of the Riemann Hypothesis:

* `natPrimes`, `natUnits`, `natComposites`, `nat_partition_dichotomy`: exact disjoint
  decomposition of `ℕ \ {0}` into `{1}`, primes, and composites, plus Bézout, Euclid, and mod-6.
* `InCriticalStrip`, `IsOnCriticalLine`, `RiemannHypothesisStrip`: critical strip and line.
* `zetaZeroReflectionSymmetry_unconditional`: unconditional functional-equation reflection of
  non-trivial zeros inside `0 < Re(s) < 1`.
* `riemannHypothesis_iff_strip`: bidirectional equivalence `_root_.RiemannHypothesis ↔
  RiemannHypothesisStrip`.
-/

@[expose] public section

open Complex

/-- Set of prime natural numbers. -/
def natPrimes : Set ℕ := {p | Nat.Prime p}

/-- Unit singleton `{1}` inside `ℕ`. -/
def natUnits : Set ℕ := {1}

/-- Set of composite natural numbers `c > 1` that are not prime. -/
def natComposites : Set ℕ := {c | 1 < c ∧ ¬Nat.Prime c}

/-- Every nonzero natural number falls into `natUnits`, `natPrimes`, or `natComposites`. -/
theorem nat_partition_dichotomy {n : ℕ} (hn : n ≠ 0) :
    n ∈ natUnits ∨ n ∈ natPrimes ∨ n ∈ natComposites := by
  rcases eq_or_lt_of_le (Nat.succ_le_of_lt (Nat.pos_of_ne_zero hn)) with h1 | hgt
  · exact Or.inl h1.symm
  · by_cases hp : Nat.Prime n
    · exact Or.inr (Or.inl hp)
    · exact Or.inr (Or.inr ⟨hgt, hp⟩)

/-- Bézout's identity for natural numbers inside `ℤ`. -/
theorem bezout_identity (a b : ℕ) :
    ∃ x y : ℤ, (a : ℤ) * x + (b : ℤ) * y = Nat.gcd a b :=
  ⟨Nat.gcdA a b, Nat.gcdB a b, (Nat.gcd_eq_gcd_ab a b).symm⟩

/-- Euclid's prime divisibility lemma: `p ∣ a * b → p ∣ a ∨ p ∣ b`. -/
theorem euclid_lemma {p a b : ℕ} (hp : Nat.Prime p) (h : p ∣ a * b) : p ∣ a ∨ p ∣ b :=
  (Nat.Prime.dvd_mul hp).mp h

/-- Modulo-6 sieve confinement: every prime `p > 3` satisfies `p % 6 = 1 ∨ p % 6 = 5`. -/
theorem modulo_6_sieve_confinement (p : ℕ) (hp : Nat.Prime p) (hp3 : 3 < p) :
    p % 6 = 1 ∨ p % 6 = 5 := by
  have hrem : p % 6 < 6 := Nat.mod_lt p (by decide)
  have h2 : ¬2 ∣ p := fun h => by
    have := (Nat.Prime.eq_one_or_self_of_dvd hp 2 h).resolve_left (by decide)
    omega
  have h3 : ¬3 ∣ p := fun h => by
    have := (Nat.Prime.eq_one_or_self_of_dvd hp 3 h).resolve_left (by decide)
    omega
  have h0 : p % 6 ≠ 0 := fun h => h2 (dvd_trans (by decide : 2 ∣ 6) (Nat.dvd_of_mod_eq_zero h))
  have h2' : p % 6 ≠ 2 := fun h => h2 <| by
    have hd : 2 ∣ 6 * (p / 6) + p % 6 := dvd_add (dvd_mul_of_dvd_left (by decide) _) (by rw [h])
    rwa [Nat.div_add_mod] at hd
  have h3' : p % 6 ≠ 3 := fun h => h3 <| by
    have hd : 3 ∣ 6 * (p / 6) + p % 6 := dvd_add (dvd_mul_of_dvd_left (by decide) _) (by rw [h])
    rwa [Nat.div_add_mod] at hd
  have h4' : p % 6 ≠ 4 := fun h => h2 <| by
    have hd : 2 ∣ 6 * (p / 6) + p % 6 :=
      dvd_add (dvd_mul_of_dvd_left (by decide) _) (by rw [h]; decide)
    rwa [Nat.div_add_mod] at hd
  omega

/-- Fermat's Little Theorem in `ZMod p`. -/
theorem fermats_little_theorem (p a : ℕ) (hp : Nat.Prime p) (h : ¬p ∣ a) :
    (a : ZMod p) ^ (p - 1) = 1 := by
  have : Fact (Nat.Prime p) := ⟨hp⟩
  refine ZMod.pow_card_sub_one_eq_one fun hz => h ?_
  have hcast : ((a : ℕ) : ZMod p) = (a : ZMod p) := rfl
  rwa [← hcast, CharP.cast_eq_zero_iff (ZMod p) p a] at hz

/-- Wilson's Theorem: `(p - 1)! ≡ -1 (mod p)` for prime `p`. -/
theorem wilsons_theorem (p : ℕ) (hp : Nat.Prime p) :
    (Nat.factorial (p - 1) : ZMod p) = -1 := by
  have : Fact (Nat.Prime p) := ⟨hp⟩
  exact ZMod.wilsons_lemma p

/-- Open critical strip `0 < Re(s) < 1`. -/
def InCriticalStrip (s : ℂ) : Prop :=
  0 < s.re ∧ s.re < 1

/-- Critical line `Re(s) = 1 / 2`. -/
def IsOnCriticalLine (s : ℂ) : Prop :=
  s.re = 1 / 2

/-- Universal critical-strip formulation of the Riemann Hypothesis. -/
def RiemannHypothesisStrip : Prop :=
  ∀ s : ℂ, InCriticalStrip s → riemannZeta s = 0 → IsOnCriticalLine s

/-- Reflection `s ↦ 1 - s` preserves `InCriticalStrip`. -/
theorem inCriticalStrip_one_sub {s : ℂ} (hs : InCriticalStrip s) :
    InCriticalStrip (1 - s) := by
  refine ⟨?_, ?_⟩ <;> · rw [Complex.sub_re, Complex.one_re]; linarith [hs.1, hs.2]

/-- No element of `InCriticalStrip` equals `-n` for `n : ℕ`. -/
theorem inCriticalStrip_ne_neg_nat {s : ℂ} (hs : InCriticalStrip s) (n : ℕ) :
    s ≠ -(n : ℂ) := fun hn => by
  have hre : s.re = -(n : ℝ) := by simp [hn]
  linarith [hs.1, Nat.cast_nonneg (α := ℝ) n]

/-- No element of `InCriticalStrip` equals `1`. -/
theorem inCriticalStrip_ne_one {s : ℂ} (hs : InCriticalStrip s) : s ≠ 1 := fun h1 => by
  have hre : s.re = 1 := by simp [h1]
  linarith [hs.2]

/-- Functional-equation zero reflection inside `InCriticalStrip`. -/
theorem riemannZeta_one_sub_eq_zero_of_inCriticalStrip {s : ℂ}
    (hs : InCriticalStrip s) (hz : riemannZeta s = 0) : riemannZeta (1 - s) = 0 := by
  rw [riemannZeta_one_sub (inCriticalStrip_ne_neg_nat hs) (inCriticalStrip_ne_one hs), hz, mul_zero]

/-- Unconditional functional-equation reflection symmetry for critical-strip zeros. -/
theorem zetaZeroReflectionSymmetry_unconditional :
    ∀ s : ℂ, InCriticalStrip s → riemannZeta s = 0 →
      InCriticalStrip (1 - s) ∧ riemannZeta (1 - s) = 0 :=
  fun _ hs hz =>
    ⟨inCriticalStrip_one_sub hs, riemannZeta_one_sub_eq_zero_of_inCriticalStrip hs hz⟩

/-- Forward implication from Mathlib's `_root_.RiemannHypothesis` to `RiemannHypothesisStrip`. -/
theorem riemannHypothesis_implies_strip : _root_.RiemannHypothesis → RiemannHypothesisStrip := by
  intro hRH s hs hz
  exact hRH s hz (by
    rintro ⟨n, rfl⟩
    have hre : ((-2 : ℂ) * (↑n + 1)).re = -2 * ((n : ℝ) + 1) := by simp [Complex.mul_re]
    linarith [hs.1, Nat.cast_nonneg (α := ℝ) n]) (inCriticalStrip_ne_one hs)

private lemma riemannZeta_one_sub_zero_of_re_le_zero {s : ℂ} (hz : riemannZeta s = 0)
    (h_not_triv : ¬∃ n : ℕ, s = -2 * (n + 1)) (h_not_one : s ≠ 1) :
    riemannZeta (1 - s) = 0 := by
  have h_not_neg_nat : ∀ n : ℕ, s ≠ -(n : ℂ) := by
    intro n hn
    subst hn
    rcases n with _ | n
    · simp [riemannZeta_zero] at hz
    · rcases Nat.even_or_odd (n + 1) with ⟨m, hm⟩ | ⟨m, hm⟩
      · refine h_not_triv ⟨m - 1, ?_⟩
        have h1 : n + 1 = 2 * ((m - 1) + 1) := by omega
        push_cast [h1]; ring
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

/-- Backward implication from `RiemannHypothesisStrip` to Mathlib's `_root_.RiemannHypothesis`. -/
theorem riemannHypothesis_of_strip (h_strip : RiemannHypothesisStrip) :
    _root_.RiemannHypothesis := by
  intro s hz h_not_triv h_not_one
  have hs_lt : s.re < 1 := by
    by_contra hge
    exact riemannZeta_ne_zero_of_one_le_re (not_lt.mp hge) hz
  have hs_pos : 0 < s.re := by
    by_contra hle
    exact riemannZeta_ne_zero_of_one_le_re
      (by rw [Complex.sub_re, Complex.one_re]; linarith)
      (riemannZeta_one_sub_zero_of_re_le_zero hz h_not_triv h_not_one)
  exact h_strip s ⟨hs_pos, hs_lt⟩ hz

/-- Bidirectional quantifier equivalence between `_root_.RiemannHypothesis` and the
critical-strip formulation `RiemannHypothesisStrip`. -/
theorem riemannHypothesis_iff_strip :
    _root_.RiemannHypothesis ↔ RiemannHypothesisStrip :=
  ⟨riemannHypothesis_implies_strip, riemannHypothesis_of_strip⟩
