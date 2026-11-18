/-
Copyright (c) 2026 Qamar Munawer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qamar Munawer
-/
module

public import RiemannBlueprint.UpstreamPRs.UpstreamPR_8G_CotangentSixReciprocity

/-!
# Universal `N`-Free Cotangent Symmetries and Infinite Octave Vanishing (`K(k, 2k) = 0`)

This module lifts Vasyunin cotangent symmetries from concrete finite truncations (`N ≤ 6`) to
unconditional universal laws valid for all `a, b, k : ℕ`:

* `vasyuninCotSum_mod_eq` and `vasyuninCotSum_dvd_right_eq_zero`: modulo periodicity in `b` and
  exact divisibility vanishing `a ∣ b → vasyuninCotSum a b = 0`.
* `vasyuninCotSum_sub_eq_neg`: universal reflection reciprocity `V(a, a - b) = -V(a, b)` for all
  `b ≤ a` without coprimality assumptions.
* `vasyuninCotSum_two_mul_self_eq_zero` and `unweightedKCot_self_two_mul_eq_zero`: infinite
  octave orthogonality `V(2k, k) = 0`, `V(k, 2k) = 0`, and `K_cot(k, 2k) = K_cot(2k, k) = 0` for
  every `k : ℕ`.
-/

@[expose] public section

open scoped BigOperators

/-- Periodicity of `vasyuninCotSum` in its second argument modulo `a`. -/
theorem vasyuninCotSum_mod_eq (a b : ℕ) : vasyuninCotSum a (b % a) = vasyuninCotSum a b := by
  by_cases ha : a = 0
  · subst ha; simp [vasyuninCotSum]
  have ha_ne : (a : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr ha
  unfold vasyuninCotSum
  refine Finset.sum_congr rfl fun m _ => ?_
  set q : ℕ := b / a
  set r : ℕ := b % a
  have hdiv : (b : ℝ) = (a : ℝ) * (q : ℝ) + (r : ℝ) := by
    exact_mod_cast (Nat.div_add_mod b a).symm
  have harg : (m : ℝ) * (b : ℝ) / (a : ℝ) =
      (m : ℝ) * (r : ℝ) / (a : ℝ) + (((m * q : ℕ) : ℤ) : ℝ) := by
    rw [hdiv, Int.cast_natCast, Nat.cast_mul]
    field_simp [ha_ne]
    ring
  rw [harg, Int.fract_add_intCast]

/-- Universal divisibility vanishing of `vasyuninCotSum`: if `a ∣ b`, then
`vasyuninCotSum a b = 0`. -/
theorem vasyuninCotSum_dvd_right_eq_zero {a b : ℕ} (h : a ∣ b) : vasyuninCotSum a b = 0 := by
  rw [← vasyuninCotSum_mod_eq a b, Nat.mod_eq_zero_of_dvd h]
  simp [vasyuninCotSum]

/-- Pointwise fractional-part reflection identity on `Ico 1 a` for all `b ≤ a`. -/
theorem fract_sub_mul_div_eq {a b m : ℕ} (ha : a ≠ 0) (hm : m ≤ a) (hb : b ≤ a) :
    Int.fract (((a - m : ℕ) : ℝ) * (b : ℝ) / (a : ℝ)) =
      Int.fract ((m : ℝ) * ((a - b : ℕ) : ℝ) / (a : ℝ)) := by
  have ha_ne : (a : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr ha
  have hcast : ((a - m : ℕ) : ℝ) * (b : ℝ) / (a : ℝ) =
      (m : ℝ) * ((a - b : ℕ) : ℝ) / (a : ℝ) + (((b : ℤ) - (m : ℤ)) : ℤ) := by
    rw [Nat.cast_sub hm, Nat.cast_sub hb]
    push_cast
    field_simp [ha_ne]
    ring
  rw [hcast, Int.fract_add_intCast]

/-- Universal reflection reciprocity for `vasyuninCotSum` without coprimality hypotheses:
for all `a, b : ℕ` with `b ≤ a`, `vasyuninCotSum a (a - b) = -vasyuninCotSum a b`. -/
theorem vasyuninCotSum_sub_eq_neg {a b : ℕ} (hb : b ≤ a) :
    vasyuninCotSum a (a - b) = -vasyuninCotSum a b := by
  by_cases ha : a = 0
  · subst ha; simp [vasyuninCotSum]
  have ha_ne : (a : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr ha
  unfold vasyuninCotSum
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_bij (fun m _ => a - m) ?_ ?_ ?_ ?_
  · intro m hm
    rcases Finset.mem_Ico.mp hm with ⟨hm1, hma⟩
    exact Finset.mem_Ico.mpr ⟨by omega, by omega⟩
  · intro m₁ hm₁ m₂ hm₂ heq
    rcases Finset.mem_Ico.mp hm₁ with ⟨_, h₁⟩
    rcases Finset.mem_Ico.mp hm₂ with ⟨_, h₂⟩
    omega
  · intro y hy
    rcases Finset.mem_Ico.mp hy with ⟨hy1, hya⟩
    exact ⟨a - y, Finset.mem_Ico.mpr ⟨by omega, by omega⟩, by omega⟩
  · intro m hm
    rcases Finset.mem_Ico.mp hm with ⟨_, hma⟩
    have hmle : m ≤ a := hma.le
    have hfr : Int.fract ((m : ℝ) * ((a - b : ℕ) : ℝ) / (a : ℝ)) =
        Int.fract (((a - m : ℕ) : ℝ) * (b : ℝ) / (a : ℝ)) :=
      (fract_sub_mul_div_eq ha hmle hb).symm
    have hang : Real.pi * (m : ℝ) / (a : ℝ) =
        Real.pi - Real.pi * ((a - m : ℕ) : ℝ) / (a : ℝ) := by
      rw [Nat.cast_sub hmle]
      field_simp [ha_ne]
      ring
    rw [hfr, hang, show Real.pi - Real.pi * ((a - m : ℕ) : ℝ) / (a : ℝ) =
      Real.pi - (Real.pi * ((a - m : ℕ) : ℝ) / (a : ℝ)) by ring,
      Real.cos_pi_sub, Real.sin_pi_sub, neg_div, mul_neg]

/-- Universal midpoint vanishing for all `k : ℕ`: `vasyuninCotSum (2 * k) k = 0`. -/
theorem vasyuninCotSum_two_mul_self_eq_zero (k : ℕ) : vasyuninCotSum (2 * k) k = 0 := by
  have href := vasyuninCotSum_sub_eq_neg (a := 2 * k) (b := k) (by omega)
  rw [show 2 * k - k = k by omega] at href
  linarith

/-- Universal octave vanishing for all `k : ℕ`: `vasyuninCotSum k (2 * k) = 0`. -/
theorem vasyuninCotSum_self_two_mul_eq_zero (k : ℕ) : vasyuninCotSum k (2 * k) = 0 :=
  vasyuninCotSum_dvd_right_eq_zero ⟨2, Nat.mul_comm 2 k⟩

/-- Universal infinite octave orthogonality of `unweightedKCot` for every `k : ℕ`:
`unweightedKCot k (2 * k) = 0` and `unweightedKCot (2 * k) k = 0`. -/
theorem unweightedKCot_self_two_mul_eq_zero (k : ℕ) :
    unweightedKCot k (2 * k) = 0 ∧ unweightedKCot (2 * k) k = 0 := by
  have h1 : unweightedKCot k (2 * k) = 0 := by
    unfold unweightedKCot vasyuninGCot
    rw [vasyuninCotSum_self_two_mul_eq_zero k, vasyuninCotSum_two_mul_self_eq_zero k]
    norm_num
  exact ⟨h1, by rw [unweightedKCot_comm (2 * k) k, h1]⟩
