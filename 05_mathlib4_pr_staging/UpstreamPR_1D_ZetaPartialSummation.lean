/-
Copyright (c) 2026 Qamar Munawer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qamar Munawer
-/
module

public import Mathlib.Analysis.Analytic.Uniqueness
public import Mathlib.Analysis.PSeriesComplex
public import Mathlib.NumberTheory.Harmonic.ZetaAsymp
public import RiemannBlueprint.UpstreamPRs.UpstreamPR_1C_ZetaRemainderSeries

/-!
# Euler–Maclaurin Analytic Continuation and Partial Summation for Zeta

This file extends the Euler–Maclaurin series representation of `riemannZeta` from `1 < s.re` to
the half-plane `0 < s.re` (away from `s = 1`, for `s.im ≠ 0`) and deduces finite partial summation
with cutoff `M`:
1. `riemannZeta_eq_one_div_sub_add_tsum_of_one_lt_re`: series identity on `1 < s.re`.
2. `riemannZeta_eq_one_div_sub_add_tsum`: analytic continuation to `0 < s.re` with `s.im ≠ 0`.
3. `riemannZeta_partial_summation`: partial summation up to cutoff `M` with remainder tail.
-/

@[expose] public section

open Complex Filter Set
open scoped Topology

/-- Euler–Maclaurin series representation of `riemannZeta s` in the region `1 < s.re`. -/
theorem riemannZeta_eq_one_div_sub_add_tsum_of_one_lt_re {s : ℂ} (hs : 1 < s.re) :
    riemannZeta s = 1 / (s - 1) + ∑' n : ℕ, zetaRemainderTerm s n := by
  have hs_pos : 0 < s.re := by linarith
  have hs1 : s ≠ 1 := fun h => by rw [h] at hs; simp at hs
  have hsum_zeta : HasSum (fun n : ℕ => ((n + 1 : ℕ) : ℂ) ^ (-s)) (riemannZeta s) := by
    have h_summ : Summable (fun n : ℕ => ((n + 1 : ℕ) : ℂ) ^ (-s)) := by
      have h_norm : Summable (fun n : ℕ => ‖((n + 1 : ℕ) : ℂ) ^ (-s)‖) := by
        have heq : (fun n : ℕ => ‖((n + 1 : ℕ) : ℂ) ^ (-s)‖) =
            fun n : ℕ => ((n + 1 : ℝ) ^ (-s.re)) := by
          ext n
          have hn : (0 : ℝ) < (n + 1 : ℝ) := by positivity
          have hcast : (((n + 1 : ℕ) : ℂ)) = ((n + 1 : ℝ) : ℂ) := by push_cast; rfl
          rw [hcast, Complex.norm_cpow_eq_rpow_re_of_pos hn, Complex.neg_re]
        rw [heq]
        refine ((summable_nat_add_iff 1).mpr (Real.summable_nat_rpow_inv.mpr hs)).congr
          fun n => ?_
        rw [Nat.cast_add, Nat.cast_one, Real.rpow_neg (by positivity)]
      exact h_norm.of_norm
    rw [zeta_eq_tsum_one_div_nat_add_one_cpow hs]
    have heq_fn : (fun n : ℕ => 1 / ((n : ℂ) + 1) ^ s) =
        fun n : ℕ => ((n + 1 : ℕ) : ℂ) ^ (-s) := by
      ext n
      rw [Nat.cast_add, Nat.cast_one, one_div, ← Complex.cpow_neg]
    rw [heq_fn]
    exact h_summ.hasSum
  have h_rem_summ := summable_zetaRemainderTerm hs_pos hs1
  have h_tele_summ : Summable (fun n : ℕ =>
      (((n + 1 : ℕ) : ℂ) ^ (1 - s) - ((n + 2 : ℕ) : ℂ) ^ (1 - s)) / (s - 1)) := by
    have h_eq : (fun n : ℕ =>
        (((n + 1 : ℕ) : ℂ) ^ (1 - s) - ((n + 2 : ℕ) : ℂ) ^ (1 - s)) / (s - 1)) =
        fun n : ℕ => ((n + 1 : ℕ) : ℂ) ^ (-s) - zetaRemainderTerm s n := by
      ext n; unfold zetaRemainderTerm; ring
    rw [h_eq]
    exact hsum_zeta.summable.sub h_rem_summ
  have h_tele_has : HasSum (fun n : ℕ =>
      (((n + 1 : ℕ) : ℂ) ^ (1 - s) - ((n + 2 : ℕ) : ℂ) ^ (1 - s)) / (s - 1))
      (1 / (s - 1)) := by
    rw [h_tele_summ.hasSum_iff_tendsto_nat]
    have h_sum_eq : ∀ N : ℕ,
        (∑ n ∈ Finset.range N,
          (((n + 1 : ℕ) : ℂ) ^ (1 - s) - ((n + 2 : ℕ) : ℂ) ^ (1 - s)) / (s - 1)) =
          (1 - ((N + 1 : ℕ) : ℂ) ^ (1 - s)) / (s - 1) := by
      intro N
      induction N with
      | zero => simp
      | succ N ih =>
        rw [Finset.sum_range_succ, ih]
        have hcast : ((N + 1 + 1 : ℕ) : ℂ) = ((N + 2 : ℕ) : ℂ) := by push_cast; ring
        rw [hcast]; ring
    simp_rw [h_sum_eq]
    have h_tail : Tendsto (fun N : ℕ => ((N + 1 : ℕ) : ℂ) ^ (1 - s)) atTop (nhds 0) := by
      rw [tendsto_zero_iff_norm_tendsto_zero]
      have heq_norm : (fun N : ℕ => ‖((N + 1 : ℕ) : ℂ) ^ (1 - s)‖) =
          fun N : ℕ => ((N + 1 : ℝ) ^ (-(s.re - 1))) := by
        ext N
        have hN : (0 : ℝ) < (N + 1 : ℝ) := by positivity
        have hcast : (((N + 1 : ℕ) : ℂ)) = ((N + 1 : ℝ) : ℂ) := by push_cast; rfl
        rw [hcast, Complex.norm_cpow_eq_rpow_re_of_pos hN]
        congr 1
        simp only [Complex.sub_re, Complex.one_re]; ring
      rw [heq_norm]
      exact (tendsto_rpow_neg_atTop (by linarith : 0 < s.re - 1)).comp
        (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
    simpa [sub_zero] using ((tendsto_const_nhds (x := (1 : ℂ))).sub h_tail).div_const (s - 1)
  have h_diff_has := hsum_zeta.sub h_tele_has
  change HasSum (zetaRemainderTerm s) (riemannZeta s - 1 / (s - 1)) at h_diff_has
  linear_combination -h_diff_has.tsum_eq

private lemma convex_linear_gt (f : ℂ →ₗ[ℝ] ℝ) (r : ℝ) : Convex ℝ {s : ℂ | r < f s} := by
  intro x hx y hy a b ha hb hab
  simp only [Set.mem_ofPred_eq, map_add, map_smul, smul_eq_mul] at hx hy ⊢
  by_cases ha0 : 0 < a
  · calc r = a * r + b * r := by rw [← add_mul, hab, one_mul]
      _ < a * f x + b * f y := add_lt_add_of_lt_of_le
          (mul_lt_mul_of_pos_left hx ha0) (mul_le_mul_of_nonneg_left hy.le hb)
  · have ha0' : a = 0 := le_antisymm (not_lt.mp ha0) ha
    have hb1 : b = 1 := by linarith
    rw [ha0', hb1]; linarith

private lemma convex_linear_lt (f : ℂ →ₗ[ℝ] ℝ) (r : ℝ) : Convex ℝ {s : ℂ | f s < r} := by
  simpa [neg_lt_neg_iff] using convex_linear_gt (-f) (-r)

/-- Analytic continuation of the Euler–Maclaurin remainder identity to `0 < s.re` with
`s.im ≠ 0`. -/
theorem riemannZeta_eq_one_div_sub_add_tsum {s : ℂ} (hs_pos : 0 < s.re) (hs_im : s.im ≠ 0) :
    riemannZeta s = 1 / (s - 1) + ∑' n : ℕ, zetaRemainderTerm s n := by
  let S : Set ℂ := {z : ℂ | 0 < z.re ∧ z ≠ 1}
  let F : ℂ → ℂ := fun z => riemannZeta z - (1 / (z - 1) + ∑' n : ℕ, zetaRemainderTerm z n)
  have hS_open : IsOpen S := (isOpen_lt continuous_const Complex.continuous_re).inter isOpen_ne
  have hF_ana : AnalyticOnNhd ℂ F S := by
    have h_zeta : AnalyticOnNhd ℂ riemannZeta S :=
      DifferentiableOn.analyticOnNhd
        (fun z hz => (differentiableAt_riemannZeta hz.2).differentiableWithinAt) hS_open
    have h_inv : AnalyticOnNhd ℂ (fun z : ℂ => 1 / (z - 1)) S :=
      DifferentiableOn.analyticOnNhd (fun z hz =>
        ((differentiableAt_const (1 : ℂ)).div (differentiableAt_id.sub (differentiableAt_const 1))
          (sub_ne_zero.mpr hz.2)).differentiableWithinAt) hS_open
    exact h_zeta.sub (h_inv.add analyticOnNhd_tsum_zetaRemainderTerm)
  let U_top : Set ℂ := {z : ℂ | 0 < z.re ∧ 0 < z.im}
  let U_bot : Set ℂ := {z : ℂ | 0 < z.re ∧ z.im < 0}
  have h_right_open : IsOpen {z : ℂ | 1 < z.re} :=
    isOpen_lt continuous_const Complex.continuous_re
  have hF_zero_right : ∀ z : ℂ, 1 < z.re → F z = 0 := fun z hz => by
    dsimp [F]; rw [riemannZeta_eq_one_div_sub_add_tsum_of_one_lt_re hz, sub_self]
  rcases lt_or_gt_of_ne hs_im with him_neg | him_pos
  · have h_pre : IsPreconnected U_bot :=
      ((convex_linear_gt Complex.reCLM 0).inter (convex_linear_lt Complex.imCLM 0)).isPreconnected
    have h_ana : AnalyticOnNhd ℂ F U_bot :=
      hF_ana.mono fun z ⟨hz_re, hz_im⟩ => ⟨hz_re, fun h1 => by subst h1; simp at hz_im⟩
    have h_ev : F =ᶠ[𝓝 ((2 : ℂ) - I)] 0 := Filter.eventually_of_mem
      (h_right_open.mem_nhds (by norm_num : 1 < ((2 : ℂ) - I).re)) hF_zero_right
    have hFz := h_ana.eqOn_zero_of_preconnected_of_eventuallyEq_zero h_pre (by simp [U_bot]) h_ev
      ⟨hs_pos, him_neg⟩
    exact sub_eq_zero.mp hFz
  · have h_pre : IsPreconnected U_top :=
      ((convex_linear_gt Complex.reCLM 0).inter (convex_linear_gt Complex.imCLM 0)).isPreconnected
    have h_ana : AnalyticOnNhd ℂ F U_top :=
      hF_ana.mono fun z ⟨hz_re, hz_im⟩ => ⟨hz_re, fun h1 => by subst h1; simp at hz_im⟩
    have h_ev : F =ᶠ[𝓝 ((2 : ℂ) + I)] 0 := Filter.eventually_of_mem
      (h_right_open.mem_nhds (by norm_num : 1 < ((2 : ℂ) + I).re)) hF_zero_right
    have hFz := h_ana.eqOn_zero_of_preconnected_of_eventuallyEq_zero h_pre (by simp [U_top]) h_ev
      ⟨hs_pos, him_pos⟩
    exact sub_eq_zero.mp hFz

/-- Euler–Maclaurin finite partial summation with cutoff `M : ℕ` for `0 < s.re` and
`s.im ≠ 0`. -/
theorem riemannZeta_partial_summation (M : ℕ) {s : ℂ} (hs_pos : 0 < s.re) (hs_im : s.im ≠ 0) :
    riemannZeta s =
      (∑ n ∈ Finset.range M, ((n + 1 : ℕ) : ℂ) ^ (-s)) +
        ((M + 1 : ℕ) : ℂ) ^ (1 - s) / (s - 1) +
        ∑' n : ℕ, zetaRemainderTerm s (n + M) := by
  have hs1 : s ≠ 1 := fun h => hs_im (by rw [h]; simp)
  have h_fin : 1 / (s - 1) + ∑ n ∈ Finset.range M, zetaRemainderTerm s n =
      (∑ n ∈ Finset.range M, ((n + 1 : ℕ) : ℂ) ^ (-s)) +
        ((M + 1 : ℕ) : ℂ) ^ (1 - s) / (s - 1) := by
    induction M with
    | zero => simp
    | succ M ih =>
      rw [Finset.sum_range_succ, ← add_assoc, ih, Finset.sum_range_succ]
      unfold zetaRemainderTerm
      have hcast : ((M + 1 + 1 : ℕ) : ℂ) = ((M + 2 : ℕ) : ℂ) := by push_cast; ring
      rw [hcast]; ring
  rw [riemannZeta_eq_one_div_sub_add_tsum hs_pos hs_im]
  have h_split := (summable_zetaRemainderTerm hs_pos hs1).sum_add_tsum_nat_add M
  rw [← h_split, ← add_assoc, h_fin]
