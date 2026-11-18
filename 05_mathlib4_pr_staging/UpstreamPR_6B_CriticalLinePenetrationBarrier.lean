/-
Copyright (c) 2026 Qamar Munawer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qamar Munawer
-/
module

public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Complex
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import Mathlib.NumberTheory.LSeries.RiemannZeta
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import RiemannBlueprint.UpstreamPRs.UpstreamPR_3A_VasyuninIntegral
public import RiemannBlueprint.UpstreamPRs.UpstreamPR_4A_AffineLagrangeProjection
public import RiemannBlueprint.UpstreamPRs.UpstreamPR_5C_MellinNymanBeurlingIff

/-!
# Critical-Line Penetration Lower Bound and Strip Rouché Defect Coupling

This module develops unconditional analytic and pointwise bounds for finite Dirichlet
polynomial reciprocal-zeta approximants `D_c(s) = ∑_{k=1}^N c_k * k^{-s}` and the strip
defect `1 + ζ(s) * D_c(s)`:

* `dirichletPoly`, `stripDefect`: finite Dirichlet polynomial and Rouché strip defect.
* `analyticOnNhd_dirichletPoly`, `analyticOnNhd_zeta_mul_dirichletPoly`: entire analyticity of
  `D_c` and `{1}ᶜ`-analyticity of `s ↦ riemannZeta s * dirichletPoly c N s`.
* `stripDefect_eq_mul_mellin_residual`: coupling `1 + ζ(s) D_c(s) = s * M(1 - Φ_c)(s)` in the
  open critical strip `0 < Re(s) < 1`.
* `critical_line_penetration_lower_bound`: unconditional penetration floor
  `(1 - ‖1 + riemannZeta s * dirichletPoly c N s‖) / ‖riemannZeta s‖ ≤`
  `‖dirichletPoly c N s‖`.
-/

@[expose] public section

open MeasureTheory Set Filter

/-- Finite Dirichlet polynomial `D_c(s) = ∑ k ∈ Finset.Icc 1 N, c k * (k : ℂ) ^ (-s)`. -/
noncomputable def dirichletPoly (c : ℕ → ℂ) (N : ℕ) (s : ℂ) : ℂ :=
  ∑ k ∈ Finset.Icc 1 N, c k * (k : ℂ) ^ (-s)

/-- Strip Rouché defect `stripDefect c N s = 1 + riemannZeta s * dirichletPoly c N s`. -/
noncomputable def stripDefect (c : ℕ → ℂ) (N : ℕ) (s : ℂ) : ℂ :=
  1 + riemannZeta s * dirichletPoly c N s

private lemma differentiable_dirichletPoly (c : ℕ → ℂ) (N : ℕ) :
    Differentiable ℂ (dirichletPoly c N) := fun s =>
  DifferentiableAt.fun_sum fun k hk =>
    (differentiableAt_const (c k)).mul <| (differentiableAt_const (k : ℂ)).cpow
      differentiableAt_id.neg (Or.inl <| by
        simpa using (Nat.cast_pos.mpr (Finset.mem_Icc.mp hk).1 : (0 : ℝ) < k))

/-- `dirichletPoly c N` is analytic on all of `ℂ`. -/
theorem analyticOnNhd_dirichletPoly (c : ℕ → ℂ) (N : ℕ) :
    AnalyticOnNhd ℂ (dirichletPoly c N) univ :=
  (differentiable_dirichletPoly c N).differentiableOn.analyticOnNhd isOpen_univ

/-- The holomorphic strip product `s ↦ riemannZeta s * dirichletPoly c N s` is analytic on
`{1}ᶜ`. -/
theorem analyticOnNhd_zeta_mul_dirichletPoly (c : ℕ → ℂ) (N : ℕ) :
    AnalyticOnNhd ℂ (fun s : ℂ => riemannZeta s * dirichletPoly c N s) {1}ᶜ :=
  analyticOn_riemannZeta.mul ((analyticOnNhd_dirichletPoly c N).mono (subset_univ {1}ᶜ))

/-- Pointwise algebraic non-vanishing: `‖1 + z * d‖ < 1` forces `z ≠ 0 ∧ d ≠ 0`. -/
theorem ne_zero_of_norm_one_add_mul_lt_one (z d : ℂ) (h : ‖1 + z * d‖ < 1) :
    z ≠ 0 ∧ d ≠ 0 :=
  ⟨fun hz => by rw [hz, zero_mul, add_zero, norm_one] at h; exact lt_irrefl 1 h,
   fun hd => by rw [hd, mul_zero, add_zero, norm_one] at h; exact lt_irrefl 1 h⟩

/-- Unconditional pointwise non-vanishing: `‖stripDefect c N s‖ < 1` forces
`riemannZeta s ≠ 0 ∧ dirichletPoly c N s ≠ 0`. -/
theorem stripDefect_norm_lt_one_implies_ne_zero (c : ℕ → ℂ) (N : ℕ) (s : ℂ)
    (h : ‖stripDefect c N s‖ < 1) : riemannZeta s ≠ 0 ∧ dirichletPoly c N s ≠ 0 :=
  ne_zero_of_norm_one_add_mul_lt_one (riemannZeta s) (dirichletPoly c N s) h

/-- Exact reciprocal-zeta approximation error identity whenever `riemannZeta s ≠ 0`. -/
theorem inv_zeta_approx_error_eq (c : ℕ → ℂ) (N : ℕ) (s : ℂ) (hz : riemannZeta s ≠ 0) :
    dirichletPoly c N s - (-1 / riemannZeta s) = stripDefect c N s / riemannZeta s := by
  unfold stripDefect
  field_simp [hz]
  ring

/-- Unconditional critical-line penetration lower bound whenever `‖1 + ζ(s) * D_c(s)‖ < 1`:
`1 - ‖1 + riemannZeta s * dirichletPoly c N s‖` divided by `‖riemannZeta s‖` is at most
`‖dirichletPoly c N s‖`. -/
theorem critical_line_penetration_lower_bound (c : ℕ → ℂ) (N : ℕ) (s : ℂ)
    (h : ‖1 + riemannZeta s * dirichletPoly c N s‖ < 1) :
    (1 - ‖1 + riemannZeta s * dirichletPoly c N s‖) / ‖riemannZeta s‖ ≤
      ‖dirichletPoly c N s‖ := by
  have hz : riemannZeta s ≠ 0 :=
    (ne_zero_of_norm_one_add_mul_lt_one (riemannZeta s) (dirichletPoly c N s) h).1
  have hz_pos : 0 < ‖riemannZeta s‖ := norm_pos_iff.mpr hz
  have htri : 1 ≤ ‖1 + riemannZeta s * dirichletPoly c N s‖ +
      ‖riemannZeta s‖ * ‖dirichletPoly c N s‖ := by
    calc
      (1 : ℝ) = ‖(1 : ℂ)‖ := norm_one.symm
      _ = ‖(1 + riemannZeta s * dirichletPoly c N s) -
            riemannZeta s * dirichletPoly c N s‖ := by ring_nf
      _ ≤ ‖1 + riemannZeta s * dirichletPoly c N s‖ +
            ‖riemannZeta s * dirichletPoly c N s‖ := norm_sub_le _ _
      _ = ‖1 + riemannZeta s * dirichletPoly c N s‖ +
            ‖riemannZeta s‖ * ‖dirichletPoly c N s‖ := by rw [norm_mul]
  rw [div_le_iff₀ hz_pos]
  linarith

private lemma integrableOn_Ioc_cpow_strip {s : ℂ} (hs : 0 < s.re) :
    IntegrableOn (fun x : ℝ => (x : ℂ) ^ (s - 1)) (Ioc (0 : ℝ) 1) :=
  ((intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0 : ℝ) ≤ 1)).mp
    (intervalIntegral.intervalIntegrable_rpow' (by linarith : (-1 : ℝ) < s.re - 1))).mono'
    (ContinuousOn.aestronglyMeasurable (fun _ ht => (Complex.continuousAt_ofReal_cpow_const _ _
      (Or.inr ht.1.ne')).continuousWithinAt) measurableSet_Ioc)
    ((ae_restrict_mem measurableSet_Ioc).mono fun x hx => by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hx.1, Complex.sub_re, Complex.one_re])

private lemma integrableOn_Ioc_scaled_cpow (k : ℕ) (s : ℂ) (hs : 0 < s.re) :
    IntegrableOn (fun x : ℝ => (recipFractScaled k x : ℂ) * (x : ℂ) ^ (s - 1))
      (Ioc (0 : ℝ) 1) := by
  have hm : Measurable (recipFractScaled k) :=
    measurable_fract.comp (measurable_const.div (measurable_const.mul measurable_id))
  refine (integrableOn_Ioc_cpow_strip hs).norm.mono'
    (hm.complex_ofReal.aestronglyMeasurable.restrict.mul
      (ContinuousOn.aestronglyMeasurable (fun _ ht => (Complex.continuousAt_ofReal_cpow_const _ _
        (Or.inr ht.1.ne')).continuousWithinAt) measurableSet_Ioc))
    ((ae_restrict_mem measurableSet_Ioc).mono fun x _ => by
      dsimp only [recipFractScaled]
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Int.fract_nonneg _)]
      exact mul_le_of_le_one_left (norm_nonneg _) (Int.fract_lt_one _).le)

private lemma integrableOn_Ioi_scaled_cpow (k : ℕ) (hk : 1 ≤ k) {s : ℂ} (hs : s.re < 1) :
    IntegrableOn (fun x : ℝ => (recipFractScaled k x : ℂ) * (x : ℂ) ^ (s - 1))
      (Ioi (1 : ℝ)) := by
  have hkm : Measurable (recipFractScaled k) :=
    measurable_fract.comp (measurable_const.div (measurable_const.mul measurable_id))
  have hr : IntegrableOn (fun x : ℝ => (1 / (k : ℝ)) * x ^ (s.re - 2)) (Ioi (1 : ℝ)) :=
    (integrableOn_Ioi_rpow_of_lt (by linarith : s.re - 2 < -1) zero_lt_one).const_mul _
  refine hr.mono' (hkm.complex_ofReal.aestronglyMeasurable.restrict.mul
    (ContinuousOn.aestronglyMeasurable (fun _ ht => (Complex.continuousAt_ofReal_cpow_const _ _
      (Or.inr (lt_trans zero_lt_one ht).ne')).continuousWithinAt) measurableSet_Ioi))
    ((ae_restrict_mem measurableSet_Ioi).mono fun x hx => ?_)
  have hx1 : 1 < x := Set.mem_Ioi.mp hx
  have hkx : 1 < (k : ℝ) * x := one_lt_mul_of_le_of_lt (Nat.one_le_cast.mpr hk) hx1
  have hfr : recipFractScaled k x = 1 / ((k : ℝ) * x) :=
    Int.fract_eq_self.mpr ⟨by positivity, (div_lt_one (by positivity)).mpr hkx⟩
  have hxp : 0 < x := lt_trans zero_lt_one hx1
  rw [hfr, norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity),
    Complex.norm_cpow_eq_rpow_re_of_pos hxp, Complex.sub_re, Complex.one_re,
    show s.re - 2 = -1 + (s.re - 1) by ring, Real.rpow_add hxp, Real.rpow_neg_one]
  exact le_of_eq (by ring)

private lemma integral_Ioi_scaled_cpow (k : ℕ) (hk : 1 ≤ k) {s : ℂ} (hs : s.re < 1) :
    ∫ x in Ioi (1 : ℝ), (recipFractScaled k x : ℂ) * (x : ℂ) ^ (s - 1) =
      -(1 / ((k : ℂ) * (s - 1))) := by
  have hs1 : s - 1 ≠ 0 := sub_ne_zero.mpr fun h => by rw [h] at hs; simp at hs
  have hkne : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hint : IntegrableOn (fun x : ℝ => (1 / (k : ℂ)) * (x : ℂ) ^ (s - 2))
      (Ioi (1 : ℝ)) := by
    refine ((integrableOn_Ioi_rpow_of_lt (by linarith : s.re - 2 < -1) zero_lt_one).const_mul
      (1 / (k : ℝ))).mono' (ContinuousOn.aestronglyMeasurable (fun _ ht =>
        continuousWithinAt_const.mul (Complex.continuousAt_ofReal_cpow_const _ _
          (Or.inr (lt_trans zero_lt_one ht).ne')).continuousWithinAt) measurableSet_Ioi)
      ((ae_restrict_mem measurableSet_Ioi).mono fun x hx => by
        have hxp : 0 < x := lt_trans zero_lt_one (Set.mem_Ioi.mp hx)
        rw [norm_mul, norm_div, norm_one, Complex.norm_natCast,
          Complex.norm_cpow_eq_rpow_re_of_pos hxp, show (s - 2).re = s.re - 2 by simp])
  have hcongr : EqOn (fun x : ℝ => (recipFractScaled k x : ℂ) * (x : ℂ) ^ (s - 1))
      (fun x : ℝ => (1 / (k : ℂ)) * (x : ℂ) ^ (s - 2)) (Ioi (1 : ℝ)) := fun x hx => by
    have hx1 : 1 < x := Set.mem_Ioi.mp hx
    have hkx : 1 < (k : ℝ) * x := one_lt_mul_of_le_of_lt (Nat.one_le_cast.mpr hk) hx1
    have hx0 : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (lt_trans zero_lt_one hx1).ne'
    dsimp only
    rw [show recipFractScaled k x = 1 / ((k : ℝ) * x) from Int.fract_eq_self.mpr
        ⟨by positivity, (div_lt_one (by positivity)).mpr hkx⟩,
      show s - 2 = s - 1 + (-1 : ℂ) by ring, Complex.cpow_add _ _ hx0, Complex.cpow_neg_one]
    push_cast; ring
  have htend : Tendsto (fun b : ℝ => ∫ x in (1 : ℝ)..b, (1 / (k : ℂ)) * (x : ℂ) ^ (s - 2))
      atTop (nhds (-(1 / ((k : ℂ) * (s - 1))))) := by
    have hval : ∀ᶠ b in atTop, ∫ x in (1 : ℝ)..b, (1 / (k : ℂ)) * (x : ℂ) ^ (s - 2) =
        (1 / (k : ℂ)) * (((b : ℂ) ^ (s - 1) - 1) / (s - 1)) := by
      filter_upwards [eventually_ge_atTop (1 : ℝ)] with b hb
      rw [intervalIntegral.integral_const_mul, integral_cpow (Or.inr ⟨fun h => hs1
          (by linear_combination h), fun h => by rw [uIcc_of_le hb, mem_Icc] at h; linarith⟩),
        show s - 2 + 1 = s - 1 by ring, Complex.ofReal_one, Complex.one_cpow]
    have hlim : Tendsto (fun b : ℝ => (1 / (k : ℂ)) * (((b : ℂ) ^ (s - 1) - 1) / (s - 1)))
        atTop (nhds (-(1 / ((k : ℂ) * (s - 1))))) := by
      rw [show -(1 / ((k : ℂ) * (s - 1))) = (1 / (k : ℂ)) * (((0 : ℂ) - 1) / (s - 1)) by
        field_simp [hkne, hs1]; ring]
      refine tendsto_const_nhds.mul ((Tendsto.sub ?_ tendsto_const_nhds).div_const _)
      refine tendsto_zero_iff_norm_tendsto_zero.mpr <|
        (tendsto_rpow_neg_atTop (by linarith : 0 < 1 - s.re)).congr' ?_
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with b hb
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hb, Complex.sub_re, Complex.one_re,
        show -(1 - s.re) = s.re - 1 by ring]
    exact hlim.congr' (hval.mono fun _ h => h.symm)
  rw [setIntegral_congr_fun measurableSet_Ioi hcongr]
  exact tendsto_nhds_unique (intervalIntegral_tendsto_integral_Ioi 1 hint tendsto_id) htend

/-- Critical-strip Mellin residual coupling for any `dirichletPoly`: on `0 < Re(s) < 1`,
`stripDefect c N s = s * (∫_{Ioc 0 1} x^(s-1) dx - ∫_{Ioi 0} (∑ c_k {1/(kx)}) x^(s-1) dx)`. -/
theorem stripDefect_eq_mul_mellin_residual (hT : TitchmarshMellinProperty)
    (c : ℕ → ℂ) (N : ℕ) {s : ℂ} (hs : 0 < s.re ∧ s.re < 1) :
    stripDefect c N s = s *
      ((∫ x in Ioc (0 : ℝ) 1, (x : ℂ) ^ (s - 1)) -
       (∫ x in Ioi (0 : ℝ),
         (∑ k ∈ Finset.Icc 1 N, c k * (recipFractScaled k x : ℂ)) *
           (x : ℂ) ^ (s - 1))) := by
  have hs0 : s ≠ 0 := fun h => by rw [h] at hs; simp at hs
  have hIoc1 : ∫ x in Ioc (0 : ℝ) 1, (x : ℂ) ^ (s - 1) = 1 / s := by
    rw [← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
      integral_cpow (Or.inl (by simp [Complex.sub_re]; linarith)),
      show s - 1 + 1 = s by ring, Complex.ofReal_one, Complex.one_cpow,
      Complex.ofReal_zero, Complex.zero_cpow hs0, sub_zero]
  have hi_ioc : ∀ k ∈ Finset.Icc 1 N, IntegrableOn
      (fun x : ℝ => c k * ((recipFractScaled k x : ℂ) * (x : ℂ) ^ (s - 1))) (Ioc 0 1) :=
    fun k _ => (integrableOn_Ioc_scaled_cpow k s hs.1).const_mul _
  have hi_ioi : ∀ k ∈ Finset.Icc 1 N, IntegrableOn
      (fun x : ℝ => c k * ((recipFractScaled k x : ℂ) * (x : ℂ) ^ (s - 1))) (Ioi 1) :=
    fun k hk => (integrableOn_Ioi_scaled_cpow k (Finset.mem_Icc.mp hk).1 hs.2).const_mul _
  have hfun : (fun x : ℝ => (∑ k ∈ Finset.Icc 1 N, c k * (recipFractScaled k x : ℂ)) *
      (x : ℂ) ^ (s - 1)) = fun x : ℝ =>
      ∑ k ∈ Finset.Icc 1 N, c k * ((recipFractScaled k x : ℂ) * (x : ℂ) ^ (s - 1)) := by
    ext x; rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun _ _ => by ring
  have hdisj : Disjoint (Ioc (0 : ℝ) 1) (Ioi (1 : ℝ)) :=
    Set.disjoint_left.mpr fun _ h1 h2 => not_lt_of_ge h1.2 h2
  have hsplit : ∫ x in Ioi (0 : ℝ),
      (∑ k ∈ Finset.Icc 1 N, c k * (recipFractScaled k x : ℂ)) * (x : ℂ) ^ (s - 1) =
      (∫ x in Ioc (0 : ℝ) 1, ∑ k ∈ Finset.Icc 1 N,
        c k * ((recipFractScaled k x : ℂ) * (x : ℂ) ^ (s - 1))) +
      (∫ x in Ioi (1 : ℝ), ∑ k ∈ Finset.Icc 1 N,
        c k * ((recipFractScaled k x : ℂ) * (x : ℂ) ^ (s - 1))) := by
    rw [hfun, ← Ioc_union_Ioi_eq_Ioi (by norm_num : (0 : ℝ) ≤ 1)]
    exact setIntegral_union hdisj measurableSet_Ioi
      (integrable_finsetSum _ hi_ioc) (integrable_finsetSum _ hi_ioi)
  have hsum : ∫ x in Ioi (0 : ℝ),
      (∑ k ∈ Finset.Icc 1 N, c k * (recipFractScaled k x : ℂ)) * (x : ℂ) ^ (s - 1) =
      -(riemannZeta s / s) * dirichletPoly c N s := by
    rw [hsplit, integral_finsetSum _ hi_ioc, integral_finsetSum _ hi_ioi,
      ← Finset.sum_add_distrib]
    trans ∑ k ∈ Finset.Icc 1 N, c k * -(riemannZeta s / (s * (k : ℂ) ^ s))
    · refine Finset.sum_congr rfl fun k hk => ?_
      rw [integral_const_mul, integral_const_mul,
        integral_Ioc_recipFractScaled_cpow_of_unit hT k (Finset.mem_Icc.mp hk).1 s hs,
        integral_Ioi_scaled_cpow k (Finset.mem_Icc.mp hk).1 hs.2]
      ring
    · unfold dirichletPoly; rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun k hk => ?_
      have hkne : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by linarith [(Finset.mem_Icc.mp hk).1])
      rw [Complex.cpow_neg]; field_simp [hkne, hs0]
  rw [hIoc1, hsum]; unfold stripDefect; field_simp [hs0]; ring
