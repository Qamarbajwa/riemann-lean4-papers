/-
Copyright (c) 2026 Qamar Munawer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qamar Munawer
-/
module

public import Mathlib.Analysis.PSeriesComplex
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.MeasureTheory.Function.Floor
public import Mathlib.NumberTheory.ArithmeticFunction.Moebius
public import RiemannBlueprint.UpstreamPRs.UpstreamPR_3A_VasyuninIntegral
public import RiemannBlueprint.UpstreamPRs.UpstreamPR_4A_AffineLagrangeProjection
public import RiemannBlueprint.UpstreamPRs.UpstreamPR_5A_ZetaLogDerivHolomorphy

/-!
# Bidirectional Mellin-Space Nyman–Beurling Equivalence in the Critical Strip
Formalizes `integral_Ioo_moebius_recipFract_eq`,
`tendsto_mellin_moebius_recipFract_of_riemannHypothesis`, and
`riemannHypothesis_iff_mellin_recipFract_approx` on `0 < Re(s) < 1`.
-/

@[expose] public section

open MeasureTheory Set Filter

/-- Titchmarsh's Mellin fractional-part identity on `(0, 1]` for `0 < Re(s) < 1`. -/
def TitchmarshMellinProperty : Prop :=
  ∀ s : ℂ, 0 < s.re → s.re < 1 →
    ∫ x in Ioc (0 : ℝ) 1, (recipFract x : ℂ) * (x : ℂ) ^ (s - 1) = 1 / (s - 1) - riemannZeta s / s

private lemma integrableOn_Ioc_cpow {s : ℂ} (hs : 0 < s.re) :
    IntegrableOn (fun x : ℝ => (x : ℂ) ^ (s - 1)) (Ioc (0 : ℝ) 1) :=
  ((intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0 : ℝ) ≤ 1)).mp
    (intervalIntegral.intervalIntegrable_rpow' (by linarith : (-1 : ℝ) < s.re - 1))).mono'
    (ContinuousOn.aestronglyMeasurable (fun _ ht => (Complex.continuousAt_ofReal_cpow_const _ _
      (Or.inr ht.1.ne')).continuousWithinAt) measurableSet_Ioc)
    ((ae_restrict_mem measurableSet_Ioc).mono fun x hx => by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hx.1, Complex.sub_re, Complex.one_re])

private lemma integrableOn_Ioc_recipFractScaled_cpow (k : ℕ) (s : ℂ) (hs : 0 < s.re) :
    IntegrableOn (fun x : ℝ => (recipFractScaled k x : ℂ) * (x : ℂ) ^ (s - 1))
      (Ioc (0 : ℝ) 1) := by
  have hm : Measurable (recipFractScaled k) :=
    measurable_fract.comp (measurable_const.div (measurable_const.mul measurable_id))
  refine (integrableOn_Ioc_cpow hs).norm.mono' (hm.complex_ofReal.aestronglyMeasurable.restrict.mul
    (ContinuousOn.aestronglyMeasurable (fun _ ht => (Complex.continuousAt_ofReal_cpow_const _ _
      (Or.inr ht.1.ne')).continuousWithinAt) measurableSet_Ioc))
    ((ae_restrict_mem measurableSet_Ioc).mono fun x _ => by
      dsimp only [recipFractScaled]
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Int.fract_nonneg _)]
      exact mul_le_of_le_one_left (norm_nonneg _) (Int.fract_lt_one _).le)

private lemma integral_Ioc_cpow_eq_one_div (s : ℂ) (hs : 0 < s.re) :
    ∫ x in Ioc (0 : ℝ) 1, (x : ℂ) ^ (s - 1) = 1 / s := by
  have hs0 : s ≠ 0 := fun h => by rw [h] at hs; simp at hs
  rw [← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
    integral_cpow (Or.inl (by simp [Complex.sub_re]; linarith)), show s - 1 + 1 = s by ring,
    Complex.ofReal_one, Complex.one_cpow, Complex.ofReal_zero, Complex.zero_cpow hs0, sub_zero]

/-- Exact scaling formula for `∫_{0}^1 {1/(kx)} x^{s-1} dx` on `0 < Re(s) < 1`. -/
lemma integral_Ioc_recipFractScaled_cpow_of_unit (hT : TitchmarshMellinProperty)
    (k : ℕ) (hk : 1 ≤ k) (s : ℂ) (hs : 0 < s.re ∧ s.re < 1) :
    ∫ x in Ioc (0 : ℝ) 1, (recipFractScaled k x : ℂ) * (x : ℂ) ^ (s - 1) =
      1 / ((k : ℂ) * (s - 1)) - riemannZeta s / (s * (k : ℂ) ^ s) := by
  have hkp : (0 : ℝ) < k := Nat.cast_pos.mpr hk
  have hkne : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hk1 : (1 : ℝ) / k ≤ 1 := div_le_one_of_le₀ (Nat.one_le_cast.mpr hk) hkp.le
  have hint := integrableOn_Ioc_recipFractScaled_cpow k s hs.1
  have hsp := intervalIntegral.integral_add_adjacent_intervals
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (by positivity : (0 : ℝ) ≤ 1 / k) |>.mpr
      (hint.mono_set (Ioc_subset_Ioc_right hk1)))
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hk1 |>.mpr
      (hint.mono_set (Ioc_subset_Ioc_left (by positivity))))
  simp only [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
    intervalIntegral.integral_of_le (by positivity : (0 : ℝ) ≤ 1 / k),
    intervalIntegral.integral_of_le hk1] at hsp
  have hlo : ∫ x in Ioc (0 : ℝ) (1 / k), (recipFractScaled k x : ℂ) * (x : ℂ) ^ (s - 1) =
      (k : ℂ) ^ (-s) * ∫ u in Ioc (0 : ℝ) 1, (recipFract u : ℂ) * (u : ℂ) ^ (s - 1) := by
    have hsc := intervalIntegral.integral_comp_mul_left
      (fun u : ℝ => (recipFract u : ℂ) * (u : ℂ) ^ (s - 1)) hkp.ne' (a := 0) (b := 1 / k)
    rw [mul_zero, mul_one_div_cancel hkp.ne', Complex.real_smul, Complex.ofReal_inv,
      Complex.ofReal_natCast, intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
      intervalIntegral.integral_of_le (by positivity : (0 : ℝ) ≤ 1 / k)] at hsc
    have hpt : (∫ x in Ioc (0 : ℝ) (1 / k), (recipFract ((k : ℝ) * x) : ℂ) *
        (((k : ℝ) * x : ℝ) : ℂ) ^ (s - 1)) = (k : ℂ) ^ (s - 1) *
        ∫ x in Ioc (0 : ℝ) (1 / k), (recipFractScaled k x : ℂ) * (x : ℂ) ^ (s - 1) := by
      rw [← integral_const_mul]; refine setIntegral_congr_fun measurableSet_Ioc fun x hx => ?_
      have hcp : (((k : ℝ) * x : ℝ) : ℂ) ^ (s - 1) = (k : ℂ) ^ (s - 1) * (x : ℂ) ^ (s - 1) := by
        push_cast; exact Complex.mul_cpow_ofReal_nonneg hkp.le hx.1.le (s - 1)
      dsimp only [recipFractScaled, recipFract]; rw [hcp]; ring
    have hks : (k : ℂ) ^ (s - 1) * (k : ℂ) = (k : ℂ) ^ s := by
      conv_rhs => rw [show s = s - 1 + 1 by ring, Complex.cpow_add _ _ hkne, Complex.cpow_one]
    rw [hpt, ← eq_inv_mul_iff_mul_eq₀ (Complex.cpow_ne_zero_iff.mpr (Or.inl hkne))] at hsc
    rw [hsc, Complex.cpow_neg, ← mul_assoc, ← mul_inv, hks]
  have hhi : ∫ x in Ioc (1 / (k : ℝ)) 1, (recipFractScaled k x : ℂ) * (x : ℂ) ^ (s - 1) =
      (1 / (k : ℂ)) * (((1 : ℂ) - (k : ℂ) ^ (1 - s)) / (s - 1)) := by
    have hcongr : Set.EqOn (fun x : ℝ => (recipFractScaled k x : ℂ) * (x : ℂ) ^ (s - 1))
        (fun x : ℝ => (1 / (k : ℂ)) * (x : ℂ) ^ (s - 2)) (Ioc (1 / k) 1) := fun x hx => by
      have hkx : 1 < (k : ℝ) * x := by
        have := mul_lt_mul_of_pos_left hx.1 hkp; rwa [mul_one_div_cancel hkp.ne'] at this
      dsimp only [recipFractScaled]
      rw [Int.fract_eq_self.mpr ⟨by positivity, (div_lt_one (by positivity)).mpr hkx⟩]
      have hx0 : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (lt_trans (by positivity) hx.1).ne'
      rw [show s - 2 = s - 1 + (-1 : ℂ) by ring, Complex.cpow_add _ _ hx0, Complex.cpow_neg_one]
      push_cast; ring
    rw [setIntegral_congr_fun measurableSet_Ioc hcongr, integral_const_mul,
      ← intervalIntegral.integral_of_le hk1, integral_cpow (Or.inr ⟨fun h => by
        have := congr_arg Complex.re h; simp at this; linarith,
        fun h => by rw [uIcc_of_le hk1, mem_Icc] at h; linarith [div_pos one_pos hkp]⟩),
      show s - 2 + 1 = s - 1 by ring, Complex.ofReal_one, Complex.one_cpow, Complex.ofReal_div,
      Complex.ofReal_one, Complex.ofReal_natCast, _root_.one_div, Complex.inv_cpow _ _ (by
        rw [← Complex.ofReal_natCast, Complex.arg_ofReal_of_nonneg hkp.le]
        exact Real.pi_ne_zero.symm), ← Complex.cpow_neg, show -(s - 1) = 1 - s by ring]
  rw [← hsp, hlo, hhi, hT s hs.1 hs.2, Complex.cpow_neg]
  have hs0 : s ≠ 0 := fun h => by rw [h] at hs; simp at hs
  have hs1 : s - 1 ≠ 0 := sub_ne_zero.mpr fun h => by rw [h] at hs; norm_num at hs
  have hks : (k : ℂ) ^ s * (k : ℂ) ^ (1 - s) = (k : ℂ) := by
    rw [← Complex.cpow_add _ _ hkne, show s + (1 - s) = 1 by ring, Complex.cpow_one]
  field_simp [hkne, hs0, hs1, Complex.cpow_ne_zero_iff.mpr (Or.inl hkne)]
  rw [show (k : ℂ) ^ s * s * (1 - (k : ℂ) ^ (1 - s)) = s * ((k : ℂ) ^ s - (k : ℂ) ^ s *
    (k : ℂ) ^ (1 - s)) by ring, hks]; ring

/-- Closed-form Mellin transform of the explicit Möbius sawtooth residual on `(0, 1)`. -/
theorem integral_Ioo_moebius_recipFract_eq (hT : TitchmarshMellinProperty)
    (s : ℂ) (hs : 0 < s.re ∧ s.re < 1) (N : ℕ) :
    ∫ x : ℝ in Ioo 0 1, (1 + ∑ k ∈ Finset.Icc 1 N, (ArithmeticFunction.moebius k : ℂ) *
        (recipFractScaled k x : ℂ)) * (x : ℂ) ^ (s - 1) =
      (1 / s) * (1 - riemannZeta s * ∑ k ∈ Finset.Icc 1 N,
        (ArithmeticFunction.moebius k : ℂ) / (k : ℂ) ^ s) +
      (1 / (s - 1)) * ∑ k ∈ Finset.Icc 1 N, (ArithmeticFunction.moebius k : ℂ) / (k : ℂ) := by
  have hs0 : s ≠ 0 := fun h => by rw [h] at hs; simp at hs
  have hs1 : s - 1 ≠ 0 := sub_ne_zero.mpr fun h => by rw [h] at hs; norm_num at hs
  have hterm : ∀ k ∈ Finset.Icc 1 N, IntegrableOn (fun x : ℝ => (ArithmeticFunction.moebius k : ℂ) *
      ((recipFractScaled k x : ℂ) * (x : ℂ) ^ (s - 1))) (Ioc 0 1) :=
    fun k _ => (integrableOn_Ioc_recipFractScaled_cpow k s hs.1).const_mul _
  rw [setIntegral_congr_set Ioo_ae_eq_Ioc, show (fun x : ℝ => (1 + ∑ k ∈ Finset.Icc 1 N,
      (ArithmeticFunction.moebius k : ℂ) * (recipFractScaled k x : ℂ)) * (x : ℂ) ^ (s - 1)) =
      fun x : ℝ => (x : ℂ) ^ (s - 1) + ∑ k ∈ Finset.Icc 1 N, (ArithmeticFunction.moebius k : ℂ) *
        ((recipFractScaled k x : ℂ) * (x : ℂ) ^ (s - 1)) from by
      ext x; rw [add_mul, one_mul, Finset.sum_mul]; congr 1
      exact Finset.sum_congr rfl fun k _ => by ring,
    integral_add (integrableOn_Ioc_cpow hs.1) (integrable_finsetSum _ hterm),
    integral_Ioc_cpow_eq_one_div s hs.1, integral_finsetSum _ hterm]
  have hsum : ∑ k ∈ Finset.Icc 1 N, ∫ x in Ioc (0 : ℝ) 1, (ArithmeticFunction.moebius k : ℂ) *
      ((recipFractScaled k x : ℂ) * (x : ℂ) ^ (s - 1)) = (1 / (s - 1)) * ∑ k ∈ Finset.Icc 1 N,
      (ArithmeticFunction.moebius k : ℂ) / (k : ℂ) - (riemannZeta s / s) *
      ∑ k ∈ Finset.Icc 1 N, (ArithmeticFunction.moebius k : ℂ) / (k : ℂ) ^ s := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hkne : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by linarith [(Finset.mem_Icc.mp hk).1])
    rw [integral_const_mul, integral_Ioc_recipFractScaled_cpow_of_unit hT k
      (Finset.mem_Icc.mp hk).1 s hs]
    field_simp [hkne, hs1, hs0, Complex.cpow_ne_zero_iff.mpr (Or.inl hkne)]
  rw [hsum]; ring

/-- Converse Mellin limit: under `RiemannHypothesis`, Titchmarsh's identity, and Dirichlet inverse
convergence of `∑ μ(k)/k^s` and `∑ μ(k)/k`, the Mellin residual tends to `0`. -/
theorem tendsto_mellin_moebius_recipFract_of_riemannHypothesis
    (hT : TitchmarshMellinProperty) (hRH : _root_.RiemannHypothesis)
    (h_cpow : ∀ {s : ℂ}, 1 / 2 < s.re → s ≠ 1 → Tendsto
      (fun N : ℕ => ∑ k ∈ Finset.Icc 1 N, (ArithmeticFunction.moebius k : ℂ) / (k : ℂ) ^ s)
      atTop (nhds (riemannZeta s)⁻¹))
    (h_div : Tendsto (fun N : ℕ =>
      ∑ k ∈ Finset.Icc 1 N, (ArithmeticFunction.moebius k : ℂ) / (k : ℂ)) atTop (nhds 0))
    {s : ℂ} (hs_lo : 1 / 2 < s.re) (hs_hi : s.re < 1) :
    Tendsto (fun N : ℕ => ∫ x : ℝ in Ioo 0 1, (1 + ∑ k ∈ Finset.Icc 1 N,
      (ArithmeticFunction.moebius k : ℂ) * (recipFractScaled k x : ℂ)) * (x : ℂ) ^ (s - 1))
      atTop (nhds 0) := by
  have hs1 : s ≠ 1 := fun h => by rw [h] at hs_hi; simp at hs_hi
  have hz : riemannZeta s ≠ 0 := fun h => by
    have hnt : ¬∃ n : ℕ, s = -2 * (n + 1) := fun ⟨n, hn⟩ => by
      have := congr_arg Complex.re hn; simp at this; linarith [Nat.cast_nonneg (α := ℝ) n]
    linarith [hRH s h hnt hs1]
  have h1 := ((tendsto_const_nhds (x := (1 : ℂ))).sub
    ((h_cpow hs_lo hs1).const_mul (riemannZeta s))).const_mul (1 / s)
  rw [mul_inv_cancel₀ hz, sub_self, mul_zero] at h1
  have h2 := h_div.const_mul (1 / (s - 1)); rw [mul_zero] at h2
  have hadd := h1.add h2; rw [add_zero] at hadd
  exact hadd.congr fun N => (integral_Ioo_moebius_recipFract_eq hT s ⟨by linarith, hs_hi⟩ N).symm

/-- Bidirectional Mellin-space Nyman–Beurling equivalence for `_root_.RiemannHypothesis`. -/
theorem riemannHypothesis_iff_mellin_recipFract_approx (hT : TitchmarshMellinProperty)
    (h_conj : ∀ s : ℂ, 0 < s.re → s ≠ 1 → riemannZeta (starRingEnd ℂ s) =
      starRingEnd ℂ (riemannZeta s))
    (h_cpow : _root_.RiemannHypothesis → ∀ {s : ℂ}, 1 / 2 < s.re → s ≠ 1 → Tendsto
      (fun N : ℕ => ∑ k ∈ Finset.Icc 1 N, (ArithmeticFunction.moebius k : ℂ) / (k : ℂ) ^ s)
      atTop (nhds (riemannZeta s)⁻¹))
    (h_div : _root_.RiemannHypothesis → Tendsto (fun N : ℕ =>
      ∑ k ∈ Finset.Icc 1 N, (ArithmeticFunction.moebius k : ℂ) / (k : ℂ)) atTop (nhds 0)) :
    _root_.RiemannHypothesis ↔ ∀ s : ℂ, 1 / 2 < s.re → s.re < 1 → Tendsto (fun N : ℕ =>
      ∫ x : ℝ in Ioo 0 1, (1 + ∑ k ∈ Finset.Icc 1 N, (ArithmeticFunction.moebius k : ℂ) *
        (recipFractScaled k x : ℂ)) * (x : ℂ) ^ (s - 1)) atTop (nhds 0) := by
  refine ⟨fun hRH s => tendsto_mellin_moebius_recipFract_of_riemannHypothesis hT hRH
    (h_cpow hRH) (h_div hRH), fun hm s₀ hz hnt h1 => ?_⟩
  by_contra hne
  have hs_lt : s₀.re < 1 := by
    by_contra hge; exact riemannZeta_ne_zero_of_one_le_re (not_lt.mp hge) hz
  have hs_pos : 0 < s₀.re := by
    by_contra hle; push Not at hle
    exact riemannZeta_ne_zero_of_one_le_re (by rw [Complex.sub_re, Complex.one_re]; linarith)
      (riemannZeta_zero_reflection_of_re_lt_half hz hnt h1 (by linarith)).1
  obtain ⟨w, hwlo, hwhi, hwz⟩ : ∃ w : ℂ, 1 / 2 < w.re ∧ w.re < 1 ∧ riemannZeta w = 0 := by
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have hr := riemannZeta_zero_reflection_of_re_lt_half hz hnt h1 hlt
      exact ⟨1 - s₀, hr.2, by rw [Complex.sub_re, Complex.one_re]; linarith, hr.1⟩
    · exact ⟨s₀, hgt, hs_lt, hz⟩
  have hwp : 0 < w.re := by linarith
  have hw0 : w ≠ 0 := fun h => by rw [h] at hwp; simp at hwp
  have hw1 : w - 1 ≠ 0 := sub_ne_zero.mpr fun h => by rw [h] at hwhi; simp at hwhi
  have hcw1 : starRingEnd ℂ w ≠ 1 := fun h => by
    have := congr_arg Complex.re h; simp at this; linarith
  have hcwz : riemannZeta (starRingEnd ℂ w) = 0 := by
    rw [h_conj w hwp (sub_ne_zero.mp hw1), hwz, map_zero]
  have step (z : ℂ) (hzp : 0 < z.re) (hzh : z.re < 1) (hz0 : z ≠ 0) (hz1 : z - 1 ≠ 0)
      (hzz : riemannZeta z = 0) (hzt : Tendsto (fun N : ℕ => ∫ x : ℝ in Ioo 0 1,
        (1 + ∑ k ∈ Finset.Icc 1 N, (ArithmeticFunction.moebius k : ℂ) *
          (recipFractScaled k x : ℂ)) * (x : ℂ) ^ (z - 1)) atTop (nhds 0)) :
      Tendsto (fun N : ℕ => ∑ k ∈ Finset.Icc 1 N, (ArithmeticFunction.moebius k : ℂ) / (k : ℂ))
        atTop (nhds (1 / z - 1)) := by
    have hmul := ((hzt.congr fun N => by rw [integral_Ioo_moebius_recipFract_eq hT z ⟨hzp, hzh⟩ N,
      hzz, zero_mul, sub_zero, mul_one]).sub (tendsto_const_nhds (x := 1 / z))).const_mul (z - 1)
    rw [zero_sub, show (z - 1) * -(1 / z) = 1 / z - 1 from by field_simp [hz0]; ring] at hmul
    exact hmul.congr fun N => by
      simp only [add_sub_cancel_left]; rw [← mul_assoc, mul_one_div_cancel hz1, one_mul]
  have heq := tendsto_nhds_unique (step w hwp hwhi hw0 hw1 hwz (hm w hwlo hwhi))
    (step (starRingEnd ℂ w) (by simpa using hwp) (by simpa using hwhi)
      (fun h => hw0 (by simpa using congr_arg (starRingEnd ℂ) h)) (sub_ne_zero.mpr hcw1) hcwz
      (hm (starRingEnd ℂ w) (by simpa using hwlo) (by simpa using hwhi)))
  have him_z : w.im = 0 := by
    have hinv : w = starRingEnd ℂ w := by
      have : (1 / w : ℂ) = 1 / starRingEnd ℂ w := by linear_combination heq
      simpa using congrArg Inv.inv this
    have := congr_arg Complex.im hinv; simp only [Complex.conj_im] at this; linarith
  have hreal : w = (w.re : ℂ) := Complex.ext rfl him_z
  have htu := hT w hwp hwhi; rw [hwz, zero_div, sub_zero] at htu
  have hre : (∫ x in Ioc (0 : ℝ) 1, (recipFract x : ℂ) * (x : ℂ) ^ (w - 1)).re =
      ∫ x in Ioc (0 : ℝ) 1, recipFract x * x ^ (w.re - 1) := by
    have hi : IntegrableOn (fun x : ℝ => (recipFract x : ℂ) * (x : ℂ) ^ (w - 1)) (Ioc 0 1) := by
      simpa [recipFract, recipFractScaled] using integrableOn_Ioc_recipFractScaled_cpow 1 w hwp
    conv_lhs => rw [← Complex.reCLM_apply, ← ContinuousLinearMap.integral_comp_comm _ hi]
    refine setIntegral_congr_fun measurableSet_Ioc fun x hx => ?_
    rw [Complex.reCLM_apply, hreal, ← Complex.ofReal_one, ← Complex.ofReal_sub,
      ← Complex.ofReal_cpow hx.1.le, ← Complex.ofReal_mul, Complex.ofReal_re, Complex.ofReal_re]
  have hpos : 0 ≤ ∫ x in Ioc (0 : ℝ) 1, recipFract x * x ^ (w.re - 1) :=
    setIntegral_nonneg measurableSet_Ioc fun x hx =>
      mul_nonneg (Int.fract_nonneg _) (Real.rpow_nonneg hx.1.le _)
  have hval := congr_arg Complex.re htu
  rw [hre, show (1 / (w - 1)).re = 1 / (w.re - 1) from by rw [hreal]; norm_cast] at hval
  linarith [div_neg_of_pos_of_neg one_pos (by linarith : w.re - 1 < 0)]
