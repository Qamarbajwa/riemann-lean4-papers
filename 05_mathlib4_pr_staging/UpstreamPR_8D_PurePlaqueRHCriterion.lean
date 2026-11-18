/-
Copyright (c) 2026 Qamar Munawer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qamar Munawer
-/
module

public import RiemannBlueprint.UpstreamPRs.UpstreamPR_5C_MellinNymanBeurlingIff
public import RiemannBlueprint.UpstreamPRs.UpstreamPR_7A_MellinKernelEnergyIdentity
public import RiemannBlueprint.UpstreamPRs.UpstreamPR_8C_PlaqueTwoDimTelescoping

/-!
# Pure Plaque Vanishing Criterion for the Riemann Hypothesis

Combines the Dirichlet-anchored (`c₁ = -1`) unit-drive `L²` identity, the 2D discrete Abel
telescoping reduction, and the Mellin weighted Cauchy–Schwarz energy floor into a direct pure
plaque criterion for `_root_.RiemannHypothesis`:

* `PurePlaqueVanishingCriterion`: Dirichlet anchoring (`c₁ = -1`), unit drive (`π * L_cot = 1`),
  and `dipolePlaqueForm (c - cBaseAnchor) N < ε`.
* `TelescopedPlaqueVanishingCriterion`: equivalent statement via the `{3, …, N}²` kernel form.
* `mellin_l2_floor_of_zeta_zero`: any off-line zero `ζ s = 0` (`1 / 2 < s.re < 1`) enforces
  `(2 * s.re - 1) / ‖s‖ ^ 2 ≤ ‖1 - ∑ c_k {1 / (k x)}‖₂²`.
* `purePlaque_floor_of_zeta_zero`: under `c₁ = -1` and `π * L_cot = 1`, any off-line zero
  enforces `(2 * s.re - 1) / ‖s‖ ^ 2 ≤ dipolePlaqueForm (c - cBaseAnchor) N`.
* `riemannHypothesis_of_purePlaque_vanishing` and
  `riemannHypothesis_of_telescoped_plaque_vanishing`.
-/

@[expose] public section

open scoped BigOperators
open MeasureTheory Set Finset

/-- Pure plaque vanishing criterion on the Dirichlet-anchored (`c₁ = -1`) unit-drive slice of
`A_N`. -/
def PurePlaqueVanishingCriterion : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ (N : ℕ) (c : ℕ → ℝ),
    2 ≤ N ∧ IsDirichletAnchored c N ∧
      Real.pi * linearCotDrive (fun k => c k - cBaseAnchor k) N = 1 ∧
      dipolePlaqueForm (fun k => c k - cBaseAnchor k) N < ε

/-- Equivalent 2D-telescoped plaque vanishing criterion on `{3, …, N}²`. -/
def TelescopedPlaqueVanishingCriterion : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ (N : ℕ) (c : ℕ → ℝ),
    2 ≤ N ∧ IsDirichletAnchored c N ∧
      Real.pi * linearCotDrive (fun k => c k - cBaseAnchor k) N = 1 ∧
      (∑ j ∈ Finset.Icc 3 N, ∑ k ∈ Finset.Icc 3 N,
        (c j * c k / ((j : ℝ) * (k : ℝ))) *
          (unweightedKCot j k - unweightedKCot j 2 - unweightedKCot 2 k)) < ε

/-- Equivalence of `PurePlaqueVanishingCriterion` and `TelescopedPlaqueVanishingCriterion`. -/
theorem purePlaqueVanishing_iff_telescoped :
    PurePlaqueVanishingCriterion ↔ TelescopedPlaqueVanishingCriterion := by
  constructor <;> intro h ε hε <;> obtain ⟨N, c, hN, hc, hd, hp⟩ := h ε hε <;>
    refine ⟨N, c, hN, hc, hd, ?_⟩
  · rwa [← dipolePlaqueForm_sub_cBaseAnchor_eq_telescoped_kernel]
  · rwa [dipolePlaqueForm_sub_cBaseAnchor_eq_telescoped_kernel]

private lemma integrableOn_cpow_loc {s : ℂ} (hs : 0 < s.re) :
    IntegrableOn (fun x : ℝ => (x : ℂ) ^ (s - 1)) (Ioc (0 : ℝ) 1) :=
  ((intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0 : ℝ) ≤ 1)).mp
    (intervalIntegral.intervalIntegrable_rpow' (by linarith : (-1 : ℝ) < s.re - 1))).mono'
    (ContinuousOn.aestronglyMeasurable (fun _ ht => (Complex.continuousAt_ofReal_cpow_const _ _
      (Or.inr ht.1.ne')).continuousWithinAt) measurableSet_Ioc)
    ((ae_restrict_mem measurableSet_Ioc).mono fun x hx => by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hx.1, Complex.sub_re, Complex.one_re])

private lemma integrableOn_scaled_cpow_loc (k : ℕ) {s : ℂ} (hs : 0 < s.re) :
    IntegrableOn (fun x : ℝ => (recipFractScaled k x : ℂ) * (x : ℂ) ^ (s - 1))
      (Ioc (0 : ℝ) 1) :=
  (integrableOn_cpow_loc hs).norm.mono'
    ((measurable_fract.comp (measurable_const.div (measurable_const.mul
      measurable_id))).complex_ofReal.aestronglyMeasurable.restrict.mul
      (ContinuousOn.aestronglyMeasurable (fun _ ht => (Complex.continuousAt_ofReal_cpow_const _ _
        (Or.inr ht.1.ne')).continuousWithinAt) measurableSet_Ioc))
    ((ae_restrict_mem measurableSet_Ioc).mono fun x _ => by
      dsimp only [recipFractScaled]
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Int.fract_nonneg _)]
      exact mul_le_of_le_one_left (norm_nonneg _) (Int.fract_lt_one _).le)

private lemma integral_Ioc_cpow_loc {s : ℂ} (hs : 0 < s.re) :
    ∫ x in Ioc (0 : ℝ) 1, (x : ℂ) ^ (s - 1) = 1 / s := by
  have hs0 : s ≠ 0 := fun h => by rw [h] at hs; simp at hs
  rw [← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
    integral_cpow (Or.inl (by simp [Complex.sub_re]; linarith)), show s - 1 + 1 = s by ring,
    Complex.ofReal_one, Complex.one_cpow, Complex.ofReal_zero, Complex.zero_cpow hs0, sub_zero]

private lemma integral_Ioc_residual_cpow_eq (hT : TitchmarshMellinProperty) (c : ℕ → ℝ) (N : ℕ)
    (hc1 : D1 c N = 0) {s : ℂ} (hs : 0 < s.re ∧ s.re < 1) (hz : riemannZeta s = 0) :
    ∫ x in Ioc (0 : ℝ) 1,
      ((1 - ∑ k ∈ Finset.Icc 1 N, c k * recipFractScaled k x : ℝ) : ℂ) * (x : ℂ) ^ (s - 1) =
        1 / s := by
  have hs1 : s - 1 ≠ 0 := sub_ne_zero.mpr fun h => by rw [h] at hs; norm_num at hs
  have hterm : ∀ k ∈ Finset.Icc 1 N, IntegrableOn (fun x : ℝ => (c k : ℂ) *
      ((recipFractScaled k x : ℂ) * (x : ℂ) ^ (s - 1))) (Ioc 0 1) :=
    fun k _ => (integrableOn_scaled_cpow_loc k hs.1).const_mul _
  have hsplit : (fun x : ℝ => ((1 - ∑ k ∈ Finset.Icc 1 N, c k * recipFractScaled k x : ℝ) : ℂ) *
      (x : ℂ) ^ (s - 1)) = fun x : ℝ => (x : ℂ) ^ (s - 1) - ∑ k ∈ Finset.Icc 1 N,
        (c k : ℂ) * ((recipFractScaled k x : ℂ) * (x : ℂ) ^ (s - 1)) := by
    ext x; push_cast; rw [sub_mul, one_mul, Finset.sum_mul]
    congr 1; exact Finset.sum_congr rfl fun k _ => by ring
  rw [hsplit, integral_sub (integrableOn_cpow_loc hs.1) (integrable_finsetSum _ hterm),
    integral_Ioc_cpow_loc hs.1, integral_finsetSum _ hterm]
  have hpt : ∀ k ∈ Finset.Icc 1 N, ∫ x in Ioc (0 : ℝ) 1, (c k : ℂ) *
      ((recipFractScaled k x : ℂ) * (x : ℂ) ^ (s - 1)) = (1 / (s - 1)) * ((c k : ℂ) / k) := by
    intro k hk
    have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hk).1
    have hkne : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    rw [integral_const_mul, integral_Ioc_recipFractScaled_cpow_of_unit hT k hk1 s hs, hz,
      zero_div, sub_zero]
    field_simp [hkne, hs1]
  rw [Finset.sum_congr rfl hpt, ← Finset.mul_sum]
  have hD1C : ∑ k ∈ Finset.Icc 1 N, (c k : ℂ) / (k : ℂ) = 0 := by
    have hcast : ∑ k ∈ Finset.Icc 1 N, (c k : ℂ) / (k : ℂ) = ((D1 c N : ℝ) : ℂ) := by
      unfold D1; push_cast; rfl
    rw [hcast, hc1, Complex.ofReal_zero]
  rw [hD1C, mul_zero, sub_zero]

private lemma measurable_residual (c : ℕ → ℝ) (N : ℕ) :
    Measurable fun x : ℝ => 1 - ∑ k ∈ Finset.Icc 1 N, c k * recipFractScaled k x :=
  measurable_const.sub (Finset.measurable_sum _ fun _ _ =>
    (measurable_fract.comp (measurable_const.div (measurable_const.mul measurable_id))).const_mul _)

private lemma abs_residual_le (c : ℕ → ℝ) (N : ℕ) (x : ℝ) :
    |1 - ∑ k ∈ Finset.Icc 1 N, c k * recipFractScaled k x| ≤ 1 + ∑ k ∈ Finset.Icc 1 N, |c k| := by
  have h1 : |∑ k ∈ Finset.Icc 1 N, c k * recipFractScaled k x| ≤ ∑ k ∈ Finset.Icc 1 N, |c k| := by
    refine (abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k _ => ?_)
    dsimp only [recipFractScaled]
    rw [abs_mul, abs_of_nonneg (Int.fract_nonneg (1 / ((k : ℝ) * x)))]
    exact mul_le_of_le_one_right (abs_nonneg _) (Int.fract_lt_one _).le
  have h2 := abs_sub (1 : ℝ) (∑ k ∈ Finset.Icc 1 N, c k * recipFractScaled k x)
  rw [abs_one] at h2
  linarith

/-- Unconditional Mellin `L²(0, 1)` energy floor forced by any zero `ζ s = 0` in
`1 / 2 < Re(s) < 1`. -/
theorem mellin_l2_floor_of_zeta_zero (hT : TitchmarshMellinProperty) (c : ℕ → ℝ) (N : ℕ)
    (hc1 : D1 c N = 0) {s : ℂ} (hs_lo : 1 / 2 < s.re) (hs_hi : s.re < 1) (hz : riemannZeta s = 0) :
    (2 * s.re - 1) / ‖s‖ ^ 2 ≤
      ∫ x in (0 : ℝ)..1, (1 - ∑ k ∈ Finset.Icc 1 N, c k * recipFractScaled k x) ^ 2 := by
  have hs_pos : 0 < s.re := by linarith
  have hw_pos : 0 < 2 * s.re - 1 := by linarith
  have hsn : 0 < ‖s‖ := norm_pos_iff.mpr fun h => by rw [h] at hs_pos; simp at hs_pos
  let g : ℝ → ℝ := fun x => 1 - ∑ k ∈ Finset.Icc 1 N, c k * recipFractScaled k x
  let B : ℝ := 1 + ∑ k ∈ Finset.Icc 1 N, |c k|
  have hnorm_eq : 1 / ‖s‖ = ‖∫ x in Ioc (0 : ℝ) 1, (g x : ℂ) * (x : ℂ) ^ (s - 1)‖ := by
    rw [integral_Ioc_residual_cpow_eq hT c N hc1 ⟨hs_pos, hs_hi⟩ hz, norm_div, norm_one]
  have hle_int : ‖∫ x in Ioc (0 : ℝ) 1, (g x : ℂ) * (x : ℂ) ^ (s - 1)‖ ≤
      ∫ x in Ioc (0 : ℝ) 1, |g x| * x ^ (s.re - 1) := by
    refine (norm_integral_le_integral_norm _).trans_eq
      (setIntegral_congr_fun measurableSet_Ioc fun x hx => ?_)
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      Complex.norm_cpow_eq_rpow_re_of_pos hx.1, Complex.sub_re, Complex.one_re]
  have hg2 : IntegrableOn (fun x : ℝ => g x ^ 2) (Ioc (0 : ℝ) 1) :=
    ((integrableOn_const (C := B ^ 2) (hs := measure_Ioc_lt_top.ne)).mono'
      ((measurable_residual c N).pow_const 2).aestronglyMeasurable.restrict
      ((ae_restrict_mem measurableSet_Ioc).mono fun x _ => by
        rw [Real.norm_of_nonneg (sq_nonneg _), ← sq_abs]
        exact sq_le_sq' (by linarith [abs_nonneg (g x), abs_residual_le c N x])
          (abs_residual_le c N x)))
  have hmg : IntegrableOn (fun x : ℝ => |g x| * x ^ (s.re - 1)) (Ioc (0 : ℝ) 1) := by
    refine ((integrableOn_cpow_loc hs_pos).norm.const_mul B).mono'
      (((continuous_abs.measurable.comp (measurable_residual c N)).mul
        (measurable_id.pow_const (s.re - 1))).aestronglyMeasurable.restrict)
      ((ae_restrict_mem measurableSet_Ioc).mono fun x hx => ?_)
    rw [Real.norm_of_nonneg (mul_nonneg (abs_nonneg _) (Real.rpow_nonneg hx.1.le _)),
      Complex.norm_cpow_eq_rpow_re_of_pos hx.1, Complex.sub_re, Complex.one_re]
    exact mul_le_mul_of_nonneg_right (abs_residual_le c N x) (Real.rpow_nonneg hx.1.le _)
  let a : ℝ := ‖s‖ / (2 * s.re - 1) ^ 2
  have hscaled := integral_Ioc_two_mul_mellin_le (fun x => a * |g x|) hs_lo
    (IntegrableOn.congr_fun (hg2.const_mul (a ^ 2)) (fun x _ => by rw [mul_pow, sq_abs])
      measurableSet_Ioc)
    (IntegrableOn.congr_fun (hmg.const_mul a) (fun x _ => by ring) measurableSet_Ioc)
  have hlhs : 2 * ∫ x in Ioc (0 : ℝ) 1, (a * |g x|) * x ^ (s.re - 1) =
      2 * a * ∫ x in Ioc (0 : ℝ) 1, |g x| * x ^ (s.re - 1) := by
    rw [← integral_const_mul, ← integral_const_mul]
    exact setIntegral_congr_fun measurableSet_Ioc fun x _ => by ring
  have hrhs : ∫ x in Ioc (0 : ℝ) 1, (a * |g x|) ^ 2 = a ^ 2 * ∫ x in Ioc (0 : ℝ) 1, g x ^ 2 := by
    rw [← integral_const_mul]
    exact setIntegral_congr_fun measurableSet_Ioc fun x _ => by rw [mul_pow, sq_abs]
  rw [hlhs, hrhs] at hscaled
  have h2a_le : 2 * (1 / (2 * s.re - 1) ^ 2) ≤
      2 * a * ∫ x in Ioc (0 : ℝ) 1, |g x| * x ^ (s.re - 1) := by
    have hmul := mul_le_mul_of_nonneg_left (hnorm_eq ▸ hle_int)
      (mul_nonneg (by norm_num) (div_nonneg hsn.le (sq_nonneg _)) : 0 ≤ 2 * a)
    rw [show 2 * a * (1 / ‖s‖) = 2 * (1 / (2 * s.re - 1) ^ 2) by
      dsimp only [a]; field_simp [hsn.ne', hw_pos.ne']] at hmul
    exact hmul
  have hineq : 1 / (2 * s.re - 1) ^ 2 ≤ (2 * s.re - 1) * a ^ 2 * ∫ x in (0 : ℝ)..1, g x ^ 2 := by
    rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    have : (2 * s.re - 1) * (a ^ 2 * ∫ x in Ioc (0 : ℝ) 1, g x ^ 2) =
        (2 * s.re - 1) * a ^ 2 * ∫ x in Ioc (0 : ℝ) 1, g x ^ 2 := by ring
    linarith
  rw [show (2 * s.re - 1) * a ^ 2 = ‖s‖ ^ 2 / (2 * s.re - 1) ^ 3 by
    dsimp only [a]; field_simp [hw_pos.ne']] at hineq
  have hfinal := mul_le_mul_of_nonneg_left hineq
    (div_nonneg (pow_nonneg hw_pos.le 3) (sq_nonneg ‖s‖))
  rwa [show (2 * s.re - 1) ^ 3 / ‖s‖ ^ 2 * (1 / (2 * s.re - 1) ^ 2) = (2 * s.re - 1) / ‖s‖ ^ 2 by
      field_simp [hw_pos.ne', hsn.ne'],
    show (2 * s.re - 1) ^ 3 / ‖s‖ ^ 2 *
      (‖s‖ ^ 2 / (2 * s.re - 1) ^ 3 * ∫ x in (0 : ℝ)..1, g x ^ 2) =
      ∫ x in (0 : ℝ)..1, g x ^ 2 by field_simp [hw_pos.ne', hsn.ne']] at hfinal

/-- On the Dirichlet-anchored (`c₁ = -1`) unit-drive (`π * L_cot = 1`) locus, any off-line zero
`ζ s = 0` (`1 / 2 < s.re < 1`) enforces a strict positive plaque floor. -/
theorem purePlaque_floor_of_zeta_zero (hT : TitchmarshMellinProperty) {N : ℕ} (hN : 2 ≤ N)
    {c : ℕ → ℝ} (hc : IsDirichletAnchored c N)
    (hd : Real.pi * linearCotDrive (fun k => c k - cBaseAnchor k) N = 1)
    {s : ℂ} (hs_lo : 1 / 2 < s.re) (hs_hi : s.re < 1) (hz : riemannZeta s = 0) :
    (2 * s.re - 1) / ‖s‖ ^ 2 ≤ dipolePlaqueForm (fun k => c k - cBaseAnchor k) N := by
  rw [unit_drive_dirichlet_plaque_eq_l2_dist hN hc hd]
  exact mellin_l2_floor_of_zeta_zero hT c N hc.1 hs_lo hs_hi hz

/-- **Pure Plaque Vanishing Criterion for the Riemann Hypothesis**. -/
theorem riemannHypothesis_of_purePlaque_vanishing (hT : TitchmarshMellinProperty)
    (h_plaque : PurePlaqueVanishingCriterion) : _root_.RiemannHypothesis := by
  intro s₀ hz hnt h1
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
  have hδ : 0 < (2 * w.re - 1) / ‖w‖ ^ 2 := div_pos (by linarith)
    (sq_pos_of_pos (norm_pos_iff.mpr fun h => by rw [h] at hwlo; norm_num at hwlo))
  obtain ⟨N, c, hN, hc, hd, hp⟩ := h_plaque _ hδ
  linarith [purePlaque_floor_of_zeta_zero hT hN hc hd hwlo hwhi hwz]

/-- **Telescoped Kernel Vanishing Criterion for the Riemann Hypothesis**. -/
theorem riemannHypothesis_of_telescoped_plaque_vanishing (hT : TitchmarshMellinProperty)
    (h_tel : TelescopedPlaqueVanishingCriterion) : _root_.RiemannHypothesis :=
  riemannHypothesis_of_purePlaque_vanishing hT (purePlaqueVanishing_iff_telescoped.mpr h_tel)
