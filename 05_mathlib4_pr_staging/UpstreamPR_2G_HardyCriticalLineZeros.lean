/-
Copyright (c) 2026 Qamar Munawer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qamar Munawer
-/
module

public import Mathlib.Analysis.Analytic.IsolatedZeros
public import Mathlib.NumberTheory.LSeries.HardyZ
public import Mathlib.Order.Bounds.Basic
public import RiemannBlueprint.UpstreamPRs.UpstreamPR_1A_CriticalLineZeros
public import RiemannBlueprint.UpstreamPRs.UpstreamPR_2B_HardyPsiAndThetaKernel
public import RiemannBlueprint.UpstreamPRs.UpstreamPR_2C_HardyThetaIteratedDeriv
public import RiemannBlueprint.UpstreamPRs.UpstreamPR_2E_HardyGContourAndMellin
public import RiemannBlueprint.UpstreamPRs.UpstreamPR_2F_HardyEvenMomentIdentity

/-!
# Hardy's (1914) Theorem: Infinitely Many Critical-Line Zeros of `riemannZeta`

Combining the boundary decay of `iteratedDeriv (2 * k) (fun w => hardyThetaTerm (I * w))` at
`π / 4` with the even moment identity `hardyGn_even_re` rules out eventual constancy of sign of
`hardyZ`, yielding Hardy's (1914) theorem on the infinitude of critical-line zeros of
`riemannZeta` and real zeros of `hardyZ`.
-/

@[expose] public section

open Complex MeasureTheory Filter Set Topology

private lemma hardyZ_unbounded_sign_changes :
    ∀ T : ℝ, ∃ a b : ℝ, T < a ∧ a ≤ b ∧ hardyZ a * hardyZ b ≤ 0 := by
  by_contra h_neg
  push Not at h_neg
  rcases h_neg with ⟨T₀, hT₀⟩
  let a₀ : ℝ := max T₀ 1 + 1
  have ha₀_gt_T₀ : T₀ < a₀ := lt_of_le_of_lt (le_max_left T₀ 1) (lt_add_one _)
  have ha₀_gt_one : 1 < a₀ := lt_of_le_of_lt (le_max_right T₀ 1) (lt_add_one _)
  have ha₀_pos : 0 < a₀ := by linarith
  have ha₀_ne : hardyZ a₀ ≠ 0 := fun hz => by
    have h0 := hT₀ a₀ a₀ ha₀_gt_T₀ le_rfl
    rw [hz, zero_mul] at h0; exact lt_irrefl 0 h0
  let sgn : ℝ := if 0 < hardyZ a₀ then 1 else -1
  have hsgn_abs : |sgn| = 1 := by dsimp [sgn]; split_ifs <;> norm_num
  have h_pos_after : ∀ t : ℝ, a₀ ≤ t → 0 < sgn * hardyZ t := fun t ht => by
    have hmul := hT₀ a₀ t ha₀_gt_T₀ ht
    dsimp [sgn]; split_ifs with ha
    · rw [one_mul]; exact (mul_pos_iff.mp hmul).elim (fun h => h.2) (fun h => by linarith)
    · have ha_neg : hardyZ a₀ < 0 := lt_of_le_of_ne (le_of_not_gt ha) ha₀_ne
      have ht_neg : hardyZ t < 0 := (mul_pos_iff.mp hmul).elim (fun h => by linarith) (fun h => h.2)
      nlinarith
  let Λre : ℝ → ℝ := fun t => (completedRiemannZeta (1 / 2 + (t : ℂ) * I)).re
  have h_Λre_pos : ∀ t : ℝ, a₀ ≤ t → 0 < sgn * Λre t := fun t ht => by
    have hΓ : 0 < ‖Gammaℝ (1 / 2 + (t : ℂ) * I)‖ :=
      norm_pos_iff.mpr (Gammaℝ_ne_zero_of_re_pos (by simp))
    have hZ : Λre t = hardyZ t * ‖Gammaℝ (1 / 2 + (t : ℂ) * I)‖ := by
      dsimp [hardyZ, Λre]; rw [div_mul_cancel₀ _ hΓ.ne']
    rw [hZ, ← mul_assoc]; exact mul_pos (h_pos_after t ht) hΓ
  have h_Λre_cont : Continuous Λre :=
    Complex.continuous_re.comp continuous_completedRiemannZeta_criticalLine
  obtain ⟨t_min, ht_min_mem, ht_min⟩ :=
    isCompact_Icc.exists_isMinOn (nonempty_Icc.mpr (by linarith : a₀ + 1 ≤ a₀ + 2))
      ((continuous_const (y := sgn)).mul h_Λre_cont).continuousOn
  let m_pos : ℝ := sgn * Λre t_min
  have hm_pos : 0 < m_pos := h_Λre_pos t_min (by linarith [ht_min_mem.1])
  obtain ⟨M_low, hM_low⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (f := Λre) h_Λre_cont.continuousOn (s := Set.Icc 0 a₀)
  let M_abs : ℝ := max M_low 0
  have hM_abs_nn : 0 ≤ M_abs := le_max_right _ _
  let C_low : ℝ := a₀ * (2 * Real.exp ((Real.pi / 4) * a₀)) * M_abs
  have h_every_k : ∀ k : ℕ, m_pos * (a₀ + 1) ^ (2 * k) - C_low * a₀ ^ (2 * k) ≤ 6 * Real.pi := by
    intro k
    obtain ⟨δ, hδ_lt, hδ_gt⟩ := ((tendsto_iteratedDeriv_hardyThetaTerm k).eventually
      (gt_mem_nhds one_pos) |>.and (Ioo_mem_nhdsGT (by positivity : (0 : ℝ) < Real.pi / 8))).exists
    let α : ℝ := Real.pi / 4 - δ
    have hα_pos : 0 < α := by dsimp [α]; linarith [hδ_gt.2]
    have hα_lt : α < Real.pi / 4 := by dsimp [α]; linarith [hδ_gt.1]
    have hα_abs : |α| < Real.pi / 4 := by rwa [abs_of_pos hα_pos]
    have h_theta_diff : ContDiffAt ℂ (2 * k) (fun w : ℂ => hardyThetaTerm (I * w)) (α : ℂ) :=
      ((differentiableOn_hardyThetaTerm_mul_I.analyticOnNhd
        (isOpen_lt continuous_re.abs continuous_const)) (α : ℂ)
        (by simpa using hα_abs)).contDiffAt.of_le (by exact_mod_cast le_top)
    have h_cosh_diff : ContDiffAt ℂ (2 * k)
        (fun w : ℂ => Complex.exp ((I * w) / 2) + Complex.exp (-(I * w) / 2)) (α : ℂ) :=
      ((contDiffAt_const.mul contDiffAt_id).div_const 2).cexp.add
        ((contDiffAt_const.mul contDiffAt_id).neg.div_const 2).cexp
    have h_psi_split : (fun w : ℂ => hardyPsi (I * w)) =
        (fun w : ℂ => hardyThetaTerm (I * w)) -
          (fun w : ℂ => Complex.exp ((I * w) / 2) + Complex.exp (-(I * w) / 2)) := rfl
    have h_norm_Gn : ‖hardyGn (2 * k) (α : ℂ)‖ ≤ 3 := by
      rw [← iteratedDeriv_hardyPsi_mul_I_eq (2 * k) hα_abs, h_psi_split,
        iteratedDeriv_sub h_theta_diff h_cosh_diff]
      exact (norm_sub_le _ _).trans (by
        linarith [hδ_lt.le, norm_iteratedDeriv_hardyCoshTerm_le (2 * k) α])
    let F_k : ℝ → ℝ :=
      fun t => t ^ (2 * k) * (Real.exp (α * t) + Real.exp (-α * t)) * (sgn * Λre t)
    have h_Fk_int : IntegrableOn F_k (Ioi 0) := by
      have h_raw := integrable_abs_pow_mul_exp_mul_completedRiemannZeta (2 * k) hα_pos.le hα_lt
      refine ((h_raw.const_mul 2).integrableOn (s := Ioi 0)).mono' ?_ (ae_of_all _ fun t => ?_)
      · exact (((continuous_id.pow (2 * k)).mul
          ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).add
            (Real.continuous_exp.comp (continuous_const.mul continuous_id)))).mul
          (continuous_const.mul h_Λre_cont)).aestronglyMeasurable
      · have hΛ_norm : |Λre t| = ‖completedRiemannZeta (1 / 2 + (t : ℂ) * I)‖ := by
          rw [Complex.norm_def, Complex.normSq_apply, completedRiemannZeta_half_add_mul_I_im t,
            mul_zero, add_zero, Real.sqrt_mul_self_eq_abs]
        have h1 : Real.exp (α * t) ≤ Real.exp (α * |t|) :=
          Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (le_abs_self t) hα_pos.le)
        have h2 : Real.exp (-α * t) ≤ Real.exp (α * |t|) := by
          rw [Real.exp_le_exp, neg_mul, ← mul_neg]
          exact mul_le_mul_of_nonneg_left (neg_le_abs t) hα_pos.le
        dsimp [F_k]
        rw [abs_mul, abs_mul, abs_pow,
          abs_of_pos (add_pos (Real.exp_pos _) (Real.exp_pos _)), abs_mul, hsgn_abs, one_mul,
          hΛ_norm]
        calc |t| ^ (2 * k) * (Real.exp (α * t) + Real.exp (-α * t)) *
              ‖completedRiemannZeta (1 / 2 + (t : ℂ) * I)‖
            ≤ |t| ^ (2 * k) * (2 * Real.exp (α * |t|)) *
                ‖completedRiemannZeta (1 / 2 + (t : ℂ) * I)‖ := by gcongr; linarith
          _ = 2 * (|t| ^ (2 * k) * Real.exp (α * |t|) *
                ‖completedRiemannZeta (1 / 2 + (t : ℂ) * I)‖) := by ring
    have h_upper : ∫ t in Ioi (0 : ℝ), F_k t ≤ 6 * Real.pi := by
      have h_eq : ∫ t in Ioi (0 : ℝ), F_k t =
          sgn * ((2 * Real.pi) * (hardyGn (2 * k) (α : ℂ)).re) := by
        calc ∫ t in Ioi (0 : ℝ), F_k t
            = ∫ t in Ioi (0 : ℝ), sgn * (t ^ (2 * k) *
                (Real.exp (α * t) + Real.exp (-α * t)) * Λre t) :=
              setIntegral_congr_fun measurableSet_Ioi fun t _ => by dsimp [F_k]; ring
          _ = sgn * ∫ t in Ioi (0 : ℝ), t ^ (2 * k) *
                (Real.exp (α * t) + Real.exp (-α * t)) * Λre t := integral_const_mul _ _
          _ = sgn * ((2 * Real.pi) * (hardyGn (2 * k) (α : ℂ)).re) := by
                rw [hardyGn_even_re k hα_abs]
      calc ∫ t in Ioi (0 : ℝ), F_k t
          ≤ |∫ t in Ioi (0 : ℝ), F_k t| := le_abs_self _
        _ = 1 * (2 * Real.pi * |(hardyGn (2 * k) (α : ℂ)).re|) := by
            rw [h_eq, abs_mul, hsgn_abs, abs_mul,
              abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)]
        _ ≤ 2 * Real.pi * ‖hardyGn (2 * k) (α : ℂ)‖ := by
            rw [one_mul]; gcongr; exact Complex.abs_re_le_norm _
        _ ≤ 2 * Real.pi * 3 := by gcongr
        _ = 6 * Real.pi := by ring
    have h_split_0 : ∫ t in Ioi (0 : ℝ), F_k t =
        (∫ t in Ioc 0 a₀, F_k t) + (∫ t in Ioi a₀, F_k t) := by
      rw [← Ioc_union_Ioi_eq_Ioi ha₀_pos.le,
        setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi
          (h_Fk_int.mono_set Ioc_subset_Ioi_self) (h_Fk_int.mono_set (Ioi_subset_Ioi ha₀_pos.le))]
    have h_low_bd : -C_low * a₀ ^ (2 * k) ≤ ∫ t in Ioc 0 a₀, F_k t := by
      have h_pt : ∀ t ∈ Ioc (0 : ℝ) a₀,
          ‖F_k t‖ ≤ a₀ ^ (2 * k) * (2 * Real.exp ((Real.pi / 4) * a₀)) * M_abs := fun t ht => by
        have h_t_nn : 0 ≤ t := ht.1.le
        have h_exp1 : Real.exp (α * t) ≤ Real.exp ((Real.pi / 4) * a₀) :=
          Real.exp_le_exp.mpr (mul_le_mul hα_lt.le ht.2 h_t_nn (by positivity))
        have h_exp2 : Real.exp (-α * t) ≤ Real.exp ((Real.pi / 4) * a₀) :=
          Real.exp_le_exp.mpr ((mul_nonpos_of_nonpos_of_nonneg (by linarith) h_t_nn).trans
            (mul_nonneg (by positivity) ha₀_pos.le))
        have h_Λ : |Λre t| ≤ M_abs := (hM_low t ⟨h_t_nn, ht.2⟩).trans (le_max_left _ _)
        dsimp [F_k]
        change |t ^ (2 * k) * (Real.exp (α * t) + Real.exp (-α * t)) * (sgn * Λre t)| ≤
          a₀ ^ (2 * k) * (2 * Real.exp ((Real.pi / 4) * a₀)) * M_abs
        rw [abs_mul, abs_mul, abs_pow,
          abs_of_pos (add_pos (Real.exp_pos _) (Real.exp_pos _)), abs_mul, hsgn_abs, one_mul,
          abs_of_nonneg h_t_nn]
        exact mul_le_mul (mul_le_mul (pow_le_pow_left₀ h_t_nn ht.2 (2 * k))
          (by linarith) (by positivity) (by positivity)) h_Λ (abs_nonneg _) (by positivity)
      have h_int_le : |∫ t in Ioc 0 a₀, F_k t| ≤
          a₀ ^ (2 * k) * (2 * Real.exp ((Real.pi / 4) * a₀)) * M_abs * a₀ := by
        simpa [Real.volume_real_Ioc_of_le ha₀_pos.le, sub_zero, Real.norm_eq_abs] using
          norm_setIntegral_le_of_norm_le_const
            (measure_Ioc_lt_top : volume (Ioc (0 : ℝ) a₀) < ⊤) h_pt
      have h_abs_le : |∫ t in Ioc 0 a₀, F_k t| ≤ C_low * a₀ ^ (2 * k) :=
        h_int_le.trans_eq (by dsimp [C_low]; ring)
      linarith [(abs_le.mp h_abs_le).1]
    have h_tail_bd : m_pos * (a₀ + 1) ^ (2 * k) ≤ ∫ t in Ioi a₀, F_k t := by
      have h_sub : Ioc (a₀ + 1) (a₀ + 2) ⊆ Ioi a₀ := fun t ht => lt_of_le_of_lt (by linarith) ht.1
      have h_nonneg_tail : ∀ t ∈ Ioi a₀, 0 ≤ F_k t := fun t ht => by
        dsimp [F_k]
        exact mul_nonneg (mul_nonneg (pow_nonneg (lt_trans ha₀_pos ht).le _)
          (add_pos (Real.exp_pos _) (Real.exp_pos _)).le) (h_Λre_pos t ht.le).le
      have h_mono : ∫ t in Ioc (a₀ + 1) (a₀ + 2), F_k t ≤ ∫ t in Ioi a₀, F_k t :=
        setIntegral_mono_set (h_Fk_int.mono_set (Ioi_subset_Ioi ha₀_pos.le))
          (ae_restrict_of_forall_mem measurableSet_Ioi h_nonneg_tail) h_sub.eventuallyLE
      have h_const_le : ∫ t in Ioc (a₀ + 1) (a₀ + 2), (m_pos * (a₀ + 1) ^ (2 * k)) ≤
          ∫ t in Ioc (a₀ + 1) (a₀ + 2), F_k t := by
        refine setIntegral_mono_on (integrableOn_const (hs := measure_Ioc_lt_top.ne))
          (h_Fk_int.mono_set (h_sub.trans (Ioi_subset_Ioi ha₀_pos.le))) measurableSet_Ioc ?_
        intro t ht
        have h_t_ge : a₀ + 1 ≤ t := ht.1.le
        have h_exp_ge : 1 ≤ Real.exp (α * t) + Real.exp (-α * t) := by
          linarith [Real.one_le_exp (mul_nonneg hα_pos.le (by linarith : 0 ≤ t)),
            Real.exp_pos (-α * t)]
        dsimp [F_k]
        calc m_pos * (a₀ + 1) ^ (2 * k)
            ≤ (a₀ + 1) ^ (2 * k) * 1 * m_pos := by ring_nf; rfl
          _ ≤ t ^ (2 * k) * (Real.exp (α * t) + Real.exp (-α * t)) * (sgn * Λre t) :=
              mul_le_mul (mul_le_mul (by gcongr) h_exp_ge zero_le_one (pow_nonneg (by linarith) _))
                (ht_min ⟨ht.1.le, ht.2⟩) hm_pos.le (mul_nonneg (pow_nonneg (by linarith) _)
                  (add_pos (Real.exp_pos _) (Real.exp_pos _)).le)
      have h_vol : ∫ t in Ioc (a₀ + 1) (a₀ + 2), (m_pos * (a₀ + 1) ^ (2 * k)) =
          m_pos * (a₀ + 1) ^ (2 * k) := by
        rw [setIntegral_const, smul_eq_mul, Real.volume_real_Ioc_of_le (by linarith),
          show a₀ + 2 - (a₀ + 1) = 1 by ring, one_mul]
      linarith
    linarith
  have h_ratio_gt : 1 < ((a₀ + 1) / a₀) ^ 2 :=
    one_lt_pow₀ ((one_lt_div ha₀_pos).mpr (by linarith)) (by norm_num)
  have h_tendsto : Tendsto (fun k : ℕ => m_pos * (((a₀ + 1) / a₀) ^ 2) ^ k) atTop atTop :=
    (tendsto_pow_atTop_atTop_of_one_lt h_ratio_gt).const_mul_atTop hm_pos
  rw [Filter.tendsto_atTop] at h_tendsto
  obtain ⟨k, hk⟩ := h_tendsto (C_low + 6 * Real.pi + 1) |>.exists
  have hk_bound := h_every_k k
  have ha0_ge1 : 1 ≤ a₀ ^ (2 * k) := one_le_pow₀ ha₀_gt_one.le
  have h_div : m_pos * (((a₀ + 1) / a₀) ^ 2) ^ k = m_pos * (a₀ + 1) ^ (2 * k) / a₀ ^ (2 * k) := by
    rw [← pow_mul, div_pow]; ring
  rw [h_div, le_div_iff₀ (pow_pos ha₀_pos _)] at hk
  have hk1 : (C_low + 6 * Real.pi) * a₀ ^ (2 * k) < (C_low + 6 * Real.pi + 1) * a₀ ^ (2 * k) := by
    nlinarith [pow_pos ha₀_pos (2 * k)]
  have hk2 : 6 * Real.pi ≤ 6 * Real.pi * a₀ ^ (2 * k) := by nlinarith [Real.pi_pos, ha0_ge1]
  linarith

/-- **Hardy's (1914) Theorem** (unconditional): the Riemann zeta function has infinitely many
zeros on the critical line `Re(s) = 1 / 2`. -/
theorem infinite_criticalLine_zeros :
    {t : ℝ | riemannZeta (criticalLine t) = 0}.Infinite :=
  infinite_criticalLine_zeros_of_sign_changes hardyZ_unbounded_sign_changes

/-- **Hardy's (1914) Theorem for `hardyZ`** (unconditional): Hardy's `Z`-function has infinitely
many real zeros. -/
theorem infinite_hardyZ_zeros :
    {t : ℝ | hardyZ t = 0}.Infinite :=
  infinite_hardyZ_zeros_of_sign_changes hardyZ_unbounded_sign_changes
