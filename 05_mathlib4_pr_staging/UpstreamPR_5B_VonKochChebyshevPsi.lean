/-
Copyright (c) 2026 Qamar Munawer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qamar Munawer
-/
module

public import Mathlib.Analysis.Analytic.IsolatedZeros
public import Mathlib.Analysis.MellinTransform
public import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
public import Mathlib.NumberTheory.LSeries.SumCoeff
public import RiemannBlueprint.UpstreamPRs.UpstreamPR_5A_ZetaLogDerivHolomorphy

/-!
# Von Koch's Forward Theorem via Chebyshev's `ψ` and Order-of-Zero Factoring
Formalizes `mellinVonKochRemainder_analyticOnNhd`, `-ζ'/ζ = s/(s-1)+J_ψ(s)`, & RH implication.
-/

@[expose] public section

open Complex MeasureTheory Filter Set Asymptotics ArithmeticFunction

/-- Chebyshev's second prime-counting function `ψ(x) = ∑ n ≤ x, Λ(n)`. -/
noncomputable def chebyshevPsi (x : ℝ) : ℝ := ∑ n ∈ Finset.Iic ⌊x⌋₊, (vonMangoldt n : ℝ)

/-- Von Koch remainder bound: `|ψ(x) - x| = O(x ^ (1 / 2 + ε))` for every `ε > 0`. -/
def VonKochRemainderBound : Prop :=
  ∀ ε > 0, ∃ C > 0, ∀ x ≥ 2, |chebyshevPsi x - x| ≤ C * x ^ ((1 / 2 : ℝ) + ε)

/-- Truncated Chebyshev remainder `(ψ(x) - x) · 1_{(1, ∞)}(x)` in `ℂ`. -/
noncomputable def chebyshevPsiRemainder (x : ℝ) : ℂ :=
  if 1 < x then ((chebyshevPsi x - x : ℝ) : ℂ) else 0

/-- Normalized Mellin transform `J_ψ(s) = s · M(chebyshevPsiRemainder)(-s)`. -/
noncomputable def mellinVonKochRemainder (s : ℂ) : ℂ := s * mellin chebyshevPsiRemainder (-s)

private lemma psi_nn (x : ℝ) : 0 ≤ chebyshevPsi x := Finset.sum_nonneg fun _ _ => vonMangoldt_nonneg
private lemma psi_icc (t : ℝ) : (∑ k ∈ Finset.Icc 1 ⌊t⌋₊, vonMangoldt k) = chebyshevPsi t := by
  unfold chebyshevPsi; rw [show Finset.Iic ⌊t⌋₊ = insert 0 (Finset.Icc 1 ⌊t⌋₊) from by
    ext k; simp; omega, Finset.sum_insert (by simp)]; simp

private lemma sum_vonMangoldt_le (n : ℕ) :
    ∑ k ∈ Finset.Icc 1 n, vonMangoldt k ≤ (n : ℝ) * Real.log n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn; · simp
  refine (Finset.sum_le_sum fun k hk => vonMangoldt_le_log.trans (Real.log_le_log
    (by exact_mod_cast (Finset.mem_Icc.mp hk).1) (Nat.cast_le.mpr (Finset.mem_Icc.mp hk).2))).trans
    (by simp [Finset.sum_const, nsmul_eq_mul])

private lemma id_mul_log_isBigO {ε : ℝ} (hε : 0 < ε) :
    (fun x : ℝ => x * Real.log x) =O[atTop] fun x : ℝ => x ^ (1 + ε) :=
  ((isBigO_refl _ atTop).mul (isLittleO_log_rpow_atTop hε).isBigO).trans (IsBigO.of_bound 1 <| by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    rw [one_mul, Real.rpow_add hx, Real.rpow_one])

private lemma psiRem_locInt : LocallyIntegrableOn chebyshevPsiRemainder (Ioi 0) volume := by
  have hmono : Monotone chebyshevPsi := fun _ _ hxy => Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.Iic_subset_Iic.mpr (Nat.floor_mono hxy)) fun _ _ _ => vonMangoldt_nonneg
  have hm : Measurable chebyshevPsiRemainder := (show chebyshevPsiRemainder = Set.indicator (Ioi 1)
      fun x => ((chebyshevPsi x - x : ℝ) : ℂ) from by ext x; simp [chebyshevPsiRemainder,
      indicator_apply]) ▸ (Complex.continuous_ofReal.measurable.comp
        (hmono.measurable.sub measurable_id)).indicator measurableSet_Ioi
  rw [locallyIntegrableOn_iff isOpen_Ioi.isLocallyClosed]; intro k hksub hkcomp
  obtain ⟨M, hM⟩ := hkcomp.bddAbove
  refine IntegrableOn.of_bound hkcomp.measure_lt_top hm.aestronglyMeasurable
    (chebyshevPsi (max M 0) + max M 0) ?_
  filter_upwards [ae_restrict_mem hkcomp.measurableSet] with x hx
  have hle := le_trans (hM hx) (le_max_left M 0); unfold chebyshevPsiRemainder; split_ifs
  · rw [Complex.norm_real]; exact (abs_sub _ _).trans (by
      rw [abs_of_nonneg (psi_nn x), abs_of_pos (hksub hx)]; exact add_le_add (hmono hle) hle)
  · rw [norm_zero]; exact add_nonneg (psi_nn _) (le_max_right M 0)

private lemma psiRem_nhds (b : ℝ) :
    chebyshevPsiRemainder =O[nhdsWithin 0 (Ioi 0)] fun x : ℝ => x ^ (-b) :=
  IsBigO.of_bound 1 <| by
    filter_upwards [Ioo_mem_nhdsGT zero_lt_one] with x hx
    simp [chebyshevPsiRemainder, not_lt.mpr hx.2.le]

/-- Under `VonKochRemainderBound`, `mellinVonKochRemainder` is analytic on `Re(s) > 1 / 2`. -/
theorem mellinVonKochRemainder_analyticOnNhd (hvk : VonKochRemainderBound) :
    AnalyticOnNhd ℂ mellinVonKochRemainder {s : ℂ | 1 / 2 < s.re} := by
  refine DifferentiableOn.analyticOnNhd (fun s hs => ?_) (isOpen_lt continuous_const continuous_re)
  dsimp at hs; let ε : ℝ := (s.re - 1 / 2) / 2; obtain ⟨C, _, hC⟩ := hvk ε (by dsimp [ε]; linarith)
  have hm : DifferentiableAt ℂ (mellin chebyshevPsiRemainder) (-s) :=
    mellin_differentiableAt_of_isBigO_rpow (a := -(1 / 2 + ε)) (b := -s.re - 1) psiRem_locInt
      (IsBigO.of_bound C <| by
        filter_upwards [eventually_ge_atTop (2 : ℝ)] with x hx
        rw [show chebyshevPsiRemainder x = ((chebyshevPsi x - x : ℝ) : ℂ) from by
            simp [chebyshevPsiRemainder, show (1 : ℝ) < x by linarith], Complex.norm_real,
          Real.norm_of_nonneg (Real.rpow_nonneg (by linarith) _), neg_neg]; exact hC x hx)
      (by simp only [neg_re, ε]; linarith) (psiRem_nhds _) (by simp only [neg_re]; linarith)
  exact (differentiableAt_id.mul (hm.comp s differentiableAt_id.neg)).differentiableWithinAt

/-- Log-derivative Mellin identity on `1 < Re(s)`: `-ζ'(s)/ζ(s) = s/(s - 1) + J_ψ(s)`. -/
theorem neg_deriv_riemannZeta_div_eq_pole_add_mellinVonKochRemainder {s : ℂ} (hs : 1 < s.re) :
    -deriv riemannZeta s / riemannZeta s = s / (s - 1) + mellinVonKochRemainder s := by
  let ε : ℝ := (s.re - 1) / 2; have hε : 0 < ε := by dsimp [ε]; linarith
  have hbo_u : chebyshevPsiRemainder =O[atTop] fun x : ℝ => x ^ (1 + ε) :=
    (IsBigO.of_bound 2 <| by
      filter_upwards [eventually_ge_atTop (max (Real.exp 1) 2)] with x hx
      have hx2 : 2 ≤ x := le_trans (le_max_right _ _) hx
      have hf1 : 1 ≤ ⌊x⌋₊ := Nat.le_floor (by norm_num; linarith)
      have hlog1 : 1 ≤ Real.log x := by
        simpa using Real.log_le_log (Real.exp_pos 1) (le_trans (le_max_left _ _) hx)
      have hpsi : chebyshevPsi x ≤ x * Real.log x := (psi_icc x ▸ sum_vonMangoldt_le _).trans
        (mul_le_mul (Nat.floor_le (by linarith)) (Real.log_le_log (by exact_mod_cast hf1)
          (Nat.floor_le (by linarith))) (Real.log_nonneg (by exact_mod_cast hf1)) (by linarith))
      rw [show chebyshevPsiRemainder x = ((chebyshevPsi x - x : ℝ) : ℂ) from by
          simp [chebyshevPsiRemainder, show (1 : ℝ) < x by linarith], Complex.norm_real,
        Real.norm_of_nonneg (mul_nonneg (by linarith) (by linarith))]
      exact (abs_sub _ _).trans (by
        rw [abs_of_nonneg (psi_nn x), abs_of_pos (by linarith)]; nlinarith)).trans
    (id_mul_log_isBigO hε)
  have hsum_bo : (fun n : ℕ => ∑ k ∈ Finset.Icc 1 n, vonMangoldt k) =O[atTop]
      fun n : ℕ => (n : ℝ) ^ (1 + ε) := (IsBigO.of_bound 1 <| by
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    rw [one_mul, Real.norm_of_nonneg (Finset.sum_nonneg fun _ _ => vonMangoldt_nonneg),
      Function.comp_apply, Real.norm_of_nonneg (mul_nonneg (Nat.cast_nonneg _)
        (Real.log_nonneg (by exact_mod_cast hn)))]; exact sum_vonMangoldt_le n).trans
    ((id_mul_log_isBigO hε).comp_tendsto tendsto_natCast_atTop_atTop)
  have hm : MellinConvergent chebyshevPsiRemainder (-s) := mellinConvergent_of_isBigO_rpow
    (a := -(1 + ε)) (b := -s.re - 1) psiRem_locInt (by simpa only [neg_neg] using hbo_u)
    (by simp only [neg_re, ε]; linarith) (psiRem_nhds _) (by simp only [neg_re]; linarith)
  have hint_eq : ∀ t : ℝ, (t : ℂ) ^ (-s - 1) • chebyshevPsiRemainder t = Set.indicator (Ioi 1)
      (fun t : ℝ => ((chebyshevPsi t - t : ℝ) : ℂ) * (t : ℂ) ^ (-(s + 1))) t := fun t => by
    rw [smul_eq_mul, mul_comm]; unfold chebyshevPsiRemainder
    by_cases ht : 1 < t <;> simp [ht, show (-s - 1 : ℂ) = -(s + 1) by ring]
  have hint_r : IntegrableOn (fun t : ℝ => ((chebyshevPsi t - t : ℝ) : ℂ) * (t : ℂ) ^ (-(s + 1)))
      (Ioi 1) volume := by
    simpa [inter_eq_left.mpr (Ioi_subset_Ioi zero_le_one)] using (integrableOn_indicator_iff
      measurableSet_Ioi.nullMeasurableSet).mp (hm.congr_fun (fun t _ => hint_eq t)
      measurableSet_Ioi)
  have hpow : ∀ t ∈ Ioi (1 : ℝ), (t : ℂ) ^ (-s) = (t : ℂ) * (t : ℂ) ^ (-(s + 1)) := fun t ht => by
    rw [show (-s : ℂ) = 1 + -(s + 1) by ring,
      cpow_add _ _ (ofReal_ne_zero.mpr (by linarith [mem_Ioi.mp ht])), cpow_one]
  have hint_t : IntegrableOn (fun t : ℝ => (t : ℂ) * (t : ℂ) ^ (-(s + 1))) (Ioi 1) volume :=
    ((integrableOn_Ioi_cpow_iff zero_lt_one).mpr (by simp; linarith) : IntegrableOn
      (fun t : ℝ => (t : ℂ) ^ (-s)) (Ioi 1) volume).congr_fun hpow measurableSet_Ioi
  have hid : ∫ t in Ioi (1 : ℝ), (t : ℂ) * (t : ℂ) ^ (-(s + 1)) = 1 / (s - 1) := by
    rw [← setIntegral_congr_fun measurableSet_Ioi hpow,
      integral_Ioi_cpow_of_lt (by simp; linarith) zero_lt_one, ofReal_one, one_cpow]
    have h1 : s - 1 ≠ 0 := sub_ne_zero.mpr fun h => by rw [h] at hs; norm_num at hs
    field_simp [h1, show -s + 1 ≠ 0 from fun h => h1 (by linear_combination -h)]; ring
  have hL := (LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs).symm.trans
    (LSeries_eq_mul_integral_of_nonneg vonMangoldt (r := 1 + ε) (by linarith) (s := s)
      (by dsimp [ε]; linarith) hsum_bo (fun _ => vonMangoldt_nonneg))
  simp_rw [show ∀ t : ℝ, (∑ k ∈ Finset.Icc 1 ⌊t⌋₊, (vonMangoldt k : ℂ)) * (t : ℂ) ^ (-(s + 1)) =
      ((chebyshevPsi t - t : ℝ) : ℂ) * (t : ℂ) ^ (-(s + 1)) + (t : ℂ) * (t : ℂ) ^ (-(s + 1))
      from fun t => by rw [show (∑ k ∈ Finset.Icc 1 ⌊t⌋₊, (vonMangoldt k : ℂ)) =
        (chebyshevPsi t : ℂ) by exact_mod_cast psi_icc t]; push_cast; ring] at hL
  rw [integral_add hint_r hint_t, hid, show (∫ t in Ioi (1 : ℝ), ((chebyshevPsi t - t : ℝ) : ℂ) *
      (t : ℂ) ^ (-(s + 1))) = mellin chebyshevPsiRemainder (-s) from by
    rw [mellin, setIntegral_congr_fun measurableSet_Ioi (fun t _ => hint_eq t),
      setIntegral_indicator measurableSet_Ioi, inter_eq_right.mpr (Ioi_subset_Ioi zero_le_one)]]
    at hL
  unfold mellinVonKochRemainder; rw [hL]; ring

private lemma cvx_gt (f : ℂ → ℝ) (hf : ∀ (a b : ℝ) (x y : ℂ),
    f (a • x + b • y) = a * f x + b * f y) (c : ℝ) : Convex ℝ {z : ℂ | c < f z} := by
  intro x hx y hy a b ha hb hab; rw [mem_ofPred_eq, hf]
  by_cases ha0 : a = 0
  · rw [ha0, show b = 1 by linarith]; simp only [zero_mul, one_mul, zero_add]; exact hy
  · linarith [mul_lt_mul_of_pos_left hx (lt_of_le_of_ne ha (Ne.symm ha0)),
      mul_le_mul_of_nonneg_left hy.le hb,
      show a * c + b * c = c from by rw [← add_mul, hab, one_mul]]

private lemma isPreconnected_re_gt_half_sdiff_one :
    IsPreconnected ({z : ℂ | 1 / 2 < z.re} \ {1}) := by
  have hre : ∀ (a b : ℝ) (x y : ℂ), (a • x + b • y).re = a * x.re + b * y.re := by simp
  have him : ∀ (a b : ℝ) (x y : ℂ), (a • x + b • y).im = a * x.im + b * y.im := by simp
  have hlt : ∀ (f : ℂ → ℝ) (_ : ∀ (a b : ℝ) (x y : ℂ), f (a • x + b • y) = a * f x + b * f y) c,
      Convex ℝ {z : ℂ | f z < c} := fun f hf c => by
    convert cvx_gt (fun z => -f z) (fun a b x y => by rw [hf]; ring) (-c) using 1; ext z; simp
  rw [show ({z : ℂ | 1 / 2 < z.re} \ {1}) = ({z : ℂ | 1 / 2 < z.re ∧ 0 < z.im} ∪ {z : ℂ | 1 < z.re})
      ∪ ({z : ℂ | 1 / 2 < z.re ∧ z.im < 0} ∪ {z : ℂ | 1 / 2 < z.re ∧ z.re < 1}) from by
    ext z; simp only [Set.mem_sdiff, mem_ofPred_eq, mem_singleton_iff, mem_union]
    refine ⟨fun ⟨hz, hne⟩ => ?_, fun h => ?_⟩
    · rcases lt_trichotomy z.re 1 with h | h | h
      · exact Or.inr (Or.inr ⟨hz, h⟩)
      · exact (lt_or_gt_of_ne fun h0 => hne (Complex.ext h h0)).elim
          (fun hn => Or.inr (Or.inl ⟨hz, hn⟩)) (fun hp => Or.inl (Or.inl ⟨hz, hp⟩))
      · exact Or.inl (Or.inr h)
    · rcases h with (⟨h1, h2⟩ | h) | (⟨h1, h2⟩ | ⟨h1, h2⟩) <;>
        exact ⟨by linarith, fun e => by subst e; norm_num at *⟩]
  exact (((cvx_gt _ hre (1 / 2)).inter (cvx_gt _ him 0)).isPreconnected.union' ⟨2 + I, by norm_num,
    by norm_num⟩ (cvx_gt _ hre 1).isPreconnected).union' ⟨2 - I, Or.inr (by norm_num),
    Or.inl (by norm_num)⟩ (((cvx_gt _ hre (1 / 2)).inter (hlt _ him 0)).isPreconnected.union'
    ⟨3 / 4 - I, by norm_num, by norm_num⟩
    ((cvx_gt _ hre (1 / 2)).inter (hlt _ hre 1)).isPreconnected)

/-- Under `VonKochRemainderBound`, `riemannZeta` has no zeros with `1 / 2 < Re(s)`. -/
theorem zero_free_re_gt_half_of_vonKoch (hVK : VonKochRemainderBound) :
    ∀ s : ℂ, 1 / 2 < s.re → riemannZeta s ≠ 0 := by
  intro ρ hre hζ
  have hne : ρ ≠ 1 := fun h => riemannZeta_ne_zero_of_one_le_re (by rw [h]; simp) hζ
  let U : Set ℂ := {z : ℂ | 1 / 2 < z.re} \ {1}
  have hUo : IsOpen U := (isOpen_lt continuous_const continuous_re).sdiff isClosed_singleton
  have hζa : AnalyticOnNhd ℂ riemannZeta U := DifferentiableOn.analyticOnNhd
    (fun z hz => (differentiableAt_riemannZeta hz.2).differentiableWithinAt) hUo
  have h2I : (2 : ℂ) + I ∈ U := ⟨by simp; norm_num, fun h => by simpa using congrArg Complex.im h⟩
  obtain ⟨n, h, hh_an, hh_ne, hfac⟩ := (hζa ρ ⟨hre, hne⟩).exists_eventuallyEq_pow_smul_nonzero_iff
    |>.mpr (fun hev => riemannZeta_ne_zero_of_one_le_re (by simp : (1 : ℝ) ≤ ((2 : ℂ) + I).re)
      (hζa.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_re_gt_half_sdiff_one
        ⟨hre, hne⟩ hev h2I))
  simp only [smul_eq_mul] at hfac; rcases n with _ | m
  · exact hh_ne (by simpa [hζ] using hfac.self_of_nhds.symm)
  · let P : ℂ → ℂ := fun z => z / (z - 1) + mellinVonKochRemainder z
    have hP_on : AnalyticOnNhd ℂ P U := (DifferentiableOn.analyticOnNhd (fun z hz =>
      (differentiableAt_id.div (differentiableAt_id.sub (differentiableAt_const (1 : ℂ)))
        (sub_ne_zero.mpr hz.2)).differentiableWithinAt) hUo).add
      ((mellinVonKochRemainder_analyticOnNhd hVK).mono sdiff_subset)
    have hcl_u : Set.EqOn (fun z => deriv riemannZeta z + P z * riemannZeta z) 0 U :=
      (hζa.deriv.add (hP_on.mul hζa)).eqOn_of_preconnected_of_eventuallyEq analyticOnNhd_const
        isPreconnected_re_gt_half_sdiff_one h2I (Filter.eventually_of_mem ((isOpen_lt
          continuous_const continuous_re).mem_nhds (by simp : (1 : ℝ) < ((2 : ℂ) + I).re))
          fun z hz => by
            dsimp [P]; rw [← neg_deriv_riemannZeta_div_eq_pole_add_mellinVonKochRemainder hz]
            field_simp [riemannZeta_ne_zero_of_one_lt_re hz]; ring)
    let K : ℂ → ℂ := fun z => ((m : ℂ) + 1) * h z + (z - ρ) * (deriv h z + P z * h z)
    have hmain : ∀ᶠ z in nhds ρ, (z - ρ) ^ m * K z = 0 := by
      filter_upwards [hUo.mem_nhds ⟨hre, hne⟩, hfac.eventually_nhds,
        hh_an.eventually_analyticAt, hfac] with z hz hy hhy hfz
      have hpow : HasDerivAt ((fun x : ℂ => x - ρ) ^ (m + 1)) (((m : ℂ) + 1) * (z - ρ) ^ m) z :=
        by simpa [Nat.add_sub_cancel, mul_one] using ((hasDerivAt_id' z).sub_const ρ).pow (m + 1)
      have hdz : deriv riemannZeta z = ((m : ℂ) + 1) * (z - ρ) ^ m * h z +
          (z - ρ) ^ (m + 1) * deriv h z := by
        rw [Filter.EventuallyEq.deriv_eq (show riemannZeta =ᶠ[nhds z] ((fun x : ℂ => x - ρ) ^
          (m + 1) * h) from hy), (hpow.mul hhy.differentiableAt.hasDerivAt).deriv]
        dsimp only [Pi.pow_apply]
      rw [show (z - ρ) ^ m * K z = deriv riemannZeta z + P z * riemannZeta z from by
        rw [hdz, hfz]; dsimp [K]; ring]; exact hcl_u hz
    have hK_ev : ∀ᶠ z in nhdsWithin ρ {ρ}ᶜ, K z = 0 := by
      filter_upwards [nhdsWithin_le_nhds hmain, self_mem_nhdsWithin] with z hmz hzne
      exact (mul_eq_zero.mp hmz).resolve_left (pow_ne_zero m (sub_ne_zero.mpr hzne))
    have hK0 : K ρ = 0 := tendsto_nhds_unique (((hh_an.continuousAt.const_mul _).add
      ((continuousAt_id.sub continuousAt_const).mul (hh_an.deriv.continuousAt.add
        ((hP_on ρ ⟨hre, hne⟩).continuousAt.mul hh_an.continuousAt)))).tendsto.mono_left
      nhdsWithin_le_nhds) (tendsto_const_nhds.congr' (hK_ev.mono fun _ h => h.symm))
    simp only [K, sub_self, zero_mul, add_zero] at hK0
    exact hh_ne ((mul_eq_zero.mp hK0).resolve_left (by exact_mod_cast Nat.succ_ne_zero m))

/-- Von Koch's theorem: `|ψ(x) - x| = O(x^(1/2+ε))` implies `RiemannHypothesis`. -/
theorem vonKoch_implies_rh (hVK : VonKochRemainderBound) : _root_.RiemannHypothesis := by
  have hnf := zero_free_re_gt_half_of_vonKoch hVK; intro s hs hnt h1; by_contra hne
  rcases lt_or_gt_of_ne hne with h | h
  · have r := riemannZeta_zero_reflection_of_re_lt_half hs hnt h1 h; exact hnf _ r.2 r.1
  · exact hnf s h hs

/-- Alias matching Mathlib naming conventions for `vonKoch_implies_rh`. -/
theorem RiemannHypothesis.of_chebyshevPsi_sub_self_isBigO (hVK : VonKochRemainderBound) :
    _root_.RiemannHypothesis := vonKoch_implies_rh hVK
