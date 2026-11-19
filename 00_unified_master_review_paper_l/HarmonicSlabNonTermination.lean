/-
Copyright (c) 2026 Qamar Munawer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qamar Munawer
-/
module

public import RiemannBlueprint.Modules.PeriodicL2CellSumCompression

/-!
# Harmonic-Slab Non-Termination and Coordinate-Space Finite-Truncation Obstruction

This module formalizes Euclid's harmonic-slab non-termination argument on `(0, 1 / 2]` and proves
unconditionally that no finite truncation `N ≥ 1` can annihilate `continuousNymanResidual c N` in
`L²(0, 1]`:

* `harmonicPlane`, `residualHorizonGap_eq_sub_sum_Icc`, `forbiddenHarmonicPlane_mem_gap`:
  any finite stack `n ∈ Icc 2 M` (`M ≥ 2`) covers width `1 / 2 - 1 / (M + 1)`, leaving a
  strictly positive unpartitioned gap `(0, 1 / (M + 1))` containing `1 / (M + 2)`.
* `discreteCellResidual_prime_sub_pred`, `exists_cell_ne_zero`: for any finite `N ≥ 1` and
  prime `p > N` (existing by Euclid's theorem), `discreteCellResidual c N p -
  discreteCellResidual c N (p - 1) = c 1`, forcing a non-zero cell residual on `A_N`.
* `continuousNymanResidual_sq_integral_pos`: for **every** finite `N ≥ 1` and **every**
  `c : ℕ → ℝ`, `0 < ∫ x in Set.Ioc 0 1, (continuousNymanResidual c N x) ^ 2`.
-/

@[expose] public section

open scoped BigOperators
open MeasureTheory Set Finset

/-- Coordinate plane `x_n = 1 / n` separating harmonic cells in `(0, 1]`. -/
noncomputable def harmonicPlane (n : ℕ) : ℝ :=
  1 / (n : ℝ)

/-- Every finite harmonic stack `Icc 2 M` (`2 ≤ M`) leaves an unpartitioned horizon gap of exact
thickness `1 / (M + 1) = harmonicPlane (M + 1)`. -/
theorem residualHorizonGap_eq_sub_sum_Icc {M : ℕ} (hM : 2 ≤ M) :
    (1 / 2 : ℝ) - ∑ n ∈ Finset.Icc 2 M, harmonicCellWidth n = harmonicPlane (M + 1) := by
  rw [sum_Icc_harmonicCellWidth hM, harmonicPlane]; push_cast; ring

/-- The remaining horizon gap thickness `harmonicPlane (M + 1)` is strictly positive. -/
theorem residualHorizonGap_pos (M : ℕ) : 0 < harmonicPlane (M + 1) := by
  unfold harmonicPlane; positivity

/-- **Euclid Harmonic-Slab Contradiction**: for every finite cutoff `M ≥ 2`, the next reflected
plane `x_{M+1} = harmonicPlane (M + 2)` lies strictly inside `(0, harmonicPlane (M + 1)) ⊂
(0, 1 / 2]` and carves out positive width `harmonicCellWidth (M + 1) > 0`. -/
theorem forbiddenHarmonicPlane_mem_gap {M : ℕ} (hM : 2 ≤ M) :
    0 < harmonicPlane (M + 2) ∧
      harmonicPlane (M + 2) < harmonicPlane (M + 1) ∧
      harmonicPlane (M + 1) < 1 / 2 ∧
      0 < harmonicCellWidth (M + 1) := by
  unfold harmonicPlane harmonicCellWidth
  have hM2 : (2 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
  refine ⟨by positivity, ?_, ?_, by positivity⟩
  · push_cast; exact one_div_lt_one_div_of_lt (by linarith) (by linarith)
  · push_cast; exact one_div_lt_one_div_of_lt (by norm_num) (by linarith)

/-- General pointwise affine decomposition on every harmonic cell `n ≤ 1 / x < n + 1` (`n ≥ 1`),
without requiring `D1 c N = 0`. -/
theorem continuousNymanResidual_eq_sub_D1_mul_inv (c : ℕ → ℝ) (N : ℕ) {n : ℕ} (hn : 1 ≤ n)
    {x : ℝ} (hx1 : (n : ℝ) ≤ 1 / x) (hx2 : 1 / x < (n : ℝ) + 1) :
    continuousNymanResidual c N x = discreteCellResidual c N n - D1 c N * (1 / x) := by
  have hterm : ∀ k ∈ Finset.Icc 1 N,
      c k * Int.fract (1 / ((k : ℝ) * x)) =
        (c k / (k : ℝ)) * (1 / x) - c k * ((n / k : ℕ) : ℝ) := fun k hk => by
    rw [Int.fract, floor_one_div_mul_eq_nat_div hn (Finset.mem_Icc.mp hk).1 hx1 hx2,
      Int.cast_natCast, mul_sub, div_eq_mul_inv, mul_inv]; ring
  unfold continuousNymanResidual discreteCellResidual D1
  rw [Finset.sum_congr rfl hterm, Finset.sum_sub_distrib, ← Finset.sum_mul]
  ring

private lemma nat_pred_div_eq_of_not_dvd {p k : ℕ} (hp : 1 ≤ p) (hk : 1 ≤ k) (hnd : ¬k ∣ p) :
    (p - 1) / k = p / k := by
  have hmod_ne : p % k ≠ 0 := fun h0 => hnd (Nat.dvd_of_mod_eq_zero h0)
  have heq : p - 1 = k * (p / k) + (p % k - 1) := by have := Nat.div_add_mod p k; omega
  have hlt : p % k - 1 < k := by have := Nat.mod_lt p hk; omega
  rw [heq, Nat.mul_add_div hk, Nat.div_eq_of_lt hlt, add_zero]

/-- **Prime-Jump Lemma**: for any `N ≥ 1` and any prime `p > N`, moving from cell `p - 1` to
cell `p` isolates solely the `k = 1` harmonic plane, giving exact jump `c 1`. -/
theorem discreteCellResidual_prime_sub_pred (c : ℕ → ℝ) {N p : ℕ} (hN : 1 ≤ N)
    (hp : Nat.Prime p) (hpN : N < p) :
    discreteCellResidual c N p - discreteCellResidual c N (p - 1) = c 1 := by
  have hp1 : 1 ≤ p := hp.one_lt.le
  have h1 : (1 : ℕ) ∈ Finset.Icc 1 N := Finset.mem_Icc.mpr ⟨le_rfl, hN⟩
  have hterm : ∀ k ∈ Finset.Icc 1 N,
      c k * ((p / k : ℕ) : ℝ) - c k * (((p - 1) / k : ℕ) : ℝ) =
        if k = 1 then c 1 else 0 := fun k hk => by
    obtain ⟨hk1, hkN⟩ := Finset.mem_Icc.mp hk
    rcases eq_or_ne k 1 with rfl | hne
    · have hsub : ((p - 1 : ℕ) : ℝ) = (p : ℝ) - 1 := by
        rw [Nat.cast_sub hp1, Nat.cast_one]
      simp only [Nat.div_one, ↓reduceIte, hsub]; ring
    · have hk_lt : k < p := lt_of_le_of_lt hkN hpN
      have hnd : ¬k ∣ p := fun hd => by
        rcases hp.eq_one_or_self_of_dvd k hd with rfl | rfl <;> omega
      rw [nat_pred_div_eq_of_not_dvd hp1 hk1 hnd, sub_self]; simp [hne]
  unfold discreteCellResidual
  rw [add_sub_add_left_eq_sub, ← Finset.sum_sub_distrib, Finset.sum_congr rfl hterm,
    Finset.sum_ite_eq']
  simp [h1]

/-- Under `IsDirichletAnchored c N` (`c 1 = -1`), any prime `p > N` forces unit jump `-1` across
`p - 1 → p`, proving both cells cannot vanish simultaneously. -/
theorem discreteCellResidual_prime_jump_of_isDirichletAnchored {c : ℕ → ℝ} {N p : ℕ}
    (hN : 1 ≤ N) (hc : IsDirichletAnchored c N) (hp : Nat.Prime p) (hpN : N < p) :
    discreteCellResidual c N p - discreteCellResidual c N (p - 1) = -1 := by
  rw [discreteCellResidual_prime_sub_pred c hN hp hpN, hc.2.2]

/-- Every finite truncation `N ≥ 1` and every sequence `c : ℕ → ℝ` has a cell `n ≥ 1` with
non-zero `discreteCellResidual c N n`. -/
theorem exists_cell_ne_zero (c : ℕ → ℝ) {N : ℕ} (hN : 1 ≤ N) :
    ∃ n : ℕ, 1 ≤ n ∧ discreteCellResidual c N n ≠ 0 := by
  by_cases hc1 : c 1 = 0
  · exact ⟨1, le_rfl, by rw [discreteCellResidual_one_eq c hN, hc1]; norm_num⟩
  · obtain ⟨p, hpN, hp⟩ := Nat.exists_infinite_primes (N + 1)
    have hjump := discreteCellResidual_prime_sub_pred c hN hp (by omega : N < p)
    by_cases hpred : discreteCellResidual c N (p - 1) = 0
    · refine ⟨p, hp.one_lt.le, fun hp0 => ?_⟩
      rw [hp0, hpred, sub_zero] at hjump; exact hc1 hjump.symm
    · exact ⟨p - 1, Nat.le_sub_one_of_lt hp.one_lt, hpred⟩

/-- Square of `continuousNymanResidual c N` is bounded and measurable, hence integrable on
`Set.Ioc 0 1`. -/
theorem continuousNymanResidual_sq_integrableOn_Ioc (c : ℕ → ℝ) (N : ℕ) :
    IntegrableOn (fun x : ℝ => (continuousNymanResidual c N x) ^ 2) (Set.Ioc (0 : ℝ) 1) := by
  have hm_term : ∀ k : ℕ, Measurable (fun x : ℝ => c k * Int.fract (1 / ((k : ℝ) * x))) :=
    fun k => measurable_const.mul
      (measurable_fract.comp (measurable_const.div (measurable_const.mul measurable_id)))
  have hm : AEStronglyMeasurable
      (fun x : ℝ => (continuousNymanResidual c N x) ^ 2) (volume.restrict (Set.Ioc 0 1)) :=
    ((measurable_const.sub (Finset.measurable_sum _ fun k _ => hm_term k)).pow_const
      2).aestronglyMeasurable
  have hbound : ∀ᵐ x ∂(volume.restrict (Set.Ioc (0 : ℝ) 1)),
      ‖(continuousNymanResidual c N x) ^ 2‖ ≤ (1 + ∑ k ∈ Finset.Icc 1 N, |c k|) ^ 2 := by
    refine Filter.Eventually.of_forall fun x => ?_
    rw [Real.norm_eq_abs, abs_sq, ← sq_abs (continuousNymanResidual c N x)]
    refine pow_le_pow_left₀ (abs_nonneg _) ?_ 2
    have hsum : |∑ k ∈ Finset.Icc 1 N, c k * Int.fract (1 / ((k : ℝ) * x))| ≤
        ∑ k ∈ Finset.Icc 1 N, |c k| :=
      (Finset.abs_sum_le_sum_abs _ _).trans <| Finset.sum_le_sum fun k _ => by
        rw [abs_mul]
        exact mul_le_of_le_one_right (abs_nonneg _)
          (by rw [abs_of_nonneg (Int.fract_nonneg _)]; exact (Int.fract_lt_one _).le)
    calc |continuousNymanResidual c N x|
        ≤ |(1 : ℝ)| + |∑ k ∈ Finset.Icc 1 N, c k * Int.fract (1 / ((k : ℝ) * x))| :=
          abs_sub _ _
      _ ≤ 1 + ∑ k ∈ Finset.Icc 1 N, |c k| := by rw [abs_one]; exact add_le_add le_rfl hsum
  exact IntegrableOn.of_bound measure_Ioc_lt_top hm _ hbound

private lemma integral_sq_pos_of_sub_Ioc {a b d : ℝ} (hab : a < b) (ha : 0 ≤ a) (hb : b ≤ 1)
    {f : ℝ → ℝ} (hf : IntegrableOn (fun x => (f x) ^ 2) (Set.Ioc 0 1)) (hd : 0 < d)
    (hlower : ∀ x ∈ Set.Ioc a b, d ≤ (f x) ^ 2) :
    0 < ∫ x in Set.Ioc (0 : ℝ) 1, (f x) ^ 2 := by
  have hsub : Set.Ioc a b ⊆ Set.Ioc 0 1 := Set.Ioc_subset_Ioc ha hb
  have hconst : d * (b - a) ≤ ∫ x in Set.Ioc a b, (f x) ^ 2 := by
    have hi : IntegrableOn (fun _ : ℝ => d) (Set.Ioc a b) :=
      integrableOn_const (hs := measure_Ioc_lt_top.ne)
    have h1 := MeasureTheory.setIntegral_mono_on hi (hf.mono_set hsub) measurableSet_Ioc hlower
    rwa [MeasureTheory.setIntegral_const, smul_eq_mul, Real.volume_real_Ioc_of_le hab.le,
      mul_comm] at h1
  have h2 := MeasureTheory.setIntegral_mono_set hf
    (Filter.Eventually.of_forall fun x => sq_nonneg (f x))
    (Filter.Eventually.of_forall fun _ hx => hsub hx)
  change (∫ x in Set.Ioc a b, (f x) ^ 2) ≤ _ at h2
  linarith [mul_pos hd (sub_pos.mpr hab)]

/-- **Finite-Truncation Impossibility Theorem**: for **every** finite cutoff `N ≥ 1` and **every**
coefficient vector `c : ℕ → ℝ`, the `L²(0, 1]` residual energy of `continuousNymanResidual c N` is
strictly positive. Zero `L²` energy strictly requires `N → ∞`. -/
theorem continuousNymanResidual_sq_integral_pos (c : ℕ → ℝ) {N : ℕ} (hN : 1 ≤ N) :
    0 < ∫ x in Set.Ioc (0 : ℝ) 1, (continuousNymanResidual c N x) ^ 2 := by
  have hf := continuousNymanResidual_sq_integrableOn_Ioc c N
  by_cases hD1 : D1 c N = 0
  · obtain ⟨n, hn1, hne⟩ := exists_cell_ne_zero c hN
    have hpos_val : 0 < (discreteCellResidual c N n) ^ 2 := sq_pos_of_ne_zero hne
    have hwid : 0 < harmonicCellWidth n := by unfold harmonicCellWidth; positivity
    have hle : (1 : ℝ) / ((n : ℝ) + 1) < 1 / (n : ℝ) :=
      one_div_lt_one_div_of_lt (Nat.cast_pos.mpr hn1) (by linarith)
    have hsub : Set.Ioc (1 / ((n : ℝ) + 1)) (1 / (n : ℝ)) ⊆ Set.Ioc 0 1 :=
      Set.Ioc_subset_Ioc (by positivity) (div_le_self zero_le_one (by exact_mod_cast hn1))
    have heq := continuousNymanResidual_sq_mul_width_eq c N hn1 hD1
    rw [intervalIntegral.integral_of_le hle.le] at heq
    have h2 := MeasureTheory.setIntegral_mono_set hf
      (Filter.Eventually.of_forall fun x => sq_nonneg (continuousNymanResidual c N x))
      (Filter.Eventually.of_forall fun _ hx => hsub hx)
    change (∫ x in Set.Ioc (1 / ((n : ℝ) + 1)) (1 / (n : ℝ)),
      (continuousNymanResidual c N x) ^ 2) ≤ _ at h2
    linarith [mul_pos hpos_val hwid]
  · have hD1sq : 0 < (D1 c N) ^ 2 := sq_pos_of_ne_zero hD1
    by_cases hrat : (1 + c 1) / D1 c N ≤ 3 / 2
    · refine integral_sq_pos_of_sub_Ioc (by norm_num : (1 / 2 : ℝ) < 5 / 8)
        (by norm_num) (by norm_num) hf (by positivity : 0 < (D1 c N / 10) ^ 2) ?_
      intro x ⟨hx1, hx2⟩
      have hx_pos : 0 < x := lt_trans (by norm_num) hx1
      have hlo : ((1 : ℕ) : ℝ) ≤ 1 / x := by
        push_cast; exact (one_le_div hx_pos).mpr (by linarith)
      have hhi : 1 / x < ((1 : ℕ) : ℝ) + 1 := (div_lt_iff₀ hx_pos).mpr (by norm_num; linarith)
      rw [continuousNymanResidual_eq_sub_D1_mul_inv c N le_rfl hlo hhi,
        discreteCellResidual_one_eq c hN]
      have hinv : 8 / 5 ≤ 1 / x := (le_div_iff₀ hx_pos).mpr (by linarith)
      have hsq : (1 / 10 : ℝ) ^ 2 ≤ (1 / x - (1 + c 1) / D1 c N) ^ 2 :=
        pow_le_pow_left₀ (by norm_num) (by linarith) 2
      have hid : 1 + c 1 - D1 c N * (1 / x) = -D1 c N * (1 / x - (1 + c 1) / D1 c N) := by
        field_simp [hD1]; ring
      rw [hid, mul_pow, neg_sq]
      calc (D1 c N / 10) ^ 2 = (D1 c N) ^ 2 * (1 / 10 : ℝ) ^ 2 := by ring
        _ ≤ (D1 c N) ^ 2 * (1 / x - (1 + c 1) / D1 c N) ^ 2 :=
            mul_le_mul_of_nonneg_left hsq hD1sq.le
    · push Not at hrat
      refine integral_sq_pos_of_sub_Ioc (by norm_num : (3 / 4 : ℝ) < 1)
        (by norm_num) le_rfl hf (by positivity : 0 < (D1 c N / 6) ^ 2) ?_
      intro x ⟨hx1, hx2⟩
      have hx_pos : 0 < x := lt_trans (by norm_num) hx1
      have hlo : ((1 : ℕ) : ℝ) ≤ 1 / x := by push_cast; exact (one_le_div hx_pos).mpr hx2
      have hhi : 1 / x < ((1 : ℕ) : ℝ) + 1 := (div_lt_iff₀ hx_pos).mpr (by norm_num; linarith)
      rw [continuousNymanResidual_eq_sub_D1_mul_inv c N le_rfl hlo hhi,
        discreteCellResidual_one_eq c hN]
      have hinv : 1 / x ≤ 4 / 3 := (div_le_iff₀ hx_pos).mpr (by linarith)
      have hsq : (1 / 6 : ℝ) ^ 2 ≤ ((1 + c 1) / D1 c N - 1 / x) ^ 2 :=
        pow_le_pow_left₀ (by norm_num) (by linarith) 2
      have hid : 1 + c 1 - D1 c N * (1 / x) = D1 c N * ((1 + c 1) / D1 c N - 1 / x) := by
        field_simp [hD1]
      rw [hid, mul_pow]
      calc (D1 c N / 6) ^ 2 = (D1 c N) ^ 2 * (1 / 6 : ℝ) ^ 2 := by ring
        _ ≤ (D1 c N) ^ 2 * ((1 + c 1) / D1 c N - 1 / x) ^ 2 :=
            mul_le_mul_of_nonneg_left hsq hD1sq.le
