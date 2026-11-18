/-
Copyright (c) 2026 Qamar Munawer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qamar Munawer
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Tactic.Linarith
public import RiemannBlueprint.UpstreamPRs.UpstreamPR_3A_VasyuninIntegral
public import RiemannBlueprint.UpstreamPRs.UpstreamPR_4A_AffineLagrangeProjection

/-!
# Smooth Vasyunin Kernel, Cotangent Sums, and Rank-4 Boundary-Dirichlet Algebra

This file defines the smooth Vasyunin kernel `GSmooth`, the off-diagonal cotangent Gram
kernel `vasyuninCotSum` / `vasyuninGCot`, and the cotangent quadratic form `QCot` / `SCot`.
It establishes symmetry and diagonal identities and proves the Rank-4 outer-product
factorization (`GSmooth_eq_rank4`) together with the affine pure-cotangent identity
`affine_bdr_pure_cotangent_identity` on `{c | D1 c N = 0 ∧ D0 c N = 2}`.
-/

@[expose] public section

open scoped BigOperators

/-- Finite Dirichlet derivative at `s = 0`: `- ∑ k ∈ Finset.Icc 1 N, c k * log k`. -/
noncomputable def D0Deriv (c : ℕ → ℝ) (N : ℕ) : ℝ :=
  - ∑ k ∈ Finset.Icc 1 N, c k * Real.log (k : ℝ)

/-- Finite Dirichlet derivative at `s = 1`: `- ∑ k ∈ Finset.Icc 1 N, c k * log k / k`. -/
noncomputable def D1Deriv (c : ℕ → ℝ) (N : ℕ) : ℝ :=
  - ∑ k ∈ Finset.Icc 1 N, c k * Real.log (k : ℝ) / (k : ℝ)

/-- Basis vector `e_k = 1` for the Rank-4 outer-product expansion. -/
def vecE (_k : ℕ) : ℝ := 1

/-- Basis vector `l_k = log k` for the Rank-4 outer-product expansion. -/
noncomputable def vecL (k : ℕ) : ℝ := Real.log (k : ℝ)

/-- Basis vector `h_k = 1 / k` for the Rank-4 outer-product expansion. -/
noncomputable def vecH (k : ℕ) : ℝ := (k : ℝ)⁻¹

/-- Basis vector `m_k = (log k) / k` for the Rank-4 outer-product expansion. -/
noncomputable def vecM (k : ℕ) : ℝ := (k : ℝ)⁻¹ * Real.log (k : ℝ)

/-- Smooth Vasyunin cross-kernel `G_{j,k}^{(smooth)}(γ)`. -/
noncomputable def GSmooth (gamma_E : ℝ) (j k : ℕ) : ℝ :=
  ((Real.log (2 * Real.pi) - gamma_E) * ((j : ℝ) + (k : ℝ)) +
   ((j : ℝ) - (k : ℝ)) * Real.log ((k : ℝ) / (j : ℝ)) - 2) / (2 * (j : ℝ) * (k : ℝ))

/-- Explicit Rank-4 symmetric outer-product form of `GSmooth`. -/
noncomputable def GSmoothRank4 (gamma_E : ℝ) (j k : ℕ) : ℝ :=
  ((Real.log (2 * Real.pi) - gamma_E) / 2) * (vecE j * vecH k + vecH j * vecE k) +
  (1 / 2) * (vecE j * vecM k + vecM j * vecE k) -
  (1 / 2) * (vecL j * vecH k + vecH j * vecL k) -
  vecH j * vecH k

/-- Vasyunin's discrete cotangent sum `∑_{m=1}^{a-1} {m * b / a} * cot (π * m / a)`. -/
noncomputable def vasyuninCotSum (a b : ℕ) : ℝ :=
  ∑ m ∈ Finset.Ico 1 a,
    Int.fract ((m : ℝ) * (b : ℝ) / (a : ℝ)) *
      (Real.cos (Real.pi * (m : ℝ) / (a : ℝ)) / Real.sin (Real.pi * (m : ℝ) / (a : ℝ)))

/-- Cotangent component `g_{j,k}^{(cot)}` of Vasyunin's cross Gram matrix. -/
noncomputable def vasyuninGCot (j k : ℕ) : ℝ :=
  -(Real.pi / (2 * (j : ℝ) * (k : ℝ))) * (vasyuninCotSum j k + vasyuninCotSum k j)

/-- Quadratic form of a kernel `g_cot` on `Finset.Icc 1 N`. -/
noncomputable def QCot (g_cot : ℕ → ℕ → ℝ) (c : ℕ → ℝ) (N : ℕ) : ℝ :=
  ∑ j ∈ Finset.Icc 1 N, ∑ k ∈ Finset.Icc 1 N, c j * c k * g_cot j k

/-- Symmetric negated cotangent quadratic form `SCot g_cot c N = -QCot g_cot c N`. -/
noncomputable def SCot (g_cot : ℕ → ℕ → ℝ) (c : ℕ → ℝ) (N : ℕ) : ℝ :=
  - QCot g_cot c N

/-- Symmetry of the smooth Vasyunin kernel `GSmooth`. -/
theorem GSmooth_comm (gamma_E : ℝ) {j k : ℕ} (hj : 0 < j) (hk : 0 < k) :
    GSmooth gamma_E j k = GSmooth gamma_E k j := by
  have hj_ne : (j : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hj.ne'
  have hk_ne : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hk.ne'
  dsimp [GSmooth]
  rw [show Real.log ((j : ℝ) / (k : ℝ)) = -Real.log ((k : ℝ) / (j : ℝ)) by
    rw [Real.log_div hj_ne hk_ne, Real.log_div hk_ne hj_ne]; ring]
  ring

/-- Diagonal evaluation of the smooth Vasyunin kernel `GSmooth`. -/
theorem GSmooth_diag (gamma_E : ℝ) {k : ℕ} (hk : 0 < k) :
    GSmooth gamma_E k k = (Real.log (2 * Real.pi) - gamma_E) / (k : ℝ) - 1 / ((k : ℝ) ^ 2) := by
  have hk_ne : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hk.ne'
  dsimp [GSmooth]
  rw [div_self hk_ne, Real.log_one, mul_zero, add_zero]
  field_simp [hk_ne]
  ring

/-- Diagonal vanishing of `vasyuninCotSum`: `vasyuninCotSum k k = 0`. -/
theorem vasyuninCotSum_diag (k : ℕ) : vasyuninCotSum k k = 0 := by
  unfold vasyuninCotSum
  by_cases hk : k = 0
  · subst hk; rfl
  have hk_pos : (0 : ℝ) < (k : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hk)
  refine Finset.sum_eq_zero fun m _ => ?_
  rw [mul_div_cancel_right₀ (m : ℝ) hk_pos.ne', Int.fract_natCast, zero_mul]

/-- Diagonal vanishing of `vasyuninGCot`: `vasyuninGCot k k = 0`. -/
theorem vasyuninGCot_diag (k : ℕ) : vasyuninGCot k k = 0 := by
  unfold vasyuninGCot
  rw [vasyuninCotSum_diag k, add_zero, mul_zero]

/-- Symmetry of the cotangent Gram kernel `vasyuninGCot`. -/
theorem vasyuninGCot_comm (j k : ℕ) : vasyuninGCot j k = vasyuninGCot k j := by
  dsimp [vasyuninGCot]
  rw [show 2 * (j : ℝ) * (k : ℝ) = 2 * (k : ℝ) * (j : ℝ) by ring, add_comm (vasyuninCotSum j k)]

/-- Diagonal value of the full Vasyunin Gram entry `GSmooth + vasyuninGCot`. -/
theorem vasyuninGram_diag (gamma_E : ℝ) {k : ℕ} (hk : 0 < k) :
    GSmooth gamma_E k k + vasyuninGCot k k =
      (Real.log (2 * Real.pi) - gamma_E) / (k : ℝ) - 1 / ((k : ℝ) ^ 2) := by
  rw [vasyuninGCot_diag k, add_zero]
  exact GSmooth_diag gamma_E hk

/-- Pointwise Rank-4 outer-product factorization of `GSmooth`. -/
theorem GSmooth_eq_rank4 (gamma_E : ℝ) {j k : ℕ} (hj : 0 < j) (hk : 0 < k) :
    GSmooth gamma_E j k = GSmoothRank4 gamma_E j k := by
  have hj_ne : (j : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hj.ne'
  have hk_ne : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hk.ne'
  dsimp [GSmooth, GSmoothRank4, vecE, vecL, vecH, vecM]
  rw [Real.log_div hk_ne hj_ne]
  field_simp [hj_ne, hk_ne]
  ring

private lemma b_dot_c_eq_boundary (gamma_E : ℝ) (c : ℕ → ℝ) (N : ℕ) :
    ∑ k ∈ Finset.Icc 1 N, c k * bVasyunin k gamma_E =
      (1 - gamma_E) * D1 c N - D1Deriv c N := by
  have h_pt : ∀ k ∈ Finset.Icc 1 N,
      c k * bVasyunin k gamma_E =
        (1 - gamma_E) * (c k / (k : ℝ)) + c k * Real.log (k : ℝ) / (k : ℝ) := fun k _ => by
    dsimp [bVasyunin]; ring
  rw [Finset.sum_congr rfl h_pt, Finset.sum_add_distrib, ← Finset.mul_sum]
  dsimp [D1, D1Deriv]
  ring

private lemma smooth_vasyunin_double_sum_eq_boundary (gamma_E : ℝ) (c : ℕ → ℝ) (N : ℕ) :
    ∑ j ∈ Finset.Icc 1 N, ∑ k ∈ Finset.Icc 1 N, c j * c k * GSmooth gamma_E j k =
      (Real.log (2 * Real.pi) - gamma_E) * D0 c N * D1 c N -
        D0 c N * D1Deriv c N + D0Deriv c N * D1 c N - (D1 c N) ^ 2 := by
  have h_sum : ∑ j ∈ Finset.Icc 1 N, ∑ k ∈ Finset.Icc 1 N, c j * c k * GSmooth gamma_E j k =
      ∑ j ∈ Finset.Icc 1 N, ∑ k ∈ Finset.Icc 1 N,
        (((Real.log (2 * Real.pi) - gamma_E) / 2) *
            ((c j * vecE j) * (c k * vecH k) + (c j * vecH j) * (c k * vecE k)) +
         (1 / 2) * ((c j * vecE j) * (c k * vecM k) + (c j * vecM j) * (c k * vecE k)) -
         (1 / 2) * ((c j * vecL j) * (c k * vecH k) + (c j * vecH j) * (c k * vecL k)) -
         (c j * vecH j) * (c k * vecH k)) := by
    refine Finset.sum_congr rfl fun j hj => Finset.sum_congr rfl fun k hk => ?_
    rw [GSmooth_eq_rank4 gamma_E (Finset.mem_Icc.mp hj).1 (Finset.mem_Icc.mp hk).1]
    dsimp [GSmoothRank4]; ring
  have hE : ∑ k ∈ Finset.Icc 1 N, c k * vecE k = D0 c N := by simp [vecE, D0]
  have hL : ∑ k ∈ Finset.Icc 1 N, c k * vecL k = - D0Deriv c N := by dsimp [vecL, D0Deriv]; ring
  have hH : ∑ k ∈ Finset.Icc 1 N, c k * vecH k = D1 c N :=
    Finset.sum_congr rfl fun _ _ => by dsimp [vecH]; ring
  have hM : ∑ k ∈ Finset.Icc 1 N, c k * vecM k = - D1Deriv c N := by
    rw [show ∑ k ∈ Finset.Icc 1 N, c k * vecM k =
      ∑ k ∈ Finset.Icc 1 N, c k * Real.log (k : ℝ) / (k : ℝ) from
      Finset.sum_congr rfl fun _ _ => by dsimp [vecM]; ring]
    dsimp [D1Deriv]; ring
  have h_const : ∀ (a : ℝ) (F : ℕ → ℕ → ℝ),
      ∑ j ∈ Finset.Icc 1 N, ∑ k ∈ Finset.Icc 1 N, a * F j k =
        a * ∑ j ∈ Finset.Icc 1 N, ∑ k ∈ Finset.Icc 1 N, F j k := fun _ _ => by
    simp only [← Finset.mul_sum]
  have h_outer : ∀ f g : ℕ → ℝ,
      ∑ j ∈ Finset.Icc 1 N, ∑ k ∈ Finset.Icc 1 N, f j * g k =
        (∑ j ∈ Finset.Icc 1 N, f j) * (∑ k ∈ Finset.Icc 1 N, g k) := fun _ _ => by
    simp only [← Finset.mul_sum, ← Finset.sum_mul]
  rw [h_sum]
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, h_const]
  simp_rw [h_outer, hE, hL, hH, hM]
  ring

/-- Boundary-locked affine pure cotangent identity on `A_N`: when `D1 c N = 0` and `D0 c N = 2`,
all smooth and logarithmic boundary terms cancel, leaving `1 + Q_cot`. -/
theorem affine_bdr_pure_cotangent_identity (c : ℕ → ℝ) (N : ℕ) (gamma_E Q_cot : ℝ)
    (hD1 : D1 c N = 0) (hD0 : D0 c N = 2) :
    1 - 2 * (∑ k ∈ Finset.Icc 1 N, c k * bVasyunin k gamma_E) +
      (∑ j ∈ Finset.Icc 1 N, ∑ k ∈ Finset.Icc 1 N, c j * c k * GSmooth gamma_E j k) + Q_cot =
      1 + Q_cot := by
  rw [b_dot_c_eq_boundary, smooth_vasyunin_double_sum_eq_boundary, hD1, hD0]
  ring

/-- Interval integrability of `{1 / (j * x)} * {1 / (k * x)}` on any interval `[a, b]`. -/
theorem intervalIntegrable_recipFractScaled_mul (j k : ℕ) (a b : ℝ) :
    IntervalIntegrable (fun x => recipFractScaled j x * recipFractScaled k x)
      MeasureTheory.volume a b := by
  have hm : Measurable (fun x => recipFractScaled j x * recipFractScaled k x) :=
    (measurable_fract.comp (measurable_const.div (measurable_const.mul measurable_id))).mul
      (measurable_fract.comp (measurable_const.div (measurable_const.mul measurable_id)))
  refine (intervalIntegrable_const (c := (1 : ℝ))).mono_fun' hm.aestronglyMeasurable
    (MeasureTheory.ae_of_all _ fun x => ?_)
  dsimp only [recipFractScaled]
  have h1 := Int.fract_nonneg (1 / ((j : ℝ) * x))
  have h2 := Int.fract_nonneg (1 / ((k : ℝ) * x))
  have h3 := Int.fract_lt_one (1 / ((j : ℝ) * x))
  have h4 := Int.fract_lt_one (1 / ((k : ℝ) * x))
  rw [Real.norm_of_nonneg (mul_nonneg h1 h2)]; nlinarith

/-- On `(1 / (n + 1), 1 / n)` for `1 ≤ j, n`, `{1 / (j * x)} = 1 / (j * x) - ⌊n / j⌋`. -/
theorem recipFractScaled_eq_of_mem_Ioo {j n : ℕ} (hj : 1 ≤ j) (hn : 1 ≤ n) {x : ℝ}
    (hx : x ∈ Set.Ioo (1 / ((n : ℝ) + 1)) (1 / (n : ℝ))) :
    recipFractScaled j x = 1 / ((j : ℝ) * x) - ((n / j : ℕ) : ℝ) := by
  have hjx_pos : 0 < (j : ℝ) * x :=
    mul_pos (Nat.cast_pos.mpr hj) (lt_trans (by positivity) hx.1)
  have hx_pos : 0 < x := lt_trans (by positivity) hx.1
  have h_inv_gt : (n : ℝ) < 1 / x := (lt_one_div hx_pos (Nat.cast_pos.mpr hn)).mp hx.2
  have h_inv_lt : 1 / x < (n : ℝ) + 1 := (one_div_lt (by positivity) hx_pos).mp hx.1
  have hrem : n % j < j := Nat.mod_lt n hj
  have hq_lo : ((n / j : ℕ) : ℝ) ≤ 1 / ((j : ℝ) * x) := by
    have h1 : (j : ℝ) * ((n / j : ℕ) : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast (by rw [mul_comm]; exact Nat.div_mul_le_self n j)
    rw [le_div_iff₀ hjx_pos]; nlinarith [(lt_div_iff₀ hx_pos).mp h_inv_gt]
  have hq_hi : 1 / ((j : ℝ) * x) < ((n / j : ℕ) : ℝ) + 1 := by
    have h2nat : n + 1 ≤ j * (n / j + 1) := by
      have : n = j * (n / j) + n % j := (Nat.div_add_mod n j).symm
      linarith [show j * (n / j + 1) = j * (n / j) + j by ring]
    have h2 : (n : ℝ) + 1 ≤ (j : ℝ) * (((n / j : ℕ) : ℝ) + 1) := by exact_mod_cast h2nat
    rw [div_lt_iff₀ hjx_pos]; nlinarith [(div_lt_iff₀ hx_pos).mp h_inv_lt]
  rw [recipFractScaled, Int.fract, Int.floor_eq_iff.mpr ⟨by exact_mod_cast hq_lo,
    by exact_mod_cast hq_hi⟩, Int.cast_natCast]

/-- Harmonic interval splitting on `[1 / L, 1]` into unit sub-intervals `[1 / (n + 1), 1 / n]`. -/
theorem intervalIntegral_split_recip (f : ℝ → ℝ)
    (hf : ∀ a b : ℝ, IntervalIntegrable f MeasureTheory.volume a b) (L : ℕ) (hL : 1 ≤ L) :
    (∫ x in (1 / (L : ℝ))..1, f x) =
      ∑ n ∈ Finset.Ico 1 L, ∫ x in (1 / ((n : ℝ) + 1))..(1 / (n : ℝ)), f x := by
  induction L, hL using Nat.le_induction with
  | base => simp
  | succ k hk ih =>
    push_cast
    rw [← intervalIntegral.integral_add_adjacent_intervals
      (hf (1 / ((k : ℝ) + 1)) (1 / (k : ℝ))) (hf (1 / (k : ℝ)) 1), ih,
      Finset.sum_Ico_succ_top hk, add_comm]
