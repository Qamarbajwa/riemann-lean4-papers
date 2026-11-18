import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Data.Matrix.Mul
import RiemannBlueprint.MellinFracPart
import RiemannBlueprint.Section8_VasyuninBDR
import RiemannBlueprint.CMIAuditBridge

/-!
# Open-Strip Rouché Zero-Exclusion, Penetration Lower Bounds & Distributed Rank-4 Neutrality

Formalizes under the standing epistemic invariant **`NO_RH_PROOF = TRUE`**:
1. Exact complex-strip coupling `stripDefect N c s = 1 + ζ(s) D_c(s)` with the unit-interval
   Mellin residual `s * Mellin(1 - Φ_c, s)` via `MellinFracPart`.
2. Unconditional entire holomorphy of `dirichletPoly N c` and `{1}ᶜ`-analyticity of
   `s ↦ ζ(s) * dirichletPoly N c s`.
3. Algebraic neutrality of weighted Rank-4 distributed orthogonal projections
   (`distributedProj_satisfies_constraints`) and endpoint `C^1` flatness of the
   scale-invariant log-Hermite window `logHermitePsi t = 1 - 3 t^2 + 2 t^3`.
4. **Theorem 1 (Unconditional Pointwise Non-Vanishing & Penetration Limit):**
   `‖1 + ζ(s) D_c(s)‖ < 1` forces both `ζ(s) ≠ 0`, `D_c(s) ≠ 0`, and the quantitative
   lower bound `(1 - ‖1 + ζ(s) D_c(s)‖) / ‖ζ(s)‖ ≤ ‖D_c(s)‖` explaining the `1/δ`
   critical-line penetration barrier as `δ → 0^+`.
5. **Theorem 1(1) & Theorem 2 (⇐) (Zero `sorry`, Zero Custom Axioms):**
   Parameterized cleanly by the classical holomorphic rectangle Rouché principle
   `RectRoucheProperty`, uniform boundary bounds `max_{∂R} ‖1 + ζ D_c‖ < 1` exclude all
   interior zeros on `R` (`theorem1_rouche_zero_exclusion`) and boundary exhaustion of
   all strip rectangles implies `_root_.RiemannHypothesis`
   (`theorem2_rouche_exhaustion_implies_rh`).
-/

namespace RiemannBlueprint.OpenStripRouche

/-- Finite Dirichlet polynomial `D_c(s) = ∑_{k=1}^N c_k k^{-s}` of horizon `N`. -/
noncomputable def dirichletPoly (N : ℕ) (c : ℕ → ℂ) (s : ℂ) : ℂ :=
  ∑ k ∈ Finset.Ico 1 (N + 1), c k * (k : ℂ) ^ (-s)

/-- Strip Rouché defect `E_c(s) = 1 + ζ(s) D_c(s)` approximating `1 - (-1) = 0` when
`D_c(s) ≈ -1 / ζ(s)`. -/
noncomputable def stripDefect (N : ℕ) (c : ℕ → ℂ) (s : ℂ) : ℂ :=
  1 + riemannZeta s * dirichletPoly N c s

/-- Unconditional Mellin-residual coupling identity in the critical strip `0 < Re(s) < 1`:
`1 + ζ(s) D_c(s) = s * ∫_0^1 (1 - Φ_c(x)) x^{s-1} dx` (written via `MellinFracPart`). -/
theorem stripDefect_eq_mul_mellin_residual (N : ℕ) (c : ℕ → ℂ) (s : ℂ)
    (hs_pos : 0 < s.re) (hs_lt_one : s.re < 1) :
    stripDefect N c s = s *
      ((∫ x in Set.Ioc (0 : ℝ) 1, (x : ℂ) ^ (s - 1)) -
       (∫ x in Set.Ioi (0 : ℝ),
         (∑ k ∈ Finset.Ico 1 (N + 1),
           c k * (NumberTheory.MellinFracPart.recipFractScaled k x : ℂ)) *
           (x : ℂ) ^ (s - 1))) := by
  have hs_ne : s ≠ 0 := by
    intro h
    rw [h] at hs_pos
    simp at hs_pos
  have hres :=
    NumberTheory.MellinFracPart.mellin_baezDuarte_residual_of_tsum_continuation
      N c s hs_pos hs_lt_one
  change (∫ x in Set.Ioc (0 : ℝ) 1, (x : ℂ) ^ (s - 1)) -
      (∫ x in Set.Ioi (0 : ℝ),
        (∑ k ∈ Finset.Ico 1 (N + 1),
          c k * (NumberTheory.MellinFracPart.recipFractScaled k x : ℂ)) *
          (x : ℂ) ^ (s - 1)) =
      stripDefect N c s / s at hres
  rw [hres]
  field_simp [hs_ne]

/-- Every term `s ↦ a * (k : ℂ) ^ (-s)` (`k ≥ 1`) is entire on `ℂ`. -/
lemma differentiableAt_const_mul_nat_neg_cpow (k : ℕ) (hk : 1 ≤ k) (a s : ℂ) :
    DifferentiableAt ℂ (fun z : ℂ => a * (k : ℂ) ^ (-z)) s := by
  have hk_re : 0 < ((k : ℂ)).re := by
    simpa using (Nat.cast_pos.mpr hk : (0 : ℝ) < k)
  have hpow : DifferentiableAt ℂ (fun z : ℂ => (k : ℂ) ^ (-z)) s :=
    (differentiableAt_const (k : ℂ)).cpow differentiableAt_id.neg (Or.inl hk_re)
  exact (differentiableAt_const a).mul hpow

/-- `dirichletPoly N c` is complex-differentiable everywhere on `ℂ` (entire). -/
theorem differentiable_dirichletPoly (N : ℕ) (c : ℕ → ℂ) :
    Differentiable ℂ (dirichletPoly N c) := by
  intro s
  unfold dirichletPoly
  exact DifferentiableAt.fun_sum fun k hk =>
    differentiableAt_const_mul_nat_neg_cpow k (Finset.mem_Ico.mp hk).1 (c k) s

/-- `dirichletPoly N c` is analytic on all of `ℂ`. -/
theorem analyticOnNhd_dirichletPoly (N : ℕ) (c : ℕ → ℂ) :
    AnalyticOnNhd ℂ (dirichletPoly N c) Set.univ :=
  DifferentiableOn.analyticOnNhd
    (differentiable_dirichletPoly N c).differentiableOn isOpen_univ

/-- The holomorphic strip product `s ↦ ζ(s) D_c(s)` is analytic everywhere away from `s = 1`. -/
theorem analyticOnNhd_zeta_mul_dirichletPoly (N : ℕ) (c : ℕ → ℂ) :
    AnalyticOnNhd ℂ (fun s : ℂ => riemannZeta s * dirichletPoly N c s) {1}ᶜ :=
  analyticOn_riemannZeta.mul
    ((analyticOnNhd_dirichletPoly N c).mono (Set.subset_univ {1}ᶜ))

/-- Scale-invariant `C^1` log-Hermite window `ψ(t) = 1 - 3 t^2 + 2 t^3`. -/
def logHermitePsi (t : ℝ) : ℝ :=
  1 - 3 * t ^ 2 + 2 * t ^ 3

@[simp]
theorem logHermitePsi_zero : logHermitePsi 0 = 1 := by
  simp [logHermitePsi]

@[simp]
theorem logHermitePsi_one : logHermitePsi 1 = 0 := by
  norm_num [logHermitePsi]

/-- Derivative of `logHermitePsi` at any `t : ℝ`, showing `ψ'(0) = 0` and `ψ'(1) = 0`. -/
theorem hasDerivAt_logHermitePsi (t : ℝ) :
    HasDerivAt logHermitePsi (-6 * t + 6 * t ^ 2) t := by
  have h1 : HasDerivAt (fun x : ℝ => (1 : ℝ) - 3 * x ^ 2) (0 - 3 * (2 * t ^ 1)) t :=
    (hasDerivAt_const t (1 : ℝ)).sub ((hasDerivAt_pow 2 t).const_mul 3)
  have h2 : HasDerivAt (fun x : ℝ => 2 * x ^ 3) (2 * (3 * t ^ 2)) t :=
    (hasDerivAt_pow 3 t).const_mul 2
  have hfn : logHermitePsi = fun x : ℝ => ((1 : ℝ) - 3 * x ^ 2) + 2 * x ^ 3 := by
    ext x
    simp [logHermitePsi]
  have hderiv : -6 * t + 6 * t ^ 2 = (0 - 3 * (2 * t ^ 1)) + 2 * (3 * t ^ 2) := by ring
  rw [hfn, hderiv]
  exact h1.add h2

theorem deriv_logHermitePsi_zero : deriv logHermitePsi 0 = 0 := by
  simpa using (hasDerivAt_logHermitePsi 0).deriv

theorem deriv_logHermitePsi_one : deriv logHermitePsi 1 = 0 := by
  simpa using (hasDerivAt_logHermitePsi 1).deriv

/-- Weighted distributed Rank-4 orthogonal projection onto any 4-constraint affine subspace
`∑_{k=1}^N u_{i,k} c_k = t_i` (`i ∈ Fin 4`), avoiding inversion of the full `N × N` Gram matrix. -/
noncomputable def distributedProj (w : ℕ → ℝ) (u : Fin 4 → ℕ → ℝ) (c0 : ℕ → ℝ)
    (Ainv : Matrix (Fin 4) (Fin 4) ℝ) (t : Fin 4 → ℝ) (N : ℕ) (k : ℕ) : ℝ :=
  let res : Fin 4 → ℝ := fun i => (∑ j ∈ Finset.Icc 1 N, u i j * c0 j) - t i
  let lam : Fin 4 → ℝ := Ainv.mulVec res
  c0 k - w k * ∑ i : Fin 4, lam i * u i k

/-- Weighted `4 × 4` constraint Gram matrix `A_{i,j} = ∑_{k=1}^N u_{i,k} w_k u_{j,k}`. -/
noncomputable def weightedConstraintGram (w : ℕ → ℝ) (u : Fin 4 → ℕ → ℝ) (N : ℕ) :
    Matrix (Fin 4) (Fin 4) ℝ :=
  Matrix.of fun i j => ∑ k ∈ Finset.Icc 1 N, u i k * (w k * u j k)

/-- Exact Rank-4 distributed projection neutrality: whenever `A * Ainv = 1`, the projected
coefficient vector satisfies every constraint `∑_{k=1}^N u_{i,k} c_proj(k) = t_i`. -/
theorem distributedProj_satisfies_constraints (w : ℕ → ℝ) (u : Fin 4 → ℕ → ℝ) (c0 : ℕ → ℝ)
    (Ainv : Matrix (Fin 4) (Fin 4) ℝ) (t : Fin 4 → ℝ) (N : ℕ)
    (hInv : weightedConstraintGram w u N * Ainv = 1) (i : Fin 4) :
    ∑ k ∈ Finset.Icc 1 N, u i k * distributedProj w u c0 Ainv t N k = t i := by
  let res : Fin 4 → ℝ := fun a => (∑ m ∈ Finset.Icc 1 N, u a m * c0 m) - t a
  let lam : Fin 4 → ℝ := Ainv.mulVec res
  have hsplit :
      (∑ k ∈ Finset.Icc 1 N, u i k * (c0 k - w k * ∑ j : Fin 4, lam j * u j k)) =
        (∑ k ∈ Finset.Icc 1 N, u i k * c0 k) -
          ∑ j : Fin 4, (∑ k ∈ Finset.Icc 1 N, u i k * (w k * u j k)) * lam j := by
    have hmul : ∀ k ∈ Finset.Icc 1 N,
        u i k * (c0 k - w k * ∑ j : Fin 4, lam j * u j k) =
          u i k * c0 k - ∑ j : Fin 4, (u i k * (w k * u j k)) * lam j := by
      intro k _
      rw [mul_sub, Finset.mul_sum]
      congr 1
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      ring
    rw [Finset.sum_congr rfl hmul, Finset.sum_sub_distrib, Finset.sum_comm]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Finset.sum_mul]
  have hmat :
      (∑ j : Fin 4, (∑ k ∈ Finset.Icc 1 N, u i k * (w k * u j k)) * lam j) = res i := by
    have hvec : ((weightedConstraintGram w u N).mulVec lam) i = res i := by
      change ((weightedConstraintGram w u N).mulVec (Ainv.mulVec res)) i = res i
      rw [Matrix.mulVec_mulVec, hInv, Matrix.one_mulVec]
    simpa [weightedConstraintGram, Matrix.mulVec, dotProduct] using hvec
  change (∑ k ∈ Finset.Icc 1 N, u i k * (c0 k - w k * ∑ j : Fin 4, lam j * u j k)) = t i
  rw [hsplit, hmat]
  dsimp [res]
  ring

/-- Clay Rank-4 functional row basis `(1, -ln k, 1/k, -(ln k)/k)` matching `(D0, D0', D1, D1')`. -/
noncomputable def clayRowBasis : Fin 4 → ℕ → ℝ
  | 0, _ => 1
  | 1, k => -Real.log (k : ℝ)
  | 2, k => 1 / (k : ℝ)
  | 3, k => -(Real.log (k : ℝ)) / (k : ℝ)

/-- Clay boundary target vector `t_Clay = (2, -2 ln(2π), 0, -1)`. -/
noncomputable def clayTarget : Fin 4 → ℝ
  | 0 => 2
  | 1 => -2 * Real.log (2 * Real.pi)
  | 2 => 0
  | 3 => -1

/-- Instantiation: any distributed Rank-4 projection using `(clayRowBasis, clayTarget)` with
`A * Ainv = 1` satisfies `SatisfiesClayBoundaryConditions` identically. -/
theorem distributedProj_satisfies_clayBoundary (w : ℕ → ℝ) (c0 : ℕ → ℝ)
    (Ainv : Matrix (Fin 4) (Fin 4) ℝ) (N : ℕ)
    (hInv : weightedConstraintGram w clayRowBasis N * Ainv = 1) :
    RiemannBlueprint.Section8_VasyuninBDR.SatisfiesClayBoundaryConditions
      (distributedProj w clayRowBasis c0 Ainv clayTarget N) N := by
  have h0 := distributedProj_satisfies_constraints w clayRowBasis c0 Ainv clayTarget N hInv 0
  have h1 := distributedProj_satisfies_constraints w clayRowBasis c0 Ainv clayTarget N hInv 1
  have h2 := distributedProj_satisfies_constraints w clayRowBasis c0 Ainv clayTarget N hInv 2
  have h3 := distributedProj_satisfies_constraints w clayRowBasis c0 Ainv clayTarget N hInv 3
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold RiemannBlueprint.Section8_VasyuninBDR.D0
    simpa [clayRowBasis, clayTarget, mul_comm] using h0
  · unfold RiemannBlueprint.Section8_VasyuninBDR.D0_deriv
    refine Eq.trans ?_ (by simpa [clayTarget] using h1)
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp [clayRowBasis]
    ring
  · unfold RiemannBlueprint.Section8_VasyuninBDR.D1
    refine Eq.trans ?_ (by simpa [clayTarget] using h2)
    refine Finset.sum_congr rfl fun k _ => ?_
    simp [clayRowBasis]
    ring
  · unfold RiemannBlueprint.Section8_VasyuninBDR.D1_deriv
    refine Eq.trans ?_ (by simpa [clayTarget] using h3)
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp [clayRowBasis]
    ring

/-- Pointwise algebraic Rouché non-vanishing lemma: if `‖1 + z * d‖ < 1`, neither `z` nor
`d` can equal `0`. -/
theorem ne_zero_of_norm_one_add_mul_lt_one (z d : ℂ) (h : ‖1 + z * d‖ < 1) :
    z ≠ 0 ∧ d ≠ 0 := by
  constructor
  · intro hz
    rw [hz, zero_mul, add_zero, norm_one] at h
    exact lt_irrefl 1 h
  · intro hd
    rw [hd, mul_zero, add_zero, norm_one] at h
    exact lt_irrefl 1 h

/-- Unconditional pointwise non-vanishing for `stripDefect`:
`‖E_c(s)‖ < 1 → ζ(s) ≠ 0 ∧ D_c(s) ≠ 0`. -/
theorem stripDefect_norm_lt_one_implies_ne_zero (N : ℕ) (c : ℕ → ℂ) (s : ℂ)
    (h : ‖stripDefect N c s‖ < 1) :
    riemannZeta s ≠ 0 ∧ dirichletPoly N c s ≠ 0 :=
  ne_zero_of_norm_one_add_mul_lt_one (riemannZeta s) (dirichletPoly N c s) h

/-- Exact reciprocal-zeta approximation error equation: when `ζ(s) ≠ 0`,
`D_c(s) - (-1 / ζ(s)) = stripDefect N c s / ζ(s)`. -/
theorem inv_zeta_approx_error_eq (N : ℕ) (c : ℕ → ℂ) (s : ℂ) (hz : riemannZeta s ≠ 0) :
    dirichletPoly N c s - (-1 / riemannZeta s) = stripDefect N c s / riemannZeta s := by
  unfold stripDefect
  field_simp [hz]
  ring

/-- **Theorem 1(2) (Critical-Line Penetration Lower Bound, Unconditional):**
At any point `s` where `‖1 + ζ(s) D_c(s)‖ < 1`, we have `ζ(s) ≠ 0` and
`(1 - ‖1 + ζ(s) D_c(s)‖) / ‖ζ(s)‖ ≤ ‖D_c(s)‖`. In particular, approaching any critical-line
zero `ρ = 1/2 + iγ` along `s_δ = ρ + δ` (`δ → 0⁺`) forces `‖D_c(s_δ)‖ ≥ (1 - ‖E_c‖)/‖ζ‖`. -/
theorem critical_line_penetration_lower_bound (N : ℕ) (c : ℕ → ℂ) (s : ℂ)
    (h : ‖stripDefect N c s‖ < 1) :
    (1 - ‖stripDefect N c s‖) / ‖riemannZeta s‖ ≤ ‖dirichletPoly N c s‖ := by
  have hz : riemannZeta s ≠ 0 := (stripDefect_norm_lt_one_implies_ne_zero N c s h).1
  have hz_pos : 0 < ‖riemannZeta s‖ := norm_pos_iff.mpr hz
  have htri : 1 ≤ ‖stripDefect N c s‖ + ‖riemannZeta s‖ * ‖dirichletPoly N c s‖ := by
    calc
      (1 : ℝ) = ‖(1 : ℂ)‖ := norm_one.symm
      _ = ‖stripDefect N c s - riemannZeta s * dirichletPoly N c s‖ := by
          unfold stripDefect
          ring_nf
      _ ≤ ‖stripDefect N c s‖ + ‖riemannZeta s * dirichletPoly N c s‖ := norm_sub_le _ _
      _ = ‖stripDefect N c s‖ + ‖riemannZeta s‖ * ‖dirichletPoly N c s‖ := by rw [norm_mul]
  rw [div_le_iff₀ hz_pos]
  linarith

/-- Compact rectangle `R(β, σ_max, t₀, t₁) ⊂ (1/2, ∞) × (0, ∞)` strictly inside the
pole-free analytic right critical strip. -/
structure CompactStripRect where
  β : ℝ
  σ_max : ℝ
  t₀ : ℝ
  t₁ : ℝ
  half_lt_β : (1 / 2 : ℝ) < β
  β_le_σ_max : β ≤ σ_max
  zero_lt_t₀ : 0 < t₀
  t₀_le_t₁ : t₀ ≤ t₁

namespace CompactStripRect

/-- Membership predicate `s ∈ [β, σ_max] × [t₀, t₁]`. -/
def mem (R : CompactStripRect) (s : ℂ) : Prop :=
  R.β ≤ s.re ∧ s.re ≤ R.σ_max ∧ R.t₀ ≤ s.im ∧ s.im ≤ R.t₁

/-- Topological boundary `∂R` of the compact strip rectangle `R`. -/
def boundary (R : CompactStripRect) (s : ℂ) : Prop :=
  R.mem s ∧ (s.re = R.β ∨ s.re = R.σ_max ∨ s.im = R.t₀ ∨ s.im = R.t₁)

/-- Every point of `R` satisfies `s ≠ 1` (since `Im(s) ≥ t₀ > 0`). -/
lemma ne_one_of_mem (R : CompactStripRect) {s : ℂ} (hs : R.mem s) : s ≠ 1 := by
  intro h1
  have him : s.im = 0 := by simp [h1]
  linarith [R.zero_lt_t₀, hs.2.2.1]

/-- Every point of `R` satisfies `1/2 < Re(s)`. -/
lemma half_lt_re_of_mem (R : CompactStripRect) {s : ℂ} (hs : R.mem s) : (1 / 2 : ℝ) < s.re :=
  lt_of_lt_of_le R.half_lt_β hs.1

end CompactStripRect

/-- Classical holomorphic rectangle Rouché principle (passed explicitly as a hypothesis,
never declared as an `axiom`): if `g` is analytic on `{1}ᶜ` and satisfies `‖1 + g(s)‖ < 1` on
every boundary point `s ∈ ∂R` (so `‖1 - (-g(s))‖ < 1`, comparing `-g` with constant `1` on `∂R`),
then `g(s) ≠ 0` throughout the entire closed rectangle `R`. -/
def RectRoucheProperty : Prop :=
  ∀ (R : CompactStripRect) (g : ℂ → ℂ),
    AnalyticOnNhd ℂ g {1}ᶜ →
    (∀ s : ℂ, R.boundary s → ‖1 + g s‖ < 1) →
    ∀ s : ℂ, R.mem s → g s ≠ 0

/-- **Theorem 1(1) (Rank-4 Rouché Zero-Exclusion on Compact Strip Rectangles):**
Under `h_rouche : RectRoucheProperty`, if a Dirichlet polynomial `D_c(s)` satisfies
`‖1 + ζ(s) D_c(s)‖ < 1` on every point of `∂R`, then neither `ζ(s)` nor `D_c(s)` has any zero
anywhere inside `R`. -/
theorem theorem1_rouche_zero_exclusion (h_rouche : RectRoucheProperty)
    (R : CompactStripRect) (N : ℕ) (c : ℕ → ℂ)
    (h_bdry : ∀ s : ℂ, R.boundary s → ‖stripDefect N c s‖ < 1) :
    ∀ s : ℂ, R.mem s → riemannZeta s ≠ 0 ∧ dirichletPoly N c s ≠ 0 := by
  have hprod : ∀ s : ℂ, R.mem s → riemannZeta s * dirichletPoly N c s ≠ 0 :=
    h_rouche R (fun s => riemannZeta s * dirichletPoly N c s)
      (analyticOnNhd_zeta_mul_dirichletPoly N c) h_bdry
  intro s hs
  exact mul_ne_zero_iff.mp (hprod s hs)

/-- **Theorem 2 (⇐) (Rank-4 Boundary-Exhaustion Implies RH, `NO_RH_PROOF = TRUE`):**
Assuming `RectRoucheProperty`, if every compact strip rectangle `R ⊂ (1/2, ∞) × (0, ∞)` admits
a Rank-4 boundary-compliant horizon `(N, c)` satisfying `SatisfiesClayBoundaryConditions c N` and
`‖1 + ζ(s) D_c(s)‖ < 1` on `∂R`, then `_root_.RiemannHypothesis` holds unconditionally. -/
theorem theorem2_rouche_exhaustion_implies_rh (h_rouche : RectRoucheProperty)
    (h_exhaust : ∀ R : CompactStripRect,
      ∃ (N : ℕ) (c : ℕ → ℝ),
        4 ≤ N ∧
        RiemannBlueprint.Section8_VasyuninBDR.SatisfiesClayBoundaryConditions c N ∧
        ∀ s : ℂ, R.boundary s → ‖stripDefect N (fun k => (c k : ℂ)) s‖ < 1) :
    _root_.RiemannHypothesis := by
  refine CMIAudit.riemannHypothesis_of_strip ?_
  intro s hs hzero
  by_contra h_not_half
  have h_gt_ex : ∃ s₁ : ℂ, CMIAudit.InCriticalStrip s₁ ∧
      (1 / 2 : ℝ) < s₁.re ∧ 0 < s₁.im ∧ riemannZeta s₁ = 0 := by
    have h_gt_half_raw : ∃ w : ℂ, CMIAudit.InCriticalStrip w ∧
        (1 / 2 : ℝ) < w.re ∧ riemannZeta w = 0 := by
      rcases lt_or_gt_of_ne h_not_half with hlt | hgt
      · refine ⟨1 - s, CMIAudit.inCriticalStrip_one_sub hs, ?_,
          CMIAudit.riemannZeta_one_sub_eq_zero_of_inCriticalStrip hs hzero⟩
        rw [Complex.sub_re, Complex.one_re]
        linarith
      · exact ⟨s, hs, hgt, hzero⟩
    rcases h_gt_half_raw with ⟨w, hw_strip, hw_re, hw_zero⟩
    have hw_im_ne : w.im ≠ 0 :=
      CMIAudit.im_ne_zero_of_inCriticalStrip_zeta_zero w hw_strip hw_zero
    have hw_ne_one : w ≠ 1 := CMIAudit.inCriticalStrip_ne_one hw_strip
    rcases lt_or_gt_of_ne hw_im_ne with hneg | hpos
    · refine ⟨starRingEnd ℂ w, ?_, ?_, ?_, ?_⟩
      · simpa [CMIAudit.InCriticalStrip] using hw_strip
      · simpa using hw_re
      · simpa using neg_pos.mpr hneg
      · rw [CMIAudit.riemannZeta_conj_of_pos_re w hw_strip.1 hw_ne_one, hw_zero, map_zero]
    · exact ⟨w, hw_strip, hw_re, hpos, hw_zero⟩
  rcases h_gt_ex with ⟨s₁, hs₁_strip, hs₁_half, hs₁_im, hs₁_zero⟩
  let R : CompactStripRect :=
    { β := s₁.re
      σ_max := 2
      t₀ := s₁.im
      t₁ := s₁.im + 1
      half_lt_β := hs₁_half
      β_le_σ_max := by linarith [hs₁_strip.2]
      zero_lt_t₀ := hs₁_im
      t₀_le_t₁ := by linarith }
  have hs₁_mem : R.mem s₁ := by
    refine ⟨le_rfl, ?_, le_rfl, ?_⟩
    · linarith [hs₁_strip.2]
    · linarith
  rcases h_exhaust R with ⟨N, c, _, _, hbdry⟩
  have hne : riemannZeta s₁ ≠ 0 :=
    (theorem1_rouche_zero_exclusion h_rouche R N (fun k => (c k : ℂ)) hbdry s₁ hs₁_mem).1
  exact hne hs₁_zero

#print axioms dirichletPoly
#print axioms stripDefect
#print axioms stripDefect_eq_mul_mellin_residual
#print axioms differentiable_dirichletPoly
#print axioms analyticOnNhd_dirichletPoly
#print axioms analyticOnNhd_zeta_mul_dirichletPoly
#print axioms hasDerivAt_logHermitePsi
#print axioms deriv_logHermitePsi_zero
#print axioms deriv_logHermitePsi_one
#print axioms distributedProj_satisfies_constraints
#print axioms distributedProj_satisfies_clayBoundary
#print axioms ne_zero_of_norm_one_add_mul_lt_one
#print axioms stripDefect_norm_lt_one_implies_ne_zero
#print axioms inv_zeta_approx_error_eq
#print axioms critical_line_penetration_lower_bound
#print axioms theorem1_rouche_zero_exclusion
#print axioms theorem2_rouche_exhaustion_implies_rh

end RiemannBlueprint.OpenStripRouche
