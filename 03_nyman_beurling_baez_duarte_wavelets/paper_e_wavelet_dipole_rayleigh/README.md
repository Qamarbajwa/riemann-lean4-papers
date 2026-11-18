<!-- Zenodo DOI: 10.5281/zenodo.24353578 -->
# Paper E: Constructive Candidate Sequences and Cotangent Gram Matrix Benchmarks on the Baez-Duarte Affine Manifold in Lean 4

- **Zenodo DOI:** [`10.5281/zenodo.24353578`](https://doi.org/10.5281/zenodo.24353578) (prev `10.5281/zenodo.24328047`)
- **MSC 2020:** Primary 11M26; Secondary 46E20, 68V20

# Submission Package: Constructive Candidate Sequences and Cotangent Gram Benchmarks on $\mathcal{A}_N$

## Title
**Constructive Candidate Sequences and Cotangent Gram Matrix Benchmarks on the Báez-Duarte Affine Manifold in Lean 4**

## Author
- **Qamar Munawer**, Brandenburg University of Technology Cottbus–Senftenberg

## Overview
This package contains the complete LaTeX source, compiled 6-page manuscript, and kernel-verified Lean 4 formalization (`MathlibPR_ForwardCandidate.lean`, 796 lines) for constructive candidate vectors $c^{(N)} \in \mathcal{A}_N = \{c \in \mathbb{R}^N : D_1(c, N) = 0 \land D_0(c, N) = 2\}$ alongside $80$-decimal-digit multi-family numerical benchmarks (`../explore_forward_weights.py`, `mp.dps = 80`, $N \in \{4, 8, 16, 32, 64, 128, 256\}$):
1. **Unconditional Projection Positivity:** `DeltaDet_double_sum_eq`, `DeltaDet_pos`, `DeltaDet_ne_zero`, and `projectAffine_mem_A_N_uncond` ($N \ge 2$).
2. **Candidate Families & Unconditional Distance Bridge:** `mollifiedMobius` / `cCandidateMobius`, `selbergSieveWeights` / `cCandidateSelberg`, and `clayGalerkinCandidate` (`clayGalerkinCandidate_mem_A_N` for $N \ge 4$), with unconditional reductions `projectAffine_l2_dist_eq_one_sub_scot`, `clayGalerkinCandidate_l2_dist_eq_one_sub_scot`, `riemannHypothesis_of_cCandidateMobius_limit`, `riemannHypothesis_of_cCandidateSelberg_limit`, and `riemannHypothesis_of_clayGalerkin_limit`.
3. **Exact Closed-Form $N = 4$ Lean 4 Certificate:** `HSum_four`, `S2Sum_four`, `DeltaDet_four`, `mollifiedMobius_four_eval`, `cCandidateMobius_four_eval`, `SCot_cCandidateMobius_four_eq` $\big((\frac{119}{576} + \frac{54467}{389376\sqrt{3}})\pi\big)$, `cCandidateMobius_four_l2_dist_eq`, and `cCandidateMobius_four_l2_dist_pos`.
4. **80-Digit Benchmarks & Obstruction Analysis:** Summarizes `explore_forward_weights.py` results ($E_{\mathrm{opt}}(256) = 0.00824337$, $R^2_{\log} = 0.99976$ on $[16, 256]$) and isolates the Gram condition-number / $\ell^2$-norm growth obstruction ($\kappa(G_{64}) = 11{,}555.80$) and rank-4 Clay boundary amplification ($\det(U_4)^{-1} \approx 664.38\times$).

## Mathematical Scope and Verification Invariants
- **MSC 2020:** Primary `11M26`; Secondary `46E20`, `68V20`. Establishes the unconditional finite-horizon affine geometry for $N \ge 2$, while asymptotic $L^2(0,1)$ closure depends on twisted fourth-moment cancellation as $N \to \infty$.
- **Foundational Axioms:** Strictly `[propext, Classical.choice, Quot.sound]` with zero `sorry`, zero `admit`, and zero custom axioms.

## Package File Manifest
- `paper_e_forward_candidates.tex`: LaTeX source (synchronized bit-for-bit with root `paper_e_forward_candidates.tex`).
- `paper_e_forward_candidates.pdf`: Compiled PDF (6 pages, 0 LaTeX errors, 0 Overfull hboxes > 10 pt).
- `MathlibPR_ForwardCandidate.lean`: Constructive candidate formalization and exact $N=4$ certificate (796 lines, synced bit-for-bit with `RiemannBlueprint/RiemannBlueprint/MathlibPR_ForwardCandidate.lean`).

## Verification Instructions
Run from the `RiemannBlueprint` Lean project root:
```bash
lake env lean RiemannBlueprint/MathlibPR_ForwardCandidate.lean
```
And execute the 80-digit benchmark from the repository root:
```bash
python explore_forward_weights.py
```
