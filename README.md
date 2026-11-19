# Riemann-Lean4-Papers: Standalone Companion Notes & Numerical Diagnostics

**Author:** Qamar Munawer (Brandenburg University of Technology Cottbus–Senftenberg)  
**MSC 2020:** Primary `11M26`; Secondary `46E20`, `68V20`

## Project Status & AI Disclosure

1. **AI-Assisted Exploration:** This repository accompanies a standalone, AI-assisted Lean 4 formalization exploration developed by the author using LLM proof assistants.
2. **Closed Mathlib Pull Requests (Nov 2026):** Between 16 and 18 November 2026, 15 pull requests derived from this project were opened against `leanprover-community/mathlib4`, labelled `LLM-generated`, and closed by Mathlib triage without merging because they did not meet Mathlib's community standards for human-authored learning and AI use.
3. **Decommissioned Automation & Frozen Archives:** All PR staging directories (`05_mathlib4_pr_staging/`), automated PR push scripts, and `Qamarbajwa/mathlib4` `feat/*` fork branches have been permanently removed, Zenodo publishing is frozen, and no further pull requests will be submitted to Mathlib without prior human mentorship and manual authorship.

## Repository Structure

### Part I — Classical Analytic Number Theory Formalizations (in `Qamarbajwa/RiemannBlueprint`)

- **Littlewood's (1912) Forward Theorem:** `LittlewoodForward.lean` (`MertensBound →` right inverse of $\zeta(s)$ on $\operatorname{Re}(s) > 1/2$). Companion note: [`paper_a_littlewood_tauberian`](./02_classical_theorems_lean4/paper_a_littlewood_tauberian/).
- **Hardy's (1914) Critical-Line Zeros Theorem:** `infinite_criticalLine_zeros` in `MathlibPR_HardyZeros.lean` and `Modules/HardyCriticalLineZeros.lean`. Companion note: [`paper_d_hardy_critical_line_zeros`](./02_classical_theorems_lean4/paper_d_hardy_critical_line_zeros/).
- **De la Vallée Poussin (1899) Zero-Free Region:** `deLaValleePoussin_zero_free_region_unconditional` ($\sigma > 1 - c / \ln^9(|t| + 2)$ for $|t| \ge 2$) in `MathlibPR_ZeroFreeRegion.lean` and `Modules/ZetaZeroFreeRegion.lean`. Companion note: [`paper_c_zero_free_region`](./02_classical_theorems_lean4/paper_c_zero_free_region/).
  - **Prior-Art Credit:** `AlexKontorovich/PrimeNumberTheoremAnd` (`PrimeNumberTheoremAnd/ZetaBounds.lean`, `ZetaZeroFree9`) already formalized the $\log^9 |t|$ zero-free region via the 3-4-1 inequality and $\log^2 |t|$ derivative bounds; `mathlib4` already provides `riemannZeta_ne_zero_of_one_le_re` and `norm_LFunction_product_ge_one`.

### Part II — Finite-$N$ Báez-Duarte / Vasyunin Cotangent Calculations and Conditional Reductions

- **Identity-Matrix Linear Algebra & Numerical Diagnostics:** Gaussian elimination of $\mathbf{D}_M$ ($\mathbf{D}_M \mathbf{D}_M^{-1} = \mathbf{I}_M$, $\mathbf{D}_M \mu = e_1$), unit lower-triangular factorization $\mathbf{F}_M = \mathbf{\Sigma}_M \mathbf{D}_M$ ($\mathbf{F}_M \mathbf{F}_M^{-1} = \mathbf{I}_M$), nullspace basis $T_{N,N-2}$, Cholesky whitening to $\mathbf{I}_{N-2}$, wavefunction Gram operator $M_N = \mathbf{\Omega}_N^T \mathbf{\Omega}_N$, and projection residual $\langle b | (\mathbf{I} - \widehat{\Pi}_N) | b \rangle = 1 - \sum_{k=3}^N \rho_k^2 / s_k$ ([`MATRIX_RELATIONS_AND_HALF_OBSERVATION.md`](./MATRIX_RELATIONS_AND_HALF_OBSERVATION.md), [`verify_matrix_half_observation.py`](./verify_matrix_half_observation.py)).
- **Finite-Dimensional Algebraic Computations & Known Cotangent Symmetries:** Exact evaluations on $N = 3, 4, 5, 6$ (`03_nyman_beurling_baez_duarte_wavelets/`), palindromic period checks, and `mpmath` / `flint.arb` numerical conditioning diagnostics (`04_spectral_diagnostics_and_audits/`).
- **Conditional Reductions:** All Nyman–Beurling / Baez–Duarte / spectral-gap equivalences parameterize their unproven analytic hypotheses explicitly; the $N \to \infty$ convergence $\widehat{\Pi}_N |b\rangle \to |b\rangle$ carries the full analytic difficulty of the open Riemann Hypothesis.

## Companion Subdirectories (Historical Frozen Zenodo Archive DOIs)

- [`00_unified_master_review_paper_l`](./00_unified_master_review_paper_l/) — Consolidated LaTeX source, bibliography, and numerical verification scripts (`verify_n_to_continuity_chain.py`, `verify_matrix_half_observation.py`, `layer_d_palindromic_period_lab.py`) — Frozen Hub 14 DOI: [`10.5281/zenodo.24357280`](https://doi.org/10.5281/zenodo.24357280) (prev `10.5281/zenodo.24354470`, `10.5281/zenodo.24353183`, `10.5281/zenodo.24341718`)
- [`01_geometric_intuition`](./01_geometric_intuition/) — [`paper_0_joined_cone_visualizations`](./01_geometric_intuition/paper_0_joined_cone_visualizations/) (`10.5281/zenodo.24354440`, prev `10.5281/zenodo.24328033`)
- [`02_classical_theorems_lean4`](./02_classical_theorems_lean4/) — `paper_a_littlewood_tauberian` (`10.5281/zenodo.24353571`, prev `10.5281/zenodo.24328035`), `paper_c_zero_free_region` (`10.5281/zenodo.24353574`, prev `10.5281/zenodo.24328039`), `paper_d_hardy_critical_line_zeros` (`10.5281/zenodo.24353575`, prev `10.5281/zenodo.24328045`), `paper_g_von_koch_spectral_closure` (`10.5281/zenodo.24353580`, prev `10.5281/zenodo.24328921`)
- [`03_nyman_beurling_baez_duarte_wavelets`](./03_nyman_beurling_baez_duarte_wavelets/) — `paper_b_titchmarsh_vasyunin_criterion` (`10.5281/zenodo.24353573`, prev `10.5281/zenodo.24328037`), `paper_e_wavelet_dipole_rayleigh` (`10.5281/zenodo.24353578`, prev `10.5281/zenodo.24328047`), `paper_f_mellin_converse_and_rouche` (`10.5281/zenodo.24353579`, prev `10.5281/zenodo.24328918`), `paper_j_pure_plaque_asymptotic_frontier` (`10.5281/zenodo.24354446`), `paper_k_dirichlet_anchored_plaque` (`10.5281/zenodo.24354448`, prev `10.5281/zenodo.24339838`)
- [`04_spectral_diagnostics_and_audits`](./04_spectral_diagnostics_and_audits/) — `paper_h_gram_indefiniteness_arb512` (`10.5281/zenodo.24353581`, prev `10.5281/zenodo.24328927`), `paper_i_prime_composite_partition` (`10.5281/zenodo.24354445`, prev `10.5281/zenodo.24328929`)
- **Historical Frozen Software Archive (Hub 07):** [`10.5281/zenodo.24357255`](https://doi.org/10.5281/zenodo.24357255) (Concept DOI [`10.5281/zenodo.24150107`](https://doi.org/10.5281/zenodo.24150107))
- **Historical Frozen Paper M:** [`10.5281/zenodo.24357107`](https://doi.org/10.5281/zenodo.24357107) (Concept DOI [`10.5281/zenodo.24357106`](https://doi.org/10.5281/zenodo.24357106))
- **Prior-Art Audit & Study Guide:** [`PRIOR_ART_AND_VERIFICATION_AUDIT.md`](./PRIOR_ART_AND_VERIFICATION_AUDIT.md) · [`STUDY_GUIDE_LITTLEWOOD_FORWARD_LINE_BY_LINE.md`](./STUDY_GUIDE_LITTLEWOOD_FORWARD_LINE_BY_LINE.md)
- **Lean 4 Repository:** https://github.com/Qamarbajwa/RiemannBlueprint
- **Citation Metadata:** [`CITATION.cff`](./CITATION.cff)
