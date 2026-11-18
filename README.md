# Riemann-Lean4-Papers: Thematic Companion Suite & Mathlib4 PRs

**Author:** Qamar Munawer (Brandenburg University of Technology Cottbus–Senftenberg)  
**Epistemic Invariant:** `NO_RH_PROOF = TRUE` — All Lean 4 formalizations verify classical conditional equivalences, unconditional zero-free regions, critical-line zero theorems, exact constructive/variational identities on the Báez–Duarte manifold, and rigorous numerical obstruction audits. **No unconditional proof of the Riemann Hypothesis is claimed.**

## Thematic Sub-Sections & Live Zenodo DOIs (14 Live Hubs / 12 PDFs: Paper 0, Papers A–L)

0. **[`00_unified_master_review_paper_l`](./00_unified_master_review_paper_l/)**
   - Unified Arithmetic & Lean 4 Master Review (`Paper L`, 54 modules + BBLR 85-digit / 512-bit diagnostics) — Zenodo Hub 14 DOI: [`10.5281/zenodo.24343534`](https://doi.org/10.5281/zenodo.24343534) *(earlier: `10.5281/zenodo.24342950`, `10.5281/zenodo.24342626`, `10.5281/zenodo.24342101`, `10.5281/zenodo.24341718`, `10.5281/zenodo.24341498`)*
1. **[`01_geometric_intuition`](./01_geometric_intuition/)**
   - [`paper_0_joined_cone_visualizations`](./01_geometric_intuition/paper_0_joined_cone_visualizations/) — Zenodo DOI: [`10.5281/zenodo.24328033`](https://doi.org/10.5281/zenodo.24328033)
2. **[`02_classical_theorems_lean4`](./02_classical_theorems_lean4/)**
   - [`paper_a_littlewood_tauberian`](./02_classical_theorems_lean4/paper_a_littlewood_tauberian/) — Zenodo DOI: [`10.5281/zenodo.24328035`](https://doi.org/10.5281/zenodo.24328035)
   - [`paper_c_zero_free_region`](./02_classical_theorems_lean4/paper_c_zero_free_region/) — Zenodo DOI: [`10.5281/zenodo.24328039`](https://doi.org/10.5281/zenodo.24328039)
   - [`paper_d_hardy_critical_line_zeros`](./02_classical_theorems_lean4/paper_d_hardy_critical_line_zeros/) — Zenodo DOI: [`10.5281/zenodo.24328045`](https://doi.org/10.5281/zenodo.24328045)
   - [`paper_g_von_koch_spectral_closure`](./02_classical_theorems_lean4/paper_g_von_koch_spectral_closure/) — Zenodo DOI: [`10.5281/zenodo.24328921`](https://doi.org/10.5281/zenodo.24328921)
3. **[`03_nyman_beurling_baez_duarte_wavelets`](./03_nyman_beurling_baez_duarte_wavelets/)**
   - [`paper_b_titchmarsh_vasyunin_criterion`](./03_nyman_beurling_baez_duarte_wavelets/paper_b_titchmarsh_vasyunin_criterion/) — Zenodo DOI: [`10.5281/zenodo.24328037`](https://doi.org/10.5281/zenodo.24328037)
   - [`paper_e_wavelet_dipole_rayleigh`](./03_nyman_beurling_baez_duarte_wavelets/paper_e_wavelet_dipole_rayleigh/) — Zenodo DOI: [`10.5281/zenodo.24328047`](https://doi.org/10.5281/zenodo.24328047)
   - [`paper_f_mellin_converse_and_rouche`](./03_nyman_beurling_baez_duarte_wavelets/paper_f_mellin_converse_and_rouche/) — Zenodo DOI: [`10.5281/zenodo.24328918`](https://doi.org/10.5281/zenodo.24328918)
   - [`paper_j_pure_plaque_asymptotic_frontier`](./03_nyman_beurling_baez_duarte_wavelets/paper_j_pure_plaque_asymptotic_frontier/) — Zenodo DOI: [`10.5281/zenodo.24330500`](https://doi.org/10.5281/zenodo.24330500)
   - [`paper_k_dirichlet_anchored_plaque`](./03_nyman_beurling_baez_duarte_wavelets/paper_k_dirichlet_anchored_plaque/) — Zenodo DOI: [`10.5281/zenodo.24343525`](https://doi.org/10.5281/zenodo.24343525) *(earlier: `10.5281/zenodo.24342906`, `10.5281/zenodo.24342619`, `10.5281/zenodo.24342096`, `10.5281/zenodo.24341228`, `10.5281/zenodo.24341007`, `10.5281/zenodo.24339838`)*
4. **[`04_spectral_diagnostics_and_audits`](./04_spectral_diagnostics_and_audits/)**
   - [`paper_h_gram_indefiniteness_arb512`](./04_spectral_diagnostics_and_audits/paper_h_gram_indefiniteness_arb512/) — Zenodo DOI: [`10.5281/zenodo.24328927`](https://doi.org/10.5281/zenodo.24328927)
   - [`paper_i_prime_composite_partition`](./04_spectral_diagnostics_and_audits/paper_i_prime_composite_partition/) — Zenodo DOI: [`10.5281/zenodo.24328929`](https://doi.org/10.5281/zenodo.24328929)
5. **[`05_mathlib4_pr_staging`](./05_mathlib4_pr_staging/)**
   - 54 self-contained, linter-verified modular Lean 4 formalization units (`UpstreamPR_1A`–`8K`, Waves 1–8), [`PR_SUBMISSION_GUIDE.md`](./05_mathlib4_pr_staging/PR_SUBMISSION_GUIDE.md), and [`push_carved_prs_to_mathlib4.py`](./05_mathlib4_pr_staging/push_carved_prs_to_mathlib4.py)
   - **Master Lean 4 Hub 07 DOI:** [`10.5281/zenodo.24329861`](https://doi.org/10.5281/zenodo.24329861) (Concept DOI [`10.5281/zenodo.24150107`](https://doi.org/10.5281/zenodo.24150107))
   - **Lean 4 Repository:** https://github.com/Qamarbajwa/RiemannBlueprint
   - **Citation Metadata:** [`CITATION.cff`](./CITATION.cff)

## Standalone Repository & Archived Wave 1 Reference Policy
All 54 modular Lean 4 units (`UpstreamPR_1A`–`8K`) are maintained as standalone verifiable artifacts on `Qamarbajwa/RiemannBlueprint`, `Qamarbajwa/mathlib4` (54 fork branches), and Zenodo, with automated upstream `leanprover-community/mathlib4` actions disabled (`ALLOW_UPSTREAM_BOT_ACTIONS = False`). Earlier Wave 1 fork-branch references:
- **PR-1A** (`feat/critical-line-zeros`): [#46127](https://github.com/leanprover-community/mathlib4/pull/46127)
- **PR-3A** (`feat/vasyunin-integral`): [#46128](https://github.com/leanprover-community/mathlib4/pull/46128)
- **PR-4A** (`feat/baez-duarte-projection`): [#46129](https://github.com/leanprover-community/mathlib4/pull/46129)
