# Reviewer Cover Letter & Independent Verification Guide — Paper L (`NO_RH_PROOF = TRUE`)

**Manuscript Title:** *Unconditional Arithmetic Reductions, Exact Cotangent Reciprocity, and Lean 4 Formal Verification for the Classical and Nyman–Beurling Theory of the Riemann Zeta Function*  
**Author:** Qamar Munawer (`Brandenburg University of Technology Cottbus–Senftenberg`)  
**Epistemic Invariant:** `NO_RH_PROOF = TRUE` (no unconditional proof of the Riemann Hypothesis is claimed)  
**Repositories:**  
- Lean 4 Codebase: https://github.com/Qamarbajwa/RiemannBlueprint  
- Companion Papers & Benchmarks: https://github.com/Qamarbajwa/riemann-lean4-papers  
- Fork Branch Archive (`55/55` branches): https://github.com/Qamarbajwa/mathlib4 (`ALLOW_UPSTREAM_BOT_ACTIONS = False`)

---

## 1. Summary for Referees
This dossier pairs the unified master review (`paper_l_unified_arithmetic_lean4_master_review.pdf`) with all arithmetic Wave 4–8 Lean 4.35 verification units (`UpstreamPR_4G`–`4M`, `7A`–`7D`, `8A`–`8L`), 85-digit `mpmath` benchmarks (including BBLR $(\ln N) E^{(N)}$ scaling and explicit analytical simplex test families), and cryptographic checksums (`SHA256SUMS.txt`). Every formal theorem compiles under `leanprover--lean4---v4.35.0` with `0` `sorry`s, `0` `#lint` errors across 15 linters, and strictly standard axioms `[propext, Classical.choice, Quot.sound]`.

## 2. One-Command Reproduction Protocol
```bash
# Build core library and latest Wave 8 module (PR-8L)
cd RiemannBlueprint && lake build RiemannBlueprint && lake build RiemannBlueprint.UpstreamPRs.UpstreamPR_8L_PlaqueRowTelescopingAndSimplex

# Run 85-digit mpmath benchmark laboratories
python layer_c_dirichlet_locked_plaque_lab.py
python layer_c_simplex_test_families_lab.py

# Run complete integrity audit suite
pytest test_monograph_audit.py -q
```

## 3. Complete 55-Module Lean 4 Ledger (Waves 1–8)
All 55 modules are located in `RiemannBlueprint/RiemannBlueprint/UpstreamPRs/` and mirrored in `MATHLIB4_PR_STAGING/`:

| ID | Wave | Module File | Lines | Axioms |
| :---: | :---: | :--- | :---: | :--- |
| `PR-1A` | 1 | `UpstreamPR_1A_CriticalLineZeros.lean` | 131 | `[propext, Classical.choice, Quot.sound]` |
| `PR-3A` | 1 | `UpstreamPR_3A_VasyuninIntegral.lean` | 250 | `[propext, Classical.choice, Quot.sound]` |
| `PR-4A` | 1 | `UpstreamPR_4A_AffineLagrangeProjection.lean` | 191 | `[propext, Classical.choice, Quot.sound]` |
| `PR-1B` | 2 | `UpstreamPR_1B_ZetaPoleAndRepulsion.lean` | 180 | `[propext, Classical.choice, Quot.sound]` |
| `PR-1C` | 2 | `UpstreamPR_1C_ZetaRemainderSeries.lean` | 166 | `[propext, Classical.choice, Quot.sound]` |
| `PR-1D` | 2 | `UpstreamPR_1D_ZetaPartialSummation.lean` | 174 | `[propext, Classical.choice, Quot.sound]` |
| `PR-1E` | 2 | `UpstreamPR_1E_ZetaLogStripBound.lean` | 213 | `[propext, Classical.choice, Quot.sound]` |
| `PR-1F` | 2 | `UpstreamPR_1F_ZetaZeroFreeRegion.lean` | 205 | `[propext, Classical.choice, Quot.sound]` |
| `PR-3B` | 3 | `UpstreamPR_3B_VasyuninSmoothAndCotDefs.lean` | 241 | `[propext, Classical.choice, Quot.sound]` |
| `PR-3C` | 3 | `UpstreamPR_3C_HarmonicCellAndAbelSum.lean` | 259 | `[propext, Classical.choice, Quot.sound]` |
| `PR-3D` | 3 | `UpstreamPR_3D_StirlingAndHarmonicAsymptotics.lean` | 209 | `[propext, Classical.choice, Quot.sound]` |
| `PR-3E` | 3 | `UpstreamPR_3E_CotangentMittagLefflerLimit.lean` | 221 | `[propext, Classical.choice, Quot.sound]` |
| `PR-3F` | 3 | `UpstreamPR_3F_VasyuninCrossIntegral.lean` | 193 | `[propext, Classical.choice, Quot.sound]` |
| `PR-3G` | 3 | `UpstreamPR_3G_MobiusCandidateFourCert.lean` | 188 | `[propext, Classical.choice, Quot.sound]` |
| `PR-3H` | 3 | `UpstreamPR_3H_VariationalOptimumFour.lean` | 199 | `[propext, Classical.choice, Quot.sound]` |
| `PR-4B` | 3 | `UpstreamPR_4B_AffineOrthogonalDecomp.lean` | 127 | `[propext, Classical.choice, Quot.sound]` |
| `PR-4C` | 3 | `UpstreamPR_4C_HarmonicWaveletBasis.lean` | 212 | `[propext, Classical.choice, Quot.sound]` |
| `PR-4D` | 3 | `UpstreamPR_4D_WaveletCotangentStencil.lean` | 203 | `[propext, Classical.choice, Quot.sound]` |
| `PR-4E` | 3 | `UpstreamPR_4E_TangentCotangentPositivity.lean` | 218 | `[propext, Classical.choice, Quot.sound]` |
| `PR-4F` | 3 | `UpstreamPR_4F_TangentRayleighQuotient.lean` | 231 | `[propext, Classical.choice, Quot.sound]` |
| `PR-4G` | 3 | `UpstreamPR_4G_GlobalOptimumFour.lean` | 215 | `[propext, Classical.choice, Quot.sound]` |
| `PR-4H` | 3 | `UpstreamPR_4H_WaveletRayleighRHCriterion.lean` | 164 | `[propext, Classical.choice, Quot.sound]` |
| `PR-4I` | 3 | `UpstreamPR_4I_CumulativeWaveletDipole.lean` | 248 | `[propext, Classical.choice, Quot.sound]` |
| `PR-4J` | 3 | `UpstreamPR_4J_FourPointDipoleKernel.lean` | 157 | `[propext, Classical.choice, Quot.sound]` |
| `PR-4K` | 3 | `UpstreamPR_4K_GeneralWaveletCompleteness.lean` | 245 | `[propext, Classical.choice, Quot.sound]` |
| `PR-4L` | 3 | `UpstreamPR_4L_DipoleQuadraticReduction.lean` | 199 | `[propext, Classical.choice, Quot.sound]` |
| `PR-4M` | 3 | `UpstreamPR_4M_DipoleDiagonalAndSymmetry.lean` | 82 | `[propext, Classical.choice, Quot.sound]` |
| `PR-2B` | 4 | `UpstreamPR_2B_HardyPsiAndThetaKernel.lean` | 259 | `[propext, Classical.choice, Quot.sound]` |
| `PR-2C` | 4 | `UpstreamPR_2C_HardyThetaIteratedDeriv.lean` | 260 | `[propext, Classical.choice, Quot.sound]` |
| `PR-2D` | 4 | `UpstreamPR_2D_CompletedZetaStripDecay.lean` | 259 | `[propext, Classical.choice, Quot.sound]` |
| `PR-2E` | 4 | `UpstreamPR_2E_HardyGContourAndMellin.lean` | 255 | `[propext, Classical.choice, Quot.sound]` |
| `PR-2F` | 4 | `UpstreamPR_2F_HardyEvenMomentIdentity.lean` | 229 | `[propext, Classical.choice, Quot.sound]` |
| `PR-2G` | 4 | `UpstreamPR_2G_HardyCriticalLineZeros.lean` | 229 | `[propext, Classical.choice, Quot.sound]` |
| `PR-5A` | 5 | `UpstreamPR_5A_ZetaLogDerivHolomorphy.lean` | 155 | `[propext, Classical.choice, Quot.sound]` |
| `PR-5B` | 5 | `UpstreamPR_5B_VonKochChebyshevPsi.lean` | 250 | `[propext, Classical.choice, Quot.sound]` |
| `PR-5C` | 5 | `UpstreamPR_5C_MellinNymanBeurlingIff.lean` | 250 | `[propext, Classical.choice, Quot.sound]` |
| `PR-6A` | 6 | `UpstreamPR_6A_CompletedZetaDerivSymmetry.lean` | 202 | `[propext, Classical.choice, Quot.sound]` |
| `PR-6B` | 6 | `UpstreamPR_6B_CriticalLinePenetrationBarrier.lean` | 250 | `[propext, Classical.choice, Quot.sound]` |
| `PR-6C` | 6 | `UpstreamPR_6C_PrimeCompositeDirichletSplit.lean` | 210 | `[propext, Classical.choice, Quot.sound]` |
| `PR-7A` | 7 | `UpstreamPR_7A_MellinKernelEnergyIdentity.lean` | 125 | `[propext, Classical.choice, Quot.sound]` |
| `PR-7B` | 7 | `UpstreamPR_7B_RectangleContourSubdivision.lean` | 107 | `[propext, Classical.choice, Quot.sound]` |
| `PR-7C` | 7 | `UpstreamPR_7C_PurePlaqueReduction.lean` | 162 | `[propext, Classical.choice, Quot.sound]` |
| `PR-7D` | 7 | `UpstreamPR_7D_DiagonalOffDiagonalFrontier.lean` | 97 | `[propext, Classical.choice, Quot.sound]` |
| `PR-8A` | 8 | `UpstreamPR_8A_PurePlaqueCauchySchwarz.lean` | 144 | `[propext, Classical.choice, Quot.sound]` |
| `PR-8B` | 8 | `UpstreamPR_8B_DirichletAnchoredPlaque.lean` | 147 | `[propext, Classical.choice, Quot.sound]` |
| `PR-8C` | 8 | `UpstreamPR_8C_PlaqueTwoDimTelescoping.lean` | 168 | `[propext, Classical.choice, Quot.sound]` |
| `PR-8D` | 8 | `UpstreamPR_8D_PurePlaqueRHCriterion.lean` | 239 | `[propext, Classical.choice, Quot.sound]` |
| `PR-8E` | 8 | `UpstreamPR_8E_DirichletOptFourCert.lean` | 162 | `[propext, Classical.choice, Quot.sound]` |
| `PR-8F` | 8 | `UpstreamPR_8F_DipoleGramFiveCert.lean` | 172 | `[propext, Classical.choice, Quot.sound]` |
| `PR-8G` | 8 | `UpstreamPR_8G_CotangentSixReciprocity.lean` | 209 | `[propext, Classical.choice, Quot.sound]` |
| `PR-8H` | 8 | `UpstreamPR_8H_UniversalCotangentSymmetries.lean` | 125 | `[propext, Classical.choice, Quot.sound]` |
| `PR-8I` | 8 | `UpstreamPR_8I_LogarithmicPlaqueDecayCriterion.lean` | 88 | `[propext, Classical.choice, Quot.sound]` |
| `PR-8J` | 8 | `UpstreamPR_8J_UnitPartitionHomogenization.lean` | 197 | `[propext, Classical.choice, Quot.sound]` |
| `PR-8K` | 8 | `UpstreamPR_8K_SuperdiagonalAndOrthogonalTriple.lean` | 188 | `[propext, Classical.choice, Quot.sound]` |
| `PR-8L` | 8 | `UpstreamPR_8L_PlaqueRowTelescopingAndSimplex.lean` | 133 | `[propext, Classical.choice, Quot.sound]` |

## 4. Complete 14-Hub Zenodo Publication Index
- **Hub 01 (Paper 0):** `10.5281/zenodo.24328033`
- **Hub 02 (Paper A):** `10.5281/zenodo.24328035`
- **Hub 03 (Paper B):** `10.5281/zenodo.24328037`
- **Hub 04 (Paper C):** `10.5281/zenodo.24328039`
- **Hub 05 (Paper D):** `10.5281/zenodo.24328045`
- **Hub 06 (Paper E):** `10.5281/zenodo.24328047`
- **Hub 07 (Master Lean 4 Repo & 55 Units):** `10.5281/zenodo.24329861` *(Concept DOI `10.5281/zenodo.24150107`)*
- **Hub 08 (Paper F):** `10.5281/zenodo.24328918`
- **Hub 09 (Paper G):** `10.5281/zenodo.24328921`
- **Hub 10 (Paper H):** `10.5281/zenodo.24328927`
- **Hub 11 (Paper I):** `10.5281/zenodo.24328929`
- **Hub 12 (Paper J):** `10.5281/zenodo.24344628` *(prev `24330500`, `24330400`)*
- **Hub 13 (Paper K):** `10.5281/zenodo.24344631` *(prev `24344084`, `24343525`, `24342906`, `24342619`, `24342096`, `24341228`, `24341007`, `24339838`)*
- **Hub 14 (Paper L — Unified Master Review):** Published live at `10.5281/zenodo.24344632` *(prev `24344093`, `24343534`, `24342950`, `24342626`, `24342101`, `24341718`, `24341498`; supplemented by `10.5281/zenodo.24329861`)*

---

## 5. Zotero BibTeX Integration & Citation-Style Switching
Every manuscript package (`PAPER_J_SUBMISSION_PACKAGE`, `PAPER_K_SUBMISSION_PACKAGE`, `PAPER_L_SUBMISSION_PACKAGE`) ships the master BibTeX database `riemann_master_references.bib` paired with pre-generated `.bbl` files:
- **Zotero Import / Better BibTeX Sync:** In Zotero, choose **File $\to$ Import...** and select `riemann_master_references.bib` (or configure Better BibTeX auto-export to track the file directly). All historical and contemporary entries include full bibliographic metadata and standard DOIs.
- **Switching Journal Styles in LaTeX:** Each `.tex` file uses `\bibliographystyle{amsplain}` and `\bibliography{riemann_master_references}`. Replace `amsplain` with any standard style (`amsalpha`, `apalike`, `unsrtnat`, `elsarticle-num`) and re-run `pdflatex -> bibtex -> pdflatex -> pdflatex`.
