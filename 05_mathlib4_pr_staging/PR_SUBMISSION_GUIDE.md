# Modular Lean 4 Formalization Guide — Waves 1–8 (55 Self-Contained Units)

**Author / Contributor:** Qamar Munawer (Brandenburg University of Technology Cottbus–Senftenberg)  
**Staging Directory:** `MATHLIB4_PR_STAGING/`  
**Verified Build Mirror:** `RiemannBlueprint/RiemannBlueprint/UpstreamPRs/`  
**Automation Script:** `push_carved_prs_to_mathlib4.py`  
**Fork Archive Target:** `Qamarbajwa/mathlib4` (`55` standalone `feat/*` branches; `ALLOW_UPSTREAM_BOT_ACTIONS = False` — never opens or comments on upstream PRs)  
**Epistemic Invariant:** `NO_RH_PROOF = TRUE` (all 55 modules verify unconditional classical identities, Hardy 1914 critical-line zeros, zero-free region estimates, Vasyunin cross-integrals, exact `N = 4, 5, 6` certificates, all-`N` universal symmetries, or conditional RH bridges; none claim an unconditional RH proof)

---

## Standalone Repository & Fork Archive Policy

1. All 55 `UpstreamPR_1A`–`8L.lean` files are maintained as **55 self-contained, linter-verified modular Lean 4 formalization units** archived on `Qamarbajwa/RiemannBlueprint`, `Qamarbajwa/mathlib4`, and Zenodo (`10.5281/zenodo.24329861`).
2. `ALLOW_UPSTREAM_BOT_ACTIONS = False` disables automated `gh pr create` and `gh pr comment` mutations against `leanprover-community/mathlib4`. `--inspect` and `--advance-queue` operate strictly as read-only local status monitors.
3. Branches are pushed strictly to the user-owned fork `https://github.com/Qamarbajwa/mathlib4.git`.
4. Every module registers cleanly as `public import Mathlib.NumberTheory.LSeries.<Name>` in `Mathlib.lean` (never before line 1 `module`).

### Fork Verification & Staging Commands

```bash
# Dry-run import rewriting & line-length audit across all 55 modules
python push_carved_prs_to_mathlib4.py --wave all --dry-run

# Push carved branches from a local mathlib4 checkout to user-owned fork Qamarbajwa/mathlib4
python push_carved_prs_to_mathlib4.py --mathlib-dir /path/to/mathlib4 --wave all --base-ref master --remote origin --push

# Verify all 55 pushed feat/* branches on Qamarbajwa/mathlib4
python push_carved_prs_to_mathlib4.py --check-remote-ci
```

---

## Wave 1, Wave 2, Wave 3 & Wave 4 Summary & Target Paths

### Wave 1 (Root Self-Contained Clusters)

| PR | Staged File | Target `mathlib4` Path | Lines | Max Chars | `#lint` (15 linters) | Axioms |
| :--- | :--- | :--- | :---: | :---: | :---: | :--- |
| **PR-1A** | `UpstreamPR_1A_CriticalLineZeros.lean` | `Mathlib/NumberTheory/LSeries/CriticalLineZeros.lean` | 131 | 99 | `0` errors (`12` decls) | `[propext, Classical.choice, Quot.sound]` |
| **PR-3A** | `UpstreamPR_3A_VasyuninIntegral.lean` | `Mathlib/NumberTheory/LSeries/VasyuninIntegral.lean` | 250 | 99 | `0` errors (`16` decls) | `[propext, Classical.choice, Quot.sound]` |
| **PR-4A** | `UpstreamPR_4A_AffineLagrangeProjection.lean` | `Mathlib/NumberTheory/LSeries/BaezDuarteProjection.lean` | 191 | 99 | `0` errors (`18` decls) | `[propext, Classical.choice, Quot.sound]` |

### Wave 2 (De la Vallée Poussin Unconditional Zero-Free Region Chain)

| PR | Staged File | Target `mathlib4` Path | Depends On | Lines | Max Chars | `#lint` (15 linters) | Axioms |
| :--- | :--- | :--- | :--- | :---: | :---: | :---: | :--- |
| **PR-1B** | `UpstreamPR_1B_ZetaPoleAndRepulsion.lean` | `Mathlib/NumberTheory/LSeries/ZetaPoleAndRepulsion.lean` | `PR-1A` | 180 | 100 | `0` errors (`10` decls) | `[propext, Classical.choice, Quot.sound]` |
| **PR-1C** | `UpstreamPR_1C_ZetaRemainderSeries.lean` | `Mathlib/NumberTheory/LSeries/ZetaRemainderSeries.lean` | `Mathlib.*` only | 166 | 98 | `0` errors (`6` decls) | `[propext, Classical.choice, Quot.sound]` |
| **PR-1D** | `UpstreamPR_1D_ZetaPartialSummation.lean` | `Mathlib/NumberTheory/LSeries/ZetaPartialSummation.lean` | `PR-1C` | 174 | 98 | `0` errors (`5` decls) | `[propext, Classical.choice, Quot.sound]` |
| **PR-1E** | `UpstreamPR_1E_ZetaLogStripBound.lean` | `Mathlib/NumberTheory/LSeries/ZetaLogStripBound.lean` | `PR-1D` | 213 | 99 | `0` errors (`2` decls) | `[propext, Classical.choice, Quot.sound]` |
| **PR-1F** | `UpstreamPR_1F_ZetaZeroFreeRegion.lean` | `Mathlib/NumberTheory/LSeries/ZeroFreeRegion.lean` | `PR-1B`, `PR-1E` | 205 | 99 | `0` errors (`3` decls) | `[propext, Classical.choice, Quot.sound]` |

### Wave 3 (Vasyunin Cross-Integral, Rank-4 Cotangent Bridge & `N = 4` Certificates)

| PR | Staged File | Target `mathlib4` Path | Depends On | Lines | Max Chars | `#lint` (15 linters) | Axioms |
| :--- | :--- | :--- | :--- | :---: | :---: | :---: | :--- |
| **PR-3B** | `UpstreamPR_3B_VasyuninSmoothAndCotDefs.lean` | `Mathlib/NumberTheory/LSeries/VasyuninDefs.lean` | `PR-3A`, `PR-4A` | 241 | 98 | `0` errors (`25` decls) | `[propext, Classical.choice, Quot.sound]` |
| **PR-3C** | `UpstreamPR_3C_HarmonicCellAndAbelSum.lean` | `Mathlib/NumberTheory/LSeries/VasyuninAbelSum.lean` | `PR-3B`, `PR-3D` | 259 | 100 | `0` errors (`5` decls) | `[propext, Classical.choice, Quot.sound]` |
| **PR-3D** | `UpstreamPR_3D_StirlingAndHarmonicAsymptotics.lean` | `Mathlib/NumberTheory/LSeries/VasyuninStirlingAsymp.lean` | `Mathlib.*` only | 209 | 99 | `0` errors (`9` decls) | `[propext, Classical.choice, Quot.sound]` |
| **PR-3E** | `UpstreamPR_3E_CotangentMittagLefflerLimit.lean` | `Mathlib/NumberTheory/LSeries/VasyuninCotangentLimit.lean` | `PR-3B` | 221 | 100 | `0` errors (`5` decls) | `[propext, Classical.choice, Quot.sound]` |
| **PR-3F** | `UpstreamPR_3F_VasyuninCrossIntegral.lean` | `Mathlib/NumberTheory/LSeries/VasyuninCrossIntegral.lean` | `PR-3C`, `PR-3D`, `PR-3E` | 193 | 100 | `0` errors (`6` decls) | `[propext, Classical.choice, Quot.sound]` |
| **PR-3G** | `UpstreamPR_3G_MobiusCandidateFourCert.lean` | `Mathlib/NumberTheory/LSeries/BaezDuarteMobiusFour.lean` | `PR-3F` | 188 | 98 | `0` errors (`16` decls) | `[propext, Classical.choice, Quot.sound]` |
| **PR-3H** | `UpstreamPR_3H_VariationalOptimumFour.lean` | `Mathlib/NumberTheory/LSeries/BaezDuarteVariationalFour.lean` | `PR-3G` | 199 | 99 | `0` errors (`15` decls) | `[propext, Classical.choice, Quot.sound]` |
| **PR-4B** | `UpstreamPR_4B_AffineOrthogonalDecomp.lean` | `Mathlib/NumberTheory/LSeries/BaezDuarteOrthogonalDecomp.lean` | `PR-4A` | 127 | 99 | `0` errors (`9` decls) | `[propext, Classical.choice, Quot.sound]` |
| **PR-4C** | `UpstreamPR_4C_HarmonicWaveletBasis.lean` | `Mathlib/NumberTheory/LSeries/BaezDuarteWaveletBasis.lean` | `PR-3H`, `PR-4B` | 212 | 99 | `0` errors (`8` decls) | `[propext, Classical.choice, Quot.sound]` |
| **PR-4D** | `UpstreamPR_4D_WaveletCotangentStencil.lean` | `Mathlib/NumberTheory/LSeries/BaezDuarteWaveletStencil.lean` | `PR-4C` | 203 | 99 | `0` errors (`5` decls) | `[propext, Classical.choice, Quot.sound]` |
| **PR-4E** | `UpstreamPR_4E_TangentCotangentPositivity.lean` | `Mathlib/NumberTheory/LSeries/BaezDuarteTangentPositivity.lean` | `PR-4D` | 218 | 100 | `0` errors (`7` decls) | `[propext, Classical.choice, Quot.sound]` |
| **PR-4F** | `UpstreamPR_4F_TangentRayleighQuotient.lean` | `Mathlib/NumberTheory/LSeries/BaezDuarteRayleighQuotient.lean` | `PR-4E` | 231 | 99 | `0` errors (`9` public decls / `18` total) | `[propext, Classical.choice, Quot.sound]` |
| **PR-4G** | `UpstreamPR_4G_GlobalOptimumFour.lean` | `Mathlib/NumberTheory/LSeries/BaezDuarteGlobalOptimumFour.lean` | `PR-4F` | 215 | 99 | `0` errors (`8` public decls / `21` total) | `[propext, Classical.choice, Quot.sound]` |
| **PR-4H** | `UpstreamPR_4H_WaveletRayleighRHCriterion.lean` | `Mathlib/NumberTheory/LSeries/BaezDuarteRayleighCriterion.lean` | `PR-4G` | 164 | 97 | `0` errors (`6` public decls / `8` total) | `[propext, Classical.choice, Quot.sound]` |
| **PR-4I** | `UpstreamPR_4I_CumulativeWaveletDipole.lean` | `Mathlib/NumberTheory/LSeries/BaezDuarteCumulativeDipole.lean` | `PR-4H` | 248 | 99 | `0` errors (`8` public decls / `26` total) | `[propext, Classical.choice, Quot.sound]` |
| **PR-4J** | `UpstreamPR_4J_FourPointDipoleKernel.lean` | `Mathlib/NumberTheory/LSeries/BaezDuarteFourPointDipole.lean` | `PR-4I` | 157 | 100 | `0` errors (`6` public decls / `7` total) | `[propext, Classical.choice, Quot.sound]` |
| **PR-4K** | `UpstreamPR_4K_GeneralWaveletCompleteness.lean` | `Mathlib/NumberTheory/LSeries/BaezDuarteWaveletCompleteness.lean` | `PR-4J` | 245 | 100 | `0` errors (`7` public decls / `12` total) | `[propext, Classical.choice, Quot.sound]` |
| **PR-4L** | `UpstreamPR_4L_DipoleQuadraticReduction.lean` | `Mathlib/NumberTheory/LSeries/BaezDuarteDipoleQuadratic.lean` | `PR-4K` | 199 | 99 | `0` errors (`8` public decls / `9` total) | `[propext, Classical.choice, Quot.sound]` |
| **PR-4M** | `UpstreamPR_4M_DipoleDiagonalAndSymmetry.lean` | `Mathlib/NumberTheory/LSeries/BaezDuarteDipoleDiagonal.lean` | `PR-4L` | 82 | 99 | `0` errors (`7` decls) | `[propext, Classical.choice, Quot.sound]` |

### Wave 4 (Hardy 1914 Infinitely Many Critical-Line Zeros Chain)

| PR | Staged File | Target `mathlib4` Path | Depends On | Lines | Max Chars | `#lint` (15 linters) | Axioms |
| :--- | :--- | :--- | :--- | :---: | :---: | :---: | :--- |
| **PR-2B** | `UpstreamPR_2B_HardyPsiAndThetaKernel.lean` | `Mathlib/NumberTheory/LSeries/HardyPsiKernel.lean` | `Mathlib.*` only | 259 | 100 | `0` errors (`9` decls) | `[propext, Classical.choice, Quot.sound]` |
| **PR-2C** | `UpstreamPR_2C_HardyThetaIteratedDeriv.lean` | `Mathlib/NumberTheory/LSeries/HardyThetaDeriv.lean` | `PR-2B` | 260 | 100 | `0` errors (`5` decls) | `[propext, Classical.choice, Quot.sound]` |
| **PR-2D** | `UpstreamPR_2D_CompletedZetaStripDecay.lean` | `Mathlib/NumberTheory/LSeries/CompletedZetaStripDecay.lean` | `PR-2B` | 259 | 100 | `0` errors (`5` decls) | `[propext, Classical.choice, Quot.sound]` |
| **PR-2E** | `UpstreamPR_2E_HardyGContourAndMellin.lean` | `Mathlib/NumberTheory/LSeries/HardyGContour.lean` | `PR-2D` | 255 | 100 | `0` errors (`7` decls) | `[propext, Classical.choice, Quot.sound]` |
| **PR-2F** | `UpstreamPR_2F_HardyEvenMomentIdentity.lean` | `Mathlib/NumberTheory/LSeries/HardyEvenMoments.lean` | `PR-2B`, `PR-2E` | 229 | 99 | `0` errors (`7` decls) | `[propext, Classical.choice, Quot.sound]` |
| **PR-2G** | `UpstreamPR_2G_HardyCriticalLineZeros.lean` | `Mathlib/NumberTheory/LSeries/HardyCriticalLineZeros.lean` | `PR-1A`, `PR-2B`–`PR-2F` | 229 | 100 | `0` errors (`3` decls) | `[propext, Classical.choice, Quot.sound]` |

### Wave 5 (Papers F & G: Zeta Log-Derivative, Von Koch Equivalence, and Mellin Nyman–Beurling Converse)

| PR | Staged File | Target `mathlib4` Path | Depends On | Lines | Max Chars | `#lint` (15 linters) | Axioms |
| :--- | :--- | :--- | :--- | :---: | :---: | :---: | :--- |
| **PR-5A** | `UpstreamPR_5A_ZetaLogDerivHolomorphy.lean` | `Mathlib/NumberTheory/LSeries/ZetaInvHolomorphy.lean` | `Mathlib.*` only | 155 | 95 | `0` errors | `[propext, Classical.choice, Quot.sound]` |
| **PR-5B** | `UpstreamPR_5B_VonKochChebyshevPsi.lean` | `Mathlib/NumberTheory/LSeries/VonKochChebyshevPsi.lean` | `PR-5A` | 250 | 100 | `0` errors (`17` decls) | `[propext, Classical.choice, Quot.sound]` |
| **PR-5C** | `UpstreamPR_5C_MellinNymanBeurlingIff.lean` | `Mathlib/NumberTheory/LSeries/MellinNymanBeurlingConverse.lean` | `PR-3A`, `PR-4A`, `PR-5A` | 250 | 100 | `0` errors (`8` decls) | `[propext, Classical.choice, Quot.sound]` |

> **Pre-Flight Rule:** All 36 staged files use Lean 4.35 `module` + `public import` + `@[expose] public section`, contain zero legacy `RiemannBlueprint.MathlibPR_*` imports, zero `sorry`s, and zero lines over `100` characters. When pushing to `Qamarbajwa/mathlib4`, rebase root branches onto live `leanprover-community/mathlib4:master` (`FETCH_HEAD`).

---

## Wave 1 Details & Fork PR Bodies

### PR-1A: Critical-Line Symmetry, IVT Zero Detection & 3-4-1 Positivity

- **Branch / Target:** `Qamarbajwa:feat/critical-line-zeros` -> `Mathlib/NumberTheory/LSeries/CriticalLineZeros.lean`
- **GitHub PR Title:** `feat(NumberTheory/LSeries): critical-line IVT zero detection and 3-4-1 zeta product positivity`
- **Bot Label Comment:** `gh pr comment <pr-url> --repo leanprover-community/mathlib4 --body "LLM-generated"`

```markdown
### Summary

Adds a small, self-contained collection of elementary lemmas for `riemannZeta` along the critical line `Re(s) = 1 / 2` and near `Re(s) = 1`:

1. **Critical-line reflection & IVT sign-change detectors:** defines `criticalLine t := 1 / 2 + I * t`, proves `completedRiemannZeta (criticalLine (-t)) = completedRiemannZeta (criticalLine t)`, certifies critical-line zeros from continuous real detectors (`exists_criticalLine_zero_of_sign_change`) and `hardyZ` (`exists_criticalLine_zero_of_hardyZ_sign_change`), and deduces infinitude of zeros from unbounded sign changes (`infinite_criticalLine_zeros_of_sign_changes`, `infinite_hardyZ_zeros_of_sign_changes`).
2. **De la Vallée Poussin 3-4-1 kernel & `riemannZeta` specialization:** proves `three_add_four_cos_add_cos_two_mul_nonneg` (`0 ≤ 3 + 4 * cos θ + cos (2 * θ)`) and specializes `norm_LFunction_product_ge_one` at `N = 1`, `χ = 1` to obtain `norm_riemannZeta_product_ge_one`.

### Main Declarations

- `criticalLine`, `criticalLine_re`, `one_sub_criticalLine`, `completedRiemannZeta_criticalLine_neg`
- `exists_criticalLine_zero_of_sign_change`, `exists_criticalLine_zero_of_hardyZ_sign_change`
- `infinite_criticalLine_zeros_of_sign_changes`, `infinite_hardyZ_zeros_of_sign_changes`
- `three_add_four_cos_add_cos_two_mul_eq`, `three_add_four_cos_add_cos_two_mul_nonneg`
- `norm_riemannZeta_product_ge_one`

### Verification

- `lake build`: pass (`0` errors, `0` warnings)
- `#lint`: `0` errors across `12` declarations (`15` linters)
- `#print axioms`: strictly `[propext, Classical.choice, Quot.sound]`
- Max line length: `99` (`131` total lines)

### AI-Assistance Disclosure

Portions of the Lean 4 refactoring and Mathlib style formatting were prepared with AI assistance (Google DeepMind Antigravity). All declarations were independently type-checked and kernel-verified by Lean 4 without `sorry` or custom axioms.
```

---

### PR-3A: Vasyunin Diagonal & Báez-Duarte Improper Reciprocal Fractional-Part Integrals

- **Branch / Target:** `Qamarbajwa:feat/vasyunin-integral` -> `Mathlib/NumberTheory/LSeries/VasyuninIntegral.lean`
- **GitHub PR Title:** `feat(NumberTheory/LSeries): exact L1 and L2 reciprocal fractional-part integrals of Vasyunin and Baez-Duarte`
- **Bot Label Comment:** `gh pr comment <pr-url> --repo leanprover-community/mathlib4 --body "LLM-generated"`

```markdown
### Summary

Formalizes exact closed-form values for the `L¹(0, 1)` and `L²(0, 1)` improper integrals of `{1 / x}` and its integer dilations `{1 / (k x)}` (`k ≥ 1`):

- `∫₀¹ {1 / x} dx = 1 - γ` via interval splitting on `[1/(n+1), 1/n]` and `Real.tendsto_eulerMascheroniSeq'`.
- `∫₀¹ {1 / (k x)} dx = (ln k + 1 - γ) / k` (`bVasyunin k γ`) via scaling and `[1/k, 1]` FTC.
- `∫₀¹ {1 / x}² dx = ln(2π) - γ - 1` via exact finite telescoping of `n (ln(n+1) - ln n)` to `M ln M - ln(M!)` and `Stirling.tendsto_stirlingSeq_sqrt_pi`.
- `∫₀¹ {1 / (k x)}² dx = (ln(2π) - γ - 1 / k) / k`.

### Main Declarations

- `recipFract`, `recipFractScaled`, `bVasyunin`
- `intervalIntegral_recipFract_zero_to_one`
- `intervalIntegral_recipFractScaled_eq_bVasyunin`
- `intervalIntegral_sq_recipFract_zero_to_one`
- `intervalIntegral_sq_recipFractScaled_zero_to_one`

### Verification

- `lake build`: pass (`0` errors, `0` warnings)
- `#lint`: `0` errors across `16` declarations (`15` linters)
- `#print axioms`: strictly `[propext, Classical.choice, Quot.sound]`
- Max line length: `99` (`250` total lines)

### AI-Assistance Disclosure

Portions of the Lean 4 formalization and style cleanup were developed with AI assistance (Google DeepMind Antigravity). All proofs were independently type-checked and kernel-verified without `sorry` or custom axioms.
```

---

### PR-4A: Affine Harmonic Lagrange Projection on the Báez-Duarte Subspace

- **Branch / Target:** `Qamarbajwa:feat/baez-duarte-projection` -> `Mathlib/NumberTheory/LSeries/BaezDuarteProjection.lean`
- **GitHub PR Title:** `feat(NumberTheory/LSeries): affine harmonic Lagrange projection on the Baez-Duarte constraint subspace`
- **Bot Label Comment:** `gh pr comment <pr-url> --repo leanprover-community/mathlib4 --body "LLM-generated"`

```markdown
### Summary

Formalizes the closed-form 2-constraint Euclidean projection `projectAffine` onto the Báez-Duarte affine hyperplane intersection `D1 c N = ∑_{k=1}^N c_k / k = 0` and `D0 c N = ∑_{k=1}^N c_k = 2`:

1. Proves Lagrange's identity `2 * DeltaDet N = ∑_{j,k=1}^N (1/j - 1/k)^2` (`DeltaDet_double_sum_eq`).
2. Deduces unconditional strict positivity `0 < DeltaDet N` and non-vanishing `DeltaDet N ≠ 0` for all `N ≥ 2` (`DeltaDet_pos`, `DeltaDet_ne_zero`).
3. Proves unconditionally that `projectAffine u N` satisfies `D1 = 0` and `D0 = 2` for every vector `u : ℕ → ℝ` and every `N ≥ 2` (`projectAffine_mem_A_N_uncond`).
4. Provides exact rational evaluations at `N = 4` (`HSum_four = 25/12`, `S2Sum_four = 205/144`, `DeltaDet_four = 65/48`).

### Main Declarations

- `D0`, `D1`, `HSum`, `S2Sum`, `DeltaDet`, `lambda1`, `lambda0`, `projectAffine`
- `DeltaDet_double_sum_eq`, `DeltaDet_pos`, `DeltaDet_ne_zero`
- `projectAffine_D1`, `projectAffine_D0`, `projectAffine_mem_A_N_uncond`
- `HSum_four`, `S2Sum_four`, `DeltaDet_four`

### Verification

- `lake build`: pass (`0` errors, `0` warnings)
- `#lint`: `0` errors across `18` declarations (`15` linters)
- `#print axioms`: strictly `[propext, Classical.choice, Quot.sound]`
- Max line length: `99` (`191` total lines)

### AI-Assistance Disclosure

Portions of the Lean 4 formalization and style cleanup were developed with AI assistance (Google DeepMind Antigravity). All proofs were independently type-checked and kernel-verified without `sorry` or custom axioms.
```

---

## Wave 2 Dependency Stack (`PR-1B`–`PR-1F`)

Submit after Wave 1 / parent dependencies merge, or as stacked fork PRs (`push_carved_prs_to_mathlib4.py --wave 2 --create-pr`):

- **PR-1B** (`feat/zeta-pole-and-repulsion`, depends on `PR-1A`): `exists_pole_bound_one_add`, `valleePoussin_cubic_opt_identity`, `deLaValleePoussin_zero_repulsion`, `deLaValleePoussin_contradiction`, `deLaValleePoussin_zero_free_region`.
- **PR-1C** (`feat/zeta-remainder-series`, depends on `Mathlib.*` only): `zetaRemainderTerm`, integral representation, decay bound, and analyticity on `{s : ℂ | 0 < s.re ∧ s ≠ 1}`.
- **PR-1D** (`feat/zeta-partial-summation`, depends on `PR-1C`): `riemannZeta_eq_one_div_sub_add_tsum`, `riemannZeta_partial_summation`.
- **PR-1E** (`feat/zeta-log-strip-bound`, depends on `PR-1D`): `tsum_rpow_neg_sub_one_le`, `norm_riemannZeta_le_of_log_strip`.
- **PR-1F** (`feat/zeta-zero-free-region`, depends on `PR-1B`, `PR-1E`): `riemannZeta_horizontal_lipschitz_of_zero`, `deLaValleePoussin_zero_free_region_unconditional`.

---

## Wave 3 Dependency Stack (`PR-3B`–`PR-4M`)

Wave 3 follows the acyclic stack `PR-3A, PR-4A -> PR-3B -> {PR-3D, PR-3E} -> PR-3C -> PR-3F -> PR-3G -> PR-3H` and `{PR-4A -> PR-4B, PR-3H} -> PR-4C -> PR-4D -> PR-4E -> PR-4F -> PR-4G -> PR-4H -> PR-4I -> PR-4J -> PR-4K -> PR-4L -> PR-4M`:

- **PR-3B** (`Mathlib/NumberTheory/LSeries/VasyuninDefs.lean`, `feat/vasyunin-defs`): `GSmooth`, `vasyuninCotSum`, `vasyuninGCot`, `QCot`, `SCot`, `GSmooth_eq_rank4`, `affine_bdr_pure_cotangent_identity`.
- **PR-3C** (`Mathlib/NumberTheory/LSeries/VasyuninAbelSum.lean`, `feat/vasyunin-abel-sum`): `sum_Ico_abel`, `abel_log_sum_exact`, `abel_cross_sum_exact`, `cross_partial_exact_identity`.
- **PR-3D** (`Mathlib/NumberTheory/LSeries/VasyuninStirlingAsymp.lean`, `feat/vasyunin-stirling-asymp`): `tendsto_stirling_log_term`, `tendsto_harmonic_Ico_sub_log`, divisor quotient & `halfSum_exact` helpers.
- **PR-3E** (`Mathlib/NumberTheory/LSeries/VasyuninCotangentLimit.lean`, `feat/vasyunin-cotangent-limit`): `cotApproxSum`, `sum_Ico_fract_diff_div_eq_cotApproxSum`, `tendsto_cotApproxSum_term`, `tendsto_cotApproxSum`.
- **PR-3F** (`Mathlib/NumberTheory/LSeries/VasyuninCrossIntegral.lean`, `feat/vasyunin-cross-integral`): `intervalIntegral_recipFractScaled_cross`, `affine_l2_pure_cotangent_bridge`, `affine_l2_dist_eq_one_sub_scot`, `projectAffine_l2_dist_eq_one_sub_scot`.
- **PR-3G** (`Mathlib/NumberTheory/LSeries/BaezDuarteMobiusFour.lean`, `feat/baez-duarte-mobius-four`): `mollifiedMobius`, `cCandidateMobius`, `cCandidateMobius_mem_A_N_uncond`, `mollifiedMobius_four_eval`, `cCandidateMobius_four_eval`, `SCot_cCandidateMobius_four_eq`, `cCandidateMobius_four_l2_dist_eq`, `cCandidateMobius_four_l2_dist_pos`.
- **PR-3H** (`Mathlib/NumberTheory/LSeries/BaezDuarteVariationalFour.lean`, `feat/baez-duarte-variational-four`): `l2_dist_sub_eq_scot_sub`, `l2_dist_lt_iff_scot_gt`, `cVariationalFour`, `cVariationalFour_mem_A_N`, `SCot_cVariationalFour_eq`, `SCot_cCandidateMobius_four_lt_cVariationalFour`, `l2_dist_cVariationalFour_lt_cCandidateMobius_four`, `cVariationalFour_l2_dist_pos`.
- **PR-4B** (`Mathlib/NumberTheory/LSeries/BaezDuarteOrthogonalDecomp.lean`, `feat/baez-duarte-orthogonal-decomp`): `cMinNorm`, `cMinNorm_eq`, `cMinNorm_mem_A_N_uncond`, `cMinNorm_inner_eq_zero`, `cMinNorm_norm_sq_eq`, `norm_sq_eq_cMinNorm_add_sub_sq`, `cMinNorm_le_norm_sq_on_A_N`, `cMinNorm_norm_sq_four`.
- **PR-4C** (`Mathlib/NumberTheory/LSeries/BaezDuarteWaveletBasis.lean`, `feat/baez-duarte-wavelet-basis`): `cBaseAnchor`, `cBaseAnchor_mem_A_N`, `SCot_cBaseAnchor_eq_zero`, `cBaseAnchor_l2_dist_eq_one`, `harmonicWavelet`, `harmonicWavelet_mem_tangent`, `cBaseAnchor_add_smul_wavelet_mem_A_N`, `cVariationalFour_eq_wavelet_decomp`.
- **PR-4D** (`Mathlib/NumberTheory/LSeries/BaezDuarteWaveletStencil.lean`, `feat/baez-duarte-wavelet-stencil`): `deltaCot`, `harmonicWavelet_div_sum_eq_second_diff`, `sum_cBaseAnchor_vasyuninGCot_eq`, `SCot_cBaseAnchor_add_eq`, `SCot_cBaseAnchor_add_smul_wavelet_eq`.
- **PR-4E** (`Mathlib/NumberTheory/LSeries/BaezDuarteTangentPositivity.lean`, `feat/baez-duarte-tangent-positivity`): `sum_GSmooth_eq_zero_of_mem_tangent`, `tangent_l2_norm_sq_eq_qcot`, `QCot_nonneg_of_mem_tangent`, `SCot_nonpos_of_mem_tangent`, `QCot_harmonicWavelet_one_eq`, `harmonicWavelet_one_l2_norm_sq_eq`, `SCot_cBaseAnchor_add_two_thirds_wavelet_one_eq`.
- **PR-4F** (`Mathlib/NumberTheory/LSeries/BaezDuarteRayleighQuotient.lean`, `feat/baez-duarte-rayleigh-quotient`): `linearCotDrive`, `optTangentStep`, `tangentRayleighQuotient`, `SCot_cBaseAnchor_add_smul_eq_rayleigh_sub_sq`, `SCot_cBaseAnchor_add_optTangentStep_eq`, `sq_linearCotDrive_le_qcot`, `tangentRayleighQuotient_le_one`, `SCot_cBaseAnchor_add_smul_wavelet_one_eq_completing_sq`, `SCot_cBaseAnchor_add_smul_wavelet_one_le`.
- **PR-4G** (`Mathlib/NumberTheory/LSeries/BaezDuarteGlobalOptimumFour.lean`, `feat/baez-duarte-global-optimum-four`): `eq_cBaseAnchor_add_wavelets_of_mem_A_four`, `QCot_harmonicWavelet_two_eq`, `SCot_cBaseAnchor_add_two_wavelets_eq`, `cGlobalOptFour`, `cGlobalOptFour_mem_A_N`, `SCot_cGlobalOptFour_eq`, `SCot_le_cGlobalOptFour_of_mem_A_four`, `l2_dist_cGlobalOptFour_le_of_mem_A_four`.
- **PR-4H** (`Mathlib/NumberTheory/LSeries/BaezDuarteRayleighCriterion.lean`, `feat/baez-duarte-rayleigh-criterion`): `tangentRayleighQuotient_smul`, `sum_smul_harmonicWavelet_mem_tangent`, `linearCotDrive_sum_harmonicWavelet_eq`, `sub_cBaseAnchor_mem_tangent`, `SCot_le_tangentRayleighQuotient_sub_cBaseAnchor`, `one_sub_tangentRayleighQuotient_le_l2_dist`.
- **PR-4I** (`Mathlib/NumberTheory/LSeries/BaezDuarteCumulativeDipole.lean`, `feat/baez-duarte-cumulative-dipole`): `cumulativeDipole`, `cumulativeDipole_mem_tangent`, `linearCotDrive_cumulativeDipole_eq`, `QCot_cumulativeDipole_two_eq`, `sum_cumulativeDipole_one_two_vasyuninGCot_eq_zero`, `vasyuninCotSum_five_one_add_four`, `vasyuninCotSum_five_two_add_three`, `sum_cumulativeDipole_two_three_vasyuninGCot_five_eq_zero`.
- **PR-4J** (`Mathlib/NumberTheory/LSeries/BaezDuarteFourPointDipole.lean`, `feat/baez-duarte-four-point-dipole`): `cumulativeDipole_div_sum_eq_four_point`, `unweightedKCot`, `unweightedKCot_comm`, `unweightedKCot_diag`, `unweightedKCot_one_sub_two`, `sum_cumulativeDipole_vasyuninGCot_eq_four_point`.
- **PR-4K** (`Mathlib/NumberTheory/LSeries/BaezDuarteWaveletCompleteness.lean`, `feat/baez-duarte-wavelet-completeness`): `cumulativeDipole_eq_four_term`, `dipoleCoord`, `waveletCoord`, `eq_sum_cumulativeDipole_of_mem_tangent`, `eq_sum_harmonicWavelet_of_mem_tangent`, `eq_cBaseAnchor_add_sum_cumulativeDipole_of_mem_A_N`, `eq_cBaseAnchor_add_sum_harmonicWavelet_of_mem_A_N`.
- **PR-4L** (`Mathlib/NumberTheory/LSeries/BaezDuarteDipoleQuadratic.lean`, `feat/baez-duarte-dipole-quadratic`): `dipoleCoord_eq_neg_sum_Icc_of_D1_eq_zero`, `dipoleGramEntry`, `linearCotDrive_eq_sum_dipoleCoord`, `QCot_eq_sum_dipoleGramEntry`, `SCot_eq_dipoleCoord_quadratic_of_mem_A_N`, `dipoleCoord_cGlobalOptFour_eval`, `dipoleCoord_cCandidateMobius_four_eval`, `dipoleCoord_cGlobalOptFour_two_lt_cCandidateMobius_four`.
- **PR-4M** (`Mathlib/NumberTheory/LSeries/BaezDuarteDipoleDiagonal.lean`, `feat/baez-duarte-dipole-diagonal`): `dipoleGramEntry_comm`, `dipoleGramEntry_diag_eq`, `QCot_cumulativeDipole_eq_dipoleGramEntry_diag`, `dipoleGramEntry_diag_nonneg`, `dipoleGramEntry_one_one_eq`, `dipoleGramEntry_two_two_eq`, `dipoleGramEntry_one_two_eq_zero`.

---

## Wave 4 Dependency Stack (`PR-2B`–`PR-2G`)

Wave 4 follows the acyclic stack `PR-2B -> {PR-2C, PR-2D -> PR-2E -> PR-2F}` and merges `PR-1A`, `PR-2C`, `PR-2F` into `PR-2G`:

- **PR-2B** (`Mathlib/NumberTheory/LSeries/HardyPsiKernel.lean`, `feat/hardy-psi-kernel`): `hardyPsi`, `hardyThetaTerm`, `differentiableAt_hardyPsi`, `differentiableOn_hardyThetaTerm_mul_I`, `hardyPsi_neg`, `norm_hardyPsi_le`, `integrable_hardyPsi_shift`, `jacobiTheta_neg_one_add`.
- **PR-2C** (`Mathlib/NumberTheory/LSeries/HardyThetaDeriv.lean`, `feat/hardy-theta-deriv`): `norm_jacobiTheta_neg_one_add_le`, `tendsto_iteratedDeriv_hardyThetaTerm`.
- **PR-2D** (`Mathlib/NumberTheory/LSeries/CompletedZetaStripDecay.lean`, `feat/completed-zeta-strip-decay`): `completedRiemannZeta_half_add_mul_I_eq_fourier`, `integrable_hardyPsi_shift_mul_cexp`, `completedRiemannZeta_half_add_mul_I_eq_shift`.
- **PR-2E** (`Mathlib/NumberTheory/LSeries/HardyGContour.lean`, `feat/hardy-g-contour`): `norm_completedRiemannZeta_criticalLine_le`, `continuous_completedRiemannZeta_criticalLine`, `integrable_abs_pow_mul_exp_mul_completedRiemannZeta`, `hardyG`, `hardyG_eq_hardyPsi`.
- **PR-2F** (`Mathlib/NumberTheory/LSeries/HardyEvenMoments.lean`, `feat/hardy-even-moments`): `norm_iteratedDeriv_hardyCoshTerm_le`, `hardyGn`, `iteratedDeriv_hardyPsi_mul_I_eq`, `hardyGn_even_re`.
- **PR-2G** (`Mathlib/NumberTheory/LSeries/HardyCriticalLineZeros.lean`, `feat/hardy-critical-line-zeros`): `infinite_criticalLine_zeros`, `infinite_hardyZ_zeros`.

---

## Wave 5 Dependency Stack (`PR-5A`–`PR-5C`)

Wave 5 covers Papers F & G:

- **PR-5A** (`Mathlib/NumberTheory/LSeries/ZetaInvHolomorphy.lean`, `feat/zeta-inv-holomorphy`): `analyticAt_inv_riemannZeta_of_ne_zero`, `analyticAt_neg_deriv_div_riemannZeta_of_ne_zero`, `differentiableOn_logDeriv_riemannZeta_of_riemannHypothesis`, `riemannHypothesis_iff_analyticAt_inv_riemannZeta`.
- **PR-5B** (`Mathlib/NumberTheory/LSeries/VonKochChebyshevPsi.lean`, `feat/von-koch-chebyshev-psi`): `chebyshevPsi`, `VonKochRemainderBound`, `chebyshevPsiRemainder`, `mellinVonKochRemainder`, `mellinVonKochRemainder_analyticOnNhd`, `neg_deriv_riemannZeta_div_eq_pole_add_mellinVonKochRemainder`, `zero_free_re_gt_half_of_vonKoch`, `vonKoch_implies_rh`, `RiemannHypothesis.of_chebyshevPsi_sub_self_isBigO`.
- **PR-5C** (`Mathlib/NumberTheory/LSeries/MellinNymanBeurlingConverse.lean`, `feat/mellin-nyman-beurling-iff`): `TitchmarshMellinProperty`, `integral_Ioc_recipFractScaled_cpow_of_unit`, `integral_Ioo_moebius_recipFract_eq`, `tendsto_mellin_moebius_recipFract_of_riemannHypothesis`, `riemannHypothesis_iff_mellin_recipFract_approx`.

---

## Wave 6 Dependency Stack (`PR-6A`–`PR-6C`, Papers F & I)

- **PR-6A** (`Mathlib/NumberTheory/LSeries/CompletedZetaDerivSymmetry.lean`, `feat/completed-zeta-deriv-symmetry`, root `master`, 202 lines, max 100 chars): `IsOnCriticalLine`, `reflection_preserves_critical_line`, `PrimeZeta`, `CompositeZeta`, `IsEquipartitionFulcrum`, `riemannZeta_eq_one_add_primeZeta_add_compositeZeta`, `zeta_at_equipartition_fulcrum`, `equipartition_fifty_fifty_split`, `zero_reflection_dichotomy`, `completedRiemannZeta_deriv_one_sub`, `completedRiemannZeta_deriv_at_half`, `completedRiemannZeta_deriv_critical_line_antisymm`.
- **PR-6B** (`Mathlib/NumberTheory/LSeries/CriticalLinePenetrationBarrier.lean`, `feat/critical-line-penetration-barrier`, stacked on `PR-4A` + `PR-5C`, 250 lines, max 100 chars): `dirichletPoly`, `stripDefect`, `analyticOnNhd_dirichletPoly`, `analyticOnNhd_zeta_mul_dirichletPoly`, `ne_zero_of_norm_one_add_mul_lt_one`, `stripDefect_norm_lt_one_implies_ne_zero`, `inv_zeta_approx_error_eq`, `critical_line_penetration_lower_bound`, `stripDefect_eq_mul_mellin_residual`.
- **PR-6C** (`Mathlib/NumberTheory/LSeries/PrimeCompositeDirichletSplit.lean`, `feat/prime-composite-dirichlet-split`, root `master`, 210 lines, max 100 chars): `natPrimes`, `natUnits`, `natComposites`, `nat_partition_dichotomy`, `bezout_identity`, `euclid_lemma`, `modulo_6_sieve_confinement`, `fermats_little_theorem`, `wilsons_theorem`, `InCriticalStrip`, `RiemannHypothesisStrip`, `zetaZeroReflectionSymmetry_unconditional`, `riemannHypothesis_iff_strip`.

---

## Wave 7 Dependency Stack (`PR-7A`–`PR-7D`, Layers B & C)

- **PR-7A** (`Mathlib/NumberTheory/LSeries/MellinKernelEnergy.lean`, `feat/mellin-kernel-energy-identity`, root `master`, 125 lines, max 98 chars): `mellinWeight`, `integrableOn_sq_mellinWeight`, `integral_Ioc_sq_mellinWeight`, `integral_Ioc_mellinWeight_sq`, `sq_mellin_weighted_le_div_two_mul_sub_one`, `integral_Ioc_two_mul_mellin_le`.
- **PR-7B** (`Mathlib/Analysis/Complex/RectangleContourSubdivision.lean`, `feat/rectangle-contour-subdivision`, root `master`, 107 lines, max 100 chars): `rectBoundaryIntegral`, `rectBoundaryIntegral_const`, `rectBoundaryIntegral_split_sigma`, `rectBoundaryIntegral_split_height`, `rectBoundaryIntegral_self_sigma`, `rectBoundaryIntegral_self_height`.
- **PR-7C** (`Mathlib/NumberTheory/LSeries/BaezDuartePurePlaque.lean`, `feat/baez-duarte-pure-plaque-reduction`, stacked on `PR-4M`, 162 lines, max 100 chars): `dipolePlaqueEntry`, `dipolePlaqueEntry_comm`, `dipolePlaqueEntry_diag_eq`, `dipoleGramEntry_eq_boundary_add_plaque`, `QCot_eq_h_one_mul_linearCotDrive_add_plaque`, `SCot_eq_neg_c_one_mul_linearCotDrive_sub_plaque`.
- **PR-7D** (`Mathlib/NumberTheory/LSeries/BaezDuarteOffDiagonalFrontier.lean`, `feat/baez-duarte-off-diagonal-frontier`, stacked on `PR-7C`, 97 lines, max 100 chars): `dipoleDiagEnergy`, `dipoleOffDiagEnergy`, `dipoleDiagEnergy_nonneg`, `QCot_eq_dipoleDiagEnergy_add_dipoleOffDiagEnergy`, `dipoleOffDiagEnergy_le_one_sub_dipoleDiagEnergy_of_mem_A_N`, `SCot_eq_drive_sub_diag_sub_offDiag`.

---

## Wave 8 Dependency Stack (`PR-8A`–`PR-8L`, Papers K & L)

- **PR-8A** (`Mathlib/NumberTheory/LSeries/BaezDuartePlaqueCauchySchwarz.lean`, `feat/baez-duarte-plaque-cauchy-schwarz`, stacked on `PR-7D` + `PR-4H`, 144 lines, max 96 chars): `dipolePlaqueForm`, `dipoleCoord_sub_cBaseAnchor_eq`, `dipolePlaqueForm_sub_cBaseAnchor_eq`, `QCot_eq_h_one_mul_drive_add_dipolePlaqueForm`, `SCot_eq_neg_c_one_mul_drive_sub_dipolePlaqueForm`, `l2_dist_eq_one_add_c_one_mul_drive_add_dipolePlaqueForm`, `sq_linearCotDrive_sub_le_dipolePlaqueForm`, `neg_h_one_sq_div_four_le_dipolePlaqueForm`, `one_sub_h_one_le_dipolePlaqueForm_of_unit_drive`.
- **PR-8B** (`Mathlib/NumberTheory/LSeries/BaezDuarteDirichletAnchoredPlaque.lean`, `feat/baez-duarte-dirichlet-anchored-plaque`, stacked on `PR-8A`, 147 lines, max 99 chars): `IsDirichletAnchored`, `cDirichletAnchor`, `cDirichletAnchor_isDirichletAnchored`, `IsDirichletAnchored.sub_mem_tangent`, `dipolePlaqueForm_ge_of_dirichlet`, `dipolePlaqueForm_nonneg_of_dirichlet_of_one_le_drive`, `neg_one_div_four_le_dipolePlaqueForm_of_dirichlet`, `SCot_eq_drive_sub_dipolePlaqueForm_of_dirichlet`, `unit_drive_dirichlet_plaque_eq_l2_dist`, `unit_drive_dirichlet_plaque_nonneg`.
- **PR-8C** (`Mathlib/NumberTheory/LSeries/BaezDuartePlaqueTelescoping.lean`, `feat/baez-duarte-plaque-telescoping`, stacked on `PR-8B`, 168 lines, max 100 chars): `unweightedKCot_two_two_eq_zero`, `sum_Icc_dipolePlaqueEntry_eq`, `dipolePlaqueForm_eq_telescoped_kernel`, `dipolePlaqueForm_sub_cBaseAnchor_eq_telescoped_kernel`, `SCot_eq_drive_sub_telescoped_kernel_of_dirichlet`.
- **PR-8D** (`Mathlib/NumberTheory/LSeries/BaezDuartePurePlaqueRHCriterion.lean`, `feat/baez-duarte-pure-plaque-rh-criterion`, stacked on `PR-8C` + `PR-5C` + `PR-7A`, 239 lines, max 100 chars): `PurePlaqueVanishingCriterion`, `TelescopedPlaqueVanishingCriterion`, `purePlaqueVanishing_iff_telescoped`, `mellin_l2_floor_of_zeta_zero`, `purePlaque_floor_of_zeta_zero`, `riemannHypothesis_of_purePlaque_vanishing`, `riemannHypothesis_of_telescoped_plaque_vanishing`.
- **PR-8E** (`Mathlib/NumberTheory/LSeries/BaezDuarteDirichletOptFour.lean`, `feat/baez-duarte-dirichlet-opt-four`, stacked on `PR-8D`, 162 lines, max 99 chars): `cDirichletOptFour`, `cDirichletOptFour_isDirichletAnchored`, `SCot_eq_dirichlet_four_sub_sq`, `SCot_cDirichletOptFour_eq`, `SCot_le_cDirichletOptFour_of_isDirichletAnchored_four`, `one_sub_31_div_108_pi_le_l2_dist_of_isDirichletAnchored_four`.
- **PR-8F** (`Mathlib/NumberTheory/LSeries/BaezDuarteDipoleGramFive.lean`, `feat/baez-duarte-dipole-gram-five`, stacked on `PR-8E`, 172 lines, max 98 chars): `dipoleGramEntry_two_three_eq_zero`, `vasyuninCotSum_five_one_eq`, `vasyuninCotSum_five_two_eq`, `dipoleGramEntry_one_three_eq`, `dipoleGramEntry_three_three_eq`, `dipolePlaqueEntry_two_three_eq`.
- **PR-8G** (`Mathlib/NumberTheory/LSeries/BaezDuarteCotangentSix.lean`, `feat/baez-duarte-cotangent-six`, stacked on `PR-8F`, 209 lines, max 100 chars): `vasyuninCotSum_six_eval`, `deltaCot_six_eq`, `vasyuninCotSum_two_six_eq_zero`, `vasyuninCotSum_three_six_eq_zero`, `vasyuninCotSum_four_six_eq_zero`, `unweightedKCot_two_six_eq`, `unweightedKCot_three_six_eq_zero`, `unweightedKCot_four_six_eq`, `dipoleGramEntry_add_succ_right`, `dipoleGramEntry_one_three_add_one_four_eq`, `dipoleGramEntry_one_four_eq`, `dipoleGramEntry_two_four_eq_zero`.
- **PR-8H** (`Mathlib/NumberTheory/LSeries/BaezDuarteUniversalCotangent.lean`, `feat/baez-duarte-universal-cotangent`, stacked on `PR-8G`, 125 lines, max 100 chars): `vasyuninCotSum_mod_eq`, `vasyuninCotSum_add_self_right`, `vasyuninCotSum_dvd_right_eq_zero`, `fract_sub_mul_div_eq`, `vasyuninCotSum_sub_eq_neg`, `vasyuninCotSum_two_mul_self_eq_zero`, `vasyuninCotSum_self_two_mul_eq_zero`, `unweightedKCot_self_two_mul_eq_zero`.
- **PR-8I** (`Mathlib/NumberTheory/LSeries/BaezDuarteLogarithmicPlaqueDecay.lean`, `feat/baez-duarte-logarithmic-plaque-decay`, stacked on `PR-8H`, 88 lines, max 96 chars): `purePlaqueVanishing_of_majorant_tendsto_zero`, `riemannHypothesis_of_plaque_majorant_tendsto_zero`, `riemannHypothesis_of_logarithmic_plaque_bound`.
- **PR-8J** (`Mathlib/NumberTheory/LSeries/BaezDuarteUnitPartitionKernel.lean`, `feat/baez-duarte-unit-partition-kernel`, stacked on `PR-8I`, 197 lines, max 100 chars): `sum_Icc_two_div_eq_one_of_isDirichletAnchored`, `sum_Icc_two_eq_three_of_isDirichletAnchored`, `sum_dipoleCoord_eq_one_of_isDirichletAnchored`, `unitDefectEntry`, `unitDefectEntry_comm`, `unitDefectEntry_eq_one_sub_drive_add_gram`, `unitDefectEntry_one_two_eq`, `one_sub_SCot_eq_sum_unitDefectEntry_of_isDirichletAnchored`, `sum_unitDefectEntry_nonneg_of_isDirichletAnchored`, `riemannHypothesis_of_unitDefectEntry_simplex_vanishing`.
- **PR-8K** (`Mathlib/NumberTheory/LSeries/BaezDuarteSuperdiagonalOrthogonalTriple.lean`, `feat/baez-duarte-superdiagonal-orthogonal-triple`, stacked on `PR-8J`, 188 lines, max 100 chars): `vasyuninCotSum_le_nine_fold`, `dipoleGramEntry_self_succ_eq_zero`, `dipolePlaqueEntry_self_succ_eq`, `unitDefectEntry_self_succ_eq`, `dipoleGramEntry_orthogonal_triple_two_three_four`, `QCot_span_two_three_four_eq_sum_sq`, `dipoleGramEntry_four_four_eq`, `dipoleGramEntry_three_three_add_four_four_eq`, `unitDefectEntry_one_one_add_two_two_eq`, `unitDefectEntry_three_three_add_four_four_eq`.
- **PR-8L** (`Mathlib/NumberTheory/LSeries/BaezDuartePlaqueRowTelescoping.lean`, `feat/baez-duarte-plaque-row-telescoping`, stacked on `PR-8K`, 133 lines, max 100 chars): `sum_Icc_deltaCot_diff_eq`, `sum_Icc_dipolePlaqueEntry_right_eq`, `sum_Icc_dipolePlaqueEntry_self_eq`, `sum_Icc_unitDefectEntry_right_eq`, `sum_mul_mul_eq_row_sum_sub_half_sq_sub`, `one_sub_SCot_eq_row_sum_sub_half_sq_sub_of_isDirichletAnchored`.
