# Lean Zulip `#PR-reviews` Review Packet (Qamar Munawer)

All PRs extract small, self-contained modules (`<= 250` lines for Waves 5-7, `<= 100` chars/line, `#lint` `0` errors across 15 linters, strictly `[propext, Classical.choice, Quot.sound]`, `NO_RH_PROOF = TRUE`).

## 1. Ready Message for Currently Open Wave 1 PRs (`#46127`–`#46129`)

```markdown
Hi! Sharing three small, self-contained NumberTheory/LSeries PRs ready for initial review (all green CI, `0` `#lint` errors, `LLM-generated` disclosed):

- [#46127](https://github.com/leanprover-community/mathlib4/pull/46127) `feat/critical-line-zeros` — `13/13` CI checks green, zero warnings, axiom-clean.
- [#46128](https://github.com/leanprover-community/mathlib4/pull/46128) `feat/vasyunin-integral` — `13/13` CI checks green, zero warnings, axiom-clean.
- [#46129](https://github.com/leanprover-community/mathlib4/pull/46129) `feat/baez-duarte-projection` — `13/13` CI checks green, zero warnings, axiom-clean.

Each module is 131-250 lines with zero custom axioms. Any review feedback is very welcome!
```

## 2. Independent Root PRs Queued Once Wave 1 Advances (`max_concurrent <= 4`)

- `PR-1C` (`feat/zeta-remainder-series` -> `Mathlib/NumberTheory/LSeries/ZetaRemainderSeries.lean`): feat(NumberTheory/LSeries): Euler-Maclaurin remainder series and analyticity of zeta on Re(s) > 0
- `PR-3D` (`feat/vasyunin-stirling-asymp` -> `Mathlib/NumberTheory/LSeries/VasyuninStirlingAsymp.lean`): feat(NumberTheory/LSeries): dilated Stirling, Euler-Mascheroni, and divisor quotient identities
- `PR-2B` (`feat/hardy-psi-kernel` -> `Mathlib/NumberTheory/LSeries/HardyPsiKernel.lean`): feat(NumberTheory/LSeries): Hardy theta-remainder kernel hardyPsi strip holomorphicity and Gaussian decay
- `PR-5A` (`feat/zeta-inv-holomorphy` -> `Mathlib/NumberTheory/LSeries/ZetaInvHolomorphy.lean`): feat(NumberTheory/LSeries): analyticity of zeta inverse and log-derivative equivalence for RiemannHypothesis
- `PR-6A` (`feat/completed-zeta-deriv-symmetry` -> `Mathlib/NumberTheory/LSeries/CompletedZetaDerivSymmetry.lean`): feat(NumberTheory/LSeries): completed zeta derivative antisymmetry, equipartition fulcrum, and zero dichotomy
- `PR-6C` (`feat/prime-composite-dirichlet-split` -> `Mathlib/NumberTheory/LSeries/PrimeCompositeDirichletSplit.lean`): feat(NumberTheory/LSeries): natural prime-composite partition and critical-strip RH equivalence
- `PR-7A` (`feat/mellin-kernel-energy-identity` -> `Mathlib/NumberTheory/LSeries/MellinKernelEnergy.lean`): feat(NumberTheory/LSeries): Mellin weight kernel L2 energy identity and weighted Cauchy-Schwarz bound
- `PR-7B` (`feat/rectangle-contour-subdivision` -> `Mathlib/Analysis/Complex/RectangleContourSubdivision.lean`): feat(Analysis/Complex): 4-segment oriented rectangle boundary integral and edge subdivisions
