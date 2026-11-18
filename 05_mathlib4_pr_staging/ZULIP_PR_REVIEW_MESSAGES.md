# Lean Zulip `#PR-reviews` Human Reference Notes (Qamar Munawer)

> **AI Policy Reminder (`mathlib4`):** Upstream `mathlib4` policy strictly forbids pasting LLM-generated comments into GitHub PRs or Zulip, and requires human-written communication plus explicit AI-tool disclosure in PR descriptions. Use this file strictly as a local reference index; write every GitHub or Zulip message yourself.

All PRs extract small, self-contained modules (`<= 250` lines for Waves 5-8, `<= 100` chars/line, `#lint` `0` errors across 15 linters, strictly `[propext, Classical.choice, Quot.sound]`, `NO_RH_PROOF = TRUE`).

## 1. Wave 1 Historical Reference (`#46127`–`#46129`)

- `#46127` `feat/critical-line-zeros` (`PR-1A`)
- `#46128` `feat/vasyunin-integral` (`PR-3A`)
- `#46129` `feat/baez-duarte-projection` (`PR-4A`)

## 2. Independent Root PRs Staged on Own Fork (`Qamarbajwa/mathlib4`)

- `PR-1C` (`feat/zeta-remainder-series` -> `Mathlib/NumberTheory/LSeries/ZetaRemainderSeries.lean`): Euler-Maclaurin remainder series and analyticity of zeta on Re(s) > 0
- `PR-3D` (`feat/vasyunin-stirling-asymp` -> `Mathlib/NumberTheory/LSeries/VasyuninStirlingAsymp.lean`): dilated Stirling, Euler-Mascheroni, and divisor quotient identities
- `PR-2B` (`feat/hardy-psi-kernel` -> `Mathlib/NumberTheory/LSeries/HardyPsiKernel.lean`): Hardy theta-remainder kernel hardyPsi strip holomorphicity and Gaussian decay
- `PR-5A` (`feat/zeta-inv-holomorphy` -> `Mathlib/NumberTheory/LSeries/ZetaInvHolomorphy.lean`): analyticity of zeta inverse and log-derivative equivalence for RiemannHypothesis
- `PR-6A` (`feat/completed-zeta-deriv-symmetry` -> `Mathlib/NumberTheory/LSeries/CompletedZetaDerivSymmetry.lean`): completed zeta derivative antisymmetry, equipartition fulcrum, and zero dichotomy
- `PR-6C` (`feat/prime-composite-dirichlet-split` -> `Mathlib/NumberTheory/LSeries/PrimeCompositeDirichletSplit.lean`): natural prime-composite partition and critical-strip RH equivalence
- `PR-7A` (`feat/mellin-kernel-energy-identity` -> `Mathlib/NumberTheory/LSeries/MellinKernelEnergy.lean`): Mellin weight kernel L2 energy identity and weighted Cauchy-Schwarz bound
- `PR-7B` (`feat/rectangle-contour-subdivision` -> `Mathlib/Analysis/Complex/RectangleContourSubdivision.lean`): 4-segment oriented rectangle boundary integral and edge subdivisions
