# Listening to the Primes in a Tared Chamber: Wavefunctions, Schur Complements, and the Hodge–Riemann Rosetta Dictionary

**Author:** Qamar Munawer (Brandenburg University of Technology Cottbus–Senftenberg)  
**Date:** November 19, 2026  
**Honesty Boundary (`NO_RH_PROOF = TRUE`):** The asymptotic $N \to \infty$ Clay Riemann Hypothesis remains **strictly OPEN**. Every theorem and numerical check documented here is a finite-horizon or modular operator certificate in Lean 4 (`[propext, Classical.choice, Quot.sound]`, zero `sorry`).

---

## Part 1 — Listening to the Primes in a Tared Chamber (Plain-English Guide)

### 1.1 The 1-Meter Vibrating Organ Pipe
Imagine a hollow metal organ pipe of length $1$ meter, and suppose you try to build a **pure flat tone** (value `1` everywhere) using only **sawtooth echoes** whose wavelengths are unit fractions $1/1, 1/2, 1/3, 1/4, \dots, 1/N$:
- **Prime numbers ($2, 3, 5, 7, 11, \dots$)** are the **fundamental strings**—indivisible rhythms.
- **Composite numbers ($4, 6, 8, 9, 10, \dots$)** are **overtone collisions** where multiple prime rhythms meet (for instance, $6 = 2 \times 3$ is the first collision of two distinct primes).

If you clamp the front half of the pipe $(1/2, 1]$, the rigid front wall reflects a loud standing echo $|b\rangle \mathbf{1}^T$. To hear the true interior prime–composite interference, you **tare the scale**: subtract the rank-1 front-wall anchor $|b\rangle\mathbf{1}^T$ and isolate the interior fluctuation $\Psi_N$.

### 1.1b $n$ Is the Sequential Clock, $p$ Are the New Dimensions
Walking along $n = 1, 2, 3, 4, 5, 6, \dots$ is moving step-by-step through discrete time:
- Most ticks of the clock $n$ are **composites**—echoes made by multiplying earlier numbers together.
- A **prime $p$** is a tick of the clock where a **brand-new, irreducible frequency** enters the system for the first time (contributing **`89.307%`** of the Cholesky innovation sum $1 - E_{\mathrm{free}}(64)$).
- Your divisor matrix $\mathbf{D}_{M,N}$ records which earlier prime and composite rhythms divide the current clock tick $n$, while $\Sigma_M$ steps forward along the clock ($F_{M,N} = \Sigma_M \mathbf{D}_{M,N}$).
- Partitioning $Q_N$ into the Prime block ($Q_{PP}$) and Composite block ($Q_{CC}$) and taking the Schur complement $\Sigma_N = Q_{CC} - Q_{CP} Q_{PP}^{-1} Q_{PC}$ tares out the primes ($p$) from the composite clock ticks ($n$): before $n = 6$, the only composite is $n = 4 = 2^2$ (a single prime echoing on its own 1D line), so $\delta_{PC}(4) = \delta_{PC}(5) = 0.0$; at clock tick $n = 6 = 2 \times 3$, two distinct primes ($p=2$ and $p=3$) collide in time for the first time, switching on the **`15.76%`** Schur depletion (`0.157648`, climbing to `30.40%` at $N = 30 = 2 \times 3 \times 5$).

### 1.2 The 8-Row Measurement Dictionary

| Everyday Idea | Mathematical Name | Formula / Lean 4 Theorem | Observed Metric / Verification |
| :--- | :--- | :--- | :--- |
| 1. Separating counting from dividing | Additive–Multiplicative Factorization | $F_{M,N} = \Sigma_M D_{M,N}$, $D_M M_\mu = I_M$ (`MatrixFactorizationAndHalfObservation.lean`) | Exact integer inversion (`0` error) |
| 2. Taring the front pipe wall | Rank-1 Dirichlet Anchor Subtraction | $\Omega_{M,N} = \|b\rangle\mathbf{1}^T + \Psi_{M,N}$ (`dirichlet_anchor_subtraction_gram`) | $\max_j |\Omega_{0,j}| = 0.0$ on $(1/2, 1]$ |
| 3. Three independent microphone channels | Superdiagonal Orthogonal Triple | $\operatorname{diag}(G_{22}, G_{33}, G_{44})$ (`superdiagonal_triple_diagonal_gram`) | Off-diagonal cross-talk `1.223e-55` |
| 4. Why squaring blurs left from right | Squared-Hamiltonian Parity Blindness | $T_{\mathrm{pal}}^2 = I$, $P_+ T_{\mathrm{pal}}^2 P_- = 0$ (`palindromic_chirality_split_and_blindness`) | $\Pi_{\mathrm{End}^+}([T_{\mathrm{pal}}, H_\Psi]) = 0$ (`9.44e-57`) |
| 5. Half-swing camera restores direction | Spatial Half-Projector Reconstruction | $K_{\mathrm{half}} + K_{\mathrm{half}}^T = 4\,T_{\mathrm{pal}}$ (`spatial_half_projector_reconstruction`) | Exact reconstruction (`err = 0.0`) |
| 6. Subtracting prime echoes from composites | Prime–Composite Schur Complement | $\Sigma_N = Q_{CC} - Q_{CP} Q_{PP}^{-1} Q_{PC}$ (`block_schur_complement_symmetric`) | $\delta_{PC}(4,5) = 0.0 \to \delta_{PC}(6) = 0.157648$ |
| 7. Splitting leftover error into Prime minus Composite | Block-Banachiewicz Schur Distance Split | $d_N^2 = d_{N,\mathrm{Prime}}^2 - \Delta_{\mathrm{Schur}}(C \mid P)$ (`block_banachiewicz_schur_distance_split`) | Split residual `7.523e-37` |
| 8. Checking decay along the primorial ladder | Primorial BBLR Envelope & Master Bridge | $N = 2 \to 6 \to 30 \to 210$ (`RiemannMasterBBLRBridge.lean`) | $\ln(210) E_{\mathrm{dir}}(210) = 0.04748453$ (within `2.80%` of $C_{\mathrm{BBLR}} = 0.04619142$) |

---

## Part 2 — The Wavefunction Interpreted Completely in Matrices

Absorbing the slab metric $W_M = \operatorname{diag}\bigl(\frac{1}{n(n+1)}\bigr)$ into the residual vector $r_M$ defines the Euclidean **wavefunction state**
$$|\psi_M\rangle := W_M^{1/2} r_M = W_M^{1/2}\bigl(\mathbf{1}_M + \mathbf{\Sigma}_M \mathbf{D}_{M,N} c_N\bigr) \in \mathbb{R}^M, \qquad \langle\psi_M|\psi_M\rangle = r_M^T W_M r_M = E_M(c).$$

1. **Vacuum Carrier, Dipole Excitations, and Simplex Hamiltonian:**
   - **50/50 Vacuum Carrier Wave:** $|b_M\rangle := W_M^{1/2}\mathbf{b}_M$ with amplitudes $(-1)^n/\sqrt{n(n+1)}$ and norm $\langle b_M|b_M\rangle = 1 - \frac{1}{M+1} \to 1$.
   - **Augmented Overlap & Simplex Hamiltonian:**
     $$\mathcal{G}_N^{\mathrm{aug}} = \begin{pmatrix} 1 & -\pi u_N^T \\ -\pi u_N & \widetilde{G}_N \end{pmatrix}, \qquad M_N = S_N^T \mathcal{G}_N^{\mathrm{aug}} S_N = \mathbf{\Omega}_N^T \mathbf{\Omega}_N, \qquad |\psi_N(\alpha)\rangle = \mathbf{\Omega}_N\alpha.$$
   - **SVD Ground-State Wavefunction:** For $\mathbf{\Omega}_N = U\Sigma V^T$, $\lambda_r(M_N) = \sigma_r(\mathbf{\Omega}_N)^2$. The isolated ground state $|\psi_0^{\mathrm{ground}}\rangle = \mathbf{\Omega}_N v_0 / \sigma_0$ carries **`93.45%`** of $\mathbf{1}^T M_{32}^{-1}\mathbf{1}$ across an **`8x–11x`** spectral gap (`svd_ground_state_energy_ceiling_unconditional`: $E_{\mathrm{dir}}(N) \le \sigma_0^2/(v_0^T\mathbf{1})^2$).
2. **Cholesky Innovation Recursion & $N = 6$ Lorentzian Light Cone:**
   - Unconstrained vacuum projection $|\psi_{\mathrm{free}}^*(N)\rangle = (I - \widehat{\Pi}_N)|b\rangle$ gives $E_{\mathrm{free}}(N) = 1 - \sum_{k=3}^N \rho_k^2/s_k$ (`cholesky_innovation_step_monotone_descent`).
   - Splitting $E_{\mathrm{dir}}(N) = (1 - \pi u^T \alpha^*) + (\alpha^*)^T P_N \alpha^*$ (`wavefunction_augmented_simplex_lorentzian_split`, `lorentzian_timelike_plaque_strict_reduction`) transitions from spacelike at $N=4$ (`+0.0468`) into the negative timelike cone for $N \ge 6$ (`-0.01825` at $N=6$; at $N=64$, $(\alpha^*)^T P_{64}\alpha^* = -0.01435$ cancels **`55%`** of the boundary defect `+0.02614`).
3. **4-Way Spatial Probability Budget (`N = 32`) & Position–Momentum Duality:**
   - At $N = 32$ (`spatial_probability_active_tail_conservation`): **`0%`** on $(1/2, 1]$, **`51.05%`** in the active window $[2, 32]$, **`12.75%`** on tail primes $p > 32$, and **`35.41%`** on tail composites $n > 32$.
   - Under the Mellin isometry $\mathcal{M}: L^2(0, 1) \xrightarrow{\sim} H^2(\operatorname{Re}(s) > 1/2)$, $\widehat{\psi}_N(s) = \frac{1}{s}(1 + \zeta(s) D_N(s))$, so any off-line zero $s_0$ enforces $\alpha^T M_N \alpha \ge \frac{2\operatorname{Re}(s_0)-1}{\|s_0\|^2} > 0$.

---

## Part 3 — Cross-Project Rosetta Dictionary with Hodge `v1.5.0-rosetta`

Every finite-dimensional operator mechanism in `RiemannBlueprint` mirrors the "Seeing Negatively" Schur-complement architecture in **Hodge `v1.5.0-rosetta`** (`10.5281/zenodo.24381741`) and our companion physics tracks:

| Structural Duality | Hodge `v1.5.0-rosetta` (`10.5281/zenodo.24381741`) | Riemann `v3.2.0-rosetta` | Open Clay Boundary |
| :--- | :--- | :--- | :--- |
| **(i) Exact Chiral / Inverse Realization** | CM Graph Realization $2 Z_{\mathrm{CM}} = T_{\mathrm{ch}}$ (special CM point vs. generic non-CM point) | Half-Projector $K_{\mathrm{half}} + K_{\mathrm{half}}^T = 4 T_{\mathrm{pal}}$, $\mathbb{Q}(\sqrt{3})$ reciprocity at $N=6$, finite Möbius inverse $D_M M_\mu = I_M$ | Generic non-CM algebraicity $\longleftrightarrow$ $N \to \infty$ tail cancellation |
| **(ii) Syzygy / Schur Threshold** | CY4 Koszul Hilbert Subtraction `[1, 6, 21, 56, 126, 246, 426]` (`0` syzygy subtraction for $d \le 4$, turning on at $d=5,6$) | Prime–Composite Schur depletion $\delta_{PC}(N)$ (`0.000000` for $N \le 5$, jumping to `0.157648` at $N = 6 = 2 \times 3$) | Infinite syzygy / primorial limit |
| **(iii) Exact Annihilation / Orthogonality** | Finite Gysin exactness $g_* f^* = 0$ | Upper-half Dirichlet annihilation $\Pi_{(1/2, 1]}\Omega_N = 0$ and $\Pi_{\mathrm{End}^+}([T_{\mathrm{pal}}, H_\Psi]) = 0$ | Asymptotic vanishing of $(I - \widehat{\Pi}_N)\|b\rangle$ |
| **(iv) Ground-State / Chiral Collapse** | $A \to A^2 \to A^3$ (`14D -> 1D`) chiral collapse | SVD ground-state collapse (`93.45%` of $\mathbf{1}^T M_{32}^{-1}\mathbf{1}$ on $\|\psi_0^{\mathrm{ground}}\rangle$) | $\lim_{N\to\infty} \sigma_0(\Omega_N)^2 / (v_0^T\mathbf{1})^2 = 0$ |

### Companion Rosetta Releases & Zenodo DOIs
- **Hodge Conjecture (`v1.5.0-rosetta`):** `10.5281/zenodo.24381741`
- **4D Yang–Mills (`v1.1.0-rosetta`):** `10.5281/zenodo.24378644`
- **3D Navier–Stokes (`v1.0.0-rosetta`):** `10.5281/zenodo.24378625`
- **Riemann Hypothesis (`RiemannBlueprint` / `riemann-lean4-papers`):** Hub 07 `10.5281/zenodo.24381534`, Hub 13 `10.5281/zenodo.24381535`, Hub 14 `10.5281/zenodo.24381605` (updated in `v3.2.0-rosetta`).
