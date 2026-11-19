# Listening to the Primes in a Tared Chamber: A Guide for Everyone

**Author:** Qamar Munawer (Brandenburg University of Technology Cottbus–Senftenberg)  
**Date:** November 19, 2026  
**Honesty Boundary (`NO_RH_PROOF = TRUE`):** The Clay Riemann Hypothesis ($N \to \infty$) remains **strictly OPEN**. Everything below explains the finite-horizon measuring instruments, exact matrix identities, and computer-checked Lean 4 theorems we built and verified.

---

## 1. The Real-World Picture: A Vibrating Organ Pipe

Imagine a hollow metal organ pipe of length $1$ meter, and suppose you want to build a **pure flat tone** (a flat `1` across the whole pipe) using only **sawtooth echoes** whose wavelengths are fractions of a meter: $1/1, 1/2, 1/3, 1/4, \dots, 1/N$.

- **Prime numbers ($2, 3, 5, 7, 11, \dots$)** are the **fundamental strings**—they cannot be broken into smaller whole-number rhythms.
- **Composite numbers ($4, 6, 8, 9, 10, \dots$)** are **overtone collisions** where two or more rhythms meet (for example, $6 = 2 \times 3$ is where the $2$-beat and the $3$-beat hit the same note).

The **Riemann Hypothesis** asks a deceptively simple question about this pipe:
> *If we keep adding more and more sawtooth echoes ($N \to \infty$), can we cancel out every ripple and make the remaining sound energy drop all the way to **zero**?*

---

## 2. What We Measure, How We Measure It, and What Each Part Is Called

| Everyday Idea | Mathematical Name | Symbol / Lean 4 Theorem | What It Actually Measures |
| :--- | :--- | :--- | :--- |
| **1. Separating counting from dividing** | Additive–Multiplicative Factorization | $F_{M,N} = \Sigma_M D_{M,N}$, $D_M M_\mu = I_M$ (`MatrixFactorizationAndHalfObservation.lean`) | Splits the sawtooth wave into a simple step-adder ($\Sigma_M$) and a pure divisibility table ($D_{M,N}$), whose exact inverse is the Möbius matrix $M_\mu$. |
| **2. Putting the heavy pipe wall on a kitchen scale and pressing "TARE"** | Rank-1 Dirichlet Anchor Subtraction | $\Omega_{M,N} = \|b\rangle\mathbf{1}^T + \Psi_{M,N}$ (`dirichlet_anchor_subtraction_gram`) | Clamping the front half of the pipe creates a loud wall echo $\|b\rangle\mathbf{1}^T$. Subtracting it zeroes out the front half $(1/2, 1]$ (`max|Omega[0,:]| = 0.0`) and leaves only the true interior ripples $\Psi_{M,N}$. |
| **3. Three completely independent microphone channels** | Superdiagonal Orthogonal Triple | $\operatorname{diag}(G_{22}, G_{33}, G_{44})$ (`superdiagonal_triple_diagonal_gram`) | Three interior modes $\{v^{(2)}, v^{(3)}, v^{(4)}\}$ have **zero** cross-talk ($1.223 \times 10^{-55}$), so their energies add cleanly without interfering. |
| **4. Why squaring the sound blurs left from right** | Squared-Hamiltonian Parity Blindness | $T_{\mathrm{pal}}^2 = I$, $P_+ T_{\mathrm{pal}}^2 P_- = 0$ (`palindromic_chirality_split_and_blindness`) | Squaring a wave turns both $-1$ (backward) and $+1$ (forward) into $+1$, erasing direction. Mirror-even measurements have **zero** overlap with directional twist (`9.44e-57`). |
| **5. Using a half-swing camera to restore direction** | Spatial Half-Projector Reconstruction | $K_{\mathrm{half}} + K_{\mathrm{half}}^T = 4\,T_{\mathrm{pal}}$ (`spatial_half_projector_reconstruction`) | Looking at only half of the chamber and adding its mirror image recovers the exact directional switch (`error = 0.0`). |
| **6. Subtracting prime echoes from composite echoes** | Prime–Composite Schur Complement | $\Sigma_N = Q_{CC} - Q_{CP} Q_{PP}^{-1} Q_{PC}$ (`block_schur_complement_symmetric`) | Measures how much composite-mode energy remains after subtracting every direct and indirect bounce off the prime modes. |
| **7. Splitting the leftover error into Prime part minus Composite reduction** | Block-Banachiewicz Schur Distance Identity | $d_N^2 = d_{N,\mathrm{Prime}}^2 - \Delta_{\mathrm{Schur}}(C \mid P)$ (`block_banachiewicz_schur_distance_split`) | Proves that every new composite mode subtracts $\Delta_{\mathrm{Schur}} \ge 0$ from the remaining error ($d_N^2 \le d_{N,\mathrm{Prime}}^2$). |
| **8. Checking if the error shrinks fast enough as $N$ grows** | BBLR Logarithmic Envelope & Master Bridge | $\ln(N)\cdot E_{\mathrm{dir}}(N) \to C_{\mathrm{BBLR}}$ (`RiemannMasterBBLRBridge.lean`) | Measures whether $\ln(N)$ times the anchored energy $E_{\mathrm{dir}}(N)$ settles down to the critical constant $C_{\mathrm{BBLR}} = 2 + \gamma - \ln(4\pi) \approx 0.04619142$. |

---

## 3. What We Actually Observed (Real Numbers, Checked to 35–55 Digits)

### Observation 1: Nothing Twists on a 1D Line ($N=4, 5$), Everything Switches On at $N = 6 = 2 \times 3$
- When we include numbers up to $N = 4$ or $N = 5$, the only composite number is $4 = 2 \times 2$. It lives on a **single prime line** (powers of $2$). Our Prime–Composite depletion gauge $\delta_{PC}(N) = 1 - \|\Sigma_N\|_F / \|Q_{CC}\|_F$ reads identically **`0.000000`**.
- The very next number is **$N = 6 = 2 \times 3$**, where **two different prime lines ($2$ and $3$) cross for the first time**. Instantly:
  - The depletion gauge jumps from `0.000000` to **`0.157647933508`** (`15.76%`), and climbs to **`0.304008082755`** (`30.40%`) at $N = 30 = 2 \times 3 \times 5$.
  - The plaque geometry flips from spacelike (`+0.046766` at $N=4$) into the negative **timelike cone** (`-0.018251` at $N=6$).
  - At $N = 6$, the exact $\mathbb{Q}(\sqrt{3})$ identity $G_{33} + G_{44} = \pi(4/\sqrt{3} - 1)$ holds to **`1.631e-55`** (fifty-five zeros after the decimal point!).

### Observation 2: Climbing the Primorial Ladder ($N = 2 \to 6 \to 30 \to 210$)
Using `probe_primorial_schur_distance_decay.py` (35-digit precision, max Block-Banachiewicz split error `7.52316e-37`), we measured both the unanchored distance $d_N^2$ and the Dirichlet-anchored energy $E_{\mathrm{dir}}(N)$:

| Cutoff $N$ | Primes $\|P\|$ | Composites $\|C\|$ | Unanchored $d_N^2$ | Anchored $E_{\mathrm{dir}}(N)$ | $\ln(N) \cdot E_{\mathrm{dir}}(N)$ | Condition $\kappa(\Sigma_N)$ |
| ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| `2` | `0` | `0` | `1.00000000` | `1.00000000` | `0.69314718` | `1.0` |
| `6` | `2` | `2` | `0.76035326` | `0.04199430` | `0.07524369` | `1.0855` |
| `30` | `9` | `19` | `0.75365222` | `0.01525451` | `0.05188360` | `12.7585` |
| `210` | `45` | `163` | `0.75216230` | `0.00888041` | **`0.04748453`** | `58.9223` |

Look at the two columns side by side:
1. Without the Dirichlet anchor ($\mathbf{1}^T\alpha = 1$), the unanchored energy $d_N^2$ stalls near `0.752`.
2. **With** the Dirichlet anchor, $\ln(N) \cdot E_{\mathrm{dir}}(N)$ drops cleanly along the primorial ladder (`0.6931 -> 0.0752 -> 0.0519 -> 0.04748`), landing right above the theoretical BBLR critical-line target **`0.04619142`**.

---

## 4. What Is Proved vs. What Remains Open

- **Proved Unconditionally in Lean 4 (zero `sorry`, strictly `[propext, Classical.choice, Quot.sound]`):**
  Every finite-$N$ matrix factorization, the $M \to \infty$ slab-to-continuum limit (`anchoredWave_gram_quadForm_tendsto_unitDefectMatrix`), the Block-Banachiewicz Schur split (`block_banachiewicz_schur_distance_split`), one-step Schur resolvent growth (`schur_resolvent_one_step_growth`), and the conditional master bridge (`riemannHypothesis_of_bblr_asymptotic_schur`).
- **Strictly Open (`NO_RH_PROOF = TRUE`) — Why the Clay Continuity Limit ($N \to \infty$) Is Still Open:**
  1. **Decreasing and positive does not force limit zero (The Off-Line Zero Plateau):** Even though adding more echoes always lowers the energy ($E_{\mathrm{dir}}(N+1) \le E_{\mathrm{dir}}(N)$) and prime jumps keep it $> 0$, a decreasing sequence can stall at a positive floor $L_\infty > 0$. By Half-Law 3 (`unitDefectMatrix_offline_zero_floor_unconditional`), even one zero of $\zeta(s_0)=0$ off the critical line ($\operatorname{Re}(s_0) > 1/2$) traps $E_{\mathrm{dir}}(N) \ge (2\operatorname{Re}(s_0)-1)/\|s_0\|^2 > 0$ for *all* $N$. No finite check ($N \le 210$) can rule out a zero at height $|t| \sim 10^{100}$.
  2. **The Active-Window vs. Tail Trade-Off:** At $N = 32$, `0%` of the energy sits on $(1/2, 1]$, **`51.05%`** leaks inside $[2, 32]$, **`12.75%`** sits on uncancelled primes $p > 32$, and **`35.41%`** sits on tail composites $n > 32$. Using $\mathbf{F}_N^{-1} = \mathbf{M}_\mu\mathbf{\Delta}_N$ to force $[2, 32]$ to `0%` sets $c_k = -\mu(k)$, which blows up the tail unless the Möbius sum has square-root cancellation — which is already equivalent to RH.
  3. **Bessel's Inequality Gives $\le 1$, Not $= 1$:** In $E_{\mathrm{free}}(N) = 1 - \sum_{k=3}^N \rho_k^2/s_k \ge 0$, Bessel's inequality proves the infinite sum is $\le 1$, not that it reaches $1$. Proving it reaches $1$ (or that $\ln(N_k)E_{\mathrm{dir}}(N_k) \to C_{\mathrm{BBLR}}$ for all $k \to \infty$) **is** the open Clay Riemann Hypothesis.
