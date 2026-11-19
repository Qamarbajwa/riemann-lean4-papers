# Matrix Relations and Half-Observation Laws of the Riemann Zeta / Báez–Duarte System

This document transcribes the full analytic–arithmetic–Hilbert-space structure of the Báez–Duarte / Vasyunin / Riemann Zeta framework into explicit matrix relations and documents the three structural **half-observation laws** connecting additive harmonic slabs, multiplicative divisibility, palindromic period folding, and the critical strip. Every algebraic, measure-theoretic, and spectral theorem below is machine-verified in [`MatrixFactorizationAndHalfObservation.lean`](https://github.com/Qamarbajwa/RiemannBlueprint/blob/main/RiemannBlueprint/MatrixFactorizationAndHalfObservation.lean) (Lean `v4.35.0`, zero `sorry`, strictly standard axioms `[propext, Classical.choice, Quot.sound]`) and cross-checked at 55-digit precision in [`verify_matrix_half_observation.py`](./verify_matrix_half_observation.py).

---

## 1. Master Matrix Transcription Map

| Analytic / Arithmetic Object | Matrix / Vector Symbol | Shape | Explicit Definition |
| :--- | :---: | :---: | :--- |
| Lower-triangular summation operator | $\mathbf{\Sigma}_M$ | $M \times M$ | $(\mathbf{\Sigma}_M)_{i,m} = \mathbf{1}_{m \le i}$ ($0$-indexed) |
| Backward first-difference operator | $\mathbf{\Delta}_M$ | $M \times M$ | $(\mathbf{\Delta}_M)_{i,m} = \delta_{i,m} - \delta_{i,m+1}$ |
| Multiplicative divisibility incidence | $\mathbf{D}_{M,N}$ | $M \times N$ | $(\mathbf{D}_{M,N})_{m,j} = \mathbf{1}_{(j+1) \mid (m+1)}$ |
| Möbius divisor-inversion matrix | $\mathbf{M}_{\mu,M}$ | $M \times M$ | $(\mathbf{M}_{\mu,M})_{i,m} = \mu\!\left(\frac{i+1}{m+1}\right)\mathbf{1}_{(m+1)\mid(i+1)}$ |
| Integer-floor quotient matrix | $\mathbf{F}_{M,N}$ | $M \times N$ | $(\mathbf{F}_{M,N})_{i,j} = \lfloor (i+1)/(j+1) \rfloor$ |
| Harmonic slab-width metric | $W_M$ | $M \times M$ | Diagonal: $(W_M)_{i,i} = \frac{1}{(i+1)(i+2)}$ |
| Three-matrix quadrature core | $Q_M$ | $N \times N$ | $Q_M = \mathbf{D}_{M,N}^T (\mathbf{\Sigma}_M^T W_M \mathbf{\Sigma}_M) \mathbf{D}_{M,N}$ |
| Discrete cell residual vector | $r_M$ | $M \times 1$ | $r_M = \mathbf{1}_M + \mathbf{\Sigma}_M \mathbf{D}_{M,N} c_N$ |
| Anti-diagonal reversal involution | $J_H$ | $H \times H$ | $(J_H)_{i,j} = \mathbf{1}_{i+j+1 = H}$ ($J_H^T = J_H$, $J_H^2 = I_H$) |
| Half-folded double-cone weights | $\overline{W}_{\mathrm{half}}$ | $H \times H$ | $\frac{1}{2}(W_L + J_H W_R J_H)$ on $[1, H]$, $L = 2H + 2$ |
| Cumulative-dipole Gram matrix | $\widetilde{G}_N$ | $(N{-}2)\times(N{-}2)$ | $(\widetilde{G}_N)_{a-1,b-1} = \mathrm{dipoleGramEntry}(a, b)$ |
| Pure 4-point plaque matrix | $P_N$ | $(N{-}2)\times(N{-}2)$ | $(P_N)_{a-1,b-1} = \mathrm{dipolePlaqueEntry}(a, b)$ |
| Unit-defect simplex matrix | $M_N$ | $(N{-}2)\times(N{-}2)$ | $(M_N)_{a-1,b-1} = \mathrm{unitDefectEntry}(a, b)$ |
| Boundary cotangent contrast vector | $u_N$ | $(N{-}2)\times 1$ | $(u_N)_{m-1} = \delta(m+2) - \delta(m+1)$ |
| Dirichlet simplex coordinate | $\alpha_N$ | $(N{-}2)\times 1$ | $\alpha_{m-1} = \sum_{k=m+2}^N c_k / k$, $\mathbf{1}^T \alpha_N = 1$ |

---

## 2. Additive–Multiplicative Factorization & Exact Two-Step Inversion

Counting multiples of $k = j+1$ up to $n = i+1$ decouples the multiplicative divisibility condition $(j+1) \mid (m+1)$ from additive accumulation $\sum_{m=1}^n$:

$$\mathbf{F}_{M,N} = \mathbf{\Sigma}_M \mathbf{D}_{M,N}, \qquad \bigl\lfloor \tfrac{n}{k} \bigr\rfloor = \sum_{m=1}^{n} \mathbf{1}_{k \mid m}.$$

Because the two factors inhabit the additive group (discrete calculus) and the multiplicative semigroup (Dirichlet convolution), each possesses an exact triangular left/right inverse:

$$\mathbf{\Delta}_M \mathbf{\Sigma}_M = I_M, \qquad \mathbf{M}_{\mu,M} \mathbf{D}_{M,M} = I_M.$$

Composing these inverses in reversed order inverts $\mathbf{F}_{M,M} = \mathbf{\Sigma}_M \mathbf{D}_{M,M}$ explicitly without floating-point arithmetic:

$$(\mathbf{M}_{\mu,M} \mathbf{\Delta}_M)\, \mathbf{F}_{M,M} = \mathbf{M}_{\mu,M} (\mathbf{\Delta}_M \mathbf{\Sigma}_M) \mathbf{D}_{M,M} = \mathbf{M}_{\mu,M} \mathbf{D}_{M,M} = I_M.$$

Hence, solving $\mathbf{F}_{M,M} c = y$ cleanly separates into an **additive** first-difference step followed by a **multiplicative** Möbius convolution: $c = \mathbf{M}_{\mu,M}(\mathbf{\Delta}_M y)$.

---

## 3. Three-Matrix Sandwich Energy Form & Harmonic Tail Exhaustion

On every truncation hyperplane $D_1(c, N) = \sum_{k=1}^N c_k / k = 0$, the continuous Báez–Duarte residual $r(x) = 1 - \sum_{k=1}^N c_k \{1/(kx)\}$ is piecewise constant on each harmonic slab $x \in \bigl(\frac{1}{n+1}, \frac{1}{n}\bigr]$ of width $w_n = \frac{1}{n(n+1)}$ with constant value $(r_M)_n = 1 + \sum_{k=1}^N c_k \lfloor n/k \rfloor$:

$$r_M = \mathbf{1}_M + (\mathbf{\Sigma}_M \mathbf{D}_{M,N}) c_N.$$

Summing over slabs $1 \le n \le M$ turns the $L^2\bigl(\frac{1}{M+1}, 1\bigr]$ Lebesgue integral into a three-matrix quadratic sandwich:

$$\int_{1/(M+1)}^{1} r(x)^2\,dx = r_M^T W_M r_M = \mathbf{1}_M^T W_M \mathbf{1}_M + 2 (\mathbf{1}_M^T W_M \mathbf{\Sigma}_M \mathbf{D}_{M,N}) c_N + c_N^T Q_M c_N,$$

where the quadratic core splits as:

$$Q_M = \mathbf{D}_{M,N}^T \bigl(\mathbf{\Sigma}_M^T W_M \mathbf{\Sigma}_M\bigr) \mathbf{D}_{M,N}.$$

Here the inner symmetric core $\mathbf{\Sigma}_M^T W_M \mathbf{\Sigma}_M$ carries pure additive geometry (cumulative harmonic tails $(\mathbf{\Sigma}_M^T W_M \mathbf{\Sigma}_M)_{a,b} = \frac{1}{\max(a,b)+1}$ shifted appropriately), while the outer $\mathbf{D}_{M,N}^T (\cdot) \mathbf{D}_{M,N}$ projects multiplicatively. By telescoping the harmonic slab widths $\sum_{n=M+1}^{M'} \frac{1}{n(n+1)} = \frac{1}{M+1} - \frac{1}{M'+1}$, Euclidean Book X.1 exhaustion gives an explicit quantitative approximation error:

$$0 \le r_{M'}^T W_{M'} r_{M'} - r_M^T W_M r_M \le \frac{B(c, N)^2}{M + 1}, \qquad B(c, N) = 1 + \sum_{k=1}^N |c_k|.$$

---

## 4. The Three Half-Observation Laws

Across the system, treating one-half of a two-sided symmetric structure as the active observation window appears in three distinct, mathematically exact forms:

### Half-Law 1 — Spatial Upper-Half Annihilation on $(0, 1/2]$
Under Dirichlet anchoring $c_1 = -1$ ($N \ge 2$) alongside $D_1(c, N) = 0$:
$$A_c(1) = 1 + c_1 = 0 \implies \int_{1/2}^{1} r(x)^2\,dx = 0, \qquad \int_{0}^{1} r(x)^2\,dx = \int_{0}^{1/2} r(x)^2\,dx.$$
Every Dirichlet-anchored residual is identically zero on $(1/2, 1]$; the entire observable $L^2$ defect lives inside $(0, 1/2]$.

### Half-Law 2 — Palindromic Half-Period Matrix Folding on $[1, H]$
For any period $L = 2H + 2$ divisible by $1, \dots, N$ and any vector $c$ in the affine manifold $A_N$ ($D_1 = 0$, $D_0 = 2$), reflecting cell indices $m \leftrightarrow L - 1 - m$ pairs the left half $a_L \in \mathbb{R}^H$ ($m \in \{1, \dots, H\}$) with the right half $a_R \in \mathbb{R}^H$ ($m \in \{H+1, \dots, 2H\}$) by exact anti-diagonal reversal involution $J_H$:

$$a_R = -J_H a_L, \qquad J_H^T = J_H, \qquad J_H^2 = I_H.$$

Because $a_R^T W_R a_R = (-J_H a_L)^T W_R (-J_H a_L) = a_L^T (J_H W_R J_H) a_L$, the full interior period energy collapses onto the half-dimensional vector $a_L \in \mathbb{R}^H$ with double amplitude and symmetrized double-cone weights $\overline{W}_{\mathrm{half}} = \frac{1}{2}(W_L + J_H W_R J_H)$:

$$E_{[1, L-2]} = a_L^T W_L a_L + a_R^T W_R a_R = 2\, a_L^T \overline{W}_{\mathrm{half}} a_L, \qquad \overline{W}_{\mathrm{half}} = \operatorname{diag}_{1 \le m \le H}\!\left(\frac{w_m + w_{L-1-m}}{2}\right).$$

### Half-Law 3 — Spectral Right Half-Plane $\operatorname{Re}(s) > 1/2$ Mellin Observational Limit
Under the unconditional Mellin–Plancherel bridge (`titchmarshMellinProperty_unconditional`), $L^2(0, 1)$ corresponds unitarily to the Hardy space $H^2(\operatorname{Re}(s) > 1/2)$ — observing strictly the right half of the critical strip symmetric under $\xi(s) = \xi(1-s)$ around $\operatorname{Re}(s) = 1/2$:

$$\mathcal{M}[r](s) = \frac{1}{s}\!\left(1 - \zeta(s) \sum_{k=1}^N \frac{c_k}{k^s}\right), \qquad \operatorname{Re}(s) > \tfrac{1}{2}.$$

If any zero $s_0$ lies off the critical line ($\operatorname{Re}(s_0) \ne 1/2$), reflection $s_0 \mapsto 1 - s_0$ places a representative strictly in $1/2 < \operatorname{Re}(s_0) < 1$, forcing a uniform positive matrix floor across every finite truncation $N \ge 2$ and every $\alpha \in \mathbb{R}^{N-2}$ with $\mathbf{1}^T \alpha = 1$:

$$\frac{2\operatorname{Re}(s_0) - 1}{\|s_0\|^2} \le \alpha^T M_N \alpha.$$

---

## 5. Core $(N-2)\times(N-2)$ Matrices & Exact Finite-$N$ Closed-Form Solution

In the cumulative harmonic dipole coordinates $\alpha \in \mathbb{R}^{N-2}$ ($\mathbf{1}^T \alpha = 1$), the ambient $L^2(0,1)$ inner product and cotangent boundary geometry condense into three symmetric $(N-2)\times(N-2)$ matrices linked by exact Rank-2 boundary shifts $\frac{\pi}{2}(u_N \mathbf{1}^T + \mathbf{1} u_N^T)$:

$$\widetilde{G}_N = P_N + \frac{\pi}{2}\bigl(u_N \mathbf{1}^T + \mathbf{1} u_N^T\bigr),$$

$$M_N = \mathbf{1}\mathbf{1}^T - \frac{\pi}{2}\bigl(u_N \mathbf{1}^T + \mathbf{1} u_N^T\bigr) + P_N = \mathbf{1}\mathbf{1}^T - \pi\bigl(u_N \mathbf{1}^T + \mathbf{1} u_N^T\bigr) + \widetilde{G}_N.$$

Key structural properties established formally and verified to 55 decimal digits:
1. **Universal Superdiagonal Orthogonality & Exact Zeros:** $(\widetilde{G}_N)_{m, m+1} = 0$ identically for all $m \ge 1$ (`dipoleGramMatrix_superdiag_eq_zero`), accompanied by the isolated non-superdiagonal exact orthogonality zeros $\widetilde{G}_{2,4} = \widetilde{G}_{2,7} = \widetilde{G}_{4,8} = 0$.
2. **Lorentzian Plaque Signature:** Stripping the Rank-2 boundary term from positive-definite $\widetilde{G}_N$ reveals that $P_N$ has exact **Lorentzian signature $(N - 3, 1)$** (one single negative eigenvalue $\lambda_{\min}(P_N) < 0$ and $N - 3$ strictly positive eigenvalues) for all verified $N \in [4, 64]$.
3. **Closed-Form Finite-$N$ Simplex Solution:** Because $M_N \succ 0$ for every tested finite $N$, constrained minimization on $\mathbf{1}^T \alpha = 1$ yields the unique exact Lagrange-multiplier solution:

$$\alpha^*(N) = \frac{M_N^{-1}\mathbf{1}}{\mathbf{1}^T M_N^{-1}\mathbf{1}}, \qquad E_{\mathrm{dir}}(N) := \min_{\mathbf{1}^T \alpha = 1} \alpha^T M_N \alpha = \frac{1}{\mathbf{1}^T M_N^{-1}\mathbf{1}}.$$

### Certified 55-Digit Numerical Summary (`verify_matrix_half_observation.py`)

| $N$ | $\dim$ | $\mathrm{sig}(P_N)$ | $\mathrm{sig}(\widetilde{G}_N)$ | $\mathrm{sig}(M_N)$ | $E_{\mathrm{dir}}(N) = (\mathbf{1}^T M_N^{-1}\mathbf{1})^{-1}$ | Prime Floor $\sum_{N<p\le 500}\frac{1}{2p^2}$ | Spectral Notes ($N \le 24$) |
|---:|---:|:---:|:---:|:---:|---:|---:|:---|
| 4 | 2 | $(1, 1)$ | $(2, 0)$ | $(2, 0)$ | `0.098246553136263` | `0.045431540243389` | $\kappa(\widetilde{G})=1.366$, $\kappa(M)=10.868$, $\lambda_{\min}(P)=-0.020541$ |
| 6 | 4 | $(3, 1)$ | $(4, 0)$ | $(4, 0)$ | `0.041994304130576` | `0.025431540243389` | $\kappa(\widetilde{G})=5.045$, $\kappa(M)=23.486$, $\lambda_{\min}(P)=-0.39202$ |
| 8 | 6 | $(5, 1)$ | $(6, 0)$ | $(6, 0)$ | `0.025907917612582` | `0.015227458610736` | $\kappa(\widetilde{G})=8.644$, $\kappa(M)=41.584$, $\lambda_{\min}(P)=-0.61956$ |
| 12 | 10 | $(9, 1)$ | $(10, 0)$ | $(10, 0)$ | `0.021616141557402` | `0.011095227205777` | $\kappa(\widetilde{G})=16.92$, $\kappa(M)=62.871$, $\lambda_{\min}(P)=-0.98654$ |
| 16 | 14 | $(13, 1)$ | $(14, 0)$ | $(14, 0)$ | `0.018832781170209` | `0.0081366473241201` | $\kappa(\widetilde{G})=23.55$, $\kappa(M)=91.566$, $\lambda_{\min}(P)=-1.2857$ |
| 24 | 22 | $(21, 1)$ | $(22, 0)$ | $(22, 0)$ | `0.016311974208946` | `0.0040763223825242` | $\kappa(\widetilde{G})=40.85$, $\kappa(M)=143.39$, $\lambda_{\min}(P)=-1.7521$ |
| 32 | 30 | $(29, 1)$ | $(30, 0)$ | $(30, 0)$ | `0.014680930075611` | `0.0029615006983145` | $LDL^T$ inertia verified to $10^{-35}$ |
| 48 | 46 | $(45, 1)$ | $(46, 0)$ | $(46, 0)$ | `0.012317019335402` | `0.0018020653999835` | $LDL^T$ inertia verified to $10^{-35}$ |
| 64 | 62 | $(61, 1)$ | $(62, 0)$ | $(62, 0)$ | `0.011786622915149` | `0.0013460567455123` | $LDL^T$ inertia verified to $10^{-35}$ |

---

## 6. Lean 4 Concordance & Exact Mathematical Boundary

### Lean 4 Theorem Concordance (`RiemannBlueprint.MatrixHalfObservation`)

| Mathematical Statement | Formalized Lean 4 Theorem / Definition |
| :--- | :--- |
| $\mathbf{F}_{M,N} = \mathbf{\Sigma}_M \mathbf{D}_{M,N}$ | `floorMatrix_eq_cumSum_mul_divisor` |
| $\mathbf{\Delta}_M \mathbf{\Sigma}_M = I_M$ | `firstDiffMatrix_mul_cumSumMatrix` |
| $\mathbf{M}_{\mu,M} \mathbf{D}_{M,M} = I_M$ | `mobiusMatrix_mul_divisorMatrix` |
| $(\mathbf{M}_{\mu,M} \mathbf{\Delta}_M)\mathbf{F}_{M,M} = I_M$ | `inverse_floorMatrix_mul` |
| $r_M = \mathbf{1}_M + (\mathbf{\Sigma}_M \mathbf{D}_{M,N}) c_N$ | `residualVec_eq_ones_add_factorized` |
| $\int_{1/(M+1)}^1 r(x)^2\,dx = r_M^T W_M r_M$ | `setIntegral_Ioc_eq_matrix_quadForm` |
| Tail exhaustion $\le B^2/(M+1)$ | `matrix_quadForm_tail_bound` |
| Spatial half collapse to $(0, 1/2]$ | `upperHalf_observation_zero` |
| Abstract reversal folding ($J^2 = I$) | `halfObservation_quadForm_eq_double_half` |
| Period $[1, 2H]$ folding onto $2\,a_L^T \overline{W}_{\mathrm{half}} a_L$ | `harmonicCellL2PartialSum_period_eq_double_halfObservation` |
| Rank-2 shifts ($\widetilde{G}_N, P_N, M_N$) | `dipoleGramMatrix_eq_purePlaque_add_boundary`, `unitDefectMatrix_eq_rankOne_sub_boundary_add_plaque` |
| Superdiagonal zeros $(\widetilde{G}_N)_{i, i+1} = 0$ | `dipoleGramMatrix_superdiag_eq_zero` |
| Simplex form $1 - S_{\mathrm{cot}} = \alpha^T M_N \alpha \ge 0$ | `one_sub_SCot_eq_unitDefectMatrix_quadForm`, `unitDefectMatrix_quadForm_nonneg_of_simplex` |
| Unconditional off-line zero floor | `unitDefectMatrix_offline_zero_floor_unconditional` |
| Matrix-simplex RH equivalence | `riemannHypothesis_of_unitDefectMatrix_vanishing_unconditional` |

### Exact Mathematical Boundary (Finite-$N$ Floor vs. Asymptotic Limit)
For every **fixed** truncation $N \ge 2$, the prime-jump lower bound `sum_primes_le_integral_Ioc` guarantees a strictly positive prime floor:

$$E_{\mathrm{dir}}(N) = \frac{1}{\mathbf{1}^T M_N^{-1} \mathbf{1}} \ge \sum_{p > N} \frac{1}{2p^2} > 0,$$

so $E_{\mathrm{dir}}(N)$ can never vanish at any finite $N$. By `riemannHypothesis_of_unitDefectMatrix_vanishing_unconditional`, the **open** Riemann Hypothesis is equivalent to the asymptotic divergence of the total resolvent sum across all dimensions:

$$\text{RH} \iff \lim_{N \to \infty} E_{\mathrm{dir}}(N) = 0 \iff \lim_{N \to \infty} \mathbf{1}^T M_N^{-1}\mathbf{1} = +\infty.$$
