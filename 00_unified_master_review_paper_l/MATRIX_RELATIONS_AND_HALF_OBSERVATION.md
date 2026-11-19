# Identity-Matrix Gaussian Elimination, Wavefunction Gram Operators, and Projection Residuals

**Lean 4 Formalization:** [`RiemannBlueprint/RiemannBlueprint/MatrixFactorizationAndHalfObservation.lean`](./RiemannBlueprint/RiemannBlueprint/MatrixFactorizationAndHalfObservation.lean)  
**55-Digit Verifier:** [`verify_matrix_half_observation.py`](./verify_matrix_half_observation.py)  
**Lean Axioms:** Strictly `[propext, Classical.choice, Quot.sound]` (`0` `sorry`, `0` `axiom`, `0` `opaque`)

---

## 1. Gaussian Elimination of the Divisibility Matrix to the Identity Matrix ($\mathbf{D}_N \mathbf{D}_N^{-1} = \mathbf{I}_N$)

Let $\mathbf{D}_N \in \mathbb{R}^{N \times N}$ be the unit lower-triangular divisibility matrix
$$(\mathbf{D}_N)_{n,k} = \begin{cases} 1, & k \mid n, \\ 0, & \text{otherwise}, \end{cases} \qquad (1 \le n, k \le N),$$
whose diagonal entries $(\mathbf{D}_N)_{n,n} = 1$ match the Identity Matrix $\mathbf{I}_N$. Its exact two-sided inverse is the Dirichlet–Möbius matrix $(\mathbf{D}_N^{-1})_{n,k} = \mu(n/k)$ if $k \mid n$ and $0$ otherwise:
$$\mathbf{D}_N \mathbf{D}_N^{-1} = \mathbf{I}_N \qquad \text{and} \qquad \mathbf{D}_N^{-1} \mathbf{D}_N = \mathbf{I}_N.$$
(`divisorMatrix_mul_mobiusMatrix`, `mobiusMatrix_mul_divisorMatrix`).

In particular, the Möbius vector $\mu = (\mu(1), \dots, \mu(N))^T$ is the unique forward-elimination solution to the first-column Identity Matrix equation
$$\mathbf{D}_N \mu = e_1 = (1, 0, \dots, 0)^T \qquad (\texttt{divisorMatrix\_mulVec\_mobius\_eq\_e1}):$$
row $n = 1$ fixes $\mu(1) = 1$, and every higher row $n \ge 2$ clears the off-diagonal divisor sum $\sum_{k \mid n} \mu(k) = 0$ to the zero entry of $\mathbf{I}_N$, matching the Dirichlet series identity $\zeta(s) \cdot \zeta(s)^{-1} = 1$.

---

## 2. Unit Lower-Triangular Factorization of the Floor Matrix ($\mathbf{F}_N = \mathbf{\Sigma}_N \mathbf{D}_N$, $\mathbf{F}_N \mathbf{F}_N^{-1} = \mathbf{I}_N$)

On each harmonic interval $x \in \bigl(\frac{1}{n+1}, \frac{1}{n}\bigr]$ where $\lfloor 1/(kx) \rfloor = \lfloor n/k \rfloor$, the Nyman–Beurling residual vector $r_M = (r_M(1), \dots, r_M(M))^T$ under the zero-slope constraint $D_1(c, N) = \sum_{k=1}^N c_k = 0$ is governed by the floor matrix $(\mathbf{F}_{M,N})_{n,k} = \lfloor n/k \rfloor$:
$$\mathbf{F}_{M,N} = \mathbf{\Sigma}_M \mathbf{D}_{M,N}, \qquad r_M = \mathbf{1}_M + (\mathbf{\Sigma}_M \mathbf{D}_{M,N}) c_N,$$
where $(\mathbf{\Sigma}_M)_{n,m} = \mathbf{1}_{m \le n}$ is the unit lower-triangular accumulation matrix and $\mathbf{\Sigma}_M^{-1} = \mathbf{\Delta}_M = \mathbf{I}_M - \mathbf{S}_M$ is the unit backward-difference matrix (`cumSumMatrix_mul_firstDiffMatrix`, `firstDiffMatrix_mul_cumSumMatrix`). Consequently, the square floor matrix $\mathbf{F}_M$ has exact two-sided inverse $\mathbf{F}_M^{-1} = \mathbf{D}_M^{-1} \mathbf{\Sigma}_M^{-1}$:
$$\mathbf{F}_M \mathbf{F}_M^{-1} = \mathbf{I}_M \qquad \text{and} \qquad \mathbf{F}_M^{-1} \mathbf{F}_M = \mathbf{I}_M$$
(`floorMatrix_mul_inverse`, `inverse_floorMatrix_mul`).

### Pivot-Row Elimination on $x \in (1/2, 1]$
Row $n = 1$ of $\mathbf{F}_{M,N}$ equals the first row $(1, 0, \dots, 0)$ of $\mathbf{I}_N$ (`floorMatrix_firstRow_eq_e1`). Therefore, locking $c_1 = -1$ eliminates the first coordinate $r_1 = 1 + (\mathbf{F}_{M,N} c_N)_1 = 0$ (`pivot_row_elimination_upperHalf_zero`), forcing the continuous residual to vanish identically on $(1/2, 1]$ (`upperHalf_observation_zero`).

---

## 3. Nullspace Basis $T_{N,N-2}$, Wavefunction Gram Operator $M_N = \mathbf{\Omega}_N^T \mathbf{\Omega}_N$, and Cholesky Whitening to $\mathbf{I}_{N-2}$

The Báez–Duarte affine constraints $D_1(c, N) = 0$ and $D_0(c, N) = 2$ with $c_1 = -1$ parameterize every anchored candidate via a $(N-2)$-dimensional simplex coordinate $\alpha \in \mathbb{R}^{N-2}$ ($\mathbf{1}^T \alpha = 1$) and nullspace basis matrix $T_{N, N-2}$:
- **Wavefunction Matrix & Spatial Annihilation:** With the slab-weighted basis $\mathbf{\Omega}_{M,N} = |b_M\rangle \mathbf{1}_{N-2}^T + \mathbf{\Psi}_{M,N}$, row $1$ vanishes identically ($\Pi_{(1/2,1]} \mathbf{\Omega}_{M,N} = 0$, `anchoredWaveMatrix_topRow_zero`), and the $L^2$-truncated energy factors as the Gram form
  $$\alpha^T (\mathbf{\Omega}_{M,N}^T \mathbf{\Omega}_{M,N}) \alpha = \|\mathbf{\Omega}_{M,N} \alpha\|_2^2 \ge 0$$
  (`anchoredWave_gram_quadForm_eq_norm_sq`, `anchoredWave_gram_quadForm_nonneg`).
- **Variational Inverse-Quadratic Identity:** For any symmetric matrix $M$ with $Mw = \mathbf{1}$ ($\mathbf{1}^T w \neq 0$) and $\mathbf{1}^T \alpha = 1$,
  $$\alpha^T M \alpha = \frac{1}{\mathbf{1}^T w} + (\alpha - \alpha^*)^T M (\alpha - \alpha^*) \ge \frac{1}{\mathbf{1}^T w}, \qquad \alpha^* = \frac{w}{\mathbf{1}^T w}$$
  (`variational_inverse_quadForm_identity`, `variational_inverse_quadForm_ge`).
- **Cholesky Whitening to the Identity Matrix $\mathbf{I}_{N-2}$:** Given $\widetilde{G}_N = \mathbf{\Psi}_N^T \mathbf{\Psi}_N = L_N L_N^T$ and $W_N L_N = \mathbf{I}_{N-2}$, the whitened basis $\widetilde{\mathbf{\Psi}}_N = \mathbf{\Psi}_N W_N^T$ has the exact Identity Matrix as its Gram matrix:
  $$\widetilde{\mathbf{\Psi}}_N^T \widetilde{\mathbf{\Psi}}_N = \mathbf{I}_{N-2} \qquad (\texttt{choleskyWhitening\_gram\_eq\_one}).$$

---

## 4. Orthogonal Projection Residual ($\mathbf{I} - \widehat{\Pi}_N$) and Exact Scope Boundary

For an orthogonal Gram–Schmidt innovation sequence $\{\tilde{\phi}_k\}_{k=3}^N$ with couplings $\rho_k = \langle b | \tilde{\phi}_k \rangle$ and norms $s_k = \langle \tilde{\phi}_k | \tilde{\phi}_k \rangle > 0$, define the rank-$(N-2)$ orthogonal projector $\widehat{\Pi}_N := \sum_{k=3}^N \frac{1}{s_k} |\tilde{\phi}_k\rangle\langle\tilde{\phi}_k|$. When $\langle b | b \rangle = 1$, the unconstrained finite-$N$ residual equals
$$E_{\mathrm{free}}(N) = \bigl\|(\mathbf{I} - \widehat{\Pi}_N)|b\rangle\bigr\|_2^2 = \langle b \,|\, (\mathbf{I} - \widehat{\Pi}_N) \,|\, b \rangle = 1 - \sum_{k=3}^N \frac{\rho_k^2}{s_k} \ge 0$$
(`identity_sub_proj_residual_eq`, `orthogonal_innovation_telescoping_energy`), implying Bessel's inequality $\sum_{k=3}^N \rho_k^2 / s_k \le 1$ and monotonicity $E_{\mathrm{free}}(N+1) \le E_{\mathrm{free}}(N)$.

### Exact Mathematical Boundary (Finite-$N$ Floor vs. Asymptotic Limit)
For every fixed truncation $N \ge 2$, the prime-jump lower bound `sum_primes_le_integral_Ioc` guarantees a strictly positive prime floor $E_{\mathrm{dir}}(N) \ge \sum_{p > N} \frac{1}{2p^2} > 0$. All matrix factorizations, finite-$N$ algebraic evaluations, and projection identities above are finite-dimensional algebraic computations and conditional reductions; the asymptotic $N \to \infty$ convergence $\widehat{\Pi}_N |b\rangle \to |b\rangle$ (equivalently $\lim_{N \to \infty} \mathbf{1}^T M_N^{-1}\mathbf{1} = \infty$ or $\sum_{k=3}^\infty \rho_k^2 / s_k = 1$) carries the full analytic difficulty of the open Riemann Hypothesis.

---

## 5. Lean 4 Theorem Index

| Mathematical Statement | Formalized Lean 4 Theorem |
| :--- | :--- |
| $\mathbf{D}_M \mathbf{D}_M^{-1} = \mathbf{I}_M$, $\mathbf{D}_M^{-1} \mathbf{D}_M = \mathbf{I}_M$ | `divisorMatrix_mul_mobiusMatrix`, `mobiusMatrix_mul_divisorMatrix` |
| $\mathbf{D}_M \mu = e_1 = (1, 0, \dots, 0)^T$ | `divisorMatrix_mulVec_mobius_eq_e1` |
| $\mathbf{F}_{M,N} = \mathbf{\Sigma}_M \mathbf{D}_{M,N}$, $\mathbf{\Sigma}_M \mathbf{\Delta}_M = \mathbf{I}_M$ | `floorMatrix_eq_cumSum_mul_divisor`, `cumSumMatrix_mul_firstDiffMatrix`, `firstDiffMatrix_mul_cumSumMatrix` |
| $\mathbf{F}_M \mathbf{F}_M^{-1} = \mathbf{I}_M$, $\mathbf{F}_M^{-1} \mathbf{F}_M = \mathbf{I}_M$ | `floorMatrix_mul_inverse`, `inverse_floorMatrix_mul` |
| Pivot-row matching & $c_1 = -1 \implies r_1 = 0$ | `floorMatrix_firstRow_eq_e1`, `pivot_row_elimination_upperHalf_zero`, `upperHalf_observation_zero` |
| Cholesky whitening $\widetilde{\mathbf{\Psi}}^T \widetilde{\mathbf{\Psi}} = \mathbf{I}$ | `choleskyWhitening_gram_eq_one` |
| Wavefunction Gram $\alpha^T(\mathbf{\Omega}^T\mathbf{\Omega})\alpha = \|\mathbf{\Omega}\alpha\|_2^2 \ge 0$ | `anchoredWave_gram_quadForm_eq_norm_sq`, `anchoredWave_gram_quadForm_nonneg`, `anchoredWaveMatrix_topRow_zero` |
| Variational inverse-quadratic identity | `variational_inverse_quadForm_identity`, `variational_inverse_quadForm_ge` |
| Identity-minus-projection $\langle b \| (\mathbf{I} - \widehat{\Pi}_N) \| b \rangle = 1 - \sum \rho_k^2/s_k$ | `identity_sub_proj_residual_eq`, `orthogonal_innovation_telescoping_energy`, `orthogonal_innovation_bessel_le_one`, `orthogonal_innovation_energy_monotone` |
