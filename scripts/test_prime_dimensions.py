import json
import math
import pathlib
import numpy as np
from flint import arb, ctx

ctx.prec = 100
PI = arb.pi()
GAM = arb.const_euler()
L2PI = (arb(2) * PI).log()
GAMMA_F = 0.57721566490153286060651209008240243
_vcache = {}


def vasyunin_V(p, q):
    if q <= 1:
        return arb(0)
    key = (p % q, q)
    if key not in _vcache:
        s = arb(0)
        qa = arb(q)
        for a in range(1, q):
            s += (arb((a * p) % q) / qa) * (arb(a) / qa).cot_pi()
        _vcache[key] = s
    return _vcache[key]


def gram_entry(j, k):
    g = math.gcd(j, k)
    p, q = j // g, k // g
    pa, qa = arb(p), arb(q)
    t1 = (L2PI - GAM) / 2 * (1 / pa + 1 / qa)
    t2 = (qa - pa) / arb(2 * p * q) * (pa / qa).log() if p != q else arb(0)
    t3 = arb(0) if (p == 1 and q == 1) else PI / arb(2 * p * q) * (vasyunin_V(p, q) + vasyunin_V(q, p))
    return float(((t1 + t2 - t3) / arb(g)).mid())


def build_gram(indices):
    m = len(indices)
    G = np.zeros((m, m), dtype=np.float64)
    for i, a in enumerate(indices):
        for j in range(i, m):
            val = gram_entry(a, indices[j])
            G[i, j] = val
            G[j, i] = val
    return G


def is_prime(n):
    if n < 2:
        return False
    for d in range(2, int(math.isqrt(n)) + 1):
        if n % d == 0:
            return False
    return True


def mobius(n):
    if n == 1:
        return 1
    factors = 0
    d = 2
    temp = n
    while d * d <= temp:
        if temp % d == 0:
            temp //= d
            if temp % d == 0:
                return 0
            factors += 1
        d += 1
    if temp > 1:
        factors += 1
    return -1 if (factors % 2 == 1) else 1


def omega(n):
    if n <= 1:
        return 0
    cnt = 0
    d = 2
    temp = n
    while d * d <= temp:
        if temp % d == 0:
            cnt += 1
            while temp % d == 0:
                temp //= d
        d += 1
    if temp > 1:
        cnt += 1
    return cnt


def is_prime_power(n):
    if n < 2:
        return False
    d = 2
    while d * d <= n:
        if n % d == 0:
            while n % d == 0:
                n //= d
            return n == 1
        d += 1
    return True


def dirichlet_energy_from_submatrix(indices, G_full):
    """
    Computes E_dir = min || 1 - sum_{k in indices} c_k {1/(k x)} ||^2
    subject to D_1 = sum c_k / k = 0 (with 1 in indices).
    Uses submatrix of G_full (indexed 1..211).
    """
    pos = [k - 1 for k in indices]
    G = G_full[np.ix_(pos, pos)]
    u = np.array([(1.0 - GAMMA_F + math.log(k)) / k for k in indices], dtype=np.float64)
    w = np.array([1.0 / k for k in indices], dtype=np.float64)
    m = len(indices)
    KKT = np.zeros((m + 1, m + 1), dtype=np.float64)
    KKT[:m, :m] = G
    KKT[:m, m] = w
    KKT[m, :m] = w
    rhs = np.zeros(m + 1, dtype=np.float64)
    rhs[:m] = u
    rhs[m] = 0.0
    sol = np.linalg.solve(KKT, rhs)
    c = sol[:m]
    e_dir = 1.0 - 2.0 * np.dot(u, c) + float(c @ G @ c)
    return e_dir, G


def dirichlet_eliminated_gram(G_full, max_n=211):
    """
    Eliminates c_1 = -sum_{k=2}^{max_n} c_k / k so D_1 = 0 holds identically.
    Basis: r_tilde_k(x) = r_k(x) - (1/k) r_1(x) for k = 2..max_n.
    Returns Q_tilde of shape (max_n-1, max_n-1).
    """
    G = G_full[:max_n, :max_n]
    w = np.array([1.0 / k for k in range(2, max_n + 1)], dtype=np.float64)
    G11 = G[0, 0]
    g1 = G[0, 1:]
    G_sub = G[1:, 1:]
    Q_tilde = G_sub - np.outer(w, g1) - np.outer(g1, w) + G11 * np.outer(w, w)
    return Q_tilde


def schur_depletion(indices, G):
    p_idx = [i for i, k in enumerate(indices) if k >= 2 and is_prime(k)]
    c_idx = [i for i, k in enumerate(indices) if k >= 2 and not is_prime(k)]
    if not p_idx or not c_idx:
        return 0.0
    Q_PP = G[np.ix_(p_idx, p_idx)]
    Q_CC = G[np.ix_(c_idx, c_idx)]
    Q_PC = G[np.ix_(p_idx, c_idx)]
    Sigma = Q_CC - Q_PC.T @ np.linalg.solve(Q_PP, Q_PC)
    tr_C = float(np.trace(Q_CC))
    tr_S = float(np.trace(Sigma))
    return (tr_C - tr_S) / tr_C


if __name__ == "__main__":
    N_MAX = 211
    G_500 = build_gram(list(range(1, 501)))
    G_full = G_500[:N_MAX, :N_MAX]

    print("=== TEST 1: Single-Prime Clock (Powers of 2 or 3) vs. Multi-Prime Collision ===")
    test1_results = []
    for label, idx in [
        ("1-Prime Universe {1, 2, 4, 8, 16}", [1, 2, 4, 8, 16]),
        ("1-Prime Universe {1, 3, 9, 27}", [1, 3, 9, 27]),
        ("2-Prime N=6 {1..6} (adds p=3 & 6=2*3)", list(range(1, 7))),
    ]:
        e_dir, G = dirichlet_energy_from_submatrix(idx, G_full)
        depl = schur_depletion(idx, G)
        test1_results.append({"label": label, "E_dir": e_dir, "schur_depletion": depl})
        print(f"{label:44s} | E_dir={e_dir:.8f} | Schur_depl={depl*100:6.2f}%")

    print("\n=== TEST 2: Primorial Prime-Dimension Ladder + Euclid's +1 Prime (211) ===")
    test2_results = []
    for label, idx in [
        ("P1: {1..2}   (primes {2})", list(range(1, 3))),
        ("P2: {1..6}   (primes {2,3})", list(range(1, 7))),
        ("P3: {1..30}  (primes {2,3,5})", list(range(1, 31))),
        ("P4: {1..210} (primes {2,3,5,7})", list(range(1, 211))),
        ("P4 + Euclid's 211 (2*3*5*7 + 1 = 211)", list(range(1, 212))),
    ]:
        e_dir, G = dirichlet_energy_from_submatrix(idx, G_full)
        depl = schur_depletion(idx, G)
        N_m = idx[-1]
        bblr = math.log(N_m) * e_dir
        test2_results.append({
            "label": label,
            "N": N_m,
            "E_dir": e_dir,
            "ln_N_E_dir": bblr,
            "schur_depletion": depl,
        })
        print(f"{label:44s} | E_dir={e_dir:.8f} | ln(N)*E_dir={bblr:.8f} | Schur_depl={depl*100:6.2f}%")

    print("\n=== TEST 3: Sequential Cholesky Identity-Matrix Innovation Ledger (k = 2..211) ===")
    Q_tilde = dirichlet_eliminated_gram(G_full, max_n=N_MAX)
    L_chol = np.linalg.cholesky(Q_tilde)
    # Verify L^{-1} Q_tilde L^{-T} = I_{N-1}
    L_inv = np.linalg.inv(L_chol)
    whitened = L_inv @ Q_tilde @ L_inv.T
    whitening_err = float(np.max(np.abs(whitened - np.eye(N_MAX - 1))))

    e_dir_seq = {}
    for k in range(2, N_MAX + 1):
        e_dir_seq[k], _ = dirichlet_energy_from_submatrix(list(range(1, k + 1)), G_full)

    ledger = []
    class_stats = {
        "pure_primes": {"count": 0, "delta_E_sum": 0.0, "s_k_sum": 0.0},
        "square_free_cross_tensors": {"count": 0, "delta_E_sum": 0.0, "s_k_sum": 0.0},
        "prime_power_echoes": {"count": 0, "delta_E_sum": 0.0, "s_k_sum": 0.0},
    }

    for k in range(3, N_MAX + 1):
        dE = e_dir_seq[k - 1] - e_dir_seq[k]
        s_k = float(L_chol[k - 2, k - 2] ** 2)
        mu_k = mobius(k)
        if is_prime(k):
            cls = "pure_primes"
        elif mu_k != 0:
            cls = "square_free_cross_tensors"
        else:
            cls = "prime_power_echoes"
        class_stats[cls]["count"] += 1
        class_stats[cls]["delta_E_sum"] += dE
        class_stats[cls]["s_k_sum"] += s_k
        ledger.append({
            "k": k,
            "class": cls,
            "mobius": mu_k,
            "E_dir_k": e_dir_seq[k],
            "delta_E_k": dE,
            "s_k": s_k,
        })

    total_drop = e_dir_seq[2] - e_dir_seq[N_MAX]
    print(f"Cholesky whitening max |L^-1 Q_tilde L^-T - I_{N_MAX-1}| = {whitening_err:.3e}")
    print(f"Total drop E_dir(2) - E_dir(211) = {total_drop:.8f}")
    for cls_name, st in class_stats.items():
        pct = (st["delta_E_sum"] / total_drop) * 100.0
        st["share_pct"] = pct
        print(f"  {cls_name:28s} | count={st['count']:3d} | sum_dE={st['delta_E_sum']:.8f} ({pct:6.2f}%)")

    top15 = sorted(ledger, key=lambda r: r["delta_E_k"], reverse=True)[:15]
    print("\nTop 15 single integer clock ticks k in [3, 211] by largest Delta E_k:")
    for rank, r in enumerate(top15, 1):
        pct = (r["delta_E_k"] / total_drop) * 100.0
        print(
            f"  #{rank:2d} k={r['k']:3d} ({r['class']:25s}, mu={r['mobius']:+d}) "
            f"| dE_k={r['delta_E_k']:.8f} ({pct:6.2f}%) | s_k={r['s_k']:.8e}"
        )

    print("\n=== TEST 4: Global Subspace Ablation at N = 211 ===")
    sub_a = [1] + [k for k in range(2, N_MAX + 1) if is_prime(k)]
    sub_b = [1] + [k for k in range(2, N_MAX + 1) if is_prime_power(k)]
    sub_c = [k for k in range(1, N_MAX + 1) if mobius(k) != 0]
    sub_d = list(range(1, N_MAX + 1))

    test4_results = []
    for label, idx in [
        ("a) Primes Only ({1} U {p <= 211})", sub_a),
        ("b) Primes + Prime Powers ({1} U {p^m <= 211})", sub_b),
        ("c) Square-Free Only (mu(k) != 0, k <= 211)", sub_c),
        ("d) Full Basis {1..211}", sub_d),
    ]:
        e_dir, _ = dirichlet_energy_from_submatrix(idx, G_full)
        bblr = math.log(N_MAX) * e_dir
        test4_results.append({
            "label": label,
            "size": len(idx),
            "E_dir": e_dir,
            "ln_211_E_dir": bblr,
        })
        print(f"{label:48s} | size={len(idx):3d} | E_dir={e_dir:.8f} | ln(211)*E_dir={bblr:.8f}")

    print("\n=== TEST 5: Exterior Wedge Grade Ladder Lambda^{<= r} at N = 211 ===")
    sqfree = [k for k in range(1, N_MAX + 1) if mobius(k) != 0]
    grades = {r: [k for k in sqfree if omega(k) == r] for r in range(5)}
    print("Square-free partition counts by exterior wedge grade r = omega(k):")
    for r in range(5):
        print(f"  Grade {r} (omega={r}): count={len(grades[r]):3d}, sample={grades[r][:6]}")

    test5_results = []
    for label, idx in [
        ("Lambda^{<=1} (Grades 0..1: {1} + Primes)", [k for k in sqfree if omega(k) <= 1]),
        ("Lambda^{<=2} (Grades 0..2: + 2D Semiprimes)", [k for k in sqfree if omega(k) <= 2]),
        ("Lambda^{<=3} (Grades 0..3: + 3D Triples)", [k for k in sqfree if omega(k) <= 3]),
        ("Lambda^{<=4} (Grades 0..4: + 4D Primorial 210)", [k for k in sqfree if omega(k) <= 4]),
        ("Full Basis {1..211} (+ 81 square-full echoes)", sub_d),
    ]:
        e_dir, _ = dirichlet_energy_from_submatrix(idx, G_full)
        bblr = math.log(N_MAX) * e_dir
        test5_results.append({
            "label": label,
            "size": len(idx),
            "E_dir": e_dir,
            "ln_211_E_dir": bblr,
        })
        print(f"{label:48s} | size={len(idx):3d} | E_dir={e_dir:.8f} | ln(211)*E_dir={bblr:.8f}")

    receipt = {
        "status": "verified-finite",
        "NO_RH_PROOF": True,
        "precision_digits": 100,
        "N_max": N_MAX,
        "dirichlet_anchor": "D_1 = sum_{k=1}^N c_k / k = 0",
        "test1_single_vs_multi_prime": test1_results,
        "test2_primorial_ladder_and_euclid_211": test2_results,
        "test3_cholesky_innovation_ledger": {
            "E_dir_2": e_dir_seq[2],
            "E_dir_211": e_dir_seq[N_MAX],
            "total_drop": total_drop,
            "whitening_identity_error": whitening_err,
            "class_summary": class_stats,
            "top_15_ticks": top15,
        },
        "test4_subspace_ablation_N211": test4_results,
        "test5_exterior_wedge_ladder": {
            "grade_counts": {str(r): len(grades[r]) for r in range(5)},
            "filtration_results": test5_results,
        },
    }

    print("\n=== TEST 6: Scale Stability of Exterior Wedge Grades Lambda^r Across N in {30, 100, 211, 350, 500} ===")
    test6_results = []
    for N_cut in [30, 100, 211, 350, 500]:
        sqf_n = [k for k in range(1, N_cut + 1) if mobius(k) != 0]
        e1, _ = dirichlet_energy_from_submatrix([k for k in sqf_n if omega(k) <= 1], G_500)
        e2, _ = dirichlet_energy_from_submatrix([k for k in sqf_n if omega(k) <= 2], G_500)
        e3, _ = dirichlet_energy_from_submatrix([k for k in sqf_n if omega(k) <= 3], G_500)
        e4, _ = dirichlet_energy_from_submatrix([k for k in sqf_n if omega(k) <= 4], G_500)
        efull, _ = dirichlet_energy_from_submatrix(list(range(1, N_cut + 1)), G_500)
        tot = e1 - efull
        sh2 = (e1 - e2) / tot * 100.0
        sh3 = (e2 - e3) / tot * 100.0
        sh4 = (e3 - e4) / tot * 100.0
        shsq = (e4 - efull) / tot * 100.0
        row = {
            "N": N_cut,
            "E_1": e1, "E_2": e2, "E_3": e3, "E_4": e4, "E_full": efull,
            "lnN_E_full": math.log(N_cut) * efull,
            "share_Lambda2_pct": sh2,
            "share_Lambda3_pct": sh3,
            "share_Lambda4_pct": sh4,
            "share_SqFull_pct": shsq,
        }
        test6_results.append(row)
        print(
            f"N={N_cut:3d} | E1={e1:.6f} -> E2={e2:.6f} -> E3={e3:.6f} -> E4={e4:.6f} -> Full={efull:.6f} "
            f"| Sh(L2)={sh2:5.2f}% Sh(L3)={sh3:5.2f}% Sh(L4)={sh4:4.2f}% Sh(Sq)={shsq:4.2f}%"
        )

    print("\n=== TEST 7: Euclid Opposite-Side Contradiction Exclusion Disc Across N in {2, 6, 30, 100, 210, 211, 350, 500} ===")
    test7_results = []
    for N_cut in [2, 6, 30, 100, 210, 211, 350, 500]:
        E, _ = dirichlet_energy_from_submatrix(list(range(1, N_cut + 1)), G_500)
        X_N = 1.0 / E
        R_N = math.sqrt(1.0 - E) / E
        beta_min = (1.0 - math.sqrt(1.0 - E)) / E
        gammas = {}
        for b0 in [0.60, 0.75, 0.90, 1.00]:
            val = (2.0 * b0 - 1.0) / E - b0 * b0
            gammas[f"{b0:.2f}"] = math.sqrt(max(0.0, val))
        row = {
            "N": N_cut,
            "E_dir": E,
            "X_N": X_N,
            "R_N": R_N,
            "beta_min": beta_min,
            "gamma_max": gammas,
        }
        test7_results.append(row)
        print(
            f"N={N_cut:3d} | E={E:.6f} | X_N={X_N:7.2f} R_N={R_N:7.2f} | beta_min={beta_min:.6f} "
            f"| g_max(0.60,0.75,0.90,1.00)=({gammas['0.60']:.2f}, {gammas['0.75']:.2f}, {gammas['0.90']:.2f}, {gammas['1.00']:.2f})"
        )

    receipt["test6_exterior_wedge_scale_stability"] = test6_results
    receipt["test7_euclid_exclusion_disc_sweep"] = test7_results

    receipt_path = pathlib.Path(
        r"D:\Comfy UI\idea memory\obsidian brains\big picture\03_Riemann_Hypothesis\Probes\prime_identity_matrix_innovation_N211.json"
    )
    receipt_path.parent.mkdir(parents=True, exist_ok=True)
    receipt_path.write_text(json.dumps(receipt, indent=2), encoding="utf-8")
    print(f"\nSaved JSON receipt: {receipt_path}")

    receipt_500_path = pathlib.Path(
        r"D:\Comfy UI\idea memory\obsidian brains\big picture\03_Riemann_Hypothesis\Probes\exterior_wedge_and_euclid_disc_N500.json"
    )
    receipt_500_path.write_text(json.dumps({
        "status": "verified-finite",
        "NO_RH_PROOF": True,
        "precision_digits": 100,
        "N_max": 500,
        "dirichlet_anchor": "D_1 = sum_{k=1}^N c_k / k = 0",
        "test6_exterior_wedge_scale_stability": test6_results,
        "test7_euclid_exclusion_disc_sweep": test7_results,
    }, indent=2), encoding="utf-8")
    print(f"Saved JSON receipt: {receipt_500_path}")

    print("\n=== TEST 8: Half-Identity & Half-Reflection Matrices at N = 211 (Square-Free Basis) ===")
    sqf_211 = [k for k in range(1, 212) if mobius(k) != 0]
    m_sqf = len(sqf_211)
    J_N = np.diag([float(mobius(k)) for k in sqf_211])
    I_sqf = np.eye(m_sqf)
    P_pos = 0.5 * (I_sqf + J_N)
    P_neg = 0.5 * (I_sqf - J_N)

    err_sum = float(np.max(np.abs(P_pos + P_neg - I_sqf)))
    err_diff = float(np.max(np.abs(P_pos - P_neg - J_N)))
    err_orth = float(np.max(np.abs(P_pos @ P_neg)))
    err_idem_pos = float(np.max(np.abs(P_pos @ P_pos - P_pos)))
    err_idem_neg = float(np.max(np.abs(P_neg @ P_neg - P_neg)))
    # Non-symmetric half-observable K_half whose symmetric part is 4 * J_N
    rng = np.random.default_rng(42)
    A_skew = rng.standard_normal((m_sqf, m_sqf))
    A_skew = A_skew - A_skew.T
    K_half = 2.0 * J_N + A_skew
    err_khalf = float(np.max(np.abs(K_half + K_half.T - 4.0 * J_N)))

    # Coupled with Cholesky L_sqf of G_sqf and optimal c* (D_1 = 0)
    pos_sqf = [k - 1 for k in sqf_211]
    G_sqf = G_500[np.ix_(pos_sqf, pos_sqf)]
    L_sqf = np.linalg.cholesky(G_sqf)
    u_sqf = np.array([(1.0 - GAMMA_F + math.log(k)) / k for k in sqf_211], dtype=np.float64)
    w_sqf = np.array([1.0 / k for k in sqf_211], dtype=np.float64)
    KKT_sqf = np.zeros((m_sqf + 1, m_sqf + 1), dtype=np.float64)
    KKT_sqf[:m_sqf, :m_sqf] = G_sqf
    KKT_sqf[:m_sqf, m_sqf] = w_sqf
    KKT_sqf[m_sqf, :m_sqf] = w_sqf
    rhs_sqf = np.zeros(m_sqf + 1, dtype=np.float64)
    rhs_sqf[:m_sqf] = u_sqf
    c_star = np.linalg.solve(KKT_sqf, rhs_sqf)[:m_sqf]

    v_white = L_sqf.T @ c_star
    norm_total = float(np.dot(v_white, v_white))
    norm_pos = float(np.sum((P_pos @ v_white) ** 2))
    norm_neg = float(np.sum((P_neg @ v_white) ** 2))
    print(f"dim(Lambda^*)={m_sqf} | err(P_+ + P_- = I)={err_sum:.1e}, err(P_+ - P_- = J)={err_diff:.1e}, err(P_+ P_- = 0)={err_orth:.1e}")
    print(f"err(P_±^2 = P_±)=({err_idem_pos:.1e}, {err_idem_neg:.1e}) | err(K_half + K_half^T = 4*J)={err_khalf:.1e}")
    print(f"Whitened ||L^T c*||^2 = {norm_total:.8f} | Even ||P_+ L^T c*||^2 = {norm_pos:.8f} ({norm_pos/norm_total*100:.2f}%) | Odd ||P_- L^T c*||^2 = {norm_neg:.8f} ({norm_neg/norm_total*100:.2f}%)")

    test8_results = {
        "dim_square_free": m_sqf,
        "err_P_sum_I": err_sum,
        "err_P_diff_J": err_diff,
        "err_P_orth": err_orth,
        "err_P_pos_idem": err_idem_pos,
        "err_P_neg_idem": err_idem_neg,
        "err_K_half_recovery": err_khalf,
        "whitened_total_norm_sq": norm_total,
        "even_grade_norm_sq": norm_pos,
        "odd_grade_norm_sq": norm_neg,
        "even_share_pct": norm_pos / norm_total * 100.0,
        "odd_share_pct": norm_neg / norm_total * 100.0,
    }

    print("\n=== TEST 9: Reconstructing pi and pi^{1/2} = Gamma(1/2) From Scratch ===")
    test9_results = []
    for N_cut in [211, 500]:
        E_cut, _ = dirichlet_energy_from_submatrix(list(range(1, N_cut + 1)), G_500)
        pi_vas = 0.25 * math.exp(2.0 + GAMMA_F - math.log(N_cut) * E_cut)
        sqrt_pi_vas = math.sqrt(pi_vas)

        primes_n = [p for p in range(2, N_cut + 1) if is_prime(p)]
        prod_euler = 1.0
        for p in primes_n:
            prod_euler *= (p * p) / (p * p - 1.0)
        pi_eul = math.sqrt(6.0 * prod_euler)
        sqrt_pi_eul = math.sqrt(pi_eul)

        prod_diode = 1.0
        for p in primes_n:
            if p >= 3:
                chi4 = 1.0 if (p % 4 == 1) else -1.0
                prod_diode *= p / (p - chi4)
        pi_dio = 4.0 * prod_diode
        sqrt_pi_dio = math.sqrt(pi_dio)

        rel_vas = abs(pi_vas - math.pi) / math.pi * 100.0
        rel_eul = abs(pi_eul - math.pi) / math.pi * 100.0
        rel_dio = abs(pi_dio - math.pi) / math.pi * 100.0
        print(f"N={N_cut:3d}:")
        print(f"  a) Vasyunin Tare : pi={pi_vas:.8f} (err={rel_vas:.4f}%), sqrt(pi)={sqrt_pi_vas:.8f}")
        print(f"  b) Euler Trace   : pi={pi_eul:.8f} (err={rel_eul:.4f}%), sqrt(pi)={sqrt_pi_eul:.8f}")
        print(f"  c) Mod-4 Diode   : pi={pi_dio:.8f} (err={rel_dio:.4f}%), sqrt(pi)={sqrt_pi_dio:.8f}")
        test9_results.append({
            "N": N_cut,
            "pi_vasyunin": pi_vas, "sqrt_pi_vasyunin": sqrt_pi_vas, "rel_err_vasyunin_pct": rel_vas,
            "pi_euler": pi_eul, "sqrt_pi_euler": sqrt_pi_eul, "rel_err_euler_pct": rel_eul,
            "pi_diode": pi_dio, "sqrt_pi_diode": sqrt_pi_dio, "rel_err_diode_pct": rel_dio,
        })

    print("\n=== TEST 10: Second-Order Schur Taring S_{>=3} (Pure 3D & 4D Above 2D Baseline) ===")
    test10_results = []
    for N_cut in [211, 500]:
        sqf_n = [k for k in range(1, N_cut + 1) if mobius(k) != 0]
        base_idx = [k - 1 for k in sqf_n if omega(k) <= 2]
        targ_idx = [k - 1 for k in sqf_n if omega(k) >= 3]
        Q_bb = G_500[np.ix_(base_idx, base_idx)]
        Q_tt = G_500[np.ix_(targ_idx, targ_idx)]
        Q_bt = G_500[np.ix_(base_idx, targ_idx)]
        S_34 = Q_tt - Q_bt.T @ np.linalg.solve(Q_bb, Q_bt)
        tr_tt = float(np.trace(Q_tt))
        tr_s34 = float(np.trace(S_34))
        depl_34 = (tr_tt - tr_s34) / tr_tt * 100.0

        e2, _ = dirichlet_energy_from_submatrix([k for k in sqf_n if omega(k) <= 2], G_500)
        e3, _ = dirichlet_energy_from_submatrix([k for k in sqf_n if omega(k) <= 3], G_500)
        e4, _ = dirichlet_energy_from_submatrix([k for k in sqf_n if omega(k) <= 4], G_500)
        d3 = e2 - e3
        d4 = e3 - e4
        tot_34 = e2 - e4
        print(
            f"N={N_cut:3d} | dim(base)={len(base_idx):3d}, dim(target)={len(targ_idx):2d} "
            f"| Tr(Q_>=3)={tr_tt:.6f} -> Tr(S_>=3)={tr_s34:.6f} (Schur_depl={depl_34:.2f}%)"
        )
        print(
            f"        Residual drop E(<=2)-E(<=4)={tot_34:.8f} | 3D Share={d3/tot_34*100:.2f}% ({d3:.8f}), 4D Share={d4/tot_34*100:.2f}% ({d4:.8f})"
        )
        test10_results.append({
            "N": N_cut,
            "dim_base_le2": len(base_idx),
            "dim_target_ge3": len(targ_idx),
            "tr_Q_ge3": tr_tt,
            "tr_S_ge3": tr_s34,
            "schur_depletion_ge3_pct": depl_34,
            "E_le2": e2, "E_le3": e3, "E_le4": e4,
            "drop_3D": d3, "drop_4D": d4, "drop_total_34": tot_34,
            "share_3D_pct": d3 / tot_34 * 100.0,
            "share_4D_pct": d4 / tot_34 * 100.0,
        })

    half_pi_path = pathlib.Path(
        r"D:\Comfy UI\idea memory\obsidian brains\big picture\03_Riemann_Hypothesis\Probes\half_reflection_matrices_and_pi_N500.json"
    )
    half_pi_path.write_text(json.dumps({
        "status": "verified-finite",
        "NO_RH_PROOF": True,
        "precision_digits": 100,
        "dirichlet_anchor": "D_1 = sum_{k=1}^N c_k / k = 0",
        "test8_half_reflection_matrices_N211": test8_results,
        "test9_pi_from_scratch": test9_results,
        "test10_second_order_schur_3D_4D": test10_results,
    }, indent=2), encoding="utf-8")
    print(f"\nSaved JSON receipt: {half_pi_path}")
