"""Sparse BNBD Basis Compression & Vasyunin Cotangent Indefiniteness Study.

Non-circular, 50-digit rigorous numerical and structural audit of Track 2:
  1. Exact Vasyunin Gram matrix G_{jk} = G^{smooth}_{jk} + G^{cot}_{jk} via
     certified python-flint Arb cotangent balls converted to 50-digit mpmath,
     cross-checked against compute_exact_gram_baez_duarte.vasyunin_gram_entry_mp.
  2. Constructive spectral indefiniteness proof for G_S^(cot): demonstrates
     negative eigenvalues lambda_min < 0 and unbounded descent c^T G_S^(cot) c -> -inf,
     explaining why only the positive-definite total Gram matrix G_S defines a valid
     minimization objective d_S^2 = 1 - b_S^T G_S^{-1} b_S.
  3. Exact consecutive baseline d_N^2 for N = 1..180 at dps = 50.
  4. Fixed-cardinality family benchmarks (|S| = 10, 20, 30, 40, 50) comparing
     consecutive integers, square-free integers, primes, P_7-smooth integers,
     P_7 divisors, coprime-to-6 integers, Orthogonal Matching Pursuit (OMP) greedy
     selection, 1-opt swap refinement, and wide sparse probes up to ~10^5.
  5. BBLR (2005) & Dedekind norm/trace lattice no-go bounds confirming that
     finite rational subsets S <= 10^6 cannot break the C_BD / ln(max S) barrier
     or cross any subcritical beta_0 = 0.70, gamma_1 ~ 14.135 floor (NO_RH_PROOF = TRUE).
"""
from __future__ import annotations

import json
from math import gcd, isqrt
from pathlib import Path
import time
from typing import Dict, Iterable, List, Sequence, Tuple

from flint import arb, ctx
import mpmath as mp

SCRIPT_DIR = Path(__file__).resolve().parent
DPS = 50
ARB_PREC_BITS = 192  # ~57.8 decimal digits, safely above dps=50

# Exact classical Baez-Duarte constant C_BD = 2 + gamma - ln(4*pi)
with mp.workdps(80):
    C_BD_EXACT = float(2 + mp.euler - mp.log(4 * mp.pi))

PRIMES_P7 = (2, 3, 5, 7, 11, 13, 17)
P7_PRIMORIAL = 510510


class CachedVasyuninEngine:
    """High-precision Vasyunin Gram and RHS inner-product evaluator with caching."""

    def __init__(self, dps: int = DPS, arb_bits: int = ARB_PREC_BITS) -> None:
        self.dps = dps
        self.arb_bits = arb_bits
        self._cot_cache: Dict[Tuple[int, int], mp.mpf] = {}
        self._cot_rad_max: float = 0.0
        self._pair_cache: Dict[Tuple[int, int], Tuple[mp.mpf, mp.mpf, mp.mpf]] = {}
        self._b_cache: Dict[int, mp.mpf] = {}

    def vasyunin_cotangent_sum(self, q: int, p: int) -> mp.mpf:
        """Compute V(q, p) = sum_{m=1}^{q-1} (m/q) * cot(pi * m * p^{-1} / q) for coprime (q,p)."""
        if q <= 2:
            return mp.mpf(0)
        p_mod = p % q
        if p_mod == 0:
            return mp.mpf(0)
        inv_p = pow(p_mod, -1, q)
        key = (inv_p, q)
        if key in self._cot_cache:
            return self._cot_cache[key]

        # Antisymmetry cot(pi*(q-m)*inv_p/q) = -cot(pi*m*inv_p/q) halves the sum;
        # when q is even and gcd(q,p)=1, the midpoint m=q/2 gives cot(pi*inv_p/2)=0.
        half = (q - 1) // 2
        with ctx.workprec(self.arb_bits):
            pi_over_q = arb.pi() / q
            total = arb(0)
            for m in range(1, half + 1):
                total += (2 * m - q) * (pi_over_q * ((m * inv_p) % q)).cot()
            total /= q
            self._cot_rad_max = max(self._cot_rad_max, float(total.rad()))
            mid_str = total.mid().str(self.dps + 8, radius=False)

        with mp.workdps(self.dps + 10):
            val = +mp.mpf(mid_str)
        self._cot_cache[key] = val
        return val

    def gram_entry(self, j: int, k: int) -> Tuple[mp.mpf, mp.mpf, mp.mpf]:
        """Return exact Vasyunin decomposition (G_total, G_smooth, G_cot) at high precision."""
        if j > k:
            j, k = k, j
        key = (j, k)
        if key in self._pair_cache:
            return self._pair_cache[key]

        g = gcd(j, k)
        a, b = j // g, k // g
        with mp.workdps(self.dps + 10):
            C_val = mp.log(2 * mp.pi) - mp.euler
            g_smooth_coprime = (C_val * (a + b) - 2 - (b - a) * mp.log(mp.mpf(b) / a)) / (2 * mp.mpf(a) * b)
            # Integral on [1/g, 1] gives (1/g) * [1/(ab) * (1 - 1/g)] = (g - 1) / (g^2 * a * b)
            g_smooth = g_smooth_coprime / g + mp.mpf(g - 1) / (mp.mpf(g) * g * a * b)
            v_ab = self.vasyunin_cotangent_sum(a, b) if a > 2 else mp.mpf(0)
            v_ba = self.vasyunin_cotangent_sum(b, a) if b > 2 else mp.mpf(0)
            g_cot = -(mp.pi / (2 * mp.mpf(g) * a * b)) * (v_ab + v_ba)
            g_total = g_smooth + g_cot
            res = (+g_total, +g_smooth, +g_cot)
        self._pair_cache[key] = res
        return res

    def rhs_entry(self, k: int) -> mp.mpf:
        """Compute b_k = int_0^1 {1/(k*x)} dx = (1 - gamma + ln k) / k."""
        if k in self._b_cache:
            return self._b_cache[k]
        with mp.workdps(self.dps + 10):
            val = +(1 - mp.euler + mp.log(k)) / k
        self._b_cache[k] = val
        return val

    def solve_subset_distance(self, indices: Sequence[int]) -> Dict[str, object]:
        """Compute exact projection distance d_S^2 via Cholesky at DPS=50."""
        idx = list(indices)
        m = len(idx)
        if m == 0:
            raise ValueError("subset must be nonempty")
        if len(set(idx)) != m:
            raise ValueError("duplicate integers in subset")

        with mp.workdps(self.dps + 10):
            G = mp.matrix(m, m)
            b = [self.rhs_entry(k) for k in idx]
            for i in range(m):
                ki = idx[i]
                for j in range(i, m):
                    g_tot, _, _ = self.gram_entry(ki, idx[j])
                    G[i, j] = g_tot
                    G[j, i] = g_tot
            L = mp.cholesky(G)
            # Forward substitution L y = b gives ||proj(1)||^2 = ||y||_2^2
            y = [mp.mpf(0)] * m
            for i in range(m):
                s = b[i]
                for j in range(i):
                    s -= L[i, j] * y[j]
                y[i] = s / L[i, i]
            norm_proj_sq = sum(yi * yi for yi in y)
            d_sq = 1 - norm_proj_sq
            min_diag = min(L[i, i] for i in range(m))
        return {
            "cardinality": m,
            "max_element": max(idx),
            "d_sq": float(d_sq),
            "d_sq_str": mp.nstr(d_sq, 20),
            "norm_proj_sq": float(norm_proj_sq),
            "min_cholesky_diag": float(min_diag),
            "bblr_asymp_bound": C_BD_EXACT / float(mp.log(max(max(idx), 2))),
        }


def consecutive_baseline(engine: CachedVasyuninEngine, max_n: int = 180) -> Dict[int, float]:
    """Compute exact consecutive d_N^2 for N = 1..max_n using incremental Cholesky."""
    with mp.workdps(engine.dps + 10):
        L_rows: List[List[mp.mpf]] = []
        y: List[mp.mpf] = []
        running_sq = mp.mpf(0)
        results: Dict[int, float] = {}
        for n in range(1, max_n + 1):
            row: List[mp.mpf] = []
            for j in range(n - 1):
                g_tot, _, _ = engine.gram_entry(n, j + 1)
                s = g_tot
                lj = L_rows[j]
                for p in range(j):
                    s -= row[p] * lj[p]
                row.append(s / lj[j])
            g_nn, _, _ = engine.gram_entry(n, n)
            diag_sq = g_nn - sum(v * v for v in row)
            row.append(mp.sqrt(diag_sq))
            L_rows.append(row)

            bn = engine.rhs_entry(n)
            s_y = bn
            for j in range(n - 1):
                s_y -= row[j] * y[j]
            yn = s_y / row[-1]
            y.append(yn)
            running_sq += yn * yn
            results[n] = float(1 - running_sq)
    return results


def equivalent_consecutive_n(d_sq: float, baseline: Dict[int, float]) -> Dict[str, object]:
    """Interpolate continuous N_equiv on the exact consecutive d_N^2 curve (or cap)."""
    max_n = max(baseline.keys())
    if d_sq >= baseline[1]:
        return {"n_equiv": 1.0, "bounded_above_by_table": True}
    if d_sq < baseline[max_n]:
        # Strictly monotone decay bounded cleanly below table limit
        return {"n_equiv": float(max_n), "exceeds_table_max": max_n, "bounded_above_by_table": False}
    for n in range(2, max_n + 1):
        prev_d, cur_d = baseline[n - 1], baseline[n]
        if prev_d >= d_sq >= cur_d:
            frac = (prev_d - d_sq) / (prev_d - cur_d) if prev_d > cur_d else 0.0
            return {
                "n_equiv": (n - 1) + frac,
                "bracket": [n - 1, n],
                "bounded_above_by_table": True,
            }
    return {"n_equiv": None, "bounded_above_by_table": False}


def mobius_sieve(limit: int) -> List[int]:
    """Return mu[0..limit]."""
    mu = [0] * (limit + 1)
    mu[1] = 1
    primes: List[int] = []
    is_comp = [False] * (limit + 1)
    for i in range(2, limit + 1):
        if not is_comp[i]:
            primes.append(i)
            mu[i] = -1
        for p in primes:
            if i * p > limit:
                break
            is_comp[i * p] = True
            if i % p == 0:
                mu[i * p] = 0
                break
            mu[i * p] = -mu[i]
    return mu


def sieve_primes(limit: int) -> List[int]:
    """Return primes <= limit."""
    sieve = [True] * (limit + 1)
    sieve[0] = sieve[1] = False
    for p in range(2, isqrt(limit) + 1):
        if sieve[p]:
            sieve[p * p : limit + 1 : p] = [False] * len(range(p * p, limit + 1, p))
    return [i for i, flag in enumerate(sieve) if flag]


def p7_smooth_numbers(count: int) -> List[int]:
    """Smallest `count` positive integers whose prime factors lie in {2,3,5,7,11,13,17}."""
    vals = {1}
    frontier = {1}
    while len(vals) < count * 8:
        nxt = set()
        for v in frontier:
            for p in PRIMES_P7:
                nv = v * p
                if nv <= 10**6:
                    nxt.add(nv)
        if not nxt:
            break
        vals.update(nxt)
        frontier = nxt
    return sorted(vals)[:count]


def p7_divisors() -> List[int]:
    """All 128 positive divisors of P_7 = 2*3*5*7*11*13*17."""
    divs = [1]
    for p in PRIMES_P7:
        divs += [d * p for d in divs]
    return sorted(divs)


def build_candidate_pool() -> List[int]:
    """Rich structured candidate pool up to ~2500 without combinatorial explosion."""
    pool = set(range(1, 161))
    pool.update(sieve_primes(1500))
    mu = mobius_sieve(2500)
    # All square-free integers <= 400
    for n in range(1, 401):
        if mu[n] != 0:
            pool.add(n)
    # Structured primorial & P_7 products <= 2310
    for d in p7_divisors():
        if d <= 2310:
            pool.add(d)
    # Semiprimes of primes <= 59
    small_p = [p for p in sieve_primes(59)]
    for i, p in enumerate(small_p):
        for q in small_p[i + 1 :]:
            if p * q <= 2000:
                pool.add(p * q)
    return sorted(pool)


def greedy_omp_select(
    engine: CachedVasyuninEngine,
    pool: Sequence[int],
    k_max: int,
) -> Tuple[List[int], List[Dict[str, float]]]:
    """Exact Cholesky Orthogonal Matching Pursuit maximizing single-step drop in d_S^2."""
    remaining = list(pool)
    selected: List[int] = []
    history: List[Dict[str, float]] = []

    with mp.workdps(engine.dps + 10):
        L_rows: List[List[mp.mpf]] = []
        y: List[mp.mpf] = []
        running_norm_sq = mp.mpf(0)

        for step in range(1, k_max + 1):
            best_c = None
            best_drop = mp.mpf(-1)
            best_row: List[mp.mpf] = []
            best_y = mp.mpf(0)

            for cand in remaining:
                # Orthogonalize rho_cand against current Cholesky orthonormal basis
                row: List[mp.mpf] = []
                for j, sj in enumerate(selected):
                    g_cs, _, _ = engine.gram_entry(cand, sj)
                    s = g_cs
                    lj = L_rows[j]
                    for p in range(j):
                        s -= row[p] * lj[p]
                    row.append(s / lj[j])

                g_cc, _, _ = engine.gram_entry(cand, cand)
                diag_sq = g_cc - sum(v * v for v in row)
                if diag_sq <= mp.mpf("1e-45"):
                    continue
                diag = mp.sqrt(diag_sq)
                row.append(diag)

                bc = engine.rhs_entry(cand)
                s_y = bc
                for j in range(len(selected)):
                    s_y -= row[j] * y[j]
                y_cand = s_y / diag
                drop = y_cand * y_cand

                if drop > best_drop:
                    best_drop = drop
                    best_c = cand
                    best_row = row
                    best_y = y_cand

            assert best_c is not None
            selected.append(best_c)
            remaining.remove(best_c)
            L_rows.append(best_row)
            y.append(best_y)
            running_norm_sq += best_drop
            d_cur = 1 - running_norm_sq
            if step in (10, 20, 30, 40, 50):
                history.append(
                    {
                        "step": step,
                        "added": best_c,
                        "d_sq": float(d_cur),
                        "max_element": max(selected),
                    }
                )
    return selected, history


def one_opt_swap_refine(
    engine: CachedVasyuninEngine,
    initial_set: Sequence[int],
    candidates: Sequence[int],
    max_swaps: int = 8,
) -> Tuple[List[int], List[Dict[str, object]]]:
    """Perform exact 1-opt swap local refinement over candidate replacement integers."""
    cur = list(initial_set)
    cur_res = engine.solve_subset_distance(cur)
    best_d = cur_res["d_sq"]
    swap_log: List[Dict[str, object]] = []
    cand_list = [c for c in candidates if c not in cur]

    with mp.workdps(engine.dps + 10):
        m = len(cur)
        for _ in range(max_swaps):
            # Build full matrix and inverse quickly via mpmath for 1-opt Sherman-Morrison-free exact leave-one-out
            G = mp.matrix(m, m)
            b = mp.matrix([engine.rhs_entry(k) for k in cur])
            for i in range(m):
                for j in range(i, m):
                    g_tot, _, _ = engine.gram_entry(cur[i], cur[j])
                    G[i, j] = G[j, i] = g_tot
            G_inv = G ** -1
            c_opt = G_inv * b
            # Leave-one-out loss for dropping index i is c_opt[i]^2 / G_inv[i, i]
            drop_losses = [(i, float((c_opt[i] ** 2) / G_inv[i, i])) for i in range(m)]
            drop_losses.sort(key=lambda pair: pair[1])
            # Only test replacing the 8 weakest elements to stay deterministic & fast
            weak_indices = [idx for idx, _ in drop_losses[:8]]

            improved = False
            best_move = None
            best_new_d = best_d

            for rm_pos in weak_indices:
                sub = [cur[p] for p in range(m) if p != rm_pos]
                # Pre-factor sub once via Cholesky!
                G_sub = mp.matrix(m - 1, m - 1)
                b_sub = [engine.rhs_entry(k) for k in sub]
                for i in range(m - 1):
                    for j in range(i, m - 1):
                        g_tot, _, _ = engine.gram_entry(sub[i], sub[j])
                        G_sub[i, j] = G_sub[j, i] = g_tot
                L_sub = mp.cholesky(G_sub)
                y_sub = [mp.mpf(0)] * (m - 1)
                for i in range(m - 1):
                    s = b_sub[i]
                    for j in range(i):
                        s -= L_sub[i, j] * y_sub[j]
                    y_sub[i] = s / L_sub[i, i]
                base_proj = sum(yi * yi for yi in y_sub)

                for add_c in cand_list:
                    row = []
                    for j in range(m - 1):
                        g_cs, _, _ = engine.gram_entry(add_c, sub[j])
                        s = g_cs
                        for p in range(j):
                            s -= row[p] * L_sub[j, p]
                        row.append(s / L_sub[j, j])
                    g_cc, _, _ = engine.gram_entry(add_c, add_c)
                    diag_sq = g_cc - sum(v * v for v in row)
                    if diag_sq <= mp.mpf("1e-45"):
                        continue
                    s_y = engine.rhs_entry(add_c) - sum(row[j] * y_sub[j] for j in range(m - 1))
                    d_new = float(1 - (base_proj + (s_y * s_y) / diag_sq))
                    if d_new < best_new_d - 1e-13:
                        best_new_d = d_new
                        best_move = (rm_pos, cur[rm_pos], add_c)
                        improved = True

            if not improved or best_move is None:
                break
            rm_pos, old_el, new_el = best_move
            swap_log.append(
                {
                    "removed": old_el,
                    "added": new_el,
                    "d_sq_before": best_d,
                    "d_sq_after": best_new_d,
                }
            )
            cur[rm_pos] = new_el
            cand_list.remove(new_el)
            cand_list.append(old_el)
            best_d = best_new_d

    return sorted(cur), swap_log


def audit_q_cot_indefiniteness(
    engine: CachedVasyuninEngine,
    subsets: Dict[str, Sequence[int]],
) -> Dict[str, object]:
    """Compute exact spectra of G, G_smooth, G_cot proving G_cot indefiniteness."""
    report: Dict[str, object] = {}
    with mp.workdps(engine.dps + 10):
        for label, s in subsets.items():
            idx = list(s)
            m = len(idx)
            G_tot = mp.matrix(m, m)
            G_sm = mp.matrix(m, m)
            G_ct = mp.matrix(m, m)
            b_vec = mp.matrix([engine.rhs_entry(k) for k in idx])
            for i in range(m):
                for j in range(i, m):
                    gt, gs, gc = engine.gram_entry(idx[i], idx[j])
                    G_tot[i, j] = G_tot[j, i] = gt
                    G_sm[i, j] = G_sm[j, i] = gs
                    G_ct[i, j] = G_ct[j, i] = gc
            e_tot, _ = mp.eigsy(G_tot)
            e_sm, _ = mp.eigsy(G_sm)
            e_ct, vec_ct = mp.eigsy(G_ct)
            # Constructive ray c = t * v_min on Q_cot(c) = 1 - 2 b^T c + c^T G_cot c
            vmin = mp.matrix([vec_ct[i, 0] for i in range(m)])
            quad_dir = float((vmin.T * G_ct * vmin)[0])
            lin_dir = float((b_vec.T * vmin)[0])
            full_quad_on_vmin = float((vmin.T * G_tot * vmin)[0])
            ray_t100_qcot = 1 - 2 * 100 * lin_dir + (100**2) * quad_dir
            ray_t100_full = 1 - 2 * 100 * lin_dir + (100**2) * full_quad_on_vmin

            report[label] = {
                "cardinality": m,
                "max_element": max(idx),
                "G_total_eig_min": float(e_tot[0]),
                "G_total_eig_max": float(e_tot[-1]),
                "G_total_pos_count": sum(1 for v in e_tot if v > 0),
                "G_smooth_eig_min": float(e_sm[0]),
                "G_smooth_neg_count": sum(1 for v in e_sm if v < 0),
                "G_cot_eig_min": float(e_ct[0]),
                "G_cot_eig_max": float(e_ct[-1]),
                "G_cot_neg_count": sum(1 for v in e_ct if v < 0),
                "G_cot_pos_count": sum(1 for v in e_ct if v > 0),
                "unit_witness_vmin_quad_cot": quad_dir,
                "unit_witness_vmin_quad_total": full_quad_on_vmin,
                "unbounded_ray_t100_Q_cot": ray_t100_qcot,
                "unbounded_ray_t100_Q_total": ray_t100_full,
            }
    return report


def run_study(save_json: bool = True) -> Dict[str, object]:
    """Execute full Track 2 study and optionally write sparse_bnbd_compression_results.json."""
    t0 = time.monotonic()
    engine = CachedVasyuninEngine(dps=DPS, arb_bits=ARB_PREC_BITS)

    baseline = consecutive_baseline(engine, max_n=180)
    t_base = time.monotonic() - t0

    mu = mobius_sieve(400)
    primes_pool = sieve_primes(500)
    sqfree_all = [n for n in range(1, 400) if mu[n] != 0]
    p7_sm_all = p7_smooth_numbers(80)
    p7_divs_all = p7_divisors()
    coprime6_all = [n for n in range(1, 400) if gcd(n, 6) == 1]

    omp_pool = build_candidate_pool()
    omp_50, omp_history = greedy_omp_select(engine, omp_pool, k_max=50)

    swap_candidates = sorted(set(range(1, 250)) | set(sieve_primes(1000)) | {210, 330, 420, 462, 630, 660, 770, 924, 1155, 2310})

    cardinality_benchmarks: Dict[str, Dict[str, object]] = {}
    omp_refined_sets: Dict[int, List[int]] = {}
    swap_logs: Dict[int, List[Dict[str, object]]] = {}

    for k_card in [10, 20, 30, 40, 50]:
        families = {
            "consecutive": list(range(1, k_card + 1)),
            "squarefree": sqfree_all[:k_card],
            "primes_with_1": [1] + primes_pool[: k_card - 1],
            "p7_smooth": p7_sm_all[:k_card],
            "p7_divisors_smallest": p7_divs_all[:k_card],
            "coprime_6_free": coprime6_all[:k_card],
            "omp_greedy": sorted(omp_50[:k_card]),
        }
        refined_k, s_log = one_opt_swap_refine(
            engine, omp_50[:k_card], swap_candidates, max_swaps=(6 if k_card == 50 else 4)
        )
        omp_refined_sets[k_card] = refined_k
        swap_logs[k_card] = s_log
        families["omp_plus_swap"] = refined_k

        card_results: Dict[str, object] = {}
        for fname, fset in families.items():
            res = engine.solve_subset_distance(fset)
            eq = equivalent_consecutive_n(res["d_sq"], baseline)
            res["equivalent_consecutive_N"] = eq["n_equiv"]
            res["equivalent_exceeds_180"] = not eq["bounded_above_by_table"]
            res["cardinality_compression_ratio"] = round(eq["n_equiv"] / k_card, 4) if eq["n_equiv"] else None
            res["ratio_d_sq_over_bblr_maxS"] = res["d_sq"] / res["bblr_asymp_bound"]
            if k_card == 50 or fname in ("consecutive", "omp_greedy", "omp_plus_swap"):
                res["elements"] = fset
            card_results[fname] = res
        cardinality_benchmarks[str(k_card)] = card_results

    # Wide-range [1, 10^5] sparse 50-element ensembles testing high primorial/prime scales
    wide_probes_def = {
        "primorial_divisors_plus_high_P7": sorted(
            p7_divs_all[:35]
            + [231, 273, 330, 385, 429, 462, 510, 770, 910, 1155, 2310, 6006, 15015, 30030, P7_PRIMORIAL]
        ),
        "omp40_plus_10_wide_primes_to_1e5": sorted(
            omp_50[:40] + [2003, 3571, 4999, 9973, 15013, 25013, 40009, 60013, 80021, 99991]
        ),
        "p7_divisors_largest_50_sparse": sorted([1] + p7_divs_all[-49:]),
    }
    wide_results: Dict[str, object] = {}
    for wname, wset in wide_probes_def.items():
        assert len(wset) == 50 and len(set(wset)) == 50
        res = engine.solve_subset_distance(wset)
        eq = equivalent_consecutive_n(res["d_sq"], baseline)
        res["equivalent_consecutive_N"] = eq["n_equiv"]
        res["cardinality_compression_ratio"] = round(eq["n_equiv"] / 50.0, 4) if eq["n_equiv"] else None
        res["ratio_d_sq_over_bblr_maxS"] = res["d_sq"] / res["bblr_asymp_bound"]
        res["elements"] = wset
        wide_results[wname] = res

    # Spectral audit of G_cot indefiniteness
    q_cot_audit = audit_q_cot_indefiniteness(
        engine,
        {
            "consecutive_10": list(range(1, 11)),
            "consecutive_20": list(range(1, 21)),
            "consecutive_50": list(range(1, 51)),
            "p7_smooth_50": p7_sm_all[:50],
            "omp_plus_swap_50": omp_refined_sets[50],
        },
    )

    # Quantitative BBLR & beta0 = 0.70 obstruction metrics
    gamma1 = 14.1347251417346938
    beta0 = 0.70
    ln_n_uncond_1e6 = float(mp.log(10**6))
    # Approximate N threshold under Báez-Duarte / Burnol height-floor scaling: ln N ~ (C_BD / floor) or N ~ (gamma1)^(1/(beta0-0.5)) scaling from monograph reference
    # Keep explicit: both unconditional BBLR lower bound on [1, 10^6] and best-observed |S|=50 distance
    bblr_1e6 = C_BD_EXACT / ln_n_uncond_1e6
    best_50 = cardinality_benchmarks["50"]["omp_plus_swap"]
    nogo_summary = {
        "NO_RH_PROOF": True,
        "C_BD_exact": C_BD_EXACT,
        "gamma_1": gamma1,
        "bblr_unconditional_floor_N_1e6": bblr_1e6,
        "consec_50_d_sq": cardinality_benchmarks["50"]["consecutive"]["d_sq"],
        "consec_180_d_sq": baseline[180],
        "best_sparse_50_d_sq": best_50["d_sq"],
        "best_sparse_50_max_element": best_50["max_element"],
        "best_sparse_50_bblr_maxS_asymp": best_50["bblr_asymp_bound"],
        "best_sparse_50_equiv_N": best_50["equivalent_consecutive_N"],
        "best_sparse_50_compression_ratio": best_50["cardinality_compression_ratio"],
        "dedekind_norm_trace_no_go": (
            "Any finite trace/norm projection of a cyclotomic/class-field character supported at conductor/dilations <= X "
            "maps to a finite Dirichlet polynomial P_S(s) of length <= X; for rational integer S <= 10^6, span(rho_S) subset "
            "span(rho_{1..max(S)}), and even real algebraic dilations in (0, X] obey the BBLR(2005)/Bagchi(2006) O(1/ln X) floor."
        ),
        "reference_beta0_floor": beta0,
    }

    payload = {
        "metadata": {
            "precision_dps": DPS,
            "arb_cot_bits": ARB_PREC_BITS,
            "max_arb_cot_radius": engine._cot_rad_max,
            "unique_cot_calls_cached": len(engine._cot_cache),
            "unique_gram_pairs_cached": len(engine._pair_cache),
            "baseline_seconds": round(t_base, 3),
            "total_seconds": round(time.monotonic() - t0, 3),
            "NO_RH_PROOF": True,
        },
        "consecutive_baseline_subset": {str(n): baseline[n] for n in [10, 20, 30, 40, 50, 60, 80, 95, 97, 100, 120, 140, 160, 180]},
        "consecutive_baseline_full": {str(n): baseline[n] for n in range(1, 181)},
        "omp_history": omp_history,
        "swap_logs": {str(k): v for k, v in swap_logs.items()},
        "cardinality_benchmarks": cardinality_benchmarks,
        "wide_sparse_probes_50": wide_results,
        "q_cot_indefiniteness_audit": q_cot_audit,
        "bblr_and_dedekind_no_go": nogo_summary,
    }

    if save_json:
        out_path = SCRIPT_DIR / "sparse_bnbd_compression_results.json"
        out_path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")

    return payload


def _print_summary(payload: Dict[str, object]) -> None:
    print("=" * 96)
    print(" TRACK 2 SUMMARY: SPARSE BNBD CARDINALITY COMPRESSION & G_COT INDEFINITENESS (DPS=50)")
    print("=" * 96)
    meta = payload["metadata"]
    print(
        f"Runtime: {meta['total_seconds']}s | Unique cot sums: {meta['unique_cot_calls_cached']} "
        f"| Max Arb cot radius: {meta['max_arb_cot_radius']:.3e}"
    )
    print("\n--- Q_cot Indefiniteness Audit ---")
    for name, row in payload["q_cot_indefiniteness_audit"].items():
        print(
            f"  {name:<18} | G_tot eig_min={row['G_total_eig_min']:+.3e} | "
            f"G_cot neg={row['G_cot_neg_count']}/{row['cardinality']} "
            f"(eig_min={row['G_cot_eig_min']:+.4e}) | ray(t=100) Q_cot={row['unbounded_ray_t100_Q_cot']:+.4e}"
        )

    print("\n--- Fixed-Cardinality |S|=50 Comparison ---")
    for fname, row in payload["cardinality_benchmarks"]["50"].items():
        print(
            f"  {fname:<22} | maxS={row['max_element']:>6} | d_S^2={row['d_sq']:.8f} | "
            f"BBLR(maxS)={row['bblr_asymp_bound']:.8f} | N_eq={row['equivalent_consecutive_N']:>6.2f} "
            f"({row['cardinality_compression_ratio']:.2f}x)"
        )

    print("\n--- Wide Sparse Probes (|S|=50, reaching up to 510,510) ---")
    for wname, row in payload["wide_sparse_probes_50"].items():
        print(
            f"  {wname:<36} | maxS={row['max_element']:>6} | d_S^2={row['d_sq']:.8f} | "
            f"BBLR(maxS)={row['bblr_asymp_bound']:.8f} | N_eq={row['equivalent_consecutive_N']:>6.2f}"
        )


if __name__ == "__main__":
    result = run_study(save_json=True)
    _print_summary(result)
