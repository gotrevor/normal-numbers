# HANDOFF twopoint — lap 40: **MERTENS' FIRST THEOREM (lower half) PROVED**

Branch `wip/twopoint-avg`.  Extends `src/NormalNumbers/TwoPointMertensLower.lean` (sorry-free,
trust-triple).

## The advance

**`mertens_lower`** — for every `N ≥ 1`,

    Σ_{p ≤ N} (log p)/p  ≥  log N − 9 ,

with an explicit absolute constant and an entirely elementary proof.  This is a genuinely new
theorem for the tree: the repo previously had only the crude *upper* bound
`mertens_crude : Σ_{p≤N} log p/p ≤ 4 log N`.

Supporting lemmas landed this lap:
| lemma | content |
|---|---|
| `log_factorial_eq_sum` | `log(N!) = Σ_{n=1}^{N} log n` |
| `log_factorial_eq_prime_sum` | `log(N!) = Σ_{p≤N} v_p(N!)·log p` (Legendre, via `Nat.prod_factorization_pow_eq_self`) |

The double count, every link now a theorem:

    N log N − N  ≤  log(N!)                              `log_factorial_ge`         (lap 38)
                 =  Σ_{p≤N} v_p(N!)·log p                 `log_factorial_eq_prime_sum`
                 ≤  Σ_{p≤N} (N/(p−1))·log p               mathlib `factorization_factorial_le_div_pred`
                 =  N·Σ(log p)/p + N·Σ(log p)/(p(p−1))
                 ≤  N·Σ(log p)/p + 8N                     `sum_log_div_mul_pred_le`  (lap 39)

Divide by `N`.  No integrals, no zeta function, no PNT — `log x ≤ x − 1` and three telescopings.

## Where this lands the campaign
Part II of the complex Wirsing step (lap 37) required exactly this input.  The remaining pieces of
part II are the interchange arguments:
1. `S^{(p)}(M) → L/(1+(z−1)/p)` as `M → ∞` for each fixed `p` — follows from `delangeSrestr_rec`
   (lap 34) plus boundedness of `S`;
2. the weight mass `Σ_{p≤N} log p/p ~ log N` concentrates on large `p`, so the weighted average of
   `L/(1+(z−1)/p)` tends to `L`.  `mertens_lower` + `mertens_crude` bracket the mass;
3. conclude `T(N)/log N → (z−1)L`, and with lap 37's `T(N)/log N → 0` get `(z−1)L = 0`, hence
   **`L = 0`**.

Then `DelangeKernelMean` ⟺ "`S` converges", which is the genuine Tauberian wall.

## Run to date
lap 28 `92ede26` · 29 `ab283df` · 30 `2d4d2c3` · 31 `6775ae3` · 32 `f29262a` · 33 `3019208` ·
34 `32cc493` · 35 `d847b72` · 36 `f34b636` · 37 `ecfc5b6` · 38 `60f455a` · 39 `f0dd52e` · 40 (this).

The C1 crux itself remains measured and pinned (lap 31 equivalence, lap 32 invariance) — the
kickoff's success criterion.

## Confidence
- `twoPointWeightedAvg_all` TRUE 90%; provable with known techniques 3%.
- Part II completable in 1–2 laps: **65%**.
- Full `DelangeKernelMean` in this run: **15%** (convergence of `S` is the wall, unchanged).
