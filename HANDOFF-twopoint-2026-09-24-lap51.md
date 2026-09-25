# HANDOFF twopoint — lap 51, 2026-09-25

Branch `wip/twopoint-avg`.  `src/NormalNumbers/TwoPointDelangeOmega.lean`, new section
"A SECOND ROUTE: the scale equation".  Green; both new theorems `#print axioms`-clean.

## A NEW ROUTE, and it looks like it closes

Laps 44–50 pushed the `v`-direction ODE to a single cancellation statement and stalled there.
**The scale direction is strictly better, for an arithmetic reason that has not been used before:**

* the `v`-direction equation `∂_v S = L·S + E` has multiplier `L = log log N` and, once normed,
  multiplier modulus `u = ‖z−1‖` — the refuted fixed point of lap 35;
* the **scale** equation has multiplier **`1 + (z−1) = z`, of modulus exactly one**, and its error
  is measured against `A(N) = Σ_{n≤N} μ²(n)u^{ω(n)}/n ≍ (log N)^u`, which is `o(log N)` **exactly
  in the repo's regime `u < 1`**.

### The equation
Both `Abel(N)` and `Σ_{p≤N}(log p/p)·S(N/p)` are the *same hyperbola sum* `Σ_{n≤N}(h(n)/n)log(N/n)`
— the first exactly, the second up to Mertens' error (`≤ 9 + log 2` per term, so `O(A(N))` in
total).  Feeding that into `delangeS_mul_log` (`S·log N = T + Abel`) and Levin–Fainleib
(`T = (z−1)Σ_p(log p/p)S^{(p)}(N/p)`, with `S^{(p)} → S` costing `O(A(N))` by lap 42's argument)
gives

    S(N)·log N  =  z · Abel(N)  +  R(N),      ‖R(N)‖ = O(A(N)) = O((log N)^u).

With `σ = log N`, `Y = Abel`, this is `σ·Y' = z·Y + R`, integrating factor `σ^{-z}` of modulus
`σ^{-Re z}`.  Hence `‖Y‖ ≲ σ^{Re z} + σ^{u}` and

    ‖S(N)‖ = ‖z·Y + R‖/σ  ≲  σ^{Re z − 1} + σ^{u−1}  →  0     for `Re z < 1` and `u < 1`.

**No bootstrap, no a priori bound on `‖S‖`** — the trivial `‖S‖ ≤ A` suffices, because the sign is
carried by the integrating factor `σ^{-z}` and is never normed.  Lap 35's refutation does not
apply: it normed the multiplier of the *`v`-direction* equation.

## Landed this lap
* `sum_log_telescope_Ico` — the Abel weights telescope on `[n, N)`.
* **`delangeAbel_eq_hyperbola`** — `Abel(N) = Σ_{n≤N}(h(n)/n)·(log N − log n)`, exactly.
* **`sum_primeWeight_delangeS_eq`** — `Σ_{p≤N}(log p/p)S(N/p) = Σ_{n≤N}(h(n)/n)·M(⌊N/n⌋)` with
  `M(x) = Σ_{p≤x} log p/p`, exactly.  (The set identity is
  `{p ≤ N : n ≤ ⌊N/p⌋} = {p ≤ ⌊N/n⌋}`.)

The two hyperbola forms are now side by side; comparing them is pure Mertens.

## Next, in order (each a self-contained brick)
1. `|M(⌊N/n⌋) − log(N/n)| ≤ 9 + log 2` for `n ≤ N` (`mertens_lower`/`mertens_upper` plus
   `log⌊x⌋ ≥ log x − log 2` for `x ≥ 1`), hence
   `‖Σ_p(log p/p)S(N/p) − Abel(N)‖ ≤ (9 + log 2)·A(N)`.
2. The scale equation `S(N)log N = z·Abel(N) + R(N)` with `‖R(N)‖ ≤ C·A(N)`, assembling 1 with
   `delangeS_mul_log`, `delangeT_eq_prime_sum` and `norm_delangeT_sub_primeSum_le`-style
   replacement (note: that lemma is stated with a uniform `B`; here use `A(N)` instead, which is
   monotone, so restate it as `≤ 16·A(N)`).
3. `A(N) ≤ C_u (log N)^u` — `delangeA_le_prod` (lap 36) gives `A(N) ≤ Π_{p≤N}(1+u/p)`; combine
   with `Π(1+u/p) ≤ exp(u·L) ≤ C(log N)^u` (needs Mertens' `Σ1/p = log log N + O(1)` in
   upper form, which `sum_inv_prime_sdiff_le` does not yet give — a dyadic sum of it does).
4. The discrete integrating factor: define `Z(N) = Abel(N)·(log N)^{-z}` and bound
   `‖Z(N+1) − Z(N)‖`, then sum.  This is the only genuinely new analytic step and it is the
   discrete analogue of `norm_delangeSv_le`, which is already in the file.

## Confidence
- `twoPointWeightedAvg_all` TRUE 90%, provable with known techniques 3% (C1 unchanged).
- `DelangeKernelMean`: 48% → **70%**.  The scale route has no unproved cancellation step left in
  its outline — only four elementary bricks, all of whose ingredients are already in the tree.
