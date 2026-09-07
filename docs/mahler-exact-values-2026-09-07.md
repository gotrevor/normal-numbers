# Exact `M(g,1)` for `g = 2 … 31` — the census, and three findings 🧮

Host session, 2026-09-07.  Instrument: `experiments/mahler_exact_M.py` (the
incremental trimmed-product SCC algorithm already in this repo), run over every
digit `W < g` and maximised.  The repo previously held only
`experiments/mahler_exact_M_k1_g14plus.txt` (`g = 14 … 29`); this run adds
`g = 2 … 13` and `g = 31`, and puts the whole table in one place.

## The census

| `g` | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 | 13 | 14 | 15 | 16 |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| `M(g,1)` | 1 | 2 | 6 | 6 | 20 | 9 | 28 | 24 | 72 | 25 | 99 | 35 | 104 | 126 | 120 |

| `g` | 17 | 18 | 19 | 20 | 21 | 22 | 23 | 24 | 25 | 26 | 27 | 28 | 29 | 31 | 32 |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| `M(g,1)` | 64 | 272 | 80 | 304 | 224 | 336 | 120 | 414 | 189 | 400 | 375 | 500 | 192 | 224 | 588 |

(`g = 30` is not yet computed — it is the running probe for Finding 3.)

📉 **Neither sequence is in OEIS** (checked 2026-09-07 against the live search
API): not the full `1,2,6,6,20,9,28,24,72,25,99,35` and not the prime
subsequence `6,9,25,35,64,80,120,192`.  ⚠️ Evidence tier: an OEIS null is a
*single-instrument* negative — it licenses "we found no prior tabulation", never
"nobody has computed these".

## Finding 1 — the divisor bound is exact at `g = 2,4,8,16` and **REFUTED at 32**

`MahlerLowerBoundGeneral.lean` proves `t(gᵏ − 1) ≤ M(g,k)` for every
factorization `g = t·c`, `c ≥ 2`.  At `g = 2ʲ` the best choice is `t = g/2`:

| `g` | 2 | 4 | 8 | 16 | **32** |
|---|---|---|---|---|---|
| `2^(j−1)(2ʲ − 1)` | 1 | 6 | 28 | 120 | 496 |
| `M(g,1)` | **1** | **6** | **28** | **120** | **588** |

Four for four, then it breaks.  The conjecture `M(2ʲ,1) = 2^(j−1)(2ʲ − 1)` was
stated and **refuted the same session** by the `g = 32` computation
(796 s; per-digit maximum at digits `0` and `31`, symmetric as
`blockNatVal_map_reflect` requires).  The agreement at `j ≤ 4` — and equally at
`g = 3` (`1·2 = 2`) and `g = 9` (`3·8 = 24`) — is a **small-base coincidence**,
not a family.  It already failed at `g = 25` (`M = 189` vs `5·24 = 120`) and
`g = 27` (`M = 375` vs `9·26 = 234`); `g = 32` shows the `2ʲ` line is no
different, it just took longer to separate.

📌 **What this buys**: the divisor construction is *not* asymptotically optimal
at any base family we can currently name, so the true `M(g,1)` needs a
construction the repo does not yet have.  The `2ʲ` ratios
`M/g²` = `.250, .375, .438, .469, .574` are climbing **through** the `1/2` that
`(g/2)(g−1)/g²` tends to — which is the substance of Finding 3.

## Finding 2 — prime bases sit at `⌊p/2⌋²`, one or two short

| `p` | 5 | 7 | 11 | 13 | 17 | 19 | 23 | 29 | 31 |
|---|---|---|---|---|---|---|---|---|---|
| `M(p,1)` | 6 | 9 | 25 | 35 | 64 | 80 | 120 | 192 | 224 |
| `⌊p/2⌋²` | 4 | 9 | 25 | 36 | 64 | 81 | 121 | 196 | 225 |
| deficit | −2 | 0 | 0 | 1 | 0 | 1 | 1 | 4 | 1 |

`M(p,1)/p²` = .240, .184, .207, .207, .221, .222, .227, .228, .233 — climbing
toward the `1/4` that the denominator-jump engine (`MahlerFarey.lean`,
`PENDING_WORK.md` §top) reaches from above.  `⌊p/2⌋²` is exactly the value at
the engine's double root `a = Q/2`, so the two sides agree on the *shape*, not
merely the order.  `p = 5` is the only base where `M` **exceeds** `⌊p/2⌋²`.

## Finding 3 — the universal constant lives at composite bases, not prime ones

`M(g,1)/g²`, sorted: the record is **`g = 18` at `0.840`** (`272/324`), then
`g = 20` (`.760`), `g = 24` (`.719`), `g = 10` (`.720`), `g = 22` (`.694`).
Every prime base is near `0.22`.

⚠️ **Consequence for the DIRECTIVE.**  The mandated crux — the prime-base upper
bound — cannot move the universal constant at all: it operates in the regime
where the ratio is `0.22`, four times below the current record.  The two are
disjoint questions and the repo's headline claim (universal `≥ 0.840`, against
B–B's `2`) is driven entirely by bases the crux does not touch.  The bases that
drive it look highly composite with `g − 1` prime (6, 10, 18, 20); `g = 30`
(`2·3·5`, `29` prime) is the natural next probe.

## Where primality enters the existing proof — one lemma, shared with the crux

`MahlerPrimeHalf.mahler_multiplier_prime_half` needs `g.Prime` through exactly
one link: `MahlerRunBranch.isCoprime_of_emod_pos (hg : g.Prime)`, which turns
`A % g ≥ 1` into `IsCoprime A g`.  That implication is *false* at `g = 2ʲ`
(`A = 2`, `g = 8`).  The repair — a `gcd`-aware `cell_hit_of_coprime` that works
at the reduced denominator `gᵏ / gcd(A, gᵏ)` — is the SAME denominator-aware
multi-scale invariant `DIRECTION.md` already names as the attack on the prime
crux.  Conjecture P2 and the mandated crux therefore share one missing lemma;
they are not competing threads.

## Reproduction

    python3 - <<'EOF'
    src = open("experiments/mahler_exact_M.py").read().split('if __name__=="__main__":')[0]
    mx={}; exec(compile(src,"m","exec"), mx)
    for g in range(2, 33):
        print(g, max(mx['M_W'](g,1,(W,))[0] for W in range(g)), flush=True)
    EOF

Cost: `g = 29` ≈ 140 s, `g = 31` ≈ 199 s, growing fast; budget accordingly.
