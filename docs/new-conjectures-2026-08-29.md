# New-math conjecture slate — 2026-08-29 evening session 🔨🕸️

Forged per `HANDOFF-2026-08-29-next-lap-new-math.md` under the conjecture-graph objective
(DIRECTION.md): every candidate weighed by its probability of producing new mathematics about the
normality/disjunctivity of non-contrived constants.  Probes ran this session; Lean freezes are
next-lap work.  ⚠️ **Novelty status: unswept except where the 2026-08-29 lit sweep already
covers the claim** — "apparently new" is the ceiling until each gets its sweep.

Probes: `experiments/lntwo_wieferich_census.py`, `experiments/stoneham6_readout.py`,
`experiments/e_binary_runs.py` (all self-testing; all green 2026-08-29).

---

## N1 — the Wieferich forcing theorem + exclusion node (R3 assembly; census DONE) 🎯

**Forcing theorem (assembly of landed pieces — `zeroRun_res_eq_ceil`,
`lnTwoNum_modEq_fermatQuotient`, `occursAt_replicate_suffix`):** a zero-run of length `k` at
position `p−1` with `lcm(1..p−1) < 2^k` forces the Fermat-quotient congruence

> `q_p(2) ≡ w_p (mod p)`, where `w_p = (⌈latticeCenter (p−1)⌉·L⁻¹ + ⌊A/L⌋) mod p`

is explicitly computable (one-run version: candidate `⌈·⌉ − 1`).  A super-threshold run is a
**Wieferich-type coincidence**, per-p probability `~1/p`.

**Census result (p < 20 000, 2261 odd primes, exact big-int arithmetic, bridge re-verified
exactly for every p):** observed coincidences **5** vs model expectation **4.11** —
Poisson-consistent, the decorrelation model holds.  The run-Wieferich primes of ln 2 so far:

> one-run: `p = 3, 17, 151` · zero-run: `p = 509, 1279` · (Wieferich 1093, 3511 recovered as
> the `q_p(2) = 0` degenerate cases, neither coincident)

Every dyadic window `(n, 2n]` observed has ≥ 26/26, 73/73, 168/168 … non-coincident primes
available — the covering hypothesis is empirically comfortable.

**Node to freeze — `LnTwoQuotientMiss g N₀`:** for every `n ≥ N₀` there is a prime
`p ∈ (n, 2n]` with `q_p(2) ≢ w_p (mod p)` (both run types).
**Edge (wiring lap):** node ⟹ hypothesis-free-style run caps `≈ 5n` elementary (Nair
`lcm ≤ 4ⁿ`), `≈ 4.3n` with lcm asymptotics, via the Bertrand covering already proved
(`run_le_of_primeRunBound` pattern).

**Honest value ledger:** the conditional *constant* is worse than Marcovecchio's in-print
`2.57n` and our proved `9n`.  The value is **route independence**: the first run cap whose
input is a *checkable arithmetic exclusion family* (Fermat quotients) rather than Diophantine
approximation — a genuinely different wall crossing, strictly weaker than `LnTwoPrimeRunBound`
(it asks for one good prime per window, not all).  And the forcing theorem itself is
unconditional new mathematics per the sweep (surrogate-pigeonhole + per-n exclusion NOT FOUND).
**Multi-prime simultaneity is the deep part:** one run of length `~5n` at `n` covers `p−1` for
*every* prime in the window ⟹ forces `~n/log n` independent coincidences at once ⟹ heuristic
failure probability `e^(−c·n/log n)` per window, summable — the first mechanism in the program
suggesting super-polynomial suppression of linear runs from arithmetic alone.

Odds the node is true: ~99% (heuristic + census).  Odds the forcing theorem + node are new
mathematics: ~70% (sweep-backed).  Refutation probe: the census, extended (any window all of
whose primes go coincident kills the node shape).

## N2 — the Stoneham Rosetta stone: base-6 α₂,₃ reads out the 2-adic digits of 3^a 🪨

**Readout theorem (elementary, provable in one lap):** for `α = α_{2,3} = Σ 1/(3^k·2^(3^k))`,
`n ≥ 3`, with `k* = min{k : 3^k > n}`, `a = n − k*`, `c = 3^{k*} − n`:

> `|frac(6ⁿ·α) − (3^a mod 2^c)/2^c| ≤ 2·3^(a−1)/2^(3^(k*+1) − n)`  (exp-small in the block)

**Probe: verified to machine precision** — per-block max observed error equals the next-term
prediction *exactly* (block `k*=8`: observed `2^−2739`, predicted `2^−2739`).  Consequences,
both confirmed in the digit stream:

- **Bailey–Borwein 2012 nonnormality is the coarse shadow:** the zero-runs are exactly the
  block segments where `3^a < 2^c/6`; predicted run at block 8 = positions 2188–2543 (length
  356), observed `(2188, 356)` — exact.
- **Fine structure:** within a block, the base-6 digits of `α` replay the base-6 expansion of
  the single dyadic rational `2^−(3^k − k)` — equivalently the binary digits of `3^a mod 2^c`.
  All 216 length-3 base-6 words already present in 6560 digits.

**Node to freeze — `PowersOfThreeReadoutDense`:** every base-6 word occurs in the base-6
expansion of `2^−(3^k−k)` within the block window, for infinitely many `k`.
**Edges (elementary given the readout theorem):** node ⟺ `α₂,₃` is 6-disjunctive.

**Why this moves the needle:** it converts the disjunctivity of a *specific real* into pure
`×2×3` arithmetic — the distribution of powers of 3 in ℤ₂ — i.e. the SAME object family as
collatz-moonshot's wall (`3^a mod 2^c` is its native coordinate).  This upgrades the shared
Diophantine-wall interface (handoff target 2) from tool-sharing to **object-sharing**: a
refutation or advance on either side now transfers as mathematics, not as analogy.  Also the
cleanest possible exhibit for the landscape page: a constant provably 2-normal, provably
6-nonnormal, whose base-6 expansion is a *readout of powers of 3*.
⚠️ KB question [[stoneham-base6-disjunctive-probe]] ("is α₂,₃ 6-disjunctive?") becomes exactly
this node.

Odds the readout theorem is new *as stated*: ~50% (BB 2012 computed the same orbit; the
identity-as-theorem + disjunctivity equivalence appear unstated — sweep owed).  Odds the node
is true: ~90% (3 generates the maximal cyclic subgroup of `(ℤ/2^c)^×`; the staircase constraint
is the open part).  Refutation probe: extend the word census per block; a word class
systematically missing from readouts would kill density.

## N3 — e enters the machine: the threshold-kick (factorial) variant 🌿

ln 2's kick machinery was BBP-locked (base-2-aligned geometric series).  **e has no BBP
formula — but it has something better: factorial thresholds.**  Split `e` at
`M(n) := min{m : 2ⁿ < (m+1)!}`:

- **Surrogate:** `x_n = frac(2^(n−ν)·A(M)/odd(M!))` with `A(M) = Σ_{k≤M} M!/k!`
  (= `⌊e·M!⌋`, OEIS A000522) satisfying `A(M) = M·A(M−1) + 1` and the **rigidity**
  `A(M) ≡ A(M mod p) (mod p)` — the surrogate numerators are *periodic mod every prime*,
  where ln 2's harmonic numerators are the acknowledged wall.  Probe-verified.
- **τ-bracket:** `τ_n = 2ⁿ·Σ_{k>M} 1/k! ∈ [1/(M+1), 1 + 2/(M+1))`.  Probe-verified at
  `n = 100, 1000, 10000`.
- **Dichotomy (elementary, provable next lap):** a run of length `j > log₂(M(n)+1) + 1`
  forces `x_n` into a width-`2^(1−j)` window around the *moving* sliver `1 − τ_n (mod 1)`.
  Threshold `≈ log₂ n − log₂ ln n` — BELOW ln 2's `log₂(2(n+1))`.
- **Probe (200 000 bits of e):** record runs track `log₂ n` at ratio ≈ 1.0 (range 0.76–1.35,
  matching ln 2's 0.8–1.4); 20 sliver events in 200k positions — the random-like picture, with
  the sliver mechanism visibly the gate.

**Three qualitative advances over the ln-2 instance:**

1. **Every base at once.**  The factorial split works verbatim for `bⁿ·e` — the first
   constant with an all-base kick dichotomy (BBP machinery can never do this).  A step toward
   *absolute*-normality forcing statements.
2. **Diophantine side already maximal:** `μ(e) = 2` exactly (classical, CITED-class node
   `EMeasureTwo`) ⟹ runs `≤ (1+ε)n` — the sharpest linear run cap of any natural
   transcendental, and per the sweep pattern (π's `6.1n` exists only in grey literature) a
   careful statement is plausibly **first in print**.  The e-gap is `(1+ε)n` vs `log₂ n`:
   same wall shape as ln 2 with both sides tighter.
3. **Rigid arithmetic door:** the e-analogue of N1's exclusion has its arithmetic side fully
   *computable* (`A(M) mod p` periodic) instead of resting on unknowns like `q_p(2)` — the
   open question with real new-math odds: does rigidity make any sparse-position exclusion
   *provable*?  (For ln 2 the analogous quantities are conjecturally random; for e they are
   theorems waiting to be exploited.)

**Family bonus:** the machine extends to the whole factorial-kick class — `e^(1/q)`, `cosh 1`,
`sinh 1` (nonneg kicks), and via the D15 signed layer `sin 1`, `cos 1`.  A class theorem
("every E-function-flavored series value has an all-base log-run dichotomy") is paper-shaped.

Lean surface next lap: `EFactorialSliver` (theorem, not node — all elementary),
`EMeasureTwo` (CITED node) + run-cap edge, node `EDerangementMiss` (exclusion family).
Odds the structure theorems are new: ~75% (no BBP ⟹ no BC-descendant coverage; sweep owed on
the "binary digits of e" literature).  Refutation probe: ran green (this session).

## N4 — the graded discrepancy ladder (the alien's socket, made concrete) 📐

Node family **`LnTwoDiscrepancyGraded f`**: the discrepancy of `{lnTwoOrbit k}_{k<N}` is
`≤ N/f(N)` eventually.  Edge family (Erdős–Turán, formalizable lane-2): `f`-graded discrepancy
⟹ every word of length `≲ log₆ f(N)`-ish occurs with positive frequency — an **interpolating
ladder** between disjunctivity (`f` slowly growing) and full normality (`f` linear/N^ε),
giving the option-4 charter ("weaken equidistribution, keep a digit conclusion") its
quantitative rungs.  `f = ∞` recovers `Equidistributed lnTwoOrbit`; each finite rung is a
strictly weaker sink-adjacent node.  Wall-class truth, architecture-level value; pairs with a
dischargeable Erdős–Turán edge per the anti-rung-minting ratio.  Probe design: compute
`D_N(lnTwoOrbit)` to `N = 10⁶` (expect `~√N·polylog` — random-like); any anomalous plateau
would be a finding in itself.

## N5 — flag: BLMV is a donor theorem adjacent to this sink 🛸

Bourgain–Lindenstrauss–Michel–Venkatesh (2009, effective ×2×3 equidistribution) applies to
points with finite irrationality measure — **ln 2 qualifies via Marcovecchio**.  So an
unconditional, *effective* density statement for `{2^a·3^b·ln 2 mod 1}` exists in the
literature, one multiplicative degree of freedom away from the sink orbit `{2ⁿ·ln 2}`.
Owed before any node freeze: a proof-level read (does the effective window reach the diagonal
`a = b` regime? almost certainly not — but the *gap between BLMV's reach and the diagonal* is
then the precisely-named obstruction, and N2's readout gives the same `×2×3` object a second
door).  CITED-class candidate only after the read.

---

## Negative finding (recorded so nobody re-derives it) 🧯

**The CRT-stacking route to a `√n` unique-candidate threshold dies at quotient opacity.**
The elementary short-sum formula gives `A_n mod p` for every `p ≤ n` (probe-verified —
self-test 4), and `ψ(n) − θ(n) = O(√n)` would then pin the numerator with only `~1.44√n` run
bits *if* residues of `lnTwoRes n` were accessible.  They are not: `lnTwoRes = A − L·s` with
`s = ⌊A/L⌋ ≈ ⌊2ⁿ·ln 2⌋` — **the quotient IS the digit prefix**, so every mod-p handle on the
res re-imports the unknown it was meant to constrain.  Conservation of difficulty, exactly as
Lagarias's Remark-1 acid predicts.  Clean reframing that survives: *for every prime `p ≤ n`,
the run event at `n` forces one mod-p checksum linking ln 2's first-n-bits integer to
elementary arithmetic* — the checksum-coincidence picture behind N1's multi-prime
simultaneity.  Only at `n = p−1` (Glaisher) does the checksum connect to an independently
studied quantity; that is why N1 lives there.

## Ranking (novelty-weighted, per the doctrine) 🥇

1. **N1** — the ranked handoff target, now probe-armed; assembly is one wiring lap over
   landed theorems, then the contrapositive node freeze.  Best value per lap.
2. **N3** — new constant, new machine variant, all-base firsts, and the rigid-arithmetic
   door; the structure theorems are a single self-contained lap.
3. **N2** — one elementary theorem turns a KB open question into a frozen node and makes the
   two-repo wall object-shared.
4. **N4** — freeze alongside whichever of the above lands first (rung + dischargeable edge).
5. **N5** — read first, cite later.

De-prioritized: more kicked-machine BBP instances (stamp-collecting, per the handoff);
the kick-decay classification law (disagreement counts `~(log N)^s`) — fold into N3's family
paper as a probe, not a campaign.
