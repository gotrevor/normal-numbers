# The hitting-set invariant `S(g,k)` — first data, prior art, and what to prove 🎯

*Host thread opened 2026-09-13 (Fable) after the CC/NN review; instrument
`experiments/mahler_hitting_set.py` (this branch).  Status: new invariant, exact data through the
automaton's reach, one conjecture already refuted, no theorem yet.*

## Definition

For a base `g ≥ 2` and block length `k ≥ 1`, a finite set `S ⊂ ℕ_{≥1}` is a **per-block hitting
set** if for every irrational `α` and every `k`-block `w` some `m ∈ S` has `w` occurring infinitely
often in the base-`g` expansion of `m·α`.  `S` is a **disjunctive hitting set** if for every
irrational `α` some single `m ∈ S` has *every* `k`-block occurring infinitely often in `m·α`.

```text
S(g,k)  = min |S| over per-block hitting sets,      S*(g,k) = min |S| over disjunctive ones.
```

Contrast `M(g,k)` (`docs/mahler-exact-values-2026-09-07.md`): the least `M` such that the initial
segment `{1..M}` is a hitting set.  `S(g,k) ≤ S*(g,k) ≤ M(g,k) < g^(k+1)` (`Mahler.mahler_multiplier_lt`).

**Scaling.**  Replacing `α` by `α/m₁` shows the property depends only on the *ratios* `m/m₁`: the
invariant is really about finite sets of positive rationals containing `1`.  In particular a single
multiplier never suffices once `g^k ≥ 3` (take `α = β/m` with `β` avoiding a block).

## Instrument

`mahler_exact_M.py`'s channel-product adder automaton, run on an arbitrary set `S` instead of
`1..M`: a block `w` is hit iff the trimmed product of the channel graphs `(m, w)`, `m ∈ S`, has no
nontrivial SCC (a lone cycle is one eventually periodic digit string, i.e. a rational, and is
trimmed; a branching SCC is uncountably many escaping irrationals).  Disjunctive: every
assignment `m ↦ w_m` must collapse.  Selftest: `S(3,1) = 2`, `{1,2}` and `{2,11}` both hit, `{1}`
does not, `S(2,1) = 1`.  Reach (measured 17:20, the earlier "five channels too large" line was
never measured and was wrong): the trimmed products are tiny - ≤ 160 states for five multipliers
≤ 13 at `(2,4)`, ≤ 170 for `{11,23,41,59}` at `(2,3)` - and take milliseconds; the cost is the
number of subsets `C(mmax, s)`, never the product.  `minimal_hitting_layered` adds subset
monotonicity (a set inherits every block a proper subset hits; `c·S ≡ S` by scaling) and
reproduces the naive controls; the naive short-circuit search stays faster for the top layer.

## Data (exact, 2026-09-13; "unique" means unique among sets within the searched range)

| `(g,k)` | `S(g,k)` | minimal sets found | `S*(g,k)` | disjunctive sets | searched |
|---|---|---|---|---|---|
| (2,1) | 1 | `{1}` | 1 | `{1}` | – |
| (3,1) | 2 | **12 channel-distinct pairs ≤ 40** (162 naive), incl. `{1,2}` (B–B) and `{2,11}` (tower C2) | 2 | **`{2,11}` unique ≤ 20**; `{1,2}` is per-block only | pairs ≤ 40 / ≤ 20 |
| (4,1) | 3 | **2 channel-distinct triples ≤ 60**: `{1,10,14}`, `{2,5,7}` (the naive 35 are these with 4-multiples and scalings, e.g. `{3,30,42} = 3·{1,10,14}`) | > 3 | – | sizes ≤ 3, ≤ 60 |
| (5,1) | **5** | **272 channel-distinct sets ≤ 30** (2008 naive), e.g. `{1,2,3,4,6}`, `{1,2,3,4,8}`, `{1,2,3,6,14}` | – | – | sizes ≤ 5, ≤ 30 |
| (6,1) | **7** | **2 channel-distinct sets ≤ 24**: `{1,8,11,14,16,20,23}`, `{3,7,10,13,14,17,20}` (the other two naive ones carry `6·1`, `6·3`); no 6-set ≤ 24 | – | – | sizes ≤ 7, ≤ 24 |
| (7,1) | **7** | **3 channel-distinct 7-sets ≤ 24**: `{1,2,3,4,5,6,13}` (**theorem** `hitting_7_1_seven`, `HittingSetBase7.lean`, chunked kernel decide, verified 23:16), `{1,3,4,5,6,9,13}`, `{1,3,4,5,6,9,18}`; `{1,…,6,8}` does NOT hit (digits 1 and 5 escape); `{1..8}` and `{1..6}` fail as theorems (`not_hitting_7_1_eight`, `not_hitting_7_1_six`) | – | – | sizes ≤ 7, ≤ 24 |
| (8,1), (9,1) | > 8 | – | – | – | sizes ≤ 8, ≤ 20 (cap probably binding) |
| (10,1) | > 9 | – | – | – | sizes ≤ 9, ≤ 20 (cap probably binding) |
| (2,2) | 2 | **3 channel-distinct pairs ≤ 60**: `{1,3}`, `{1,11}`, `{3,5}` (151 naive, with 2-multiples and scalings) | 3 | `{1,3,5}` | ≤ 60 / ≤ 30 |
| (2,3) | 4 | **2 channel-distinct 4-sets ≤ 60**: `{1,3,5,7}`, `{1,5,7,11}` (the naive 928 are these with elements doubled: `{1,3,5,14}` is `{1,3,5,7}`, channel 14 = channel 7 shifted) | > 4 (`{1,3,5,7}` fails) | – | sizes ≤ 4, ≤ 60 (naive, 2 h 38 min) |
| (2,4) | **9** (within ≤ 40) | **`{1,3,5,7,9,11,13,15,17}`, the first nine odd numbers, is the only channel-distinct 9-set ≤ 40** (930 s); `{1,3,…,15}` does NOT hit, nor any 8-set ≤ 40 (196 s; 1297 sparse survivors, all fail at `0000`). Size 8 at cap 60 running; N5 gives `≥ 8` | – | – | sizes ≤ 9, ≤ 40 |
| (3,2) | **6** | **1 channel-distinct set ≤ 20**: `{1,2,4,5,7,8}` (42 naive; `{1,4,5,6,7,8}` is it with `6 = 3·2`) | – | – | sizes ≤ 6, ≤ 20 |

Read along rows: `S(g,1) = 1, 2, 3, 5, 7, >6, >8, >8, >9` for `g = 2..10`; `S(2,k) = 1, 2, 4, >7`
for `k = 1..4`; `S(3,k) = 2, 6`.  The tempting conjecture that the odd multipliers below `2^k`
realise `S(2,k) = 2^(k−1)` is **refuted at `k = 4`**, but the value `8` is not.  `S(6,1) = 7` is
the first value above `g`; base 8 (a prime power) is already `> 8`, so no "prime power vs two
primes" reading.  **Growth heuristic (Fable, 19:50)**: each multiplier deletes about a fraction
`g^(−k)` of the product automaton's edges and branching survives until a constant fraction is
gone, so `S(g,k) ≍ g^k` - the order of Mahler's `g^(k+1)`; every entry above is consistent.
Whether `S(g,k)` is even unbounded in `k` is open: B–B 95 Cor 3.3 does not settle it, and every
adversary we have (sparse, background+burst, local lemma) is limited to multipliers with about
`g^k` digits - the analysis is in the KB leaf `moonshot-review-2026-09-13.md` §7.20.  Every ">" is a search cap on the
multipliers, never a theorem; every exact value's upper half is exact (a hitting set is a finite
automaton verdict).

**Recount (21:50, `experiments/hitting_set_search.py`).**  "Channel-distinct" means elements not
divisible by `g` (channel `g·m` is channel `m` shifted) and `gcd = 1` (`c·S` hits iff `S` does);
the naive counts above in parentheses include those redundancies.  The earlier "unique ≤ 40"
entries were early-exit runs (`mahler_hitting_set.py` stops at the first set unless `--all`),
not counts, and are withdrawn.  The new instrument also prefilters with sparse-adversary
bitmasks (`B ≤ 2^15`) and runs the automaton on the survivors, constant blocks first; the
(7,1) size-7 run took 88 s where the naive one would have taken hours.

### Initial segments and the base channel (21:10)

Channel `g` is channel `1` shifted one place (`gα` and `α` have the same digit sequence), so any
hitting set may be taken with `g ∤ m`; in particular `{1..M(g,1)}` minus `g` hits, which gives
`S(g,1) ≤ M(g,1) − 1` (the exact `M(g,1)` for prime `g` is in `src/NormalNumbers/MahlerPrimeLowerBound.lean`).
Base 5's `{1,2,3,4,6}` is exactly this, and at base 7 the two 8-subsets of `{1..9}` that hit
are `{1..9}∖{7}` and `{1..9}∖{1}` - the same channel set - while no 7-subset of `{1..9}`
hits.  The guess that the base-5 pattern `{1..p−1, p+1}` hits at every prime is **false at
`p = 7`**: `{1,…,6,8}` leaves digits 1 and 5 unhit.  The size-7 search below 24 (21:50, new instrument) found three 7-sets, so **`S(7,1) = 7`**:
`{1,2,3,4,5,6,13}`, `{1,3,4,5,6,9,13}`, `{1,3,4,5,6,9,18}` - again `{1..p−1}` plus one element,
but `13 ≡ 6 (mod 7)`, not `p+1`; and at base 5 the extra element `6 ≡ 1`.  For `S(11,1)` the same argument gives
`≤ 24`, surely far from tight.

## Sparse adversaries: an elementary lower-bound route (`experiments/mahler_sparse_adversary.py`)

For `α = Σ_j B_j g^(−n_j)` with growing gaps, the digits of `m·α` are the digit strings of the
integers `m·B_j` padded by zeros, so a block `W ≠ 0^k` occurs finitely often in `m·α` iff `W` is
eventually absent from `0^(k−1)·digits_g(m B_j)·0^(k−1)`.  Hence **if some `W ≠ 0^k` is avoided by
all of `m·B`, `m ∈ S`, for a single `B ≥ 1`, then `S` is not a hitting set** (take `B_j = B`; the
growing gaps make `α` irrational; B–B 94 §3 is `B = 1`).  An earlier draft asked for infinitely
many `B` - one suffices, so "defeated" below means "has an avoider `≤ 4096`".  Sound relative to the automaton: on every set the probe visits with `--check`, each
`(S, W)` the sparse family defeats is also "not hit" by the automaton (no assertion fired).
Counting avoiders `B ≤ 4096`:

| case | primitive sets | defeated by a sparse family | thinnest |
|---|---|---|---|
| (4,1) pairs ≤ 60 | 1101 | **all** | `{30,49}`: 11 avoiders of digit 1 |
| (2,3) triples ≤ 40 | 8410 | **all** | `{21,35,39}`: 23 avoiders of `111` |
| (2,4) quads ≤ 20 | 4619 | **all** | `{1,9,13,15}`: 492 avoiders of `1111` |
| (3,2) quads ≤ 20 | 4619 | **all** | `{1,11,14,17}`: 81 avoiders of `22` |
| (5,1) quads ≤ 30 | 25819 | 22962; **2857 undefeated**, e.g. `{1,2,3,4}`, `{1,2,4,8}` | `{4,7,12,28}`: 1 avoider |

So the lower bounds `S(4,1) ≥ 3`, `S(2,3) ≥ 4`, `S(2,4) ≥ 5`, `S(3,2) ≥ 5` each reduce, within the
searched multipliers, to a statement about **digit-avoiding common multiples**.  The base-5 bound
does not, and the reason is a lemma:

**Lemma (prime base, `k = 1`; proved 2026-09-13).**  Let `p` be prime and write `m'` for the
`p`-free part of `m`.  If `{m' mod p : m ∈ S} = (ℤ/p)^×`, then `S` has no sparse adversary.
*Proof.*  The last nonzero base-`p` digit of `m·B` is `m'·B' mod p`, and `B'` is a unit, so the
last nonzero digits of `{m·B : m ∈ S}` run over every nonzero residue for every `B`. ∎
Check: the 2857 quads `≤ 30` with no avoider `≤ 4096` are **exactly** the 2857 residue-covering
quads (both inclusions, computed).  **Conjecture (converse).**  If the `p`-free residues of `S`
miss a nonzero class, `S` has a sparse adversary.  Evidence: every non-covering quad `≤ 30` at base
5 (22962 sets) and 391 of 391 random non-covering 5-sets `≤ 40` at base 7 have an avoider `≤ 4096`.
**Consequence if true: `S(p,1) ≥ p − 1` for every prime `p`** (a set of `p − 2` elements misses a
class).  Tight at `p = 2, 3`; not at `p = 5`, where `S(5,1) = 5`: the residue-covering 4-sets are
defeated only by dense adversaries the automaton exhibits.

**Kill test (19:35): the converse is FALSE as stated.**  Take base 5 and `S` = every `m ≤ 30`
whose 5-free residue is not 4 (23 elements, one missing class): no `B ≤ 10^6` avoids the forced
digit `4·B' mod 5` in every `m·B` (independent code paths agree below 4096), and the random-`B`
heuristic `BMAX·(4/5)^(|S|·digits) ≈ 10^6·10^(−20)` says none exists at all.  Same at base 7
(all `m ≤ 40` with residue `≠ 3`, 33 elements) and base 3 (30 elements).  The residue criterion
is only *necessary* for a sparse adversary; sufficiency fails once `|S|` is large.  What survives
is the version the bound needs, **N4′: every `S` with `|S| ≤ p − 2` has a sparse adversary**
(true for all triples `≤ 30` at base 5 - subsets of defeated quads - and 391 random 5-sets `≤ 40`
at base 7).  The random-`B` heuristic for `|S| = p − 2` dies at roughly 20 base-`p` digits per
element, so beyond that N4′ needs a *structured* `B`; a probe on random small sets of large
elements is in `scratchpad/n4_edge_test.py` (results in the KB leaf §7.19).

## Holes: the dynamical reformulation, and conjecture N5 (21:30)

Write `T t = g·t mod 1` and, for a multiplier `m` and a `k`-block `w`,
`H(m,w) = { t ∈ [0,1) : the first k digits of frac(m·t) are w }` - `m` intervals of length
`g^(−k)/m`, equally spaced.  Since the digit of `mα` at position `n+1` is the first digit of
`frac(m·Tⁿα)`, **`w` occurs infinitely often in `mα` iff the `T`-orbit of `α` enters `H(m,w)`
infinitely often**, and

> `S` hits `w`  ⟺  the survivor set `{ t : Tⁿ t ∉ ⋃_{m∈S} H(m,w) for all n ≥ 0 }` contains no irrational.

So `S(g,k)` is a question about open dynamical systems (`×g` with a hole that is a finite union of
intervals), where there is a literature: Urbański 1986 (dimension of the survivor set of `×g` with
an interval hole), Glendinning–Sidorov 2015 (the doubling map with a hole `(a,b)`: the survivor set
is uncountable iff the hole is short enough, thresholds at Thue–Morse-type points),
Bunimovich–Yurchenko 2011 (holes containing short periodic orbits leak *slowest*).

*Literature pass (21:55, abstracts only, arXiv 1302.2486 and 0811.4438):* Glendinning–Sidorov
characterize completely, for the doubling map with **one** hole `(a,b)`, when the survivor set
is nonempty / infinite / uncountable of dimension zero / of positive dimension, and prove that
positive dimension holds whenever `b − a < ¼·∏_{n≥1}(1 − 2^(−2^n)) ≈ 0.175092`, sharp.
Bunimovich–Yurchenko: among holes of equal measure in a strongly chaotic map, the escape is
fastest through the hole whose minimal-period periodic point has the *largest* period - so a hole
containing a fixed point leaks slowest, which is the qualitative reason the constant blocks `d^k`
(whose holes `H(1, d^k)` contain the fixed point `d/(g−1)`) are the binding blocks in every row.
Neither result covers a hole that is a union of `m` equally spaced intervals, let alone the union
over a set `S`; the one-interval theory does not transfer, and the symbolic description of our
holes is exactly the product automaton.  So the literature supplies the right *frame* and the
qualitative reading, not a theorem for N5.

*Full read of Glendinning–Sidorov (22:20, sub-agent; notes in
`papers/glendinning-sidorov-2015-doubling-map-asymmetrical-holes.md`):* the deep machinery
(extremal pairs, the substitutions `ρ_r`, balanced words, the `0.175092` threshold from
period-doubling, Thm 2.13 / Cor 3.9) is welded to a single hole straddling the discontinuity
`1/2` and does not transfer to `⋃_m H(m,w)`.  What transfers is the shallow layer, Lemma 1.1(ii):
positive dimension is shown by exhibiting a positive-entropy SFT inside the survivor set.  For
holes with rational endpoints, which every `H(m,w)` has, the survivor set is sofic, so "`S` hits
`w`" is equivalent to zero entropy, to zero Hausdorff dimension, and to only finitely many
periodic survivors; that is precisely what the trimmed product automaton decides, so the two
pictures are one.  Two negatives worth keeping: (a) `J(S,w) = ⋂_m M_m^(−1)(X_w)` is an
intersection of pullbacks of the `w`-free SFT under `t ↦ mt`, all `×g`-invariant, so no
transversality theorem applies and the obstruction to N5 is channel correlation; (b) a bound of
the form "N intervals each shorter than c/N gives positive dimension" is false: unavoidable sets
of `n`-words of size `≈ 2^n/n` (Mykkeltveit 1972, cited from memory in the notes, not opened)
give cylinder holes of measure `≈ 1/n` with empty survivor set.  So N5, if true, is a statement
about the multiplier structure of the holes, not about their measure.  Closest paper: Allaart–Kong
arXiv 2411.03516 §8 (`kx mod 1` with `k−1` equal holes at the discontinuities), not our geometry.

Both adversary families in this repo are one object in this picture: an **`H`-free periodic orbit
plus a landing strip**.  The sparse adversary hugs the fixed point `0` and makes the excursion
`B·g^(−J), B·g^(−J+1), …` (the digits of `mB`); Mahler's `a/(g−1) + Σ c·g^(−i!)` hugs the fixed
point `a/(g−1)` and makes the excursion `a/(g−1) + c·g^(−i)`, `i = J, …, 1`, which returns *exactly*
to the fixed point.  Any `H`-free periodic orbit `P/(g^ℓ−1)` with an `H`-free excursion gives an
irrational escape; the residue lemma says which fixed point (`0`) has no landing strip at a prime
base when the residues cover.

**Mean-field count.**  `s` holes of measure `g^(−k)` each remove at most `s·g^(−k)` of the circle;
for a hole made of *random* depth-`n` cylinders the survivor set has entropy
`≈ log g + log(1 − μ)`, positive iff the complement `1 − μ` exceeds `1/g`, i.e. iff
`s < (g−1)·g^(k−1)`.  Hence

> **N5.**  `S(g,k) ≥ (g−1)·g^(k−1)`.

Data: `(g−1)g^(k−1)` is `1, 2, 4, 8` at base 2 (table: `1, 2, 4, 9 within ≤ 40`, so strict at `k = 4` unless an 8-set between 40 and 60 hits), `2, 6` at base
3 (`2, 6`), `3` at base 4 (`3`), `4, 5, 6, 7, 8, 9` at bases 5–10 (`5, 7, 7, ≥ 9, ≥ 9, ≥ 10`).
Never violated; tight at bases 2–4 for the exact entries; a strict lower bound from base 5 on.
⚠️ The count is a heuristic with a known failure mode: a single interval hole next to the fixed
point `0` (Glendinning–Sidorov) beats mean-field, and inside our own family the block `01` at
base 2 is hit by `{1}` alone although its hole has measure `1/4`.  So N5 is a pattern with a
story, not a derivation; the blocks that bind are the constant ones `d^k`, whose holes contain a
fixed point and leak slowest, which is exactly the Bunimovich–Yurchenko direction.

Where N5 is most exposed: every lower half in the table is capped at multipliers `≤ 60`, which is
where sparse adversaries are cheap.  Probe (21:35, seeded scratch `n5_large_probe.py`): 40 random
primitive pairs in `[100, 500]` at `(4,1)`, 40 at `(2,3)`, and 12 random triples in `[40, 120]` at
`(2,3)` - **none hits** (39 s in all; the trimmed products stay small).  Controls through the same
function: `{1,3,5,7}`, `{1,10,14}`, `{2,5,7}` hit, `{1,3,5}`, `{1,11}` do not.  So N5 survives the
one place the table could not see.

## Pairs at base 4: the lower bound N2 as an integer statement (22:21)

N2 says every pair `{m₁, m₂}` fails at base 4, i.e. `S(4,1) ≥ 3`.  Channel reduction lets us assume
`4 ∤ m_i` and `gcd(m₁, m₂) = 1`.

**Clean truncation.**  For `{1, m}`: if `t ∈ (0,1)` and `t/m` are purely periodic with periods
dividing `L`, then `B := ⌊(t/m)·4^L⌋` has `m·B = ⌊t·4^L⌋` exactly, because
`m·frac((t/m)4^L) − frac(t·4^L) = t − t = 0`.  For a pair, `m_i·B = ⌊m_i r 4^L⌋ − ⌊m_i r⌋`, exact
when `r < 1/max m_i`.  So a hole-free periodic orbit with a landing strip (the Mahler family) is
the sparse adversary (N1) with a block `B`; the two families in the "Holes" section are one.

**The crux.**  `{1, m}` fails at digit `d` if (★) some `B ≥ 1` has `d ∉ digits(B) ∪ digits(mB)`;
`{m₁, m₂}` fails if (★★) some `B` has `d ∉ digits(m₁B) ∪ digits(m₂B)`.  The automaton verdict is
stronger in principle (any escape), but every pair tested falls to (★★).  Checked (scratch
`star_test.py`, 1 s): (★) for every `m < 4^6` with `4 ∤ m`, least `B ≤ 1045` (at `m = 2174`; the
least `B` is 1 for 940 of the 3072 values, 3 for 478, 2 for 420); (★★) for 400 random coprime pairs
in `[2, 2000]`, least `B ≤ 3238`.

**Explicit families (proved).**
- `B = 1`: `d ∉ digits(m)` (Berend–Boshernitzan).
- `B = 4^k − 1` with `4^k > m`: `mB = (m−1)·4^k + (4^k − m)`, whose digits are those of `m − 1` and
  their 3-complements; `d ∈ {1,2}` works iff `m − 1` uses only the digits 0 and 3.
- `B = 4^k − 2 = 3…32` with `4^k > 2m` (avoids 1): `4^k − 2m = (4^k − 1) − (2m − 1)` is the digit-wise
  complement of `2m − 1`, so `d = 1` works iff `1 ∉ digits(m − 1)` and `2 ∉ digits(2m − 1)`.  Example
  `m = 43`: `m − 1 = 222₄`, `2m − 1 = 1111₄`, `B = 254`, `mB = 2222222₄`.
- Repunit: if `m | 4^k − 1`, `B = (4^k − 1)/m` (the repetend of `1/m`) gives `mB = 3…3`, so
  `d ∈ {1, 2}` works iff the repetend avoids `d`.  Example `m = 33`: `1/33 = 0.(00133)`, `B = 31`.
- Digit 3 with `B` over the digits `{1, 2}`: for odd `m` and every carry `c`, one of `b ∈ {1,2}` has
  `(mb + c) mod 4 ≠ 3` (`c ≡ 0, 2`: `b = 2`; `c ≡ 1, 3`: `b = 1`), so an infinite 3-free path always
  exists 4-adically; the finite obstruction is the final carry `⌊mB/4^j⌋ ∈ [m/4, m)`, whose digits
  must avoid 3.  Up to `m = 63` every digit-3 avoider found has digits in `{1,2}` and is `≤ 22`.

**What a proof of (★) needs.**  `#{B < 4^N : B, mB ∈ K_d} = 4^N Σ_t F̂_K(t) F̂_K(−mt)` with main term
`(9/4)^N`; the pointwise bound `|F̂_K(s)| ≤ (3/4)^N/3` for `s ≠ 0` (one factor `|φ(1/4)| = 1/3`) does
not control the `L¹` mass of the other factor, so one needs the Erdős–Mauduit–Sárközy / Maynard
missing-digit Fourier machinery with a dilation `t ↦ mt` in place of an arithmetic progression.
Geometrically: `K_d ∩ (m₁/m₂)·K_d` (an automatic set) has positive dimension.  That is the shape of
the theorem; it is not proved here.

**Literature (22:45, abstracts and reviews; notes in `papers/lit-cantor-dilate-intersections-2026-09-13.md`).**
Positivity of `dim(K_d ∩ λK_d)` for all rational `λ` is not a theorem or a stated conjecture, and it
fails at base 3: with `λ = 2` the intersection is countable for every `d` (doubling sends the digits
`{0,1}` to `{0,2}` without carries), which is the pair `{1,2}` hitting every ternary digit.  So N2 is
a base-`g ≥ 4` statement and, as far as we found, unstudied.  The upper side is known:
Jiang–Li–Li–Wu (arXiv 2607.19813, July 2026) show `dim((γK + α) ∩ K) < dim K` for rational `γ`
coprime to the base iff `γ ∉ ±b^ℤ`; Abram–Lagarias (J. Fractal Geom. 2014, arXiv 1308.3133) treat
the 3-adic integer version with an automaton and `dim = log₃(Perron eigenvalue)`.  The
translate literature (Davis–Hu 1995, Kenyon–Peres 1991, Deng–He–Wen 2008) never treats `λ`.

## Prior art (literature sweep 2026-09-13; [R] = read in the source)

- The fixed-`k` cardinality appears **nowhere** (either variant): forward citation cones of Mahler
  1973, Berend–Boshernitzan 1994 and 1995, Szüsz–Volkmann 1983 checked.
- **Berend–Boshernitzan 1995**, *Numbers with complicated decimal expansions*, Acta Math. Hungar.
  66, 113–126 [R] - the only prior *set* formulation: an **`M_g`-set** is `A ⊆ ℕ` such that every
  irrational and every block *of every length* has some `m ∈ A` with the block i.o. in `mα`.
  Thm 3.1: `A` is `M_g` ⟺ `A·E = 𝕋` for every infinite closed `×g`-invariant `E ⊆ 𝕋`.
  **Cor 3.3: no finite `M_g`-set exists.**  Cor 3.6: `{hⁱ}` is `M_g` for `h, g` multiplicatively
  independent.  Our `S(g,k)` is precisely the fixed-length, finite refinement their Cor 3.3 rules
  out at unrestricted length; their Thm 3.1 is the natural framework for a structure theorem
  (cover every `k`-cylinder by `∪_{m∈S} m·E` over invariant closed `E`).
- **Bugeaud 2012**, *Distribution modulo one and Diophantine approximation*, §8.6 [R]: Def 8.12
  = `M(b,n)`; **Thm 8.11: `M(b,n) ≤ b^(n+1) + b^n − 1`** (between B–B 94's `2g^(k+1)` and our
  `g^(k+1)`; owed as a statement-only ledger entry); Ex. 8.7 `M(3,1) = 2`.
- Lower-bound constructions in print (B–B 94 §3) bound only the initial segment: for sparse
  `α = Σ g^(−n_j)` the blocks of `mα` are the digit string of `m`, so one de Bruijn-shaped `m`
  covers everything - cardinality lower bounds need non-sparse adversaries.
- Also: Alon–Peres 1992 Cor 7.2 (good multipliers have density 1); Thangadurai–Tripathi 2025
  (every integer in an explicit interval is a multiplier, conditional on a long zero block).

## What would be a theorem here

1. **Any exact value beyond the table with a proof**, e.g. `S(4,1) = 3`.  Upper half: the
   automaton verdict on `{1,10,14}` (a finite computation, certifiable the AdderTower way).  Lower
   half, via the sparse route: **for every pair `m₁ < m₂` there is a digit `d ∈ {1,2,3}` and
   infinitely many `B` with `d ∉ digits₄(m₁B) ∪ digits₄(m₂B)`** - true for all 1101 primitive pairs
   ≤ 60 with `B ≤ 4096`; the theorem is the uniform argument in `(m₁, m₂)`.  The wiring
   ("block-sparse `α` is irrational and defeats `S`") is elementary and formalizable on its own.
   Recommended freeze candidate (Fable, 17:45): two nodes, the digit-avoidance lemma and the wiring.
2. **Growth**: is `S(g,k)` bounded in `k` for fixed `g`?  B–B 95 Cor 3.3 says the all-lengths
   answer is "no finite set", which suggests `S(g,k) → ∞`; a proof would be new.  A single
   quantitative lower bound `S(g,k) ≥ f(k)` with `f → ∞` is the first real target.
3. **Per-block vs disjunctive**: `{1,2}` vs `{2,11}` at `(3,1)` shows they differ; is `S* ≤ S + c`,
   or can they diverge?
4. **Structure of minimal sets**: the "uniqueness" of `{1,10,14}` and `{1,3}` was a search-cap
   artifact - with multipliers `≤ 60` there are 35 hitting triples at base 4 and 151 hitting
   pairs at `(2,2)`; in ratio terms `{1, 5/2, 7/2}`, `{1, 10, 56}`, `{1, 6}`, `{1, 11}`, ... - so
   the right object is the set of ratio-sets that hit, and its structure (which rationals `q`
   make `{1, q}` hit at `(2,2)`?) is the first thing to characterize.

The caps are search limits, not theorems.  The graph as of 17:55–18:40:
- **U1–U4, L1, mono - GREEN 2026-09-13 20:43** (`src/NormalNumbers/HittingSetBounds.lean`, one
  Fable lap, 60 min, commit `15945c8`, every certificate a kernel `decide`, the 26880-state
  family chunked through `checkEdgesOnA_of_chunks`): `hitting_4_1_three : IsHittingSet 4 1
  {1,10,14}` (**`S(4,1) ≤ 3`**), `hitting_5_1_five : IsHittingSet 5 1 {1,2,3,4,6}` (**`S(5,1) ≤ 5`**),
  `hitting_2_2_two : IsHittingSet 2 2 {1,3}` (**`S(2,2) ≤ 2`**), `hitting_2_3_four : IsHittingSet
  2 3 {1,3,5,7}` (**`S(2,3) ≤ 4`**), `IsHittingSet.mono`, and `not_hitting_5_1_four`,
  `not_hitting_5_1_five` from `Mahler.mahler_lower_bound_base5`.  All seven on the standard
  triple (`#print axioms`, host, 20:58).  So at `(5,1)` both halves of the base-5 story are
  theorems: `{1,2,3,4}` fails, `{1,2,3,4,6}` works, `M(5,1) = 6` while `S(5,1) ≤ 5`.
- **N1 (wiring) - GREEN 2026-09-13 19:00** (`src/NormalNumbers/SparseAdversary.lean`, one
  Fable lap, 16 min, commit `2cffd31`): `not_isHittingSet_of_avoider` - for finite `S`, base
  `g ≥ 2`, a block `w` of length `k ≥ 1` with a nonzero digit, and one `B ≥ 1` with
  `¬ (w <:+: paddedDigits g k (m * B))` for every `m ∈ S`, `¬ IsHittingSet g k S`.  Adversary
  `α = B · LiouvilleNumber.remainder g k₀`, block boundaries at factorials, digits recovered through
  `Bridge.digitOf_realOfDigits` from partial sums at block boundaries (no tsum rearrangement).
  Corollaries by kernel `decide`: `pair_one_eleven_not_hitting : ¬ IsHittingSet 4 1 {1, 11}`
  (`B = 62`, `w = [1]`) and `triple_one_three_five_not_hitting : ¬ IsHittingSet 2 3 {1, 3, 5}`
  (`B = 1`, `w = [1,1,1]`).  All three on the standard triple (`lean-green --axioms`, host, 19:05).
  So every "not hitting" claim in the tables above that the sparse probe defeats is now one
  `decide` away from a theorem; the automaton's dense adversaries are not yet wired.
- **N2 (frozen Prop, open)**: `∀ m₁ < m₂` coprime, `∃ B ≥ 1, d ∈ {1,2,3}` with `d ∉ digits₄(m₁B) ∪
  digits₄(m₂B)`.  Probe: all 1101 primitive pairs `≤ 60` with `B ≤ 4096`.  With N1 and the
  automaton verdict on `{1,10,14}` this is `S(4,1) = 3`.
- **N3 (lemma, proved)**: the prime-base residue obstruction above.
- **N4′ (frozen Prop, open)**: the converse for `|S| ≤ p − 2` (the unrestricted converse is false, see the kill test); gives `S(p,1) ≥ p − 1`.

N1 and the four upper bounds are done.  Every exact value in the table now has its upper half
as a theorem except `S(3,1)` (B–B, `AdderTowerC1`/`C2` already) and `S(6,1)` (seven channels,
`1·8·11·14·16·20·23 ≈ 8·10^7` ambient states - beyond kernel `decide` without a reduction).  The
lower halves `S(g,k) ≥ s` remain the open nodes N2/N4′, and no table will supply them.
