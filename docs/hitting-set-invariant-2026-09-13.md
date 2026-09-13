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
| (3,1) | 2 | 162 pairs ≤ 40, incl. `{1,2}` (B–B) and `{2,11}` (tower C2) | 2 | **`{2,11}` unique ≤ 20**; `{1,2}` is per-block only | pairs ≤ 40 / ≤ 20 |
| (4,1) | 3 | `{1,10,14}` (unique ≤ 40); **35 triples ≤ 60**, e.g. `{2,5,7}`, `{1,10,56}`, `{3,30,42}` | > 3 | – | sizes ≤ 3, ≤ 60 |
| (5,1) | **5** | 2008 sets ≤ 30, e.g. `{1,2,3,4,6}`, `{1,2,3,4,8}`, `{1,2,3,6,14}` | – | – | sizes ≤ 5, ≤ 30 |
| (6,1), (7,1) | > 5 | – | – | – | sizes ≤ 5, ≤ 30 |
| (2,2) | 2 | `{1,3}` (unique ≤ 40); **151 pairs ≤ 60**, e.g. `{1,6}`, `{1,11}`, `{1,12}`, `{2,3}` | 3 | `{1,3,5}` | ≤ 60 / ≤ 30 |
| (2,3) | 4 | `{1,3,5,7}` unique ≤ 40; **928 sets ≤ 60**, e.g. `{1,3,5,14}`, `{1,3,7,10}`, `{1,3,10,14}` (in ratios `{1,3,5,14}` is new, not a scaling) | > 4 (`{1,3,5,7}` fails) | – | sizes ≤ 4, ≤ 60 (naive, 2 h 38 min) |
| (2,4) | > 6 | **`{1,3,…,15}` does NOT hit** (nor any 7-subset of it); no set of size ≤ 6 below 20 | – | – | sizes ≤ 6, ≤ 20 |
| (3,2) | **6** | 42 sets ≤ 20, e.g. `{1,2,4,5,7,8}`, `{1,4,5,6,7,8}` | – | – | sizes ≤ 6, ≤ 20 |

Read along rows: `S(g,1) = 1, 2, 3, 5, >5, >5` for `g = 2..7`; `S(2,k) = 1, 2, 4, >6` for
`k = 1..4`; `S(3,k) = 2, 6`.  The tempting conjecture `S(2,k) = 2^(k−1)` via the odd multipliers
below `2^k` is **refuted at `k = 4`** (no 6-set below 20 hits).  Every ">" is a search cap on the
multipliers, never a theorem; every exact value's upper half is exact (a hitting set is a finite
automaton verdict).

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

N1 is done; N2/N4 need an idea (a construction of `B` from `S`), and no table will supply it.
