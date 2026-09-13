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
does not, `S(2,1) = 1`.  Reach: products of ≤ 4 channels with multipliers ≤ 60 in seconds; five
channels at `k = 4` are already too large for the naive product.

## Data (exact, 2026-09-13; "unique" means unique among sets within the searched range)

| `(g,k)` | `S(g,k)` | minimal sets found | `S*(g,k)` | disjunctive sets | searched |
|---|---|---|---|---|---|
| (2,1) | 1 | `{1}` | 1 | `{1}` | – |
| (3,1) | 2 | 162 pairs ≤ 40, incl. `{1,2}` (B–B) and `{2,11}` (tower C2) | 2 | **`{2,11}` unique ≤ 20**; `{1,2}` is per-block only | pairs ≤ 40 / ≤ 20 |
| (4,1) | 3 | **`{1,10,14}` unique ≤ 40** | > 3 | – | sizes ≤ 3, ≤ 40 (≤ 60 running) |
| (5,1) | > 4 | – | – | – | sizes ≤ 4, ≤ 30 |
| (6,1), (7,1) | > 3 | – | – | – | sizes ≤ 3, ≤ 40 |
| (2,2) | 2 | `{1,3}` unique ≤ 40 | 3 | `{1,3,5}` | ≤ 40 / ≤ 30 |
| (2,3) | 4 | `{1,3,5,7}` unique ≤ 40 | > 4 (`{1,3,5,7}` fails) | – | sizes ≤ 4, ≤ 40 |
| (2,4) | ? | **`{1,3,…,15}` does NOT hit** (nor any 7-subset of it) | – | – | that family only |
| (3,2) | > 4 | – | – | – | sizes ≤ 4, ≤ 20 |

The tempting conjecture `S(2,k) = 2^(k−1)` via the odd multipliers below `2^k` is **refuted at
`k = 4`**; the two small cases were coincidences, or the minimal sets at `k = 4` involve larger
multipliers.  `S(2,4)` is beyond the naive instrument (five channels, multipliers in the twenties);
a smarter search (incremental products with early collapse, or a BDD over carries) is the next
tooling step before more data.

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

1. **Any exact value beyond the table with a proof**, e.g. `S(4,1) = 3` needs a lower bound: an
   adversary `α` defeating every pair `{1, q}` of rationals - the automaton's escaping SCC for a
   given pair is a *construction* of such `α`; the theorem is the uniform argument over all `q`.
2. **Growth**: is `S(g,k)` bounded in `k` for fixed `g`?  B–B 95 Cor 3.3 says the all-lengths
   answer is "no finite set", which suggests `S(g,k) → ∞`; a proof would be new.  A single
   quantitative lower bound `S(g,k) ≥ f(k)` with `f → ∞` is the first real target.
3. **Per-block vs disjunctive**: `{1,2}` vs `{2,11}` at `(3,1)` shows they differ; is `S* ≤ S + c`,
   or can they diverge?
4. **Structure of minimal sets**: `{1,10,14}` at base 4, `{2,11}` at base 3 - what makes a set
   minimal?  The scaling remark says to look at the rational ratios (`{1, 10, 14}`, `{1, 11/2}`).

Not a lap target yet: freeze a statement only after the smarter instrument confirms the small
values are stable under larger multipliers (the `≤ 40` caps are search limits, not theorems).
