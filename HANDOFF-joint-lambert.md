# HANDOFF — joint Lambert, first bounded target: DONE

Date: 2026-09-27.  Operator override run (`KICKOFF-2026-09-26-joint-lambert.md`,
first bounded target only), recorded in `DIRECTION.md`.

## Result

`NormalNumbers.JointLambert.evenEncoding : NormalNumbers.JointLambert.EvenEncoding`
is **proved**, sorry-free, in `src/NormalNumbers/JointLambertEncodingProof.lean`.

```
#print axioms NormalNumbers.JointLambert.evenEncoding
  -- [propext, Classical.choice, Quot.sound]
```

The three frozen `Prop` definitions in `JointLambertStatement.lean` are byte-identical
to commit `78e6048` (`git diff 78e6048 -- src/NormalNumbers/JointLambertStatement.lean`
is empty).  The module is in the root build (`src/NormalNumbers.lean:499`).

## The mathematical advance

The paper (§2) routes the encoding through torus Fourier analysis: the uniform
measure on `({2a/b^s})_{b∈S}`, `0 ≤ a < lcm(S)^s`, annihilates each fixed
nontrivial character once `s` is large, hence tends weakly to Haar measure.  That
is correct but expensive to formalize in arbitrary dimension (one needs a
nonnegative product kernel and an exact-Fourier/Markov argument to convert weak
convergence into an interior-box hit).

**This session replaced it by an elementary, constructive proof** — the "equivalent
elementary proof" the kickoff invites.  Two observations collapse the problem:

1. *Free choice at one base.*  With `frac b s a = {2a/b^s}`, the reachable values
   `{(2n mod b^s)/b^s}` form a grid of spacing `2/b^s`.  So any window inside
   `[0,1]` longer than `2/b^s` is hit by some offset `α < b^s`, and the witness is
   explicit — `α = (n + b^s - A % b^s) % b^s` for the grid index
   `n = ⌊u·b^s/2⌋ + 1`.  No congruence machinery, no character sums.
   (`exists_offset_mem_window`.)
2. *Cheap interference.*  That offset satisfies `α < b₀^s`, so it moves a **larger**
   base `b > b₀` by only `2α/b^s < 2(b₀/b)^s ≤ 2θ^s`, `θ = b₀/(b₀+1) < 1`.

Therefore: induct on `S.card`, **strip the smallest base**, solve the remaining
(larger) bases against windows shrunk by `ε/2`, then spend exactly that slack on a
single correction at the smallest base.  Depth `s` is chosen large enough that
`2θ^s < ε/2`, which simultaneously makes the grid fine enough and the interference
negligible.  The `2 ≤ a` requirement is met by padding with `2·∏_{b∈S} b^s`, using
periodicity (`frac_add_mul`).

The only property of the bases used is that they are **distinct** — that is exactly
what makes `b₀/b < 1`.  No coprimality, no multiplicative independence.  Explicit
audit anchors `evenEncoding_two_four` and `evenEncoding_two_three_six` are in the
file; the latter is the fully dependent triple where the base-`6` coordinate is a
CRT function of the base-`2` and base-`3` coordinates.

### Independent check of the mathematics

Done two ways.  (a) A faithful Python transcription of the recursion (same `s₀`
recursion, same per-level `ε/2` shrink, same residue witness) over 400 random
window systems on `{2,4}`, `{2,3,6}`, `{2,3,4,6,12}`, `{5,7}`, `{2,4,8,16}`,
`{3,9,27,2,6}`: 0 failures.  (b) A deliberately *sloppy* transcription that used a
single global `θ` and only one `ε/2` shrink **fails** on `{2,3,4,6,12}` at base `4`.
That is the sharp edge: the slack budget must halve per recursion level, because
each of the `|S|` correction steps can consume it.  The Lean proof does this
correctly (each level's `s₀` comes from the IH at `ε/2`); a future reader tempted
to "simplify" to one uniform `θ` and one shrink should not.

No obstruction or counterexample was found.  `probes/swingc2_window.py test` could
not be run: it wants `pytest` from pypi and this box has no egress.

## Exact next dependency

The encoding interface is now discharged; what it feeds is kickoff item 1:

> **Generalize the existing selectable-prime CRT constructor to exponent
> `lcm(bases) - 1`, so that one survivor has divisor count `2a`.**

Concretely, the next Lean obligation is the §4 construction with `c = lcm S`:
a common arithmetic progression `n_m = R + mA` such that
`τ(n_m + r) = 2a` at the single survivor slot `r = s - 1` (with the `s`, `a`
produced by `evenEncoding`), and `c^{j+1} ∣ τ(n_m + j)` at every killed slot
`j < k`, `j ≠ r`.  Note the shape of the hand-off: `evenEncoding` returns `s` and
`a`, §4 must consume **both** — `r = s - 1` sets the survivor position and `2a` is
the divisor count that every coordinate then reads at a different scale.  Raising
the killed-slot valuation from `1` (scalar binary case) to `c - 1` is the only
change to the scalar construction, and it costs a fixed factor `c` in `log B`.

AGP and the prime-interval supply stay **explicit named hypotheses**; do not use
the old vacuous `PrimeDensityAP`.  §5's single binary majorant `T_m` is shared
across all coordinates — do not introduce per-coordinate survivor primes or a
prime-tuples hypothesis.

Not claimed here, and not to be claimed until §§3–6 are formalized:
`JointLambertDisjunctivity`, or `JointWords` for any `S`.
