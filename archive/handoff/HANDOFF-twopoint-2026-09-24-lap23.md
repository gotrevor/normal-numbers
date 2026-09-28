# HANDOFF twopoint lap 23 — the constancy requirement was an artefact

Branch `wip/twopoint-avg`.  New file `src/NormalNumbers/TwoPointBlockRotation.lean`, sorry-free,
axioms `[propext, Classical.choice, Quot.sound]`.

## Advance on the crux

Lap 22 killed the pairing construction because the rotation `Z(m)` is not constant: the `q`-dilate
picks up the defect `(q−p)k`.  This lap shows **constancy was never needed**.

* **`norm_sum_le_of_rotation_pointwise`** — if `σ` injects `A ⊆ S` into `S \ A` and
  `f(σ m) = Z(m)·f(m)` with the *pointwise* gap `‖1 + Z(m)‖ ≤ 2 − c` on `A`, then

      ‖Σ_{m∈S} f(m)‖ ≤ |S| − c·|A| .

  The pairing sums term by term — `f(m) + f(σ m) = (1 + Z(m))·f(m)` — so nothing links different
  `m`'s.  Lap 21's fixed-`z` lemma is the special case.
* `norm_one_add_lt_two` — every unimodular `z ≠ 1` has `‖1+z‖ < 2`;
  `norm_one_add_le_of_re_le` — `‖1+z‖ ≤ √(2+2ρ)` from `Re z ≤ ρ`, an explicit gap.
* `twoPointTruncSum_blockRotation` — the leaf's per-pair sum under a pointwise-gap pairing.

## The target, now a sieve question rather than an Elliott question

Take `σ(m) = rm + k` with `r = pk+1` (`pairing_shift`).  Then off a thin set,

    Z(m) = ζ^{1 − Δ_q(m)} · (weight ratio),
    Δ_q(m) = ω( r(qm+1) + (q−p)k ) − ω(qm+1).

The saving needs only `Z(m) ≠ 1` with a uniform gap on a positive-density set — i.e.

> **`Δ_q(m) ≢ 1 (mod b)` (after accounting for the weight ratio) for a positive density of `m`.**

This asks that the `ω`-difference of two linear forms *misses one prescribed residue* on a
positive density — not that it equidistributes.  It is a sieve/statistical statement, and it is
the first target in this run that is not of Elliott type.  It is also plainly true heuristically:
`Δ_q` has an Erdős–Kac-type spread, so no single residue class can carry everything.

## Next attack (lap 24)

Two sub-bricks, in order:

1. **The weight ratio.**  `peelWeight b p q t (σ m) / peelWeight b p q t m` must be computed (or
   bounded away from cancelling the `ζ`-factor).  `PairDecoupleOneDigit.lean` has `peelWeight` as
   `phase (t/b · shiftPairTail b p q 1 1 m)`; the ratio is a phase of a tail difference and is
   the one piece that is NOT arithmetic in `ω`.  If it can be shown to lie in a bounded arc for a
   positive density of `m`, the gap follows.
2. **`Δ_q` misses a residue.**  Formalise the weakest usable form: there exist `c > 0` and a
   density-`α` set on which `ω(r(qm+1)+(q−p)k) ≠ ω(qm+1) + 1`.  A cheap sufficient condition:
   restrict to `m` with `r ∣ qm+1`, where the left form gains a known factor — the CRT class is
   nonempty since `gcd(r, q) = 1`, and has density `1/r`.

## Confidence
- `twoPointWeightedAvg_all` TRUE: 88%.
- `twoPointGramSum` leaf TRUE: 80%; provable with known techniques: 10% (up from 6: the pointwise
  gap removes the obstruction lap 22 found, and the residual target is sieve-shaped).
- The pointwise-rotation route yields the saving: 30%.
