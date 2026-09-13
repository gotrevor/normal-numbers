# Stoneham boundary campaign: fixed statements, elementary details

Attended brief by Ren / Astra, 2026-09-13.  This is AI-written mathematical guidance, not a published novelty claim.

## Scope and authority

Prove the six frozen declarations in `src/NormalNumbers/StonehamBoundary.lean`.  The endpoint is `isDisjunctive_six_stoneham23`, with the stronger arbitrary-late interval theorem immediately above it.  The old Mahler campaign is not this run's task.  This brief and the dated operator override in DIRECTION take precedence over old HANDOFF objectives.

Two grind laps, low effort, nominal two-hour between-lap duration limit.  No adaptive escalation, review laps, reflection laps, Aristotle, downloads, or other campaigns.  A lap succeeds by advancing a load-bearing proof or refuting a statement with an exact counterexample.  Additional named intermediate proof obligations are welcome; do not measure success by their count.

Frozen signatures and existing definitions are immutable.  Do not weaken, re-hypothesize, delete, rename, shadow, or replace them.  Do not introduce axioms, opaque assumptions, altered meanings of Stoneham/disjunctivity, or a generic density hypothesis.  If a statement is wrong, record the exact failure in HANDOFF and ask the attended judge to adjudicate.  `JUDGE.md`'s division of statement authority applies; its old CF-specific route restrictions do not describe this new task.

Worker footprint: `src/NormalNumbers/StonehamBoundary.lean`, optional new helper modules named `StonehamBoundary*.lean`, and dated HANDOFF files.  Existing source is read-only.  Do not edit DIRECTION, JUDGE, this brief, other mathematics, STATUS, ROADMAP, or KB files.  Host owns those during the run.  Commit green proof batches; do not push or send outward messages.  Do not leave a red tree at handoff.  Stop when the endpoint and dependencies are genuinely proved, or at the supervisor's bounds.

## The proof

Write alpha = sum_(j >= 1) 1/(3^j 2^(3^j)).  The existing `stoneham_base6_readout` states, for n >= 3,

    r/2^c < orbit 6 alpha n <= r/2^c + 2*3^(a-1)/2^(3^(J+2)-n),

where J = jstar n, a = n-(J+1), c = 3^(J+1)-n, r = 3^a mod 2^c.

The proof of that theorem already establishes that the positive error is strictly less than 1/2^c.  Expose the resulting one-cell inequality as `stoneham_orbit_readout_cell` by combining its public inequality with the same short elementary power estimate.  No new infinite-series argument is needed.  Copying/adapting the internal `hT_lt` estimate into a new proof is allowed; changing the existing theorem is not necessary.

### A. The block-index permutation

f(k) = 3^k - k permutes the residues mod 2^r.  Integer subtraction avoids truncated-natural-subtraction hazards.

Elementary lifting proof: modulo 2, f(k) = 1-k.  For r >= 1,

    3^(2^r) = 1 (mod 2^(r+2)),
    f(k+2^r) = f(k)-2^r (mod 2^(r+1)).

The two input lifts therefore cover the two output lifts.  Start at r=0 or r=1 as convenient.  Also prove the needed periodicity: f(k+2^r) = f(k) mod 2^r (r >= 1), and its multiples.  This upgrades finite surjectivity to arbitrarily large k in a solving residue class.

An alternative is the exact isometry v_2(f(k)-f(l)) = v_2(k-l).  For odd d=k-l, the difference is odd.  For even d, v_2(3^d-1)=v_2(d)+2, so subtracting d gives exactly v_2(d).  Mathlib `NumberTheory/Multiplicity.lean` has the two-adic LTE theorems, but induction may be less setup for low effort.

### B. The residue grid

For c >= 3, every a < 2^c with a = 1 mod 8 is a power of 9, hence of 3, modulo 2^c.

Direct lifting route:

    9^(2^r) = 1 + 2^(r+3) (mod 2^(r+4)), r >= 0.

Squaring proves the successor step.  At modulus 8 the only grid residue is 1.  Lifting from 2^c to 2^(c+1), the exponents e and e+2^(c-3) of 9 give the two possible lifts.  This suffices; do not build a full group-classification library just for this theorem.

Alternatively, the order of 3 mod 2^c is 2^(c-2), and its powers are exactly residues 1 or 3 mod 8, by LTE and finite cardinality.

### C. Combine them at the boundary

Fix c >= 3 and an admissible a.  Choose e with 3^e = a mod 2^c.  Put P=2^(c-2); 3^P = 1 mod 2^c.  Solve

    f(k) = e+c (mod P).

Every sufficiently large k in that residue class works.  At n=3^k-c,

    3^(k-1) <= n < 3^k,
    jstar n = k-1, sC n = c, sA n = 3^k-k-c,
    readout n = a.

Choosing k >= max(K,c,3) is enough for the block inequalities; larger elementary thresholds are equally valid since none are frozen.  Be explicit about subtraction bounds before using integer congruences to compare the natural power exponents.  Preserve the frozen unconditional recurrence conclusion.

### D. Hit an entire grid cell

For any real interval 0 <= u < v <= 1, choose c large enough and a = 1 mod 8 such that

    u < a/2^c < (a+1)/2^c < v.

The grid spacing is 8/2^c, so this is a basic Archimedean/floor lemma.  Taking a grid point near the midpoint and requiring 16/2^c < v-u gives ample slack.  The strict containment ensures a < 2^c, positivity, and the word-boundary margin.  No limit theorem is needed for the tail: the whole orbit cell is already inside the target interval.

Choose K large enough that 3^k-c >= N whenever k >= K, apply C and the one-cell inequality, and assemble interval recurrence.  The headline then follows by the supplied proof.

## Evidence and claim limits

The paper proof is in `~/personal/claude/knowledge/core/projects/normal-numbers-boundary-route-2026-09-13.md`, visible read-only inside the box.  Finite checks there covered permutations through r=16, residue grids through c=16, all words of lengths 1 through 4, and 172 exact rational readouts.  Those are diagnostics, not substitutes for the universal proof.

Hertling, *Disjunctive omega-Words and Real Numbers* (1995), Theorem 8, already proves a very similar separated-block base-6 theorem for sum 2^(-q^i), q odd.  The present weighted Stoneham statement may be an elementary extension of known work.  Do not claim literature novelty.  Bailey-Borwein (2012) proved this Stoneham constant is NOT normal in base 6.  Sparse recurrence is consistent with that.  This says nothing about normality or disjunctivity of log 2.

## Verification and handoff

Build the focused module first.  The host checked `lake-base status 4.33.1` and `relake plan` before staging; the toolchain is v4.33.1.  The box uses its existing shared toolchain/dependency mechanism.  Do not bump dependencies or hydrate a fresh unshared mathlib tree.

Before claiming completion, build `NormalNumbers.StonehamBoundary` and print axioms of all six frozen declarations.  No `sorryAx`, custom axioms, trust escapes, or changes of statement meaning.  Required-declaration and file completion gates are additional checks, not permission to move unresolved dependencies to another file.  Compare the frozen signatures with the scaffold commit.  Hand off what mathematical lemma was proved, what remains, and any exact obstruction, not a sorry-count metric.
