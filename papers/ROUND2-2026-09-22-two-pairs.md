# Round two: unequal cutoffs and overlapping windows

Prepared for Trevor's request for two more interactive Fable/Astra pairs.
This is a research plan, not a claim that either proposed mechanism works,
and not authorization for an unattended campaign.

## Why these two

The completed sparse-NN proof reaches divergent prime sets with vanishing
fresh reciprocal mass, including the little-o L4 family.  The explicit
density approximately 1/L4 example defeats the present majorants, not
normality.  The next positive attack should change an estimate, not another
schedule in the same estimate.

The G4 Riesz construction defeats a substantial package of summary laws,
even with exact singleton marginals.  Its author left an actual unfinished
carry construction for overlapping windows.  This is a bounded new theorem
target, not another audit of the completed sparse-NN proof.

Both pairs therefore work in normal-numbers.  The Collatz wrap leaves
order-sensitive tail inequalities open, but supplies no candidate estimate.
Its three refuted relaxations are not a new assignment.  This allocation
does not assert that Collatz is exhausted.

## Shared operating rules

Repo: `/Users/gotrevor/src/normal-numbers`, presently `wip/g5-prime-subset`.
Read local instructions and inspect current state before editing.  Use
disjoint new files; do not rewrite the assembly paper or the Riesz note.
Do not change branches in a shared tree.  Negotiate any actual file overlap.

Mailboxes, created on first message:

- Pair A: `agent-mail/multicutoff/`
- Pair B: `agent-mail/shift-consistency/`

Use the existing protocol `agent-mail/20260922T174110Z-protocol.md`, with
this already-settled correction: read messages ordered by timestamp,
regardless of permission bits.  Git does not preserve chmod 444.
Every message is a new immutable `UTC-SENDER-UUID.md`; obtain UTC from the
clock and a real UUID.  Include From, To, UTC, Reply-to, Subject.  Use
explicit identities `fable-multicutoff`, `astra-multicutoff`,
`fable-shift-consistency`, `astra-shift-consistency`.  Corrections are new
messages.  Never edit old mail.  Check mail before major work and after a
result; avoid acknowledgement-only loops.  A file does not wake a session.

Fable leads construction; Astra independently derives the load-bearing
estimate and attacks it.  Both do mathematics.  At the first exchange,
send an exact finite statement and its first obstruction, not a long menu.
Then improve or refute that statement.  A failed approach must leave a
precise reason, not an inflated universal impossibility claim.

No repeat headline-axiom sweep or Brun audit.  No formalization treadmill
until a new useful statement and proof survive the pair's exchange and
there is explicit launch authorization.  If numerical probes help, retain
tests with independently computed controls.  Prefer paper derivation first.

Capacity expires 2026-09-23 09:00 UTC (05:00 EDT).  Reserve a final handoff
before that deadline.  Report a crux advance, counterexample, or precise
remaining lemma; do not report token use or theorem counts as progress.

## Pair A: site-dependent prime cutoffs

### Read

- `papers/prime-model-assembly-2026-09-22.md`, especially Part I's actual
  model-transfer estimates and Part VI, including the explicit barrier set.
- `src/NormalNumbers/PrimeModelKMTFixedH.lean`
- `src/NormalNumbers/PrimeModelFamilyConsumer.lean`
- The dependencies defining `Regime`, radical-state transfer and the sieve
  remainder, following the actual declarations rather than historical plans.
- Existing `agent-mail/sparse-nn/` closing handoffs as needed for the frontier.

### Concrete proposed change

The phase weights decay geometrically in the site index.  The current
proof nonetheless gives every site the same prime cutoff y=N^epsilon,
constrained by the full growing window J.  Test whether unequal cutoffs
can retain more primes at heavily weighted early sites without exhausting
the joint sieve level.

Begin with TWO tiers: sites j<=m use y_head; m<j<=J use y_tail, with
y_head>=y_tail.  Derive the finite phase-transfer bound directly from the
existing per-shift counts.  Its suggested shape, not an assumed theorem,
is a fixed-h constant times

    sum_{j=1}^J 4^(-j) S_P(y_j,N) + explicit endpoint errors.

Here S_P(a,b)=sum_{a<p<=b,p in P}1/p.  The essential new obligation is a
JOINT arithmetic-to-model estimate for these unequal cutoffs.  For a prime
p the active sites are {j:p<=y_j}; retain their actual local factor and
the dependence on their number.  Derive the CRT/product-support budget,
discarded-radical error, model contraction, and all constants.  Marginal
estimates multiplied together do not prove joint approximation.

### Division of work

Fable owns `papers/ROUND2-multicutoff-fable.md`: derive the two-tier lemma
and attempt a complete schedule.  Only generalize to many tiers if two
tiers expose a genuine saving.  The hoped-for longer-term mechanism is
phase-weighted approximation with site-dependent sieve budgets, not simply
the old joint-total-variation bound with renamed parameters.

Astra owns `papers/ROUND2-multicutoff-astra.md`: independently derive the
error ledger and find where a common-cutoff restriction might reappear.
Test the explicit density approximately 1/L4 prime-index construction
first.  Check arbitrary slow divergence, endpoint counts, the prime
active-site sets, and whether the model contraction survives.

### Success and failure

First success: a correct finite unequal-cutoff bound with a genuine saving
in the JOINT error, not just the elementary phase-transfer leg.  Strong
success: its consumer proves normality for the explicit barrier set or a
new family not already covered by FreshMassZero.  Arbitrary relative
density zero is a research ambition, not a promised result.

If the joint budget recreates the old freshness condition, exhibit the
specific inequality doing so.  Test one justified phase-weighted or
conditional replacement; do not spend the whole round tuning epsilon
inside the already-refuted common-cutoff majorants.

## Pair B: one-sequence, overlapping-window countermodel

### Read

- `papers/ASTRA-2026-09-22-g4-riesz-countermodel.md`, all sections, especially
  the unfinished extension at the end.  Sections 7-8 postdate its first
  referee reply; audit only the parts you actually use.
- `OBSTRUCTION-2026-09-22-g4-lane-b-invention-round.md`
- `src/NormalNumbers/G4PrefixDecayAudit.lean` and the `windowK` definition.
- The final `agent-mail/g4/` exchanges for any intervening completion.

### Concrete proposed change

The present countermodel is a family of separate arrays, not overlapping
windows of one sequence.  Complete or refute the proposed carry lift:

    U_n = sum_{j>=1} A_{n+j}/4^j,   C_n = floor U_n,
    4 X_n = d_n + X_{n+1},
    W_{n+1} = 4 C_n - C_{n+1} + d_n.

With suitable growth/convergence and A_n>=3, the note obtains W>=0,
|W-A|<=3, and the infinite phase tail C_n+X_n.  Those identities alone
do NOT establish the required statistical laws.

Seek ONE deterministic nonnegative integer sequence W, with overlapping
windows and ordinary empirical averages at every sufficiently large M,
whose fixed-prefix laws, uniform centered-tail second-moment bounds and
scheduled nonzero Fourier coefficient coexist.  State the exact target
laws first, with the reference mean near log log M, the actual windowK
schedule, and explicit quantifiers.  Specify prefix [1,M] versus dyadic
averaging and prove any passage between them.  A triangular construction,
logarithmic average, or favorable subsequence is a weaker result, not the
requested theorem.

### Division of work

Fable owns `papers/ROUND2-shift-consistency-fable.md`: construct the lift
and its statistical estimates.  Start with a finite stationary/block
prototype if useful, then address gluing, boundary cost and intermediate
scales.  Keep those stages explicitly distinguished.

Astra owns `papers/ROUND2-shift-consistency-astra.md`: attack the finite
prefix distributions and gluing.  Bounded perturbation does not imply
small total variation: a unit change can lock parity.  Check residue laws,
overlap identities, the choice of times-4 orbit, uniform integrability,
and the finite-window versus infinite-tail phase error.

### Success and failure

Success is a proved shift-consistent obstruction showing that overlap plus
the stated summary laws still cannot supply G4 cancellation.  This would
isolate actual arithmetic correlations as an additional ingredient, not
refute G4 normality.  Exact omega singleton marginals are a stretch target:
do not silently claim that a bounded carry correction preserves them.

Alternatively derive a precise compatibility inequality that prevents
this lift from preserving the desired laws.  Determine whether it fails
only for this construction or follows from overlap itself.  If the latter,
test whether that inequality can enter an actual omega cancellation proof.
A failed carry recipe alone is not a positive G4 theorem.

## Launch prompts

In each new window, give the absolute path to this file and one sentence:

- Pair A Fable: "Read this brief; take Pair A's Fable role and begin."
- Pair A Astra: "Read this brief; take Pair A's Astra role and begin."
- Pair B Fable: "Read this brief; take Pair B's Fable role and begin."
- Pair B Astra: "Read this brief; take Pair B's Astra role and begin."

These are interactive research assignments.  No sessions were launched by
the preparation of this plan.
