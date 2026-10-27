# Three second-round candidates for pi disjunctivity

These are proposals for short mechanism tests, not three established proof routes or authorization to launch long jobs.  The statements and conditional transfers are in [`RoundTwo.lean`](../../src/NormalNumbers/PiDisjunctiveRoutes/RoundTwo.lean).  Read [MAZE.md](../../MAZE.md) before acting on them.  The first three routes remain retired.

The local screening covered the original-route and follow-up Maze entries, the pi-route notes, and searches of the statement corpus for these mechanisms.  No literature-priority claim is made.  No web search was used.

## Route 4: prove that an exact spigot cannot avoid a word forever

**Object.** `HypergeometricPiIdentity` records

\[
\pi=\sum_{n\ge0}\frac{2^{n+1}(n!)^2}{(2n+1)!}.
\]

The corresponding unread-tail maps are `z -> 2 + (n+1)z/(2n+3)`, with tails in `[2,4]`.  `SpigotState`, `refine`, `CanEmit`, `emit`, and `spigotRun` specify the exact integer machine for the fractional part.  Its state retains the input index and all numerator/denominator information.  `SpigotSound` is the ordinary correctness input, explicitly unproved in this module.

**Proposed mechanism.** Compose this machine with the finite automaton that detects a chosen word.  Search for an inductive arithmetic invariant and a decreasing rank on the states before detection.  The proof must exploit the actual coefficients `n+1` and `2n+3`.  This is program termination with arithmetic state, not a finite carry automaton supplied only with an irrationality bound.

**Precise quantitative conjecture.** `SpigotEscapeBudget`: some fixed `C` suffices to produce every length-`k` word within `C (k+1) 2^k` read/emit steps.  `pi_disjunctive_of_spigotEscape` proves the transfer assuming soundness.  The budget alone is a stronger digit assertion, not progress; the proposed contribution would be an invariant explaining it.

**First discriminating test.** For all words of lengths 2 through 4, seek one reusable family of inequalities/congruences in `(n,p,r,q,automaton state)`.  A certificate listing the already-computed trajectory does not count.  Require it to distinguish the rational tail map `z -> 5/3+z/2`, whose fixed point is `10/3` and whose fractional digits alternate.

**Calibration already run.** `scripts/pi_round_two_spigot.py` computes exact integer enclosures.  It checks the first 256 output bits against an independent Machin-series interval and checks the rational control.  Its finite `C=4`, length-at-most-8 observation is recorded as the unproved finite node `SpigotCalibrationC4`; output is in `round-two-spigot-probe.json`.  This checks the machine and a candidate constant.  It supplies no invariant and no evidence of a uniform proof.

**Stop condition.** If the available invariants reduce to interval width, irrationality, or a table of the emitted digits, retire that certificate family.  A bigger digit computation is not a reason to continue.

**Maze distinction.** This uses a different exact recurrence and proposes a proof invariant, not a replacement prime reservoir.  Nonetheless, exactness by itself is already known to be insufficient as an argument: reconstructing the true sequence does not prove visits.  The old approximate-forcing countermodels cannot simply be dismissed without producing the new invariant.

## Route 5: a polynomial certificate tied to sin(pi) = 0

**Object.** `OscillatorIntegralIdentity` records the integration-by-parts identity

\[
 P(0)+P(\pi)=\int_0^\pi (P''(t)+P(t))\sin t\,dt.
\]

For a rational polynomial with `P''+P>0` on `[0,4]`, the right side is positive.  That elementary analytic input is `OscillatorPositivityBridge`, explicitly unproved here.

**Proposed mechanism.** Given a forbidden binary word `w`, construct a rational polynomial `P_w` with positive oscillator residual, but with `P_w(0)+P_w(x)<=0` for every `x` in `[3,4]` whose expansion avoids `w`.  Then pi cannot be one of those numbers.  The word-avoidance automaton supplies recursive cylinder constraints; the hoped-for new ingredient is a uniform polynomial-positivity certificate using those constraints.

**Precise conjecture.** `OscillatorCertificateSupply`.  The conditional transfer is `pi_disjunctive_of_oscillatorCertificates`.  There is no claim that existence of these certificates is logically easier than disjunctivity.  What would make the route useful is a construction using the word's automaton, not prior knowledge of where the word appears in pi.

**First discriminating test.** Search low-degree rational polynomial certificates for small nontrivial forbidden words, using positivity on cylinder intervals and a recursive certificate for the remaining automaton states.  Inspect the proof object: does a common construction depend on the word's overlap structure, or does it merely isolate pi into a cylinder already known to contain the word?  The latter is a baseline digit-search procedure, not the proposed mechanism.

**Stop condition.** Retire any certificate family whose only successful construction needs the first occurrence of `w` as input, or whose proof reduces to locating that occurrence.  Do not spend a long lap proving the elementary integration identity while the certificate construction is missing.

**Maze distinction.** This uses a pi-specific analytic identity to certify exclusion from an entire forbidden-word set.  It is not an irrationality-measure estimate for an individual rational approximation, and it neither assumes odd orbit invariance nor asks a geometric counting approximation to cover an interval.

## Route 6: retain a chosen embedding through the radical tower

**Object.** Define `Q_0=X`, `Q_(n+1)(X)=Q_n(X^2-2)`.  `radicalPolynomial_eval_two` proves `Q_n(2)=2`.  `RadicalRootIdentity` records the distinguished root `a_n=2 cos(pi/2^(n+1))`; `RadicalPerimeterLimit` records the polygon limit `2^(n+1) sqrt(2-a_n) -> pi`.  Those two classical bridges are stated but not proved here.

**Proposed mechanism.** Use relative norms at successive quadratic extensions, retaining the positive real branch at every step.  Try to turn repeated forbidden-word constraints into a loss in the product of conjugate factors that cannot be reconciled with the exact polynomial value `Q_n(2)=2`.

This is the highest-risk proposal.  A full norm usually loses precisely the information we need: which conjugate approximates pi.  The unexplored question is whether relative norms plus branch inequalities preserve enough information.  No word-dependent norm estimate has been obtained.

**Precise broader conjecture.** `AlgebraicAngleDisjunctivity`: for algebraic real `a` with `-2<a<2`, the angle `2 arccos(a/2)` is binary disjunctive.  Setting `a=0` gives pi, as proved by `pi_disjunctive_of_algebraicAngles`.  This stronger conjecture describes what a general successful branch-sensitive argument might establish; it is not itself the missing norm estimate.

**First discriminating test.** Carry the first few quadratic steps with interval constraints on the distinguished branch and exact polynomial identities on all branches.  Determine whether a forbidden word causes a quantitative deficit after the other conjugates are allowed their full admissible ranges.  Merely obtaining the polygon error bound or recovering `Q_n(2)=2` does not count.

**Stop condition.** If every putative loss on the chosen branch is compensated by the other conjugates, retire that norm inequality.  Do not replace it with an ordinary height bound, a finer polygon approximation, or an assumed distribution of conjugates.

**Maze distinction.** The proposed input is exact algebraic conjugacy, not just a new approximation to pi.  A polygon-residue cover would repeat the retired disk-shadow route and is expressly excluded.

## Order and evidence

My first choice is the **oscillator-certificate test** (60% confidence in this ranking), followed by spigot invariants.  Both have explicit proof objects that can reveal whether anything beyond digit computation is happening.  The radical-norm idea should receive only its compensation test before any serious commitment.

All three crucial inputs remain open.  The three Lean transfers are conditional reductions, not advances on their premises.

## Bounded pilot results, 2026-10-26

Three Opus/low laps supplied the following results.  The three narrowly scoped
failed mechanisms now have checked Maze links; the broader routes are not declared
impossible.  See [the run receipt](pilots/review.md) for validation and provenance.

- **Oscillator:** `cubicBlindAtThree` and `quarticEndpointObstruction` rule out
  degree at most four for simultaneous exclusion of 3 and 4.  The exact positive
  quadrature is `quarticQuadratureIdentity`; `quarticRejectsThree` is its control.
  An exact rational quintic calculation suggests a sharp positive control,
  formally stated as `MinimumDegreeWordOne` but not yet proved.  The next bounded
  task is [that calibration](pilots/oscillator-followup.md), not a digit search.
- **Spigot:** `positiveWidthAlternatingPrefix` and `no_index_only_emit_rank`
  exclude input-index-only waiting bounds uniform over positive-width states.
  The constructed states are not claimed reachable from the pi initial state.
  No pi-specific invariant establishing `SpigotEscapeBudget` was found.
- **Radicals:** `branchNorm_eq` proves exact compensation through the entire
  signed radical tree at every depth; `not_uniform_branchLoss` refutes a uniform
  gain in the full product.  A word-sensitive estimate retaining a distinguished
  branch is still missing.  More full-product calculations will not supply it.

The next research filter is whether a higher-degree oscillator construction uses
the word automaton independently of a known occurrence in pi.  A degree-five
certificate for the single word `[1]` would calibrate the method, not establish
that missing construction or prove pi disjunctive.
