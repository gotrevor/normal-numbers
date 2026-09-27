# Research trajectory: Collatz, Busy Beaver, normal numbers

**26 September correction:** scalar binary Erdős–Borwein disjunctivity, including the large-prime buffer, is already claimed in [CaptainSude’s paper](https://github.com/CaptainSude/erdos-borwein-disjunctivity/tree/bd98789a177470cc4b3e33e6769e859f6144c906).  Its Lean development takes published prime-distribution inputs as hypotheses.  The fresh target is [simultaneous words at a common position](../papers/2026-09-26-joint-lambert-disjunctivity.md), with a proposed paper proof for any finite set of distinct bases, including 2 and 4.  The scalar C2 novelty assessment below is superseded.

25 September 2026.  Review of the past week's work and current outstanding work, including live branches and fresh primary sources.  Ren/Codex synthesis with three delegated source reviews.  No research campaign launched or stopped.

## Judgment

The portfolio is producing worthwhile mathematics.  Normal numbers has the strongest trajectory: two substantial completed results and a reusable logarithmic Elliott theorem.  Collatz has gained rigorous constraints and a better account of failed approaches, but no demonstrated mechanism currently closes its headline obstructions.  Busy Beaver should concentrate on specific arithmetic dynamics and a reusable obstruction to regular certificates.  Confidence in this allocation: about 85%, not a probability of resolving a headline conjecture.

Distance to a landmark is not measured by the number of reductions completed.  A useful next statement must be true, have a credible mechanism, and expose something the original target did not already ask for.  This review found both genuine results and reductions that fail those tests.

## Evidence and snapshots

- Collatz: `collatz-moonshot`, `main`, `11794c5` (23 September).
- BB: `collatz-cryptid`, `init`, `3ba24b0`, plus 25 September BMO #9 work being staged by another session during review.
- NN main: `normal-numbers`, `wip/g5-prime-subset`, `48e981e`.  Older master and parts of STATUS/PENDING_WORK do not summarize current worktrees.
- Elliott: `nn-elliott`, `44e3cbb`, handoff lap 111.
- C4: `nn-c4`, `5acf4dd`; closing theorem at `ee38065`.
- C3-MRT: `nn-c3mrt`, `0134c0d`, with a live writer in `C3MrtSlowSched.lean`.
- Two-point: `nn-twopoint`, `5ed791a`; C2: `nn-c2`, `df29025`.

Detailed source reviews:

- [NN](REVIEW-2026-09-25-normal-numbers.md).
- [Collatz](/Users/gotrevor/src/collatz-moonshot/REVIEW-2026-09-25-trajectory.md).
- [BB](/Users/gotrevor/src/collatz-cryptid/notes/31-research-trajectory-2026-09-25.md).
- [C3 input audit and persistent Lean witnesses](/Users/gotrevor/src/nn-c3mrt/reviews/2026-09-25-input-audit/README.md).

## Corrections that change the allocation

### C3-MRT rests on false/vacuous interfaces

`TTNonPretentious g X L` chooses its positive constant after X and L.  For g identically 1, every prime summand is nonnegative, so A=1/L always works.  The proposed no-exception correlation input consequently asserts decay for the constant-one correlation, which is exactly 1.  For any fixed positive decay exponent and finite multiplicative constant, large L contradicts it.  This is a false hypothesis, not an unsolved analytic theorem.

Separately, `TwoPointNaturalCorrelation` permits a measurable real exceptional set but tests its conclusion only at natural-number scales.  That set can contain every tested integer and still have Lebesgue measure zero.  A Lean proof of the entire statement by this construction is included in the audit.  The pretentious distance also omits Dirichlet characters and uses the wrong twist-height range compared with Tao-Teravainen (2025), equation (1.18) and Theorem 3.1.

The conditional implications remain valid as implications.  Their premises cannot support the claimed mathematical trajectory.  Sparse normality and general Elliott are independent of these interfaces.  Repair the input before investing further in its quantitative descendants, then reassess the concrete nonpretentiousness certificate against the repaired definition.

The twopoint handoff's separate claim that only a prime-cube sieve input separates it from subpolynomial richness is unsupported.  TT section 5.2 uses a rationality assumption for its global mod-one identity; its alternating-sum algebra does not bound the original Weyl average.  The prime-cube lemma also uses Gowers-norm monotonicity.  `WeylTailAlmostAll` remains an additional analytic input.

### BMO #9 has a fresh solution announcement

The [BB wiki revision 8696](https://wiki.bbchallenge.org/w/index.php?title=Beaver_Math_Olympiad&oldid=8696), dated 24 September, moves BMO #9 into the solved section.  A fresh read of bb6 Discord confirms Mxdys's announcement and description of an LLM solution.  No proof artifact was located in the inspected channel export.  Retrieve and verify the proof; do not continue an original-research campaign predicated on unsolved status.  A stale machine link still says undecided.

Read-only export: `/private/tmp/bb6-since-20260923.txt`, announcement lines 148-150, discussion 181-199.  The latest attached BB6 list was 815 on 24 September.  These counts do not determine a research thread's mathematical value.

### Completed NN results need accurate positioning

C4's arbitrary exact-length classification is stronger than an abelian-normal/non-normal example.  Campbell's current [v2](https://arxiv.org/html/2603.04396v2), dated 21 August, already constructs a decimal example of the latter.  Do not describe that older existence question as still open.

C-prime's fully unwound statement is already proved in `PrimeModelGradedStatement.lean`.  Its abstract geometric-mass interface does not enlarge the reachable class: the paper gives the relevant reverse estimate.  Some task-board prose is stale on both points.

## Top ten, ranked by expected research value

### 1. NN: consolidate sparse-prime normality

**Established:** if P has divergent reciprocal sum and `sum_{sqrt(N)<p<=N, p in P} 1/p -> 0`, then `sum_{p in P} 1/(4^p-1)` is normal in base 4.  This covers relative-density-zero prime sets with divergent reciprocal sum, and some bursty sets of upper relative density one.

**Next:** independent novelty review and a readable proof centered on the graded lower sieve and joint-state estimate.  Extract the reusable argument charging each prime band by its active sites.  The audit theorem and basic illustrative constructions already exist.

**Larger door:** normality for a broad arithmetic family and a reusable multiscale sieve mechanism.  This is the strongest completed mathematical return of the week.  All primes fail the hypothesis: their square-root-window reciprocal mass tends to log 2.  General bases need substantive estimates, not a wrapper.

### 2. NN: connect general logarithmic Elliott to the actual omega phases

**Established:** the general coprime-multiplicative, two-affine-form logarithmic theorem is implemented.  The concrete z^omega application still needs uniform archimedean prime-twist bounds.  Low-height estimates have advanced; moderate and near-maximal polynomial heights remain, including the Vinogradov-Korobov range.

**Next:** assemble the completed low-height bridge and audit the exact two remaining bands against the literature.  Prove those interfaces before broader extension.

**Larger door:** a reusable formal engine for logarithmic correlations of multiplicative functions, beyond this constant.  This substantial formalization opportunity uses known mathematics.  It supplies logarithmic averages, not the ordinary averages needed for G4 normality.

### 3. NN: extract C4's abelian-normality spectrum theorem

**Established:** all possible sets S of positive lengths at which a binary sequence has the binomial count-of-ones distribution are exactly the empty set and the sets containing 1.  Arbitrary infinite and nonperiodic S are covered.

**Next:** referee the readable construction and locate it in the abelian-normality/spectrum literature.  Develop a paper around the classification if new in this form.  A subsequent mathematical extension is a computable witness for decidable S; that is not established here.

**Larger door:** a complete realization theory of which statistical tests can hold independently.  This could stand alone as a contribution and is independent of the analytic bets.  It is not a route to normality of a named arithmetic constant.

### 4. NN: C2 with a selectable modulus avoiding the exceptional list

**Established:** a substantial CRT/divisor-moment layer for the Erdős-Borwein family.  The universal `PrimeDensityAP` interface permits `Y/M=0` with no primes, while its unfinished consumer needs a nonempty set.

**Next:** choose the large prime-search scale Y first.  Alford-Granville-Pomerance gives finitely many exceptional moduli.  Omit one prime factor of each from the candidate pool, then build the kill modulus from surviving primes.  Audit CRT pinning, gcd estimates, the survivor exponent, and the size budget.  `exists_pin_progression` already accepts arbitrary injective prime families; specialized downstream lemmas need generalization.

Campbell uses exception avoidance for a narrower digit result in [his May paper](https://arxiv.org/html/2605.24160v1).  Our proposed adaptation is unproved.  The local size diagnosis also needs correction: `log M=O_b(K^4)` and `log Y` of size `b^(K/4)` give `M<=exp(O_b((log log Y)^4))`, inside any fixed `Y^delta` range eventually.  This does not by itself remove exceptional characters, but makes avoidance worth testing.  See the NN note for quantifier order and the bounded excluded-prime pool.

**Larger door:** every finite word occurs in `sum_n 1/(b^n-1)`, b>=3, a recognizable arithmetic constant family.  This would be disjunctivity, not normality or a result for the binary Erdős-Borwein constant.

### 5. Collatz: finite temporal packing with a coverage theorem

**Established on paper:** sufficiently long Christoffel first-crossing words cannot be realized with a linearly bounded start and distinct odd states.  Time order provides a constraint where unordered spacing failed.  Finite packing gives `L+1=O(X^beta log X)`, beta<1, for distinct states bounded by X.

**Next:** first audit the concrete periodic-branch composition found during this review: packing forces an early repeat; the long remaining balanced Beatty factor forces a Christoffel cycle word; Knight excludes the nontrivial integral cycle.  The trivial cycle has the wrong frequency.  This derivation is unproved locally and concerns only the existing family.  Then seek a broader word-family coverage theorem with a prefix-height bound.  Details: [candidate note](/Users/gotrevor/src/collatz-moonshot/RESEARCH-2026-09-25-packing-balanced-period-candidate.md).

**Larger door:** exclude actual integer trajectories in whole families with a mechanism specific to multiplier 3.  Arbitrary words, arbitrary heights, and nontrivial cycles remain outside the present result.

### 6. BB: Bigfoot's recovery invariant

**Established:** six-case arithmetic dynamics and considerable machine scaffolding.  The arithmetic gap is a recovery/cascade invariant keeping the exponent parameter away from fatal small values.  A separate machine-to-arithmetic simulation gap remains.

**Next:** retain pattern, residue, and exponent through a full decrement-and-recovery cycle, using the recorded failed invariants as controls.  Demand an inductive predicate on reachable states; then close the separate simulation correspondence if the arithmetic proof succeeds.

**Larger door:** settle a major BB(3,3) behavior and possibly expose a method for related residue-affine machines.  No ordinary-Collatz theorem currently transfers to it.  One Bigfoot proof would not settle BB(3,3) or BB(6).

### 7. NN: the growing-prime localized logarithm

**Proposal:** normality of `sum_{P+(m)<=Y(m)} 1/(m*2^m)` for slowly growing unbounded Y, with prime count below `(1-epsilon) log_2 log n`.  This is a different coefficient family from C-prime.

**Next:** audit Vandehey's constants uniformly in the growing prime set.  Repair the segment cutoff: intervals merely longer than sqrt(N) do not preserve the proposed exponent margin.  Discarding intervals below `N exp(-(log log N)^4)` appears to cost o(N) while retaining the needed length.  The complete analytic argument remains to be checked.

**Larger door:** an explicit normal constant with unbounded prime support.  The method remains in a density-zero index regime and does not prove normality of log 2.  This is a bounded paper audit before a proof campaign.

### 8. BB: a universal obstruction to regular certificates

**Target:** a concrete machine, such as the proposed Finned #3/Skelet #17 examples, for which no regular closed tape-language contains its orbit while excluding halt.

**Next:** a pumping/Myhill-Nerode obstruction valid for arbitrary finite-automaton size, connected to machine semantics.  Soundness of positive regular certificates is useful infrastructure but does not prove this negative theorem.

**Larger door:** identify behaviors requiring stronger invariant languages, guide decider development, and share obstructions across cryptids.  It need not decide the target machine's halting behavior.

### 9. NN: actual all-scale arithmetic cancellation for G4

**Target:** normality of `G4=sum_p 1/(4^p-1)`.  The week's deterministic countermodel rules out fixed-window Poisson laws, generic CLTs, and shift consistency as sufficient inputs.  Full scheduled-window decay can merely restate normality.

**Next:** repair C3's interfaces, then formulate a target-specific ordinary two-site correlation for the actual z^omega phases.  Test intermediate claims against the countermodel and state the extra step to growing depth.  Keep all-scale and almost-all-scale goals distinct.

**Larger door:** genuine arithmetic cancellation could advance C1/C3 and ultimately normality.  There is no surviving all-scale mechanism yet; two-site cancellation alone leaves the growing-depth carry problem.  Count these correlated bets once.

### 10. Collatz: the many-run integer-admission obstruction

**Target:** exclude a small canonical integer residue pointwise at first crossing.  A lower bound on run count alone does not suffice.  Coefficient crossing is equivalent to nondivergence; CST supplies the separate no-cycle implication.

**Next:** authorize a proof campaign only after an order-sensitive inequality survives Christoffel/P6 controls, 2305/2313, and 5n+1, with a coverage rule for an unbounded class.  A further fixed-prefix filter or fixed-run bound does not clear the existing gate.

**Larger door:** direct relevance to the central Collatz obstruction, with enormous possible value.  This has the least concrete mechanism in the list.  Maintain a mechanism-research slot rather than a routine proving treadmill.

## Allocation and exclusions

Give the largest share of sustained effort to NN's completed results, the concrete Elliott application, and the bounded C2 modulus test.  Use Collatz effort for mechanism discovery and family exclusions.  Make BB effort specific to a dynamics or a reusable obstruction.

Short follow-up outside the ten: retrieve the announced BMO #9 proof and verify stream/TM semantics, then assess transfer.  Do not resurrect the August collapse argument; it was refuted in its own thread.

Do not fund another generic G4 CLT, a renamed full-Weyl hypothesis, larger fixed Collatz run rungs, an Antihydra Baker estimate already in the peer negative inventory, another blind bulk BB sweep, or a BMO #9 campaign premised on unsolved status.  No current result establishes a theorem-level bridge from fixed 3n+1 to the BB cryptids.

## Review limits

This was a source/statement/strategy review, not a rebuild or independent proof of every reported theorem.  Completed-result assessments use exact statements and recorded audits.  New C3 witnesses were compiled against existing live definitions.  Literature checks establish the cited comparisons, not universal priority.  The strongest speculative mechanisms identified here are C2 modulus choice, temporal packing with coverage, and the uniform-constant audit for the growing-prime logarithm.
