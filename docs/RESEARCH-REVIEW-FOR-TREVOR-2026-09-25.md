# Research review: Collatz, Busy Beaver, and normal numbers

**26 September correction:** scalar binary Erdős–Borwein disjunctivity, including the large-prime buffer, is already claimed in [CaptainSude’s paper](https://github.com/CaptainSude/erdos-borwein-disjunctivity/tree/bd98789a177470cc4b3e33e6769e859f6144c906).  Its Lean development takes published prime-distribution inputs as hypotheses.  The fresh target is [simultaneous words at a common position](../papers/2026-09-26-joint-lambert-disjunctivity.md), with a proposed paper proof for any finite set of distinct bases, including 2 and 4.  The scalar C2 novelty assessment below is superseded.

September 25, 2026

## Are we on a good trajectory?

**Yes, but unevenly.**  Normal numbers (NN) has the strongest trajectory: substantial completed mathematics, reusable analytic machinery, and credible next steps.  Collatz has gained useful constraints and eliminated misleading approaches, but its central obstruction still needs a new mechanism.  Busy Beaver (BB) warrants focused work on particular machines and proof methods.

My confidence in that assessment is **85%**.  The ranking below weighs mathematical reach against the credibility of the next step.

## Two findings that change the priorities

**The C3-MRT work needs a correction before further investment.**  Its current condition for an arithmetically irregular function also admits the constant function 1.  That makes the proposed correlation-decay hypothesis false: a constant correlation stays at 1.  Separately, the formal statement allows its exceptional set to contain every tested integer scale while costing zero measure.  I preserved reproducible mathematical witnesses of both defects.  The independent sparse-normality and Elliott results are unaffected.

**BMO #9 was announced solved on September 24.**  Its immediate next task is retrieving and checking that proof.  We should update our understanding of the problem before continuing an independent invariant search.

## The ten most useful threads, in order

### 1. NN: consolidate sparse-prime normality

The theorem already proves normality for a broad family of prime Lambert sums, including sparse prime sets whose reciprocals have a divergent sum.  Normality means every finite digit block occurs with its expected frequency.

**Next:** extract the graded sieve argument into a clear mathematical account, obtain independent review, and establish its place in the literature.  **Potential:** a reusable method for arithmetic normality.  The set of all primes fails the present hypothesis, so reaching G4, the Lambert sum over all primes, requires another idea.

### 2. NN: finish the concrete application of logarithmic Elliott

The general theorem is implemented.  Connecting it to the prime-factor-count functions used by NN still requires uniform estimates in the remaining frequency ranges.  Those are identifiable analytic tasks grounded in known mathematics.

**Next:** close those specific estimates and assemble the application.  **Potential:** a substantial reusable tool for correlations of multiplicative functions.  Its logarithmically weighted averages remain weaker than the ordinary averages needed for normality.

### 3. NN: develop C4's complete classification

You can realize exactly any set of positive window lengths containing 1, or the empty set, as the lengths with the correct binomial count-of-ones distribution in a binary sequence.  This is considerably more substantial than a single example separating abelian normality from ordinary normality.

**Next:** literature review and a readable proof; afterward, investigate computable witnesses for decidable sets.  **Potential:** a realization theory for which statistical tests can hold independently.  This contribution is independent of the difficult analytic bets.

### 4. NN: use selectable moduli in the Erdős-Borwein construction

This is the most promising fresh NN move from the review.  Choose the analytic scale first, then select the primes used in the Chinese remainder construction so its modulus avoids the finite exceptional list in the prime-distribution theorem.  The generic CRT lemma already permits selectable primes.

**Next:** check that the size, divisor, and survivor estimates survive this choice.  **Potential:** every finite word occurring in the Erdős-Borwein family for bases at least 3.  That would prove disjunctivity, a weaker property than normality.  It would not establish the binary case.  A recent paper uses this maneuver for a narrower digit result.

### 5. Collatz: close the repeated-state branch of finite packing

There is a precise candidate argument: packing forces an early repeat; the long remaining balanced parity pattern forces a Christoffel cycle; Knight's theorem excludes the nontrivial integral cycle.

**Next:** write and independently check that composition.  **Potential:** completely exclude the existing Christoffel candidate family when the starting value grows at most linearly with word length, then seek broader coverage.  The proposed strengthening is not yet proved, and its scope is much smaller than the full Collatz conjecture.

### 6. BB: find Bigfoot's recovery invariant

Follow the exponent through a complete decrement-and-recovery cycle, retaining the pattern and residue information that earlier invariants discarded.  The correspondence between the arithmetic model and the actual Turing machine is a separate remaining obligation.

**Next:** find an inductive invariant that excludes the fatal small-parameter states, then close that correspondence.  **Potential:** settle a major behavior in the three-state, three-symbol Busy Beaver problem and possibly uncover a method for related machines.  This has high value and low present tractability.

### 7. NN: audit the growing-prime localized logarithm

The proposal allows the prime support to grow while preserving normality.  Its immediate test is concrete: track Vandehey's constants uniformly and repair the segment-length cutoff in the argument.

**Next:** a bounded mathematical audit before a formalization campaign.  **Potential:** an explicit normal constant with unbounded prime support.  This would be a structural advance beyond fixed-support constructions, but it does not currently reach normality of log 2.

### 8. BB: prove an obstruction to regular certificates

For a concrete candidate machine, prove that no finite automaton can describe a closed tape-language containing its orbit while excluding halt.  The argument must apply to arbitrary automaton size.

**Next:** develop the pumping or Myhill-Nerode obstruction and connect it to the machine's transitions.  **Potential:** explain which cryptids require stronger invariant languages and guide new deciders.  This could be a reusable mathematical result even without deciding that machine's behavior.

### 9. NN: pursue actual arithmetic cancellation for G4

Repair the C3 statements, then isolate a specific ordinary two-point correlation for the actual arithmetic functions.  The week's countermodels show why generic central limit theorems, fixed-window laws, and shift consistency cannot finish the job.

**Next:** identify cancellation that uses the arithmetic itself, and state the additional step needed as window depth grows.  **Potential:** genuine progress toward G4 normality.  Even two-point cancellation leaves the growing-depth carry problem.  These overlapping routes deserve one research allocation.

### 10. Collatz: keep many-run integer admission central

The remaining challenge is an inequality that excludes actual integer realizations, respects the order of the trajectory, and covers an unbounded family.  More bounds for a fixed number of runs or fixed-length prefix filters will not supply that.

**Next:** require a proposed mechanism to survive the recorded adversarial examples and come with a coverage argument.  **Potential:** direct progress on the central Collatz obstruction.  Its enormous upside earns a place here; the absence of a surviving mechanism puts it last.

## Where I would put the effort

Put the largest sustained effort into **1-4**.  The most interesting concrete new tests are **C2's modulus choice** and **Collatz's packing-to-Knight composition**.

Keep the larger conjectures driving the questions, while demanding a demonstrable mathematical advance from each campaign.  Completed theorems, reusable methods, and decisive refutations all count as advances.  Another reduction earns its place when it makes the remaining mathematics more accessible.

The larger landmarks remain possible destinations.  The current evidence supports a productive research programme, especially in NN; it does not yet support a claim that full Collatz or G4 normality is close.
