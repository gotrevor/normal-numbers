# Normal Numbers: where the proof stands

**Project map · 26 September 2026**  
[Visual edition](OVERVIEW.html) · [Detailed research review](docs/REVIEW-2026-09-25-research-trajectory.md)

## The destination

**Prove that an explicit, naturally arising number has genuinely random-looking digit frequencies.**  The central candidate here is the prime Lambert constant:

**G₄ = ∑ over primes p of 1/(4ᵖ − 1).**

We know that **every finite base-four word occurs** in G₄.  We do not know that each length-L word occurs with frequency exactly 4⁻ᴸ.  That second statement is normality, and remains the main open destination.

The programme has produced substantial complete results around this goal.  The remaining distance to G₄ normality includes new arithmetic, not just assembly of the results already proved.

## The map

![Normal Numbers map: completed sparse-prime and digit-spectrum theorems, the missing ordinary growing-carry estimate for G4, and the separate Elliott, C3, and C2 branches.](docs/overview.svg)

**Reading the map:** solid arrows are proved reductions, with the labeled open inputs still required.  Dashed arrows are missing research steps.  Separate branches do not imply one another.  The completed sparse-prime theorem does not apply to the full prime set.

## What we have actually established

| Result | What it says | Its boundary |
|---|---|---|
| **G₄ is disjunctive** | Every finite base-four digit word appears. | Occurrence does not determine frequency. |
| **C′: a family of prime Lambert constants is normal** | Keep a prime set P with divergent reciprocal sum but vanishing reciprocal mass between √N and N.  Its Lambert constant is base-four normal. | All primes fail the vanishing-mass condition.  This is a finished theorem about a different family. |
| **C4: complete classification of abelian length spectra** | For binary digits, every set of positive lengths that is empty or contains 1 can be exactly the set of lengths with the correct binomial count of ones. | This statistic forgets digit order.  It does not establish normality of G₄. |
| **General two-point logarithmic Elliott** | A general theorem controlling logarithmically averaged two-point correlations of multiplicative functions is proved. | Applying it to the relevant prime-factor function still needs an estimate; its averages are logarithmic. |

Earlier completed work includes an explicit constructed number that is simultaneously absolutely normal, continued-fraction normal, and Khinchin typical.  The move toward naturally specified arithmetic constants introduced the new difficulties shown here.

## Where we are pressing

### Main frontier: the actual carries of G₄

Writing G₄ as **∑ ω(n)/4ⁿ**, where ω(n) counts distinct prime factors, exposes the difficulty: the coefficient at one position can carry into earlier digits.  Normality requires cancellation for the **actual growing carry window**, averaged over ordinary initial intervals.

Fixed-size prime-factor statistics, Poisson models, and even consistent distributions under shifts are insufficient.  Counterexamples to those generic routes are already recorded.  A successful input must use more of the specific arithmetic of ω.  The sufficient Fourier criterion is proved; the needed arithmetic cancellation is open.

### Elliott: a concrete analytic input, followed by a genuine strength gap

The latest work reduces the logarithmic two-point application to a **sublinear power-of-log bound for the logarithmic derivative of the Riemann zeta function**, in the specified height range.  The existing bound has exponent 9; the consumer needs an exponent below 1.

Closing that input would deliver the logarithmic application.  It would not automatically give ordinary averages, nor control arbitrarily growing carry depth.  Those gaps are drawn explicitly in the map.

### C3: every word with positive lower frequency

This is a meaningful intermediate target, called **richness**, for every prime Lambert constant G_b with b ≥ 3.  The September 25 audit found incorrect or vacuous inputs; the live branch has since repaired their statements.  Its central missing ingredient is now faithfully stated: **K-point cancellation at every sufficiently large scale**, without exceptional scales and with quantitative control as K grows, together with the required uniform analytic estimates.

The published two-point result with exceptional scales does not supply that input.  The `UniformResonantMass` proposition itself is already proved; an unfinished alternate proof is not a new mathematical barrier.

### C2: every word in an Erdős–Borwein constant

For **E_b = ∑ₙ≥₁ 1/(bⁿ − 1), b ≥ 3**, the target is disjunctivity.  Much of the digit-forcing and divisor control is in place; the prime-survivor argument is open.

The review proposes choosing the search height first, then selecting the primes in the Chinese-remainder construction to avoid the finite exceptional moduli in an applicable prime-distribution theorem.  This redesign is **proposed, not implemented**.  Its first test is whether that selection preserves every congruence and size requirement of the digit construction.

## What would count as a change in position?

| Next result | What changes |
|---|---|
| Expose C′ and C4 as readable standalone proofs | Makes two completed mathematical achievements independently assessable. |
| Supply Elliott's sublinear analytic bound | Completes a concrete logarithmic application. |
| Prove the faithful C3 inputs | Every word gains positive lower frequency, still short of normality. |
| Make C2's prime-survivor construction work | Completes disjunctivity for the stated Erdős–Borwein family. |
| Prove ordinary cancellation through G₄'s growing carries | Reaches G₄ normality via the existing criterion. |

The growing-prime localized-logarithm proposal is another independent normality prospect, still at paper-audit stage.  It is not a route already connecting these branches to G₄.

## Evidence and upkeep

Snapshot: main `wip/g5-prime-subset` at `97215f6`; worktrees `nn-elliott:d420003`, `nn-c3mrt:7cedd1b`, `nn-c2:df29025`, `nn-c4:5acf4dd`.  These are snapshots, not promises that the branches stay still.

Main-tree sources: [C′ audit statement](src/NormalNumbers/PrimeModelGradedStatement.lean), [carry criterion](src/NormalNumbers/G4WindowK.lean), [precise rungs](src/NormalNumbers/CastingOut.lean), and [retired routes](src/NormalNumbers/Maze.lean).  Worktree sources: [C4 theorem](../nn-c4/src/NormalNumbers/AbelianWindowBuild.lean), [Elliott frontier](../nn-elliott/HANDOFF-elliott-2026-09-25-lap121.md), [C3 direction](../nn-c3mrt/DIRECTION.md), and [C2 construction](../nn-c2/src/NormalNumbers/SwingC2.lean).  Worktree links are local to this checkout layout.  The September 25 review predates C3's repair and the latest Elliott reduction.

This is the maintained reader's map.  Update it when a frontier is proved, refuted, or replaced; keep proof details in their existing source and research notes.  Diagram source: [docs/overview.dot](docs/overview.dot).  Rebuild the visual edition with `make -f docs/overview.mk`.
