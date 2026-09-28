# Normal Numbers: where the proof stands

**Project map · 28 September 2026**  
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
| **Simultaneous Lambert disjunctivity (conditional)** | For finitely many distinct bases, including dependent ones such as 2 and 4, any prescribed words occur in the constants E_b = ∑ 1/(bⁿ − 1) at one common digit position, infinitely often. | Assumes two named prime-distribution inputs (primes in progressions with few exceptional moduli, and primes in (L, 2L)).  This is about occurrence, not frequency. |
| **Wall: rational maps preserve normality** | If x is normal in base b, so is qx + r for every rational q ≠ 0 and every rational r. | A classical theorem, now machine-checked. |
| **Philipp: continued-fraction ψ-mixing** | Gauss-measure cylinder sets mix at a geometric rate. | A classical input, proved rather than assumed. |
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

This is a meaningful intermediate target, called **richness**, for every prime Lambert constant G_b with b ≥ 3.  The September 25 audit found incorrect or vacuous inputs; their statements have since been repaired, and the branch is merged into the main tree.  Its central missing ingredient is now faithfully stated: **K-point cancellation at every sufficiently large scale**, without exceptional scales and with quantitative control as K grows, together with the required uniform analytic estimates.

The published two-point result with exceptional scales does not supply that input.  The `UniformResonantMass` proposition itself is already proved; an unfinished alternate proof is not a new mathematical barrier.

### Erdős–Borwein: simultaneous words across distinct bases

Scalar binary disjunctivity already has a [peer paper and conditional Lean development](https://github.com/CaptainSude/erdos-borwein-disjunctivity/tree/bd98789a177470cc4b3e33e6769e859f6144c906).  Our simultaneous version is now **formalized**: `jointLambertDisjunctivity` proves that prescribed words occur in finitely many constants **E_b** at a **common digit position**, infinitely often, even for bases 2 and 4.  The [paper proof](papers/2026-09-26-joint-lambert-disjunctivity.md) is the blueprint.  Two analytic inputs remain hypotheses: primes in progressions with few exceptional moduli, and primes in every interval (L, 2L).  Discharging them would make the theorem unconditional.  The quantitative occurrence count is a separate target.  Our scalar C2 implementation remains incomplete.

### Continued fractions: Vandehey's open problem

Vandehey (2017) asks whether a Möbius image of a continued-fraction-normal number is again continued-fraction normal.  His §3 relied on a Moshchevitin–Shkredov criterion that Airey and Mance refuted.  That section is now **proved unconditionally**: along every CF-normal x, the joint frequency of a digit window and a projective class mod a prime D converges to its expected value.  The remaining crux is a uniform block-frequency limit along the image.  A counterexample to the Moshchevitin–Shkredov criterion as stated, using the digits 1, 2, 3, …, is stated in Lean but not yet proved.

## What would count as a change in position?

| Next result | What changes |
|---|---|
| Expose C′ and C4 as readable standalone proofs | Makes two completed mathematical achievements independently assessable. |
| Supply Elliott's sublinear analytic bound | Completes a concrete logarithmic application. |
| Prove the faithful C3 inputs | Every word gains positive lower frequency, still short of normality. |
| Discharge the joint Lambert prime inputs | Makes common-position words in distinct constants unconditional. |
| Prove Vandehey's uniform-frequency crux | Möbius images of CF-normal numbers are CF-normal. |
| Prove ordinary cancellation through G₄'s growing carries | Reaches G₄ normality via the existing criterion. |

The growing-prime localized-logarithm proposal is another independent normality prospect, still at paper-audit stage.  It is not a route already connecting these branches to G₄.

## Evidence and upkeep

Snapshot: one checkout, `wip/g5-prime-subset`, with every campaign branch merged on 27–28 September and `lake build` covering every module.  Current fronts and the work queue: [STATUS.md](STATUS.md), [PENDING_WORK.md](PENDING_WORK.md).

Sources: [C′ audit statement](src/NormalNumbers/PrimeModelGradedStatement.lean), [carry criterion](src/NormalNumbers/G4WindowK.lean), [precise rungs](src/NormalNumbers/CastingOut.lean), [C4 theorem](src/NormalNumbers/AbelianWindowBuild.lean), [joint Lambert](src/NormalNumbers/JointLambertDisjunctivity.lean), [Elliott ledger](src/NormalNumbers/ElliottLedger.lean), [C3 headline](src/NormalNumbers/C3MrtBlockDefect.lean), [Vandehey §3](src/NormalNumbers/VandeheyClassEquidist.lean), [C2 construction](src/NormalNumbers/SwingC2.lean), and [retired routes](src/NormalNumbers/Maze.lean).  The September 25 review predates C3's repair and the latest Elliott reduction.

This is the maintained reader's map.  Update it when a frontier is proved, refuted, or replaced; keep proof details in their existing source and research notes.  Diagram source: [docs/overview.dot](docs/overview.dot).  Rebuild the visual edition with `make -f docs/overview.mk`.
