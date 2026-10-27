# Retiring research routes and screening new ideas

The Maze preserves both **mathematical findings** and **research decisions** so future sessions do not spend another campaign rediscovering the same obstruction or unresolved crux.  A route can be abandoned because we cannot make it tractable with current methods.  An impossibility theorem is not a prerequisite for recording that decision.

Read this file before proposing new ideas, retiring a route, or reopening one.  `src/NormalNumbers/Maze.lean` is the register; `MazeAudit.lean` connects its entries to Lean declarations and checks their coverage.  Keep this policy linked at the top of both files and in `AGENTS.md`.  Other repositories adopting the practice should likewise link their policy from every Maze register.

## Separate the mathematical claim from the research decision

| Finding or decision | Required record | What it does not establish |
|---|---|---|
| A mechanism is false | Precisely quantified Lean proposition and counterexample/refutation, with its hypotheses and scope | That every variant of the broader approach is impossible |
| A criterion is equivalent to the target | Lean equivalence theorem | That no useful proof can pass through that criterion |
| A reduction works but its premise is unproved | Named premise `Prop`, proved transfer, and difficulty explanation | The premise, or the goal |
| A paper argument or experiment supports a claim | Lean statement with explicit admitted/open status; reproducible evidence and controls | A kernel-verified proof or an infinite conclusion from finite data |
| We abandon a route as too hard with current methods | `Verdict.abandonedIntractable`, linked mathematical findings and open crux, attempted methods, decision scope, and reopening requirements | Absolute intractability, unprovability, or falsity of the target |

**“Too hard” is a research judgment.**  Store it explicitly as such in Lean's register data.  Do not invent a proposition asserting impossibility merely to make the decision look proved.  Conversely, do not leave the route eligible for rediscovery just because no impossibility theorem exists.

`Tier.kernel` on a decision row describes the supporting mathematical findings, not a proof that the decision is correct.  A proved conditional theorem still requires its hypotheses.  Inspect types as well as `#print axioms`.  The audit checks declarations and links; it does not validate prose, historical accuracy, or a difficulty judgment.

## Before offering “three new ideas”

1. Read the Maze and its links, then search the relevant statement files and route notes.  A missing register entry is not evidence that an idea is new.
2. Match the **mechanism**, including aliases, coordinate changes, parameter changes, splits into auxiliary constants, and equivalent sufficient criteria.  A new name does not make an old route new.
3. Exclude refuted mechanisms and routes abandoned as intractable from the candidate list.  Acknowledge a recognizable near-duplicate briefly as already retired; do not offer it as one of the requested new ideas.
4. Reopen only with concrete new evidence or a testable mechanism addressing the recorded crux.  Name the old row, explain exactly what changes, and show why the old counterexample or missing estimate no longer applies.  Merely naming the open premise, restating the target, increasing numerical coverage, or completing an auxiliary lemma without a bridge to the goal is insufficient.
5. Reopening need not begin with a completed proof.  It must begin with a specific mathematical reason to expect progress and a discriminating test.  Keep the old entry and append the reopening rationale and outcome.

## Retirement checklist

A campaign is not documented as retired until all of these are present:

- **Identity and aliases:** the original idea and recognizable variants, not just its last subproblem.
- **Attempt and attraction:** what the proposed mechanism was supposed to accomplish and why it appeared promising.
- **Mathematics in Lean:** proved implications, exact counterexamples, equivalences, open premises, and admitted findings.  A mathematical conclusion appearing only in a string or doc-comment is not a formal statement.
- **Difficulty locus:** the precise missing estimate or construction; which attempts failed; why the available results do not supply it.  “No mechanism found” is acceptable when accurate, but name what the missing mechanism must do.
- **Operational disposition:** abandoned, parked, refuted, superseded, or reopened, with date and scope.  State whether the decision covers a specific mechanism or a family of closely related approaches.
- **Reopening requirements:** link the formal open crux and describe what new argument, input, or evidence would warrant another investigation.  “Prove the goal” alone is not an actionable reopening rationale.
- **Limits:** what has not been refuted, which hypotheses remain external, and which observations are only finite.  Preserve useful lemmas even when the approach is retired.
- **Discoverability:** an original-route Maze row, a checked `Link`, and pointers from the route note/handoff.  Follow-up subroute entries do not replace the original entry.
- **Verification:** compile the relevant modules, inspect the important types and axioms, run the Maze audit, and complete repository checks.  Validate a claimed refutation against an appropriate known-answer control or explicit counterexample.

For new `abandonedIntractable` entries, the Maze audit requires both supporting declarations and a linked reopening premise.  The prose checklist still requires review; the checker does not certify all of it.  The current 107 legacy prose-only rows are a disclosed backlog, not a model for new work.

## Row template

Use the existing `Hall` fields rather than creating a separate unlinked status list:

```text
name: original route name
tried: mechanism, intended payoff, searchable aliases
verdict: abandonedIntractable (or the precise mathematical verdict)
tier: evidence status of the supporting mathematics
mechanism:
  ABANDONED with current methods.  Named crux.  Attempts and findings.
  Why those findings fail to supply the crux.  Scope and non-claims.
  REOPEN ONLY: concrete changed mechanism/evidence, not a cosmetic variant.
evidence: Lean declarations and route-note paths
date: verified decision date
```

Then add the same row name to `mazeLinks`, with actual declaration references in `decls` and open `Prop` references in `reopen`.  Do not add it to `mazeLegacy`.

## The six pi ideas: current disposition

All three original routes are now **abandoned as intractable with current methods**, not proved impossible.  Their rows appear at the start of `Maze.register` and `MazeAudit.mazeLinks`.

The three later proposals in [round-two.md](docs/pi-routes/round-two.md) are also
now abandoned with current methods, as `Pi route 4` through `Pi route 6`.  Their
exact refutations have separate scoped rows.  The audit guards all six retirement
rows and requires linked evidence and open cruxes for each.  The second round
does not reopen the first.

The subsequent [invention screen](docs/pi-routes/invention-screen.md) admitted
zero new routes.  Its three scoped failed proof steps have separate Maze entries
and Lean controls in `PiDisjunctiveRoutes/InventionScreen.lean`; they are not a
third campaign or claims that all approximation, automaton, or averaging methods
are impossible.

A later [creative pass](docs/pi-routes/dual-radix.md) produced an exploratory
quadratic-twisted dual-radix conjecture.  Its Maze row is **parked**, not an admitted
campaign: the direct norm probe did not beat denominator cost, and a word-dependent
construction is still missing.

The [ln(2) screen](docs/ln-two-routes/screen.md) records Euler acceleration,
dyadic synthesis of Pade forms, and localized-normal limit transfer.  The first
and third are parked pending their named estimates.  The Pade route's
[bounded cost test](docs/ln-two-routes/cost-test.md) passed with an explicit
budget below 1/8; its parameter-uniform construction remains an open wall.
Preserve both the finite positive witness and the finite exclusion certificates.

| Original route | Formal crux and evidence | What must change to reopen |
|---|---|---|
| Triple return / odd orbit invariance | `PiOrbitClosureOddInvariant`; `pi_disjunctive_iff_oddInvariant`; the odd-return equivalence; the abstract doubling/tripling counterexample | A pi-specific arithmetic mechanism for odd invariance or returns.  A different odd multiplier or self-return prerequisite alone does not qualify. |
| Prime reservoir / residual coupling | `PiPrimeReservoirSupport`, `PiReservoirDiagonalSupport`; exit collapse; rho orbit shadow; sum cancellation; scoped rational comparison theorems | A coupling that actually forces visits of the sum, with an explanation of which comparison hypothesis it escapes.  A new cutoff or transverse nonvanishing alone does not qualify. |
| Disk residues / divisor floor sums | `DiskResidueCover`; shadow and cover sandwich; `diskSmallPart_orbit`; conditional tail-floor estimate | An additional arithmetic relation or estimate producing residue visits.  Improved shadow accuracy alone does not qualify. |
| Exact spigot / arithmetic word-avoidance ranks | `SpigotEscapeBudget`, `SpigotSound`; `positiveWidthAlternatingPrefix`; `no_index_only_emit_rank` | An invariant proved for pi-reachable states that excludes the alternating controls and forces word visits.  Width bookkeeping or a larger trajectory table alone does not qualify. |
| Oscillator polynomial certificates | `OscillatorCertificateSupply`; `not_quartic_endpoint_certificate`; sharp positive control `minimumDegreeWordOne` | A uniform construction exploiting word structure without first locating the word in pi.  The single-word degree-five calibration alone does not qualify. |
| Distinguished radical branch / relative norms | `AlgebraicAngleDisjunctivity`; `branchNorm_eq`; `not_uniform_branchLoss` | A word-dependent estimate retaining information absent from the full product, with a mechanism producing visits.  Further telescoping or a sharper polygon approximation alone does not qualify. |

### Finding inventory and evidence limits

- **Route 1:** [route1.md](docs/pi-routes/route1.md) and `TripleReturn*.lean`.  The correct set is the omega-limit set; irrationality already gives infinitude.  Odd invariance remains open.  The finite return probe is evidence about a finite range, not proof of the premise.
- **Route 2:** [route2.md](docs/pi-routes/route2.md), `PrimeReservoir*.lean`, and `ReservoirCutoff*.lean`.  The rho necessary-condition theorem is not a comparison of the difficulty of rho and pi.  The cutoff-six results and their conditional inputs are in [cutoff-six-density.md](docs/pi-routes/cutoff-six-density.md).  `EligibleChebotarevDensity` and `DFIBoundaryScarcity` are explicit hypothesis Props.
- **Rho identity search:** [rho-identity-probe.md](docs/pi-routes/rho-identity-probe.md) records a finite search with planted controls; it is not a theorem excluding identities.  `RhoDyadicIdentity` is the separate formal open regrouping statement in `ReservoirCutoffReview.lean`.
- **Approximate coupling:** [reservoir-comparison.md](docs/pi-routes/reservoir-comparison.md), [reservoir-denominator.md](docs/pi-routes/reservoir-denominator.md), and [bbp-adelic-grid.md](docs/pi-routes/bbp-adelic-grid.md) cite the corresponding Lean comparisons.  Preserve their exact scopes: approximate versus exact forcing, denominator divisibility versus equality, finite precision versus full p-adic agreement, and stated error budgets.
- **Backward BBP:** [bbp-backward.md](docs/pi-routes/bbp-backward.md) and `BBPBackward.lean`.  `backward_hasSum_zero` is admitted, `BackwardValuation` is open, and the finite algebra/controls are proved.  No digit-visitation bridge has been established.  These findings do not reopen the prime/whole-BBP family on their own.
- **Route 3:** [route3.md](docs/pi-routes/route3.md), [disk-floor-error.md](docs/pi-routes/disk-floor-error.md), and `DiskResidue*.lean` / `DiskFloorError.lean`.  The sandwich is a reformulation result.  The floor-error bound explicitly takes `DiskDivisorIdentity` and `LeibnizRemainderBound`; fixed-cutoff periodicity does not refute every growing-cutoff approach.
- **Goal audit:** [proof-frontier-audit.md](docs/pi-routes/proof-frontier-audit.md).  The BBP formula is proved, but every available disjunctivity transfer still needs an unproved premise.  No unconditional pi-disjunctivity result is claimed.

The inventory points to the actual Lean statements rather than duplicating them as prose proofs.  Numerical outputs retain their reproducible scripts and scope; they must not be promoted into unproved universal conclusions.
