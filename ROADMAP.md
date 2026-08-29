# Roadmap

The programme, in dependency order.  Status keys: ✅ done · 🔨 in progress · ⬜ queued.

## Phase 1 — foundations (✅ complete, 2026-08-22, all axiom-clean)

- ✅ Definitions (`SeqDefs.lean`, `RealDefs.lean`): sequence normality (aligned
  with OldMathematician/ChampernowneNormality), digit map, real normality,
  equidistribution, the ×b orbit.
- ✅ **Bridge** (`Bridge.lean`): `digitOf_realOfDigits` + `isNormal_realOfDigits`.
- ✅ Counting/visit algebra (`Counting.lean`, `Visits.lean`): occurrences as
  index sets, boundary-window comparison, frequency transfer, cell sums.
- ✅ Digit↔interval toolkit (`DigitInterval.lean`): floor recursion,
  `blockNatVal`, `digits_prefix_iff`, shift lemma `digitOf_orbit`.
- ✅ **B-adic sandwich** (`Sandwich.lean`): `equidistributed_of_badic`.
- ✅ **Wall's theorem** (`Wall.lean`): `isNormal_iff_equidistributed_orbit`.
  Per the 2026-08-22 literature sweep, apparently the first formalization of
  Wall's theorem (and of interval equidistribution) in any proof assistant.

**Track A is COMPLETE** (2026-08-23): all three Phase-2 headlines below are
proved and axiom-clean.  Remaining Track-A work is outward (Phase 3), not proof.

## Phase 2 — the two headline artifacts

- ✅ **Bailey–Crandall reduction** (`LnTwo.lean`):
  `isNormal_log_two_of_equidistributed : Equidistributed lnTwoOrbit →
  IsNormal 2 (Real.log 2)` — sorry-free, axiom-clean.  The open conjecture
  "ln 2 is normal in base 2" is now one machine-checked hypothesis about the
  explicit orbit `x₀ = 0, xₙ = 2xₙ₋₁ + 1/n mod 1`.
- ✅ **Stoneham's theorem** (`Stoneham.lean`), unconditional — COMPLETE
  2026-08-23, axiom-clean: `isNormal_two_stoneham23 : IsNormal 2 stoneham23`
  (`#print axioms` = trust-base triple only).  Hot-spot route: `StonehamArith`
  (2 a primitive root mod 3^M), window state recurrence/approx, unit counting,
  one-sided `segment_visit_upper`, hot-spot lemma
  (`isNormal_of_visit_upper_bound`, `HotSpot.lean`), assembly.  No Erdős–Turán,
  no character sums — a partial cycle is a subset of a full cycle, and the
  hot-spot lemma needs only upper visit bounds.

## Moonshot map (from the 2026-08-22 literature sweep)

Bailey–Crandall 2002 Thm 4.8 / Cor 4.9 covers `Σ 1/(cⁿ·b^(dⁿ))` for coprime
`b,c` with `d > √c` (so `Σ 1/(3ⁿ·2^(4ⁿ))` is NOT new).  Genuinely open
neighbors: `Σ 1/(9ⁿ·2^(2ⁿ))` (`d < √c`, incomplete-exponential-sum wall),
`Σ 1/(3ⁿ·2^(n²))` (polynomial exponents; also not covered by their
nonnormality theorem), and their Artin-prime conjecture `Σ 1/(p·2^p)`.
Realistic new-math play: formalize the Stoneham mechanism *parametrically*
and squeeze the hypotheses (e.g. Thm 4.8's monotonicity condition (ii)).

## Track B — metric theory of continued fractions (→ KHINCHIN.md)

Same Birkhoff-on-[0,1] machine, second digit system: the Gauss map.  Added
2026-08-23; detail, landscape survey and references live in `KHINCHIN.md`.
Headline targets: Gauss–Kuzmin digit law + **Khinchin's theorem** — apparently
unformalized in any prover (surveyed 2026-08-23), and the founding hook's twin:
no naturally-occurring number is proven Khinchin-typical.

- ⬜ B0 defs: `gaussMap`, `cfDigit`, `gaussMeasure` (+ `GenContFract.of` bridge)
- ⬜ B1 invariance of the Gauss measure
- ⬜ B2 ergodicity of the Gauss map (Rényi bounded-distortion route first)
- ⬜ B3 pointwise Birkhoff: consume mathlib PR #42078 or vendor behind an interface
- ⬜ B4 harvests: Gauss–Kuzmin frequencies, Khinchin's theorem (K₀ as a tprod),
  Lévy's constant (stretch), arithmetic-mean divergence
- ⬜ B5 stretch exhibit: machine-checked Khinchin-typical witness (Wieting 2008)
- ✅ **B5′ expedition COMPLETE 2026-08-24** — plan W1–W6 in KHINCHIN.md, run in
  ONE day (launched 2026-08-23).  **Tier 1** `exists_absolutely_normal_cf_normal`
  (Becher–Yuhjtman, `b3bc2c4`; Pillai formalized from scratch) and **Tier 2**
  `exists_absolutely_normal_cf_normal_khinchin` (`4629029`) both PROVED.
  Judge-ratified at kernel tier 2026-08-24: 8 headline decls, trust triple only,
  sweep instrument red-tested; statement integrity clean since the freeze (three
  privacy lifts, nothing else); `/lean-review` over 151 commits, zero 🔴.
  Ledger: `JUDGE.md` close-out section.  Historical plan text follows.
- **Historical B5′ expedition plan (completed above; retained for provenance):** one witness, absolutely
  normal + CF-normal + Khinchin-typical, via Becher–Yuhjtman minus efficiency
  (pin notes in `papers/`).  ≈ 5.5–10k lines, ~8–16 laps, ≈ 2–4 weeks;
  Birkhoff-free.  Pre-flight ✅ (W3 route decided: self-contained
  `tailDensity` + ratio-contraction; KPW non-blocking).
  **W1 ✅ + W2 ✅ COMPLETE 2026-08-23** — all 12 `CFCylinder.lean` and all
  10 `CFDigitLaw.lean` statements proved (3 treadmill laps each, same
  day), statements character-frozen throughout, axiom-clean verified by
  judge `#print axioms` sweeps (the standard triple only).
  **W3's then-current scaffold state (2026-08-23)**: `CFMixing.lean` — Gauss-measure
  invariance (= flag B1), the conditional-density identity,
  `cylinder_mixing` (cylinder-conditioned quantitative Gauss–Kuzmin–Lévy,
  the expedition core, judge-governed rate escape valve), and
  `gauss_kuzmin` (= flag B4); 4 sorry'd frozen statements, builds green,
  anchors frozen — campaign-ready.  NB W3 completing will tick B1 and B4
  below as expedition lemmas.

## Track D — conditional disjunctivity (→ docs/conditional-disjunctivity.md)

Named axioms in the Hypothesis-A pattern, one rung below normality; the doc is
the source of truth for statements and claim status (novelty unswept).

- ✅ D0 orbit dictionary complete: `Disjunctive.lean` has `OccursAt`, the
  word/dense-orbit equivalences, positive base-power invariance, and the
  unconditional API theorem `IsNormal.isDisjunctive`; the
  endpoint-safe `UnitAddCircle` orbit and closed/forward-invariant/full
  ω-limit equivalence are in `ConditionalDisjunctive.lean`
- ✅ D1 the 0-1 law: a closed `×b`-forward-invariant circle set with positive
  Haar measure is everything, via mathlib's `AddCircle.ergodic_nsmul`
- ✅ D2 conditional headlines for ln 2 complete: Axiom Λ (positive limit mass),
  `Λ ⟹ IsDisjunctive 2 (Real.log 2)`, the named per-word `LnTwoHypothesisD`,
  `D_w ⟹` arbitrarily late occurrences of `w`, and the all-words disjunctivity
  assembly are in `ConditionalDisjunctive.lean`
- ✅ D3 (stretch) Axiom M implication: `QuadraticDisjunctive.lean` freezes the
  faithful named Prop `QuadraticHypothesisM`, proves the independent
  missing-word subshift dimension bound from an endpoint-safe finite cover,
  and proves the exact axiom-clean conclusion
  `quadratic_irrationals_disjunctive_of_hypothesisM`: for every `b ≥ 2`,
  `M_b` implies every quadratic irrational is `b`-disjunctive
- ✅ D4 **Baire slate (unconditional, SHIPPED 2026-08-25)**:
  `residual_absolutelyDisjunctive`, `isMeagre_setOf_isNormal`, and
  `exists_absolutelyDisjunctive_forall_not_isNormal`; pure Baire category
  in `DisjunctiveBaire.lean` + `NormalMeager.lean`
- ✅ D5 recurrence-rate rung (2026-08-29): `LnTwoFreq.lean` — the named
  hypothesis `LnTwoHypothesisFreq w` (positive lower visit frequency of the
  surrogate in a compact sub-cylinder), strictly below equidistribution
  (`hypothesisFreq_of_equidistributed`), yields `w` occurring with positive
  lower frequency in binary `ln 2`; all wiring sorry-free
- 🔨 D6 run tower (2026-08-29, → docs/lnTwo-kick-blueprint.md):
  `LnTwoRuns.lean` — run dictionary, τ-floor, and the sorry-free **sliver
  dichotomy** (super-log runs pin the surrogate to the top sliver); frozen
  Diophantine tiers `LnTwoExpSep` (citable, Marcovecchio) and `LnTwoPolySep`
  (Mahler-class open) with proved run-bound wiring
- ✅ D7 wall + gates (2026-08-29, → docs/diophantine-wall.md): the wall
  interface `lnTwoDyadicSep_iff_int` (`DiophantineWall.lean` - the tiers in
  pure number-theoretic form, consumable with zero repo context; the regime
  map places collatz-moonshot's `sep_two_three` at the same wall's other
  door); `KickDynamics.lean` - unconditional gate theorems `kick_floor` /
  `top_gate` (the sliver is reachable only through measure-`1/n` gates),
  the frozen node `SliverEscape` (no Diophantine input, probe-supported,
  ⚠️ costume check owed), and its proved edge `zeroRun_le_of_sliverEscape`

## Phase 3 — outward (publishing-prep pass ✅ complete locally, 2026-08-26)

- ✅ PR to OldMathematician/ChampernowneNormality: **done and staged** —
  branch `real-number` on `gotrevor/ChampernowneNormality`
  (`champernowne_real_normal`, axiom-clean on their v4.32.0-rc1 toolchain).
  This is staged external work, not merged or published; **Trevor opens the PR**.
  The Zulip note remains drafted in `drafts/`.
- ✅ formal-conjectures definition correction: PR-ready local work on sibling
  branch `fix/full-normality-definition`: correction commit `c6126c56` changes
  `IsNormalInBase` from simple normality to all nonempty overlapping blocks and
  retains the old notion as `IsSimplyNormalInBase`; branch HEAD `5d5832d0` adds
  the empty-block boundary test. **Neither is merged upstream**; no sibling
  repository was mutated by this publishing-prep lap.
- ✅ Production comparator harness for exact
  `isNormal_iff_equidistributed_orbit` and exact conditional
  `isNormal_log_two_of_equidistributed`: Mathlib-only faithful Challenge,
  import-only Solution, three non-vacuity anchors, exact trust-triple whitelist,
  `enable_nanoda: true`, pinned Lean v4.33.1 Linux CI, honest
  `formalization.yaml`, and a local identity probe with a passing missing-name
  teeth test. Full landrun + nanoda execution remains CI-only.
- ⬜ Publish the repository and post the Zulip announcement (**Trevor posts**;
  no PR, push, or announcement was performed by the autonomous lap).
- ⬜ Long game: normality definitions + Wall toward mathlib.

## References

📚 **Pinned sources + the literature-crawl recipe live in [`papers/README.md`](papers/README.md)**
— read that before re-searching anything; it carries the standing findings from the
2026-08-24 citation crawl (including a load-bearing erratum in Vandehey's §3).

- D. G. Champernowne, *The construction of decimals normal in the scale of ten*,
  J. London Math. Soc. 8 (1933) 254–260.
- D. D. Wall, *Normal numbers*, PhD thesis, UC Berkeley, 1949.
- D. H. Bailey, R. E. Crandall, *On the random character of fundamental constant
  expansions*, Exp. Math. 10 (2001) 175–190.  (Hypothesis A; the ln 2 orbit.)
- D. H. Bailey, R. E. Crandall, *Random generators and normal numbers*,
  Exp. Math. 11 (2002) 527–546.  (Stoneham normality, dynamical proof.)
- R. Stoneham, *On absolute (j, ε)-normality in the rational fractions with
  applications to normal numbers*, Acta Arith. 22 (1973) 277–286.
- D. H. Bailey, J. M. Borwein, *Nonnormality of Stoneham constants*,
  Ramanujan J. 29 (2012) 409–422.  (α₂,₃ not 6-normal.)
