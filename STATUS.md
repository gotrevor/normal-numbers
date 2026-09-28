# STATUS — normal-numbers 📊

State at the post-merge checkpoint of 2026-09-27 (`f5034b6` onward), on branch
`wip/g5-prime-subset`, Lean/mathlib v4.33.1.  One checkout, every campaign branch merged, and
`lake build` green.  The per-campaign detail and ledgers from before the merge are in
`archive/STATUS-to-2026-09-27.md`, and the lap-by-lap log is in
`archive/PENDING_WORK-to-2026-09-27.md`.

## Open fronts

### Joint Lambert: simultaneous disjunctivity (headline proved, conditional)
- **Proved** (`JointLambertDisjunctivity.lean`):
  - `JointLambert.jointLambertDisjunctivity (hagp : AGP) (hpis : PrimeIntervalSupply)`: for
    every finite set of bases, every tuple of target words occurs at one common digit offset,
    infinitely often.
  - `jointWords_two_four`: the dependent-base check.
- **Hypotheses left:** `AGP` and `PrimeIntervalSupply` (`JointLambertPrimeSelection.lean:64,74`).
- **Remains:**
  1. Discharge both hypotheses from PNT+ / PNT in APs, which makes the result unconditional.
  2. The quantitative all-`N` count of paper §6, as a separate target.
- **Read:** `archive/handoff/HANDOFF-joint-lambert.md`, `papers/2026-09-26-joint-lambert-disjunctivity.md`.

### Vandehey 2017 Thm 1.1: Möbius images of CF-normal numbers are CF-normal (partial)
- **Proved:**
  - `VandeheyTwo.tendsto_jointCount_classStep` (`VandeheyClassEquidist.lean`).  This is
    Vandehey's §3 made unconditional, without the refuted Moshchevitin-Shkredov criterion.
  - `vandehey_matrix_action_of_uniformFreq`.
- **Open:**
  - `vandeheyUniformFreq_holds` (`LiteratureVandehey.lean`, sorry) is the crux: block
    frequencies along a Möbius image have an `x`-independent limit.
- **Retired 2026-09-28:** `exists_jointFreq_limit` is gone.  Its `Synchronizing` hypothesis is
  unsatisfiable for the needed transducer, and that is now a theorem:
  `VandeheyAut.not_synchronizing_of_injective_quotient` (axiom-free) — a quotient on which
  every letter acts injectively is never forgotten, and the transducer's row-lattice class in
  `ℙ¹(ℤ/D)` is such a quotient.  Maze: `hall_vandehey_synchronizing_transducer`.  The live
  transfer principle is `VandeheyCocycle.tendsto_jointCount_of_classEquidistribution`; its
  hypothesis `ClassEquidistribution` is the real crux.
- **Read:** `archive/handoff/HANDOFF-2026-09-28-vandehey-bridge-CLOSED.md` (its NEXT list),
  `papers/vandehey-2017-open-problem-attack-map.md`.

### Moshchevitin-Shkredov refutation (PROVED 2026-09-28)
- `moshchevitinShkredov_cf_false` (`MoshchevitinShkredovRefuted.lean`, in the root import,
  axiom-clean): uniformly bounded upper block frequencies do NOT imply CF-normality.
- Witness `x = [0;1,2,3,…]`, built as the limit of the nested cylinders `[1,…,s+1]`
  (`exists_irrational_cfDigit_succ`, reusable).  Strictly increasing digits ⇒ every genuine
  block occurs at most once ⇒ every frequency is `O(1/p)`, so the hypothesis holds vacuously at
  `σ = 0`, while CF-normality would force `γ(I_1) = log₂(4/3) > 0`.
- Maze: `hall_moshchevitin_shkredov_cf_false`.  Any route through Vandehey 2017 Lemma 3.3 is dead.

### C3/MRT: `ConjC3` (richness of `∑ ω(n)/bⁿ`) as a conditional theorem
- **Live headline:** `conjC3_of_geom_input_band'` (`C3MrtBlockDefect.lean`), sorry-free and
  axiom-clean.  It is `conjC3_of_geom_input_band` with `UniformResonantMass` DISCHARGED
  (2026-09-28), so it takes three inputs, not four:
  1. `KPointNoExcAtWith …`: the Tao-Teräväinen K-point correlation input, faithful to arXiv
     2512.01739 Thm 3.1.  Out of reach today, and TT say so themselves.
  2. ~~`UniformResonantMass`~~: discharged by `uniformResonantMass_holds`
     (`C3MrtUniformMass.lean`).  No longer a hypothesis anywhere on the archimedean side.
  3. `CharPrimeSumLogQ D` with `2D < 125`: standard in strength, but needs Dirichlet
     L-function theory that mathlib lacks.  The `t = 0` slice is reduced to
     `CharTailCancellation` (`C3MrtCharSumZero.lean`).
  4. `WideBlockSavingBand`: a bespoke per-block saving, not a literature statement.
- **Retired 2026-09-28:** `highResonantMass_le_narrow` (`C3MrtURMLowHigh.lean`) was the one
  open obligation on a second, redundant route to `UniformResonantMass`.  With the theorem
  already in the kernel it had no consumer, so it and its two dependents are removed; the
  file's sorry-free lemmas stay.  Maze: `hall_urm_low_high_split`.
- **Vacuous, do not retry:** `conjC3_of_geom_input_blocks`, `_blockPartial`, `_pairing` (lap 115).
- **Read:** `archive/findings/ROUTE-ESCALATION-2026-09-25-c3mrt.md`,
  `archive/handoff/HANDOFF-2026-09-25-6-urm-lowhigh.md`.

### Elliott: two-point logarithmic Elliott for the Lambert twist (one hypothesis left)
- **Proved:** `ElliottLedger.twoPointElliottLog_of_zetaExponent` gives `TwoPointElliottLog` from
  a single input, `ZetaLogDerivExponent θ` with `θ < 1`: `‖ζ'/ζ‖ ≪ (log |t|)^θ` on `Re s ≥ 1`.
  `ledger_nonvacuous` guards it, and the chain has no sorries.
- **Gap:** Vinogradov-Korobov gives `θ = 2/3`.  The repo owns `θ ≥ 9`, and the gap is recorded
  as `zetaLogDerivExponent_gap`.
- **Relation to the rest:** it feeds the log-average, whereas the normality route consumes the
  natural-average `CastingOut.TwoPointElliott`, a Chowla-strength step away.  It shares with
  C3/MRT only the type of debt (archimedean non-pretentiousness), not a `Prop`.
- **Read:** `archive/handoff/HANDOFF-elliott-2026-09-25-lap121.md`,
  `archive/findings/ON-LINE-FINDINGS-2026-09-26-tao-2016-log-elliott.md`.

### Casting-out programme: the designated-open crux leaves
These are the ratified conjecture nodes.  They are open by design, and none is scaffolding.
- **C1:**
  - `SwingC1.hAutoCorrAll`, which supersedes `hDepthAll`.
  - `SwingC1Log.castLawLog_one`, the first rung.
  - `SwingC1Log.conjC1Log`.
  - `TwoPointBet.twoPointWeightedAvg_all`, a research bet.
- **C2:** `SwingC2.shiftedDivisorIncidence_holds` is the one open obligation on the headline
  path (Brun-Titchmarsh plus a Linnik lower bound).
- **C3:**
  - `SwingC3Leaf.weylLambertTwist_holds`, the crux that C3/MRT attacks.
  - `SwingC3Rotation.tailLargeDecouple_holds`.
- **Pair decoupling:** `PairDecoupleProve.multiElliott_all` and its refutation twin
  `PairDecoupleRefute.not_pairDecouple_all`.
- **Other open nodes:**
  - `PrimeLambertOscillation.phaseOscillation`, which gates `irrational_primeLambert`.
  - `MahlerDriftOne.exists_prime_nonresidue`, which is Linnik-strength and probe-true below 6000.
- **Likely stale (triage):** `SwingC2.tauMomentPrimesShiftStruct_of_primeDensity`, which takes the
  old vacuous `PrimeDensityAP`, and `SwingC2.survivorLeaf_of_struct`.
  `SwingC2.constructionInputs_even` is off the headline path.

## Closed campaigns (headline, Lean name)
- **Track A.**  Wall's criterion `isNormal_iff_equidistributed_orbit`, the ln 2 reduction, and
  Stoneham's constant `isNormal_two_stoneham23`.
- **Wall rational (2026-09-27).**  `WallRational.isNormal_rat_mul_add`: normality in base `b` is
  preserved by `x ↦ qx + r` for rational `q ≠ 0` and `r`.
- **Philipp ψ-mixing (2026-09-27).**  `philipp_psi_mixing_holds`: Gauss-measure cylinders ψ-mix
  at a geometric rate.
- **B5′ Khinchin.**  `xstar` is absolutely normal and CF-normal (Becher-Yuhjtman).  B6 affine
  images: `exists_cfNormal_and_affine_cfNormal`.  Leftover stretch: `ae_tail_average_tendsto`.
- **G4 disjunctivity.**  `G4.isDisjunctive_base` for every `b ≥ 3`, with corollaries
  `irrational_primeSum` and `every_word_occurs_base_late`.
- **Entropy expedition (2026-09-15).**  `IsNormal 2 fullRealW`.  The mechanism's normality wall is
  itself a theorem.
- **Campaign B (2026-09-20).**  Master additive weight, polylog-`c` weights.
- **Pair A multicutoff, Theorem C′ (2026-09-23).**
  `FamilyGraded.isNormal_subsetLambert_of_sqrtFreshMassZero`, unconditional.
- **C4 (2026-09-25).**  `Abelian.c4_realizable`, plus the odd and finite-complement variants.
- **Elliott, Tao 2016 Thm 1.3.**  Two-point log-Elliott, in both the CM and multiplicative forms.

## Map of the repo
- `src/NormalNumbers.lean`: the root import.  `lake build` covers every module except the
  Elliott chain.
- `src/NormalNumbers/Maze.lean`: every refuted route, as Lean data.
- `papers/`: per-paper notes (PDFs live in `~/personal/papers`, symlinked in, not committed), plus
  `literature-review.md`, which has one route-synthesis chapter per campaign.
- `archive/`: pre-merge handoffs, kickoffs, probes, findings and the old DIRECTION/STATUS/
  PENDING_WORK.  Lean docstrings still cite some of these by bare filename, so use
  `find archive -name <file>`.
- `OVERVIEW.md`/`.html`: the reader's project map, refreshed 2026-09-28.  Rebuild it with
  `make -f docs/overview.mk`.
