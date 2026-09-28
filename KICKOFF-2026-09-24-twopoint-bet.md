# KICKOFF 2026-09-24 — Research bet: the averaged weighted two-point leaf (C1)

Worktree `~/src/nn-twopoint`, branch `wip/twopoint-avg`.  Opus/low.  Target
`src/NormalNumbers/TwoPointBet.lean`: `twoPointWeightedAvg_all`.  This is a moonshot: an open
named `sorry` plus a sharper map of WHY is an acceptable end state; a refutation or an
equivalence with a named open problem is a success.

## Where the leaf sits

`conjC1_of_delange_kataiAvg_twoPointWeightedAvg` (`PairDecoupleTwoPoint.lean`) gives `ConjC1`
(casting-out law for `G4_b`) from Delange (known), the averaged Kátai/BSZ criterion
`KataiOrthogonalityAvg` (`PairDecoupleAvg.lean`, known) and `TwoPointWeightedAvg b (m/b)`:

    ∀ε>0, ∀ᶠ w, ∀ᶠ N,  π(w)^{-2} Σ_{p≠q ≤ w prime} |E_{n<N} ζ^{ω(pn+1)} conj ζ^{ω(qn+1)} · W(n)| < ε,

`ζ = e(t/b)`, `W = peelWeight` (unit modulus, depends on `ω` at `pn+1+k`, `qn+1+k`, `k ≥ 1`).
Nearest literature: Tao 2016 (two-point log-Elliott, unweighted, LOG density); MRT 2015 (averaged
Chowla, average over SHIFTS `h ≤ H(N)` with `H → ∞`).

## Ren's worry, to test first (≈65%)

The quantifier order puts `w` BEFORE `N`.  Then the average is over a FIXED finite set of pairs,
so the statement says "for most pairs `(p,q)`, the natural-density correlation has small limsup".
That smells no easier than natural-density two-point Elliott for a positive proportion of pairs,
which is open.  MRT-style averaging only wins when the averaging range grows WITH `N`.

1. **Decide the worry.**  Either prove an implication `TwoPointWeightedAvg → <named open
   statement>` (e.g. natural-density two-point Elliott for `ζ^ω` along some pair, perhaps with
   `W ≡ 1` after a separate `WeightDecouple`-type step), or find why averaging over multipliers is
   genuinely stronger than averaging over a fixed pair set.
2. **The growing-`w` re-plumb (the real bet).**  The Kátai/BSZ inequality is quantitative
   (Turán–Kubilius): `|E_{n≤N} f(n)a(n)|² ≲ 1/Σ_{p≤w}1/p + avg_{p≠q≤w} |E_{n≤N/max(p,q)} a(pn)conj a(qn)|`.
   State a quantitative `KataiQuantAvg` with `w = w(N) → ∞` slowly, prove it (it is a Cauchy–Schwarz
   + Turán–Kubilius argument; `PairDecoupleAvg.lean` and `PairDecoupleMertens.lean` have pieces),
   and re-wire C1 onto a leaf `TwoPointWeightedAvgGrowing` where the pair average runs over
   `p, q ≤ w(N)`.  Then attack THAT leaf: an average over dilations growing with `N` is where an
   MRT/entropy-decrement-style argument, or a large-sieve-in-the-multiplier argument, has room.
3. **Refute direction, in parallel.**  Probe (stdlib-only Python in `probes/`, with a
   hand-computed known-answer check) the averaged correlation for `b = 3, 5`, small `w`, `N` up to
   ~10⁷ if feasible.  Look for a structural obstruction (e.g. `p ≡ q mod b` pairs, or `W` correlating
   with the two-point factor through shared small prime factors of `pn+1`, `qn+1`).
4. If a leaf is honestly equivalent to an open problem, state the equivalence as a theorem, name
   the problem, add a `Maze.lean` row only via a NEW file if needed (do not edit `Maze.lean`), and
   say so in the handoff.

## Rules
- The target theorem is RATIFIED.  Never delete, rename or weaken `twoPointWeightedAvg_all`.
  Never edit existing files' statements (`PairDecouple*.lean`, `SwingC1*.lean`, `CastingOut*.lean`,
  `Maze.lean`), `papers/`, `agent-mail/`, other KICKOFFs.  New code goes in
  `src/NormalNumbers/TwoPoint*.lean` (add imports to `src/NormalNumbers.lean`).
- Read first: `PairDecoupleTwoPoint.lean`, `PairDecoupleAvg.lean`, `PairDecoupleProve.lean`
  (header: the chain), `PairDecoupleOneDigit.lean`, and the "Status after the 2026-09-24 swings"
  section of `CONJECTURES-2026-09-23-casting-out-and-rungs.md`.
- Build `lake build NormalNumbers.<your module>` (warm tree; never run `lake exe cache get`).
  Commit each green step.  Each HANDOFF (`HANDOFF-twopoint-2026-09-24-lapN.md`) names the crux,
  the advance this lap, and a confidence that the ratified leaf is TRUE and that it is PROVABLE
  with known techniques.
