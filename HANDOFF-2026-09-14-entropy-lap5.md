# HANDOFF — entropy expedition, laps 1–5 (2026-09-14, Opus grind)

**Branch** `wip/g4-entropy`.  **HEAD** `73bfc89`.  Working tree clean.  `lake build` green,
8946 jobs.  All six new modules are **sorry-free** and introduce **no axioms**.

Spec: `BRIEF-entropy-expedition-2026-09-14.md`; staging
`KICKOFF-2026-09-14-entropy-expedition.md`; DIRECTION override at the top of `DIRECTION.md`.
Lap-by-lap detail is in `HANDOFF-2026-09-14-entropy-lap1.md` (laps 1–5 appended there).

## Where the mathematics stands

The expedition's structural programme (§2, §3A, §3B, §3C, §4 wiring) is **complete**.  E0 is
reduced to one numeric inequality about the implemented schedule.

| brief | statement | declaration |
|---|---|---|
| §2 | frozen sample, exact identity `n = t_α + d_α k` | `G4EntropySample.kIdx_spec` |
| §2 | **dictionary**: `Z` = the `m`-bit binary window at position `2k` | `ZSample_eq_blockVal` |
| §2 | joint law = pushforward of ONE uniform `n ∈ P_K`; `H₂ ≤ min(mH, log₂|P_K|)` | `jointLaw`, `H₂_jointLaw_le_mul`, `H₂_jointLaw_le_card` |
| §4 | **information-set lemma** | `G4EntropyInfo.FinLaw.prob_infoSet_ge` + `card_infoSet_le` |
| §3C | two-sided sample↔Haar transfer (old `separating_test_bound` recovered) | `G4EntropyCapture.abs_sampleAvg_sub_integral_le` |
| §3C | Jackson for an ARBITRARY bounded `dAv`-Lipschitz test, budgets independent of `E` | `G4EntropyJackson.jackson_of_clipTest`; old recovered as `propJackson_of_general` |
| §3C | **(C)** on the torus | `G4EntropyFrame.Frame.capture_le` |
| §3B | **(G)**, cover factor `|𝓑|` not `(#Bs)^H` | `G4EntropyCover.volume_tube_le_joint`; old recovered as `volume_tube_le_of_joint` |
| §3A | **exact** transported sample as an EQUATION | `G4EntropyTransport.Ffull_eq_of_progression`; `PropA` recovered as `propA_of_Ffull_eq` |
| §3A→§3B | quantized sample ⟹ membership in the transported joint box | `gridFrame_Ffull_mem_boxUnion` |
| §4 | **E0** | `G4EntropyE0.entropy_gt_of_budget` |

Three old endpoints were generalized strictly by ADDING lemmas and recovering the old statement
as an instance; `G4Jackson.lean`, `G4TubeVolume.lean`, `G4Transport.lean`, `G4Frame.lean`,
`G4SeparatingTest.lean` are all **untouched**.  `isDisjunctive_four` / `isDisjunctive_two` and
every other preserved declaration are unchanged.

## The single remaining obligation for E0

`entropy_gt_of_budget` needs

    2^{(1−δ/2)M} · (∑_{G good} η^{|G|} · vol(pieceCube G)) + δ₂ + 2κ + Λδ₃  <  δ/(2−δ)

with `M = m_K H_K`, `PropD δ₂`, `PropC δ₃`, `2^{-m} ≤ η`.

**The observation the assembly exposed, and the next lap's real problem:** the right-hand side
`δ/(2−δ) ≈ δ/2` *shrinks* with `δ`, whereas the disjunctivity argument only ever had to beat a
fixed `7/8`.  So the entropy budget must beat a moving target.  This is the actual content of
brief §4 and the reason `D_K = (16K²2^{m_K})²` and `κ_K ≤ 1/(16K)` are obligations, not givens.

## Next steps, hardest first

1. **Discharge the E0 budget** against `G4ScheduleParams`/`G4ScheduleBudget`/`G4ScheduleFar`/
   `G4ScheduleBig`.  `∑_G η^{|G|}vol(pieceCube G)` is exactly what `G4GridTube` +
   `G4Ellipsoid` + `G4Tensor` already bound for disjunctivity (`gridFrame_volume_pieceCube_le`,
   `log_det_one_add_tensorGram_le'`); only the prefactor changed, from `(#Bs)^{H_K}` to
   `2^{(1−δ/2)m_K H_K}`.  Compare exponents on the existing `K^{cK+d}` ladder.
   Decide `δ = δ_K` as a function of `K` (the brief's `ε_K = 1/K` suggests `δ_K ≍ 1/√K`, which
   is what E1's `C H_K √K` rate wants) and check the three error terms against it — including
   whether `a_K/ρ_K → 0` really follows from `G4Remainder`/`G4FarTail` rather than the old
   fixed 1/8 allowances.
2. If the budget closes, **E0 and then E1**; then brief §5 (S) via entropy subadditivity and
   the finite entropy-to-TV inequality; then §6 T_E.
3. Brief §6's counterexample worker can start now that §2 is frozen: the support/collision
   structure of `w_{K,ℓ}` is computable from `kIdx`/`sampleCentre` without touching anything
   above.

## Claim discipline

Nothing here asserts normality, E0, or E1 unconditionally.  `entropy_gt_of_budget` is an
explicit conditional whose hypothesis is visible in its statement.  The transfer `T_E` of brief
§6 has not been touched, and remains the frontier.
