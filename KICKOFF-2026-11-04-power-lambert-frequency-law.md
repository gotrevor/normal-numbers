# KICKOFF 2026-11-04 (second run on this branch): the frequency law is computable

**Supersedes `KICKOFF-2026-11-04-power-lambert-frequencies.md` (gate met: `5961a210`,
`24fc5170`) and its handoff** for branch `wip/power-lambert-frequencies`, worktree `~/src/nn-freq`.
Operator: Ren (Claude), attended session 2026-11-04.  Lane: new mathematics.

## The target

File: `src/NormalNumbers/PowerLambertFrequencyLaw.lean` (planted, builds green with two `sorry`s).
Host gate: `--done-when sorry-free:src/NormalNumbers/PowerLambertFrequencyLaw.lean`.  Both theorems
are FROZEN (`JUDGE-FLAG:` in the handoff if one is false).  Build only what you touch; add the root
import once sorry-free.  **ONE `lake build` at a time, foreground** (the shared box memory ceiling
OOM-kills containers running several); commit every green file at once.

## The proofs

1. `powerLambert_frequency_law`: `⟨isRich_powerLambert …, powerLambertFrequenciesExist …,
   not_isNormal_powerLambert …⟩` (`PowerLambertRich.lean`, `PowerLambertFrequenciesExist.lean`,
   `PowerLambertNonNormal.lean`).
2. `powerLambertFreq_eq_lim`.  `powerLambertFreq b r w = limUnder atTop a` with
   `a N = #{n<N : OccursAt …}/N`; by `powerLambertFrequenciesExist` and `tendsto_nhds_limUnder`
   (or `Tendsto.limUnder_eq`), `a → powerLambertFreq b r w`.  The proof of
   `exists_eventually_abs_wordFreq_sub_le` (`PowerLambertPeriodicApprox.lean`) produces, for each
   `ε`, a threshold `D₀` and shows `|a N − G_D| ≤ ε` eventually in `N`, where `G_D` is exactly
   `periodicModelFreq b r (D! ^ r) w` for the `D` it picks (its `g`).  Re-run that argument
   quantified over ALL `D ≥ D₀` (the only place `D` enters is the mean bound
   `sum_range_aperiodicTail_le`, `2/(D+1) ≤ 2/(D₀+1)`, and `hQD` for `Q = (D!)^r`, both monotone
   in `D`): state and prove a NEW lemma
   `eventually_abs_wordFreq_sub_periodicModelFreq_le : ∀ ε > 0, ∃ D₀, ∀ D ≥ D₀, ∀ᶠ N, |a N −
   periodicModelFreq b r (D! ^ r) w| ≤ ε` by copying the existing proof and replacing the chosen `D`
   by an arbitrary `D ≥ D₀` (do not edit the existing lemma).  Then for `D ≥ D₀`:
   `|G_D − f| ≤ ε` (pass to the limit in `N`, `le_of_tendsto`), which is `Metric.tendsto_atTop`.
3. Handoff sanity table (not Lean): for `b = 10, r = 2` compute the first `10^6` digits of
   `Σ_{n≥1} 1/(10^{n²} − 1)` exactly (big integers: `floor(10^N · S)` from the finite sum of
   `n ≤ √N` terms with the geometric tails) and report the empirical digit frequencies; compare
   the digit-`1` frequency with the density of squarefree numbers `6/π² ≈ 0.6079` (the digit at
   position `m` is `1 + #{d ≥ 2 : d² ∣ m}` plus a rare carry).  No claim beyond the data.

## Rules

No `native_decide`, no new axioms, no `maxHeartbeats` bumps without `-- HEARTBEAT:`.  Never edit
existing statements; new lemmas in this file or `PowerLambertPeriodicApprox.lean` (appended).  No
`git add -A`.  Handoff `HANDOFF-2026-11-04-power-lambert-frequency-law.md` with `#print axioms` of
both frozen theorems.  Lines ≤ 100 chars; docstrings on every new theorem.
