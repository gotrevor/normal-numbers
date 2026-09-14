# HANDOFF — entropy lap 17 (2026-09-14, Opus)

**Branch** `wip/g4-entropy`, HEAD `b16dae6`.  `lake build` green, **8957 jobs**.  New module
`src/NormalNumbers/G4EntropyStable.lean`, sorry-free, `#print axioms` = the trust triple.  No
pre-expedition file edited; `DIRECTION.md`, `STATUS.md`, the brief untouched.

## 1. What was proved

Lap 16 sharpened the locality barrier to *density one*.  The obvious question it left open is
whether `1` is attained or is itself a proof artifact.  It is attained.

**`isNormalSequence_congr_of_density_zero`** (and its real form
`isNormal_congr_of_density_zero`): if two digit sequences agree off a set `D` of density `0`,
they are normal together.  Proof: one changed digit disturbs at most `ℓ` windows of length `ℓ`;
the disturbed window starts below `n` inject into `[0,ℓ) × (D ∩ [0,n))` via
`i ↦ (least j < ℓ with D(i+j), i+j)` (`card_badWin_le`), giving

  `#occ_x(w,n) ≤ #occ_y(w,n) + ℓ·|D ∩ [0,n)|`  (`countOcc_le_add`, and symmetrically),

so the two frequencies have the same limit.

**`isNormal_local_of_density_one`**: for every `S` with `Sᶜ` of density `0`, binary normality is
an `S`-local property in exactly the barrier's sense.

**`exists_digitLocal_forces_normal_iff`**: given that a binary normal number exists in `[0,1)`
(hypothesis, not proved here — the repo has no explicit normal number), the position sets `S`
carrying a *satisfiable* `S`-local hypothesis that implies binary normality are **exactly** the
density-one sets.

## 2. Which bottleneck moved

Brief §6's obstruction is no longer a bound with an unknown constant; it is a characterization.

| reads | can a digit-local hypothesis there force normality? |
|---|---|
| density `< 1` (any `c < 1`) | never (lap 16) |
| density `1` | yes, and the only such hypothesis is normality itself (lap 17) |

The implemented sample reads `≤ 1/4`; every admissible family over any set of scales reads
`≤ 1/8`; `not_readableScale` shows the sparsity is intrinsic to the freezing construction.  So
inside digit-locality the expedition's route is closed with no room left to quantify over: a
repair would have to read *all but a density-zero set* of the binary digits of `G₄`, at which
point the hypothesis is normality and nothing has been gained.  **This is the expedition's
structural endpoint**, and it is stronger than the session-wrap's statement.

## 3. Next bounded test

The only remaining room is **outside digit-locality**, which is now precisely delimited:

1. **A non-quantized functional.**  `ZSample_eq_blockVal` is what makes every sample statistic
   digit-local: the quantizer `⌊2^m u⌋` reads a finite window.  A test against `{4^k x}` that is
   *not* a function of finitely many digits — the bounded-Lipschitz bump layer in `G4Jackson` /
   `G4SeparatingTest` is exactly such a functional — escapes the barrier by construction.  The
   bounded next test: state `IsBlockLocal` (a property factoring through `blockVal` windows) and
   prove the Jackson bump functional is *not* block-local, i.e. exhibit two reals with the same
   sampled blocks at every scale and different bump values.  That names what the entropy route
   would have to use instead of `E0`.
2. **Existence of a normal number in `[0,1)`.**  `exists_digitLocal_forces_normal_iff` carries
   it as a hypothesis.  Champernowne in base 2 is the standard witness; the repo has the
   disjunctivity machinery (`isDisjunctive_two`) but no normality construction.  Proving
   `∃ z ∈ [0,1), IsNormal 2 z` would discharge the hypothesis and is a self-contained (if long)
   brick: block-frequency counting for the concatenation sequence.

Item 1 is on the campaign's crux; item 2 is a clean prerequisite that would make the lap-17
characterization unconditional.
