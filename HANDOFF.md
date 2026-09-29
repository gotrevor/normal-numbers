# Handoff: every analytic input of the capstone is PROVED — only assembly is left

## Current Lambert status, 29 September 2026

The bounded qualitative Lambert objective is complete: `f6fbf87` proves the original
common-position theorem unconditionally.  [Completed proof](docs/JOINT-LAMBERT-RESCALED-PROOF.md).
The [next quantitative target](docs/JOINT-LAMBERT-QUANTITATIVE-NEXT.md) has a paper derivation
of `N exp(-C (log log N)^2 log log log N)` occurrences for every sufficiently large N.
No new treadmill is launched by this documentation update.  The older AGP-only status
below is historical; proving AGP is not the next Lambert obligation.  Vandehey work is
separate, in the main checkout.


**Date**: 2026-09-28 (lap 6) · **Branch**: `wip/g5-prime-subset` · **HEAD**: `3173fb4` ·
`lake build` 🟢 10332 jobs · working tree clean · nothing pushed.

Scope: `sorry-free: src/NormalNumbers/LiteratureVandehey.lean`
(`vandeheyUniformFreq_holds`).  **`DIRECTION.md`'s CURRENT DIRECTIVE outranks this file**; its
lap-4/5 steps are now all either DONE or superseded.  The current queue head is the top section
of `PENDING_WORK.md`.

## 🎯 Where the proof stands

    vandehey_matrix_action_holds                      ← Vandehey 2017 Thm 1.1
      ← vandeheyUniformFreq_of_scaleUniformFreq       ✅ VandeheyLeafReduction
      ← mobiusUniformFreq_of_transducer               ⚠ needs a RESTATEMENT (see NEXT 1)
            hjs  ✅ `jointStateFreq_lrDelta` / `jointStateFreq_lrB`   (lap 6 — was THE crux)
            hρ   ✅ `subWindow_rhoLR` / `subWindow_rhoLRB`            (free)
            hlen ✅ `tendsto_numAlt_lrWord_div`  (run clock, lap 6)
            hc   ✅ `zero_lt_runRate`            (lap 6)
            hkK, hK ✅ `lr_trigger_bounds`;  hout ✅
            hgen ⬜ (near-free, `patWord_alternation`), htail ⬜ (cylinder estimate), hcof ⬜

## ✅ This lap (9 green commits, every headline `#print axioms`-clean)

`54610ea` **`VandeheyTransport.lean` — `hjs` CLOSED.**  Lap 5 proved `ClassEquidistribution` for
the product automaton `prodStep rplusDelta`; this transports it to the genuine `lrDelta`.
Bridge: `runState lrDelta M.toRState w = ι^{|w|} (runState rplusDelta M w).toRState`, and the
DETERMINANT PINS THE PHASE (`runState_lrDelta_eq_iff`), so
`jointSet lrDelta s₀ t q x n = jointSet (prodStep rplusDelta) (s₀,0) (tPlus t, tPhase t) q x n`
as FINSETS — an ext, not an estimate.

`c8922b4` + `3373096` **`VandeheyOutLen.lean`.**  `outLen = Σ_t wCount δ s₀ t (blockLen out t) 1`,
so Lemma 6.1 is the length-1 `wCount` engine (`tendsto_outLen_div`).  Plus
`sum_jointCount_eq_winCard` → `sum_rho_eq_gauss` (`Σ_t ρ q t = γ(I_q)`, the de-factorized
analogue of `Σ_t ν t = 1`), `le_wLimit_single`, `outLenLimit_pos`.

`0322e3c` **ARCHITECTURAL FINDING + `VandeheyRunBirkhoff.lean`.**  The concrete `out` (`lrOutN`)
emits LETTERS, whose count per input digit diverges (infinite Gauss digit mean), so no `hB`/`hlen`
can exist for it: the capstone must run on the RUN clock.  `numAlt_append_eq` (the seam identity)
shows the right state augmentation is the last emitted letter, and
`numAlt_lrWord_eq_sum : numAlt (b₀ :: lrWord … n) = Σ_{i<n} altOut (stateAt lrB … i) (cfDigit x i)`
with `altOut ≤ 2D+1`.

`3487af4` + `a3f1f87` **`VandeheyTransportB.lean`.**  The involution acts on the augmented state
by `ι'(M,b) = (ι M, !b)`, so the phase argument is verbatim; `rplusB_common_reach` is a length-3
uniform common reach (2 digits to `diag(1,D)`, a third whose block `Lᴰʲ` overwrites the letter).
Hence `jointStateFreq_lrB` and **`tendsto_numAlt_lrWord_div` = Lemma 6.1 for the true clock**.

`7dce80b` + `1b5a0d5` + `3173fb4` **`VandeheyFirstLetter.lean` — `hc` CLOSED.**  Probing D=2..11
found two exceptionless facts, both now theorems: `det_pos_iff_branch` and
**`head_lrOut_eq_true_iff` (the first letter of a nonempty block is `L` iff `det M > 0`)**.
`det` flips every digit ⇒ consecutive blocks start with OPPOSITE letters ⇒
`one_le_altOut_add : altOut i + altOut (i+1) ≥ 1` (internally, or at the SEAM).  Blocks are
nonempty for digits `≥ D` (`lrOut_ne_nil_of_le`), so
`winCard [D,D] x n ≤ 2 · numAlt(… (n+1))` and `γ(I_[D,D]) ≤ 2c`, giving `zero_lt_runRate`.

## 🎬 Next actions, in order

1. **Restate the capstone against a SEPARATE clock.**  `mobiusUniformFreq_of_transducer` takes
   `ℓ(n) = |outWord|`, the letter count.  The run clock is not of that form — a run's VALUE is
   not a function of a finite state (the partial run length is unbounded), which is exactly why
   the letter transducer is the finite-state one.  So the capstone wants:
   * `out := lrOutN` (letters) for the occurrence side, with CF occurrences read through
     `VandeheyLRPattern.card_cf_eq_card_patWord` (CF occurrences of `v` ↔ `patWord` occurrences
     in the letter stream) — `hkK`/`hK` are already proved for exactly that `v = patWord b v'`;
   * `ℓ := numAlt (b₀ :: lrWord …)` (runs), fed to
     `Rescale.tendsto_div_of_tendsto_comp_of_monotone` (which does need `0 < c` — checked, it
     inverts `c`; `zero_lt_runRate` supplies it).
   Guard rule applies to the new `Prop`.
2. `hgen` (near-free from `patWord_alternation`), `htail` (a cylinder estimate), `hcof` (the run
   count diverges — follows from `winCard_le_two_mul_numAlt` since `winCard [D,D] x n → ∞`).
3. Only then the `PrimeIntervalSupply` side item of the operator objective.

## ⚠ Gotchas found this lap

- `open Classical in` must precede the DOCSTRING, not sit between it and the `def`.
- `split` cannot split a dependent `dite` whose branches use the hypothesis: restructure the def
  so the `if` is on the VALUE (`⟨if c then u else v, by split …⟩`), then `show` + `if_pos`.
- `!x = y` parses as `!(decide (x = y))`: write `(!x) = y`.
- `Prod.ext_iff` rewrites ANY product equation (including the one you wanted to keep); use
  `Prod.mk.injEq` to hit only literal pairs, then `← Prod.ext_iff` to repack.
- `Subtype.ext` goals across two different subtypes of `Mat2` need an explicit `show` of the
  `.val` equation; `rw` alone leaves a defeq-but-not-syntactic goal (finish with `rfl`).
- `wLimit_nonneg` takes `(ha0, haC)` in that order, `wLimit_set_bddAbove` the other way round.
- A full `lake build` now takes ~4½ minutes; run it in the background before committing.

## 📁 Files

New: `VandeheyTransport.lean`, `VandeheyOutLen.lean`, `VandeheyRunBirkhoff.lean`,
`VandeheyTransportB.lean`, `VandeheyFirstLetter.lean`.
Changed: `src/NormalNumbers.lean`, `PENDING_WORK.md`.

---
**→ SUPERSEDED for the Lambert front: see HANDOFF-2026-09-29-joint-lambert-unconditional.md.**
