# Handoff: Vandehey 2017 Theorem 1.1 is PROVED

## Joint Lambert update, 29 September 2026

The synchronized-word theorem is unconditional at proof commit `f6fbf87` on
`proof/joint-lambert-unconditional`, in the sibling checkout `normal-numbers-lambert`.
There are no remaining prime-distribution hypotheses on that theorem.
The old AGP target below is a separate analytic question, not a prerequisite.
The next Lambert target is an all-N occurrence count; its proposed stronger paper bound is
`N exp(-C (log log N)^2 log log log N)`, documented on that branch in
`docs/JOINT-LAMBERT-QUANTITATIVE-NEXT.md`.  It is not yet formalized.


**Date**: 2026-09-29 (lap 9) · **Branch**: `wip/g5-prime-subset` · **HEAD**: `6d7a8ad` (+ this docs
commit) · `lake build` 🟢 10485 jobs · working tree clean · nothing pushed.

Scope: **MET.**  `DIRECTION.md` OPERATOR OBJECTIVE 2026-09-28 (c) — finish the Vandehey assembly —
is complete.

## 🎯 The headline

    Literature.vandehey_matrix_action_holds        -- NormalNumbers/VandeheyCapstone.lean
    #print axioms ⇒ [propext, Classical.choice, Quot.sound]        (no sorryAx)

    vandehey_matrix_action
      ← vandehey_matrix_action_of_uniformFreq      (either-or endgame, LiteratureVandehey)
      ← vandeheyUniformFreq_of_scaleUniformFreq    (Serret + Smith ⇒ x ↦ D·x, D prime)
      ← scaleUniformFreq_holds                     (VandeheyCFBridge)         ✅ NEW
      ← mobiusUniformFreq_of_runClock              (VandeheyRunClock)
            hr    ✅ zero_lt_runRate'
            hmono ✅ runClock_mono'   (NEW: unconditional — see below)
            hrate ✅ tendsto_runClock_div          (Lemma 6.1)
            hcount ✅ exists_tendsto_cfCount_runClock                          ✅ NEW

## ✅ This lap

`6d7a8ad` **`VandeheyCFBridge.lean` (`hcount`) + `VandeheyCapstone.lean` (the headline).**
`hcount` is one chain of bounded differences, every constant a function of `D` and `|v|` only:

1. `countOccurrences ↔ occStart` on both sides (slack `|v|`, resp. `|patWord|`).
2. `card_range_split` / `card_parity_split`: the image's CF start-position count over `range M`
   is, up to the single index `0`, the sum over the two parities of the parity-restricted count
   over `Ico 1 M` — and `card_cf_eq_card_patWord` turns each into a **pattern card** on letter
   positions `[lrPos img 1 − 1, lrPos img M − 1)`.
3. `patCard_window`: the two ends of that window cost at most ONE occurrence.  Below
   `lrPos img 1 − 1` there is **none**: `cf_of_patWord_occ` forces `P + 1 = lrPos (runIdx P + 1)`
   with `runIdx P + 1 ≥ 1`, so `P ≥ lrPos 1 − 1` is automatic.  Above `lrPos img M − 1` the same
   identity plus `runClock = runIdx (N − k₀)` pins the run index to `M`, leaving only
   `P = lrPos M − 1`.
4. `patCard_shift`: past the leading `R^{⌊D·fract x⌋}` run the stream of `D·fract x` **is** the
   stream of the image, so the two position sets are in bijection; the head costs `k₀ ≤ D`
   (`headRun_le`).
5. `occStart_patN_eq`: `encLetter` is injective, so the engine's ℕ-alphabet occurrence count and
   the `Bool`-level pattern card are literally the same natural number.

`runIdx_mono'` (new, and the one genuine simplification): `runIdx w P` is
`Nat.findGreatest (fun n => lrPos w n ≤ P) P` — a predicate that only *weakens* as `P` grows with
a bound that only *grows*, so `Nat.findGreatest_mono` gives monotonicity for **every** `w`, with
no irrationality.  That is what lets `runClock` satisfy the *unconditional* `hmono` of
`mobiusUniformFreq_of_runClock` (the old `runClock_mono` needed `Irrational x`).

**Structural move.**  `vandeheyUniformFreq_holds` / `vandehey_matrix_action_holds` now live in
`VandeheyCapstone.lean`, not `LiteratureVandehey.lean`: every module of the Raney chain imports
the latter for the frozen `VandeheyUniformFreq` / `vandehey_matrix_action` statements, so proving
the crux there is an import cycle.  Both frozen statements and the endgame reduction
`vandehey_matrix_action_of_uniformFreq` are byte-identical where they were.

## ⚠ Gotchas found this lap

- `set x := e with h` folds `e` only in hypotheses that **already exist**.  Obtain everything
  first, `set` last — otherwise `omega` sees two atoms for one term and fails with a counterexample
  whose `where` block shows both spellings (that is the tell).
- `div_add_div_same` is shadowed inside `NormalNumbers.VandeheyLR`; use `ring`.
- `Finset.card_filter_add_card_filter_not` takes ONE explicit argument (the set), not two.
- `occStart` filters over `Finset.range`; a `Finset.Ico 0 N` target needs
  `← Finset.range_eq_Ico` **before** `Finset.filter_congr`.
- Two concurrent `lake build`s reliably trigger the box's "too many open files" (see the
  reference corpus note `lean-box-fd-exhaustion-is-mmap-not-nofile.md`); it can also invalidate
  mathlib traces and provoke a wide rebuild.  Never run two builds at once; retry loops fix it.

## 📁 Files

New: `VandeheyCFBridge.lean`, `VandeheyCapstone.lean`.
Changed: `LiteratureVandehey.lean` (the two theorems moved out; statements untouched),
`src/NormalNumbers.lean`, `STATUS.md`, `DIRECTION.md`.

## 🎬 Next

Vandehey is finished.  The remaining open fronts are the casting-out conjectures C1/C3
(`SwingC1*.lean`, `SwingC3*.lean`, `C3MrtNoExc.lean`), `PairDecoupleProve`, and the joint-Lambert
`AGP` gap (`docs/JOINT-LAMBERT-AGP-GAP.md` names `AGPExpRange` as the concrete next target).
Take an objective from `PENDING_WORK.md`.
