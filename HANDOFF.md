# Handoff: the capstone has ONE obligation left — `hcount`

**Date**: 2026-09-29 (lap 8) · **Branch**: `wip/g5-prime-subset` · **HEAD**: `4b59e62` ·
`lake build` 🟢 10483 jobs · working tree clean · nothing pushed.

Scope: `sorry-free: src/NormalNumbers/LiteratureVandehey.lean` (`vandeheyUniformFreq_holds`),
under **DIRECTION.md OPERATOR OBJECTIVE 2026-09-28 (c)** — finish the Vandehey assembly.
DIRECTION.md outranks this file.

## 🎯 Where the proof stands

    vandehey_matrix_action_holds                       ← Vandehey 2017 Thm 1.1
      ← vandeheyUniformFreq_of_scaleUniformFreq        ✅ (reduces to `x ↦ D·x`, D prime)
      ← mobiusUniformFreq_of_runClock                  ✅ NEW (VandeheyRunClock)
            hr    ✅ `zero_lt_runRate'`                  (VandeheyRunDict)
            hmono ✅ `runClock_mono`                     (VandeheyRunDict)
            hrate ✅ `tendsto_runClock_div`              (VandeheyRunDict)
            hcount ⬜ **THE ONLY OPEN OBLIGATION**

## ✅ This lap (5 green commits, every headline `#print axioms`-clean)

`329ea74` **The run-clock restatement + `hgen` dissolved.**
`mobiusUniformFreq_of_runClock`: `MobiusUniformFreq` talks about `cfDigit` of the image
*directly*, so the assembly never needed the automaton to PRODUCE the output stream — only a
monotone clock with rate `r > 0` and a Cesàro limit for the count sampled along it.  `hcof` and
`hout` therefore do not exist in the new capstone.  Separately: `hgen` ("triggers are supported
on genuine words") is NOT a property of a trigger family — a window with a `0` digit can carry a
trigger (`B_0` is the swap, and it emits).  It is a property of the ORBIT, and there it is free:
`exists_tendsto_trigTotal` now takes `∀ m, 1 ≤ cfDigit x m`, supplied by `one_le_cfDigit_fract`.

`6de4882` **`VandeheyLetterGrowth.lean` — the LOWER Lemma 2.2.**  `genuine_length_le`:
`|q| ≤ 2·|lrBlocks t q| + 2D + 6` for every Raney state.  Entry-sum comparison across the
word-level transducer identity `lrBlocks_run` (needed because `trigPrefix` quantifies over WORDS,
not orbits): `L`/`R` at most double the entry sum and Raney entries are `≤ D`; on COLUMN sums
`B_j` acts by `(c₁,c₂) ↦ (c₂, c₁ + j c₂)`, the Fibonacci recursion — `fib_col_le`, a single-step
induction once stated with both columns.  `col₂ t ≥ 1` because `col₂ t = 0` forces `det t = 0`.

`e366e8e` **`VandeheyLRTail.lean` — `htail`, and it is not analytic.**  `tailMass` is EXACTLY `0`
past `2|v| + 2D + 6`: `trigPrefix` is empty there (`length_le_of_kOut_ne_zero`).

`864f0d8` **`VandeheyScaleCount.lean` — the engine, wired to the machine.**
`exists_tendsto_countOccurrences_patN`: the count of `patWord b v` in the emitted letter word has
an `x`-independent Cesàro limit.  Plus `lr_hcof` (third corollary of the lower Lemma 2.2),
`startPlus`, and `cesaro_of_bounded_diff`.

`4b59e62` **`VandeheyRunDict.lean` — the clock.**  `runClock`, `runClock_mono`,
`tendsto_runClock_div`, `zero_lt_runRate'`.  Key new lemma `numAlt_lrExpandWord`: `numAlt` of the
length-`L+1` prefix of an `L/R` expansion IS `runIdx w L`.  Plus `map_range_split` /
`lrExpand_shift` for the leading `R^{⌊z⌋}` run (`⌊z⌋ ≤ D − 1`, uniformly bounded).

## 🎬 Next actions — `hcount`, and nothing else

Goal: for genuine `v = a :: v'` and prime `D`, an `x`-independent `L` with
`cfCount v (imgOf D x) (runClock hD x n) / n → L`.  **The plan is fully worked out; it is
`O(1)` bookkeeping, no new mathematics.**  Let `img = imgOf D x`, `k₀ = headRun D x`,
`P n = letterLen hD x n`, `M = runClock hD x n`.

1. **A-side.**  `|cfCount v img M − occStart v (cfDigit img) M| ≤ |v|`
   (`countOccurrences_le_occStart` / `occStart_le_countOccurrences_add`, already in the kernel).
   Split `occStart` over `Ico 1 M` by parity (cost: index `0`, ≤ 1) and apply
   `VandeheyLRPattern.card_cf_eq_card_patWord` to get, for each `b`, a count of `patWord b v`
   occurrences in letter positions `Ico (lrPos img 1 − 1) (lrPos img M − 1)`.
2. **No occurrence below `lrPos img 1 − 1`**: `cf_of_patWord_occ` gives `P = lrPos (runIdx P + 1) − 1`
   for ANY occurrence, so `P < lrPos 1 − 1` forces `runIdx P = 0` hence `P = lrPos 1 − 1`.
   So both windows may be taken to start at `0`.
3. **B-side.**  `countOccurrences (patN b v) (outWord …)` vs the position count over
   `range (P n)`: `≤ |patN|` slack; then shift by `k₀ ≤ D − 1` (`map_range_split`) to positions
   of `lrExpand img` over `range (P n − k₀)`.  Letters vs encoded letters: `encLetter` injective.
4. **Window difference ≤ 1.**  `lrPos img M ≤ P n − k₀ < lrPos img (M+1)` (this is exactly what
   `runClock = runIdx img (P n − k₀)` says), and an occurrence in `[lrPos M − 1, P n − k₀)` has
   `lrPos i − 1` there, so `i = M` by `lrPos_strictMono`: at most ONE extra, per parity.
5. Feed the total (a bounded difference) to `cesaro_of_bounded_diff` with
   `L = L_true + L_false` from `exists_tendsto_countOccurrences_patN`, then
   `mobiusUniformFreq_of_runClock` and `vandeheyUniformFreq_of_scaleUniformFreq` finish
   `vandeheyUniformFreq_holds`.

## ⚠ Gotchas found this lap

- `Nonneg.mul` resolves to a mathlib `Mul` instance; write `Mat2.Nonneg.mul`.
- `Nat.fib_add_two : fib (n+2) = fib n + fib (n+1)` — that order.
- Section `variable`s used only in a PROOF need `include h₁ h₂ in` before the declaration; inside
  an equation-compiler recursion, call the lemma WITHOUT them (they are re-applied automatically).
- `rw [hpval]` where `hpval : v = …` rewrites `v` inside `v.length` too; rewrite the other side.
- `set k₀ := headRun D x` leaves `omega` unable to see `k₀ = ⌊·⌋.toNat`; introduce the equation as
  a `have … := rfl` and `rw` it into the hypothesis instead of the goal.
- `Int.fract_sub_intCast`, `List.take_drop : take i (drop j l) = drop j (take (j+i) l)`.

## 📁 Files

New: `VandeheyRunClock.lean`, `VandeheyLetterGrowth.lean`, `VandeheyLRTail.lean`,
`VandeheyScaleCount.lean`, `VandeheyRunDict.lean`.
Changed: `VandeheyOutputFreq.lean` (hgen → orbit genuineness), `VandeheyAssembly.lean`,
`src/NormalNumbers.lean`.

---
**→ Next session: `hcount`, steps 1–5 above.  Tree clean at `4b59e62`.**
