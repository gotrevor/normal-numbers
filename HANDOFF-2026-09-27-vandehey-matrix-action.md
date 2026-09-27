# HANDOFF — Vandehey 2017 Theorem 1.1 side quest (2026-09-27)

**Branch** `wip/vandehey-matrix-action` · **HEAD** `a7467f0` · `lake build` 🟢 9281 jobs ·
working tree clean · nothing pushed.

**Scoped objective (`LEAN_DONE_WHEN`)**: `sorry`-free
`src/NormalNumbers/LiteratureVandehey.lean`, i.e. prove
`Literature.vandehey_matrix_action_holds` (no weakening/renaming of the `def` or theorem).

## The route, and why it is better than the published proof

Vandehey's Lemma 3.3 (published) / 3.2 (arXiv) is the Pyatetskii-Shapiro criterion in the
Moshchevitin–Shkredov form, which Airey–Mance (arXiv:1912.10265) show is **false on
non-compact spaces**; the CF space is non-compact.  This run does **not** repair it — it
routes around it twice:

1. **Identification is free.**  §6's either-or trick means the transducer programme only has
   to produce an `x`-*independent* limiting frequency; `γ(I_v)` is then forced by a
   measure-theoretic pigeonhole.  That pigeonhole is now proved in full, so the broken lemma
   is off the identification half entirely.
2. **Existence needs no hot-spot criterion either.**  Vandehey needs P-S only because his
   merging is *distributional* (Lemma 3.4, Saloff-Coste–Zúñiga).  With a **synchronizing
   word** the merging is *pathwise* and the whole soft-analysis layer (P-S, tightness as a
   hypothesis, Ryll-Nardzewski/Vitali-Hahn-Saks, ergodicity) evaporates.
3. And the tightness the corrected criterion would *assume* is here **derived** from
   CF-normality (`tendsto_digitTail_freq` + `digitTail_le`, with an explicit `O(1/K)`
   modulus).

## Files (all wired into `src/NormalNumbers.lean`)

| file | contents | sorries |
|---|---|---|
| `LiteratureVandehey.lean` | endgame + headline | 1 (`vandeheyUniformFreq_holds`) |
| `VandeheyAutomaton.lean` | §3 replacement: automaton/window combinatorics | 1 (`exists_jointFreq_limit`) |
| `VandeheyZFree.lean` | `γ(z-free) → 0`; `z`-free cylinders ⊆ avoidance sets | 0 |
| `VandeheyTransfer.lean` | index-shift helpers; digit-tail `O(1/K)` | 0 |

## Proved this run (all `#print axioms` = `[propext, Classical.choice, Quot.sound]`)

* `volume_image_mobius_null` — nonsingular Möbius maps are Lebesgue-nonsingular.
* `exists_null_cover_notCFNormal_fract` — `{y | ¬ IsCFNormal (Int.fract y)}` is null.
* `exists_cfNormal_with_cfNormal_image` — CF-normals meet their `M`-preimages in `(0,1)`.
* `vandehey_matrix_action_of_uniformFreq` — **Theorem 1.1 from the crux, unconditional.**
* `stateAt_eq_runState_window` + `stateAt_indep_of_init`, `stateAt_eq_of_window_eq` —
  pathwise merging: the state is computed by the lookback window, from any reference state.
* `card_joint_good_eq_sum` — joint (window,state) count = finite sum of window counts.
* `goodSet_card_le_jointCount`, `jointCount_le`, `badSet_card_le`,
  `card_unbounded_window_le` — the residue sandwich.
* `tendsto_windowFreq`, `card_window_mem_eq_sum`, `tendsto_window_mem_freq` — CF-normality
  on windows and on finite word families.
* `tendsto_digitTail_freq`, `digitTail_le`, `tendsto_digitTail_bound` — tightness, derived,
  with an explicit `O(1/K)` modulus.
* `zFreeSet`, `gaussMeasure_zFreeSet_succ_le`, `tendsto_gaussMeasure_zFreeSet` — geometric
  decay of the `z`-avoidance mass.
* `mem_zFreeSet_of_mem_cfCylinder`, `sum_gaussMeasure_zfree_le` — `z`-free window mass ≤
  avoidance mass.
* `tendsto_sub_div`, `tendsto_add_div`, `gaussMeasure_Ioo_inter`, `cfDigit_iterate`,
  `getD_drop` — glue.

## NEXT (in order)

1. **Close `exists_jointFreq_limit`** — pure bookkeeping, every input exists.  Work in
   `VandeheyTransfer.lean`; the recipe (with the exact `A_n`, `C_n`, `err(L,K)` and the
   observation that **no Cauchy argument on `mainSum` is needed**) is the last section of
   `PENDING_WORK.md`.  Sketch: define `stateWords`, `zfreeWords`, `mainSum`; get
   `A_n → mainSum` from `card_joint_good_eq_sum` + `tendsto_windowFreq` + `tendsto_sub_div`;
   get `C_n → mainSum + err` from `jointCount_le` + `badSet_card_le` +
   `card_unbounded_window_le` + `tendsto_digitTail_freq` + `tendsto_window_mem_freq`; then
   `liminf ≥ mainSum`, `limsup ≤ mainSum + err`, `err(L,K(L)) → 0`.
2. **`Synchronizing` for Vandehey's `M_D` transducer** — the one genuinely open mathematical
   debt left on this route (his §2 + §4).  The 2026-08-25 probe
   (`PROBE-2026-08-25-1235-route-a-transducer.md`) measured `2x` merging **pathwise at step
   3** over ℤ (and `φ` never merging over `ℤ[φ]`), which is direct evidence a synchronizing
   word exists in the integer case — exactly the case Theorem 1.1 needs.  Concrete target:
   a long run of one large digit should drive any det-`±D` normal form to a canonical state.
3. **§2 transducer construction + identity (9)**, then **§5–§6 trigger counting** to convert
   joint (window,state) frequencies into word frequencies in `Mx`.  Only after that does
   `vandeheyUniformFreq_holds` close.

## Notes for the next lap

* `VandeheyAut.boundedWords` shadows an existing `NormalNumbers.boundedWords`
  (`CFScheduleA.lean`, which also has `sum_gaussMeasure_boundedWords_le_one`).  They are
  namespaced apart; consider unifying if the CFScheduleA one has the same membership shape.
* `Maze.lean` still cites Vandehey 1.1 as `.cited` — repoint only once
  `vandehey_matrix_action_holds` is genuinely sorry-free.
* Mathlib gotchas hit this lap: `div_add_div_same` is gone (use `← add_div`);
  `Finset.filter_card_add_filter_neg_card_eq_card` is now
  `Finset.card_filter_add_card_filter_not` (predicate explicit, set implicit);
  `tendsto_finset_sum` → `tendsto_finsetSum`; `Set.image_subset` → `Set.image_mono`;
  `Set.mem_biUnion_iff` → `Set.mem_iUnion₂`.  `omega` needs beta-reduced goals — insert
  `show` before it inside `Finset.card_le_card_of_injOn` obligations.
