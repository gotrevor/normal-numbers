# Handoff: the output side is CLOSED; the leaf is one concrete transducer, correctness proved

**Date**: 2026-09-28 (lap 2) · **Branch**: `wip/g5-prime-subset` · **HEAD**: `34857a8` ·
`lake build` 🟢 10319 jobs · working tree clean · nothing pushed.

Scope: `sorry-free: src/NormalNumbers/LiteratureVandehey.lean`, i.e. prove
`vandeheyUniformFreq_holds`.  Read `DIRECTION.md` CURRENT DIRECTIVE first — it outranks this
file.  Its mandated move (the §5–§6 output-frequency engine, abstract, in `src/`) is **done**.

## 🎯 Where the proof now stands — ONE chain, ONE open end

    vandehey_matrix_action_holds                      ← the headline (Vandehey 2017 Thm 1.1)
      ← vandeheyUniformFreq_of_scaleUniformFreq       ✅ VandeheyLeafReduction
      ← ScaleUniformFreq  (x ↦ p·x, prime p, ONE map)
      ← mobiusUniformFreq_of_transducer               ✅ VandeheyAssembly  ← THE CAPSTONE
          needs, for the concrete transducer:
            hout   ✅ (L/R level) lrWord_eq_lrExpandWord     — run↔CF-digit translation OPEN
            hjs    ⬜ JointStateFreq                          — VandeheyCocycle supplies it
            hlen   ⬜ ℓ(n)/n → c > 0                          — Vandehey Lemma 6.1
            hK/hkK ⬜ uniform trigger bound                    — Vandehey Lemma 2.2
            hgen   ⬜ triggers on genuine words
            htail  ⬜ Gauss-null trigger tails                 — Lemma 4.3 (2)

Everything analytic and combinatorial is in the kernel and axiom-clean.  What is left is six
named hypotheses about a single concrete finite-state machine.

## ✅ What landed this run (10 green commits, all `#print axioms`-clean)

`1ec1e49` **§6 assembly** — `exists_tendsto_trigTotal`: trigger counts have an `x`-independent
Cesàro limit.  `trigLimit` monotone and `≤ K`, `L = ⨆ J`, ε/3 sandwich.  Guard rule:
`exists_tendsto_trigTotal_locator` (empty family, limit 0).

`e6a808f` **`VandeheyLeafReduction`** — the either-or endgame ONE MATRIX AT A TIME.
`MobiusUniformFreq`, `mobiusCFN_of_uniformFreq`, `ScaleUniformFreq`.  Guard rule:
`mobiusUniformFreq_one`, `mobiusUniformFreq_const` (the singular `x ↦ 1` satisfies
`MobiusUniformFreq` but not `MobiusCFN`, so nonsingularity is load-bearing).

`cb0d45e` **`VandeheyRescale`** — `tendsto_div_of_tendsto_comp_of_monotone`: a monotone count
sampled at `ℓ(n)` with `ℓ n/n → c > 0` and `C(ℓ n)/n → L` has `C m/m → L/c` over ALL `m`.
Pure analysis; used TWICE (input→L/R, L/R→output CF digits).

`b770708` **`VandeheyOutputWord`** — `outWord`/`outLen`/`outDigit`, `outWord_eq_map_outDigit`,
`countOccurrences_le_of_prefix`, `tendsto_outCount_div`.

`980a2a0` **§5 bucketing** — `occStart_eq_sum_fireOut` (EXACT: occurrences bucket by the block
they start in), `abs_countOccurrences_sub_sum_fireOut_le` (the `O(1)`),
`tendsto_countOccurrences_outWord_of_fireOut`.

`85b809d` **`VandeheyTrigger`** — `blocksOf` + `blocksOf_append` (locality), `occIn`, and
`kOut := occIn q − occIn q.dropLast` (increment ⇒ minimality is FREE), `sum_kOut_eq`.

`9bfb54c` **`fireTotal_kOut_eq_fireOut`** — the §5 identity, ABSTRACT (any block emitter).

`d1a7770` **`VandeheyAssembly`** — `mobiusUniformFreq_of_transducer`, the capstone.

`bf72368` **`VandeheyLRTransducer`** — `RState D` (Fintype), `lrStep`/`lrOut`/`lrDelta` from
`isRD_ingest`, `lrRun_eq`: `M₀·B_{a₁}⋯B_{aₙ} = lrProd (lrWord n)·M_n`.

`761b568` **`act_startState_eq`** — `D·x = lrProd (lrWord n) · (M_n · Tⁿx)`.

`34857a8` **`lrWord_eq_lrExpandWord`** — the emitted word IS the L/R expansion's prefix.

## 🔑 The three design findings that made it work

1. **A CF-digit emitter cannot be finite-state.**  `isRD_ingest_cfString` emits
   `A_{d₀} B_{d₁}⋯B_{d_m}`, and `B_d·A_e = B_{d+e}`, so the last digit is provisional and the
   pending value is unbounded — it would have to live in the state, killing `Fintype S`.
   Emitting **L/R letters** fixes it: a letter, once emitted, is final.  The image's CF digits
   are the RUNS of the L/R word, so "the last run may still grow" is a ONE-LETTER look-ahead.
   Price: two reindexings, both `VandeheyRescale`.
2. **Minimality of triggers is free** if `k` is defined as an INCREMENT of a monotone count
   (`kOut`), not as a "minimal completing word".  Telescoping does the rest.
3. **`occStart` (already in the repo, from an unrelated audit) makes §5 EXACT.**  It counts start
   positions reading past the window end, which is precisely the convention in which an
   occurrence belongs to exactly one block.  Vandehey's four "not nicely" positions are
   subsumed; the only inequality left (`≤ |v|`) was already proved in `OccurrenceCountEquiv`.

## 🎬 Next actions, in order

1. **`hK`/`hkK` — the uniform trigger bound.**  Nearest of the six.  `raneyEntry_le` puts all
   Raney-state entries in `[0, D]`, so `entrySum ≤ 4D`, and `exists_balanced_decomp`'s descent
   measure bounds the emitted L/R word length per step.  Then a trigger multiplicity at one
   position is at most that block length, uniformly.
2. **The run↔CF-digit translation.**  An occurrence of a CF word `v` in the image's expansion is
   an occurrence of the L/R run-pattern of `v` with maximal runs at both ends (the one-letter
   look-ahead).  Then `outCount` at L/R index rescales to CF index by `VandeheyRescale` again,
   with `c₂` = the density of run boundaries.
3. **`hlen`** (Lemma 6.1) — `ℓ(n)/n → c > 0`.  Lower bound: every step emits `≥ 0` and the
   product must grow; upper: entries bounded by `D`.  Likely wants the ergodic average of the
   per-step emission length, i.e. `tendsto_wCount_div` at weight `|lrOut|` — the SAME engine.
4. **`hjs`** — `JointStateFreq` for `lrDelta`, from
   `VandeheyCocycle.tendsto_jointCount_of_classEquidistribution` + the common-target reach.
   `archive/handoff/HANDOFF-2026-09-28-raney-section2.md` has the row-family identity
   `δ(R_b, a) = R_{(a+b⁻¹) mod D}`, probed to `D = 23`.
5. **`htail`** — Gauss-null trigger tails.  For a FIXED `v` the trigger prefixes shrink because a
   long window forces many emitted letters; the tail mass is then a cylinder-mass estimate.

## ⚠️ Gotchas found this run

- `div_add_div_same` does not exist — use `← add_div`.
- `div_le_div_of_nonneg_right` takes `0 ≤ c`, NOT `0 < c` (pass `h.le`).
- `Finset.Icc_succ_right` does not exist — `ext p; simp [Finset.mem_Icc, Finset.mem_insert]; omega`.
- `List.tails_nil` does not exist; `(List.mem_tails _ _).mp`, not `List.mem_tails.mp`.
- `simp only [f_zero]` cannot see through eta on a partially applied function — `funext` first.
- `Nonneg.mul` resolves to Mathlib's `Nonneg` subtype instance; write `Mat2.Nonneg.mul`.
- `Mat2` is NOT a `Monoid`: use `mul_assoc'`, `one_mul'`, `mul_one'`.
- `finite_isRD D : Finite ↑{M | IsRD D M}` is a `Finite`, not a `Set.Finite`; make `RState` an
  `abbrev` so the subtype coercion and instances fire, then `Fintype.ofFinite`.
- `card_filter_range_shift`-style rewrites need the predicate passed EXPLICITLY (higher-order
  unification will not guess `fun p => Q (c + p)`).

## 📁 Key files

`VandeheyOutputFreq.lean` (engine) · `VandeheyOutputWord.lean` (§5 bucketing) ·
`VandeheyTrigger.lean` (trigger family) · `VandeheyRescale.lean` (reindexing) ·
`VandeheyAssembly.lean` (capstone) · `VandeheyLRTransducer.lean` (the machine) ·
`VandeheyLeafReduction.lean` (per-matrix endgame) · `VandeheyRaney.lean` (Raney states, Lemma 2.1).

---
**→ Next session: NEXT action 1 (`hK`, the uniform trigger bound).  It is the nearest of the six
remaining hypotheses and it is pure finite combinatorics on the Raney cone.**
