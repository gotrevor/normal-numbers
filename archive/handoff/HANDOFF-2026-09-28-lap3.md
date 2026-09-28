# Handoff: the trigger bound and the run↔CF-digit translation are CLOSED; one analytic leaf left

**Date**: 2026-09-28 (lap 3) · **Branch**: `wip/g5-prime-subset` · **HEAD**: `ee5365d` ·
`lake build` 🟢 10325 jobs · working tree clean · nothing pushed.

Scope: `sorry-free: src/NormalNumbers/LiteratureVandehey.lean`, i.e. prove
`vandeheyUniformFreq_holds`.  Read `DIRECTION.md` CURRENT DIRECTIVE first — it outranks this
file.  Its mandated move (the §5–§6 output engine) was done in lap 2; this lap discharged the
two hypotheses that lap 2 named as NEXT 1 and NEXT 2.

## 🎯 Where the proof stands

    vandehey_matrix_action_holds                      ← Vandehey 2017 Thm 1.1
      ← vandeheyUniformFreq_of_scaleUniformFreq       ✅ VandeheyLeafReduction
      ← ScaleUniformFreq  (x ↦ p·x, prime p)
      ← mobiusUniformFreq_of_transducer               ✅ VandeheyAssembly (the capstone)
          for the concrete L/R transducer:
            hkK, hK ✅ **PROVED this lap** — `VandeheyLRTrigger.lr_trigger_bounds`
            hout    ✅ at L/R level (lap 2) + ✅ the run↔CF-digit translation (this lap)
            hjs     ⬜ JointStateFreq — VandeheyCocycle + the common-target reach
            hlen    ⬜ **the one analytic leaf**: run count grows at least linearly
            hgen    ⬜ triggers on genuine words (now near-free: `patWord_alternation`)
            htail   ⬜ Gauss-null trigger tails

## ✅ This lap (7 green commits, all `#print axioms`-clean)

`3d36857` **Lemma 2.2, run form** (`VandeheyRunBound.lean`).  `numAlt`; `colApp` (a Mat2 on a
column: `L : (p,q) ↦ (p,p+q)`, `R : (p,q) ↦ (p+q,q)`); `numAlt_le_colApp` — each letter ADDS one
coordinate to the other, so the coordinate SUM bounds the alternation count, and a vanishing
coordinate persists under only one letter (so the rest of the word is one run, no alternation).
Fed by `lrStep_col`'s `j`-free identity: `numAlt (lrOut M j) ≤ M.b + M.d ≤ 2D`, **no dependence
on the ingested digit and no case split on vanishing denominators** — Vandehey's Cases 1–3 vanish.

`170aa47` **Occurrences counted by alternations** (`VandeheyAltCount.lean`).  `altCount` on a
stream; `card_occ_le_altCount` (an alternation at `i₀` in `v` forces one at `P+i₀`, and `P ↦ P+i₀`
is injective); `card_occ_le_altCount_add` (`+|v|` is the price of running past the block end);
`trigger_bounds_of_occIn_le` — **`hK` and `hkK` are ONE statement** (`kOut` is an increment of
`occIn`, and the `hK` sum telescopes along CF prefixes).

`4737aea` `occIn_le_numAlt_add` — abstract: occurrences starting in the first emitted block are
`≤ numAlt(block) + 2 + |v|`, with NO reference to the block's LENGTH (which is unbounded).

`4bd6a43` **`lr_trigger_bounds`** (`VandeheyLRTrigger.lean`) — `hK`/`hkK` for the real machine,
`K = 2D + 2 + |v|`, for every `v` that alternates somewhere.

`f0042d1` **The run dictionary** (`VandeheyLRRuns.lean`).  `lrTail` subtracts one above `1` and
subtracts one in the RECIPROCAL below `1`, so the L/R expansion is the slow Stern–Brocot CF.
`lrTail_lrPos`: after `n` runs the point is `Tⁿw` (`n` even) or `(Tⁿw)⁻¹` (`n` odd) — **the runs
ARE the CF digits**.  `lrExpand_run`, and then `6e30401`: `runIdx`,
`lrExpand_eq_runIdx_parity` (letter = parity of its run), `runIdx_eq`, `lrExpand_ne_succ_iff`
(**alternation ⟺ run end**).

`3df352f` + `7463b86` + `61fef68` **The translation, both directions and as a count**
(`VandeheyLRPattern.lean`).  `patBody b (a::v) = replicate a b ++ patBody (!b) v` is the identity
that makes everything a one-run induction; `patWord b v = (!b) :: patBody b v` is the single
forced pattern.  `patWord_alternation` (alternates at index 0 — the hypothesis
`lr_trigger_bounds` needs), `map_range'_eq_patWord` (forward), `cfDigit_of_map_range'_eq_patBody`
(converse: a run can't end early — parity flips — nor late — the border differs), and
**`card_cf_eq_card_patWord`**: a BIJECTION `n ↦ lrPos w n - 1` between CF occurrences in `[1,N)`
of parity `b` and pattern occurrences.

`ee5365d` **⚠ The structural finding, and the upper half of Lemma 6.1** (`VandeheyRunCount.lean`).
The Gauss measure has INFINITE digit mean, so the emitted LETTER count per input digit diverges
a.e. and the density of run boundaries is `0`.  **Never rescale the letter index against the
input index.**  What is linear is the RUN count — which is why Lemma 6.1 is about emitted CF
digits, and why the bijection (landing on CF INDICES) is the right interface.  Proved:
`numAlt_append_le`, `numAlt_lrWord_le` — at most `(2D+1)·n` alternations after `n` input digits.

## 🎬 Next actions, in order

1. **`hlen` — the lower bound, the one analytic leaf.**  `liminf (runs of lrWord n)/n > 0`.
   Route (`PENDING_WORK.md` item (a′)): `lrRun_eq` gives `M₀·B_{a₁}⋯B_{aₙ} = lrProd w · M_n` with
   `M_n` in a FINITE set, and the input product's own Stern–Brocot word has exactly `n` runs (one
   per input digit).  Right-multiplying by a bounded matrix perturbs the path's cone boundedly,
   so the run counts differ by a bounded FACTOR.  Making that precise is the work.  Note only
   `liminf > 0` is needed, not convergence, if the assembly is restated accordingly.
2. **Factor the assembly.**  `mobiusUniformFreq_of_transducer` demands `out` emit the image's CF
   digits; the L/R machine emits letters.  Split it into an alphabet-agnostic `OutputWordFreq`
   (every output word has an `x`-independent Cesàro frequency, `K` allowed to depend on `v`) plus
   a CF bridge through `card_cf_eq_card_patWord`.  Note `hK` is FALSE at the L/R level for a
   CONSTANT `v` (`LL` occurs ~`j` times in one block), so a direct instantiation cannot work —
   the bridge is forced, not a convenience.
3. **`hgen`** — now near-free: `patWord_alternation` plus `kOut ≠ 0 → …`.
4. **`hjs`** — `JointStateFreq` for `lrDelta`, from
   `VandeheyCocycle.tendsto_jointCount_of_classEquidistribution` + the common-target reach
   (`archive/handoff/HANDOFF-2026-09-28-raney-section2.md` has the row-family identity).
5. **`htail`** — Gauss-null trigger tails: a long window forces many emitted letters, so the
   tail mass is a cylinder estimate.

## ⚠ Gotchas found this lap

- `congr 1` on `decide X = decide Y` leaves a Prop EQUALITY, which `omega` cannot do — use
  `decide_eq_decide.mpr (by omega)`.
- `Finset.card_insert_of_not_mem` is `card_insert_of_notMem` in this Mathlib.
- `simp only [Finset.mem_filter]` makes no progress on a `Set`-coerced Finset membership; add
  `Finset.coe_filter, Set.mem_ofPred_eq` (`Set.mem_setOf_eq` is deprecated).
- `omega` fails through a `def` wrapper (`runIdx` vs `Nat.findGreatest`): `show` + `rw [← runIdx]`.
- A `(by omega)` side goal whose statement mentions a not-yet-unified metavariable fails — bind
  it with a named `have` first.
- `rw [h]` where `h`'s proof is `rfl` fails on `v.sum + 2 = (v.sum+1)+1`; use `show` (defeq).
- `include hirr hw` also attaches to lemmas that don't use them — `omit hirr hw in` per lemma, and
  then pass `(w := w)` explicitly at the call sites.
- `List.range'_append_1 : range' s m ++ range' (s+m) n = range' s (m+n)` — rewriting with `←`
  splits the WRONG summand; apply it forward with explicit `(s := …) (m := …) (n := …)`.

## 📁 New files this lap

`VandeheyRunBound.lean` (Lemma 2.2) · `VandeheyAltCount.lean` (alternation counting + the
`hK`/`hkK` reduction) · `VandeheyLRTrigger.lean` (the bounds on the real machine) ·
`VandeheyLRRuns.lean` (the run dictionary) · `VandeheyLRPattern.lean` (the pattern and the
bijection) · `VandeheyRunCount.lean` (Lemma 6.1, upper half).

---
**→ Next session: NEXT action 1 (`hlen`'s lower bound).  Everything else on the concrete machine
is either proved or routine.  Tree clean at `ee5365d`.**
