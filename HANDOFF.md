# Handoff: Vandehey's output side opened — Lemma 4.3 proved, §6 sandwich assembled

**Date**: 2026-09-28 (lap 1, review lap) · **Branch**: `wip/g5-prime-subset` ·
**HEAD**: `8b30f7e` · `lake build` 🟢 10313 jobs · working tree clean · nothing pushed.

Scope: `sorry-free: src/NormalNumbers/LiteratureVandehey.lean`, i.e. prove
`vandeheyUniformFreq_holds`.  **Read `DIRECTION.md` CURRENT DIRECTIVE first — it outranks this
file.**  It was set this lap and it still stands.

## ⚠️ The course correction this lap made

The previous three laps all went into the transducer's **input** side (Raney normal forms §2,
the bijectivity-free transfer-operator pin, Doeblin minorization at a common target).  The
**output** side — Vandehey's Lemma 4.3 + §5 triggers + §6 assembly — had never been touched,
and it is the route-decisive piece: if output-word frequencies cannot be read off the joint
(window, state) frequencies, the entire automaton build is worthless.  `DIRECTION.md` now
FORBIDS spending a lap on `raneyNorm` / `RaneyState` / the common-target reach (the old
HANDOFF's NEXT 1–3) until the output engine is closed.

## 🔑 The structural find that makes §5–§6 elementary

Our own `VandeheyCocycle.tendsto_jointCount_of_classEquidistribution` returns the joint
(window, state) limit in **factorized** form `ν t · γ(I_q)` — the state reads the past, the
window reads the future, and ψ-mixing decouples them.  Vandehey has only `ρ ≪≫ μ̃`
(Remark 3.6, no product structure), so he needs a genuine limiting measure `ρ`, built from
Ryll-Nardzewski a.e. convergence plus Vitali-Hahn-Saks on top of the hot-spot criterion that
Airey–Mance later refuted.  With the product form, countable additivity of the limit reduces to
countable additivity of `γ` alone — and the infinite CF alphabet is escaped by a **finite**
digit-truncated family of Gauss mass `> 1 − ε`.  That finite escape is also exactly the
tightness patch the published §3 owes and never pays.

## ✅ Landed — `src/NormalNumbers/VandeheyOutputFreq.lean` (new, in the root import)

Three green commits, every headline `#print axioms`-clean (trust base only).

1. `cedcf6f` **the upper-bound engine.**
   - `JointStateFreq δ s₀ ν` — the factorized hypothesis.  Guard rule discharged:
     `jointStateFreq_unit` (content locator: the one-state automaton, `ν ≡ 1`, on CF-normality
     alone), `not_jointStateFreq_unit_zero` (`ν ≡ 0` is FALSE, so `ν` is load-bearing),
     `wCount_zero_length` / `wCount_zero_weight` (the `m = 0` and `a ≡ 0` boundaries).
   - `gaussMeasure_allWordsEvent m = 1`; `exists_boundedWords_sum_gt` (the finite escape).
   - `wCount_le_of_finset` — the pointwise split, pure fiberwise counting.
   - `eventually_wCount_le` — `wCount ≤ (Sb + ε)·n` eventually.
2. `25d1c5e` **Vandehey Lemma 4.3 at a single window length.**
   - `sum_gaussMeasure_le_one_of_length`, `sum_filter_mem_eq` (the fiberwise identity shared by
     both halves), `wCount_ge_of_finset`, `eventually_le_wCount`.
   - `wLimit ν t a m` = `sSup` over FINITE subfamilies of `allWords m`; `wLimit_set_nonempty`,
     `wLimit_set_bddAbove` (bound `C · ν t`).
   - **`tendsto_wCount_div`** — for a bounded nonnegative weight on the countably infinite
     length-`m` genuine words, `wCount / n → wLimit ν t a m`, a value mentioning no `x`.
3. `8b30f7e` **the trigger layer and its tail.**
   - `fireAt` / `fireTotal` (untruncated per-position multiplicity as a supremum, ATTAINED
     because `K` bounds it: `exists_fireAt_eq_fireTotal`), `trigCount` bucketed by
     length × state, `trigCount_eq` (= `Σ_i fireAt i J`), `sum_state_wCount`, `trigLimit`,
     **`tendsto_trigCount_div`** (truncated count converges `x`-independently).
   - `trigPrefix k t m` / `trigInd` / `tailMass k ν m`; `cfWindow_take` (windows nest);
     **`fireTotal_sub_fireAt_le`** (the structural step: a position whose truncation misses a
     trigger has its length-`J` window in `trigPrefix`, by contraposition);
     `trigTotal_le_trigCount_add`; `wLimit_trigInd_le`.

## 🎬 Next actions, in order

1. **Close the assembly** — `exists_tendsto_trigTotal`.  All the pieces are in the kernel; what
   remains is arithmetic.  Sketch, verified on paper:
   - `0 ≤ wLimit ν t a m` (take `Q = ∅` in `le_csSup`), hence `trigLimit k ν` is **monotone**
     in `J` (larger `Finset.Icc 1 J`).
   - `trigLimit k ν J ≤ K`: pick a CF-normal `x` (`exists_isCFNormal`); `trigTotal x n ≤ K·n`
     from `fireTotal_le`, so `trigCount x n J / n ≤ K`, and `tendsto_trigCount_div` passes it
     to the limit.
   - So `L := ⨆ J, trigLimit k ν J` exists and `Tendsto (trigLimit k ν) atTop (nhds L)`
     (`tendsto_atTop_ciSup`).
   - For `ε > 0` pick `J ≥ 1` with `trigLimit J > L − ε/3` **and** `K · tailMass k ν J < ε/3`
     (uses the one honest hypothesis `Tendsto (tailMass k ν) atTop (nhds 0)`).
   - Lower: `trigCount_le_trigTotal` + `tendsto_trigCount_div` ⇒ eventually
     `trigTotal/n > L − ε/2`.
   - Upper: `trigTotal_le_trigCount_add` + `tendsto_wCount_div` (with `C = 1`, weight
     `trigInd`) + `wLimit_trigInd_le` ⇒ the majorant's limit is
     `trigLimit J + K·Σ_t wLimit ν t (trigInd k t J) J ≤ L + K·tailMass J < L + ε/3`.
   - Conclusion: `∃ L, ∀ x CF-normal, trigTotal k δ s₀ x n / n → L`.
   Guard rule: `trigPrefix`/`tailMass` are defs, not new `Prop`s, but the assembly's
   hypothesis bundle (`hK`, `hgen`, `htail`) needs a content locator — the EMPTY trigger family
   (`k ≡ 0`) satisfies everything with `L = 0`, and a singleton bounded-length family with
   `tailMass` eventually `0` gives the finite case, whose limit is the plain sum.
2. **The per-matrix either-or endgame.**  `LiteratureVandehey.vandehey_matrix_action_of_uniformFreq`
   is stated for ALL matrices at once; the leaf route needs the single-matrix form so
   `MobiusCFNScale` can be reached from a per-matrix uniform-frequency statement.  Its proof
   body is already per-matrix (`intro x a b c d …; obtain ⟨L, hL⟩ := h a b c d …`), so this is
   a cheap refactor.  Do it when the assembly lands.
3. **Bridge §5 to the CF digits of `p·x`.**  `trigTotal` counts trigger firings; the output
   word count is that up to `O(1)` (Vandehey §5, the four "not nicely" positions), and the
   output *length* `ℓ(n) = c₁n(1+o(1))` is Lemma 6.1 — the SAME engine with the weight
   `g(s,M)` of §6, so `tendsto_wCount_div` covers it too.  Then rescale `i ≤ ℓ(n)` to
   `i ≤ m` via `ℓ⁻¹`.
4. **Only then** the supply side: `raneyNorm` as a total function by well-founded recursion on
   `(a+b+c+d).toNat`, `RaneyState D` as a `Fintype` subtype, `δ N a = J · raneyNorm (N · B a)`,
   and the common-target reach for prime `D` from the row-family identity
   `δ(R_b, a) = R_{(a+b⁻¹) mod D}` (probed to `D = 23`; composite `D` has no common target,
   consistent with `MobiusCFNScale` quantifying over primes).  Details in
   `archive/handoff/HANDOFF-2026-09-28-raney-section2.md`.

## ⚠️ Gotchas found this lap

- **`boundedWords` and `mem_boundedWords` are AMBIGUOUS**: `NormalNumbers.boundedWords`
  (`CFSchedule.lean`, `Finset`, implicit args) vs `VandeheyAut.boundedWords`
  (`VandeheyAutomaton.lean`, explicit args).  The ambient-namespace one wins over `open
  VandeheyAut`, so `mem_boundedWords m w` fails with "Function expected".  Use the implicit
  form `mem_boundedWords.mp`.
- **`ℝ≥0∞` needs `open ENNReal`** — it is scoped notation, not transitive through imports.
  Without it Lean parses `ℝ ≥ 0 ∞` and reports `LE Type` / `OfNat Type 0`.  This file spells
  `ENNReal` out.
- `div_le_div_iff` is gone in v4.33; it is **`div_le_div_iff₀`**.
- `tendsto_finset_sum` → **`tendsto_finsetSum`**.
- `Finset.filter_card_add_filter_neg_card_eq_card` → **`Finset.card_filter_add_card_filter_not`**.
- `omit [inst] in` must come **before** the docstring, not between docstring and `lemma`
  (same shape as `set_option … in`).
- `cfWord_take`, `cfWord_iterate`, `mem_familySetC_iff_cfWord`, `cfWord_length` live in
  `NormalNumbers` directly (`VandeheyTwoPoint.lean` lines < 127), **not** in `VandeheyTwo`.
- `Metric.tendsto_atTop` turns the goal into `∃ N, ∀ n ≥ N, …`, which `filter_upwards` cannot
  use.  Use **`Metric.tendsto_nhds`**, which gives `∀ ε > 0, ∀ᶠ n in l, …`.

## 📁 Key files

- `src/NormalNumbers/VandeheyOutputFreq.lean` — everything above (the output side).
- `src/NormalNumbers/VandeheyCocycle.lean` — `JointStateFreq`'s supplier,
  `tendsto_jointCount_of_classEquidistribution`.
- `src/NormalNumbers/VandeheyClassEquidist.lean` — `*_of_common_reach` entry points.
- `src/NormalNumbers/VandeheySmith.lean`, `VandeheySerret.lean` — the leaf reduction.
- `PENDING_WORK.md` queue item 0 — the crux decomposition, mirrored here.
- `/tmp/.../scratchpad/vandehey.txt` is gone with the box; re-extract the paper with
  `python3 ~/src/sum-product/tools/pdf_extract.py papers/vandehey-2017-matrix-actions-cf-normality.pdf`.
  §4.3 is around line 6290, §5 around 6860, §6 around 7210.

---
**→ Next session: NEXT action 1 (close `exists_tendsto_trigTotal`).  Every input it needs is
already in the kernel; the sketch above is the whole proof.**
