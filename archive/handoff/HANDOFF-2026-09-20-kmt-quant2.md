# HANDOFF 2026-09-20 — `KMT_quant₂` two-constant re-freeze: DONE

**Branch** `wip/g5-prime-subset`.  **HEAD at handoff** `65b9311` (this doc committed on top).
**Build** green (`lake build`, 9098 jobs); `src/NormalNumbers/G4WiringSparse.lean` sorry-free.
The only `sorry` reachable in the repo from this file's imports is the pre-existing, out-of-scope
`src/NormalNumbers/PrimeLambertOscillation.lean:94` (`phaseOscillation`) — forbidden drift, untouched.

Branch `wip/g5-prime-subset`.  File `src/NormalNumbers/G4WiringSparse.lean` (pure addition; `git diff
2a58809` shows **no deleted line** — every frozen statement is untouched).  The file is sorry-free and

```
#print axioms NormalNumbers.G4Sparse.exists_sparse_normal_of_KMT_quant₂
  → [propext, Classical.choice, Quot.sound]
```

## What landed (the whole kickoff, leaves 1–6)

| name | role |
| --- | --- |
| `KMT_quant₂ C₁ C₂` | ratified statement, verbatim: `C₁` on the two distance terms, `C₂` on the sieve/truncation term |
| `KMT_quant₂_of_KMT_quant` | the one-constant form is the diagonal `C₁ = C₂ = C` |
| `BlockData.Good₂ C₁ C₂` | `Good` with `terms` split into `terms₁`/`terms₂`; `sep` keeps the repaired `1 ≤ i` |
| `BlockData.kmt_along₂` | `KMT_quant₂ + Good₂ → KMT_along` |
| `GoodExists.JF₂ C₁ C₂ i` | `findGreatest {J ≤ i : ∀ J' ≤ J, |C₁ J'| ≤ ⁴√i ∧ log|C₂ J'| ≤ i/2}` |
| `GoodExists.DDJ Jf` | the explicit block data with an **arbitrary** schedule (`x`, `B`, `ε` as in `DD`) |
| `GoodExists.terms₁_tendsto`, `terms₂_tendsto` | leaves 5a/5b, both stated for a general `Jf` |
| `GoodExists.log_o_pow₂` | **the mathematical content**: `log i = o(4^{Jᵢ})` for the `JF₂` schedule |
| `GoodExists.tail_tendsto_gen` | leaf 6 for a general `Jf` |
| `exists_good₂`, `exists_sparse_normal_of_KMT_quant₂` | assembly |

## The advance

The frozen `KMT_quant C` charges one constant to all three terms, so `Good.terms` silently demands
`log C_FL(k) = o(4^k)` for the fundamental-lemma constant of KMT (4.20) — unverified
(`papers/kmt-2023-prop43-k-dependence.md`).  `KMT_quant₂` charges the sieve term separately, and the
two-constant existence theorem only needs `log log C₂ k = o(4^k)`, i.e. `C₂` may be
`exp(exp(o(4^k)))`.  The mechanism is in `log_o_pow₂`: at the maximality point `Jᵢ+1` the schedule
fails for one of two reasons, and the `C₂` branch converts `i/2 < log|C₂(Jᵢ+1)|` into
`log i < log 2 + log log C₂(Jᵢ+1)`, i.e. one extra logarithm of slack against `4^{Jᵢ+1}`.
The `C₂`-term of KMT is killed by the schedule itself: `1/(8Jᵢ²εᵢ) = (i+3)³/Jᵢ² ≥ i` with
`εᵢ = 1/(8(i+3)³)` and `Jᵢ ≤ i`, so `C₂(Jᵢ)·exp(−1/(8Jᵢ²εᵢ)) ≤ exp(i/2)·exp(−i) = exp(−i/2)`.

Side benefit: `kmt_along₂` needs **no sign hypothesis** on the constants.  `kmt_along` had to derive
`0 ≤ C (Jᵢ)` by contradiction from the bound; the two-constant proof instead majorises by
`|C₁(Jᵢ)|·B + |C₂(Jᵢ)|·T` and squeezes against `|terms₁| + |terms₂|`.  Same trick would simplify the
one-constant proof if it is ever re-touched.

## What is still open on the headline

`KMT_quant₂` is a **frozen input**, not a theorem: the remaining obligation is to extract `C₁`, `C₂`
from KMT 2023 Prop. 4.3 with the stated `k`-dependence and verify `log C₁ k = o(4^k)`,
`log log C₂ k = o(4^k)`.  `papers/kmt-2023-prop43-k-dependence.md` has the (4.7)/(4.20)/(4.22)
accounting; the open piece is the fundamental-lemma constant in (4.20).  That is the next crux.

## Gotchas met (for the corpus)

* `Nat.findGreatest_is_greatest` + `push_neg` on a **conjunctive** predicate yields an
  *implication* `A → ¬B`, not `¬A ∨ ¬B` — destructure accordingly (cost ~2 build cycles).
* Nested `|…|` does not parse (`|Real.log |x||`); write `abs (Real.log |x|)`.
* `Tendsto.neg` is for `𝓝`-limits; for `atTop → atBot` use `tendsto_neg_atTop_atBot.comp`, and
  `.congr` needs `simp only [Function.comp_apply]` before `ring`.
* ⚠️ editing hazard: a python splice keyed on a proof-body fragment (`push_neg at hng; obtain …`)
  matched the **older** copy of the same idiom and silently deleted 400 lines.  Anchor splices on a
  unique statement line, and `assert s.count(old) == 1`.

## Exact next steps for the next lap

1. **The crux, stated concretely.**  `KMT_quant₂ C₁ C₂` is still a frozen *input*.  Discharge it by
   reading KMT 2023 (arXiv:2304.05344) Prop. 4.3 and its proof, and producing explicit `C₁ k`, `C₂ k`
   with `log C₁ k = o(4^k)` and `log log C₂ k = o(4^k)`.  The accounting so far is in
   `papers/kmt-2023-prop43-k-dependence.md`:
   * (4.7) and (4.22) — the two distance terms — carry the `C₁` constant; the note already argues
     these are `exp(O(k log k))`-ish, i.e. comfortably `log C₁ k = o(4^k)`.  **Verify this line by
     line and record the exponent**; that is the smallest useful probe.
   * (4.20) — the sieve/fundamental-lemma step — carries `C₂`.  Its constant is the open piece.  The
     only thing needed now is a bound of the shape `C₂ k ≤ exp(exp(o(4^k)))`, which is very weak;
     a crude `C₂ k ≤ exp(exp(k²))`-type bound from the standard Rosser–Iwaniec fundamental lemma
     (sieve dimension `k`, level `x^ε`) would already close it.
2. Landing shape: add `theorem KMT_quant₂_of_KMT_prop43 …` (or an axiom narrowed to (4.20) alone,
   with the distance terms proved), then feed it to `exists_sparse_normal_of_KMT_quant₂` to get an
   *unconditional* `∃ S, DivergentRecip S ∧ IsNormal 4 (subsetLambert S 4)`.
3. Do not re-derive `exists_good₂` / `log_o_pow₂`: the schedule side of the sandwich is closed and
   axiom-clean.  If a future lap needs different `ε`, note that `GoodExists.DDJ` now takes an
   arbitrary schedule `Jf`, and `terms₁_tendsto`, `terms₂_tendsto`, `tail_tendsto_gen` are all
   stated for a general `Jf` — only `JF₂` and `log_o_pow₂` are schedule-specific.
4. If the paper is not readable from the box, append a dated request to `ON-LINE-REQUEST.md` for the
   text of KMT 2023 §4 (Prop. 4.3 proof, eqs (4.7), (4.20), (4.22)) and work step 1's (4.7)/(4.22)
   half meanwhile.
