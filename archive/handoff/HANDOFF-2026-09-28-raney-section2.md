# Handoff: §2 rebuilt on Raney normal form, and the equidistribution engine freed

**Date**: 2026-09-28 · **Branch**: `wip/g5-prime-subset` · **HEAD**: `b7446fa` ·
`lake build` 🟢 10312 jobs · working tree clean · nothing pushed.

Scope this run: `sorry-free: src/NormalNumbers/LiteratureVandehey.lean`, i.e. prove
`vandeheyUniformFreq_holds`.  The Smith reduction (`VandeheySmith.lean`) had already cut that
to the single leaf `MobiusCFNScale` — `x ↦ p·x` preserves CF-normality for prime `p`.  This
run removed **three** structural blockers between that leaf and the machinery, and none of
them were visible from the previous handoff.

## ✅ Landed (five green commits, every headline `#print axioms`-clean)

1. `33b15bb` **Vandehey's Lemma 2.1 proof is wrong; Raney replaces it.**
   `probes/vandehey_lemma21.py`: the prescribed rule `d = min(⌊α/γ⌋, ⌊β/δ⌋)` does not
   terminate.  Smallest witness — from the genuine `M_3` state `[[0,3],[1,1]]` with `j = 1`,
   the paper's own `d₀ = 1` lands on `[[2,1],[1,2]]`, whence the rule two-cycles through
   `[[1,2],[2,1]]`, neither in `M_3`.  Once the two column ratios separate, one floor is `0`
   and the `min` emits nothing.  A free search over digit strings rescues **every** stalled
   start, so the *statement* survives; the proof does not.  Kernel witness
   `Mat2.vandeheyStep_not_terminating`, Maze row `hall_vandehey_lemma21_min_rule`.
   `VandeheyRaney.lean`: balanced = nonnegative with neither row dominating the other;
   `raneyEntry_le` (`|det| ≥ α+δ−1`, so entries lie in `[0,D]`), `finite_isRD`,
   `exists_balanced_decomp` (descent terminates because stripping `L`/`R` strictly drops the
   entry sum), `exists_cfString_of_lrProd` (an `L/R` word *is* a CF string
   `A_{d₀}B_{d₁}⋯B_{d_m}`, `m` even), `isRD_ingest_cfString` (Lemma 2.1, no `d₀ ≥ −1`).
2. `81eab50` **The pin without bijectivity.**  `stateHorizonIntegral_pin` needed every digit
   to act bijectively on the states; the Raney step **is not injective** (`D = 2`: digit `1`
   collapses two balanced states onto `[[1,0],[0,2]]`).  `stateStepOp` is an honest average,
   so `famInf` is monotone and `famSup` antitone along the iteration; nested intervals of
   vanishing width give a limit `L ≤ γ(A)`, and `c = L/γ(A) ∈ [0,1]`.
3. `5eb48aa` **`hpin`'s second state argument weakened in all eight signatures** (every call
   site instantiates it at the target `t`).  `classEquidistribution_of_reach`,
   `tendsto_jointCount_of_reach`.
4. `b56c524` `exists_uniform_reach_of_loop` — diameter `≤ r` plus ONE self-loop gives
   exact-length-`M` reach for every `M ≥ 2r`.  One loop kills every periodicity.
5. `b7446fa` **Doeblin at a single common target.**  `stateStepIter_osc_doeblin_common`,
   `stateStepIter_osc_geom_common`, and `exists_osc_geom` /
   `stateHorizonIntegral_pin_of_reach` / `classEquidistribution_of_common_reach` /
   `tendsto_jointCount_of_common_reach` rebuilt on it.

## 🧠 The three obstructions found, and why they were fatal

* **Bipartite by determinant.**  Every `B_a` has `det = −1`, so on balanced matrices of
  determinant `±D` the automaton reaches half its states only at even times.  Fixed-length
  transitivity is *unsatisfiable*.  Cure: row-swap normalization, `δ N a = J · raneyNorm (N · B a)`,
  which keeps `det = +D`.
* **Transient states.**  Even after that, full transitivity fails: `M_D` has states no word
  reaches (Vandehey's §4).  Cure: the classical Doeblin minorization at ONE common state.
* **The Lyapunov weight.**  Dropping from `1−2β` to `1−β` breaks the old weight `2β` — its
  `Ω`-coefficient becomes exactly `1`.  Cure: `V = Ω + (9/5)β·Λ`, rate `1 − β/10`.

## 🎯 The structure that makes the rest provable

On the **row family** `R_b = [[1,b],[0,D]]`, `0 ≤ b < D`:

* `δ(R_b, a) = R_{(a + b⁻¹) mod D}` for every digit `a ≥ D − 1` and `b ≠ 0` — i.e. the Raney
  automaton restricted to the row family **is** the class automaton `b ↦ a + b⁻¹` of
  `VandeheyClass.lean`.  Threshold exact, probed to `D = 23`.
* `δ(diag(D,1), a) = R_{a mod D}`; `δ(R_0, a) = diag(D,1)` for every `a`.
* One digit carries every other state into the row family.
* Hence `z = R_1` has **in-radius 2 from the whole state set**, and a self-loop at `a = D`
  (index `(D+1) mod D = 1`).  Verified at `D = 2,3,5,6,7,11,13,17`; **composite `D` has no
  common target at all**, which is consistent with `MobiusCFNScale` quantifying over primes.

## 🎬 Next actions, in order

1. **`raneyNorm : Mat2 → Mat2`** as a total function, by well-founded recursion on
   `(a+b+c+d).toNat`, guarded so the subtracted row is positive:
   `if 0 < a+b ∧ a ≤ c ∧ b ≤ d then raneyNorm (stripL N) else if 0 < c+d ∧ c ≤ a ∧ d ≤ b then
   raneyNorm (stripR N) else N`.  Termination: under either guard both `a+b` and `c+d` are
   positive, so `toNat` strictly drops.  Then `raneyNorm_balanced` and
   `exists_lrProd_mul_raneyNorm` (uniqueness of the normal form follows because both guards
   together force `a = c`, `b = d`, i.e. `det = 0`).
2. **`RaneyState D`** as a `Fintype` subtype `{M // IsRD D M ∧ M.det = D}` (`finite_isRD` gives
   the instance), and `δ D : RaneyState D → ℕ → RaneyState D`, `δ N a = J · raneyNorm (N · B a)`.
3. **The common-target reach**, for prime `D`: the row-family identity above, then
   `exists_uniform_reach_of_loop`-style padding to a fixed `M ≥ 4`.  Feeds
   `tendsto_jointCount_of_common_reach` directly.
4. **§5–§6 assembly**: `ℓ(n) = c₁n(1+o(1))`, `#occ_r(n) = c_r n(1+o(1))`.  The paper warns
   trigger lengths are NOT provably bounded — plan for the `f_j^±` approximants.

## ⚠️ Gotchas

- `Int.natCast_nonneg` takes its argument as `n`, not a type ascription `(α := ℤ)` / `(R := ℤ)`.
- `famRange_nonempty`/`famInf_le`/`le_famSup` all need `[Nonempty S]`; add it to every new
  lemma that touches `famInf`/`famSup`.
- `stateStepOp_mem_range_bounds` already existed; this run added the equivalent
  `famInf_le_stateStepOp` / `stateStepOp_le_famSup` separately.  Harmless duplication, worth a
  cleanup lap.
- `A 0 = 1` for `Mat2.A` is not `rfl` until `Nat.cast_zero` has fired: `simp only [A,
  Nat.cast_zero]; rfl`.
- In `exists_cfString_of_lrProd` the emitted digit list may contain interior `0`s (`B 0 = J`);
  that is fine for the matrix identity but a CF *reading* of the string needs the run-length
  form.

## 📁 Key files

- `src/NormalNumbers/VandeheyRaney.lean` — §2 rebuilt, plus the refutation witness.
- `src/NormalNumbers/VandeheyStatePin.lean` — the pin, now `hbij`-free and common-target.
- `src/NormalNumbers/VandeheyClassEquidist.lean` — `*_of_common_reach` entry points.
- `src/NormalNumbers/VandeheyAutomaton.lean` — `exists_uniform_reach_of_loop`.
- `probes/vandehey_lemma21.py` — the non-termination probe.

---
**→ Next session: start at NEXT action 1 (`raneyNorm` as a total function).  Everything the
reach proof needs downstream (`tendsto_jointCount_of_common_reach`) is already in the kernel.**
