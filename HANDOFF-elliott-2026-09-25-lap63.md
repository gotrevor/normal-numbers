# HANDOFF elliott 2026-09-25 laps 55-63 — leaf 2 assembled; 2 sorries left

Branch `wip/elliott-port`, HEAD `0426217`, **working tree clean**.
`lake build NormalNumbers.ElliottAxiomAudit` green, **9577 jobs**.
Never `lake exe cache get`.  Never edit `.lake/packages/lean-proofs-latest/`.
**`DIRECTION.md` CURRENT DIRECTIVE governs — read it first.  Do NOT edit it (altitude laps own it).**

## One-paragraph version

Every one of the five sub-steps the directive mandated for leaf 2 now has its load-bearing content
machine-checked, and leaf 2 is **assembled**: `ElliottLeafTwo.nonasymptotic_of_affineCM` is proved
outright from two halves, with no gap at the junction.  Along the way one **real obstruction** was
found and discharged (lap 60 → 62): `AffineCMLogElliott` hands out its threshold *per affine pair*,
so the squarefull `d`-sum needs a truncation point fixed before the function — strictly stronger
than lap 57's bound on the total, and exactly the inference that killed the `v`-expansion at lap 54.
It is now proved by a Rankin shift.  `src/` holds **exactly two** sorries, both in
`ElliottLeafTwo.lean`, and both are bookkeeping over already-proved content.

## `src/` sorry inventory (authoritative — `grep -rn sorry src/NormalNumbers/Elliott*.lean`)

| file:line | name | state |
|---|---|---|
| `ElliottLeafTwo.lean:73` | `exists_caseA_thin_threshold` | all ingredients proved; see plan below |
| `ElliottLeafTwo.lean:124` | `exists_caseB_threshold` | 6 itemised steps, 5 proved, 1 open |

`ElliottLadder.nonasymptotic_of_affineCM` **no longer exists** — leaf 2 moved to
`ElliottLeafTwo.lean` (it must: it consumes five modules that import `ElliottLadder`).
`ElliottGeneral.nonasymptoticLogElliott` is repointed and unchanged in statement.

## New modules this session (all zero-sorry, all bare trust triple, all in the audit surface)

| module | content |
|---|---|
| `ElliottPretentiousTransfer` | 1-bounded pretentious triangle ineq (constant 3); `pretentiousDistSq g u X = ∑(1−‖g p‖²)/p` **deterministically**; `mrtNonpretentious_transfer` |
| `ElliottSquarefull` | `local_factor_squarefull_le`; **`sum_Icc_le_exp_two`** (`∑_{m≤Y} f m ≤ e²`, absolute) |
| `ElliottSquarefullConv` | `cmExt`, `mul_apply_divisors`, `squarefullPart = (μ·cmExt U) ⋆ U`, `u(p^k) = U(p^k) − U p·U(p^{k−1})`, `sum_norm_squarefullPart_div_le_exp_two` |
| `ElliottProgression` | `integerAffine_progression`; **`det_progression`** (determinant preserved *exactly*) |
| `ElliottCaseAThin` | `sum_window_le_transfer_ge`, `norm_elliottLogCorrelation_le_caseA_thin` (**no regime hypothesis**), `div_le_four_mul`, `natLog_mul_log_two_le` |
| `ElliottRankin` | `local_factor_geom_le` (general ratio), `sum_primesBelow_inv_mul_sqrt_le` (`∑_p p^{-3/2} ≤ 2`), `sum_Icc_shifted_le` (`≤ e^{11}`), **`exists_squarefull_tail_bound`** |

## NEXT (lap 64), in order

### 1. `exists_caseA_thin_threshold` — a dichotomy on `⌊X/W⌋`, both branches already proved

* `⌊X/W⌋ ≥ 2|b₁|+2`: use `ElliottCaseAThin.norm_elliottLogCorrelation_le_caseA_thin` with
  `L = caseAScale a₁ b₁ X W = a₁(⌊X/W⌋+1) − |b₁|` (`hLle` is then `le_rfl`), then `div_le_four_mul`
  gives `Y/L ≤ 4W`, so `Nat.log 2 (Y/L) + 1 ≤ Nat.log 2 (4W) + 1 = Nat.log 2 W + 3`, and
  `natLog_mul_log_two_le` turns that into `log W/log 2 + 3`.  Choose `D₀ = log(K/ε)` with
  `K = (a₁+|b₁|)·2·hallConst·e^{1+B}·(1/log 2 + 3)` and `W₀` large enough to absorb `+|b₁|`.
* `⌊X/W⌋ < 2|b₁|+2`: then `X < W(2|b₁|+3)`, so `log X ≤ log W + log(2|b₁|+3)`; with
  `W₀ ≥ 2|b₁|+3` this gives `(1/2)log X ≤ log W`, i.e. the **thick** regime, and the already-proved
  `ElliottCaseA.exists_caseA_threshold ha₁ b₁ (θ := 1/2) hε` applies directly.
* **The joint:** `primeDefect` is monotone in its scale (summands `1/p − ‖g p‖/p ≥ 0` for
  1-bounded `g`), and `caseAScale ≤ a₁X+|b₁|`, so the hypothesis stated at `L` implies the one the
  thick lemma wants at `Y`.  Take `D₀ = max` of the two branches' thresholds, `W₀ = max` of theirs
  and `2|b₁|+3`.

### 2. `exists_caseB_threshold` — one open step remains

Its docstring itemises six steps.  Proved: (1) `ElliottRandomize.exists_cover_pair_ge`,
(2) `ElliottPretentiousTransfer.mrtNonpretentious_transfer`, (3) `ElliottSquarefullConv`,
(4) `exists_squarefull_tail`, (5-arithmetic) `ElliottProgression`.  **Open: the step-5
window/weight reindexing** — the constrained window `{n ≡ n₀ mod q}` becoming an
`elliottLogWindow` at scale `X/q` with the *same* ratio `W`, and `1/(qk+n₀)` versus `(1/q)(1/k)`
(difference sums to `O(1/q)`, then multiplied by the `e²` tail bound).  Bulky, not conceptually
uncertain.  Then (6) `A₀ :=` finite max of `h`'s thresholds over `d₁,d₂ ≤ D`, plus the `A'` slack.

## Traps recorded — do NOT re-derive

1. **`‖u n‖ ≤ 2` is FALSE for general `n`** (it grows with `ω(n)`); only `‖u(p^k)‖ ≤ 2` holds.
   `ElliottSquarefull.sum_Icc_le_exp_two`'s `hbd` is therefore stated at **prime powers only**,
   which is also all the local-factor proof uses.  The strong form is unsatisfiable.
2. **A bounded total is not a small tail.**  Lap 57's `e²` bound does *not* give
   `exists_squarefull_tail`; that needed the Rankin shift.  This is the lap-54 `v`-expansion error
   in a new costume — check it, never assume it.
3. **The Rankin shift must be strictly below `1/2`.**  At `δ = 1/2` the local factor is
   `1 + 2/(√p(√p−1))` and `∑_p 1/(√p(√p−1)) ≍ ∑_p 1/p` diverges.  `δ = 1/4` is used.
4. **Keep rpow exponents positive.**  Write the Rankin step as `shifted d / d^{1/4}`, never
   `d^{-1/4} · shifted d`; then `gcongr` closes the monotonicity in one call.
5. **`caseAScale` is a nat subtraction** and truncates to `0` when `|b₁|` dominates, so the cast
   `↑(M−b) ≤ ↑M − ↑b` is **false** there.  `le_integerAffine_of_mem_window` case-splits; the
   truncated branch is just `0 ≤ a₁n+b₁`.
6. **`div_le_four_mul` needs `⌊X/W⌋ ≥ 2|b₁|+2`, not `≥ |b₁|+1`.**  The margin is
   `b(1+4W) ≤ 3Wa₁(q+1)`; the factor 2 is load-bearing.
7. **`q = d₁d₂`, not `lcm`.**  Only then does the determinant come out *equal* rather than scaled.
8. The `v`-expansion (`‖g̃‖ = 1 ⋆ v`) is **refuted** — see `DIRECTION.md` item 0.  Do not build it.

## Fidelity note (do not lose)

`Erdos67b.IsMultiplicativeOnPositiveInt` has **no coprimality hypothesis** — it is *complete*
multiplicativity.  So the dependency's `NonasymptoticLogElliott` is Tao 2016 Thm 1.3 restricted to
completely multiplicative `g₁,g₂`.  The kickoff ratifies that `Prop` as the target, so the target
stands, but the headline must be *described* as the CM case, and `STATUS.md` must say so.  The
corrected leaf-2 route never uses complete multiplicativity of the `g_i`, so a genuinely general
`NonasymptoticLogElliottMult` stated in `src/` is a cheap stretch goal once the headline lands.
