# HANDOFF elliott 2026-09-25 laps 64-70 — Case A CLOSED; Case B has every ingredient but the assembly

Branch `wip/elliott-port`, HEAD `e3e8099`, **working tree clean**, `lake build` green (9581 jobs
for the audit surface).  Never `lake exe cache get`.  Never edit `.lake/packages/lean-proofs-latest/`.
**`DIRECTION.md` CURRENT DIRECTIVE governs — read it first.  Do NOT edit it.**

## One-paragraph version

`exists_caseA_thin_threshold` is **proved**, so Case A now covers every window.  `src/` holds
**exactly one** sorry: `ElliottLeafTwo.exists_caseB_threshold`.  Every ingredient it needs is now
proved and in the audit surface, across five new zero-sorry modules.  The design decision that made
Case B tractable this session: **expand one function at a time** (stage 1 on `U₁`, stage 2 on `U₂`
*after* the first substitution).  Expanding both at once produces a two-variable tail
`∑_{d₁,d₂} ‖u₁d₁‖‖u₂d₂‖·gcd(d₁,d₂)/(d₁d₂)`, whose `gcd` factor breaks the naive product bound and
would need a second, two-dimensional Rankin argument.  One variable at a time avoids it entirely.

## `src/` sorry inventory (authoritative)

| file:line | name | state |
|---|---|---|
| `ElliottLeafTwo.lean:~270` | `exists_caseB_threshold` | all ingredients proved; only the ε-budget assembly remains |

## New modules this session (all zero-sorry, all in the audit surface)

| module | content |
|---|---|
| `ElliottReindex` | `progScale`, `progLow`, `progression_image`, `sum_progression_eq`, **`norm_sum_sub_reindexed_le`**: the weighted sum over `n ≡ n₀ (q)` in `(X/W,X]` = `(1/q)·(genuine elliottLogWindow sum at X'=(X−n₀)/q, W'=min W X')` up to an **absolute** error `≤ 4` |
| `ElliottDivisorTail` | `sum_Icc_inv_le`, `sum_Icc_multiples_inv_le` (`∑_{L≤m≤Y,d∣m}1/m ≤ (1+log Y−log L)/d`), `sum_window_le_transfer_nonneg` (thin-window transfer for an ARBITRARY nonneg weight), **`sum_window_divisor_tail_le`** |
| `ElliottExpand` | `divTerm`, `posExt_eq_sum_divTerm`, `elliottLogCorrelation_expand`, **`norm_elliottLogCorrelation_le_truncated`** |
| `ElliottRestricted` | `newShift`, `det_newShift` (determinant preserved exactly), **`norm_restrictedCorr_le`** |
| `ElliottScaleDescent` | `mrtDescentCost`, `reciprocalPrimeInterval_le_log_two_add`, `pretentiousDistSq_descend`, **`mrtNonpretentious_descend`** |

Also in `ElliottSquarefullConv`: `moebius_pmul_cmExt_mul_cmExt`, `squarefullPart_mul_cmExt`,
`U_eq_sum_divisors` — the reconstruction identity `U = u ⋆ Ũ`.

## The Case-B chain, as now proved (stage 1)

For `U₁` unimodular multiplicative and any `1`-bounded `g₂`:

1. `ElliottExpand.norm_elliottLogCorrelation_le_truncated`:
   `‖corr(U₁,g₂)‖ ≤ ∑_{d≤D}‖u₁d‖·‖corr_d‖ + (a₁+|b₁|)(1+log Y−log L)ε`,
   where `ε` is `ElliottRankin.exists_squarefull_tail_bound`'s uniform tail and
   `L = caseAScale` makes `Y/L ≤ 4W` (`ElliottCaseAThin.div_le_four_mul`), so the tail is
   `O(ε(log W+1))`.
2. `ElliottRestricted.norm_restrictedCorr_le`:
   `‖corr_d‖ ≤ ∑_{n₀<d}((1/d)‖corr(Ũ₁,g₂; a₁, a₂d, c, a₂n₀+b₂; X', W')‖ + 4)`,
   `c = (a₁n₀+b₁)/d`.  **With `q = d` the first dilation is unchanged**, and `det_newShift` gives
   `a₁(a₂n₀+b₂) − (a₂d)c = a₁b₂ − a₂b₁` exactly.
3. `∑_{d≤D}‖u₁d‖ ≤ D·e²` (from the tail bound at `D`), so the `4d` errors and the per-pair
   `ε''` are affordable: choose `ε → D → ε'' = ε/(cD²) → A₀`.

## NEXT (lap 71), in order

### 1. Stage 2 — expand the second function (mechanical, reuses stage 1 verbatim)
Add `elliottLogCorrelation_swap : corr g₁ g₂ a₁ a₂ b₁ b₂ X W = corr g₂ g₁ a₂ a₁ b₂ b₁ X W`
(one `Finset.sum_congr` + `ring`).  Then apply `ElliottExpand` + `ElliottRestricted` to the
swapped correlation, expanding `U₂`, and swap back so that the non-pretentious `Ũ₁` is again the
FIRST argument — which is where `AffineCMLogElliott` wants it.

### 2. The ε-budget assembly of `exists_caseB_threshold`
Order of choice (no circularity): `ε` → `D` (from `exists_squarefull_tail` at `ε/(4·const)`) →
`ε'' = ε/(c·D⁴)` → `A₀^h` from `h` for each of the finitely many substituted affine pairs
(`d₁,d₂ ≤ D`, `n₀ < d₁d₂`) → `A₀ := max(A₀^h + mrtDescentCost + 3, 2D⁴, …)` large enough that
  * `A'' := A − ⌈mrtDescentCost⌉ − 1 ≥ A₀^h` and `A'' ≤ W' = min W X'`;
  * `X ≤ X'^2` for `ElliottScaleDescent.mrtNonpretentious_descend` (guaranteed by `A₀ ≥ D⁴`);
  * the additive `4·(d₁+d₂)·D·e²` and `(a₁+|b₁|)(1+log 4)ε` constants are `≤ (ε/2)log W`
    (use `W ≥ A ≥ A₀` and `log W ≥ log A₀`).
`ElliottPretentiousTransfer.mrtNonpretentious_transfer` carries the hypothesis from `g₁` to `U₁`
(Case B's small defect `D₀` is exactly its `hcaseB`), and `Ũ₁` has the same prime values as `U₁`,
so its pretentious distances are literally equal.
`ElliottRandomize.exists_cover_pair_ge` supplies the unimodular `U₁,U₂` from the `1`-bounded
`g₁,g₂` at the start.

## Traps recorded this session — do NOT re-derive

1. **The two-variable tail is a trap.**  Expanding both functions at once needs
   `∑ gcd(d₁,d₂)/(d₁d₂)` over squarefull pairs — true but a second Rankin argument.  Expand one
   at a time; the crude bound `‖corr_d‖ ≤ (stuff)/d` then only ever involves ONE divisor.
2. **A per-`d` additive constant in the TAIL is fatal** (`∑_{d≤Y}‖u d‖` is unbounded), which is
   why the tail goes through `sum_window_le_transfer_nonneg` + `sum_Icc_multiples_inv_le`
   (keeping `1/d`) and NOT through the progression lemma.  In the HEAD (`d ≤ D`) the additive
   `4` per class is fine.
3. **`le_or_lt` does not exist in this mathlib** — use `le_or_gt`.
4. **`omega` refuses any product/quotient of two variables.**  Introduce the product as an
   `fvar` (`set`) or route through `Nat.le_sub_of_add_le`, `Nat.le_div_iff_mul_le`,
   `Nat.div_lt_iff_lt_mul` by hand.  All of `ElliottReindex` is written this way.
5. **`rw [← hsplit]` where `hsplit : d*(n/d)+n₀ = n` loops** (it rewrites the `n` inside `n/d`).
   Cast to `ℤ` first and rewrite that.
6. `Complex.norm_real` leaves a *real* norm — follow with `Real.norm_eq_abs`, and use `norm_inv`
   first when the inverse is outside the cast.
7. `Int.ofNat_div` is `Int.natCast_div`; `Int.ediv_nonpos_of_nonpos_of_nonneg` does not exist
   (use `Int.ediv_le_ediv` against `0`).

## Fidelity note (unchanged, do not lose)

`Erdos67b.IsMultiplicativeOnPositiveInt` has **no coprimality hypothesis** — it is *complete*
multiplicativity, so the dependency's `NonasymptoticLogElliott` is Tao 2016 Thm 1.3 restricted to
completely multiplicative `g₁,g₂`.  The kickoff ratifies that `Prop` as the target, so the target
stands, but `STATUS.md` must describe the headline as the CM case.  The leaf-2 route never uses
complete multiplicativity of the `g_i`, so a genuinely general `NonasymptoticLogElliottMult` is a
cheap stretch goal once the headline lands.
