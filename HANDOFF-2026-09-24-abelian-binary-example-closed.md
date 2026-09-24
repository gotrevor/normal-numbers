# HANDOFF 2026-09-24 — abelian-binary-example lap CLOSED

Branch `wip/g5-prime-subset`.  Scope: `sorry-free:src/NormalNumbers/AbelianBinaryExample.lean`
(KICKOFF-2026-09-23-abelian-binary-example.md).  **Met.**

## Result

`src/NormalNumbers/AbelianBinaryExample.lean` is sorry-free; all three ratified statements are
proved with statements/binders untouched and are axiom-clean
(`propext, Classical.choice, Quot.sound` — no `native_decide`, no `sorryAx`):

* `isAbelianNormalTwo_xiBits`
* `not_isNormalSequence_xiBits`
* `exists_abelianNormal_not_normal`

So there is an explicit infinite binary sequence — `hexSwap` (2→3, 5→4, B→A, C→D) applied to the
base-16 digits of `fullRealW`, read four bits per digit — that is abelian-normal but not normal.

## New files

`src/NormalNumbers/AbelianBlockDensity.lean` — **analytic workhorse.**  `tendsto_blockEvent`: for
base-16 normal `c`, any event determined by (bit position mod 4, the `S` hex digits starting at
`c (n/4)`) has density `#{admissible (r, word) pairs} / (4·16^S)`.  Built from
`tendsto_winCount_wordOf` plus the AP reindexing `n = 4m + r` (`blocks r N = (N - r + 3)/4`,
`card_res_eq_winCount`, `tendsto_blocks_div`), with word↔numeral plumbing (`wordVal`,
`wordOf_wordVal`, `wordVal_wordOf`, `wordOf_injOn`).

`src/NormalNumbers/AbelianIntervalBinomial.lean` — **combinatorial crux**, parametrized by an
arbitrary digit substitution `g` so it does not depend on `hexSwap`.
`HBinom g` := every in-block interval `[r, r+m)` has one-count `2^(4-m)·choose m i` over the 16
hex digits.  `two_pow_mul_wordCount`: `HBinom g → 2^L · wordCount g L r S j = 16^S · choose L j`
for every offset `r < 4` and `r + L ≤ 4S`.  Strong induction on `L`, peeling the leading hex digit
(`sum_split` for `16^(S+1) ≃ 16 × 16^S`, `wordOf_cons`, `onesW_peel`), glued by Chu-Vandermonde
(`Nat.add_choose_eq`, wrapped as `vander`).

## Finite checks (kernel `decide`, not `native_decide`)

* `HBinom hexSwap` — `interval_cases r <;> interval_cases m <;> interval_cases i <;> decide`.
  All 10 in-block intervals are exactly Binomial; that is the whole reason the construction works.
* offset counts for `0011` over the 256 hex pairs: `32, 16, 16, 16` → `80/1024 = 5/64 ≠ 1/16`.

## Not touched

Pre-existing designated-open sorries elsewhere (`MahlerDriftOne.lean:378`,
`PrimeLambertOscillation.lean:94`) are untouched.  `src/NormalNumbers.lean` gained the two new
imports.
