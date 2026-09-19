# KICKOFF 2026-09-19 — W4: dyadic means → prefix means, one lap (PREPARED, not fired)

Design: `DESIGN-2026-09-19-bcr-wiring.md` §2 row W4.  Branch `wip/g5-prime-subset`.  Engine Opus/low.

## The one target — statement FROZEN, name guarded

`src/NormalNumbers/DyadicToPrefix.lean`, `NormalNumbers.prefixMean_tendsto_zero_of_dyadic`:
bounded `F : ℕ → ℂ` with `dyadicMean F N = (∑_{N≤n<2N} F n)/N → 0` as `N → ∞` (all `N`, not only
powers of two) has `prefixMean F n = (∑_{k<n} F k)/n → 0`.

## Route
1. `sum_range_eq_head_add_blocks`: for `m`, `∑_{k<n} F k = ∑_{k < ⌊n/2^m⌋} F k + ∑_{i<m} ∑_{k ∈ Ico ⌊n/2^{i+1}⌋ ⌊n/2^i⌋} F k`
   (telescoping over `Finset.range`/`Ico` with `Nat.div_div_eq_div_mul`).
2. `block_vs_dyadic`: `‖∑_{k ∈ Ico ⌊n/2^{i+1}⌋ ⌊n/2^i⌋} F k − ∑_{k ∈ Ico N (2N)} F k‖ ≤ C` with `N = ⌊n/2^{i+1}⌋`
   (the two ranges differ by at most one endpoint since `⌊n/2^i⌋ ∈ {2N, 2N+1}`).
3. Assemble: given `ε`, pick `m` with `C 2^{-m} < ε/3`; pick `N₀` from `hD` at `ε/(3·2)` (each block
   contributes `N‖dyadicMean F N‖ ≤ N ε/6` and `∑_i N_i ≤ n`), then `n` large so every `⌊n/2^{i+1}⌋ ≥ N₀`
   for `i < m` and `m C / n < ε/3`.

## Rules
Report the advance; `native_decide`/deprecations fine; `box done --green` when sorry-free; nothing else in scope.
