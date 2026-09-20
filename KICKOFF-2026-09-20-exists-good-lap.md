# KICKOFF 2026-09-20 — `exists_good`: the explicit block schedule (FIRED 2026-09-20 00:50 EDT; DONE 01:40, see HANDOFF-2026-09-20-exists-good.md - the lap found `Good.sep` unsatisfiable at i=0 and added `1 ≤ i`)

Branch `wip/g5-prime-subset`.  Engine Opus/low.  Design: `DESIGN-2026-09-19-bcr-wiring.md` §5 ("`exists_good`,
explicit").  Goal: `src/NormalNumbers/G4WiringSparse.lean` **sorry-free**.  Its only sorry is
`exists_good (C) (hgrow : Tendsto (fun k => Real.log (C k) / 4 ^ k) atTop (𝓝 0)) : ∃ D : BlockData, D.Good C`.
Everything it needs is proved above it: `exists_block (y) (hy : 1 ≤ y) (δ) (hδ : 0 < δ)` (a block of primes
`> y` with `δ ≤ ∑ 1/p ≤ δ + 1/y`), `divergentRecip`, `blockIndex_*`.  **Never change the statements of
`exists_good`, `BlockData`, `BlockData.Good`, `KMT_quant`, `exists_sparse_normal_of_KMT_quant'`.**

## The construction (the theorem's docstring is authoritative)

`φ(J) := max(1, max_{J'≤J} log C J')`; `Jᵢ := max{J ≤ ⌊log i⌋ : 4φ(J) + 4J ≤ log i}` (`Nat.findGreatest`;
0 when empty — the fields only matter eventually); `εᵢ := 1/(8 Jᵢ² log i)`; `Bᵢ := exists_block (y := xᵢ)
(δ := 1/(i+1))` (choose); `xᵢ₊₁ := max(max Bᵢ, 2xᵢ, (xᵢ+1)^{⌈1/εᵢ₊₁⌉}, ⌈exp exp(8Jᵢ₊₁² log(i+1))⌉)`, `x₀ := 1`.
⚠️ Small `i`: `log i ≤ 0` for `i ≤ 1`, so `εᵢ` as written is not in `(0, 1/2)` there.  The `Good` fields
`ε_range`, `sep`, `x_double` are stated for **all** `i`; pick an offset (e.g. `log (i+3)` everywhere, or
`ε_i := 1/(8 (Jᵢ+1)² log(i+3))`) so every field holds for all `i`, and say what you chose in the handoff.
The proofs below are unchanged by a constant offset.

## Leaves, in order (commit a compiling skeleton with these as named `sorry`s FIRST)

1. `sched_J`: the definition of `Jᵢ`, plus `J_tendsto : Tendsto J atTop atTop`, `C_J_le : C (J i) ≤ i^{1/4}`
   eventually, and `log_o_pow : Tendsto (fun i => Real.log i / 4 ^ J i) atTop (𝓝 0)` (by maximality,
   `4φ(Jᵢ+1) + 4(Jᵢ+1) > log i`, and `φ(J+1) = o(4^J)` from `hgrow`).
2. `build`: the `Nat.rec` producing `⟨xᵢ, Bᵢ⟩` from `exists_block` (`Classical.choose`), with the
   `BlockData` obligations `x_mono` (`xᵢ₊₁ ≥ 2xᵢ > xᵢ`) and `B_prime` (`exists_block` gives `xᵢ < p`;
   `p ≤ xᵢ₊₁` from `max Bᵢ ≤ xᵢ₊₁`).
3. `δ_div`: `δᵢ ≥ 1/(i+1)`, harmonic divergence (`Real.not_summable_one_div_natCast`).
4. `ε_range`, `sep`, `x_double`: `N > xᵢ ≥ exp exp(8Jᵢ² log i)` gives `log log N > 8Jᵢ² log i`;
   `N^{εᵢ} ≥ ((xᵢ₋₁+1)^{⌈1/εᵢ⌉})^{εᵢ} ≥ xᵢ₋₁ + 1`; `x_double` is by construction.
5. `terms`: `δᵢ₋₁ + δᵢ ≤ 2/i + 2/xᵢ₋₁ ≤ 3/i`; `log(1/εᵢ) ≤ log(8 (log i)³)` since `Jᵢ ≤ log i`;
   `C(Jᵢ) ≤ i^{1/4}`; `exp(−∑_{i'<i−1} δᵢ') ≤ exp(1 − log(i−1))`; `exp(−1/(8Jᵢ²εᵢ)) = 1/i`.
   Each of the three products is `≤ i^{1/4} · polylog(i) · i^{−1/2}` → 0.
6. `tail`: `∑_{i'<i+2} δᵢ' ≤ log(i+2) + 3`, then leaf 1's `log_o_pow`.
7. Assemble `exists_good`; then `#print axioms NormalNumbers.G4Sparse.exists_sparse_normal_of_KMT_quant'`
   must show no `sorryAx`.  `box done --green` only then.

Report the advance, not the sorry count: a skeleton with named leaves committed is progress.  If a leaf
costs more than ~40 minutes, commit what compiles with the leaf as a named sorry and say which one.
