# Step 1′: the shifted growing-moment criterion 🎯

**COMPLETED 2026-10-26.**  The target module is sorry-free, the headline has only the standard
Lean trust base, and the scoped `lean-green` gate passes.  See
`HANDOFF-2026-10-26-eb-shift-lap1.md`.

**Objective:** make `src/NormalNumbers/CoefmassErdosBorweinShift.lean` sorry-free.  The headline
`ebRandom_ae_normal_of_shiftedVariance_diverges` must be axiom-clean
(`[propext, Classical.choice, Quot.sound]`).

**Do not change** `shiftedVarianceMass` or the headline statement: they are verbatim from the KB
packet.  Helpers go above the headline or in a new `CoefmassErdosBorweinShiftAux.lean`.  No
`native_decide`, no new `axiom`, no edits to existing files except deleting `private` on helpers in
`CoefmassErdosBorweinEndpoint.lean` that you need to reuse.
**NEVER git push:** `research/eb-endpoint` is local only.

## Reuse
Step 1 is PROVED: `ebRandom_ae_normal_of_divisorVariance_diverges` (CoefmassErdosBorweinEndpoint.lean
~1443), with its moment expansion, good-divisor contraction, collision count, Borel–Cantelli along
`N_j = ⌈exp √j⌉` and interpolation.  **Copy and generalize it; do not re-derive.**  The only changes:

1. **Which divisors contract.**  Step 1 uses `d > P₀` with `d ∣ n_i + a₀`.  Now use `d > P₀` with
   `d ∣ n_i + j` for some `j ∈ [j₀, J N]`.  Since `d > P₀ > J N` (eventually), each `d` divides at
   most one of `n_i + 1, …, n_i + K′`.
2. **The angle.**  For `d ∣ n_i + j` with `j < d`: `frac(b^{n_i}/(b^d − 1)) = b^{d−j}/(b^d − 1) =
   b^{−j}(1 + O(b^{−d}))`.  For the other coordinates `i′` with `d ∤ n_{i′} + r` for all `r ≤ K′`,
   the contribution is `≤ 2b^{−K′}`.  So `θ_d = σ_i h b^{−j}(1 + O(b^{−d})) + O(2k|h| b^{−K′})`.
   Choose `j₀` with `b^{j₀} ≥ 2|h|` and `K′ = J + j₀ + ⌈log_b(16k)⌉ + 1`.  Then
   `|h|b^{−j}/4 ≤ ‖θ_d‖ ≤ 1/2`, and `sin²(π θ_d) ≥ 4‖θ_d‖² ≥ h² b^{−2j}/4`.
   So the factor is `≤ exp(−c·h²·b^{−2j}·v_d)`, and the product over good `d` is
   `≤ exp(−c h² Σ_i shiftedVarianceMass … n_i)` on the no-collision event.
3. **Collisions.**  `G = #{(i, i′, j, r, d) : i ≠ i′, j ≤ J, r ≤ K′, d > P₀, d ∣ n_i + j, d ∣ n_{i′} + r}`,
   with `E G ≤ 4k²·J·K′·(3/P₀ + 4/N)`.  Since `J N ≤ log log N` (hypothesis `hJ`) and `P₀ =
   exp((log log N)²)`, the Borel–Cantelli bookkeeping of Step 1 survives with `K` replaced by
   `J·K′ ≤ (log log N)²`-ish.  Recheck every numeric.
4. **Assembly.**  Identical to Step 1.  `φ̃_N := (1/N)Σ exp(−c h² shiftedVarianceMass …) → 0` follows
   from `hdiv b hb j₀ T` (split at `T`).  Then the moment bound, Borel–Cantelli, Weyl.

Degenerate cases (why the binders are as they are): `J N < j₀` gives an empty sum, so `hdiv` fails and
the theorem is vacuous.  `δ ≡ 0` and `δ ≡ 1` give `v ≡ 0`, so again vacuous.

## Order of attack
Restate Step 1's internal lemmas with `a₀` replaced by a window `[j₀, J]`, then follow its proof
order.  Commit each green lemma.
