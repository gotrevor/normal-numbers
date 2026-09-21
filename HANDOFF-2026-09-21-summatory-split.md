# HANDOFF 2026-09-21 — the summatory SPLIT lap (`G4SummatorySplit.lean`)

Branch `wip/g5-prime-subset`, HEAD `efedddc`.  Working tree clean, `lake build` green (9108 jobs).
New file `src/NormalNumbers/G4SummatorySplit.lean` (~1500 lines), **pure addition** — no existing
line deleted, no frozen statement touched.

## Result

The file is **sorry-free**; these are all `[propext, Classical.choice, Quot.sound]`:

`isNormal_G4_of_oddNode`, `isNormal_G4_of_shiftSplit`, `sdShiftFree_of_sdOdd`,
`exists_classOmegaSum_zero_bound`, `roughSummatory_of_split`,
`norm_roughClassSum_sub_classOmegaSum`, `shift_cost_small`, `exists_re_sdExponent_le_neg_one`.

Last lap left the G4 window law (off the Chowla sector) resting on ONE node, `RoughSummatory h`.
This lap **peels that node down to its two genuinely different halves**:

```
isNormal_G4_of_oddNode :
    (∀ h ≠ 0 off Chowla, RoughSummatoryPrefix h)   -- OPEN.  the crux.
  → (∀ h ≠ 0 off Chowla, SDOdd h)                  -- CLASSICAL (Tenenbaum II.5.3).
  → (Chowla sector WindowDecay) → SiteDecayFull
  → IsNormal 4 (primeLambertAtBase 4)
```

* `RoughSummatoryPrefix h` — Selberg–Delange for `Σ_{m<M} ∏_{j=1}^{k} z_j^{ω_{>2}(m+j)}`: a
  correlation of `k` multiplicative functions at `k` DISTINCT SHIFTS, uniformly for `k ≤ windowJ M`.
* `SDOdd h` — LSD for the single function `n ↦ z_k^{ω_{>2}(n)}`, **no shift, ODD arguments only**,
  for `k ≤ windowJ X + 2`.

Everything between the old node and that primitive object is now machine-checked: shift removal,
the parity classes, the 2-adic decomposition, and the window-range bookkeeping.

## What was proved, in dependency order

1. **Shift removal** (`norm_roughClassSum_sub_classOmegaSum`): reindex `n = m+k`; the two boundary
   blocks `[0,k) ∪ [M,M+k)` cost `2k`.  `shift_cost_small` shows that is below the node's own
   `C 4^{-k} M (log M)^{Re κ−1}` budget, because `k ≤ windowJ M` forces `2k·4^k ≤ 64 (log M)^3`
   (`two_mul_pow_four_le`) and `(log M)^{Re κ_k} ≥ (log M)^{−⌈4π|h|⌉}`.
2. **The split** (`roughSummatory_of_split`): `RoughSummatoryPrefix + SDShiftFree → RoughSummatory`.
   Constants glued by `combinedConst` (indexed by `s.sup id`; `Icc 1 1 = {1}` forces the `k=1`
   singleton to be served by the prefix clause, hence the singleton sub-node only needs `k ≥ 2`).
3. **Halving is exact** (`classOmegaSum_zero_eq`): `ω_{>2}` is blind to the factor 2, so `n ↦ n/2` is
   a bijection from the even residues below `M` onto ALL residues below `⌈M/2⌉`:
   `E(M) = E(⌈M/2⌉) + O(⌈M/2⌉)`, unrolled by `classOmegaSum_zero_unroll`.
4. **The 2-adic assembly** (`exists_classOmegaSum_zero_bound`), at depth
   `halfDepth M = 10 log₂ log₂ M`, in three pieces:
   * `main_sum_diff` — the `V` main terms collapse onto one, error
     `(‖c‖/2)(log M)^{Re κ}(4‖κ‖(log2/log M)(2M+V²) + (M2^{-V}+V))`.  The identity
     `Σ_{v≥1} 2^{-v} = 1` is where the **equal-constants-on-both-parity-classes clause gets
     DERIVED** — the previous handoff flagged it as "consistent, not sharply tested"; it is now a
     theorem, not a hypothesis.
   * `err_sum_le` — `Σ_v A/log M_v (M_v (log M_v)^r) ≤ 4A/log M (M+V)(log M)^r` for `r ∈ [−2,0]`.
   * `norm_classOmegaSum_le` — the remainder `‖E(M_V)‖ ≤ M_V`.
   All three dominated through ONE interface, `budget_lower`:
   `M/(64 (log M)^6) ≤ (1/4)^k/log M · (M (log M)^{Re κ})` on the whole window range.
   `eventually_assembly` supplies the side conditions; `windowJ_halfIter` is the range check that
   `SDOdd`'s `+2` pays for (the true loss is only `+1`).

## Crux progress: one route REFUTED, with the reason

`exists_re_sdExponent_le_neg_one` (proved): for `h ≠ 0` there is `t ≥ 1` with
`Re (sdExponent h (Icc 1 k)) ≤ −1` for all `k ≥ t` — at the first site `j` with `4^j ∤ h`, `e(h/4^j)`
is a quarter or half turn, so `Re(e(h/4^j)−1) ≤ −1`; all other sites contribute `≤ 0`.

Consequence: the prefix main term is `≤ M/log M`, so the node's budget is `≤ C M (log M)^{-2}`.
**Pointwise truncation of the shift product is therefore refuted for every `j₀`**: truncating at
`j₀ ≤ windowJ M` costs `≍ M (log log M) 4^{-j₀} ≥ M (log log M)/(4 (log₂ M)²)`, over budget by a
factor `log log M`.  The loss is intrinsic — the truncation error is measured against `M` while the
budget is measured against the much smaller main term `M (log M)^{Re κ}`.
**Standing constraint: any future attack must keep the tail sites INSIDE the main term.**

## Next lap

1. **The crux is `RoughSummatoryPrefix h`.**  It is the joint distribution of `ω_{>2}(m+1),…,
   ω_{>2}(m+k)` being asymptotically independent Poisson, with SD-strength error `O(1/log M)`
   uniformly for `k ≤ log₂log₂M + 1`.  For `k ≥ 3` even the fixed-`k` asymptotic is open territory
   (ternary shifted divisor).  Narrow it; do not expect to clear it.  Two concrete probes:
   * *Range reduction.*  Where does `k ≤ windowJ M` come from upstream?  If the G₄ wiring can be run
     with `k ≤ K` FIXED, the crux becomes a fixed-`k` shifted correlation — `k = 2` is
     Ingham/Estermann and genuinely known.  This is a question about `G4WiringCRT`/`G4WiringRough`,
     not about the node.  **Check this first; it is the only visible route that changes the class of
     the problem.**
   * *Keep the tail inside the main term.*  Per the refutation above: instead of discarding sites
     `j > j₀`, absorb them into the Dirichlet series, i.e. state the node for the full Euler product
     `∏_{j} (1 + (z_j−1)/p + …)` and let the `j`-tail perturb the singularity exponent rather than
     the summand.
2. `SDOdd h` is classical but NOT in mathlib (no Selberg–Delange, no Landau's theorem).  Formalizing
   it is a multi-lap project of its own; it is honest to leave it frozen while the crux is open.
3. Optional: the numerical probe of `SDOdd`'s equal-constant clause is no longer needed for the
   EVEN/ODD comparison (that is now derived), but `RoughSummatoryPrefix` asserts equal constants on
   the two classes for the PREFIX sums, and that is still only probe-level evidence.
