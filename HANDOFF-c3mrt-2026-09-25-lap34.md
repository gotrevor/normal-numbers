# HANDOFF c3-mrt 2026-09-25 — lap 34: the `K`-point input, named and located

**Branch** `wip/c3-mrt`.  Both targets green: `lake build` (9257 jobs) and
`lake build NormalNumbers.C3MrtKPoint` (the new chain tip — it imports
`C3MrtArchimedean`, so building it covers the whole `C3Mrt*` chain).
Prior baton: `HANDOFF-c3mrt-2026-09-25-lap33.md`.

## The route-decisive fact settled this lap

`Erdos67b.NonasymptoticLogElliott` (`.lake/.../Erdos67b/LogElliott.lean:411`) is **strictly
two-point**: two multiplicative functions along two affine forms, non-pretentiousness required
only of the first.  So it can never serve the `D ≥ 3` rung of `ConjC3`.  Read, verified, and now
formalised.

## New module `src/NormalNumbers/C3MrtKPoint.lean` (all sorry-free, trust-triple)

| name | content |
|---|---|
| `kPointLogCorrelation` | `∑_{X/W<n≤X} n⁻¹ ∏_{i<K} g_i(a_i n + b_i)` — the dependency's window and weight, `K` factors |
| `NondegenerateForms` | `0 < a i`, and `a i · b j ≠ a j · b i` for `i ≠ j` |
| `KPointLogElliott K` | the `K`-point conjecture in the dependency's *exact* nonasymptotic shape (same `A₀`/`A ≤ W ≤ X` quantifier block, same `pretentiousDistSqToTwist` hypothesis on the first factor only) |
| `kPointLogElliott_two_iff` | **`KPointLogElliott 2 ↔ Erdos67b.NonasymptoticLogElliott`** — faithfulness: our generalisation really specialises to the dependency's bet, so lap 33's `D = 2` rung *is* the `K = 2` case |
| `kPointLogElliott_of_succ` | **`KPointLogElliott (K+2) → KPointLogElliott (K+1)`** — pad with the constant `1` along `n + B`, `B = ∑|b i| + 1` (nondegenerate against every `a i n + b i` because `a i ≥ 1`); admissible because the non-pretentiousness hypothesis binds only the first factor |
| `nonasymptoticLogElliott_of_kPointLogElliott_three` | `KPointLogElliott 3 → NonasymptoticLogElliott` |

## What this buys

The named-input ledger for `ConjC3` is now fully explicit and **stratified**:

* `D = 1`: PROVED outright (`depthAvg_one_tendsto`, Delange).
* `D = 2`: proved modulo `KPointLogElliott 2` (= the dependency's own bet) + Vinogradov–Korobov.
* `D = k`: needs `KPointLogElliott k`, which by `kPointLogElliott_of_succ` is **strictly at least
  as strong** as everything below it.  `KPointLogElliott 0` is false (empty product ⇒ the
  correlation is the full log mass `≍ log W`), which is why the step is stated from `K + 2`.

So the crux's remaining distance is no longer "quantitative Elliott, somehow": it is exactly
`KPointLogElliott k` uniformly for `k ≍ log log log N`, plus the quantitative rate
(`QuantDepthElliott`).  That is the honest equivalence.

## NEXT

1. **The uniform-in-`K` statement.**  `QuantDepthElliott` needs `KPointLogElliott k` with the
   `A₀` and the decay *uniform* in `k` up to `≍ log log log N`.  State that as
   `UniformKPointLogElliott` and prove `QuantDepthElliott ⇐ UniformKPointLogElliott`-shaped
   reduction — i.e. redo laps 23–33's two-shift assembly with `K` shifts.  The `D`-shift
   analogues of `sum_pow_omega_two_shift_eq_coprime`, `two_shift_truncation_bound`,
   `inner_pair_bound`, `full_sum_bound` are all `Finset.prod`-over-`Fin K` generalisations of
   proved lemmas; the only genuinely new bookkeeping is pairwise coprimality of `K` powerful
   moduli and the `K`-fold CRT.
2. Cheaper first step on that path: `sum_pow_omega_shift_eq` for `K` shifts (the bridge
   expansion) — no analysis, pure Dirichlet convolution over `Fin K`.
3. Literature check worth one `WebSearch`: whether Tao–Teräväinen's odd-order log-Elliott gives
   `KPointLogElliott k` for odd `k` under the *unimodular* (not just `±1`) hypothesis, and with
   what uniformity in `k`.  If it does for odd `k` only, the schedule can be restricted to odd
   depths, which costs nothing (`D_N` is ours to choose).

## Still refuted — DO NOT RETRY

Unchanged from lap 32/33's lists.  Do not attack `TwistedPrimeSumSaving`.

## Confidence

* `KPointLogElliott` faithful to the dependency at `K = 2`: **proved in-kernel** (an `iff`).
* `D = k` rung reachable from `KPointLogElliott k` by generalising laps 23–33: ≈ 60%
  (mechanical, but a lot of `Fin K` bookkeeping).
* leaf TRUE ≈ 95%; leaf PROVABLE with known techniques ≈ 15% (unchanged).
