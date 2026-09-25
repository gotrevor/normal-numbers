# HANDOFF c3-mrt 2026-09-25 — lap 40 (REVIEW LAP: the budget is repaired)

**Branch** `wip/c3-mrt` · both build targets green · read `DIRECTION.md` → CURRENT DIRECTIVE
first (it OUTRANKS this file; it was rewritten this lap).

## Build hygiene

`src/NormalNumbers.lean` does not import the `C3Mrt*` chain, so a bare `lake build` does not
typecheck it.  Run BOTH:

    lake build                                # 9257 jobs
    lake build NormalNumbers.C3MrtBudget      # 8976 jobs — the C3Mrt chain tip (new this lap)

`C3MrtBudget.lean` now imports `C3MrtMultiForms` as well as `C3MrtSchedule`, so it is the single
tip of the whole `C3Mrt*` chain.  (It is therefore a `lean-proofs-latest` consumer; it is NOT
imported by the `NormalNumbers` root, as the kickoff requires.)

## The crux is untouched

`weylLambertTwist_holds` (`SwingC3Leaf.lean`) unchanged — the only campaign `sorry` in `src/`.
No existing statement was weakened, renamed or edited; `QuantDepthElliott` is left exactly as it
was and the new `Prop` sits beside it.  Pure addition: one new file, 13 declarations, all
`[propext, Classical.choice, Quot.sound]`.

## What this lap found — a defect in the reduction's own `Prop`

Lap 37's `prod_le_lcm_mul_pow` puts a factor `K^{K²}` into the `K`-fold rung.
`QuantDepthElliott` allows only a `b^{κD}` budget and asks `η` to beat every power of
`llProxy ≍ log log N`.  **That cannot pay for it.**  With `v = log log log N`:

    D_N ≍ v ,   D_N^{D_N²} = exp(Θ(v² log v)) ,   (log log N)^m = exp(m v) ,   v² log v ≫ m v .

So the lap-39 handoff's "`K^{K²}` is `(log log N)^{o(1)}`" is **wrong**, and until this lap the
whole `D ≥ 3` assembly was aimed at a `Prop` that could not receive it.  This was the one open
obligation whose failure would have forced a redesign, which is why it was taken first.

## What landed — `src/NormalNumbers/C3MrtBudget.lean`

| declaration | content |
|---|---|
| `QuantDepthElliottGen b` | free budget `C : ℕ → ℝ`; decay clause is the JOINT vanishing `C(depthLL b N)·η N → 0` |
| `weylLambertTwist_of_quantDepthElliottGen` | the widened `Prop` still closes the crux |
| `quantDepthElliottGen_of_quantDepthElliott` | old ⟹ new: **nothing weakened**, every ledger row survives |
| `tIdx`, `tendsto_tIdx` | `t_N = ⌊log₂(⌊log₂⌊log₂ N⌋⌋+1)⌋ ≍ log log log N` |
| `depthLL_le_triple_log` / `depthLL_le_tIdx` | `D_N ≤ 2t_N + 2`, uniform in `b ≥ 2` (`Nat.log b ≤ Nat.log 2`) |
| `log_log_ge_triple_log` | `log log N ≥ (2^{t_N} − 2)·log 2` |
| `eventually_cube_le_pow_two` | `c(2t+3)³ ≤ ε·2^t` eventually |
| `budget_absorb` | `C D ≤ exp(c(D+1)³)` × `η N ≤ A(log N)^{-a}` ⟹ joint vanishing |
| `budget_absorb_of_tIdx` | **the sharp form**: the decay needed is only `η N ≤ exp(−t_N⁴)` |
| `pow_self_sq_le_exp_cube` | `K^{K²} ≤ exp(K³)` |
| `kfold_budget_le_exp_cube` | `A₀·K^{K²}·b^{κK} ≤ exp((log A₀ + 1 + κ log b)(K+1)³)` |
| `weylLambertTwist_of_kfold_bound` | **the campaign's new endpoint** (see below) |

**The mechanism in one line.**  The schedule's depth is LINEAR in `t_N`; `log log N` is
EXPONENTIAL in `t_N`.  So a budget that is any fixed polynomial in `D` is absorbed by a decay
that is any fixed polynomial in `t_N` inside an exponential.

## The sharp ledger entry this produces

    the K-point log-Elliott saving must beat every power of log log N,
    by a quasi-polynomial margin in log log log N.

Precisely: `η N ≤ exp(−(log log log N)⁴)` suffices; `(log log N)^{-m} = exp(−m t_N log 2 + O(1))`
does not.  Quantitative log-Chowla/Elliott results of `(log log X)^{-c}` shape therefore fall
**just** short — and nothing stronger than that margin is needed.  The `(log N)^{-a}` decay of
`budget_absorb` is what the `D = 1` rung actually has (Selberg–Delange) and what
`probes/swingc3_weyl_lambert_twist.py` measures for the leaf (`a ≈ 1.3–3.7`).

## The new endpoint

`weylLambertTwist_of_kfold_bound`: if for every twist the assembly delivers

    ‖depthAvg b P Q j h D N‖ ≤ A₀·D^{D²}·b^{κD}·η N ,   η N ≤ A(log N)^{-a},  a > 0,

then `WeylLambertTwist b` holds.  That is the shape laps 36–39 are producing; aim steps 1–4
below at it.

## NEXT — resume here

1. `inner_sum_linear_forms` analogue at `K` points: reindex `n = L·k + a` (from
   `joint_class_multi`), so `(n+i+1)/d_i = (L/d_i)k + (a+i+1)/d_i`; `filter_linear_lt_eq_range`
   then applies verbatim with `L` for `d·e`.
2. `multi_truncation_bound`: iterate `offset_truncation_bound_of_mass` `K` times; the error
   telescopes to `≤ ∑_{i<K}(∏_{j<i} sqfWMass z_j)(1 + log(N+K))·bridgeTail z_i Y`.
3. Pay lap 38's indexing debt: standardise on `Fin K` + `Finset.univ.lcm`.
4. Per-tuple rung bound + ε-chase, mirroring laps 29–33, landing in
   `weylLambertTwist_of_kfold_bound`'s shape.

## Still refuted — DO NOT RETRY

Everything in the lap-39 session wrap, plus, new this lap:

* **the lap-39 estimate "`K^{K²}` is `(log log N)^{o(1)}`"** — false, see above;
* **hoping a `(log log N)^{-c}` decay suffices** — it does not, by the same computation;
* **sharpening `prod_le_lcm_mul_pow`'s exponent.**  `gcd(d_i,d_j)` divides `j−i` AND is itself
  powerful (both `d_i,d_j` are, so every gcd exponent is `≥ 2`).  Splitting the tuple sum by the
  pairwise-gcd pattern replaces `∏_{i<j}(j−i) ≈ K^{K²/2}` by
  `∏_{i<j}∑_{g powerful, g ∣ j−i} 1/g ≤ ∏_p(1+2/p²)^{K²/2}` — still `exp(Θ(K²))`, because a
  positive proportion of the `K²/2` differences are divisible by a square.  So the constant is
  `exp(Θ(K²))` INTRINSICALLY, and improving lap 37 is worth at most a constant in the exponent
  and cannot change the required decay class.

## Confidence

* `D = 2` rung on two named inputs: **done, in-kernel**.
* `K ≥ 3` assembly completable: ≈ 85% (the budget obstruction, the only structural risk that
  could have killed the route, is now discharged in-kernel).
* leaf TRUE ≈ 97%.
* leaf PROVABLE with known techniques ≈ 22% (down from 28%: the required decay is now known
  precisely, and it is a quasi-polynomial margin beyond the best published `k`-point rates —
  previously this margin was unmeasured and assumed favourable).
