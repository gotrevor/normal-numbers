# HANDOFF c3-mrt 2026-09-25 — SESSION WRAP (laps 40–42)

**Branch** `wip/c3-mrt` · **HEAD** `b03fe8f` · working tree **clean** · both build targets green
at every commit.  Read `DIRECTION.md` → **CURRENT DIRECTIVE** first — it OUTRANKS this file and
was rewritten by lap 40 (an altitude lap).  Per-lap detail: `HANDOFF-c3mrt-2026-09-25-lap40.md`
(with the lap-41 and lap-42 addenda appended).  Earlier: `-session-wrap-laps33-39.md`,
`-lap32.md` (20–32), `-lap18/19/21.md`, `-session-wrap.md` (1–6), `-lap8.md`.

## BUILD HYGIENE — read before claiming green

`src/NormalNumbers.lean` does **not** import the `C3Mrt*` chain (the directive forbids importing
a `lean-proofs-latest` consumer into the `NormalNumbers` root), so a bare `lake build` and the
pre-commit hook do **not** typecheck any `C3Mrt*` module.  Always run BOTH:

    lake build                             # 9257 jobs
    lake build NormalNumbers.C3MrtBudget   # 8978 jobs — THE CHAIN TIP (changed this session)

The tip moved from `C3MrtMultiForms` to `C3MrtBudget`, which now imports
`C3MrtSchedule` + `C3MrtMultiMass`; the chain is
`… → C3MrtMultiForms → C3MrtMultiLinear → C3MrtMultiMass → C3MrtBudget`.

## The crux is untouched

`weylLambertTwist_holds` (`SwingC3Leaf.lean`) unchanged — still the only campaign `sorry` in
`src/`, still what `conjC3_via_weylLambert` carries `sorryAx` through.  `QuantDepthElliott` was
NOT edited; the new `Prop` sits beside it.  This session is pure addition: 3 new files, 20 new
declarations, every one `[propext, Classical.choice, Quot.sound]`.

## Session result — the route survived its one structural risk, and the target is now sharp

**Lap 40 (review lap) found a defect in the reduction's own `Prop`.**  Lap 37's
`prod_le_lcm_mul_pow` puts a factor `K^{K²}` into the `K`-fold rung, and `QuantDepthElliott`'s
`b^{κD}` budget cannot pay for it: with `v = log log log N`, `D_N ≍ v`, so
`D_N^{D_N²} = exp(Θ(v² log v))` while `(log log N)^m = exp(m v)`.  The lap-39 handoff's
"`K^{K²}` is `(log log N)^{o(1)}`" is arithmetically **wrong**, and until lap 40 the whole
`D ≥ 3` assembly was aimed at a statement that could not receive it.  That was the one open
obligation whose failure would have forced a redesign, so it went first.

| lap | file | what landed |
|---|---|---|
| 40 | `C3MrtBudget.lean` | `QuantDepthElliottGen` (free budget `C`, decay clause = joint vanishing `C(depthLL b N)·η N → 0`); `weylLambertTwist_of_quantDepthElliottGen`; `quantDepthElliottGen_of_quantDepthElliott` (old ⟹ new — **nothing weakened**); `tIdx`/`tendsto_tIdx`; `depthLL_le_triple_log`/`depthLL_le_tIdx` (`D_N ≤ 2t_N+2`, uniform in `b ≥ 2`); `log_log_ge_triple_log` (`log log N ≥ (2^{t_N}−2)log 2`); `eventually_cube_le_pow_two`; `budget_absorb`; **`budget_absorb_of_tIdx`** (the sharp form); `pow_self_sq_le_exp_cube`; `kfold_budget_le_exp_cube`; **`weylLambertTwist_of_kfold_bound`** (the campaign's new endpoint) |
| 41 | `C3MrtMultiLinear.lean` | **`inner_sum_multi_forms`** — the `K`-fold `inner_sum_linear_forms`, with **no coprimality anywhere**; `inner_sum_multi_empty`; `univLcm_pos`, `shift_div_eq_linear_multi`, `joint_base_mod` |
| 42 | `C3MrtMultiMass.lean` | **`joint_multi_harmonic_mass`** — the `K`-point joint mass with BOTH gains; `joint_class_range` (pays part of lap 38's indexing debt) |

### The sharp ledger entry (lap 40's real product)

> the `K`-point log-Elliott saving must beat every power of `log log N`,
> by a quasi-polynomial margin in `log log log N`.

Precisely: with `t_N = ⌊log₂(⌊log₂⌊log₂N⌋⌋+1)⌋ ≍ log log log N`, a budget `exp(c(D+1)³)` — which
covers `K^{K²}` and also the `exp(Θ(K²))` the expansion costs intrinsically — is absorbed by
`η N ≤ exp(−t_N⁴)`.  That is strictly stronger than `(log log N)^{-m} = exp(−m t_N log 2 + O(1))`
for every fixed `m`, but only quasi-polynomially so.  **Mechanism**: the schedule's depth is
LINEAR in `t_N`, `log log N` is EXPONENTIAL in it.  Published `(log log X)^{-c}` rates therefore
fall *just* short, and nothing stronger than that margin is needed.  The `(log N)^{-a}` decay of
`budget_absorb` is what the `D = 1` rung actually has (Selberg–Delange) and what
`probes/swingc3_weyl_lambert_twist.py` measures for the leaf (`a ≈ 1.3–3.7`).

### The new endpoint

`weylLambertTwist_of_kfold_bound`: if for every twist the assembly delivers

    ‖depthAvg b P Q j h D N‖ ≤ A₀·D^{D²}·b^{κD}·η N ,   η N ≤ A(log N)^{-a},  a > 0,

then `WeylLambertTwist b` holds.  That is the shape laps 36–42 are producing.  Aim everything at
it.

## `K`-fold assembly scoreboard (the directive's item 4)

| step | status |
|---|---|
| 1. `inner_sum_linear_forms` at `K` points | **DONE lap 41** (`inner_sum_multi_forms`) |
| 2. `multi_truncation_bound` | **quantitative heart DONE lap 42** (`joint_multi_harmonic_mass`); the telescope itself remains |
| 3. lap 38's `Fin K` / `Finset.univ.lcm` indexing debt | **partly paid** (`joint_class_range`); the `prod_div_lcm_le` / `tuple_mass_le` restatement remains |
| 4. per-tuple rung bound + ε-chase | not started |
| 5. widen the budget | **DONE lap 40** |

## NEXT — resume here

1. **The truncation telescope** (finishes step 2).  Induct on `K` peeling the **LAST** shift (as
   `sum_pow_omega_multi_eq` does — and note `F` **must** be quantified inside the induction,
   lap 36's gotcha).  At stage `m` feed `joint_multi_harmonic_mass` as
   `offset_truncation_bound_of_mass`'s `hmass`, with the block `d_s ∣ n+m+s+1` (`s < K−m`) that
   the already-peeled shifts impose.  Target:

       Err ≤ ∑_{m<K} [ (m+1)·∏_{j>m} sqfWPartial z_j Y
                       + (1+log N)·K^{K²}·∏_{j>m} sqfWMass z_j ] · bridgeTail z_m Y .

   Model: `two_shift_truncation_bound` (`C3MrtTwoShift`), the `K = 2` case.
2. Finish step 3: restate `prod_div_lcm_le` / `tuple_mass_le` over `Finset.univ` (`Fin K`) via
   the `ℕ → ℕ` extension; `Fin.prod_univ_eq_prod_range` is the bridge for the products.
3. Step 4: per-tuple rung bound + ε-chase, mirroring laps 29–33, landing in
   `weylLambertTwist_of_kfold_bound`'s shape.

## Still refuted — DO NOT RETRY

Everything in `-session-wrap-laps33-39.md`, plus, new this session:

* the lap-39 estimate "`K^{K²}` is `(log log N)^{o(1)}`" — **false** (lap 40);
* hoping a `(log log N)^{-c}` decay suffices — it does not (lap 40);
* **sharpening `prod_le_lcm_mul_pow`'s exponent.**  `gcd(d_i,d_j)` divides `j−i` AND is itself
  powerful, so splitting by gcd pattern replaces `∏_{i<j}(j−i) ≈ K^{K²/2}` by
  `∏_{i<j}∑_{g powerful, g∣j−i}1/g ≤ ∏_p(1+2/p²)^{K²/2}` — still `exp(Θ(K²))`, because a
  positive proportion of the `K²/2` differences are divisible by a square.  The constant is
  `exp(Θ(K²))` INTRINSICALLY; improving lap 37 cannot change the required decay class;
* **bounding the joint mass by one congruence** in the truncation telescope (lap 42): it makes
  the stage-`m` error carry `∏_{j>m} sqfWPartial z_j Y ≍ Y^{(K−m−1)/2}` against a
  `bridgeTail ≍ Y^{−1/2}`, which DIVERGES for `K−m ≥ 3`.  Always use the full joint modulus;
* worrying about coprimality anywhere in the `K ≥ 3` route — laps 37/39/41 close it end to end.

## Confidence

* `D = 2` rung on two named inputs: **done, in-kernel**.
* `K ≥ 3` assembly completable: ≈ 88% (the budget obstruction and the truncation-divergence
  trap, the two structural risks, are both discharged; what remains is bookkeeping of a shape
  already executed once at `K = 2`).
* leaf TRUE ≈ 97%.
* leaf PROVABLE with known techniques ≈ 22% (down from 28% at session start: the required decay
  is now known precisely and sits a quasi-polynomial margin beyond the best published `k`-point
  rates — previously that margin was unmeasured and tacitly assumed favourable).
