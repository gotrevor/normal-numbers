# HANDOFF — objective A0, the decisive probe: **VERDICT NO**, and the obstruction is a theorem

**Branch** `wip/g4-entropy`.  `lake build` 🟢 **8996 jobs**.  New module
`src/NormalNumbers/G4EntropyXCeiling.lean`, sorry-free, every endpoint
`[propext, Classical.choice, Quot.sound]`.

## The question

> Does the E0 chain hold for every `X ≥ Sched.X K` at fixed `K`?

## The audit

`X` enters `G4EntropyE0.entropy_gt_of_budget` — the whole structural content of E0 — through
**exactly one field of `gridFrame`**: `P := apSample X G.P₀ G.b₀`.  Everything else the frame
carries (`θ`, `γ`, `S`, `A`, `d`, `t`, `η`, `ε`, `D`, hence `goodSets`, `pieceCube`, `res`, and
the cover sum `∑_{G'} η^{|G'|} vol(pieceCube G')`) is literally `X`-free, and so is E0's target
`M = k₄·(K²+1)^K`.  Therefore the only `X`-sensitive hypotheses are `hX`, `PropC`, `PropD`.
Unwinding those through `ScheduleWitness` gives five terms:

| # | declaration / field | the inequality | monotone in `X`? |
|---|---|---|---|
| 1 | `ScheduleWitness.hne`, `entropy_gt_of_budget`'s `hX` | `G.b₀ < X` | **YES** |
| 2 | `hbudget` / `G4Frame.smallPrimeBound` (`PropC`'s `δ₃`) | `…·2R^{Mc}/Psz`, `2(2e/Mc)^{Mc}(#sm)^{Mc}·2R^{Mc}/Psz`, `Psz = |apSample X P₀ b₀|` | **YES** (`Sched.card_apSample_ge_half`: `|P| ≥ X/2P₀` grows) |
| 3 | `ScheduleWitness.hbig`, second summand | `2Y²·(2^{−K}/3)²/|P|` | **YES** |
| 4 | `ScheduleWitness.hbig`, third summand (via `hMx`) | `(log Mx / log Y)·(1/2)^K/3 ≤ δbig·εη`, with `hMx` forcing `Mx ≥ X − P₀` | **NO** — see below |
| 5 | `ScheduleWitness.hfar` / `G4FarTail.farC` | `farC G X Dm = log((X+Dm)/|P|) + log(log(X+Dm)+1)` | **NO**, but slack `4^{−(K+N)}`, `N = 100K²`: the cap is `log log X ≲ 4^{100K²}`, i.e. `X ≲ 2^{2^{2^{200K²}}}` — never binding |

Row 1 is the only place the schedule's `Sched.X K` numeral is used at all in the E0 *statement*;
rows 2–3 improve with `X`; rows 4–5 are ceilings, and **row 4 binds**.

## Verdict: **NO.**  The named estimate is row 4

`NormalNumbers.G4.Sched.log_Mx_div_le` (`G4ScheduleBig.lean:148`) discharging the third summand
of `ScheduleWitness.hbig`.  Mathematically it is not an artifact: `log Mx / log Y` is the number
of prime factors `> Y` a sample point can have, and a larger sample simply has more of them.

The obstruction is now **proved**, not asserted, in `G4EntropyXCeiling.lean`:

```
ScheduleWitness.log_Mx_div_log_Y_le : log Mx / log Y ≤ bigExp        -- bigExp = 3·2^K·δbig·ε·η
ScheduleWitness.Mx_le_rpow          : Mx ≤ Y ^ bigExp                -- (1 < Y)
ScheduleWitness.X_le_rpow           : (X:ℝ) ≤ Y ^ bigExp + P₀        -- (1 < Y, G.Idx inhabited)
ScheduleWitness.X_lt_X_step         : W.X < Sched.X (K+4)
```

`X_lt_X_step` is the punchline: **any** witness at scale `K` with the implemented allowances
(`δbig ≤ 1/8`, `ε ≤ 1/K`, `η ≤ 2^{−k₄}`, `Y = Sched.Y K`, `2P₀ ≤ X K`) has outer scale strictly
below the *next rung* `Sched.X (K+4)` of the ladder.  Numerically `bigExp ≤ 2^{3k₄}`, so
`log₂ X ≤ 2^{m K + 3k₄}`, whereas the next rung needs `log₂ X = 100·2^{m(K+4)}` and
`m(K+4) ≥ 4096·m₁(K) + 8(K+4)² > m K + 3k₄` (`Sched.m₁_step`, `Sched.m_add_lt`,
`Sched.pow_add_X_lt_X_step`).

## Why raising `Y` with `X` does not rescue it

`hbig`'s *first* summand is `√(4(1 + log log₂ Y − log log₂ R)·8^{−K}/15)`, which must also beat
`δbig·εη = (1/(8K))2^{−k₄}`; that permits `m − m₁ ≲ 2^{5K/2}/K²` (against the schedule's
`m₂ = 8K²`), so `m` can be raised at fixed `K`, but only by `O(2^{5K/2})`.  One rung of the
ladder costs `m₁(K+4) − m₁(K) ≥ 4095·m₁(K) = 4095·1000·8^K·K^{2K+1}`, and
`K^{2K+1} ≫ 2^{5K/2}`.  The two allowances are incommensurable: the ladder's jump is set by the
**small**-prime budget (`Λ = (2D+1)^r ≤ 4^{Kr}` against `θ₀∑_{p≤R}1/p`, which is what forces
`m₁ = 1000·8^K K^{2K+1}`), while the headroom at fixed `K` is set by the **medium**-prime dyadic
factor.  Formalizing this second half was not needed — `X_lt_X_step` already settles A0 —
so it is recorded here as prose, with `Sched.m₁_step` the ℕ fact it turns on.

## Consequence for objective A: **STOP**

Per the 18:20 RE-TARGET override, A0 = NO ⟹ record the obstruction as a named `Prop` and stop
objective A.  Done: `ScheduleWitness.X_lt_X_step`.  The prefix-control design of A (choose
`X'_i ≫` head of band `i+1`) needs exactly what this theorem forbids — band `i`'s scale reaching
band `i+1`'s head, which sits at `X(K+4)`.

## Next: objective B (the residue probe)

Read-only sweep: does every estimate in the E0 cone hold for **every** residue class with frozen
multiplier residues `c`, same constants?  `apSample X P₀ b₀` is the only place `b₀` enters the
frame (same field as `X`), which is the right starting point.
