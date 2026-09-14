# HANDOFF — entropy grind lap 28 (2026-09-14, Opus)

**Branch** `wip/g4-entropy`.  `lake build` green, **8966 jobs**; new work in
`src/NormalNumbers/G4EntropyRender.lean`, sorry-free, `#print axioms` clean.

## What was proved — the capacity inequality (laps 26 and 27 are both instances)

| declaration | statement |
|---|---|
| `abs_blockFreq_sub_le_of_deficit` | `H₂ ≥ (m_K − δ)·H_K ⇒ \|blockFreq i ℓ x w − 2^{−ℓ}\| ≤ √(2 log 2 · ℓ(ℓ+δ)/m_K)`, uniformly in `w` **and in `x`** |
| `tendsto_blockFreq_of_capacity` | the limit form: words `w_K`, reals `x_K` and deficits `δ_K` may all vary; `ℓ(ℓ+δ)/m_K → 0` suffices |

This answers the question lap 27 left open — whether the `o(√K)` ceiling is an artifact of the
Hellinger/AM-GM conversion — and the answer is **no**.  The bound splits into a *sampling* cost
`√(ℓ²/m_K)` and a *deficit* cost `√(ℓδ/m_K)`; at `δ = 50√K` and `m_K = K/4` the two cross
exactly at `ℓ ≍ √K`.  So:

* any improvement of `entropy_E1`'s deficit `δ` extends control to `ℓ = o(m_K/δ)`, and
* no improvement of `δ` ever beats `ℓ = o(√m_K)`, which is the *sampling* limit: an `m`-bit
  window simply has only `m/ℓ` disjoint `ℓ`-blocks to average over.

That is a genuine structural statement about this sample, not a lemma bookkeeping step, and it
is the sharp form of "how much of `G₄`'s digit structure this schedule sees".

## Bottleneck that moved

§5 is now closed in both directions with the trade-off explicit: `E0` alone gives every fixed
word (lap 27); the deficit's size gives the word-length range (lap 26 quantitatively, lap 28
structurally); and the ceiling is attributed to the right cause (the window's block count, not
the inequality chain).

## Next bounded test

- The remaining free direction is `entropy_E1`'s `50√K` itself.  Record, as an explicit
  conditional, what `ℓ` would follow from `δ = K^{1/2−ε}`; then decide whether the schedule's
  own structure could supply it.  (Do not touch the barrier modules; this is an input-quality
  question about `entropy_E1`, not a re-proof of it.)

## Lean gotchas from this lap

- `field_simp` closed FOUR goals outright in this file; the trailing `ring` errors with "No
  goals to be solved" each time.  When it does leave something it is often `1 + 1 = 2`
  (`norm_num`), never a `ring`-shaped goal.
- For `a/(t*D) ≤ a*ℓ/(m*t)`-type steps `nlinarith` needs the product hint spelled out:
  `mul_nonneg (by positivity) (by linarith) : 0 ≤ (log 2 * ℓ * t) * (ℓ*D − m)`.
- `defRatio ≤ δ/m ⇒ m·defRatio ≤ δ` is `mul_le_mul_of_nonneg_left` + `mul_div_cancel₀`.
