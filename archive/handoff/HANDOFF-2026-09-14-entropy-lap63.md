# HANDOFF — entropy lap 63, 2026-09-14, Opus

**Branch** `wip/g4-entropy`.  `lake build` 🟢 **8987 jobs**.  New module
`src/NormalNumbers/G4EntropyMixture.lean`, sorry-free, endpoints
`[propext, Classical.choice, Quot.sound]`.

## What was proved — the sample-time side of the restriction cost

Lap 62's granularity wall rested on a *reading*: "a certified granule must average over
`≳ |P_K|/m_K` sample times".  This lap makes that a theorem.

```
negMulLog_add_le                negMulLog (u+v) ≤ negMulLog u + negMulLog v
FinLaw.mix σ L₁ L₂              the σ-mixture of two laws
FinLaw.H₂_mix_le                H₂(mix) ≤ σH₂(L₁) + (1−σ)H₂(L₂) + 1     (the extra bit is
                                Real.binEntropy σ ≤ log 2)
FinLaw.H₂_of_mix_part_ge        a part of a mixture inherits deficit (δ+1)/σ
empirical_eq_mix                empirical P = mix (|S|/|P|) (empirical S) (empirical (P∖S))
H₂_empirical_restrict_ge        the general restriction cost
H₂_empirical_window_restrict_ge the window form, ceiling m bits
capture_bound_vacuous           the capture bound is ≥ 1, i.e. says nothing, below threshold
Sched.certified_granule_exceeds_previous_scale
```

The last one is the endpoint:

> For any `S ⊆ P_{K_{i+1}}` whose derived capture bound (capture inequality fed the restricted
> deficit `(δ+1)/σ`, `σ = |S|/|P|`) is **not vacuous**,
> `|Atom_i|·|P_{K_i}|·m_i < |S|·m_{i+1}`.

Everything scale `i` produced — every atom, every sample time, every digit — is smaller than
the digit count of **any** non-vacuously certified granule at scale `i+1`.  Independent of how
the granule is cut: by atoms (`H₂_restrictCoords_ge`), by sample times (this module), or both.

## Status of the route family

* Lap 54 `chunks_insufficient` — chunking by atoms, refuted via atom-count growth.
* Lap 61 `card_good_ge` — the granule *can* be shrunk to one atom (so lap 54's mechanism was
  not the real obstruction).
* Lap 62 `granule_exceeds_previous_scale` — arithmetic wall, driven by
  `X(K) = 2^{100·2^{m(K)}}`, `m(K) ≥ K³`.
* Lap 63 (this) — the wall in certified form, with the sample-time restriction cost proved.

**Conclusion.**  The whole family "read `G₄`'s sampled digits in position order as a
concatenation of certified granules" is closed on this schedule: the first granule of each new
scale wipes out the entire history, so prefix frequencies cannot converge.  Normality of
`realOfDigits 2 enumDigits` is therefore not reachable by any granule-concatenation argument —
and the disjunctivity endpoints of laps 56–60 remain the strongest infinite objects the
mechanism supports.

## Next bounded tests

1. `posAvg = (1/|A|)·Σ_α coordAvg` — the consistency bridge for `coordAvg` (lap 61).
2. The escape the wall leaves open: a scale ladder with `X(K)` growing *polynomially* rather
   than as `2^{2^{K³}}`.  `X` is fixed by `G4ScheduleFar` (far-tail control), so this is a
   question about the *schedule*, not about the entropy argument — the first honest place the
   expedition's mechanism could be changed.
