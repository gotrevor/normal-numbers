# HANDOFF — entropy lap 58 (the disjunctive real off a true subsequence), 2026-09-14, Opus

**Branch** `wip/g4-entropy`.  `lake build` 🟢 **8984 jobs**.  `G4EntropyEnum.lean` sorry-free,
no `axiom`.

## 0. The lap in one line

The lap-57 endpoint is upgraded to a **real number**: `G₄`'s binary digits read along the
strictly increasing, schedule-defined `sampleEnum` sum to an **irrational, disjunctive** real.

## 1. What was proved

```
enumDigits j = digitOf 2 (fract G₄) (sampleEnum j)      enumDigits_lt
properDigits_enumDigits    ProperDigits 2 enumDigits
isDisjunctive_enumReal     IsDisjunctive 2 (realOfDigits 2 enumDigits)
irrational_enumReal        Irrational (realOfDigits 2 enumDigits)
```

All `[propext, Classical.choice, Quot.sound]`.

## 2. Which bottleneck moved

The lap-57 handoff flagged "upgrade to infinitely many occurrences" — via a multiplicity bound on
`(n,α) ↦ kIdx(n,α)` — as the next obligation.  **That detour is unnecessary.**  Applying
`occurs_along_sampleEnum` to `List.replicate (N+1) 0` puts a `0` at subsequence index `t + N ≥ N`,
which *is* `ProperDigits`.  One occurrence of a long enough word gives lateness for free, because
lateness is measured in the subsequence's own index, not in `G₄`'s positions.  Then
`digitOf_realOfDigits` + `isDisjunctive_iff_forall_occursAt` close it.

## 3. Where the campaign stands

* 🎯 lap-51 objective — met (lap 52): a normal real from `G₄`'s sampled digits, with a
  repetition-padded position map.
* E-T8 at the **normality** level — refuted as a route (lap 54, `chunks_insufficient`).
* E-T8 at the **disjunctivity** level — **proved** (laps 56–58), with a genuinely `StrictMono`
  position map.
* Open, and not excluded by anything proved: is `realOfDigits 2 enumDigits` **normal**?

## Claim limits

Nothing here is a statement about the normality of `G₄` itself; `sampleEnum` enumerates a
density-zero set of positions.
