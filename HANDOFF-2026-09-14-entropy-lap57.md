# HANDOFF — entropy lap 57 (a genuine subsequence, at the disjunctivity level), 2026-09-14, Opus

**Branch** `wip/g4-entropy`.  `lake build` 🟢 **8984 jobs**.  `G4EntropyEnum.lean` **sorry-free**,
no `axiom`.

## 0. The lap in one line

E-T8 is refuted at the normality level (lap 54); this lap proves its **disjunctivity** analogue
with a genuinely **strictly increasing**, `x`-free position map — so the expedition now owns a
theorem about a real subsequence of `G₄`'s digits, not just a repetition-padded assembly.

## 1. What was proved — `G4EntropyEnum.lean`

```
IsSampledPos q            ∃ i n α p, n ∈ P_i ∧ p < m_i ∧ q = 2·kIdx(n,α) + p
exists_isSampledPos_gt / infinite_isSampledPos
sampleEnum j = Nat.nth IsSampledPos j        schedule-only; no real in its body
sampleEnum_strictMono                        StrictMono sampleEnum
sampleEnum_mem                               every value is a sampled position
sampleEnum_run     q..q+ℓ−1 sampled ⟹ sampleEnum (count q + j) = q + j  for j < ℓ
exists_occursAt_sampled   every binary word occurs in some sampled window
occurs_along_sampleEnum   ∃ t, MatchesAt (fun j => digitOf 2 (fract G₄) (sampleEnum j)) v t
```

All print `[propext, Classical.choice, Quot.sound]`.

## 2. Why this route survives the lap-54 obstruction

`chunks_insufficient` says a sub-collection is *frequency*-certifiable only while its digit count
exceeds the total entropy deficit — which kills repetition-free **normality**.  Disjunctivity
needs no frequency control at all, only occurrence, so that barrier never enters.  The structural
ingredient is `sampleEnum_run`: nothing sits strictly between `q` and `q+1`, so consecutive
sampled positions are **adjacent in the increasing enumeration**, and a word occupying a run of
positions inside one window survives as a contiguous block of the subsequence.

## 3. The next bounded test

Upgrade to *infinitely many* occurrences per word.  That yields `ProperDigits` (from `[0]`) and
hence, via `digitOf_realOfDigits`, `IsDisjunctive 2 (realOfDigits 2 (digits of G₄ along
sampleEnum))`.  Missing ingredient: the set of positions carrying an occurrence is unbounded —
the counting at one scale gives `≈ 2^{−ℓ}|P_i||Atom_i|(m_i−ℓ+1)` occurrence triples, so the
natural route is a multiplicity bound on `(n,α) ↦ kIdx(n,α)`.

## Claim limits

Nothing here is a statement about the normality of `G₄` itself; `sampleEnum` enumerates a
density-zero set of positions.
