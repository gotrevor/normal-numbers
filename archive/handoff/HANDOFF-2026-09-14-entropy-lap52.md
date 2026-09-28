# HANDOFF — entropy lap 52 (🎯 OBJECTIVE MET), 2026-09-14, Opus

**Branch** `wip/g4-entropy`.  `lake build` 🟢 **8982 jobs**.  New work **sorry-free**, no `axiom`.
No pre-expedition G4/G5 file edited.

## 0. The lap in one line

Rung 2 was completed and the three rungs assembled: **`G₄`'s binary digits, read along an
explicit `x`-independent sequence of sampled positions, form a normal sequence — and hence a
normal real.**  That is exactly the lap-51 CURRENT DIRECTIVE's 🎯 objective, so **E-T7 fires**:
this lap does not pick its own successor; the next altitude lap sets one.

## 1. What was proved (`G4EntropyBlockWord.lean`, all in `NormalNumbers.G4.Sched`)

```
matchesAt_per_blen_iff   a fitting window of the block ↔ an OccursAt of x at a sampled position
goodCount                the numerator of tendsto_occursCountP_primeLambertFour, verbatim
card_filter_fit          counting on [0,m) vs on the fitting [0,m−ℓ+1): differ by ≤ ℓ
cyc_eq_sum               the cyclic count split into the nwin i sampled windows
sum_fit_eq_goodCount     ∑ over windows of the fitting count = goodCount  (the enumeration bridge)
cyc_bounds               goodCount ≤ cyc ≤ goodCount + nwin·|v|        ← lap 51's one open lemma
tendsto_kk_atTop, tendsto_blen_atTop
tendsto_cyc_div_blen     cyc i / blen i → 2^{−|v|}  for every finite binary word  ← RUNG 2 DONE
sampleDigits             seq blen (bdig G₄)
isNormalSequence_sampleDigits      IsNormalSequence 2 (sampleDigits G₄)
isNormal_sampleReal                IsNormal 2 (realOfDigits 2 (sampleDigits G₄))
samplePos                the x-FREE position map: samplePosIn (grp j) ((j − Tacc (grp j)) % blen …)
sampleDigits_eq          sampleDigits x j = digitOf 2 (fract x) (samplePos j)      (rfl)
samplePos_spec           ∀ j, ∃ i n α p, n ∈ P_i ∧ p < m_i ∧ samplePos j = 2·kIdx(n,α) + p
isNormalSequence_digits_along_samplePos
        IsNormalSequence 2 (fun j => digitOf 2 (fract G₄) (samplePos j))     ← THE HEADLINE
isNormal_realOfDigits_samplePos
        IsNormal 2 (realOfDigits 2 (fun j => digitOf 2 (fract G₄) (samplePos j)))
```

All five endpoints print `[propext, Classical.choice, Quot.sound]`.

## 2. The objective, matched clause by clause

The directive asked for a map `samplePos : ℕ → ℕ` **defined from the schedule alone** (`samplePos`
mentions only `blen`, `grp`, `Tacc`, `wpos`, `kk` — no real appears in its type or body), with
**every value a sampled position** (`samplePos_spec`), such that `IsNormalSequence 2 (fun j =>
digitOf 2 (Int.fract G₄) (samplePos j))` (`isNormalSequence_digits_along_samplePos`), hence
`IsNormal 2 (realOfDigits 2 …)` (`isNormal_realOfDigits_samplePos`).  Every clause is a theorem.

This is the expedition's **first infinite object**: laps 31–50 all produced statistics at scale
`i` with `i → ∞`; this is one number.

## 3. Which bottleneck moved

Lap 51 left exactly one lemma (`cyc_bounds`) and called the rest bookkeeping.  It was: the chain
`card_filter_range_mul` → fitting-position split → `matchesAt_per_blen_iff` → `sum_range_mul` +
`wpos_mk` → `sum_range_nthP`/`sum_range_nthA` → `Fintype.sum_prod_type`/`Finset.sum_comm` went
through as written.  The limit then needed only the two vanishing corrections `(m−ℓ+1)/m → 1`
and `|v|/m → 0`, both from `kk i = 40000 + i → ∞`.

## 4. Claim limits (unchanged, and load-bearing)

**Nothing here is a claim about the normality of `G₄` itself**, which stays closed on this
mechanism (lap 37: the sampled positions have density `≤ ½(3/K⁴)^K`).  The number built is made
*from* `G₄`'s digits along a density-zero position sequence and is not `G₄`.

## 5. Open, for the altitude lap to weigh (NOT a self-assigned target)

* **E-T8** (recorded in the directive): `samplePos` is not injective — repetition reuses
  positions.  Upgrading to a strictly increasing `samplePos` (a genuine subsequence of `G₄`'s
  digits) is the named next target, reachable by restricting the empirical law to `S ⊆ P_K` of
  relative size `ρ` at deficit cost `Δ/ρ`.
* The bounded secondary target (`Sched.density_le_pow`, `Sched.window_needed_ge`) is untouched.
