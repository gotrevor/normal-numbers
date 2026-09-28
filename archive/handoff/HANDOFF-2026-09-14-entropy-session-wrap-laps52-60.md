# HANDOFF — entropy session wrap, laps 52–60, 2026-09-14, Opus

**Branch** `wip/g4-entropy`.  **HEAD** `90ed1e2`.  Working tree **clean**.
`lake build` 🟢 **8984 jobs**.  Every new module **sorry-free**; no `axiom` introduced;
no pre-expedition G4/G5 file edited.  Every endpoint below prints
`[propext, Classical.choice, Quot.sound]`.

## The session in one line

The lap-51 🎯 objective was **proved** (lap 52), its named successor **E-T8 was refuted as a
route** with a theorem (lap 54), and then E-T8's *disjunctivity* analogue was **proved** with a
genuinely strictly increasing, density-zero position map (laps 56–60).

## What was proved, by module

### `G4EntropyBlockWord.lean` — rung 2, and the 🎯 headline (laps 52, 55)
```
matchesAt_per_blen_iff, card_filter_fit, cyc_eq_sum, sum_fit_eq_goodCount
cyc_bounds                  goodCount ≤ cyc ≤ goodCount + nwin·|v|      (lap 51's one open lemma)
tendsto_cyc_div_blen        cyc i / blen i → 2^{−|v|}                   RUNG 2 COMPLETE
samplePos                   x-FREE position map (blen, grp, Tacc, wpos, kk only)
samplePos_spec              every value is a sampled position 2·kIdx(n,α)+p
isNormalSequence_digits_along_samplePos    ← THE 🎯 HEADLINE
isNormal_realOfDigits_samplePos, isDisjunctive_sampleReal, irrational_sampleReal
```

### `G4EntropySubsample.lean` — E-T8's tool, and its refutation (laps 53–54)
```
FinLaw.H₂_restrictCoords_ge   dropping coordinates costs ≤ m bits each: total deficit survives
abs_posAvg_restrict_sub_le    a sub-collection of relative size ρ costs √(1/ρ), not 1/ρ
card_Atom_growth              (K²+1)⁴·|Atom_i| ≤ |Atom_{i+1}|
chunks_insufficient           kk i/(50√(KK i)) < |Atom_{i+1}|/|Atom_i|
```
Reading: the left side is the most disjoint chunks one scale can *certify* (`m/δ = √K/200`); the
right side lower-bounds how many a repetition-free assembly needs.  Never enough.  The barrier is
**dimension-independent** — window truncation is `lowTuple`'s dual — so chunking the sample times
instead of the atoms does not escape it.  *Refutes the route, not the existence of the sequence.*

### `G4EntropyEnum.lean` — the strictly increasing subsequence (laps 56–60)
```
IsSampledPos / isSampledPos_iff_isSampled        = the repo's IsSampled
infinite_isSampledPos, sampleEnum = Nat.nth IsSampledPos
sampleEnum_strictMono                            a GENUINE subsequence
sampleEnum_run     consecutive sampled positions are ADJACENT in the enumeration
exists_occursAt_sampled, occurs_along_sampleEnum every binary word occurs along sampleEnum
enumDigits, properDigits_enumDigits
isDisjunctive_enumReal    IsDisjunctive 2 (realOfDigits 2 enumDigits)
irrational_enumReal
exists_cover / card_filter_isSampled_le          density ≤ ¼
exists_cover_tail / density_geom / card_tail_le
tendsto_density_isSampled                        **density ZERO**
```

Why this survives `chunks_insufficient`: disjunctivity needs no frequency control, only
occurrence, so the `ρ ≫ δ/m` barrier never enters.  The structural ingredient is
`sampleEnum_run` — nothing sits strictly between `q` and `q+1`, so a word occupying a run of
positions inside one window survives the enumeration as a contiguous block.

## Two things this session caught that were not on anyone's list

1. **`ProperDigits` for free.**  Lap 57 flagged "upgrade to infinitely many occurrences, via a
   multiplicity bound on `(n,α) ↦ kIdx`".  Unnecessary: apply `occurs_along_sampleEnum` to
   `List.replicate (N+1) 0` — the match puts a `0` at subsequence index `t + N ≥ N`, because
   lateness is measured in the *subsequence's* index, not in `G₄`'s positions.
2. **A real non-vacuity gap.**  `density_le_pow_real` bounds **one** scale; the headline reads the
   **union over all scales**, which nothing controlled.  Had that union been cofinite, `sampleEnum`
   would be the identity and lap 58 a restatement of `isDisjunctive_two`.  Laps 59–60 closed it:
   each `sampledPosAt i` is finite, so a cutoff splits the union into a fixed finite head and a
   geometric tail — density zero.

## Campaign state

* 🎯 lap-51 objective — **MET** (lap 52).  E-T7 is in force: a grind lap that meets the objective
  does not pick its own successor; **the next objective is owed by an altitude lap.**
* E-T8 at the **normality** level — refuted as a route (lap 54).
* E-T8 at the **disjunctivity** level — **proved**, density-zero (laps 56–60).
* 📌 bounded secondary target (`Sched.density_le_pow`, `Sched.window_needed_ge`) — already proved
  in `G4EntropyWall.lean`; nothing open there.

## Next bounded test (for the altitude lap to weigh, not a self-assigned objective)

Is `realOfDigits 2 enumDigits` **normal**?  `chunks_insufficient` does not transfer directly —
`enumDigits` is not a block concatenation — but the same prefix problem reappears: `|S_i|` explodes
with `i` and the enumeration order is forced, so repetition (rung 3's fix) is unavailable.  A
frequency estimate is further blocked because the enumeration interleaves windows from different
scales, so a word may straddle two scales' windows.  **First concrete sub-probe**: are maximal runs
of `IsSampled` exactly single windows?

## Claim limits (load-bearing, repeated in every module docstring)

Nothing in laps 52–60 is a statement about the normality of `G₄` itself, which stays closed on
this mechanism (lap 37).  Both reals built are made *from* `G₄`'s digits along density-zero
position sets and are not `G₄`.
