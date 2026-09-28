# HANDOFF — entropy lap 54 (the E-T8 obstruction, formalized), 2026-09-14, Opus

**Branch** `wip/g4-entropy`.  `lake build` 🟢 **8983 jobs**.  Sorry-free, no `axiom`.

## 0. The lap in one line

The quantitative obstruction lap 53 computed is now a **theorem**, and the escape route it left
open (route (b), chunking the sample times instead of the atoms) is closed by a better argument:
the barrier is dimension-independent.

## 1. What was proved — `G4EntropySubsample.lean`

```
card_Atom_growth      (KK i ^ 2 + 1) ^ 4 * |Atom_i| ≤ |Atom_{i+1}|
chunks_insufficient   kk i / (50 · √(KK i))  <  |Atom_{i+1}| / |Atom_i|
```

Both `[propext, Classical.choice, Quot.sound]`.

**Reading.**  The left side is the largest number of disjoint chunks one scale can *certify*:
`abs_posAvg_restrict_sub_le` (lap 53) certifies relative size `ρ` only while `ρ ≫ δ/m`, and
`δ = 50√K`, `m = K/4` give `m/δ = √K/200`.  The right side is a lower bound for how many chunks
a repetition-free assembly needs, since the block length grows at least as fast as the atom
count.  The strict inequality says there are never enough.

## 2. Which bottleneck moved — the barrier is dimension-independent

Lap 53 left open: maybe chunk along a different coordinate.  It does not help.  Truncating each
window to its top `s` bits is the *same* subadditivity argument as `H₂_restrictCoords_ge`
(it is `lowTuple`'s dual), so a chunk cut by atoms **and** by window length carries
per-coordinate deficit `δ|A|/|G|` on `s` bits and is certifiable exactly when
`(|G|/|A|)·(s/m) ≫ δ/m`.  The split between the two dimensions cancels.  In one line:

> a chunk is certifiable only if its digit count exceeds the collection's **total entropy
> deficit** — so the minimal certifiable granule at scale `i+1` is `≈ δ_{i+1}·W_{i+1}` digits,
> already bigger than scale `i`'s entire block `m_i·W_i`.

So `E-T8` needs a different *construction*, not a different chunking.  Recorded in
`PENDING_WORK.md`'s ACTIVE section, with what is **not** excluded: a mechanism lowering `δ` below
`m/K²` at some scale, or one producing good blocks of comparable length at many scales.  Neither
is visible in the current schedule.

## 3. Claim limits

`chunks_insufficient` refutes the chunking **route** to a strictly increasing `samplePos`; it is
not a proof that no such sequence exists.  The docstring says so.  Nothing in this lap is about
the normality of `G₄` itself.

## 4. Next bounded test

The campaign's 🎯 objective was met at lap 52 and E-T7 forbids a grind lap picking the successor;
the E-T8 upgrade is now refuted as a route.  The next altitude lap owes a new objective.  Until
then the directive's 📌 bounded secondary target stands: `Sched.density_le_pow` (`≤ ½(3/K⁴)^K`)
and `Sched.window_needed_ge`.
