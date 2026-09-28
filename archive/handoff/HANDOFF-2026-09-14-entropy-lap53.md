# HANDOFF — entropy lap 53 (E-T8's affirmative tool + its refuting arithmetic), 2026-09-14, Opus

**Branch** `wip/g4-entropy`.  `lake build` 🟢 **8983 jobs**.  New module sorry-free, no `axiom`.

## 0. The lap in one line

Lap 52 met the 🎯 objective; this lap attacked the directive's named successor **E-T8** (a
strictly increasing `samplePos`, i.e. a genuine subsequence of `G₄`'s digits): its affirmative
tool is now **proved**, and the same tool's constant **refutes** the chunking route quantitatively.

## 1. What was proved — `G4EntropySubsample.lean`

```
FinLaw.restrictCoords / padG / splitG      restriction of a window law to a coordinate subset G
FinLaw.padG_injective
FinLaw.H₂_restrictCoords_ge    L.H₂ − (|A| − |G|)·m ≤ (L.map (restrictCoords G m)).H₂
abs_posAvg_restrict_sub_le     |posAvg (L.map restrictCoords G m) w − 2^{−ℓ}|
                                 ≤ 2√(log 2 · ℓ · (δ|A|/|G|) / (m−ℓ+1))
```

Both print `[propext, Classical.choice, Quot.sound]`.

The content: dropping a coordinate costs at most `m` bits (generalized subadditivity against the
split "restricted family ⊕ each dropped coordinate"), so a *total* deficit `δ·|A|` survives
restriction unchanged — the restricted law has per-coordinate deficit `δ/ρ` with `ρ = |G|/|A|`.
Because the capacity bound is a square root, **restriction costs `√(1/ρ)`, not `1/ρ`**.  That
is the strongest form of the directive's "deficit cost `Δ/ρ`, affordable for `ρ ≫ K^{−1/2}`".

## 2. Which bottleneck moved — E-T8 is refuted on this mechanism

With the tool in hand the route closes by arithmetic (recorded in `PENDING_WORK.md`'s ACTIVE
section):

* removing repetition needs `c` **disjoint** good chunks per scale;
* a chunk of relative size `ρ = 1/c` is good only while `δ/(ρm) → 0`, i.e. `ρ ≫ 200ℓ/√K`
  (`δ = 50√K`, `m = K/4`), so `c = O(√K)`;
* the prefix condition needs `ρ_{i+1} ≪ L_i/L_{i+1}`, and
  `L_{i+1}/L_i ≥ |Atom_{i+1}|/|Atom_i| ≈ e²K²`;
* so E-T8 needs `K^{−1/2} ≪ ρ ≪ K^{−2}`. **Impossible.**

So E-T8 is not a bookkeeping follow-up to lap 52: coordinate chunking cannot replace repetition.
This is a negative result whose value is its constant, exactly as the directive frames them.

## 3. The next bounded test

(a) Formalize the obstruction in lap-48 shape: the growth half is the concrete lemma
`blen (i+1) ≥ c·(KK i)²·blen i` out of `card_Atom_gridAt`, pairable with
`abs_posAvg_restrict_sub_le`'s constant.  (b) Or find a mechanism giving many disjoint good
chunks without shrinking relative size — the only visible candidate is splitting the **sample
times** `P_K` instead of the atoms, for which the naive analogue is false (`H₂` of a one-point
empirical law is `0`).

## Claim limits

Unchanged: nothing here is about the normality of `G₄` itself.
