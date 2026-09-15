# HANDOFF — lap 128: 🏁 `IsNormal 4 fullRealW` and `IsNormal (2^k) fullRealW`, axiom-clean

**Branch** `wip/g4-entropy`.  Working tree clean.  `lake build` 🟢 **9033 jobs**, exit 0.
`src/` carries **two** `sorry`s, both pre-expedition, off-path, on the forbidden-drift list
(`PrimeLambertOscillation.phaseOscillation`, `MahlerDriftOne.exists_drift_one_background`).
Everything this lap added is **sorry-free** and prints `[propext, Classical.choice, Quot.sound]`.

## The objective is met

`DIRECTION.md`'s lap-126-close CURRENT DIRECTIVE asked for `IsNormal 4 fullRealW`, then
`IsNormal (2^k) fullRealW`.  Both are proved — by the successor route that lap 127's E-T13
escalation identified, not by the directive's own steps 3–4 (step 3 stays refuted).  **E-T7:
this lap does not choose the next target.**

```
NormalNumbers.G4.Sched.isNormal_four_fullRealW    : IsNormal 4 fullRealW
NormalNumbers.G4.Sched.isNormal_two_pow_fullRealW : ∀ k, 0 < k → IsNormal (2 ^ k) fullRealW
NormalNumbers.PowerBase.isNormal_pow              : IsNormal b x → IsNormal (b ^ K) x
```

`isNormal_pow` is the classical theorem "normal to base `b` ⇒ normal to base `b^K`" (one half of
Maxfield), proved here **elementarily**: no Wall, no Weyl/Fourier, no measure theory, no ergodic
theorem.  It applies to every base and every normal number, so it is strictly more than the
directive asked for, and `fullRealW`, `fullPosW`, `fullDigW`, `G4EntropyWStatement` are untouched.

## This lap's commits

| commit | content |
|---|---|
| `da…` skeleton | `PowerBaseLimit` skeleton; `Sys.shift` gains `k < b ^ m` |
| `…` | **`PowerBaseLimit`** — the ultrafilter glue, sorry-free |
| `…` skeleton | `PowerBaseBlock` skeleton |
| `…` | **`PowerBaseBlock`** — `isNormalSequence_pow`, sorry-free |
| `…` | **`PowerBaseReal`** — `isNormal_pow` and the two corollaries |

(`git log --oneline -6` for the hashes.)

## The three new modules

**`PowerBaseLimit.lean`** — manufactures a `BlockRigidity.Sys` out of a normal sequence.
`Gseq b K c s m k n = (K/n)·resCount K c s (wordOf b m k) n` lives in the compact `[0, K]`, so
`IsCompact.ultrafilter_le_nhds` + `le_nhds_lim` give a limit `G` along **any** ultrafilter
`g ≤ atTop`.  The three `Sys` relations survive: `right` is an exact pointwise identity
(`resCount_append`), `prepend` is exact up to `1/n` (`resCount_prepend_bounds`, pushed through by
`eq_of_tendsto_of_close`), `unit` needs the AP count `|K·#{p<n : p ≡ c} − n| ≤ K`
(`resCount_nil_bounds`), and `bdd` (`C = K`) is normality of `s`
(`tendsto_winCount_wordOf`, the converse of `isNormalSequence_of_tendsto_winCount`).
`shift` is `G_prepend` iterated `K` times plus `K`-periodicity of `G` in the class.  Rigidity then
pins `G = b^{−m}` for *every* ultrafilter, so `tendsto_iff_ultrafilter` gives

> 🎯 `tendsto_resCount` : `(K/n)·resCount K c s (wordOf b m k) n → b^{−m}`.

**`PowerBaseBlock.lean`** — the bookkeeping.  `valOf` (numeric value) is inverse to `wordOf`
(`wordOf_valOf`, `valOf_wordOf`), `wordOf_split` and `wordOf_mod` make `wordOf` a genuine digit
expansion, `flat b K` expands each base-`b^K` letter into `K` base-`b` digits with
`flat_wordOf : flat b K (wordOf (b^K) ℓ k) = wordOf b (K·ℓ) k`, and
`matchesAt_blockOf : MatchesAt (blockOf b K s) w j ↔ MatchesAt s (flat w) (K·j)`.  Hence
`winCount (blockOf b K s) w N = resCount K 0 s (flat w) (K·N)` (an exact bijection `j ↦ K·j`) and
`isNormalSequence_pow` follows by composing `tendsto_resCount` with `N ↦ K·N`.

**`PowerBaseReal.lean`** — `blockOf_digitOf : blockOf b K (digitOf b z) j = digitOf (b^K) z j`,
i.e. the base-`b^K` digit *is* the `K`-block of base-`b` digits.  Both sides are read off the one
integer `⌊z·b^{K(j+1)}⌋₊` via the nested-floor identity `⌊z·b^e⌋₊ = ⌊z·b^{e+r}⌋₊ / b^r`
(`floorNat_pow`, on `Nat.floor_div_natCast`).  Then `isNormal_pow`, then the corollaries.

## Hygiene learned this lap

* `Finset.range_succ` does not exist; it is **`Finset.range_add_one`** (`List.range_add` *does*
  exist and is the right tool for splitting `wordOf`).
* `Finset.card_le_card_of_injOn`'s membership hypotheses are stated on the **coe** sets: rewrite
  with `Finset.mem_coe` *first*, or the `mem_filter`/`mem_range` rewrite fails.
* After `refine tendsto_of_tendsto_of_tendsto_of_le_of_le _ _ ?_ ?_; intro n`, the goal is not
  beta-reduced — `dsimp only` before `gcongr`/`rw`, or they silently fail to match.
* `omega` atomises `K * j` but will not relate it to `K * (j + 1)`: supply
  `have : K * (j+1) = K * j + K := by ring` alongside.
* `Int.floor_toNat : ⌊a⌋.toNat = ⌊a⌋₊` turns `digitOf`'s `Int` floor into a `Nat` floor, after
  which `Nat.floor_div_natCast` does the nesting with no sign side conditions.
* `Nat.mul_lt_mul_left hK` is an **iff** here (`K*a < K*b ↔ a < b`), not an implication.

## Governing documents

* `DIRECTION.md` lap-126-close CURRENT DIRECTIVE: 🏁 **its 🎯 is met**.  A grind lap may not edit
  DIRECTION; the next altitude lap owns the successor.
* `PENDING_WORK.md` ACTIVE rewritten for lap 128 (the lap-126-close section is marked superseded).
* `ROUTE-ESCALATION-2026-09-15-base2k-step3.md` stands unchanged: step 3 is refuted, and the
  successor it names is exactly what landed.
* Still open and untouched: the Aristotle line-by-line diff of job
  `48c7d703-d18e-4e47-ae9c-6734f6737047` (cheap, optional).
