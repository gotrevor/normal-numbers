# Handoff: the run+jump chain theorem is PROVED (`mahler_lower_bound_runjump`)

**Date**: 2026-09-08 · **Branch**: `wip/adder-tower-c9` · build green **8888 jobs**
· `#print axioms` of `mahler_lower_bound_runjump`, `…_three`, `…_four`, `…_base31_runjump`
= `[propext, Classical.choice, Quot.sound]`.  No `sorry` in either file.

## 🎯 Directive — READ `DIRECTION.md` §CURRENT DIRECTIVE FIRST (it outranks this baton)

Its mandated move (`MahlerRunJump.lean` + the two `b ∣ p+1` corollaries) is **DONE** within
two grind laps (trigger T1 satisfied).  Trigger **T3** now applies: the unconditional constant is
`3/16` for `p ≢ 1 (mod 12)` and `1/12` for `p ≡ 1 (mod 12)`.  The next ALTITUDE lap decides what
follows; do not invent a new route in a grind lap.

## ✅ What landed (two laps)
* `src/NormalNumbers/MahlerRunJump.lean` — the certificate, valid for every `M < b(p−b−1)`.
* `src/NormalNumbers/MahlerRunJumpWalk.lean` — data from `p^f ≡ −1 (mod b)`, walks, theorem:
  **prime `p`, `3 ≤ b < p/2`, `−1 ∈ ⟨p⟩ (mod b)` ⟹ `M(p,1) > b(p−b−1) − 1`**; corollaries
  `2/9` (`3 ∣ p+1`) and `3/16` (`4 ∣ p+1`), anchors `M(13,1) ≥ 35`, `M(31,1) ≥ 224` (both EXACT).
* Census cross-check passes at every admissible pair `p ≤ 31`; exact at `(13,5)`, `(23,10)`, `(31,14)`.
Full account + gotchas: `PENDING_WORK.md` §GRIND 2026-09-08 (laps 2, 3).

## 📏 Lap 4 measurement (see `PENDING_WORK.md` §MEASURED 2026-09-08)
The theorem's hypothesis is satisfiable within `j ≤ 33` of `p/2` at EVERY prime `< 2000`, so the
proved bound is `1/4 − O(1/p)` there, `p ≡ 1 (mod 12)` included; `…_near_half` states it.  The
uniform-`1/4` question is now purely arithmetic: an admissible `b` near `p/2`.

## 🎬 If a grind lap runs before the altitude lap
* `p ≡ 1 (mod 12)`: census which primes have a divisor `b ∈ (p/3, p/2)` of `p² + 1` (then `f = 2`
  and `mahler_lower_bound_runjump` applies with `b(p−b−1) ≥ 2p²/9`); this is a Python probe, not Lean.
* Otherwise idle-correct: nothing in `src/` is open on this route.

## 📁 Key files
- `DIRECTION.md` §CURRENT DIRECTIVE · `PENDING_WORK.md` §GRIND 2026-09-08 (lap 3) · `STATUS.md` (updated)
- `src/NormalNumbers/MahlerRunJump.lean`, `src/NormalNumbers/MahlerRunJumpWalk.lean`
