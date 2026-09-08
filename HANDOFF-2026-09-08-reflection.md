# Handoff: the reflection lap — the certificate space is mapped, the run+jump chain is the route

**Date**: 2026-09-08 · **Branch**: `wip/adder-tower-c9` · build green 8886 jobs, trust triple
(untracked host files `docs/mahler-universal-constant-is-one-2026-09-07.md`,
`experiments/mahler_delta_star*.py`, `scratch/` are not mine; leave them).

## 🎯 What we're doing
`DIRECTION.md` CURRENT DIRECTIVE (set THIS lap, and it OUTRANKS this baton): build
`src/NormalNumbers/MahlerRunJump.lean`.  Read the directive first; the derivation is
`PENDING_WORK.md` §Reflection 2026-09-08.

## 🧠 The one thing to carry forward — the model

Backgrounds `D`, `3 ≤ D < p`.  A construction is a closed walk `… → D_{i−1} → D_i → D_{i+1} → …`
with consecutive `D` coprime.  Junction `D → D'` costs `D'(p − D)` (first failing channel).
Vertex condition at `D_i`: `−D_{i−1}/D_{i+1} ∈ ⟨p⟩ (mod D_i)`.  Then
**`M(p,1) = max over closed walks of min junction cost`** — checked exact against the census at
`p = 13,19,23,29,31` and off by one at `7,11,17` (`experiments/mahler_bg_cycle_model.py`).

## ✅ The target theorem (validated, not conjectured)

> `M(p,1) ≥ b(p − b − 1)` for every `b` with `3 ≤ b < p/2`, `gcd(b,p) = 1`,
> `−1 ∈ ⟨p⟩ (mod b)`.

Cycle: the descending run of CONSECUTIVE integers `p−b, p−b−1, …, b+1, b`, closed by the single
jump `b → p−b`.  Vertex arithmetic (do this on paper once, it is short):
* interior `D`: `prev = D+1 ≡ 1`, `next = D−1 ≡ −1` ⟹ condition `p^f ≡ 1 (mod D)` — **free**
  (`f = ord_D(p)`).
* `D = p−b`: `p ≡ b (mod D)`, `prev = b ≡ p`, `next ≡ −1` ⟹ `p^f ≡ p` — **free** (`f = 1`).
* `D = b`: `prev = b+1 ≡ 1`, `next = p−b ≡ p` ⟹ `p^{f+1} ≡ −1 (mod b)` — **the only condition**.
Bottleneck is the two end steps, both `b(p−b−1)`; the jump costs `(p−b)²`, larger.
**Checked: 2512 `(p,b)` pairs over primes `11 … 397`, ZERO mismatches**
(`experiments/mahler_runjump.py`).

Named unconditional instances (`b ∣ p+1` ⟹ `p ≡ −1 (mod b)` ⟹ condition free at `f = 1`):
* `3 ∣ p+1`: `b = (p+1)/3` ⟹ `M(p,1) > 2(p+1)(p−2)/9 − 1` (`2/9 ≈ 0.2222`)
* `4 ∣ p+1`: `b = (p+1)/4` ⟹ `M(p,1) > (p+1)(3p−5)/16 − 1` (`3/16 = 0.1875`)
* together: **`M(p,1) > 3p²/16 − O(p)` for every prime `p ≢ 1 (mod 12)`** — 2.25× family II.
Sanity: `p = 11, b = 4` ⟹ `24` (census `25`); `p = 23, b = 8` ⟹ `112` (census `120`).

## 🚫 Refuted this lap — do NOT retry
* **Orbit-free / identity-closed cycles.**  `D_{i−1}+D_{i+1} = λ_i D_i`, `λ_i ≥ 1`; at the max
  `λ_j ≤ 2` and `λ_j = 2` forces all equal, so `λ_j = 1`, the monodromy is parabolic, the solution
  space is 1-dimensional, and consecutive coprimality pins the scale to 1 ⟹ `D_i = O(1)`, cost
  LINEAR.  Measured: the `E = 0` column is empty for every prime `7 … 89`.  The previous lap's
  `(5p+7)/9, (4p+2)/9, (2p+4)/3` "cost `5/27`" lead is **dead**.
* **Closed-form single backgrounds** `D = (p+j)/c`: `j = 1` degenerate for every `c`
  (`gcd(D, p+1) = gcd(D, 1−j) = D`), so `cj ≥ 6` and the frame's ceiling is **exactly `p²/12`**.
* **Single-background multi-offset cycles**: ceiling `(b−1)/(b+b'b−b')` maximised at `(2,3)` = `1/5`,
  but NO uniform floor — `p+1 = 2q` leaves only offsets `2, q, 2q`.
* Chain steps of size `s > 1` do NOT stay free (they need `s ∈ ⟨p⟩ (mod D)`), so the run really must
  be consecutive integers.

## 🎬 Next actions
1. `MahlerRunJump.lean`.  Generalise `MahlerFareyJunction.lean` — it is the `b = (p−3)/2`
   two-background shadow of this theorem.  State type: `(j, a)` with `j ≤ p−2b`, `a < D_j = p−b−j`
   (one index more than its `Fin (2k+3)`); `E = p·lcm(b … p−b)` symbolically.
2. Then the two corollaries, then the `p ≢ 1 (mod 12)` union theorem.
3. `p ≡ 1 (mod 12)` with `(p+1)/2` prime is the one class the run+jump leaves at `1/12`; that is
   where the arithmetic wall genuinely sits — do not grind it.

## ⚠️ Gotchas
* `omega` atomizes ℕ-subtraction of nonlinear terms — state identities additively before `omega`.
* `rw [if_neg (by omega)]` inside `rw [...]` can elaborate against a metavariable — use `show … by omega`.
* The pre-commit hook runs the full `lake build`; commit only after your own green build.

## 📁 Key files
- `DIRECTION.md` §CURRENT DIRECTIVE (binding, read-only for grind laps)
- `PENDING_WORK.md` §Reflection 2026-09-08 — the full derivation
- `src/NormalNumbers/MahlerFareyJunction.lean` — the two-background shadow to generalise
- `experiments/mahler_bg_cycle_model.py` / `…_ecap.py` / `mahler_runjump.py` — the instruments

---
**→ Next session: pick up at "Next actions" #1.**
