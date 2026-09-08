# Handoff: `MahlerRunJump.lean` — the run+jump chain, set up and decomposed

**Date**: 2026-09-08 · **Branch**: `wip/adder-tower-c9` · **HEAD**: `3081f1f` · tree clean
· build green **8887 jobs**
(untracked host files are gone from the tree: `scratch/` is now gitignored; the host's
`docs/mahler-universal-constant-is-one-2026-09-07.md` and `experiments/mahler_delta_star*.py`
were committed at `f1e042e` — that was an over-broad `git add -A`, not a deliberate change.)

## 🎯 What we're doing — READ `DIRECTION.md` §CURRENT DIRECTIVE FIRST

It was rewritten by the 2026-09-08 deep reflection lap and **outranks this baton**.  Objective:
pin `M(p,1)`; crux = the factor `3`; **mandated move = `src/NormalNumbers/MahlerRunJump.lean`**,
then the two `b ∣ p+1` corollaries.  Route triggers **T1–T3** are registered there — check them
on the next altitude lap.  Full derivation: `PENDING_WORK.md` §Reflection 2026-09-08 and
§GRIND 2026-09-08 (post-reflection).

## 🧠 The theorem being built (validated numerically before formalising)

> `M(p,1) ≥ b(p − b − 1)` for every `b` with `3 ≤ b < p/2`, `gcd(b,p) = 1`, `−1 ∈ ⟨p⟩ (mod b)`.

Cycle: the descending run of CONSECUTIVE integers `p−b, p−b−1, …, b+1, b`, closed by the single
jump `b → p−b`.  Interior vertices are free (`p^f ≡ 1`), the top `p−b` is free (`f = 1`), and the
ONLY arithmetic condition is at the bottom `b`.  2512 `(p,b)` pairs checked, zero mismatches
(`experiments/mahler_runjump.py`).  `b ∣ p+1` makes the condition free ⟹ `b = (p+1)/3` gives
`2/9` and `b = (p+1)/4` gives `3/16`, covering every prime `p ≢ 1 (mod 12)`.

## ✅ State of the file (all observed: `lake build` green 8887 jobs)

`src/NormalNumbers/MahlerRunJump.lean`, wired into `src/NormalNumbers.lean` (line 122).

* `Dh b i = b + i` (`p = 2b + L`, so `Dh 0 = b`, `Dh L = p − b`); `nx L i = if i = 0 then L else i−1`
  (the closing jump); `Dn b L i = Dh b (nx L i)`.
* `Data` = `al` (departure), `cj` (injection source), `ap` (landing), `dj` (junction digit).
  `Hyp` = ranges + `inj : cj i * p % Dh i = al i` + the **single exact-landing identity**
  `key : p * al i * Dn i + 1 = ap i * Dh i + dj i * (Dh i * Dn i)`
  (mod `Dh` it is the departure condition, mod `Dn` the landing condition).
* States `Fin ((L+1)*p + (L+1))`; `s.1 / p ≤ L` = far `(i,a)`, `= L+1` = junction `J (s.1 % p)`.
* **PROVED**: `dm`, `far_val`, `ix_far`, `rs_far`, `jn_val`, `ix_jn`, `rs_jn`, `state_cases`,
  `Dh_bounds`, `Dn_bounds`, `dig_lt`, **`intervals`**.
* **4 disclosed sub-`sorry`s** (the decomposition, in `src/` deliberately): `edges`, `carries`,
  `recursion`, `block`.  Each has its paper proof written out in `PENDING_WORK.md`
  §GRIND 2026-09-08.

## 🎬 Next actions, in order
1. **`edges`** — three edge types (far / injection / junction).  Needs `nxt` unfolded through the
   decoding lemmas; the junction case is EXACT by `Hyp.key`.
2. **`block` + `recursion` together** via one shared lemma in the style of `NumCert.chDigit_eq`:
   `m * dig s + cc s' m = x + p * cc s m` with `x = ⌊p·{m·lo s} + m·ε⌋`, `ε` the per-edge gap.
   `block` is `x < p − 1`, `recursion` is `x < p`.  **`block` is where `M` comes from**: it reduces
   to `p·Dn·(m·al mod Dh) + m < (p−1)·Dh·Dn`, which follows from `m ≤ M` and the exact identity
   `p·Dn·(Dh−1) + Dn·(p−Dh) = Dh·Dn·(p−1)` — i.e. `M < Dn i·(p − Dh i)`, whose minimum over the run
   is `b(b+L−1) = b(p−b−1)`.
3. **`carries`**.
4. **`Data` existence**: for `i ≥ 1`, `al i = p⁻¹ mod Dh i`, `ap i = 1`, `dj i = (p·al i − 1)/Dh i`
   (the identity then collapses to `p·al ≡ 1 mod Dh`); for `i = 0` the closing jump.  Then the walk
   (Euler: `p^(φ(D)−2)` connects landing to injection source) and the two corollaries.

## ⚠️ Gotchas hit this lap
* `Fin` anonymous-constructor `.1` rewrites give "motive is not type correct" — use
  `show <the raw ℕ expression> = …` to unfold `Fin.val` definitionally first, then `rw`.
* `omega` needs `h.hb`/`h.hp` materialised as local `have`s (it cannot project a structure).
* `omega` treats `x * p` and `p * x` as distinct atoms — add a `by ring` bridge (`state_cases`
  needed exactly this).
* `omit h in` must go BEFORE the doc comment, not between doc comment and `theorem`.
* `field_simp` closes these interval identities on its own; a trailing `ring` then errors with
  "No goals to be solved".
* `set P := …` (a ℕ) will NOT fold `↑p * ↑d * ↑dn` in a ℚ goal — add
  `have hPQ : (P : ℚ) = … := by rw [hP]; push_cast; ring` and `rw [← hPQ]`.
* The pre-commit hook runs the full `lake build`; commit only after your own green build.

## 📁 Key files
- `DIRECTION.md` §CURRENT DIRECTIVE (binding, read-only for grind laps)
- `PENDING_WORK.md` §Reflection 2026-09-08 (the model + three refutations) and
  §GRIND 2026-09-08 (this file's design + the four paper proofs)
- `src/NormalNumbers/MahlerRunJump.lean` — the target
- `src/NormalNumbers/MahlerFareyJunction.lean` — the two-background shadow (template for the walk)
- `experiments/mahler_bg_cycle_model.py`, `…_ecap.py`, `mahler_runjump.py` — the instruments

---
**→ Next session: pick up at "Next actions" #1.**
