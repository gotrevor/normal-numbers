# Handoff: `MahlerRunJump.valid` proved — the run+jump certificate is sorry-free

**Date**: 2026-09-08 · **Branch**: `wip/adder-tower-c9` · build green **8887 jobs**
· `#print axioms RunJump.valid` = `[propext, Classical.choice, Quot.sound]`.

## 🎯 Directive — READ `DIRECTION.md` §CURRENT DIRECTIVE FIRST (it outranks this baton)

Objective: pin `M(p,1)`; mandated move = `src/NormalNumbers/MahlerRunJump.lean`, then the two
`b ∣ p+1` corollaries.  (The 09-07 kickoff's `g²/4` objective already landed on 09-07 — see
`PENDING_WORK.md` §"THE MULTI-SCALE BOUND LANDED AT `k = 1`"; the kickoff is stale on that point.)

## ✅ This lap

All four sub-`sorry`s of the last handoff (`edges`, `carries`, `recursion`, `block`) are PROVED,
by ONE mechanism: the generic two-denominator edge lemma (`gen_*`) + three edge-type instances
(`edge_data`) + the carry inequality (`carry_data`).  The whole content is `cost_ge`
(`M < Dn i·(p − Dh i)`, minimum `b(p−b−1)` at both ends of the run) and `jmod` (the junction residue).
Full account + six Lean gotchas: `PENDING_WORK.md` §GRIND 2026-09-08 (lap 2).

## 🎬 Next actions, in order
1. `Data` existence from `p` prime, `3 ≤ b`, `2b < p`, `−1 ∈ ⟨p⟩ (mod b)`: `al i = p⁻¹ mod Dh i`,
   `ap i = 1`, `dj i = (p·al i − 1)/Dh i` for `i ≥ 1`; the closing jump at `i = 0` uses `hord`.
2. The closed walk through every junction with mixing (template `MahlerFareyJunction.lean`).
3. `mahler_lower_bound_runjump : M(p,1) > b(p−b−1) − 1`, then `b = (p+1)/3` (`2/9`) and
   `b = (p+1)/4` (`3/16`).

## 📁 Key files
- `DIRECTION.md` §CURRENT DIRECTIVE (binding) · `PENDING_WORK.md` §GRIND 2026-09-08 (lap 2)
- `src/NormalNumbers/MahlerRunJump.lean` (sorry-free certificate; theorem still to state)
- `src/NormalNumbers/MahlerFareyJunction.lean` (walk template)
