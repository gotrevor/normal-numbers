# Handoff: the Farey junction — the census construction is a cycle of backgrounds

**Date**: 2026-09-08 · **Branch**: `wip/adder-tower-c9` · **HEAD**: `b9d4fb8` · build green 8886 jobs, trust triple
(untracked host files `docs/mahler-universal-constant-is-one-2026-09-07.md`,
`experiments/mahler_delta_star*.py`, `scratch/` are not mine; leave them).

## 🎯 What we're doing
`DIRECTION.md` CURRENT DIRECTIVE: close the factor `3` in the uniform prime lower bound
(`1/12 → near 1/4`).  The kickoff's `g^(k+1)/4` objective had already landed (`MahlerQuarter.lean`).

## 🧠 What this lap found (details: `PENDING_WORK.md` §top)
* **The exact census optimum (`⌊p/2⌋² − {0,1,2,4}`) is a cycle of backgrounds `D ≈ p/2`**
  joined by EXACT Farey landings; the only perturbation is `1/(pDD')` one step before a
  junction.  General rule: `D → D'` leaves from `−1/(pD') (mod D)`, lands on `1/D (mod D')`,
  costs `m < D'(p − D)`.  Orbit condition at `D`: `p^e ≡ −D_prev/D_next (mod D)`.
* Family I is this with `{(p+1)/2, (p+3)/2}` in disguise (its `N₀` is `1/D₁ + 1/(pD₁D₂)`).
  **My Lean file `MahlerFareyJunction.lean` re-proves family I's bound** `⌊p/2⌋² − 2` in the
  explicit two-background form, weaker hypotheses (`p ≥ 5` odd, any `s`).  It is the base
  for the chain generalisation, not a new bound — say so, don't oversell.
* **Chain theorem (paper):** `k, …, k+t` up/down needs only `−1 ∈ ⟨p⟩ (mod k+t)`, bound
  `⌊p/2⌋² − 1 − t²`; least `t ≤ 24` for all primes `< 20000`.
* **Refuted:** orbit-free cycles with `D_i = (p+r_i)/2` (turnaround forces `r = 1`).
* **Settled:** closed-form drift-one 2-cycles: full cover mod `13440` but floor `1/16`,
  ceiling `1/5` — a per-class tool only.  Do NOT write the class theorems.
* **Open lead:** identity-closed 3-cycles with rational backgrounds, e.g.
  `(5p+7)/9, (4p+2)/9, (2p+4)/3` at `p ≡ 4 (mod 9)`, cost `5/27` unconditional — UNVERIFIED.
  A search (`scratch multibg2.py 6 12 12 3 1 7`) was running at lap end.

## 🎬 Next actions
1. Verify the 3-cycle lead with a literal `NumCert.Good` checker (generalise
   `scratch farey_cert.py`: states per background + pre-junction states, closure by orbit).
   If real, search a covering family over residue classes → unconditional `c ≈ 0.18`.
2. Chain theorem in Lean (generalise `MahlerFareyJunction.lean`; `E = p·lcm(k..k+t)`).

## ⚠️ Gotchas
* `rw [if_neg (by omega)]` / `Nat.mod_eq_of_lt (by omega)` inside `rw [...]` can elaborate
  against a metavariable goal — use `show … by omega`.
* `omega` handles products of atoms; `Nat.mod_mul_mod`, `Nat.mul_mod_mul_left` do the mod
  algebra; `lift`/`lift_le` (in the file) multiply a core inequality by a common factor
  instead of feeding degree-4 goals to `nlinarith`.
* `M_W` in `experiments/mahler_exact_M.py` returns the first COLLAPSING channel; the escape
  set is `1..M_W − 1`.

## 📁 Key files
- `src/NormalNumbers/MahlerFareyJunction.lean` — two-background certificate (new)
- `src/NormalNumbers/MahlerFamilyI.lean` — the same bound, older coordinates
- `PENDING_WORK.md` §top — full findings and scripts; `DIRECTION.md` — directive (read-only)

---
**→ Next session: pick up at "Next actions" #1.**
