# HANDOFF 2026-09-08 — every burst position is an affine congruence; Law 2 proved 🧮

**Branch** `wip/adder-tower-c9` · **Build** 🟢 green (8879 jobs) · trust triple on
all new theorems.  Untracked HOST files (`docs/mahler-universal-constant-is-one-2026-09-07.md`,
`experiments/mahler_delta_star*.py`) left alone.  `DIRECTION.md` CURRENT DIRECTIVE
(2026-09-08 review lap) still governs; this lap executed its first mandated move.

## Landed — `src/NormalNumbers/MahlerBurstCarry.lean` (new)

* `carryG`, `digit_of_carry`: digits of ANY integer-coefficient expansion
  `Σ F_j g^j` are `G_j mod g`, `G_{j+1} = F_{j+1} + ⌊G_j/g⌋`.
* `bgDigit_family`: the `a = 2` family's adder digit at position `i` equals
  `G_i mod g` with `F_j = 2r + e_j m` for any integer digits `B = Σ e_j g^j`.
  Every position is an affine congruence in `(u, r)` plus a bounded carry —
  uniformly in `g`.  The `decide`-only window form is no longer in the way.
* `bgDigit_one_ne` (**Law 2**): `B ≡ −4 (mod g²)` ⟹ position 1 safe for all
  `m < Q²`.  With `bgDigit_zero_ne`, positions 0 and 1 are uniform theorems.

## Found / measured (detail in `PENDING_WORK.md` §top)

* Position 1 has exactly two safe continuations: the `g`-adic ideal
  (`e_1 = −2`, never terminates) and Law 2 (`e_1 = 0`, **self-similar**:
  `B = g²ℓ − 4` is the same problem for `ℓ` with twist `−[u>r]`).
* Length-≤3 bursts: `c ≥ 0.30` at `p ≤ 61` but drifting down; small fixed
  signed digits give `c ~ 1/p`.  The top digit must scale with `Q`; the
  DIRECTIVE's "terminate at length 3" is probably capped.

## 🎯 Found late in the lap — family I (detail in `PENDING_WORK.md` §top)

Background `1/D`, `D = (p+3)/2`, ONE junction digit, `M = ⌊p/2⌋² − 2` at every
prime `17 … 199` where `−1 ∈ ⟨−3⟩ (mod D)` (29 % of primes below 2000).  It is a finite
escape certificate (`AdderEscapeCert.lean`) whose validity is three explicit
inequalities in `m mod D` — the first genuinely uniform quadratic construction.

## Next lap — start here (revised)

Formalize family I: build `EscapeCert p` symbolically (far states
`[c/D, c/D + 2/(p³D)]`, near states `T₋₁, T₀`, junction edge digit `1`) and
prove `Valid` for all such primes; `escape_mahler_lower_bound` then gives
`M(p,1) ≥ ⌊p/2⌋² − 2`.  Then close the cycle for the remaining primes.  The old
pointer below is superseded unless this stalls.

## Old pointer

Search for a top digit `ℓ_K = αQ + β` (small rational `α`, parity-of-`u`
split allowed) with a short signed tower holding `c ≥ 1/8` on all primes
`≤ 200` (`experiments/mahler_signed_digit_tower.py` is the exact evaluator);
transcribe via `bgDigit_family` + `ediv_small` + `omega`.  Fallback: the
generalized junction certificate.
