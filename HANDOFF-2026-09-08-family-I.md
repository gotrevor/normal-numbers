# HANDOFF 2026-09-08 — family I is a theorem: `M(p,1) > ⌊p/2⌋² − 2` uniformly 🧮

**Branch** `wip/adder-tower-c9` · **HEAD** see `git log -1` (this commit) · **Build** 🟢 green
(8880 jobs) · trust triple `[propext, Classical.choice, Quot.sound]` on every new theorem · no
`sorry` in the new file.  Untracked HOST files (`docs/mahler-universal-constant-is-one-2026-09-07.md`,
`experiments/mahler_delta_star*.py`, `scratch/`) left alone.  `DIRECTION.md` CURRENT
DIRECTIVE (2026-09-08 review lap) governs; the 2026-09-07 kickoff it marks spent was not reopened.

## Landed — `src/NormalNumbers/MahlerFamilyI.lean` (new)

* `mahler_lower_bound_family_I (p k) (h : Hyp p k)` — for every **odd `p ≥ 17`** (primality
  unused) with `p^k ≡ −1 (mod (p+3)/2)`: an irrational `α` with no digit `p−1` in `m·α` for all
  `1 ≤ m ≤ ⌊p/2⌋² − 2`.  The first **uniform-in-`p`** quadratic lower bound on the prime side,
  within `2` of the exact census at every covered prime.
* `mahler_lower_bound_prime_family_I` — prime-facing form; instances `M(41,1) ≥ 399` (new point),
  `M(199,1) ≥ 9799`.
* Engine reuse: `AdderEscapeCert.escape_mahler_lower_bound` with a symbolic `EscapeCert p`
  (states `Fin (D+2)`, uniform slack `4/(p³D)`, carries `⌊m·num/E⌋`).  The certificate reduces to
  four residue inequalities (`key_far`, `key_junction`, `key_n0`, `key_nm1`); the last is sharp at
  `m = n² − 1` (`m ≡ 3 mod D`, `⌊m/D⌋ = n−2`), which is exactly why the bound is `n² − 2`.
* Generic pieces worth reusing for the next junction certificate: `edge_data` (every edge is
  `dig·E + num' = p·num + δ`), `chDigit_eq`, `isClosedWalk_periodic`, `not_hiMax_of_edge`.
* `experiments/mahler_family_I_cert_check.py` is the exact Python evaluator of this certificate.

## Next lap — start here

Close the remaining primes (those with `−1 ∉ ⟨−3⟩ mod D`): a second junction returning from the
coset of `−1` to the coset of `1`, or a different background denominator whose dynamics puts
`−1` in the orbit of `1`.  Detail and order in `PENDING_WORK.md` §top.  The Lean template is
in place: only `num`/`dig`/the keys/the walks change for a new one-junction family.
