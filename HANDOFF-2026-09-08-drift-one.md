# HANDOFF 2026-09-08 — drift one: both keys proved, crux reduced to a bare existence 🧮

**Branch** `wip/adder-tower-c9` · **Build** 🟢 green (8884 jobs) · trust triple on every
theorem of the new file except the ONE disclosed `sorry` (`exists_drift_one_background`)
and the corollary that cites it.  `DIRECTION.md` CURRENT DIRECTIVE (2026-09-08 fresh-mind
review) governs; the kickoff's literal objective (`g^(k+1)/4` multi-scale) had already
landed on 2026-09-07 (`MahlerQuarter.lean`), so this lap executed the directive's
"attack the new arithmetic crux" line.

## Landed — `src/NormalNumbers/MahlerDriftOne.lean`

* `mahler_lower_bound_drift_one`: `M(p,1) ≥ D(p−1)/2 − 1` for `p, D` odd, `3 ≤ D`,
  `2D < p`, `c₂(p+1) ≡ −2 (mod D)`, `p^t ≡ −1 (mod D)`.  Both `Keys` of the
  background certificate proved for EVERY channel from the congruence (parity kills
  keyB's only bad channel; keyA is automatic below `p/2`).  Sharp: the keys fail exactly
  at `m = D(p−1)/2`.
* `exists_c₀` (source from coprimality), `driftOne_of_background`, `driftBound_mono`.
* Instances `M(127,1) ≥ 3843`, `M(101,1) ≥ 2450` — only two residue `decide`s each.
* `mahler_lower_bound_prime_drift_one`: `M(p,1) ≳ p²/6` for every prime `p ≥ 61`,
  conditional on the crux.

## The crux (disclosed `sorry`, `MahlerDriftOne.lean`)

`exists_drift_one_background`: every prime `p ≥ 61` has odd `D ∈ (p/3, p/2)`,
`gcd(D, p+1) = 1`, `−1 ∈ ⟨p⟩ (mod D)`.  Verified for all primes `61 ≤ p < 4000`
(`experiments/mahler_drift_one_probe.py`); false at `p = 23, 59`.  Attack order in
`PENDING_WORK.md` §top.

## Untracked files (not mine, left alone)

`docs/mahler-universal-constant-is-one-2026-09-07.md`, `experiments/mahler_delta_star*.py`,
`scratch/` arrived from the host/architect after the last handoff; not committed here.
