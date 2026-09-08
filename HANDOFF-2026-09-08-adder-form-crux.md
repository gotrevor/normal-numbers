# HANDOFF 2026-09-08 — the prime lower side is now a long addition 🧮

**Branch** `wip/adder-tower-c9` · **Build** 🟢 green (8878 jobs) · every headline
on the trust triple.  Working tree clean apart from three untracked HOST files
(`docs/mahler-universal-constant-is-one-2026-09-07.md`,
`experiments/mahler_delta_star*.py`) — not mine, leave them.

**This was a REVIEW lap.**  `DIRECTION.md` CURRENT DIRECTIVE was rewritten and
OUTRANKS this handoff; `STATUS.md` refreshed; the crux analysis is
`PENDING_WORK.md` §top.

## Direction change (read this first)

The 2026-09-07 kickoff ("finish the multi-scale bound to `g^(k+1)/4`") is
**spent**: the `k = 1` upper side is proved (`mahler_multiplier_quarter`) and the
constant `1/4` was already refuted at `k = 2` by exact data.  The single open
crux is now named precisely:

> **`M(p,1) ≥ c·p²` for EVERY prime `p`** — a uniform statement, not one more
> per-prime certificate.

## Landed this lap — `src/NormalNumbers/MahlerBurstDigit.lean` (new, trust triple)

1. **The adder form.**  `bgCarry`, `bgDigit` = the carry/digit of the school long
   addition "constant background `b` + burst `N`"; `bgResidue_div_eq_bgDigit`
   identifies the window digit at distance `d = i+1` with the digit emitted at
   position `i`.  `mahler_lower_bound_bg_adder` restates the `k=1` bound with
   **one condition per digit position**, and drops `hstab` entirely (the carry
   dies on its own once the burst runs out — `bgDigit_of_lt`).
   *Why it matters:* the window form re-derives the whole addition for each `d`,
   so it can only ever be `decide`d.  The adder form is what a **uniform-in-`p`**
   proof can be written against.
2. **First uniform brick — `bgDigit_zero_ne`.**  Odd `g ≥ 5`, `Q = (g−1)/2`, any
   burst with `B ≡ −4 (mod g)`: position `0` misses the target `g−1` for **every**
   `m < Q²`.  (Digit sum `≡ 2(u−r) (mod g)`; `≡ −1` forces `g ∣ 2(u−r)+1`, odd and
   `≤ g−2`.)  `Q² = ⌊g/2⌋²` is exactly the census value of `M(p,1)`.
3. **`mahler_lower_bound_base29` : `M(29,1) ≥ 140`** — engine validated
   end-to-end, `decide +kernel`, and its burst obeys the `B ≡ −4 (mod 29)` law.

## The two laws, and the tower (detail in PENDING_WORK §top)

* **Law 1 (proved):** `B ≡ −4 (mod p)`.  Empirically the lowest base-`p` digit of
  the extremal burst is `p−4` at every prime `7 … 59`.
* **Law 2 (derived + confirmed at `p = 7,11,13,17,19,23`, NOT yet Lean):**
  with `QB = pλ + 2`, position `1` needs `λ ≡ −2 (mod p)`.  The failure locus is
  an AP in `r` with difference `2(1+λ⁻¹)`; `λ ≡ −2` makes it `1`, and the carry
  `c₁ = [u ≥ r]` shifts the constant by `Q`, pushing every failure to `u > Q`.
  This **explains** the previously recorded `κ ≡ −8/3 (mod p)` law.
* **Tower:** integrality forces `λ ≡ −2 (mod Q)` too, so `λ = pQℓ − 2` and the
  level-2 integer is `ℓm − 1` — one new parameter per base-`p` digit of `B`,
  pinned mod `p` by that level.  Level 2 wants `ℓ ≡ −4` or `−4/3 (mod p)`.
  Past level 2 the floors break affinity: no closed form.

## ⛔ Refuted this lap — do not retry

`B = p²−4`, `B = p²(p−4)−4`, and the whole shape `B = p^K(p−c) − 4`: all only
`Θ(p)` (the higher digits of `I` kill them).  Also: a junction certificate with
two DIFFERENT backgrounds is **unsound** unless the return junction is certified
too (that bug produced `M` above the census), and the burst must approach the
background from ABOVE (`Δ > 0`).

## Route evidence (settled)

Exact digit-DFS max-`M` for the burst family, `M/⌊p/2⌋²`:

    p    7    11   13   17   19   23   29   31   37   41   43   47   53   59
         .78  .92  .94  .97  .58  .98  .71  .99  .61  .44  .52  .44  .44 1.00

Never below `0.43` — the family **is** uniformly quadratic; the gap to a theorem
is a formula for `B`, not existence.

## Next lap — start here

1. Measure the reachable `c` for **length-3** bursts
   (`experiments/mahler_burst_tower.py`, restrict to `K = 3`).  A three-digit
   burst makes the tower terminate: positions `≥ 3` are the `bgDigit_of_lt` tail.
2. Then prove `bgDigit_one_ne` (position 1) uniformly in Lean, and assemble
   `M(p,1) ≥ c·p²` for all primes `p ≥ p₀`.
3. Fallback: the generalized junction certificate
   (`experiments/mahler_junction_cert.py`), background = any `c/D` with `D < p`.

New scripts: `experiments/mahler_burst_tower.py` (exact digit-DFS for `B`),
`mahler_burst_maxm.py` (max `M` for a given `B`), `mahler_junction_cert.py`
(the generalized junction model).
