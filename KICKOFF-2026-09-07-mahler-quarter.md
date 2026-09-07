# KICKOFF 2026-09-07 — finish the multi-scale bound to `g^(k+1)/4` 🧮

**Engine**: Claude, model `fable`, effort `low`.  **Branch**: `wip/adder-tower-c9`.
**Read first**: `DIRECTION.md` CURRENT DIRECTIVE (2026-09-02, still in force),
then `PENDING_WORK.md` §top ("THE MULTI-SCALE ARGUMENT REACHES `g^(k+1)/4`").

## The objective

The complete argument is on paper and its engine is already in `src/`
(`MahlerFarey.lean`, trust triple).  What is open is chain/exit-time
bookkeeping — **no new idea is required**, which is why this runs at `low`.
Four steps, in order, from `PENDING_WORK.md`:

1. The exit time `n*` as a `Nat.find` on "shadow defect `≥ 1/Q`", and the
   shadow-defect recursion `E_{i+1} = g·E_i` extracted from `orbit_escapes`
   (which currently proves the recursion and then discards it).
2. The stage iteration as an induction of `⌈1/(M/(gQ) − 1/4)⌉` steps on the
   denominator, each step one application of `den_jump_of_bad`.
3. Carry the `O(1/g)` loss (`a·(defect σ) ≤ Q/(2Q+1)`, not `1/2`) so the
   constant lands at `1/4 + O(1/g)` rather than `1/2`.
4. Then retire `mahler_multiplier_prime_half` to a corollary.

**One coherent green commit per lap.**  A disclosed sub-`sorry` in `src/` that
decomposes a step is a valid checkpoint and counts as the lap's advance — do not
avoid raising the `sorry` count to make a step look finished.

## New host evidence (2026-09-07) — use it as a tripwire, not as a lemma

`docs/mahler-exact-values-2026-09-07.md` adds the exact census `M(g,1)` for
`g = 2 … 32`.  Two consequences for this lap:

- 🎯 **The target constant is confirmed.**  `M(p,1)/p²` = `.240 .184 .207 .207
  .221 .222 .227 .228 .233` at `p = 5 … 31`, climbing toward `1/4` from below,
  and `M(p,1)` sits at `⌊p/2⌋²` minus `0`, `1` or `4` at every prime from 7 to
  31.  `⌊p/2⌋²` is exactly the value at the engine's double root `a = Q/2`.  So
  a proof that lands **below** `⌊p/2⌋²` at any of those primes has a bug —
  check any intermediate bound against the table before believing it.
- 🚨 **`M(5,1) = 6 > ⌊5/2⌋² = 4`** is the one base where the shape inverts.  If
  a step needs `g` large, say so in the statement rather than silently assuming
  it.

## Scope fence

Unchanged from the DIRECTIVE: `CFScheduleA.lean` fenced, Comparator statement
holes fenced, no repo-wide sorry-free gate, no paper downloads, **no outward
actions**, do not edit `DIRECTION.md` (altitude laps own it).  Claim hygiene:
Berend–Boshernitzan constants here are tier-S secondary sources — state OUR
quantifiers, never attribute, and do not headline "beats B–B".

## Launch (Trevor fires)

    lean-treadmill start normal-numbers --engine claude --model fable --effort low \
      --max-duration 8h --review-every 3 --reflect-every 9 \
      --prompt "Execute KICKOFF-2026-09-07-mahler-quarter.md: finish the multi-scale bound to g^(k+1)/4. One coherent green commit per lap." \
      --allow-from-agent
