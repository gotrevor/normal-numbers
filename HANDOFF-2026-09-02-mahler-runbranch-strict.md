# HANDOFF 2026-09-02 (autonomous): Mahler run branch at `gᵏ`, `M(g,k) < g^(k+1)`, prime conjecture refuted 🧮


Branch `wip/adder-tower-c9`, HEAD `398ceea` (+ this hash-stamp commit).  Working tree clean at hand-back; no uncommitted edits.  Budget governor stopped the lap at 04:41 UTC.
Branch `wip/adder-tower-c9`.  Every commit's pre-commit hook ran the full
`lake build` green.  `src/` sorry-free; every new theorem audits
`[propext, Classical.choice, Quot.sound]`.

## The crux and what advanced

The lap's stated crux was the **prime-base upper side** of the Mahler
multiplier chapter (`gᵏ − 1 ≤ M(g,k) ≤ g^(k+1)` for prime `g`, factor `g`
open, PENDING item "is `M(g,k) = Θ(gᵏ)` for prime `g`?").  Three advances:

1. **Run branch settled** (`MahlerRunBranch.lean`, new).  For prime `g`: if
   `0ᵏ` or `(g−1)ᵏ` occurs i.o. in `α`, some `m ≤ gᵏ` has any `k`-block i.o.
   in `m·α` (`mahler_multiplier_of_zero_runs`, `…_pred_runs`).  Four-line
   core (`cell_hit_of_coprime`): `gᵏ·x = A + ε` with the pre-run block `A`
   a unit mod `gᵏ`, take `m ≡ W·A⁻¹`.  The Liouville witnesses live in this
   branch, so it is pinned to `[gᵏ − 1, gᵏ]`; all remaining room is in the
   run-free branch.
2. **The conjecture is refuted, and the room is on the LOWER side.**  Exact
   adder-machine values (`experiments/mahler_exact_M.py`; incremental
   trimmed product, SCC-entropy exact; validated on B–B's `M(3,1) = 2`, the
   divisor family, and `B = 125` ⇒ `M(10,1) = 72`): for odd primes
   `M(g,1)` tracks `((g−1)/2)²` (`9, 25, 35, 64, 80, 120, 192` for
   `g = 7 … 29`).  So `Θ(g^(k+1))` for primes too; witnesses are Farey-hopping
   orbits below rationals `p/q`, `q < g` (mechanism in `PENDING_WORK.md`).
3. **Berend–Boshernitzan's open question answered** (`MahlerMultiplierStrict.lean`,
   new): `Mahler.mahler_multiplier_lt` gives `1 ≤ m < g^(k+1)`; ledger
   `Literature.berendBoshernitzan_strict(_holds)`.  Their p. 320: *"We do
   not know whether it is true in general that `M(g,k) < g^(k+1)`."*

## Source event this lap

The host answered `ON-LINE-REQUEST.md` with the full B–B 1994 paper
(findings harvested → `archive/findings/ON-LINE-FINDINGS-2026-09-02-berend-boshernitzan-1994.md`;
PDF at `papers/berend-boshernitzan-1994-mahler-multiples.pdf`).  Acted on:
`t(gᵏ − 1)` = their Thm 3.1, `8(10ᵏ − 1)` = their Ex 3.1 — re-attributed in
`MahlerLowerBoundGeneral.lean` / `Literature.lean` (title misattribution
"Renewal-type theorems…" fixed); their Thm 3.3 `(3/2)(g−1)` is tight for
`g = 5, 7` by our exact values and far from tight from `g = 11`.

## Commits

`e9b6ae2` MahlerRunBranch + numerics · `398ceea` MahlerMultiplierStrict + ledger
edge + attributions + findings archive + this handoff.

## Next attack (PENDING_WORK.md top, in order)

1. Formal `Θ(g²)` prime-base lower bound, `k = 1`: start with the family
   `α = c/(g−1) + Σ_{i≥2} g^(−i!)` (B–B's Thm 3.3 witness generalised;
   finite digit check per `m`), then the Farey-hopping family
   (`q = (g−1)/2`, `q'' = (g+1)/2` suggested by the data).
2. `M(5,1) = 6`, `M(7,1) = 9` as theorems (collapse certificate + witness).
3. Composite-`g` run theorem (predecessor digit coprime to `g`).
4. B–B Thm 3.2 (`(1−ε)g^(k+1)`, non-prime-powers) formalization.

Then the operator's remaining list: cited-only ledger nodes, N2/N3.
