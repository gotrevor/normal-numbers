# HANDOFF 2026-09-07 — the multi-scale bound lands: `M(g,1) ≤ (g² + 6g + 1)/4` 🧮

**Branch** `wip/adder-tower-c9`.  **Build** 🟢 green (8872 jobs).  Kickoff:
`KICKOFF-2026-09-07-mahler-quarter.md`.  Read `PENDING_WORK.md` §top for the
full account; this is the pointer.

## Landed this lap

`src/NormalNumbers/MahlerQuarter.lean` (new, imports `MahlerFarey`, trust
triple on `mahler_multiplier_quarter`, `mahler_multiplier_prime_half_of_quarter`,
`no_bad_orbit` — `#print axioms` checked).

* `mahler_multiplier_quarter` — odd prime `g`: some `m ≤ (g² + 6g + 1)/4` has
  every digit i.o. in `m·α`.  **`M(g,1) ≤ g²/4 + O(g)`**, the census constant.
  Sanity against `docs/mahler-exact-values-2026-09-07.md`: the method's minimal
  `M` (`(g+1)(g+5)/4 − 2`) is above every exact value `g = 5 … 31`.
* `mahler_multiplier_prime_half_of_quarter` — `g(g+1)/2` for `g ≥ 5` as a
  corollary (kickoff step 4).  `MahlerPrimeHalf.lean` is left in place: it is the
  only route at `g = 3` and holds the `k ≥ 2` result `mahler_multiplier_prime_gen`.
* Engine → theorem, in order: `shadow_chain` (denominator fixed when
  `Coprime g den`), `canonical_exists` / `canonical_den_lt` / `covering_canonical`,
  `stage_arith` (pure real inequality) + `stage_jump` (the `Nat.find` exit time),
  `den_grows`, `no_bad_orbit`, `mahler_multiplier_quarter_param`,
  `jump_condition_k1` (discriminant `−4μ²`).

## What differed from the kickoff's plan

* Steps 1–2 collapsed: no exit-time COUNT and no `⌈1/(M/(gQ) − 1/4)⌉` induction.
  Denominators are integers `≤ Q` and strictly increase per stage, so `Q` stages
  suffice.  The `Nat.find` is only used to locate one stage's exit.
* Step 3's `O(1/g)` loss is the single inequality `d·F ≤ d/μ` (`stage_arith`
  Step A).
* 🚨 **`k ≥ 2` is NOT reached and the kickoff's "no new idea required" is false
  there.**  If `g ∣ den`, the shadow denominator drops by `g` and the stage
  argument does not increase it.  `k = 1` is exactly where all canonical
  denominators are `< g` and hence coprime to a prime `g`.  The general
  `_param` theorem carries this as the explicit hypothesis `hcop`.

## Next lap

The drop case for `k ≥ 2` (`PENDING_WORK.md` §Next).  It is the one open
obligation on the route to `g^(k+1)/4` in general; everything else is done.
