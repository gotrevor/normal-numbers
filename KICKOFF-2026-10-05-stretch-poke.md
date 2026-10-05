# KICKOFF 2026-10-05: poke the cantorexp stretch until it lands or drops to 1%

Branch `proof/cantorexp-stretch`, worktree `~/src/nn-stretch`.  Target node:
`CantorExactExponentStretch.ae_not_liouvilleWith_all` (exponent upper bound for `2 < μ₀ ≤ 3.585`),
currently 10%.  Trevor (2026-10-05): poke until it lands or the honest confidence is 1%.

**Each lap ends by restating the node's confidence** in the Stretch module doc, with what moved
it.  Every route closed gets a Maze row whose verdict rests on a declaration.  A route that
survives gets frozen statements and a plan.  New math is the goal; formalizing literature is not.

## What is already closed (do not re-walk)

- Measure-level counts (He–Liao, any Bugeaud–Durand-strength count): cap at `μ₀ > 3`
  (`endpoint_sep`, `thickening_cost_ge_one`, Maze "He-Liao local count on the forced-run measure").
- The trivial count: `bcTerm_red_mu_three` on the repo's schedule.

## Ren's seed (2026-10-05, on paper, unverified; verify each step before building on it)

Notation: a run starts at `b`, the previous run ended at `a = λb`, the bad window for exponent
`τ` is `q ≈ 3ᵐ` with `b/τ ≤ m ≤ b/(τ−1)`, and the event is `|P/3^b − p/q| < q^{−τ}` for the
Cantor-digit integer `P` (digits `0, 2`).

- **H0 (schedule-free barrier).**  Deterministic avoidance with the spacing count (rationals with
  `q ≤ Q` in a cylinder of length `3^{−a}`: `≲ Q²3^{−a} + Q`, each kills `≤ 1` integer `P`)
  succeeds iff `2/(τ−1) < λ + (1−λ) log₃2` and `1/(τ−1) < (1−λ) log₃2` hold together; over all
  `λ` this is exactly `τ > 2 + log₂3`.  So no schedule helps the trivial count.  Lean: a real
  inequality lemma; Maze row "schedule redesign for the trivial count" (refuted).
- **H1 (where the trivial count already works).**  In a run-entering window the trivial cost is
  about `3ᵐ / 2^{b−m}`, below 1 iff `m < b·log 2 / log 6 ≈ 0.387 b`.  Check against
  `bcTerm_red_mu_three` (`m = 108 = b/2`, fails) and derive the exact cutoff from the repo's
  `freeCount` formulas.
- **H2 (continued-fraction duality, large `q`).**  For `τ > 2` and large `q`, a bad `p/q` is a
  convergent of `A/B = P/3^b`.  With `r = Aq − pB`, `|r| < 3^{b−(τ−1)m}` and
  `‖r A*/B‖ = q/B < 3^{m−b}`, where `A* = A⁻¹ mod B`.  So for `m ≥ b/2` the window event becomes
  a small-denominator approximation of `θ = A*/3^b`.  Lean: an exact algebraic lemma (landable).
- **H3 (3-adic linearization).**  If the last `k ≥ b/2` ternary digits of `P` are fixed (`P ≡ P₀
  mod 3^k`), then `P⁻¹ ≡ P₀⁻¹ − P₀⁻² 3^k t (mod 3^b)` with `t` the high digits: `θ` is affine in
  `t` with slope `u = P₀⁻² mod 3^{b−k}`, which **we choose** (the low digits are free digits of
  the current stretch; needs `k ≤ (1−λ)b`, so `λ ≤ 1/2`).  Lean: exact lemma (landable).
- **H4 (chosen-frequency Riesz bound).**  The large-`q` part then needs one `P₀` for which the
  Cantor Riesz product `∏ⱼ |cos(2π h r u 3ʲ/3ⁿ)|` is uniformly small over the needed `(h, r)`.
  Price it: averaging over the `2ⁿ` admissible `P₀` mod `3ⁿ`; compute numerically first.
- **H5 (the gap).**  `0.387b ≲ m ≤ b/2` is covered by neither H1 nor H2–H4 as stated.  Under
  duality it maps to dual denominators `r ∈ [3^{b(1−(τ−1)/2)}, 3^{b(1−0.387(τ−1))}]` at the chosen
  base frequency `u`: an incidence count of `{h r P₀⁻² mod 3ⁿ}` against the Riesz product's large
  spectrum.  This is the probable crux.  Price it with a probe before any proof work.

## Order

1. Verify H0–H3 on paper and with a numeric probe (`experiments/`, with a pytest file and values
   worked by hand); fix anything wrong in a NEW statement, never by editing a frozen one.
2. State H0, H2, H3 in Lean and prove them (they are exact and should land).
3. Probe H4 and H5 numerically.  If H5 is a known-hard problem (sum-product in `ℤ/3ⁿ`), record
   it as a wall with its reopen `Prop` and lower the confidence.
4. Restate the confidence.  Stop when it is 1% with every walked route in the Maze, or when a
   surviving route has frozen statements and a plan.

Rules: commit a compiling state with named `sorry` leaves early in each lap; scoped builds
(`lake build NormalNumbers.CantorExactExponentStretch`); frozen statements byte-identical.
