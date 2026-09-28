# HANDOFF c3-mrt 2026-09-25 lap90 — the threshold is DISCHARGED; the headline rests on ONE input

**Read first:** `DIRECTION.md` → CURRENT DIRECTIVE (refreshed this lap, review 91).  Branch
`wip/c3-mrt`, tree clean.  Tip module `NormalNumbers.C3MrtSlowSched` (build it explicitly —
`NormalNumbers.lean` does not import the `C3Mrt*` chain).

    lake build                              # 9257 jobs, green
    lake build NormalNumbers.C3MrtSlowSched # green

## One-line state

    conjC3_of_geom_input :
      (∀ b ≥ 3, ∀ K, KPointNoExcWith (cKgeom c₀ θ b) (CstKdeg m) K) → ConjC3     (0 < θ < 1)

No threshold hypothesis, no schedule hypothesis, no budget layer.  `ConjC3` is a conditional
theorem on exactly ONE open statement.

## What moved, and why it is the crux advance

Lap 89's NEXT ① guessed that `KPointThresholdOKWith` FAILS for the geometric profile.  It does
not.  The guess mis-estimated the available budget `log log a_N` as `log u_N`; since
`2^{u_N} ≍ log₂ N` it is in fact `≍ u_N · log 2`, a full power of `u_N`.  The demand at the
diagonal level `K = D_N` is `log log Athr(D_N) ≳ b^{θ D_N} log D_N ≍ (u log u)^θ log log u`,
which for `θ < 1` is `o(u)`.  So the threshold is a THEOREM, and this lap proves it:

    φ K    = b^{θK} · log(K+2+M₀) / (κ c₀ log 2)          (`thrPhi`)
    Athr K = 2 ^ (2 ^ ⌈φ K⌉)                               (`thrAthr`)

* clause (i) `2 ≤ Athr K` — `two_le_thrAthr`.
* clause (ii) `max(max 2 (K+1), Q·primorial P) ≤ (2 log Athr K)^{κ c_K}` — `thrAthr_rpow_ge`.
  `(2^g)^{κc₀b^{-θK}} = exp(g·κc₀b^{-θK}·log 2) ≥ exp(log(K+2+M₀))` exactly when `g ≥ φ K`,
  which `Nat.le_ceil` supplies; `pow_ceil_le_two_log_thrAthr` passes from `2^g` to `2 log Athr K`.
* clause (iii) `Athr K ≤ N/2^{u_N}` for all `K ≤ depthSlow b N` — `thrAthr_monotone` reduces to
  `K = D_N`; then `two_pow_two_pow_le_cut` (pure ℕ: `2^{2^g} ≤ N/2^{u}` whenever `g+1 ≤ u`,
  since `2^g + u ≤ 2^{u} ≤ log₂ N`) and the one analytic step
  `ceil_thrPhi_depthSlow_add_one_le : ⌈φ(D_N)⌉ + 1 ≤ u_N` eventually.

The analytic step, with `y = u_N+1`, `t = log y`:
`φ(D_N) ≤ C'·y^θ·(2+3t)²` (from `pow_depthSlow_le_log`, `depthLL_succ_le_log`,
`Real.log_le_sub_one_of_pos`), and `(C'+1)(2+3t)² ≤ exp((1-θ)t)` eventually by
`tendsto_exp_div_polyPow (1-θ) 2`; multiply by `y^θ` and use `y^θ·exp((1-θ)t) = y`.

**Why `θ = 1` is structural, now visible on BOTH sides.**  The saving needs
`u^{1-θ}(log u)^{-θ}` to beat `log CstKdeg = O(log u)^m`; the threshold needs
`(u log u)^θ log log u` to fit inside `u·log 2`.  Same `u^{1-θ}` margin, spent twice.  Widening
past `θ = 1` needs a different lever than the schedule or the threshold.

## New declarations in `src/NormalNumbers/C3MrtSlowSched.lean` (pure addition, 12)

`thrPhi`, `thrAthr`, `two_le_thrAthr`, `pow_ceil_le_two_log_thrAthr`, `thrPhi_monotone`,
`thrAthr_monotone`, `thrAthr_rpow_ge`, `add_one_le_two_pow`, `two_pow_two_pow_le_cut`,
`ceil_thrPhi_depthSlow_add_one_le`, `kPointThresholdSlow_of_geom`,
`weylLambertTwist_of_geom_input`, `conjC3_of_geom_input`.

All `[propext, Classical.choice, Quot.sound]`.  The `C3Mrt*` chain still has zero `axiom`s and
zero `sorry`s; nothing earlier was weakened, renamed or deleted.

## NEXT (in order) — see `PENDING_WORK.md` lap 91 for the full plan

1. `depthRoot_ne_one_of_not_dvd_all` — `depthRoot b h' i ≠ 1` for EVERY `i` when `¬ b ∣ h'`.
2. `KPointNoExcAllWith` — `KPointNoExcWith` with `∃ i, TTNonPretentious (g i)` weakened to
   `∀ i, …`.  Strictly less assumed, and ① shows the C3 consumer can still meet it.
3. Rethread `dyadic_window_bound_K` (the `∃ i` is used at `C3MrtKPointNoExc.lean:133` and
   nowhere else), its `_with` twin, `depthAvg_gen_tendsto_of_geom_slow`,
   `depthDiagonalSlow_of_geom`, and the two headline forms.
4. `kPointNoExcWith_mono` (down in `cK`, up in `CstK`) — pins the geometric profile as a
   degradation-RATE hypothesis on constants `KPointNaturalCorrelationNoExc K` already supplies.
5. Then: can `∀ K` be weakened to `∀ᶠ K`?

## Still refuted — DO NOT RETRY

Lap 89's list, plus: **lap 89's own NEXT ① guess** that the threshold fails for the geometric
profile (refuted in the kernel this lap).  And: deriving the `K ≥ 3` rung from the `K = 2` rung —
TT state in print that triple correlations are "not within current technology".
