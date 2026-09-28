# HANDOFF c3-mrt 2026-09-25 lap93 — the open input, narrowed twice and refuted once

**Read first:** `DIRECTION.md` → CURRENT DIRECTIVE (set by review lap 91; it OUTRANKS this file).
Branch `wip/c3-mrt`, HEAD `265fc87`, tree clean, no uncommitted edits.

    lake build                                # 9257 jobs, green
    lake build NormalNumbers.C3MrtRootsInput  # green  ← current tip
    lake build NormalNumbers.C3MrtNoExcAll    # green
    lake build NormalNumbers.C3MrtSlowSched   # green

`NormalNumbers.lean` does NOT import the `C3Mrt*` chain — always build the tip explicitly.

## One-line state

`ConjC3` is a sorry-free, axiom-clean conditional theorem on ONE open statement, and that
statement has been narrowed three times this run:

    conjC3_of_geom_input       (lap 90)  ⇐ KPointNoExcWith  (cKgeom c₀ θ b) (CstKdeg m) K, ∀K
    conjC3_of_geom_input_roots (lap 93)  ⇐ KPointNoExcRoots (cKgeom c₀ θ b) (CstKdeg m) K, ∀K

for every `0 < θ < 1`, with no threshold, schedule or budget hypothesis.

## What this run did (laps 90, 92, 93; lap 91 was the review)

**Lap 90 — the threshold DISCHARGED.**  `kPointThresholdSlow_of_geom` constructs
`Athr K = 2^(2^⌈φ K⌉)`, `φ K = b^{θK}log(K+2+M₀)/(κ c₀ log 2)`, and proves all three clauses;
`two_pow_two_pow_le_cut` (ℕ: `2^{2^g} ≤ N/2^u` when `g+1 ≤ u`) plus
`ceil_thrPhi_depthSlow_add_one_le` (analytic: `⌈φ(D_N)⌉+1 ≤ u_N`) give clause (iii).  This
REFUTES lap 89's guess that the threshold fails.  `θ < 1` is spent twice and symmetrically —
saving `u^{1-θ}(log u)^{-θ}` vs `log Cst = O(log u)^m`, threshold `(u log u)^θ log log u` vs
`log log a_N ≍ u log 2` — which is why `θ = 1` is the route's structural boundary.

**Lap 92 — the `∀ i` narrowing REFUTED** (`C3MrtNoExcAll.lean`).  Weakening
`∃ i, TTNonPretentious (g i) X L` to `∀ i, …` looks free (every `depthRoot b h' i ≠ 1`, by the
new `depthRoot_ne_one_of_not_dvd_all`), but it is not: `ttNonPretentious_zOmegaNat` certifies
only `L ≤ (log X)^{ttExponent z}`, and `tendsto_ttExponent_depthRoot` proves
`ttExponent (depthRoot b h i) → 0`, so `no_uniform_ttExponent_depthRoot` — no positive `κ` serves
every factor at the single shared cutoff `L`.  Quantitatively `ttExponent(z_i) ≍ b^{-2i}`, so at
`K = D_N` even the threshold clause `L^{c_K} ≥ K+1` fails.  **Content:** the deep digits of the
Lambert constant are *almost pretentious* (`z_i` within `O(b^{-i})` of 1); only the leading root
carries usable non-pretentiousness.  The `∃ i` is the shape of the problem, not slack.
Also landed: `kPointNoExcWith_mono` (down in `cK`, up in `CstK`) — so the geometric profile is a
RATE hypothesis on constants `KPointNaturalCorrelationNoExc K` already supplies, not a new claim.

**Lap 93 — the family and shifts RESTRICTED** (`C3MrtRootsInput.lean`).  `KPointNoExcRoots` asks
the bound only for `g i = zOmegaNat (z i)`, `‖z i‖ = 1`, at consecutive shifts `i+1` — the only
instances the chain ever uses.  `kPointNoExcRoots_of_with` keeps everything; the whole chain is
rethreaded (`dyadic_window_bound_roots` … `conjC3_of_geom_input_roots`).  Free, unlike lap 92,
because the consumer has to discharge nothing new.

## NEXT (in order) — full plan in `PENDING_WORK.md` lap 93

1. **Restrict `z` to the one geometric family.**  `KPointNoExcRoots` still quantifies over all
   unimodular `z : ℕ → ℂ`; the chain only feeds `z i = depthRoot b h' i = e(h'/b^{i+1})`, and
   `depthAvg_le_roots` fixes that `z` outright — so `KPointNoExcDepth b h'` should be another
   free restriction, cutting the open statement to a single explicit sequence.  Do this FIRST.
2. **`∀ᶠ K` instead of `∀ K`.**  `KN N = max 1 (depthSlow b N - v) → ∞`, so fixed `K` matters at
   only finitely many `N`.  In `depthAvg_gen_tendsto_of_unif_roots` the `hin _` already sits
   inside a `filter_upwards`; add `hKNtop.eventually hin` to that list, then thread up.
3. Then the `Statement.lean` audit surface + ledger writeup (trigger **C3-T6**).

## Still refuted — DO NOT RETRY

Lap 89's list, plus: lap 89's own guess that the threshold fails (lap 90); the `∀ i`
non-pretentiousness weakening (lap 92, with the quantitative reason above); deriving the `K ≥ 3`
rung from `K = 2` (TT: triple correlations "not within current technology"); removing TT's
exceptional set (`exceptional_set_can_pin_a_scale`, lap 80); fixed-`K` `Tendsto` as a route to
the diagonal (lap 87 F2); the `QuantDepthElliottGen` budget layer (lap 87 F1).
