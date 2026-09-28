# HANDOFF 2026-09-08 — escape engine proved; `(7,2)` instance is the next brick 🧮

**Branch** `wip/adder-tower-c9` · **HEAD** `5fa2846` (+ this handoff) · **Build** 🟢 green
(8877 jobs), every headline on the trust triple.  Working tree clean apart from three
untracked HOST files (`docs/mahler-universal-constant-is-one-2026-09-07.md`,
`experiments/mahler_delta_star*.py`) — not mine, leave them.

## Done this run (six laps, six green commits)

1. `dc9723d` **`MahlerLowerBoundSmooth.lean`** — `t ∣ g^j`, `t < g` ⟹ `M(g,k) ≥ t(gᵏ−1)`;
   instances `M(630,1) ≥ 393125`, `M(26250,1) ≥ 688878756`; and
   `mahler_constant_one_sharp`: ∀ `k ≥ 1`, `ε > 0`, `L`, ∃ `g ≥ L` with
   `M(g,k) ≥ (1−ε)g^(k+1)` (Dirichlet on `log 3/log 2`).  With `mahler_multiplier_lt`:
   `sup_g M(g,k)/g^(k+1) = 1`, not attained.  Closes the universal-constant wing.
2. `3aee3b8`, `bad3095` **prime lower side** — `M(17,1) ≥ 63`, `M(31,1) ≥ 224`,
   `M(59,1) ≥ 840` (beyond the census).  Burst law `B = p^j κ − 4 S_j`, `κ ≡ −8/3 (mod p)`;
   the `j = 2` family is NOT uniformly quadratic (refuted with data).
3. `93d77e0` **`MahlerLowerBoundPeriod2.lean`** — period-2 backgrounds via base `g²` and
   the Pillai bridge `digitOf_pow_digitAt`; `M(19,1) ≥ 80` exact (`1/(Q+1)` background).
4. `5fa2846` **`AdderEscapeCert.lean`** — the escape engine as a theorem:
   `EscapeCert.escape_mahler_lower_bound` (decidable `Valid` + `WitnessPair` ⟹ irrational
   `α`, block never occurs in `m·α`, `1 ≤ m ≤ M`).

## Next lap — start here

**Brick: the `(7,2)` instance `M(7,2) ≥ 176`.**  Build the 10-state certificate from
`experiments/mahler_scc_cycles.py 7 2 175 00` (states = live SCC after channel 175;
refine to one digit per state if needed).  Data to generate (Python, then `decide +kernel`):
- `lo s, hi s : ℚ` = least/greatest fixed points of `lo s = min (a s + lo s')/7`,
  `hi s = max (a s + hi s')/7` over edges (attained by eventually-periodic paths, so
  rational; iterate or solve the cycle equations).  Check `lo ≤ (a+lo')/g`, `(a+hi')/g ≤ hi`.
- carries `c s m` for `m ≤ 175`: `c s m = ⌊m·lo s⌋` should work (check `m·hi ≤ c+1`).
- witness pair: closed walks of equal length from a common state, e.g. `15·15` and `5412`
  (each needs a digit `≠ 6` and an internal non-`hi`-extremal edge; differ in a digit).
- `Valid` quantifies over `σ : Fin 3 → Fin 10` (1000 maps) × 175 channels — fine for the kernel.
Then the same engine at `k = 1`: exact `M(11,1) ≥ 25`, `M(17,1) ≥ 64` from their SCCs.

Directive (`DIRECTION.md`, unchanged): prime-base `M(p,1)`; upper side at `1/4` done, the
general prime LOWER bound is the open crux (`PENDING_WORK.md` §top has the full analysis,
refuted sub-approaches, and the two attacks).
