# HANDOFF twopoint — laps 53–56, 2026-09-25: **the 🟡 `DelangeMean` is DISCHARGED**

Branch `wip/twopoint-avg`.  HEAD `ca122d6`.  Working tree **clean**; every lap committed green
(pre-commit runs `lake build`, 9294 jobs).  All new declarations `#print axioms`-clean
(`[propext, Classical.choice, Quot.sound]`).  **No `sorry` introduced anywhere this run.**

## The headline

`DelangeMean t` — cited throughout `SwingC1*.lean` as "Delange's theorem (1969), via
Selberg–Delange, KNOWN, not in mathlib" — is now a **THEOREM of this repo** on its stated regime:

    delangeMean_of_norm_lt_one : phase t ≠ 1 → ‖phase t − 1‖ < 1 → DelangeMean t
    delangeMean_one_div        : 7 ≤ b → DelangeMean (1 / b)          -- hypothesis-free instance

with NO analytic number theory: two exact hyperbola identities, Mertens' FIRST theorem, and
elementary summation.  `norm_phase_sub_one_eq` (`‖e(t)−1‖ = 2|sin πt|`) makes the regime legible:
exactly `‖t‖_{ℝ/ℤ} < 1/6`.

## Rules honoured
`twoPointWeightedAvg_all` never deleted, renamed or weakened.  No edits to `PairDecouple*.lean`,
`SwingC1*.lean`, `CastingOut*.lean`, `Maze.lean`, `papers/`, `agent-mail/`, other KICKOFFs.  All new
code in `src/NormalNumbers/TwoPointDelange{Scale,Wire}.lean` (both new), imports added to
`src/NormalNumbers.lean`.  `DIRECTION.md` edited only by lap 53 (the review lap), which owns it.

## Lap by lap

| lap | commit | result |
|---|---|---|
| 53 | `c2c1710` | **REVIEW lap.**  Direction REVISED: the kickoff's success criterion (C1 pinned to a named open problem) was already MET at WRAP 4, so the objective moves to the 🟡 `DelangeMean`.  Route decomposed into three bricks; TWO feared dependencies designed OUT (see below).  Brick 1 landed: `log_one_add_ge_sub_sq`, `log_succ_eq_mul`, `sum_logRatioStep_le'`, `gronwall_le_rpow`. |
| 54 | `bedd43e` | **Brick 2**: `exists_delangeA_le_rpow` — `A(N) ≤ C(log N)^{u'}`, `u' = u + (1−u²)/4 < 1`, unconditional, NO Mertens input. |
| 55 | `ae19852` | **Brick 3 + the closure**: `norm_one_add_mul_ofReal_le`, `one_add_rpow_ge`, `exists_norm_delangeAbel_le_rpow`, `delangeKernelMean_of_norm_lt_one`, **`delangeMean_of_norm_lt_one`**. |
| 56 | `ca122d6` | **The payoff**: `TwoPointDelangeWire.lean` — `norm_phase_sub_one_eq`, `phase_div_ne_one`, `delangeMean_one_div`, `delangeMean_div_of_abs_lt`, **`delangeMean_all_of_large`**, `conjC1_of_delangeLarge_multiElliott`, `conjC1_of_delangeLarge_pairDecorr`. |

## The two route simplifications that made it work (do NOT re-derive)

1. **Mertens' second theorem is NOT needed.**  `delangeA z = delangeS ((1+‖z−1‖ : ℝ))` — the scale
   equation's error term is itself a kernel sum at a REAL parameter — so `delange_scale_equation`
   applied at `z' = 1+u` bounds its own error, with the sharp exponent.  The repo's available form
   `primeRecipSum_le` has constant **12** and would have shrunk the discharged regime from
   `‖z−1‖ < 1` to `‖z−1‖ < 1/12`.
2. **`Complex.cpow` is NOT needed.**  The integrating factor becomes a real-`rpow` induction
   `‖Abel(N)‖ ≤ C(log N)^θ` at ANY `θ ∈ (max(Re z, u'), 1)`; no sharp exponent, no Taylor bound on
   complex powers.

Why the sign survives (and lap 35 did not): the scale equation's multiplier is `z`, of modulus
**exactly one**, so `‖1 + z·s‖ ≤ 1 + s·Re z + s²/2` keeps `Re z < 1`.  Lap 35's Gronwall normed a
multiplier of modulus `u`, destroying it.

## Cross-check against the literature
Delange: the mean is `≍ (log N)^{Re z − 1}`.  The route produces `‖S(N)‖ ≲ (log N)^{ϑ−1}` with `ϑ`
just above `max(Re z, u')`, i.e. the right exponent up to the `ε` spent in brick 2; as `u → 0`,
`ϑ − 1 → Re z − 1 = −u²/2`.  Numerically sanity-checked at `u = 1/2` and `u = 1` against the
Euler-product asymptotics of `A`, `Abel`, `S`.

## NEXT SESSION — start here

The regime `‖t‖_{ℝ/ℤ} ≥ 1/6` is **not a technical gap**.  PENDING_WORK records the diagnosis:
`Σ_n (−1)^{ω(n)} n^{-s} = ζ(s)·Π_p(1−2p^{-s}) ≈ 1/ζ(s)`, so `t = 1/2` is Möbius/PNT strength, and
Halász's theorem (the general tool) implies `Σμ(n) = o(x)` hence PNT.  Two escapes already refuted:
the Kubilius-model product route (`E ω_{>P} = Σ_{P<p≤N}1/p ≍ log log log N → ∞`, the same
obstruction as leaf (D)), and anchor bootstrapping `z^ω = y^ω * G` (the `d > √N` tail does not
decay).  So, in order:

1. **`delangeMean_of_kernel`'s crude `⌊N/n⌋` defect bound.**  It currently needs
   `Σ_{n≤N}‖h_z(n)‖ = o(N)` (`DelangeKernelTail`), which is FALSE for `u ≥ 1`.  Replace it by a
   Dirichlet-hyperbola split at `√N`, or by the identity `E_{m≤N}z^{ω(m)} = (1/N)Σ_{k≤N}H(N/k)`
   with `H(x) = Σ_{n≤x}h_z(n)`.  Note `H(x) ≍ x(log x)^{Re z − 2}` is `o(x)` for ALL `|z| = 1`,
   `z ≠ 1` — so this half may well be reachable without Halász, which would leave brick 2 as the
   only obstruction.  **This is the cheapest decisive probe and where the next lap should start.**
2. **Brick 2 past `u = 1`.**  `A(N) ≍ (log N)^u` is no longer `o(log N)`, so the scale equation's
   error swamps the main term.  This is the genuine Wirsing/Levin–Fainleib ↔ Halász boundary.
3. **Halász over `PNTPort.ZetaBounds`** (`ZetaNoZerosOn1Line`, `ZetaZeroFree9` are in tree) — the
   long-term route to the full `DelangeMean`.

## Confidence at wrap
- `DelangeMean t` on `‖t‖ < 1/6`: **DONE** (was 80% at WRAP 5).
- `DelangeMean t` for all `t ∉ ℤ` (i.e. `‖z−1‖ ≥ 1`): **20%** this decade's-worth of repo work; it
  is PNT-strength and needs item 1 then item 3.  Item 1 alone: **55%**.
- `twoPointWeightedAvg_all` TRUE: **90%**; provable with known techniques: **3%** (unchanged; not
  touched this run, and the directive forbids reopening it — it is pinned as an equivalence).
