# HANDOFF 2026-09-20 — `RoughIndependence` split lap (N1 = N1a + N1a′ + N1b)

Branch `wip/g5-prime-subset`.  Kickoff: `KICKOFF-2026-09-20-rough-independence-lap.md`.
New file **`src/NormalNumbers/G4WiringRough.lean`** — **sorry-free**, axiom-clean
(`[propext, Classical.choice, Quot.sound]` for `isNormal_G4_of_rough`,
`crtConstantSched_of_rough`, `smoothWindowCRT`, `periodic_mean_close`,
`omegaLe_add_primorial`).  Pure addition: no existing statement was touched, no frozen
Prop was proved.

## The crux advance

`CRTConstant` (frozen, uniform in `J`, and measured FALSE in the Chowla sector) is no longer
the SD-sector input.  It is now *derived*, in schedule form, from three strictly weaker nodes:

* **N1b `RoughIndependence`** — frozen crux.  Factorisation of the window mean after the primes
  `≤ y` are stripped, error `C/(y log N)` relative to `∏‖roughSiteMean‖`.  Blueprint probe 6.
* **N1a′ `SmoothRoughDecoupling`** — frozen, *unprobed*.  Probe before proving.
* **N1a `SmoothNonvanishing`** — frozen, elementary (a CRT product over `p ≤ y`).

and the fully machine-checked small-prime half:

* `omegaR = omegaLe y + omegaAbove y`, `omegaLe_add_primorial` (primorial-periodicity),
  `truncTail_eq_smooth_add_rough`, `ePhase_truncTail_factor`, `smoothTail_add_primorial`;
* `periodic_mean_close` — `‖mean_[N,2N) F − mean_period F‖ ≤ 2P/N` for `P`-periodic `‖F‖ ≤ 1`
  (⌊N/P⌋ full blocks + two boundary blocks);
* `smoothWindowCRT` (**N1a proper**) — `S_W = c′(J)·∏ S_j + O(J·y#/N)` with `c′` the ratio of
  period averages, cut off to `0` when `‖∏ A_j‖ < δ/2`, which is what makes `‖c′‖ ≤ 2/δ`
  uniform in `J`;
* `crtConstantSched_of_rough` and `isNormal_G4_of_rough` — the wiring.

New reusable helpers: `norm_prod_sub_prod_le` (telescoping product estimate for unit-bounded
factors), `windowJ_div_tendsto_zero`, `windowJ_log_div_tendsto_zero`,
`norm_smoothSiteMean_le_one`, `norm_roughSiteMean_le_one`, `crtConstantSched_of_crtConstant`,
`fullWindowMean_tendsto_zero_of_sched`.

## Two deviations from the kickoff (both forced, both recorded in the file)

1. **`omegaLe_add_primorial` is false as written.**  At `m = 0`, `primeFactors 0 = ∅` gives
   `omegaLe y 0 = 0` while `omegaLe y (y#) = π(y) > 0`.  The theorem carries `(hm : m ≠ 0)`;
   every use site has `m = n + j + 1 ≥ 1`, so nothing downstream changes.

2. **Leaf 5 needed a different route.**  The kickoff says the `J·P/N` errors are "`≤ 1/log N`
   eventually", but the target bound is *relative*: `C/log N · ∏‖fullSiteMean‖`, and that
   product tends to `0`, so an absolute `o(1)` error cannot be absorbed.  The repair: keep the
   term relative by never bounding `‖R_W‖` by `1`.  Writing

       W − c′c_R ∏f = (W − S_W R_W) + (S_W − c′∏S)·R_W + (c′∏S)(R_W − c_R∏R) + c′c_R(∏S∏R − ∏f)

   the second term carries a factor `‖R_W‖ ≤ (B_R + |C_R|)·∏‖R_j‖`, and hD.2 + hS convert
   `∏‖R_j‖ ≤ (1+|C_D|)/δ · ∏‖full_j‖`.  What is then needed is `windowJ N · log N / N → 0`
   (new lemma, via `L³ ≤ 2^L ≤ N` and `log N ≤ L+1` with `L = log₂ N`), not `J·P/N ≤ 1/log N`.

## Next attack

* **Probe N1a′ `SmoothRoughDecoupling`** — it is the only unprobed frozen node in the new
  chain, and it is doing real work (both halves of it).  Numerically: compare
  `fullWindowMean` with `smoothWindowMean · roughWindowMean` at `y = 2, 3, 5`, and the site
  products likewise, along `J = windowJ N`.  If it fails, the split needs redesign before any
  effort goes into N1b.
* **N1b `RoughIndependence`**: the `y`-dependence `C/(y log N)` is the measured shape; the
  honest next step is a second probe at larger `y` to confirm the `1/y` and, in parallel, to
  see whether the statement can be weakened to `C/log N` (which is all the wiring uses — the
  `y` factor is never exploited in `crtConstantSched_of_rough`, which fixes `y = 2`).
  **That is a real simplification opportunity**: the wiring only ever needs `y = 2`.
* `SmoothNonvanishing` is elementary and should be provable outright (CRT over `p ≤ y`);
  it is frozen only because this lap was wiring-only.

## Post-lap addendum: the crux is narrower than it was frozen

`RoughIndependenceAt h y` (added, pure addition) is the shape the wiring actually consumes:
a **single** `y`, a constant `c : ℕ → ℂ` of one argument, and a relative error `C / log N`
with **no `1/y` gain**.  `roughIndependenceAt_of_rough` shows the frozen node implies it (for
every `y ≥ 2`), `crtConstantSched_of_roughAt` is the wiring from it, and the kickoff's
`crtConstantSched_of_rough` is now a one-line corollary — statement untouched.

So the open obligation is exactly: **`RoughIndependenceAt h 2`** — after stripping the primes
`p ≤ 2` (i.e. dividing out the parity of `ω`), the window mean factorises into its site means
with relative error `O(1/log N)`.  The measured `1/y` decay of probe 6 is head-room, not a
requirement.  A future probe should attack `y = 2` directly.
