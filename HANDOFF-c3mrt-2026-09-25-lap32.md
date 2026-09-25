# HANDOFF c3-mrt 2026-09-25 — laps 20–32 (SESSION WRAP)

**Branch** `wip/c3-mrt` · **HEAD** `a4bddbc` · working tree **clean** · both build targets green
at every commit.  Read first: `DIRECTION.md` → CURRENT DIRECTIVE (it outranks this file).
Detailed lap-by-lap log: `HANDOFF-c3mrt-2026-09-25-lap21.md` (laps 21–32 appended there).
Earlier batons: `-lap19.md`, `-lap18.md`, `-lap8.md` (laps 7–17), `-session-wrap.md` (1–6).

## BUILD HYGIENE — read this before claiming green

`src/NormalNumbers.lean` does **not** import the `C3Mrt*` chain (deliberately: the directive
forbids importing a `lean-proofs-latest` consumer into the `NormalNumbers` root).  So a bare
`lake build` — and the pre-commit hook — does **not** typecheck any `C3Mrt*` module.  Always run
BOTH:

    lake build                                  # 9257 jobs
    lake build NormalNumbers.C3MrtArchimedean   # the C3Mrt chain tip

Done at every commit in laps 20–32.

## Session result

**The directive's mandated move (items 1–3) is COMPLETE, and the `D = 2` rung now rests on
exactly TWO named literature inputs.**

* `nonPretentious_zOm` (lap 21) — Elliott's hypothesis for `ζ^Ω`, granted only the named
  Range-2 saving.  Range 1 (`|t| ≤ T/log X`) is **proved outright**; Range 2 is named once as
  `TwistedPrimeSumSaving` (= Vinogradov–Korobov = the dependency's own
  `PolynomialHeightPrimeCorrelationBound`).
* `rung_two_of_named_inputs` (lap 22) — the single-pair `D = 2` rung on
  `Erdos67b.NonasymptoticLogElliott` + `TwistedPrimeSumSavingAllLevels` and nothing else.
* Laps 23–32 built the whole path from the `ζ^ω` two-shift correlation down to that rung,
  in the new module `src/NormalNumbers/C3MrtTwoShift.lean` (all sorry-free, trust-triple).

## The crux is untouched

`weylLambertTwist_holds` (`SwingC3Leaf.lean`) unchanged; `conjC3_via_weylLambert` carries
`sorryAx` through it alone.

## `src/` sorry ledger for this campaign

* `weylLambertTwist_holds` — the crux (unchanged, out of scope to close).
* **`rung_two_correlation`** (`C3MrtArchimedean.lean`, added lap 29) — the `D = 2` obligation,
  stated with one disclosed `sorry`.  Deliberate: the target is visible and the remaining work
  is bounded, named and purely an ε-chase.

## NEXT — close `rung_two_correlation` (one lap, no new mathematics)

`two_shift_bound_of_rung` (lap 32) is the deterministic half.  Instantiate it with
`R = (1 + log (A^{i₀})) + ε_r · log N` and `ε_r = ε / (3·(sqfWMass ζ₀ · sqfWMass ζ₁ + 1))`:

1. `rung_two_of_named_inputs` at `ε_r` gives `A₀` per pair; `exists_common_threshold` (lap 30)
   over `range (Y+1) ×ˢ range (Y+1) ×ˢ range (Y²+1)` collapses those to one `A`, then a second
   call collapses the `i₀`'s.  (Indices: `(d, e, a)`; `b₀ = (a+1)/d`, `b₁ = (a+2)/e`; the
   determinant hypothesis is `linear_forms_nondegenerate`.)
2. `bridgeTail_tendsto` gives `Y` with `bridgeTail ζ₀ Y ≤ ε/3` and
   `sqfWMass ζ₀ · bridgeTail ζ₁ Y ≤ ε/3`.
3. The one estimate: `(Nat.log A J) · log A = log (A^{Nat.log A J}) ≤ log J ≤ log N`, which turns
   the rung's per-window `m·ε_r·log A` into `ε_r·log N`.  Needs `Nat.log A J ≥ i₀`, i.e.
   `N₀ ≥ Y²·A^{i₀} + Y²`.
4. `C` collects everything with no `log N`: `sqfWPartial`s, `3 + log A`, `1 + log A^{i₀}`, and
   the `+1` from `log(N+1) ≤ log N + 1`.

After that: feed `rung_two_correlation` into the `ConjC3` reduction and re-examine what
`weylLambertTwist_holds` still needs (`QuantDepthElliott` at `≍ log log log N` points remains
out of reach — see the directive).

## Still refuted — DO NOT RETRY

Resonance counting past `|t| ≳ (log X)^K` (short-interval-hard); crude `|ζ(1+it)| ≪ log t`
(cancels exactly at `|t| ≍ X`); naive iteration of the truncation bound without the `1/(de)` gain
(lap 24: `∑_{d≤Y}‖sqfW‖ ≍ Y^{1/2}` times `bridgeTail ≍ Y^{-1/2}` is `O(1)`, so it buys nothing);
plus the four standing refutations from the earlier wraps.  **Do not attack
`TwistedPrimeSumSaving`** — it is the named VK input.

## Confidence

* `rung_two_correlation` closable next lap: ≈ 85% (no new mathematics; the risk is Lean
  bookkeeping volume).
* `nonPretentious_zOm` faithful to `NonasymptoticLogElliott`'s hypothesis block: ≈ 95% (the
  shapes were matched deliberately and `rung_two_of_named_inputs` compiled against it first try).
* `D = 2` rung conditional on exactly two literature inputs: ≈ 85% (up from 75% at lap 19).
* leaf TRUE ≈ 95%; leaf PROVABLE with known techniques ≈ 15% (unchanged).
