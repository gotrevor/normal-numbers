# HANDOFF c3-mrt 2026-09-25 — lap 33: the D=2 rung is CLOSED

**Branch** `wip/c3-mrt`.  Both targets green: `lake build` (9257 jobs) and
`lake build NormalNumbers.C3MrtArchimedean`.  Read `DIRECTION.md` first; prior baton
`HANDOFF-c3mrt-2026-09-25-lap32.md`.

## Advance

`rung_two_correlation` (`C3MrtArchimedean.lean`) — the log-averaged `D = 2` correlation of
`ζ₀^ω`, `ζ₁^ω` at the shifts `n+1`, `n+2` — is **proved**, axiom-clean
`[propext, Classical.choice, Quot.sound]`.  The campaign's only remaining `src/` sorry is the
crux `weylLambertTwist_holds` itself.

So: **`ConjC3`'s `D = 2` rung now rests on exactly two named literature inputs**,
`Erdos67b.NonasymptoticLogElliott` and `TwistedPrimeSumSavingAllLevels` (= Vinogradov–Korobov),
with everything between them machine-checked.

## What landed

* `rung_two_uniform` (new) — collapses the per-pair `A₀` and `i₀` that
  `rung_two_of_named_inputs` returns to ONE base `A` and ONE starting exponent `I`, uniformly
  over the finitely many triples `(d, e, a)` with `d, e ≤ Y`, `a < d·e`.  Two applications of
  `exists_common_threshold`; the `i₀` collapse works because enlarging `i` only enlarges the
  bound's constant term `1 + log (A^i)`.
* `rung_two_correlation` — the ε-chase, in the order `ε → εr → Y → A → I → N₀`:
  - `εr = ε / (3·(sqfWMass ζ₀ · sqfWMass ζ₁ + 1))`, so the rung's contribution to the
    `log N` coefficient is `εr·M₀M₁ ≤ ε/3`;
  - `Y` from `bridgeTail_tendsto` with `bridgeTail ζ₀ Y ≤ ε/3` and `M₀·bridgeTail ζ₁ Y ≤ ε/3`
    — the other two thirds;
  - `N₀ = Y²·A^I + Y² + 2` forces `Nat.log A ((N−1−a)/(d·e)) ≥ I` for every admissible pair;
  - `m·log A = log (A^m) ≤ log ((N−1−a)/(de)) ≤ log N` turns the rung's per-window
    `m·εr·log A` into the single `εr·log N`, which is what makes `R` uniform in `(d,e,a)`;
  - `log (N+1) ≤ 1 + log N` absorbs the truncation error's `N+1`.

## NEXT

1. Feed `rung_two_correlation` into the `ConjC3` reduction chain (`C3MrtShape` /
   `C3MrtSchedule`) and see exactly which `QuantDepthElliott` instance at `D = 2` it discharges
   — i.e. state the `D = 2` case of the schedule as a corollary with no `sorry`.
2. Then the wall is unchanged: `QuantDepthElliott` at `≍ log log log N` points.  The honest
   next research move is `D = 3`: whether `Erdos67b.NonasymptoticLogElliott`'s statement is
   `k`-point or strictly 2-point, and if 2-point, what the `D = 3` analogue must be named as.

## Still refuted — DO NOT RETRY

Unchanged from lap 32's list (resonance counting past `|t| ≳ (log X)^K`; crude `|ζ(1+it)|`;
naive iteration without the `1/(de)` gain; smooth/rough Kubilius split; self-similar recursion;
growing `P`; direct `unitCircleLogElliott`).  Do not attack `TwistedPrimeSumSaving`.

## Confidence

* `D = 2` rung conditional on exactly two named literature inputs: **done, in-kernel** (was 85%).
* leaf TRUE ≈ 95%; leaf PROVABLE with known techniques ≈ 15% (unchanged).
