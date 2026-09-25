# HANDOFF c3-mrt 2026-09-25 — laps 21–22

**Branch** `wip/c3-mrt` · working tree clean · `lake build` green (9257 jobs).
Read first: `DIRECTION.md` → CURRENT DIRECTIVE (it outranks this file).
Prior batons: `-lap19.md`, `-lap18.md`, `-lap8.md`, `-session-wrap.md`.

## The directive's mandated move is DONE (items 1–3)

`src/NormalNumbers/C3MrtArchimedean.lean` now carries the FULL archimedean
non-pretentiousness certificate for `ζ^Ω`, assembled on exactly ONE named open input.

| name | content | axioms |
|---|---|---|
| `range_one_certificate` (lap 20) | `|t|·log X ≤ T ⟹ A ≤ dist`, all large `X`, uniform in `χ` | trust triple |
| `range_one_certificate_uniform` | same, merged over all moduli `q ≤ Q` (induction on `Q`, `max` of thresholds) | trust triple |
| `TwistedPrimeSumSaving A T` | **the named Range-2 input**: `T/log X ≤ |t| ≤ A·X ⟹ ‖∑_{p≤X} χ(p)p^{it}/p‖ ≤ primeReciprocals X − A` | — (a `Prop`) |
| `range_two_certificate` | Range 2 from the named input, two lines via `pretentiousDistSqToTwist_zOm_ge` | trust triple |
| `nonPretentious_zOm` | **Elliott's hypothesis for `ζ^Ω`**, granted `TwistedPrimeSumSaving`: `∀ q ≤ A, ∀ χ, ∀ |t| ≤ A·X`, `A ≤ pretentiousDistSqToTwist (ζ^Ω) χ t X` for all large `X` | trust triple |

The two ranges cover `ℝ` because `X ≥ 2` makes `log X > 0`; the split is `|t|·log X ≤ T` vs not.

**Why the ceiling `|t| ≤ A·X` is essential** (recorded in the module docstring): by simultaneous
Diophantine approximation there are arbitrarily large `t` with `t·log p` near `0 (mod 2π)` for
every `p ≤ X` at once, so the saving is genuinely FALSE without a ceiling.  `NonasymptoticLogElliott`
(`LogElliott.lean:411`) asks for precisely `|t| ≤ A·X`, so the shapes match.

## Lap 22: the `D = 2` rung now rests on exactly TWO named inputs

`rung_two_of_named_inputs` (same module, trust-triple, first compile): granting
`Erdos67b.NonasymptoticLogElliott` **and** `TwistedPrimeSumSavingAllLevels`
(`∀ A, ∃ T, TwistedPrimeSumSaving A T` — the level grows with the cutoff exponent, so the
saving is needed at each level), the harmonic-weighted two-point correlation of `ζ₀^Ω` and
`ζ₁^Ω` along a nondegenerate affine pair is `≤ (1 + log A^{i₀}) + m·ε·log A` on the initial
segment, i.e. `o(log J)`.  **Nothing else is assumed** — the archimedean certificate is proved.

The wiring was pure plumbing (the shapes were matched in lap 21 deliberately).  The one
arithmetic point: `initial_segment_bound_of_elliott` wants non-pretentiousness at every cutoff
`A^i` with `i > i₀`, while `nonPretentious_zOm` gives it for `X ≥ X₀`; take `i₀ = X₀` and use
`A ≥ 2 ⟹ A^i ≥ 2^i > i > X₀` (`Nat.lt_two_pow_self` + `omega`).

**This is the ratified success criterion met at the `D = 2` rung:** an equivalence with named
open problems, both of them the Erdős-67b project's own open analytic bets.

## NEXT — resume here

1. **The tuple sum over coprime powerful pairs `d, e ≤ Y`** — laps 8–13 supply weight transfer,
   truncation and the window stack.  This is what lifts the single-pair rung to `ConjC3`'s
   `D = 2` obligation.
2. Then re-examine what `weylLambertTwist_holds` still needs beyond the `D = 2` rung
   (`QuantDepthElliott` at `≍ log log log N` points remains out of reach — see the directive).

## Still refuted — DO NOT RETRY
Lap 18's two (resonance counting past `|t| ≳ (log X)^K` is short-interval-hard; crude
`|ζ(1+it)| ≪ log t` cancels exactly at `|t| ≍ X`), plus the four standing ones.
Do NOT attack `TwistedPrimeSumSaving`.

## Confidence
* `nonPretentious_zOm` faithful to `NonasymptoticLogElliott`'s hypothesis block: ≈ 90%
  (shapes were matched deliberately; item 1 is the check).
* `D = 2` rung conditional on exactly two literature-proved inputs: ≈ 80% (up from 75%).
* leaf TRUE ≈ 95%; leaf PROVABLE with known techniques ≈ 15% (unchanged).
