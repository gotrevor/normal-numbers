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

## Lap 23 — `C3MrtTwoShift.lean`: the truncation machinery for BOTH moduli

The `D = 2` assembly expands twice, so the truncation bound must be iterable.  Two new
sorry-free, trust-triple results:

* **`offset_truncation_bound_of_mass`** — `bridge_truncation_bound_of_mass` in the generality of
  `sum_pow_omega_offset_eq`: arbitrary finite index set `S`, arbitrary offset `c`.  That
  generality is exactly what makes it applicable a *second* time, inside the congruence
  condition the first expansion imposed.  Cost still `B · bridgeTail z Y`.
* **`progression_harmonic_mass`** — the mass hypothesis in the same generality: for any
  `S ⊆ range M`, any offset `c ≥ 1`, any modulus `e ≥ 1`,
  `∑_{n ∈ S, e ∣ n+c} ‖F n‖ ≤ c·(1 + log(M+c))/e` when `‖F n‖ ≤ (n+1)⁻¹`.
  Mechanism: inject `n ↦ (n+c)/e` into `Icc 1 ((M+c)/e)` (injective because `n + c = e·φ(n)`
  pins `n`), and pay the harmless factor `c` from `(n+1)⁻¹ ≤ c·(n+c)⁻¹`.
  `harmonic_mass_bound`'s reindexing `n = dk−1` does not survive to a general `S`; the
  injection does.

**Build hygiene note (found this lap, IMPORTANT).**  `src/NormalNumbers.lean` does NOT import
the `C3Mrt*` chain — deliberately, since the directive forbids importing a `lean-proofs-latest`
consumer into the `NormalNumbers` root.  Consequence: a bare `lake build` (and hence the
pre-commit hook) does NOT typecheck any `C3Mrt*` module.  **Always also run
`lake build NormalNumbers.C3MrtArchimedean`** (the chain tip, which now imports
`C3MrtTwoShift` as well) before claiming green.  Done for laps 20–23.

### NEXT (revised)
1. **Assemble the two-shift truncation** from the two new lemmas: apply
   `offset_truncation_bound_of_mass` with `(z₀, c = 1)` and then, inside each `d ≤ Y` term, with
   `(z₁, c = 2)`, the mass hypotheses coming from `progression_harmonic_mass`.  Total cost
   `≍ (1 + log N)·(bridgeTail z₀ Y + bridgeTail z₁ Y)`.
2. Then combine with `inner_sum_linear_forms` (CRT), `weight_transfer`, and
   `rung_two_of_named_inputs` to get the full `D = 2` correlation bound.

## Lap 24 — the joint mass with BOTH gains (a quantitative trap, found and avoided)

The naive iteration of `offset_truncation_bound_of_mass` **does not work**, and the reason is
quantitative, not structural.  The second expansion's error is
`∑_{d ≤ Y} ‖sqfW z₀ d‖ · (mass on the (d,e) progression) · ∑_{e > Y} ‖sqfW z₁ e‖`.  With the
one-condition mass `B/e` this is `(∑_{d ≤ Y} ‖sqfW z₀ d‖) · B · bridgeTail z₁ Y`, and since
`∑_{d ≤ Y} ‖sqfW z₀ d‖ ≍ Y^{1/2}` while `bridgeTail z₁ Y ≍ Y^{-1/2}`, the product is `O(1)` —
an error of the same order `log N` as the main term.  **The truncation would buy nothing.**
Only the weighted sum `∑_d ‖sqfW z₀ d‖/d`, which converges, is small enough, so the mass bound
must carry the gain of BOTH divisibility conditions.

Two new sorry-free, trust-triple results supply it:

* **`class_harmonic_mass`** — any subset of `range M` inside one class `a (mod L)` has harmonic
  mass `≤ (a+1)⁻¹ + (1 + log M)/L`.  Split at `n/L = 0` (the class's first element, `S0 ⊆ {a}`)
  and inject `n ↦ n/L` into `Icc 1 (M/L)` on the rest.
* **`joint_progression_harmonic_mass`** — for `d ∣ n+1`, `e ∣ n+2` the mass is
  `≤ 2/e + (1 + log N)/(d·e)`.  The joint condition IS one class mod `de`
  (`exists_joint_class`), giving the `1/(de)` main term; the head `(a+1)⁻¹` is NOT `O(1/(de))`
  (`a` can be `≍ d`), but `e ∣ a + 2` gives `(a+1)⁻¹ ≤ 2/e`, and that term carries no `log N`,
  so it contributes only an `N`-independent constant — absorbed by the quantifier order
  `ε → Y → A → i₀ → N → ∞`, exactly as in laps 13 and 16.
  Non-coprime `d, e` are free: the set is empty (`joint_progression_eq_empty_of_not_coprime`).

So the two-shift truncation error will be
`(1 + log N)·bridgeTail z₀ Y + (1 + log N)·M₀·bridgeTail z₁ Y + C(Y)`,
`M₀ = ∑_d ‖sqfW z₀ d‖/d < ∞` (lap 7), `C(Y)` an `N`-independent constant.  That IS `o(log N)`
after `Y` is chosen from `ε`.

### NEXT
Assemble `two_shift_truncation_bound` from `offset_truncation_bound_of_mass` (twice) with the
mass hypotheses from `progression_harmonic_mass` (outer, `c = 1`) and
`joint_progression_harmonic_mass` (inner, `c = 2`).  The inner application must be summed
against `‖sqfW z₀ d‖` over `d ≤ Y`, which is where the `1/(de)` is spent.

## Lap 25 — **`two_shift_truncation_bound`**: both moduli cut, sorry-free

    ‖ ∑_{n<N} F n · ζ₀^{ω(n+1)} ζ₁^{ω(n+2)}
        − ∑_{d,e ≤ Y} g₀(d) g₁(e) ∑_{n<N, d∣n+1, e∣n+2} F n ζ₀^{Ω((n+1)/d)} ζ₁^{Ω((n+2)/e)} ‖
      ≤ (1 + log(N+1))·bridgeTail ζ₀ Y
        + (2·sqfWPartial ζ₀ Y + (1 + log N)·sqfWMass ζ₀)·bridgeTail ζ₁ Y

for any `‖F n‖ ≤ (n+1)⁻¹` (so in particular the harmonic weight).  Two new defs:
`sqfWPartial z Y = ∑_{d ≤ Y} ‖sqfW z d‖` (`N`-independent, grows like `Y^{1/2}`) and
`sqfWMass z = ∑_d ‖sqfW z d‖/d` (finite, lap 7).

Both `bridgeTail`s → 0 as `Y → ∞` independently of `N`, so with `Y` chosen from `ε` first the
error is `ε·log N + C(ε)` — the shape the rung consumes.  The `d = 0` term needs no special
casing in the statement but does inside the mass hypothesis: `0 ∣ n+1` is empty, so the mass is
`0`, and `joint_progression_harmonic_mass` (which needs `0 < d`) is only invoked for `d ≥ 1`.

**This closes the last structural gap in the `D = 2` chain.**  Every step from the `ζ^ω`
correlation to "`ζ^Ω` along two linear forms, harmonically weighted, truncated uniformly in `N`"
is now proved and axiom-clean:
`sum_pow_omega_two_shift_eq_coprime` (expand) → `two_shift_truncation_bound` (truncate both) →
`inner_sum_linear_forms` (CRT to linear forms) → `weight_transfer` (weight variable) →
`rung_two_of_named_inputs` (Elliott + the archimedean certificate).

### NEXT
Chain those five into one statement: `∑_{n<N} (1/(n+1)) ζ₀^{ω(n+1)} ζ₁^{ω(n+2)} = o(log N)`,
conditional on the same two named inputs.  The remaining work is bookkeeping of the quantifier
order `ε → Y → A → i₀ → N → ∞` (laps 13/16 pattern), not new mathematics.

## Lap 26 — the joint inner sum brought to the rung's shape

Three changes, all sorry-free and trust-triple:

* **`weight_transfer` hypothesis relaxed** from `a < L` to `a ≤ L` (`C3MrtRungTwo.lean`; the
  proof only ever used `a ≤ L`).  This is not cosmetic: the harmonic weight is
  `1/(Lj + a + 1)`, so the offset `weight_transfer` sees is `a + 1`, and `a + 1 = L` genuinely
  occurs — exactly when `e = 1` (then `a = d − 1`, since `e ∣ a + 2` forces `e ∣ de + 1`).
  No call sites existed, so nothing else moved.
* **`filter_linear_lt_eq_range`** — the cutoff `{j : L·j + a < N}` IS the initial segment
  `range ((N−1−a)/L + 1)`.
* **`joint_inner_harmonic_le`** — peeling `j = 0` and applying `weight_transfer`,

      ‖∑_{j ≤ J} (Lj + a + 1)⁻¹ • ζ₀^{Ω(ej+b₀)} ζ₁^{Ω(dj+b₁)}‖
        ≤ ((a+1)⁻¹ + 2/L) + L⁻¹ · ‖∑_{1 ≤ j ≤ J} j⁻¹ • ζ₀^{Ω(ej+b₀)} ζ₁^{Ω(dj+b₁)}‖ ,

  `L = de`.  The right-hand sum is *exactly* the object `rung_two_of_named_inputs` bounds
  (modulo the `harmonicWeight`/`integerAffine` spelling, lap 11's `zOmInt_integerAffine`), and
  the additive cost carries no `log N`, so summed over `d, e ≤ Y` it is an `N`-independent
  constant.

`C3MrtTwoShift` now imports `C3MrtRungTwo` (was `C3MrtLinearForms`) so it can see
`weight_transfer`; chain is `C3MrtArchimedean → C3MrtTwoShift → C3MrtRungTwo → … `.

### NEXT
The remaining gap to the full `D = 2` statement is one spelling bridge plus one quantifier
assembly:
1. `∑_{1 ≤ j ≤ J} j⁻¹ • ζ₀^{Ω(ej+b₀)} ζ₁^{Ω(dj+b₁)}` vs the rung's
   `∑_{j ∈ Ioc 0 (A^m)} harmonicWeight j * zOmInt ζ₀ (integerAffine e b₀ j) * …`:
   `Erdos67b.harmonicWeight j = j⁻¹`, `Icc 1 J = Ioc 0 J`, and lap 11's
   `zOmInt_integerAffine` / `integerAffine_eq_linear_form` do the rest.  Also need
   `A^m ≤ J < A^{m+1}` and the gap `(A^m, J]` whose harmonic mass is `≤ log A + 1`.
2. `max` over the finitely many pairs `(d, e)` with `d, e ≤ Y` of the `A₀` that
   `rung_two_of_named_inputs` returns (the pattern of `range_one_certificate_uniform`,
   now over pairs).
