# HANDOFF elliott 2026-09-25 lap 54 — DEEP REFLECTION + the two-point cover PROVED

Branch `wip/elliott-port`; this lap is the two commits `b4aa17c` (reflection synthesis) and its
child (the cover, HEAD).  Working tree clean.
`lake build NormalNumbers.ElliottAxiomAudit` green (9570 jobs).
Never `lake exe cache get`.  Never edit `.lake/packages/lean-proofs-latest/`.
**`DIRECTION.md` CURRENT DIRECTIVE was rewritten this lap and governs.  Read it first.**

## The one-paragraph version

The crux is closed and verified.  Exactly one `sorry` is left in scope,
`ElliottLadder.nonasymptotic_of_affineCM`.  This lap **refuted** the documented Case-B step for it
(the `‖g̃‖ = 1 ⋆ v` unimodularisation: its truncation level cannot be fixed before `g₁`), replaced
it with an exact finite two-point unimodular cover, and **proved the decisive probe in the kernel**
the same lap.  Registered trigger ET-1 (due lap 62) is therefore already discharged.

## What is proved and new: `src/NormalNumbers/ElliottRandomize.lean` (zero sorry, trust triple)

| name | statement |
|---|---|
| `lift b z` | `phase z * (‖z‖ ± i√(1-‖z‖²))` — the two unimodular lifts of a disc point |
| `lift_add_lift` | `lift true z + lift false z = 2 z` |
| `norm_lift` | `‖z‖ ≤ 1 → ‖lift b z‖ = 1` |
| `re_lift_mul_conj` | `(lift b z * conj z).re = ‖z‖²` — **for both signs**; this is what makes the pretentious transfer deterministic |
| `cover g Y ω m` | `∏_{i : Fin (Y+1)} if i ∈ ppIndex m then lift (ω i) (g i) else 1` |
| `cover_one`, `cover_mul_of_coprime`, `norm_cover` | `cover g Y ω` is a unimodular **multiplicative** function of `ℕ` |
| `cover_prime`, `re_cover_prime_mul_conj` | at a prime `p ≤ Y` the cover *is* a lift of `g p`, so `(u p * conj (g p)).re = ‖g p‖²` |
| `sum_cover` | `∑_ω cover g Y ω m = 2^(Y+1) · g m` for `1 ≤ m ≤ Y` — the averaging identity |
| `sum_sum_elliottLogCorrelation_cover` | the correlation of `g₁,g₂` is the average of the covers' correlations |
| **`exists_cover_pair_ge`** | **∃ unimodular multiplicative `u₁,u₂`, lifts of `g₁,g₂` at every prime `≤ Y`, with `‖corr(g₁,g₂)‖ ≤ ‖corr(u₁,u₂)‖`** |

`ElliottAxiomAudit.lean` (new, permanent) prints every load-bearing `#print axioms` in one build.

## Two things not to re-derive

1. **The `v`-expansion is dead.**  Counterexample (satisfies Case B *and* non-pretentiousness):
   `g₁ = λ·h`, `h` completely multiplicative with `h(p) = 0` exactly on a set `S` of primes all
   `> D` with `∑_{p∈S}1/p = C`.  Then `∑_{d>D}‖v(d)‖/d ≥ C` for **every** `D`.
2. **The ordering matters.**  Randomise to a *merely multiplicative* unimodular target (one moment
   per prime power → two-point law, exact, finite).  A *completely* multiplicative target would
   need `E[V^k] = r^k` for all `k`, i.e. the Poisson kernel, which has no finite support.  Complete
   multiplicativity is recovered afterwards by the squarefull convolution, whose tail bound
   `∏_p(1+2/(p(p-1))) ≤ e²` is absolute.

## NEXT (lap 55), in order

1. **`ElliottPretentiousTransfer.lean`.**  (a) The 1-bounded pretentious triangle inequality —
   `pretentiousTerm f h p ≤ 3 * (pretentiousTerm f g p + pretentiousTerm g h p)` for
   `‖f p‖,‖g p‖,‖h p‖ ≤ 1` (the dependency's `Erdos67b.pretentiousTerm_triangle_sq` needs all three
   unimodular, which `g₁` and `χ·n^{it}` are not).  Proof: `1−Re(ac̄) = [1−(‖a‖²+‖c‖²)/2] + ‖a−c‖²/2`,
   then `1−x² ≤ 2(1−x)` and `‖a−c‖² ≤ 2(‖a−b‖²+‖b−c‖²)` with `‖a−b‖² ≤ 2(1−Re(ab̄))`.
   (b) `pretentiousDistSq g u X = ∑_{p≤X}(1−‖g p‖²)/p` straight off `re_cover_prime_mul_conj`.
   (c) Conclude `MRTNonpretentious u₁ A' X` with `A' ≈ A/3 − 2·Σ_X(g₁)`.
2. Case A thin window off `ElliottHall.sum_Icc_dyadic_le` (supersedes `exists_caseA_threshold`;
   needs no regime hypothesis, so it covers all `W`).
3. `ElliottSquarefull.lean`: `u = U ⋆ μŨ`, squarefull support, absolute tail `≤ e²`, truncation.
4. `ElliottProgression.lean`: `d ∣ a₁n+b₁ ⟹ n = qk+n₀`; new pair `(a₁q, a₁n₀+b₁; a₂q, a₂n₀+b₂)`
   with determinant `q(a₁b₂−a₂b₁) ≠ 0`; `1/(qk+n₀) − 1/(qk)` sums to `O(1)`; scale `X ↦ X/q`.
5. Assembly of `nonasymptotic_of_affineCM`.

## Fidelity note (do not lose)

`Erdos67b.IsMultiplicativeOnPositiveInt` has **no coprimality hypothesis** — it is *complete*
multiplicativity.  So the dependency's `NonasymptoticLogElliott` is Tao 2016 Thm 1.3 restricted to
completely multiplicative `g₁,g₂`.  Target unchanged (the kickoff ratifies that `Prop`), but the
headline must be *described* as the CM case.  The corrected route never uses complete
multiplicativity of `g_i`, so the genuinely general form is a cheap stretch goal afterwards.
