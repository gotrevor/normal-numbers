# HANDOFF elliott 2026-09-25 laps 84–91 — the fidelity gap closed, the consumer built, the crux decomposed to two classical statements

Branch `wip/elliott-port`, HEAD `46b1158`, working tree clean, `lake build` green (9257 jobs).
Never `lake exe cache get`.  Never edit `.lake/packages/lean-proofs-latest/`.
**`DIRECTION.md` CURRENT DIRECTIVE governs — read it first.  Do NOT edit it.**

## Status against the directive

* Items **1–3 (the fidelity upgrade): DONE, lap 84.**  `ElliottGeneral.nonasymptoticLogElliottMult
  : ElliottMultStatement.NonasymptoticLogElliottMult` is proved and axiom-clean — Tao 2016 Thm 1.3
  for merely (coprime-)multiplicative `g₁, g₂`.  **Trigger EM-1 did NOT fire**: complete
  multiplicativity of `gᵢ` is consumed nowhere; three proof sites needed a coprimality argument
  threaded and nothing else moved.  `nonasymptoticLogElliott` is unchanged, now a one-line corollary.
* Item **4 (the downstream consumer): stated, derived, and its hypothesis reduced to two classical
  statements** (laps 85–91).

```
'NormalNumbers.ElliottGeneral.nonasymptoticLogElliottMult' : [propext, Classical.choice, Quot.sound]
'NormalNumbers.ElliottGeneral.nonasymptoticLogElliott'     : [propext, Classical.choice, Quot.sound]
'…ElliottCharRigidity.twoPointElliottLog_of_archimedean_and_density' : trust triple
```

## `src/` sorry inventory (Elliott scope)

Empty.  Every file below is sorry-free; the open obligations are **named `Prop`s taken as
hypotheses**, never axioms, never `sorry`.

## The chain, bottom to top (new files, laps 84–91)

| file | content |
|---|---|
| `ElliottMultStatement.lean` | `IsCoprimeMultOnPosInt`, `NonasymptoticLogElliottMult`, the free downcast |
| `ElliottTwoPointLog.lean` | `zetaOmegaInt`, its coprime multiplicativity, `UniformlyNonPretentious`, `TwoPointElliottLog`, the derivation from the headline |
| `ElliottZetaOmegaPretentious.lean` | `D(ζ^ω,χn^{it})² = M − Re(ζC)`; Mertens I harvested; near-trivial estimate; `TwistModulusDichotomy` (the crux) |
| `ElliottTwistBootstrap.lean` | clustering ⇔ `‖C‖≈M`; the power bootstrap `Δ_k ≤ k√(2ΔM)`; Euler kills the character; de-twisting; the crux from inputs (c)+(d) |
| `ElliottCharRigidity.lean` | root-of-unity gap; `PrimeDensityAP`; **(d) proved** from it |

## What is left — exactly two classical statements

1. **(c)** `ElliottTwistBootstrap.ArchimedeanCorrelationBound A η`:
   `‖∑_{p≤X} p^{-iv}/p‖ ≤ (1−η)·∑_{p≤X}1/p` for `1 < |v| log X`, `|v| ≤ A²X`.
   Zero-free region at polynomial height — the same wall the dependency names as
   `Erdos67b.PolynomialHeightPrimeCorrelationBound` and deliberately does not prove.
2. **(d1)** `ElliottCharRigidity.PrimeDensityAP A`: Mertens in progressions,
   `c·M(X) − B ≤ ∑_{p≤X, p≡a (q)} 1/p` on unit classes.  **No zero-free region** — only
   `L(1,χ) ≠ 0`.

## What the next lap does

**(d1) first — it is the softer one.**  Do a survey lap before writing analysis: `BoundedGaps`
already carries Siegel–Walfisz (`BoundedGaps.BombieriVinogradov.Analytic.SiegelWalfisz`) and the
Dirichlet L-function machinery, and `BoundedGaps.Maynard.PrimeMertens` already gave us Mertens I
(`exists_uniform_abs_primeLogHarmonicSum_sub_log`) — check for an AP analogue there and in
`PrimeNumberTheoremAnd` before deriving one.  `ArithmeticFunction.vonMangoldt.residueClass` showed
up in `PrimeMertens.lean` and is a promising handle.

After (d1), (c) is the long pole; narrow it, do not expect to clear it in one lap.

## Traps recorded this run

* `grep -c sorry` **exits 1 on a count of 0**, which silently kills an `&&` chain.  Use `;`.
* `Finset.sum_mul_sq_le_sq_mul_sq` is the Cauchy–Schwarz in this tree (not `inner_mul_le_…`).
* `fun p => (p : ZMod q) = a` elaborates with `p : ZMod q`; write `fun p : ℕ => (Nat.cast p : ZMod q) = a`.
* `pow_eq_one_iff_cases` takes `(R := ℝ)`, not `(M := ℝ)`.
* `div_le_div_of_nonneg_right` wants `0 ≤ c`, not `0 < c`.
* Euler (`Nat.ModEq.pow_totient`) beats `orderOf` for killing a Dirichlet character: `φ(q)` is one
  explicit exponent good for every `χ` mod `q`, and needs no finiteness instance.
* Quantifier order is load-bearing twice: the bootstrap's admissible `δ` shrinks with `A`, and
  rigidity's `θ` shrinks like `1/A²`.  Both had to move inside `∀ A`.

## Audit surface

`lake build NormalNumbers.ElliottAxiomAudit` prints `#print axioms` for the whole campaign
including all five new files.  All trust triple.
