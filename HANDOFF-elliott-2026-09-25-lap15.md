# HANDOFF elliott 2026-09-25 (review lap 15 + drive) — the crux is down to `a ≥ 2`

Branch `wip/elliott-port`, HEAD `9cbabb7` (this lap: `db80291` then `9cbabb7`).  Working tree
clean.  `lake build NormalNumbers.ElliottGeneral` green, 9548 jobs.
Never `lake exe cache get`.  Never edit / vendor `.lake/packages/lean-proofs-latest/`.

## Headline

`NormalNumbers.ElliottGeneral.nonasymptoticLogElliott : Erdos67b.NonasymptoticLogElliott`
(Tao 2016, Thm 1.3).  Two open leaves, both disclosed `sorry`s in `src/`:

| leaf | file | what is left |
|---|---|---|
| `dilatedSliceCMLogElliottGe` | `ElliottDilatedSlice.lean` | the multiples-of-`a` slice, **`a ≥ 2` only** |
| `nonasymptotic_of_affineCM` | `ElliottLadder.lean` | 1-bounded multiplicative → CM unimodular (untouched) |

## This lap

### 1. The crux was re-decomposed (review)

The remaining content of `DilatedCMLogElliott` is the **dilation-slice rung**.  Substitute
`m = a·n` (residue **0**, preserved by every graph dilation `m ↦ p·m`), NOT `m = a·n + c₁`
(residue `c₁`, destroyed by `p·c₁`), keeping both shifts inside the observable:

```
∑_{n∈(X/W,X]} (1/n) f₁(an+c₁) f₂(an+c₂) = a · ∑_{m∈(aX/W,aX], a∣m} (1/m) f₁(m+c₁) f₂(m+c₂)
```

`elliottLogCorrelation_eq_slice` proves this **exactly** — no boundary terms, no weight
discrepancy — because it is the dependency's own `Erdos67b.sum_elliottDilationSlice`.
`dilatedCM_of_slice` is then free.

**Refuted and recorded (do not re-derive):** the Dirichlet-character route loops.  Characters
detect `m ≡ r (a)` for `gcd(r,a)=1`, and `χ·f₁` stays CM-*unimodular* under the surrogate `χ̃`
(equal to `χ` off `p ∣ a`, `1` on `p ∣ a`).  But Möbius-removing the leftover coprimality yields
mixed-dilation correlations, which `affineCM_of_dilatedCM` returns to a common dilation, i.e. to a
slice at residue 0.  The slice rung is that loop's fixed point.

### 2. The `a = 1` case is PROVED — `src/NormalNumbers/ElliottTwoShift.lean` (new, zero sorry)

`twoShiftCMLogElliott : TwoShiftCMLogElliott` — `∑ (1/m) f₁(m+c₁) f₂(m+c₂)` for **arbitrary
integer** `c₁ ≠ c₂`, from `shiftCMLogElliott` (if `c₁ < c₂`) and `shiftCMLogElliottMirror` (if
`c₂ < c₁`, where the hypothesised `f₁` sits at the larger shift — exactly what the mirror was
proved for).

The translation estimate `norm_twoShift_le_shiftedPair_add`:
`‖twoShift f₁ f₂ c₁ c₂ X W‖ ≤ ‖shiftedPair f₁ f₂ (c₂-c₁).toNat X W‖ + 3|c₁|`, with

* `sum_harmonicWeight_shift_diff_le` — the telescoping weight bound
  `∑_{k∈s}(1/k − 1/(k+r)) ≤ r` for `s ⊆ [1,X]`, proved by splitting `Icc 1 X` inside
  `Icc 1 r ∪ Icc (1+r) (X+r)`;
* `norm_sum_window_sub_le` — the boundary bound, `2r` terms of harmonic weight `≤ 1`, via the
  symmetric-difference lemma `norm_sum_sub_sum_le_sdiff`;
* the sign of `c₁` is the only case split (forward translation via `image (·+r)`, backward via
  `filter (r < ·) |>.image (· - r)`); the vanishing of `positiveIntExtension` at `m ≤ r` handles
  the backward boundary.

The `3|c₁|` is absorbed by `Erdos67b.elliottExists_finalThreshold (3*|c₁|) 0 0`, exactly as `L₀`
is absorbed in `Erdos67b.unitCircleLogElliott`.

Wired in as `ElliottDilatedSlice.sliceCM_one` + `dilatedSlice_of_ge`, so the open rung is now
`DilatedSliceCMLogElliottGe` (`2 ≤ a`).

All new theorems `#print axioms` = `[propext, Classical.choice, Quot.sound]`.

## NEXT (lap 16)

**`dilatedSliceCMLogElliottGe`, `a ≥ 2`.**  Smallest decisive probe first: does the graph's
divisibility compose?  Read `NormalNumbers.ElliottTwistedGraph.norm_logProb_pairTwistedDivisible_sub_correlation_le`
and the dependency's `Erdos67b.norm_logProb_divisiblePair_sub_correlation_le`, and check whether
`if q ∣ n` can be replaced by `if a*q ∣ n` with the same error terms.  For a dyadic prime `q > a`,
`gcd(a,q) = 1`, so for `q ∣ n` we have `a*q ∣ n ↔ a ∣ n/q`: the correlation on the right-hand side
becomes the `a`-slice correlation, which is what the lower bound must reproduce.  If the CRT /
Hoeffding layer also tolerates the fixed extra modulus (it indexes by `ZMod p`, `p` the dyadic
primes, and `a` is coprime to all of them), the whole stack goes through with `a` as a spectator.

**Fallback if it does not compose:** restrict the prime graph to `p ≡ 1 (mod a)` — density
`1/φ(a)`, a constant — which needs Mertens in arithmetic progressions and IS a redesign.  Probe
the composition first.

**Parallel leaf:** `nonasymptotic_of_affineCM` (route in its docstring in `ElliottLadder.lean`).
