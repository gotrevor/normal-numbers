# HANDOFF elliott 2026-09-25 laps 25–26 — the dilated upper bound is assembled; the lower half is started

Branch `wip/elliott-port`.  `lake build` green.
Never `lake exe cache get`.  Never edit / vendor `.lake/packages/lean-proofs-latest/`.

## Headline

`NormalNumbers.ElliottGeneral.nonasymptoticLogElliott : Erdos67b.NonasymptoticLogElliott`
(Tao 2016, Thm 1.3).  Open leaves in `src/` unchanged: `dilatedSliceCMLogElliottGe`
(`ElliottDilatedSlice.lean:220`, superseded/refuted route) and `nonasymptotic_of_affineCM`
(`ElliottLadder.lean:297`).

## Lap 25 — `ElliottDilatedUpper.lean` (new, zero sorry, trust triple)

NEXT item 1 of lap 24 is **done**.

* `exists_eventually_scaledTwistedMultiplier_bounds` — the dependency's fourth-moment and supremum
  bounds at the *factorable* modulus `T = a·(4hH+1)` (the dilated orthogonality needs `T = α·D`
  with `α = a`).  The fourth-moment input is stated for an arbitrary modulus `> 4Ph`, so scaling by
  the fixed `a` only multiplies `C` by `a`; the supremum bound never sees `T`.
* `exists_dilatedPairTwistedMean_small_of_fourier_first_moment` — the dilated analogue of
  `ElliottTwistedGraph.exists_pairTwistedPrimeGraphMean_small_of_fourier_first_moment`.

**The alias factor cancels exactly.**  The large-frequency prefactor is `H·M/(T·α)` and the
frequency count is `α` times the undilated one, so the budget `cutoff + 16ζN ≤ η/32` is the
dependency's verbatim with no `α` in it.  The only trace of the dilation is inside `C`.

## Lap 26 — `ElliottDilatedLower.lean` (new, zero sorry, trust triple)

The one piece of the lower-bound port the dependency does not supply: its graph never moves the
base point *backwards*, but the dilated block bookkeeping produces edges at
`n + 1 + j − ⌊q c₁ / a⌋`.

* `norm_logProbExpectation_backtranslate_sub_le` — backward translation costs what forward does;
  obtained from `Erdos67b.norm_logProbExpectation_translate_sub_le` applied to `fun n ↦ F (n - d)`.
* `norm_logProb_affineTwistedObservable_shift_sub_correlation_le` — **each edge at the dilated
  index still has mean `C/q`**, with the dependency's errors plus `2d/(L·M)`.  Hypothesis `d ≤ L`,
  free since `d ≤ q c₁ / a ≤ P|c₁| ≪ L`.

## Lap 27 — `ElliottGenericGraphCRT.lean` (new, zero sorry, trust triple)

Route (b) of the decision below, taken and **landed for the CRT rung**: the whole CRT /
concentration layer is now proved over an **arbitrary edge family** `E : ℕ → Fin H → ℂ` with
`‖E p j‖ ≤ B²`.  Reading `ElliottTwistedGraphCRT` shows the edge enters in exactly two places (the
coordinate norm bound, and the total `∑_j` in the mean), so the generalisation is free.

* `genCoordinate`, `genObservable`, `genSum`, `genMeanCRT`; `norm_gen*_le`,
  `sum_genCoordinate`, `crtComplexMean_genObservable`.
* `gen_tail_card_mul_exp_le`, `exists_gen_exponential_tail` — the Hoeffding tail with the
  dependency's own constant `c = ρ²/(64R²)`.
* **Anchors `genCoordinate_pairShiftEdge`, `genSum_pairShiftEdge`, `genMeanCRT_pairShiftEdge` are
  `rfl`**: the proved pure-shift layer is literally the instance
  `E p j = pairShiftEdge b c (p*h) j`.  Nothing in `src/` was edited.

**And the prime-dependent residue shift turns out to be free.**  The dilated layer needs the
condition `z + (j+1) − d_p = 0` with `d_p = ⌊p c₁/a⌋`; that is the standard condition evaluated at
`z − d_p`, and `z ↦ z − d_p` is a bijection of `ZMod p`.  So the shift is applied to the residue
variable by the *caller* and never enters the layer.  Genericity in the edge was the only
generalisation needed — this is the lap's main structural finding.

## Lap 28 — the dilated block is an ordinary block, and the entropy layer needs NO new lemma

`ElliottDilatedLower.affineBlock_eq_finiteSequenceBlock` (proved): for `a > 0`,

```
affineBlock f a n H = finiteSequenceBlock f H (a*(n+1) - 1).
```

The dilated graph therefore reads an **ordinary consecutive block of the same sequence**, at the
dilated base point `a(n+1) - 1`.

That alone would leave the entropy layer wanting blocks at `β(n) = a(n+1) - 1` while
`Erdos67b.logProb_block_rare_event_le` and `exists_logProb_block_entropy_control` speak about
blocks at `n`.  **The fix is to group the alphabet, and then nothing has to be re-proved:**

> Let `G : ℕ → (Fin a → α)`, `G m = (F(a m), …, F(a m + a - 1))`.  The block of `G` of length `H'`
> at position `n` reads `F` over `[a(n+1), a(n+1) + a H')`.  So `affineBlock f a n (a H')` is a
> **function of `finiteSequenceBlock G H' n`** — an ordinary block, at the ordinary base point `n`,
> of a sequence over the still-finite alphabet `α^a`.

`logProb_block_rare_event_le` takes an *arbitrary* rare-event family
`E : (Fin H → α) → Finset (ZMod P)` over an *arbitrary* finite `α`, so it applies **verbatim** with
`α ↦ α^a`, `H ↦ H'`; likewise `exists_logProb_block_entropy_control`.  The graph length is
`H = a H'`, and `a` is a constant fixed before every parameter.

**Consequence for the port.**  The only genericity the decoupling layer still needs, beyond lap
27's generic edge, is that the two graph blocks be produced from the alphabet block by a
**block-level** decode `(Fin H' → α) → (Fin H → ℂ)` rather than the pointwise `d₁ ∘ b` of the
proved port.  That is a widening of a hypothesis, not new mathematics.

## Lap 29 — `ElliottGenericGraphDecoupling.lean` (new, zero sorry, trust triple)

The entropy rung, ported with both widenings:

* `genDiscrepancyAt`, `norm_genDiscrepancyAt_le` — the centred generic graph observable at an
  **arbitrary** residue (so the caller can apply the per-prime shift; by CRT the family `(d_p)_p`
  is a single element of `ZMod (primeGraphModulus H)`).
* `entropy_scale_ratio` — `m / log m ≤ 2 · (am) / log (am)` for `2 ≤ m`, `a ≤ m`.  **This is the
  only place the dilation costs anything in the entropy layer**, and it costs a factor `2`: the
  dependency's `τ = cκ/2` becomes `τ = cκ/4`.
* `exists_logProb_gen_small_tail` — the port of
  `ElliottTwistedGraph.exists_logProb_pairTwisted_small_tail` for an arbitrary block-level edge
  builder `mkE : (m : ℕ) → (Fin m → α) → ℕ → Fin (a*m) → ℂ` with `‖mkE m b p j‖ ≤ B²`.  The
  entropy block length is `m`, the graph length `a*m`; `Erdos67b.logProb_block_rare_event_le` and
  `exists_logProb_block_entropy_control` are used **unchanged** (the latter's constant `C` becomes
  `log 4 · a`).

Lap 28's prediction is confirmed in the kernel: no new entropy lemma was needed.

## Lap 30 — the averaged generic decoupling, and the residue shift is now a parameter

* `exists_logProb_gen_small_tail` gained the parameter
  `Δ : (m : ℕ) → ZMod (primeGraphModulus (a*m))`: the rare event is tested at `z - Δ m`.  This is
  how the dilated graph's per-prime shifts `d_p = ⌊p c₁/a⌋` enter — by CRT they are a single
  element of `ZMod (primeGraphModulus H)`.  The tail bound is unaffected because `z ↦ z + Δ m` is
  injective, so the shifted rare set has the same cardinality.
* `exists_logProb_gen_decoupling` — the averaged form, with the dependency's coefficients
  `ρ = ε/2`, `κ = ε/(16R)` and budget `ρ + 8Rκ = ε`, at graph length `a*m`.

**The whole lower-bound machinery is now available for an arbitrary edge family at a dilated
length with an arbitrary per-prime residue shift, all sorry-free and axiom-clean.**

## Lap 31 — `ElliottDilatedBridge.lean` (new, zero sorry, trust triple): the two halves meet

`pairTwistedMeanCRT_eq_pairTwistedPrimeGraphMean` is the join between the lower-bound side's CRT
mean and the upper-bound side's Fourier mean.  This file proves the same join generically and then
instantiates it at the dilated edge:

* `genPrimeGraphMean`, `genMeanCRT_eq_genPrimeGraphMean` (for `s ⊆ primesLE H`).
* `dilatedEdgeFamily b c α c₁ h p m = dilatedPairShiftEdge b c α (p c₁) (p h) m`.
* `genPrimeGraphMean_dilatedEdgeFamily` — **`rfl`**.
* `genMeanCRT_dilatedEdgeFamily` — **the CRT mean that the entropy/decoupling layer controls is
  literally the Fourier mean that `ElliottDilatedUpper` bounds.**
* `norm_dilatedEdgeFamily_le` — the dilated edge family is `B²`-bounded, the hypothesis shape the
  generic layer wants.

So both halves of the crux now speak about one object, `dilatedPairTwistedMean`.

## Lap 32 — `genSum` at the shifted residue is the shifted-divisibility graph sum

* `crtShift H d` — the CRT element whose `p`-component is `d p`; `crtShift_component`.
* `genSum_natCast_sub_crtShift` — for `d p ≤ n`,

```
genSum w E s (n − crtShift H d)
  = ∑_p [p ∈ s] ∑_j [ p ∣ n + (j+1) − d p ] · w p · E p j.
```

  Generic analogue of `ElliottTwistedGraph.pairTwistedSum_natCast`.  This is the formal content of
  "the per-prime residue shift never enters the layer": testing `genSum` one CRT element to the
  left imposes exactly the dilated divisibility condition, prime by prime.

**Lean gotcha (cost ~4 builds, worth remembering).**  `primeGraphModulus H` is a plain `def` for
`∏ p : PrimeGraphIndex H, p.1`.  `map_sub e x y` / `map_natCast e n` elaborate `e`'s domain in the
`∏` form, so the resulting hypothesis is *not syntactically* rewritable against a goal written with
`primeGraphModulus H` — `rw` and even `simp only` both fail with "no progress" while `trace_state`
shows two identical-looking terms.  Fix: state the `map_sub` / `map_natCast` instance as an
explicitly-typed `have` using `primeGraphModulus H`, proved by `map_sub _ _ _`.

## Lap 33 — the edge family must be indexed by the PROGRESSION index, not the block position

A real obstruction found and removed.  `dilatedEdgeFamily` (lap 31) is indexed by the block
position `m`.  That is the wrong index for the CRT layer: the divisibility the dilated observable
carries is `p ∣ n + 1 + j − ⌊p c₁/a⌋` with `m = a j + (p c₁ mod a)`, i.e. **affine in the
progression index `j`, not in `m`**.  Written in `m` it becomes `m ≡ a d + r − a(n+1) (mod p)`, so
the residue random variable would have to be `a·n + Δ_p` — and `Erdos67b.logProb_block_rare_event_le`
requires it to be `n` itself.  (Rescaling by `a⁻¹ mod P` does not save it: `a` is invertible modulo
each large prime of the graph but not modulo `primeGraphModulus H`, which contains the prime
factors of `a`.)

The fix is to index the edge family by `j` from the start.  Then `genCoordinate`'s standard
condition `z + (j+1) = 0` tested at `z = n − crtShift` is *exactly* the dilated divisibility, and
laps 27–32 apply unchanged.

* `dilatedEdgeReindexed b c α c₁ h p j = blockExtend b (α j + r_p) · blockExtend c (α j + r_p + p h)`,
  `r_p = (p c₁) mod α`.
* `sum_dilatedEdgeReindexed` — **same total** as the `m`-indexed family
  (`sum_dilatedPairShiftEdge_eq_progression` plus the vanishing of the overflow terms).
* `genPrimeGraphMean_dilatedEdgeReindexed`, `genMeanCRT_dilatedEdgeReindexed` — the join of lap 31,
  now for the family the CRT layer can actually use.
* `norm_blockExtend_le`, `norm_dilatedEdgeReindexed_le` — the `B²` hypothesis shape.

## Lap 34 — the dilated `pairTwistedSum_sequenceBlock` is proved

* `blockExtend_affineBlock_mul` — the pointwise content of `sum_dilatedPairShiftEdge_affineBlock`:
  on the non-overflow range, the reindexed dilated edge of the re-based blocks **is** the affine
  pair observable at index `n + 1 + j − ⌊q c₁/a⌋`.
* `genSum_dilatedEdgeReindexed_affineBlock` —

```
genSum w (dilatedEdgeReindexed (affineBlock f₁ a n H) (affineBlock f₂ a n H) a c₁ h) s
    (n − crtShift H (fun p ↦ ⌊p c₁/a⌋))
  = ∑_p [p ∈ s] ∑_{j : a j + r_p + p h < H}
      affineTwistedObservable w f₁ f₂ a p c₁ (c₁+h) (n + (j+1) − ⌊p c₁/a⌋),
```

  under `⌊p c₁/a⌋ ≤ n` for every `p ≤ H`.  This is the dilated analogue of
  `ElliottTwistedGraph.pairTwistedSum_sequenceBlock`, and the last identification the
  correlation-transfer rung needs: lap 26 already controls the log-mean of exactly these
  observables.

## NEXT (lap 35 onwards)

1. **The dilated correlation-transfer rung**: the analogue of
   `ElliottTwistedGraphCorrelation.norm_logProb_pairTwistedGraph_sub_correlation_le`.  Take
   `logProbExpectation` of `genSum_dilatedEdgeReindexed_affineBlock`, apply lap 26's
   `norm_logProb_affineTwistedObservable_shift_sub_correlation_le` to each `(p, j)` term, and
   collect: the correlation coefficient is `∑_p [p∈s] #{j : a j + r_p + p h < H} / p`, the dilated
   analogue of `Erdos67b.primeGraphCorrelationWeight` (≈ `H/a` terms per prime instead of `H`).
   Then `norm_logProb_..._sub_correlation_le` with the decoupling error, the entropy-selected
   scale, and the contradiction.
2. Then the correlation-transfer rung with lap 26's
   `norm_logProb_affineTwistedObservable_shift_sub_correlation_le`, and the contradiction.
2. Combine with lap 26's `norm_logProb_affineTwistedObservable_shift_sub_correlation_le` for the
   correlation-transfer rung, then the entropy-selected scale and
   `exists_logProb_dyadic_*_lower`.
2. Then instantiate at `E p j = dilatedPairShiftEdge (affineBlock f₁) (affineBlock f₂) a (p c₁) (p h) j`
   with residue variable `z − ⌊p c₁/a⌋`, and combine with
   `sum_dilatedPairShiftEdge_affineBlock` + lap 26's edge-mean estimate.

OLD PLAN (superseded by lap 27, kept for the reasoning):
   **The dilated CRT / decoupling layer.**  The remaining lower-bound chain is
   `ElliottTwistedGraphCRT` → `Decoupling` → `Correlation`, all written for `pairShiftEdge`.
   The dilated coordinate is `∑_j if z + (j+1-d_q) = 0 then w q · dilatedPairShiftEdge … j`:
   the residue condition is *translated by `d_q = ⌊q c₁/a⌋`*, which is a bijection of `ZMod q`
   and so disturbs neither the CRT factorisation nor the entropy/rare-event argument.  Two options,
   decide at the start of the lap:
   (a) port the three files with the shifted coordinate (mechanical, ~3 laps);
   (b) **generalise the proved stack once over an arbitrary bounded edge family `E : ℕ → Fin H → ℂ`
       and residue shift**, making both the pure-shift and dilated cases instances (one refactor,
       higher leverage, touches proved `src/` files only).
   (b) looks better: the entropy layer only ever uses boundedness of the edge.
2. Then `DilatedCMLogElliott` by the same contradiction as `shiftCMLogElliott`.
3. **Parallel leaf:** `nonasymptotic_of_affineCM` (route in its docstring in `ElliottLadder.lean`).

## Note

`DIRECTION.md` still mandates the slice route (written before lap 16, which refuted it and
answered the directive's own decisive question — "do `q ∣ n` and `a ∣ n` compose?" — in the
negative for the translated observable).  The dilated route is the replacement and stays inside the
directive's objective, scope and forbidden-drift list.  An altitude lap should refresh it; do not
edit it from a proof lap.
