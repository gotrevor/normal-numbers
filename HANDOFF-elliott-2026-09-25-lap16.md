# HANDOFF elliott 2026-09-25 lap 16 — the slice detour is RETIRED; the dilation is a spectator

Branch `wip/elliott-port`.  Working tree clean at commit time.
`lake build NormalNumbers.ElliottAffineGraph` green, 9539 jobs.
Never `lake exe cache get`.  Never edit / vendor `.lake/packages/lean-proofs-latest/`.

## Headline

`NormalNumbers.ElliottGeneral.nonasymptoticLogElliott : Erdos67b.NonasymptoticLogElliott`
(Tao 2016, Thm 1.3).  Open leaves in `src/`:

| leaf | file | what is left |
|---|---|---|
| `dilatedSliceCMLogElliottGe` | `ElliottDilatedSlice.lean` | `a ≥ 2` slice — **superseded, see below** |
| `nonasymptotic_of_affineCM` | `ElliottLadder.lean` | 1-bounded multiplicative → CM unimodular |

## This lap's advance: the crux does not need the slice at all

Lap 15 factored the crux through the multiples-of-`a` slice because `m ↦ p m` preserves the
residue class `0`.  True, but the wrong bookkeeping, and this lap **refutes it as a route**:

* the slice pushes an extra indicator `a ∣ m` through the entire Fourier layer, and
* worse, the translation by `p c₁` that centres the edge observable on `f₁` (needed to reuse the
  proved pure-shift rung) converts `a ∣ m` into `a ∣ n − p c₁`, a condition depending on
  `p mod a`.  It therefore does **not** factor out of the prime sum, and the block Fourier
  transform does not see it as a single fixed periodic factor.  Recorded; do not re-derive.

The right bookkeeping was already sitting in `ElliottLadder.pairObservable_dilation_twisted`:

```
conj (f₁ q * f₂ q) * pairObservable f₁ f₂ a (q*c₁) (q*c₂) (q*n) = pairObservable f₁ f₂ a c₁ c₂ n
```

The graph step `n ↦ q n` sends the *pair of forms* `(a n + c₁, a n + c₂)` to
`q · (a n + c₁, a n + c₂)`: **both shifts dilate with `q`**, exactly as `h ↦ q h` in the proved
pure-shift rung, and the common dilation `a` rides along untouched.  No divisibility condition,
no slice, no arithmetic progression anywhere.

### What is proved (new file `src/NormalNumbers/ElliottAffineGraph.lean`, zero sorry)

* `affineLogCorrelation L U f₁ f₂ a c₁ c₂` — the crux's correlation under the finite log law.
* `affineTwistedObservable w f₁ f₂ a q c₁ c₂ n = if q ∣ n then w q * pairObservable f₁ f₂ a (q c₁) (q c₂) n else 0`
  — the general-affine graph edge; `norm_affineTwistedObservable_le_one`.
* **`norm_logProb_affineTwistedObservable_sub_correlation_le`** — *every translated general-affine
  graph edge has mean `C/q`*, with the dependency's verbatim errors
  `2/M + 2j/(L·M)`.  **The dilation `a` does not appear in the estimate.**  This is the exact
  general-forms replacement for
  `ElliottTwistedGraph.norm_logProb_pairTwistedDivisible_sub_correlation_le` (the case
  `a = 1, c₁ = 0, c₂ = h`), i.e. the whole lower-bound engine of the crux, now at full generality.
* `affineTwistedObservable_one` — the `a = 1, c₁ = 0, c₂ = h` consistency check against the
  proved observable.

All `#print axioms` = `[propext, Classical.choice, Quot.sound]`.

## What is left of the crux, exactly

**Only the Fourier layer.**  In block coordinates the general edge is

```
b (a*j + q*c₁) * c (a*j + q*c₂)       (proved case: b j * c (j + q*h))
```

i.e. the block index is **dilated by `a`**.  The Fourier identity survives:

```
∑_j b (a j + q c₁) c (a j + q c₂) e(t j / T)
  = ∑_{t₁,t₂ : a(t₁+t₂) ≡ −t (T)} b̂ t₁ · ĉ t₂ · e((t₁ c₁ + t₂ c₂) q / T),
```

so the phase in `q` is still a **single** frequency `s = t₁ c₁ + t₂ c₂`, and
`twistedPrimeGraphMultiplier` is evaluated at `s` exactly as before — in particular
`fourth_moment_twistedPrimeGraphMultiplier_le_energy` and the whole large-frequency /
Markov / entropy stack above it are untouched.

## Lap 17 (same session): the new Fourier lemma is PROVED

`src/NormalNumbers/ElliottDilatedPairing.lean` (new, zero sorry).  Write `T = α*D`.

* `dilatedPairShiftEdge b c α s σ m` — the `a`-dilated edge: block positions `m` in the residue
  class `s (mod α)`, paired with `m + σ`.  (`α = 1, s = 0` is `pairShiftEdge`.)
* `dilatedBlockPairing T D b c t u = b̂(t + u*D) * conj ĉ̄(t)` — the two blocks are transformed at
  frequencies differing by `u*D`.  (`u = 0` is `pairBlockPairing`.)
* **`sum_dilatedBlockPairing_mul_phase`** —
  `∑_{t<T} ∑_{u<α} dilatedBlockPairing T D b c t u * e_T(t σ) * e_α(-u s) = T·α·∑_m dilatedPairShiftEdge …`,
  under `H + σ ≤ T`.  The residue-class restriction costs exactly one extra frequency variable
  ranging over `α` (a constant) values.
* **`phase_mul_phase_eq_single_frequency`** — with `s = q c₁`, `σ = q(c₂−c₁)`,
  `e_T(t σ) · e_α(−u s) = phase T (t(c₂−c₁) − u D c₁) q`: a **single** frequency in the prime `q`.
  This is the load-bearing fact: the prime sum still produces `twistedPrimeGraphMultiplier` at one
  frequency, so `fourth_moment_twistedPrimeGraphMultiplier_le_energy` and the Markov /
  large-frequency / entropy layers above it are untouched.
* Supporting: `phase_add_left`, `phase_dilate` (`e_α(u m) = e_T(u D m)`), `sum_phase_dvd`.

All `#print axioms` = `[propext, Classical.choice, Quot.sound]`.

## Lap 18 (same session): the dilated graph mean has an exact Fourier identity

Also in `src/NormalNumbers/ElliottDilatedPairing.lean` (still zero sorry):

* `dilatedPairTwistedMean w b c α c₁ h s = ∑_{p∈s} w p · p⁻¹ · ∑_m dilatedPairShiftEdge b c α (p c₁) (p h) m`
  — the prime `p` contributes the edge at residue class `p c₁ (mod α)` and step `p h`.
* `dilatedTwistedMultiplier T D h c₁ s w t u = ∑_{p∈s} w p · p⁻¹ · e_T((t h − u D c₁) p)`.
* **`dilatedTwistedMultiplier_eq`** — this is *literally*
  `twistedPrimeGraphMultiplier T 1 s w (t*h − u*D*c₁)`.  So the fourth-moment / additive-energy
  bound `fourth_moment_twistedPrimeGraphMultiplier_le_energy`, the trivial bound, the dyadic
  bounds — all of the proved multiplier theory — apply to the dilated graph **verbatim**, at a
  shifted frequency.  Nothing in the arithmetic layer has to be re-proved.
* **`dilatedPairTwistedMean_eq_fourier`** —
  `dilatedPairTwistedMean = (T·α)⁻¹ ∑_{t<T} ∑_{u<α} dilatedBlockPairing T D b c t u · dilatedTwistedMultiplier T D h c₁ s w t u`,
  under `∀ p ∈ s, H + p*h ≤ T`.  The exact analogue of
  `pairTwistedPrimeGraphMean_eq_fourier`; the only changes are the extra alias variable `u` and the
  normalisation `(T·α)⁻¹`.
* Supporting: `phase_pair_single_frequency` (the `h`-form of the collapse).

## Lap 19 (same session): the large-frequency bound survives the dilation

Still `src/NormalNumbers/ElliottDilatedPairing.lean`, zero sorry.

* `phase_add_modulus`, `blockFourier_add_modulus` — the block transform is `T`-periodic in the
  frequency.
* `sum_range_shift_of_periodic` — a `T`-periodic `g : ℤ → ℝ` has the same sum over `range T` after
  any integer shift (mathlib has no such lemma; proved by induction on the shift).
* `sum_norm_sq_blockFourier_shift` — hence **aliased Parseval**: each alias `t ↦ t + u D` permutes
  the frequency range, so `∑_{t<T} ‖b̂(t+uD)‖² = ∑_{t<T} ‖b̂(t)‖² ≤ T·H`.
* **`norm_dilatedPairTwistedMean_le_largeFrequencies`** —
  `‖dilatedPairTwistedMean‖ ≤ θ·H + (H·M/(T·α)) · ∑_{(t,u) large} ‖b̂(t+uD)‖`,
  the verbatim analogue of `norm_pairTwistedPrimeGraphMean_le_largeFrequencies`, with the same
  leading term `θ·H`.  The threshold split is unchanged (AM–GM across the two *different*
  frequencies `t+uD` and `t`), and Parseval costs exactly the factor `α`, which the normalisation
  `(T·α)⁻¹` cancels.

So both halves of the Fourier layer are now dilated: the exact identity and the large-frequency
bound, with **no loss in the shape of the estimate**.

## NEXT (lap 20)

1. re-base `finiteSequenceBlock` at `a*(n+1)` and identify the dilated edge with
   `ElliottAffineGraph.affineTwistedObservable` (the re-basing shift `q*c₁ ≤ P|c₁|` is absorbed by
   the existing translation error `2j/(L·M)`).

## Older NEXT (superseded by the two items above)

1. Re-base the sequence block at `a*(n+1)` and prove the analogue of
   `pairTwistedSum_sequenceBlock` for the dilated edge, i.e. identify
   `dilatedPairShiftEdge` on `finiteSequenceBlock`-style blocks with
   `ElliottAffineGraph.affineTwistedObservable`.  The re-basing shift `q*c₁ ≤ P|c₁|` is absorbed by
   the existing translation error `2j/(L·M)` (now with the constant `|c₁|`).
2. Then re-run `ElliottTwistedGraphCorrelation` / `...Bounded` with the dilated pairing and the new
   edge estimate; `DilatedCMLogElliott` should fall out directly, and
   `ElliottDilatedSlice.dilatedSliceCMLogElliottGe` becomes dead weight (leave the file, retarget
   `dilatedCMLogElliott` at the new route).
3. Parallel leaf: `nonasymptotic_of_affineCM`.
