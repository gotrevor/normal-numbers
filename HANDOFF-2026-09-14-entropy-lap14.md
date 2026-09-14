# HANDOFF — entropy expedition, lap 14 (2026-09-14, Opus grind)

**Branch** `wip/g4-entropy`.  `lake build` green, 8954 jobs.  `G4EntropyScales.lean` extended,
sorry-free, axiom-clean.  Previous baton: `HANDOFF-2026-09-14-entropy-lap13.md`.

## Headline: the sparsity obstruction is **intrinsic to the freezing construction**

```
G4Entropy.ReadableScale C K N m : Prop := 2 * scaleDmin K N ≤ C * ((K^2+1)^K * m)
G4Entropy.not_readableScale     : 4 ≤ K → C ≤ K → m ≤ K → ¬ ReadableScale C K N m
G4Entropy.not_readable_scale    : 4 ≤ K → C ≤ K → m ≤ K →
                                    C * ((K^2+1)^K * m) < 2 * scaleDmin K N
```

Laps 9–13 reduced the whole §6 question to one comparison: a sampler can read a positive
fraction of the digit positions only if its **period** `2 d_min` is comparable to its
**alphabet** `H_K·m = (K²+1)^K·m`.  Lap 14 settles that comparison, for every constant `C`:

* `GridParams` forces `Q ≥ U` (`gridQ_gt`) and `D₀ = K·U` (defeq), so
  `scaleDmin = 1 + Q D₀ ≥ K·U²`;
* `U ≥ B^K ≥ (K³)^K = K^{3K}` (`cube_le_gridB`, `pow_le_gridUmax`), so
  `2·scaleDmin ≥ 2·K^{6K+1}`;
* `C·H·m ≤ K·((2K²)^K·K) ≤ K^{3K+2}` once `C ≤ K` and `m ≤ K` (using `2^K ≤ K^K`);
* `3K+2 ≤ 6K+1` for `K ≥ 1`.

The gap is a factor `K^{3K}`, not a constant.  **No admissible scale is readable.**  The
sample's sparsity is therefore not an artefact of the schedule's particular choices (atoms,
frozen residue, layer count, block length, sample range) but a consequence of the freezing
requirement itself: the modulus that makes the CRT transport exact is forced to dwarf the
alphabet the quantization can distinguish.

## The expedition's §6 answer, complete

1. `T_E` is false (`not_T_E`, lap 8), with a witness meeting its exact premise.
2. No property determined by the joint sample laws implies normality
   (`exists_nonnormal_jointLocal`, lap 9); `T_S`, `T_mix` are refuted-or-vacuous.
3. Any repair needs a position set of upper density `≥ 1/2`
   (`upper_density_half_of_forces_normal`, lap 10).
4. No admissible sampler family supplies it: translates (lap 10), one scale (lap 11), any set of
   scales `K` (lap 12), any set of scale pairs `(K,N)` (lap 13).
5. And the reason is structural, not a matter of tuning: **no admissible scale can be readable
   at all** (lap 14).

`entropy_E0` and `entropy_E1` stand unchanged: unconditional, axiom-clean theorems about the
joint quantized sample of `G₄`.  What the expedition adds is the exact reason they cannot be
upgraded to normality, and a proof that no upgrade of this shape exists.

## What is NOT claimed

Nothing about the normality of `G₄` — it may well be normal.  Nothing about samplers outside
the `GridParams` interface: a different arithmetic mechanism, one that does not need a frozen
modulus dominating its alphabet, is untouched by all of this.  The expedition's output is that
*this* mechanism cannot be the bridge, and precisely why.

## Next bounded test

1. **§5's (S)** is now the only open item inside the brief: `S_freq` is defined
   (`G4EntropyBarrier`), and the question "what does `entropy_E0` actually control about the
   sampled block frequencies?" is a clean finite-probability leaf.  The honest target is a
   *statement* (entropy deficit ⟹ TV distance to uniform, via Pinsker on the joint law), not a
   step toward normality — the bridge is closed.
2. An altitude/review lap should fold the §6 table into `STATUS.md` and the CURRENT DIRECTIVE
   (grind laps do not edit the directive).  The brief's §8 outcome condition is met.

## Lean gotchas from this lap

- `Nat.pos_pow_of_pos` is gone; use `pow_pos`.
- After `rw [mul_pow, ← pow_mul]` the goal can already be closed — a trailing `ring_nf` then
  errors with "no goals".
- `ring` proves `K * (K ^ (3*K) * K) = K ^ (3*K+2)` directly; the `pow_succ` rewrites are not
  needed and misfire.
