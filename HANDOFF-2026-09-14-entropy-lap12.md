# HANDOFF — entropy expedition, lap 12 (2026-09-14, Opus grind)

**Branch** `wip/g4-entropy`.  `lake build` green, 8954 jobs.  New module
`src/NormalNumbers/G4EntropyScales.lean`, sorry-free, axiom-clean.  Previous baton:
`HANDOFF-2026-09-14-entropy-lap11.md`.

## Headline: the §6 positive branch is closed — **across all scales**, not just one

```
G4Entropy.card_le_of_scales  : |U' ∩ [0,L)| ≤ (1/12)·L
G4Entropy.not_dense_of_scales: 0 < L → ¬ (L ≤ 2·|U' ∩ [0,L)|)
```

for **any** finite set `S` of distinct scales `K ≥ 2`, **any** family `F` of grids each
carrying the schedule's parameters `(gridQ K (nn K), gridD₀ K (nn K), gridUmax K (nn K))` at one
of those scales, **any** block lengths `mm K ≤ K`, and any positions `U'` the family covers.

Lap 11 closed a single scale; this closes the union over an arbitrary scale set, which is the
brief's direction 2 (*synchronize construction scales*) in the only form that could have
defeated the barrier.

### The estimate

Per scale the weight is `w(K) = (U+1)·m / (2(1 + Q·D₀))`, and

* `scaleWeight_le` : `w(K) ≤ 4^{-K}` for `K ≥ 2`, `m ≤ K`.  Inputs: `Q ≥ U` (`gridQ_gt`),
  `D₀ = K·U` (defeq), so `1 + Q D₀ ≥ K U²`; `(U+1)m ≤ 2U·K`; hence `w ≤ 1/U`; and
  `U ≥ B^K ≥ 4^K` because `B = K²(K+N)+1 ≥ 4` for `K ≥ 2`.
* `sum_inv_four_pow_le` : distinct scales `K ≥ 2` give `Σ_{K ∈ S} 4^{-K} ≤ 1/12` (shift
  `K ↦ K-2`, inject into `range n`, geometric series).
* `card_filter_le_of_scales` : the Nat count across scales, family-free, via `multSet` and
  `periodCol`.

`1/12 < 1/2`, so the whole admissible class misses more than half of **every** prefix.

### Scope of the claim (read before quoting it)

The theorem quantifies over: family size, atoms, frozen residues, translations, the scale set,
the sample range `XX`, and the block lengths up to `mm K ≤ K`.  It fixes one layer count per
scale (`nn : ℕ → ℕ`), which is how the schedule's family is built — a genuinely two-parameter
family `(K,N)` with many `N` per `K` is *not* covered, and is the only surviving gap in the
averaging direction.  (It would need `Σ_{K,N} (4(K+N))^{-K} ≤ 1/2`, a convergent double series;
the work is the `Σ 1/M²` estimate, not a new idea.)

## Where the expedition now stands

* §2, §3A/B/C, §4: closed (laps 1–7): `entropy_E0`, `entropy_E1` unconditional and clean.
* §6 `T_E`: **refuted** (lap 8), and refuted structurally (lap 9): no property determined by the
  joint sample laws can imply normality.  `T_S`, `T_mix`: refuted-or-vacuous (lap 9).
* §6 positive branch, direction 1 (averaging over samplers): **closed negatively** — lap 10 for
  translates, lap 11 for a whole scale, lap 12 for all scales at once.
* §6 positive branch, direction 2 (scale synchronisation): the union-over-scales reading is now
  also closed; what the brief additionally asks there — *which ranges of `X` the arithmetic
  estimates permit at a given `K`* — is a statement about the transport machinery, not about
  the sampled position set, and is the honest remaining item.
* §5 (S): defined (`S_freq`), open, off the critical path.

## Next bounded test, hardest first

1. **The two-parameter gap** above: allow `(K,N)` with many `N` per `K`.  Needs
   `Σ_{K≥2} Σ_{M≥K} (4M)^{-K} ≤ 1/2`; the inner sum is geometric in `K` and the outer needs
   `Σ_{M≥2} M^{-2} ≤ 1`.  Mechanical but not free.  Closing it makes the negative answer
   unconditional over the entire `GridParams` interface at the schedule's parameter functions.
2. **The genuinely different input.**  Everything proved says the obstruction is
   `d_α = 1 + Q(D₀ + u_α) ≥ 1 + Q D₀` with `Q` factorially large.  A sampler reading positive
   density needs `d_α` comparable to `H_K·m_K`, i.e. the frozen modulus `Q` must not dominate
   the alphabet.  State that as a property of a hypothetical arithmetic input
   (`2 d_min ≤ C·H·m` for some fixed `C`) and check against `G4CRTInput`/`G4ScheduleGrid`
   whether *any* choice of the freezing construction can satisfy it — that is the last
   mathematical question the expedition's §6 can answer.
3. §5's (S) as a statement of what entropy controls.

## Lean gotchas from this lap

- `div_le_div_iff` → `div_le_div_iff₀`; `pow_le_gridUmax` lives in `NormalNumbers.G4.Sched`.
- `nlinarith` on a degree-3 product goal usually fails; supply the exact nonneg product
  (`mul_nonneg (mul_nonneg _ _) _`) and finish with `linarith`, which ring-normalizes monomials.
- `Nat.cast_div_le` is the bridge `((a / b : ℕ) : ℝ) ≤ (a : ℝ) / b`; `push_cast` first.
- `field_simp` can close the goal outright — a trailing `ring` then errors with "no goals".
