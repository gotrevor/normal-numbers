# HANDOFF 2026-09-14 — G4 disjunctivity, lap 6 (review lap #2 + two named inputs DISCHARGED)

Branch `wip/g4-disjunctivity`, HEAD `4ed5f00`.  Working tree clean.  Not pushed.
Commits this lap: `3a290fb` (G4Frame + PropA), `3e0cedd` (PropC), `f8cf59c` (§4D algebra),
`d9773ca` (PropD reduction), `4ed5f00` (row masses).
Build line: `lake build NormalNumbers.G4Frame NormalNumbers.G4Remainder NormalNumbers.G4RowMass`
— green, and the pre-commit `lake build` (8888 jobs) is green.
Every new headline prints `[propext, Classical.choice, Quot.sound]`.

## This was an altitude lap: `DIRECTION.md` CURRENT DIRECTIVE was rewritten

Diagnosis: five laps had produced *inputs* without closing a single named `Prop`, and the seam
between the abstract `Frame` and the concrete grid/progression/small-prime vector had **never
been compiled**.  Mandated move changed from "decompose §4C" to "close a named `Prop`".
Trigger **G-T1 retired as satisfied** (C3 is proved: `G4CRTInput.crt_input` +
`G4TransferMoment.norm_sampleAvg_prod_ee_le`; no sieve theorem in the route).  New trigger
**G-T4** covers the seam.  Ordering after the seam: **D → Jackson → B assembly → §5 schedule**.
`STATUS.md` refreshed.  Grind laps read and obey `DIRECTION.md`; do not edit it.

## Proved this lap (declaration names)

`src/NormalNumbers/G4Frame.lean`
* `GridParams.rowEquiv : (Fin K → Fin s) ≃ Fin (s^K)`, `GridParams.atomEquiv : Atom ≃ Fin ((s+1)^K)`,
  `GridParams.Amat` — the reindexing onto the wiring's `Fin r` / `Fin H`, with `r = s^K`,
  `H = (s+1)^K` on the nose.
* `gridFrame G X hne sm γ hη hε D : Frame` — draft §§2–3 assembled.  `γ, η, ε, D` are parameters.
* **`gridFrame_propA`** — `PropA` DISCHARGED.  `θ` is the transport translate by `rfl`, and
  `propA_of_progression`'s residue-freezing hypothesis is exactly `exists_mult_mul` at `c = 0`.
* `card_roots_shiftPhase_le` — the root set of `shiftPhase ρ x p` is `image (root p ρ) univ`,
  **independent of the coefficients**.  This is what makes §4C uniform over the box.
* `torusChar_gridFrame_S`, `smallPrimeBound`, **`gridFrame_propC`** — `PropC` DISCHARGED, with a
  frequency-free explicit bound whose main term is `exp(−4·4^{−4}8^{−K} ∑_{p∈sm} 1/p)`.

`src/NormalNumbers/G4Remainder.lean`
* **`sum_kronPow_mul_shiftG_eq_zero`** — the first `K` layers cancel exactly, for ANY weight
  (not just `ω`): `ρ_{α,j} = j + Q(jD₀ + proj B j α)` and `proj` ignores coordinate `j−1`.
* **`gridFrame_Ffull_eq`**, `tailFrom_split`, `summable_dilatedTailB` — `Ffull` is the retained
  tail (`j > K`) minus `γ`, and that tail is the `J`-truncation plus `farPart`.
* `smallPrimes R P₀`, `omegaBig R P₀`, **`omega_split`** — frozen / small / large partition of `ω`.
* `omegaOn_primeFactors_congr`, `frozenTranslate`, `frozenGamma`, `blockSum_frozen_eq` — the
  frozen primes are constant on the progression; `γ` is pinned.
* **`gridFrame_Ffull_decomp`** — on the sample, exactly
  `Ffull n = (Sval n + bigBlock n + farPart n) mod 1`.
* **`gridFrame_propD`** — `PropD (δbig + δfar)` from `bigAvg G X R ≤ δbig·εη` and
  `farAvg G X ≤ δfar·εη`.  §4D is now two named real estimates.

`src/NormalNumbers/G4RowMass.lean`
* `sum_kronPow_eq_prod`, `sum_kronPow_map_eq_prod` — the atom sum of a Kronecker power
  factorises coordinatewise.
* **`sum_kronPow_diffZ_eq_zero`** (`∑_α A_{aα} = 0`, the signed cancellation),
  `sum_abs_kronPow_diffZ` (`= 2^K`), `sum_sq_kronPow_diffZ` (`= 2^K`).
* `geom_range_le`, `sum_layer_inv_le` (`≤ 4^{−K}/3`), `sum_layer_inv_sq_le` (`≤ 16^{−K}/15`).
* `abs_blockSum_le` — `|blockSum| ≤ C·2^{−K}/3` when the weight is `≤ C`.  **`p > Y` only.**

## Dependency map

`PropA` ✅ proved · `PropC` ✅ proved · `PropB` open (all inputs proved, assembly is labour)
· `PropD` reduced to `bigAvg` + `farAvg` · `PropJackson` open · §5 schedule open.
Nothing refuted.  `isDisjunctive_four_of_frames` remains CONDITIONAL on `SeparatingFrameExists`.

## Resume here — the `Y`-split of `bigAvg` (host tripwire, `CHECK-g4-route-deviations.md` §4)

1. **`p > Y` (pointwise).**  `abs_blockSum_le` with `C = ⌈log(3X)/log Y⌉ = 100` for
   `Y = X^{1/100}`: an `m ≤ 3X` has at most `100` prime factors above `X^{1/100}`.  Needs a
   small lemma `card {p ∈ m.primeFactors : p > Y} ≤ log m / log Y` (product of the large prime
   factors divides `m`).  Gives `O(2^{−K}) = o(η)`.
2. **`R < p ≤ Y` (L², signed).**  Expand `E_n |∑_{α,j} c_{αj} 1_{p ∣ n+ρ_{α,j}}|²` by
   two-congruence counting; the `1/p` main terms cancel by `sum_kronPow_diffZ_eq_zero`, leaving
   `O(8^{−K/2}√(log M))` from `∑ c² = 8^{−K}/15` (`sum_sq_kronPow_diffZ` +
   `sum_layer_inv_sq_le`) plus a progression-counting error `≤ P₀/X` per pair.
   **Do NOT discharge `bigAvg` with a single pointwise bound — it typechecks and is wrong.**
3. **`farAvg`.**  Needs the AP-mean `E_{n∈P} ω(n+ρ) = O(L + log P₀)`.  **Route found this lap,
   worth writing down**: avoid Mertens entirely — `2^{ω(m)} ≤ d(m)`, so
   `ω(m) log 2 ≤ log d(m)`; then hand-rolled Jensen via `log x ≤ log c + x/c − 1` at
   `c = E[d]` gives `E[ω] ≤ log(E[d])/log 2`; and
   `∑_{n∈P} d(n+ρ) ≤ ∑_{m < X+ρ} d(m) = ∑_{k} ⌊·/k⌋ ≤ (X+ρ)(log(X+ρ)+1)`, so
   `E[d] = O(P₀ log X)` and `E[ω] = O(L + log P₀)`.  Upper Mertens is NOT needed.
   Then `E|farPart| ≤ 2^K·4^{−J}·O(L) = O(2^K L^{−5}) = o(η)`.
4. After D: `PropJackson` (product kernel, one-coordinate first moment `O(1/D)`; the average
   metric makes `κ = O(1/(εηD))` dimension-free), then the B assembly, then §5.
