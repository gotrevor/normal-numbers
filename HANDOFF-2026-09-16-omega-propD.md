# HANDOFF 2026-09-16 — campaign A CLOSED (unconditional); G5/Ω at §4D

Branch `wip/g5-prime-subset`, HEAD `0e25078`, working tree clean,
`lake build` green (**9055 jobs**).  `src/` carries exactly the two pre-expedition,
forbidden-drift `sorry`s (`phaseOscillation`, `exists_prime_nonresidue`); **zero `axiom`s**.
Every declaration added this session prints `[propext, Classical.choice, Quot.sound]`.

## 1. Campaign A — DONE, unconditional

```lean
theorem isDisjunctive_residueClass_primeSum {q : ℕ} [NeZero q] {a : ZMod q} (ha : IsUnit a)
    {b : ℕ} (hb : 3 ≤ b) :
    IsDisjunctive b (∑' p : ℕ, if p.Prime ∧ (p : ZMod q) = a then 1 / ((b : ℝ) ^ p - 1) else 0)
```

plus `isDisjunctive_residueClass` (the weight form `c_S(b) = ∑_n ω_S(n)/bⁿ`),
`isDisjunctive_subsetLambert` (any `S` with a `MertensAP.MertensRate`), and
`isDisjunctive_subsetLambert_univ` (the `S = univ` sanity instance, re-deriving
`isDisjunctive_base`'s statement through the `S`-route).  Details:
`HANDOFF-2026-09-16-residueClass.md`.

**How it closed.**  Two schedule parameters were freed:
* the **cutoff exponent** `e` — `G4SchedBE` proves the parameter layer and all six budget terms
  at a free `e`, and `hbudget_holdsE_gen` states the budget over an *arbitrary sub-family* `sm`
  of the small primes: terms (a),(d) need `sm.card ≤ RE e + 1`, terms (b),(c) need
  `∑_{p∈sm} 1/p ≤ 3e+5`, and the gain term is the single `S`-dependent input, taken as `hlow`.
  So the `S`-restricted budget needs **no new analytic estimate**.
* the **outer dimension** `K = 4k₄` — `SchedB.hyp_KG`/`KG_ge`/`MG` let the witness take any
  `k₄ ≥ k₄bℓ b ℓ`, which is what makes the moment cap reachable: the Mertens loss inflates the
  cutoff by a constant `Dc ≈ 1/(c log 2)`, absorbed by `k₄ = max (k₄bℓ b ℓ) Dc`.
* the one non-monotone input is `SchedB.four_mul_le_two_pow_NE` (far-tail size), discharged by
  the moment cap itself (`e ≤ 2^{8K²}` vs `N K = 100K²`).

## 2. G5/Ω — §4A–§4D are structural and in kernel

* `G4OmegaWeight.lean` — `TWeight.cardFactors`: `Ω` as a `TWeight` with `ov = 0` (complete
  additivity).  §4C never sees the weight (the retained vector is the `ω`-vector on
  `smallPrimes R P₀`), so PropA/PropB/PropC are free from `G4TransportW`/`G4FrameW`.
  Plus `cardFactors_eq_omegaR_add_excess` and `excess_one_eq_cast`.
* `G4OmegaRemainder.lean` — the §4D structure:
  `cardFactors_split` (`Ω = [ω_{p∣P₀} + frozenExcess] + ω_{sm} + ω_big + junk`),
  `frozenWeightΩ`/`frozenTranslateΩ`/`frozenGammaΩ`/`blockSum_frozenΩ_eq` (the frozen bracket is
  constant on the progression → absorbed by `γ`), `blockSum_cardFactors_split`,
  `gridFrameW_cardFactors_Ffull_decomp`, and **`gridFrameW_cardFactors_propD`**:
  `PropD (δbig + δjunk + δfar)` from `bigAvgΩ`, `junkAvgΩ`, `farAvgΩ`.

So `Ffull` for `Ω` is the `ω` shape plus exactly ONE new term, the valuation junk.

## 3. Resume here (also in `PENDING_WORK.md`, top section)

1. **`junkAvgΩ_le`** — the only genuinely new arithmetic on the path to `isDisjunctive_Omega`.
   Input is already in kernel: `G4WeightJunk.sum_junk_le` at each shift `ρ_{α,jj}`, summed
   against the layer weights `bb^{-layer}`.  Target shape
   `junkAvgΩ ≤ rowL1 bb G.K · (2(log ω(P₀) + 2) + 2P₀(√(X+ρmax)+1)log₂(X+ρmax)/X)`.
2. `bigAvgΩ_le` / `farAvgΩ_le` — should be the existing `ω` estimates verbatim (`omegaBig` is
   literally the same function; the far tail needs `cardFactors_le_log` where the `ω` proof
   used `ω(m) ≤ log₂ m`).
3. Schedule: `hbig`/`hfar` gain the junk term (no new `Hyp` field at `c = 1`), then
   `isDisjunctive_Omega` through `isDisjunctive_of_framesW`.
4. `∑_n Ω(n)/bⁿ = ∑_{p,a≥1} 1/(b^{pᵃ}−1)`.

## 4. Session commits (this lap)

`ad2eaf5` free-cutoff budget over any sub-family · `5a9fb62` `scheduleWitnessSE` ·
`03cf3a7` **campaign A headline** · `ce83a97` `Ω` as a `TWeight` · `0e25078` `Ω` §4D + PropD.
`DIRECTION.md` CURRENT DIRECTIVE was reset this lap (review) to campaign A's ladder; that
ladder is now complete, so the next altitude lap should retarget it at G5/Ω.
