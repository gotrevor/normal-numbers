# HANDOFF 2026-09-16 (late) — G5: the general weight headline, and the merged `w_{c,S}` frame

Branch `wip/g5-prime-subset`, HEAD `130160f`, tree clean, `lake build` 🟢 **9067 jobs**.
`src/` carries exactly the two pre-expedition forbidden-drift `sorry`s (`phaseOscillation`,
`exists_prime_nonresidue`); **zero `axiom`s**.  All headlines print
`[propext, Classical.choice, Quot.sound]`.

## Headlines closed this session

1. **`SchedB.isDisjunctive_Omega`** : `3 ≤ b → IsDisjunctive b (∑ₙ Ω(n)/bⁿ)`, and
   **`isDisjunctive_Omega_primePowerSum`** : the same constant as
   `∑_{q a prime power} 1/(b^q − 1)` (`G4OmegaClosedForm`: `Ω n = #{q ∣ n : q a prime power}`
   by the sigma-bijection `(p,i) ↦ p^i`).
2. **`SchedB.isDisjunctive_weight c C hC (hb : 3 ≤ b) : IsDisjunctive b (weightLambert b c)`** —
   every bounded coefficient vector `c ≤ C`.

## How the general weight was closed (the chain, in dependency order)

* `G4TransportW`: `TWeight.ov` is now **ℤ-valued** with `|ov| ≤ ovC·ω(d)`.  Forced: for `c_p ≥ 2`,
  `w_c` is *superadditive* (`w_c(p²) > 2 w_c(p)`), so the ℕ-valued correction cannot express it.
  `omega`, `subset S`, `cardFactors` keep their proofs at `ovC = 1, 1, 0`.
* `G4WeightTW`: `TWeight.weight c C hC`, `ov_c(d,m) = ∑_{p∣d,p∣m}(1 − c_p)`, `ovC = max C 1`.
* `G4WeightRemainder`: the four-way split and `gridFrameW_weightC_propD`.
* `G4WeightJunkAvg`: `bigAvgC` = the `ω` estimate; `junkAvgC` costs one factor `C`;
  `farAvgC` costs `κ = max C 1`, via `weightW_le_kappa_mul_cardFactors : w_c ≤ κ·Ω`.
* `G4SchedWeight`: `hjunk_holdsCE` (condition `100000·C·k₄³ ≤ 2^{k₄}`), and — the one real
  obstacle — `hfarC_holdsE`.  The far budget had no room for `κ`, so the four `Ω` far pieces were
  re-proved against a target smaller by `(1/2)^{k₄}` (`half_pow_le_target''`,
  `hfar_frozen/junkA/junkB_leSE`, `hfar_holdsSE`); the far tail decays like `2^{-50K²}`, so the
  spare factor is free and is exactly what `κ ≤ 2^{k₄}` consumes.
* `G4WeightAssembly`: `cube_le_two_pow_shift`, `exists_good_k₄` (`k₄ = j + C`,
  `j ≥ max(50, 2C, k₄bℓ b ℓ)`), `scheduleWitnessCE`, `exists_scheduleWitnessC`, the headline.

## Resume here

`G4SubsetCWeight` (new, committed) has the **merged weight**
`w_{c,S}(m) = ω_S(m) + ∑_{p∣m, p∈S} c_p (v_p(m) − 1)` as a `TWeight`
(`TWeight.weightS`), with `weightSW_zero` (`= ω_S`) and `weightSW_univ` (`= w_c`) showing both
closed headlines are its instances.  §4A/§4B/§4C are therefore already done for it.

**Next: §4D for `w_{c,S}`.**  Port `G4WeightRemainder` + `G4WeightJunkAvg` with the small primes
`S`-filtered:
1. the split `w_{c,S} = [ω_{S,p∣P₀} + frozenExcess_{c'}] + ω_{S,small} + ω_{S,big} + junk_{c'}`
   — the `S`-side pieces are in `G4SubsetJunk`, the `c'`-side in `G4WeightJunkAvg`, and `c'` is
   literally `coeffOn S c`, so both halves are already available;
2. the witness type: `ScheduleWitnessS` (which carries the Mertens `hlow` through
   `hbudget_holdsE_gen` at the `S`-filtered small primes) with `ScheduleWitnessC`'s two §4D
   fields;
3. the schedule then needs **both** free parameters at once: the cutoff `e` from
   `MertensAP.exists_cutoff_subset` and `k₄ ≥` the `C`-condition of `exists_good_k₄` —
   they are independent (the `e`-side only enlarges `R`, the `C`-side only enlarges `k₄`), so
   `exists_scheduleWitnessS` and `exists_good_k₄` should compose without a new estimate.

Also open (ranked in `PENDING_WORK.md`): unbounded `c` (needs a `c_p/p`-weighted junk estimate —
no `k₄` can fix a junk budget linear in `C`); base 2 for `Ω` (refuted for this route).
