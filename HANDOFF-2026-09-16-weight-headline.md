# HANDOFF 2026-09-16 — G5: `isDisjunctive_weight`, the general bounded-coefficient headline

Branch `wip/g5-prime-subset`, `lake build` green (9067 jobs).  `src/` carries exactly the two
pre-expedition forbidden-drift `sorry`s; zero `axiom`s.  Every declaration below prints
`[propext, Classical.choice, Quot.sound]`.

## Headlines now in the kernel

* `SchedB.isDisjunctive_residueClass` — `∑_{p ≡ a (q)} 1/(b^p − 1)`, `b ≥ 3` (earlier session).
* `SchedB.isDisjunctive_Omega` / `isDisjunctive_Omega_primePowerSum` —
  `∑ₙ Ω(n)/bⁿ = ∑_{q prime power} 1/(b^q − 1)`, `b ≥ 3`.
* **`SchedB.isDisjunctive_weight (c) (C) (hC : ∀ p, c p ≤ C) (hb : 3 ≤ b) :
  IsDisjunctive b (weightLambert b c)`** — every bounded coefficient vector.

## The route, this session

1. `TWeight.ov` made **signed** (`ℤ`, `|ov| ≤ ovC·ω(d)`): for `c_p ≥ 2` the weight is
   superadditive, so the ℕ-valued correction of the `ω`/`ω_S` interface cannot express it.
2. `TWeight.weight c C hC` — `ov_c(d,m) = ∑_{p∣d,p∣m}(1 − c_p)`, `ovC = max C 1`; §4A/§4B/§4C free.
3. `G4WeightRemainder` — the four-way split and `gridFrameW_weightC_propD`.
4. `G4WeightJunkAvg` — the three estimates: `bigAvgC` = the `ω` one; `junkAvgC` costs one
   factor `C`; `farAvgC` costs `κ = max C 1` via `weightW_le_kappa_mul_cardFactors`.
5. `G4SchedWeight` — `hjunk_holdsCE` (needs `100000·C·k₄³ ≤ 2^{k₄}`) and `hfarC_holdsE`.
   The far field needed the four `Ω` far pieces re-proved against a target smaller by
   `(1/2)^{k₄}` (`half_pow_le_target''`, `hfar_*_leSE`, `hfar_holdsSE`) — the decay is
   `2^{-50K²}`, so the spare factor is free, and it is exactly the room `κ ≤ 2^{k₄}` needs.
6. `G4WeightAssembly` — `exists_good_k₄` (take `k₄ = j + C` with `j ≥ max(50, 2C, k₄bℓ b ℓ)`;
   `cube_le_two_pow_shift`), the witness `scheduleWitnessCE`, and the headline.

## Next

The weight interface is now closed for all bounded `c`.  Open directions, in order of interest:
* unbounded `c` (e.g. `c_p = p`) — the junk factor is `C`, so this needs a different junk
  estimate, not a bigger `k₄`;
* combining the two axes: `w_c` restricted to a prime subset `S` (`ω_S + excess_{c·1_S}`),
  which would need the Mertens-in-AP cutoff *and* the `C`-inflated `k₄` simultaneously;
* base 2 for `Ω` (the far junk grows like `2^j`, so `bb ≥ 3` is a real wall — see
  `HANDOFF-2026-09-16-omega-schedule.md` §2).
