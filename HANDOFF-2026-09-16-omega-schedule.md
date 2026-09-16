# HANDOFF 2026-09-16 — G5/Ω: §4D closed, conditional headline in kernel, schedule 2/3 done

Branch `wip/g5-prime-subset`, HEAD `7873af5`, tree clean, `lake build` green (**9058 jobs**).
`src/` carries exactly the two pre-expedition forbidden-drift `sorry`s (`phaseOscillation`,
`exists_prime_nonresidue`); **zero `axiom`s**.  Every declaration added this session prints
`[propext, Classical.choice, Quot.sound]`.

## 1. Landed this session

**`src/NormalNumbers/G4OmegaJunk.lean`** (new) — §4D for `Ω`, all three `PropD` inputs closed:
* `junkAvgΩ_le` — valuation junk, via the *`n`-averaged* ℓ¹ row budget
  (`sampleAvg_abs_blockSum_le_of_shift`, weight-generic) + `sum_junk_one_le`.
* `bigAvgΩ_le'` — `bigAvgΩ = bigAvg` by `rfl`; the `ω` estimate verbatim.
* `farAvgΩ_le` — from `sum_abs_farPartΩ_le`, itself from `sum_cardFactors_shiftG_le`.
* `gridFrameW_cardFactors_propD_of_bounds` — `PropD` from three closed-form inequalities.

**`src/NormalNumbers/G4OmegaWitness.lean`** (new) — `ScheduleWitnessΩ` and the **conditional
headline** `isDisjunctive_cardFactorsLambert_of_witness`: `IsDisjunctive bb (∑ Ω(n)/bbⁿ)` for
`bb ≥ 3` given a witness at each omitted cylinder.  A/B/C came through the weight-generic
machinery untouched.

**`src/NormalNumbers/G4SchedOmega.lean`** (new) — the size arithmetic; **both new witness fields
are proved**:
* `hjunk_holdsE` (needs `k₄ ≥ 40`), `hfarΩ_holdsE` (`δfar = 11/64`).
* Supporting: `sum_inv_le_harmonic`, `sum_inv_sub_one_primeFactors_le_log`,
  `junkShiftBound_div_le'`, `junk_sqrt_term_le`, `junk_size_holdsE'`, `junkA_div_le`,
  `junkB_div_le`, `cardFactors_P₀_leE`, `log_card_primeFactors_P₀_leE`,
  `hfar_frozen_leE`, `hfar_junkA_leE`, `hfar_junkB_leE`, plus the power-of-two helpers
  (`eight_mul_le_two_pow`, `half_pow_mul_two_pow`, `half_pow_le_target(')`, `cube_le_two_pow`).

## 2. Three findings worth keeping

1. **Ω's far tail cannot reuse the `ω` proof.**  That rests on `2^{ω(m)} ≤ d(m)`, which *reverses*
   for `Ω`; and the pointwise `Ω(m) ≤ log₂ m` costs a `log X` the schedule cannot pay
   (`farC_leE` budgets `log P₀ + m + 10`).  Route: the §4D split itself,
   `Ω = ω + frozenExcess + junk`, `frozenExcess ≤ Ω(P₀)`, junk by `sum_junk_one_le`.
2. **Ω's far tail needs base `≥ 3`** — strictly more than the `ω` route's `bb ≥ 2`.  The junk at
   layer `j` grows like `2^j` (`junkShiftBound_layer_le`), so `∑ 2^j bb^{-j}` converges only for
   `bb > 2` (`hasSum_farJunkBound`).  Consistent with the headline's `b ≥ 3`.
3. **The frozen sum must be `log log`-size.**  `T(P₀) = ∑_{p∣P₀} 1/(p−1)` multiplies
   `rowL1 ≈ (2/3)^K`, while `ω(P₀)` is super-exponential in `K` (`logP₀Nat` contains `(K²+1)^K`).
   The `j`-th smallest prime factor is `≥ j+2`, so `T(P₀) ≤ harmonic ω(P₀) ≤ 1 + log ω(P₀)`
   (`sum_inv_sub_one_primeFactors_le_log`) — and `log ω(P₀) ≤ 15K²` kills it.

## 3. Resume here (the only gap to the unconditional Ω headline)

1. **`hbudget_holdsΩE`** — the budget with **four** deltas:
   `δ₁ + (δbig + δjunk + δfar) = 1/8 + (1/8 + 1/8 + 11/64) = 35/64`.
   `Sched.budget_assembly` currently proves `3/8 + A + Λ·(…) < 1` with `A ≤ 1/8` and
   `Λ·(…) ≤ 3e^{-4} + 2/64 ≈ 0.087`; so `35/64 + 1/8 + 0.087 ≈ 0.759 < 1`.  Write a
   `budget_assemblyΩ` copy of `G4ScheduleBudget.budget_assembly` with `35/64` in place of `3/8`
   (the `linarith` at the end takes it), then mirror `hbudget_holdsE`.
2. **`scheduleWitnessΩE`** — copy `SchedB.scheduleWitnessSE`
   (`G4SchedBEAssembly.lean:380–460`) field for field, with
   `ρmax := J K * gridDm K (N K)`, `hρm := Sched.shiftAL_le`, `hP₀ := G.P₀_pos`,
   `δjunk := 1/8`, `δfar := 11/64`, `hjunk := hjunk_holdsE`, `hfar := hfarΩ_holdsE`,
   and `k₄ := max (k₄bℓ b ℓ) 40` (the `40` is what `hjunk_holdsE` needs).
   The small primes are the *unfiltered* `smallPrimes (RE e) P₀`, so `hbudget` is
   `hbudget_holdsΩE` directly (no `hlow` hypothesis, no Mertens input — `Ω` is not `S`-restricted).
3. Then `isDisjunctive_Omega` = `isDisjunctive_cardFactorsLambert_of_witness` applied to that,
   and finally the closed form `∑_n Ω(n)/bⁿ = ∑_{p,a≥1} 1/(b^{p^a}−1)`.
