# HANDOFF 2026-09-16 — G5/Ω: the Ω headline is PROVED (unconditional, axiom-clean)

Branch `wip/g5-prime-subset`, `lake build` green (9060 jobs).  `src/` carries exactly the two
pre-expedition forbidden-drift `sorry`s (`phaseOscillation`, `exists_prime_nonresidue`); zero
`axiom`s.

## Landed this session

* `SchedB.hbudget_holdsΩE` (`G4SchedOmega.lean`) — the four-delta budget
  `1/8 + (1/8 + 1/8 + 11/64) = 35/64`, via a `budget_assemblyΩ` copy of `Sched.budget_assembly`
  with the head constant `35/64`; all five term bounds are the `e`-schedule's own.
* `SchedB.scheduleWitnessΩE` (`G4SchedOmegaAssembly.lean`, new) — the `ScheduleWitnessΩ`
  field for field: `scheduleWitnessSE` plus `hP₀`, `ρmax := J K * gridDm K (N K)`,
  `hρm := gridOf.shiftAL_le`, `δjunk := 1/8` (`hjunk_holdsE`), `δfar := 11/64`
  (`hfarΩ_holdsE`).  Extra demand over `ω`: `k₄ ≥ 40`.
* `SchedB.exists_scheduleWitnessΩ` — no Mertens input, so `k₄ = max (k₄bℓ b ℓ) 40` and the
  cutoff sits at its minimum `e = m₁ b K`; the moment cap comes from
  `MertensAP.moment_cap_subset` at `D = 1`.
* **`SchedB.isDisjunctive_Omega`** : `3 ≤ b → IsDisjunctive b (∑ₙ Ω(n)/bⁿ)`.
* `card_divisors_filter_isPrimePow` + `cardFactorsLambert_eq_tsum_inv`
  (`G4OmegaClosedForm.lean`, new) — `Ω n = #{q ∣ n : q a prime power}` by a sigma-bijection
  `(p,i) ↦ p^i`, hence `∑ₙ Ω(n)/bⁿ = ∑_{q prime power} 1/(b^q − 1)`.
* **`SchedB.isDisjunctive_Omega_primePowerSum`** — the headline in closed form.

`#print axioms` on both headlines: `[propext, Classical.choice, Quot.sound]`.

## Next

Campaign A items 1–4 and the `Ω` extension (item 4 of the operator override) are now closed:
`isDisjunctive_residueClass`, `isDisjunctive_subsetLambert`, `isDisjunctive_Omega`.  The next
open thread in `PENDING_WORK.md` is the `weightW c` family beyond `c ≡ 1` (general bounded
coefficient vectors) — the `Ω` route above is exactly the `c ≡ 1` instance and its junk/far
estimates are the ones a general `c ≤ C` would have to pay `C` times.
