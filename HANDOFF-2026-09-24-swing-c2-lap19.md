# HANDOFF 2026-09-24 — swing at C2, lap 19 baton

Branch `wip/swing-c2`, HEAD `f5531ff`, working tree **clean**, `lake build` **green**
(9177 jobs).  Predecessor with full narrative: `HANDOFF-2026-09-24-swing-c2-lap18.md`
(laps 18a–18j); before that `…-lap17.md`.

## Files

* `src/NormalNumbers/SwingC2.lean` — **2 `sorry`s**: `shiftedDivisorIncidence_holds`
  (the headline-path crux) and `constructionInputs_even` (off path, the QR layer, unchanged
  since lap 17).
* `src/NormalNumbers/SwingC2Moment.lean` — **NEW this session, sorry-free**, imported by
  `SwingC2.lean` and by `src/NormalNumbers.lean`.

## The chain (every `⟸` machine-checked)

    ConjC2 ⟸ tau_windowPrescribable ⟸ WindowPrescribable ⟸ WindowShape ⟸ SubLeafA
          ⟸ ConstructionInputsB ⟸ SurvivorLeaf ⟸ CarryLeaf ⟸ TauMomentPrimes
          ⟸ TauMomentPrimesShift ⟸ ShiftedDivisorIncidence      ← the ONLY open leaf

At lap 17 the open leaf was `CarryLeaf` (a mix of analysis and number theory).  It is now a
theorem, and so are the three links below it.  The open leaf contains **no carry, no series, no
divisor function and no `τ`**: it is one counting inequality about how often the primes of a
single arithmetic progression are hit by the classes `2^a p ≡ −e (mod d)`.

    ShiftedDivisorIncidence b :
      ∀ K M r a N, 2 ≤ K → 0 < M → gcd(r,M)=1 → a ≤ b^(K/4) → M ≤ 2^(b^(K/4)) → N ≤ b^(K/4) →
        ∃ Y P, (∀ p ∈ P, N < p ∧ p.Prime ∧ p ≡ r [MOD M] ∧ p ≤ Y) ∧ 0 < P.card ∧
          ∀ k, 8 * Σ_{d ≤ √(2^a Y + (K+1+k))} #{p ∈ P : d ∣ 2^a p + (K+1+k)}
                 ≤ b^K/4 * (k+1) * P.card

## What this session proved (all `#print axioms`-clean)

**In `SwingC2Moment.lean`** — `card_le_of_mod_eq`, `card_divisors_le_two_mul_small`
(`τ(n) ≤ 2#{d∣n, d≤√n}`), `sum_div_le_log` (dyadic harmonic), `tau_sum_AP_le`,
**`tau_sum_AP_le_log`** (first moment of `τ` over a progression, `gcd(r,M)=1`),
**`tau_shift_sum_le`** (hyperbola reduction in the shifted/sparse form),
**`card_shift_dvd_le`**, `sum_card_shift_dvd_le`.

**In `SwingC2.lean`** — `tau_sum_AP`, `card_large_tau_le` (exceptional set),
**`carry_le_of_tau_geom`** (`τ(N+1+k) ≤ A(k+1)2^k ⟹ carry ≤ 3A`, constant `b/(b−2)² ≤ 3`),
`carry_le_of_tau_le`/`'`/`carry_lt_of_tau_le` (linear versions, kept), `le_two_pow_pred`,
**`sum_le_of_geom_bound`**, **`dvd_of_dvd_shift`**, and the four implications
`carryLeaf_of_tauMomentPrimes`, `tauMomentPrimes_of_shift`,
`tauMomentPrimesShift_of_incidence`, plus the tightened `exists_pad_budget`.

## Findings recorded (do not re-derive)

1. **`CarryLeaf` was FALSE at `K=0`** for `b=3` — `probes/swingc2_carryleaf_K0.py`.  Fixed by
   `2 ≤ K`; `SurvivorLeaf` supplies `K ≥ 110`.
2. **A linear threshold `A(k+1)` cannot work** — the union bound over shifts then costs
   `√(2^a Y)`.  The geometric threshold `A(k+1)2^k` makes the union bound *free*.
3. **The CRT/Dirichlet escape from the sieve is circular** (needs `z ≈ m^{1/K}`, primorial
   doubly exponential past the budget).
4. **The `1/p`-weighted shortcut off `Σ_{p≡r(M)} 1/p = ∞` (mathlib `PrimesInAP`) is REFUTED**:
   the bad-set weight `≍ (log Y)²/2T` overtakes the total weight `≍ log log Y` once
   `Y > exp(exp(T))`.  A density lower bound at a fixed scale is unavoidable.
5. **Parameters tightened `K/2 → K/4`** (`exists_pad_budget` now returns `K = 20ℓ+200`), which
   turned the incidence requirement from critical (`b^K` vs `b^K`) into `3b^{K/2} ≪ b^K`.
6. **The gcd loss is `2^ω`, not `τ(M)`** (`dvd_of_dvd_shift`).  Remaining gap: a factor
   `K/log K` between the affordable `ω ≈ (K/2)log₂b` and the crude worst case
   `ω ≈ K²log b/(80 log K)`.

## Next actions, in order

1. **Cheapest and elementary: kill the `K/log K` gap.**  Each kill prime `q` offends on ONE
   residue class `k ≡ −(ℓ−1−j_q+K+1) (mod q)`, and there are only `L² ≈ K²` kill primes against
   `kb ≈ b^{K/4}` shifts.  Prove "for all but at most `K²` shifts `k`, `gcd(2^a p + K+1+k, M) = 1`"
   and absorb the exceptional shifts into the `2^{-k}` slack of `TauMomentPrimesShift`.  Then
   `sum_card_shift_dvd_le` applies verbatim to the good shifts.
2. **The second, independent input: a lower bound for `π(Y;M,r)`.**  Not in mathlib; finding 4
   shows it cannot be dodged.  Options: Siegel–Walfisz/Linnik (project-scale); or redesign (K2)
   (`exists_survivor_data`) so the witness comes from a family with an ELEMENTARY count in an AP.
3. If (1) stalls: Brun–Titchmarsh.  Mathlib's `NumberTheory/SelbergSieve.lean` supplies
   `BoundingSieve` and the Λ² diagonalisation but stops before the optimal-`λ` choice; the rest
   exists in `PrimeNumberTheoremAnd/Mathlib/NumberTheory/Sieve/Selberg.lean` (present under
   `.lake/packages` but NOT a declared dependency and built against a different mathlib rev —
   vendor or reprove, do not add the require blindly).
4. `constructionInputs_even` (off path, unchanged): the QR layer.

## Gotchas added this session

* `omega` fails on `2^(k+1) − 2^k = 2^k` when other `2^j` atoms are in context —
  `rw [pow_succ]; generalize (2:ℕ)^k = z; omega`.
* `omega` cannot use a hypothesis of the form `c * (k+1) ≤ A * (k+1)` with `A` an atom
  (atom × variable); extract the linear step first and `le_trans`.
* `Finset.card_filter_add_card_filter_not` takes the predicate only; membership after
  `Finset.card_le_card_of_injOn` is `↑s` (a `Set`), so use
  `simp only [Finset.coe_filter, Set.mem_ofPred_eq, …]`, not `rw [Finset.mem_filter]`.
