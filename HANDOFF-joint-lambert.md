# HANDOFF — joint Lambert: PRIME SELECTION proved

Date: 2026-09-27.  Operator objective recorded at the top of `DIRECTION.md`
(bounded run after `566586a`; target = prime selection with a quantitative count).

## Result

`NormalNumbers.JointLambert.exists_joint_prime_candidates`, in the new
`src/NormalNumbers/JointLambertPrimeSelection.lean`, is **proved, sorry-free**.

```
#print axioms NormalNumbers.JointLambert.exists_joint_prime_candidates
  -- [propext, Classical.choice, Quot.sound]
#print axioms NormalNumbers.JointLambert.exists_prime_allocation
#print axioms NormalNumbers.JointLambert.exists_prime_allocation_nonvacuous
#print axioms NormalNumbers.JointLambert.exists_selection_scale
#print axioms NormalNumbers.JointLambert.pool_card_ge
#print axioms NormalNumbers.JointLambert.count_lower_bound
  -- all [propext, Classical.choice, Quot.sound]
```

`lake build` green.  Module in the root build (`src/NormalNumbers.lean:501`).  The
three frozen files are byte-identical to their pins: `JointLambertStatement.lean`
vs `78e6048`, `JointLambertEncodingProof.lean` vs `7f05cb2`,
`JointLambertArithmetic.lean` vs `566586a` (`git diff` empty in all three).

## The two analytic inputs — named `Prop`s, passed as hypotheses

Neither is a global axiom; neither is `PrimeDensityAP` (the old vacuous one is not
imported or used anywhere in this file).

* `AGP` — `∃ X0 D0, ∀ X ≥ X0, ∃ Dset, #Dset ≤ D0 ∧ (∀ D ∈ Dset, log X < D) ∧ ∀ B u,
  1 ≤ B → (B:ℝ) ≤ X^(1/4) → (u,B)=1 → (∀ D ∈ Dset, ¬ D ∣ B) →
  X/(2 φ(B) log X) ≤ #{z ≤ X | z.Prime ∧ z ≡ u [B]}`.  The exceptional set is bound to
  `X` alone, hence chosen **before** `B`, `u` and the allocation, exactly as §3 demands.
* `PrimeIntervalSupply` — `∃ L0, ∀ L ≥ max(L0,2), (L:ℝ)/(3 log L) ≤ #{primes in Ioo L (2L)}`
  — the **open** interval, and the constant `3` is not improved.

## Contract of the target (as proved)

For fixed `c ≥ 2`, `a ≥ 2`, `r ≥ 1` and any cutoff `K`: there are `k ≥ K` with `r < k`
and, with the dyadic schedule `L = 2^k`, `U = 2^(k⁴)`, `X = U⁴ = 2^(4k⁴)`,

* `q` prime in the open `(L, 2L)`, and for each killed slot `j < k`, `j ≠ r` a family
  `p j t` (`t < j+1`) of primes in `(L, 2L)`;
* the **complete** `exists_joint_progression` conclusion for that data, retained clause
  by clause: `0 < R < A`, `1 ≤ u < B`, `R + r = Qu`, `A = QB`, `u ≡ 1 [MOD q]`,
  `(u,B) = 1`, `R + r ≡ Q [MOD q^a]`, `R + j ≡ P_j^(c-1) [MOD P_j^c]`,
  `c^(j+1) ∣ τ(R + mA + j)` at every killed slot for **every** `m`,
  `τ(R + mA + r) = 2a` whenever `u + mB` is prime, and `(R + j, A) = 1` for `k ≤ j < L`;
* `Q ≤ (2L)^(a-1)`, `B ≤ (2L)^(1 + c·killPoolSize k r)`, `B ≤ U`, `Q ≤ U`, `R > L`;
* `(M : ℝ)/(16 k⁴) ≤ #{m < M | (u + mB).Prime ∧ u + mB ≤ X}` with `M = X/B + 1`.

## How it is proved

1. **`exists_prime_allocation`** (the finite avoidance and allocation theorem).  A pool
   `S` of primes with `≥ 1 + killPoolSize k r + #Dset` members yields `q` and the whole
   killed-slot family distinctly in `S` with `∀ D ∈ Dset, D ≠ 1 → ¬ D ∣ jointB c k r q p`.
   The enabling structural lemma is **`prime_dvd_jointB`**: *every* prime divisor of
   `jointB` is a selected prime.  So removing, for each `D`, the least pool prime factor
   `f D` of `D` (`Finset.min'` of `D.primeFactors ∩ S`) is enough, by one contradiction:
   if `D ∣ jointB` then `D.minFac` is selected, hence in `S`, hence `f D` is defined and
   is itself a prime factor of `D` in `S`, hence also selected, hence in
   `T ⊆ S \ Removed` — contradicting `f D ∈ Removed`.  `D = 0` dies on `jointB_pos`; a `D`
   with no pool prime factor needs no removal at all.  At most `#Dset` primes are lost
   (`Finset.card_image_le`).
   Allocation itself flattens `(j,t)` by `killOffset k r j + t`, an injection into
   `[0, killPoolSize k r)` (`killOffset_add_le`, `killOffset_add_lt`, `killOffset_inj`),
   then uses `Finset.exists_subset_card_eq` + `Finset.orderEmbOfFin` to get an injective
   enumeration of a `1 + killPoolSize k r` element subset of the reduced pool.
   Control: `exists_prime_allocation_nonvacuous` (pool `{3,5,7,11}`, `Dset = {6}`,
   `k = 2`, `r = 1`, `c = 2`) — exercises the removal branch, not the vacuous one.
2. **Parameter availability, proved.**  `pow_four_le_two_pow`: `k⁴ ≤ 2^k` for `k ≥ 16`
   (tight at `16`), by induction with the monomial ladder `16 k^n ≤ k^(n+1)`.
   `exists_selection_scale` then produces `k = K + r + 16 + X0 + L0 + 4c + a + D0`
   satisfying `k ≥ K`, `r < k`, `16 ≤ k`, `L0 ≤ 2^k`, `X0 ≤ 2^(4k⁴)`,
   `3k(1 + k² + D0) ≤ 2^k` (pool supply), `(k+1)(1 + ck²) ≤ k⁴` (`B ≤ U`) and
   `(k+1)(a-1) ≤ k⁴` (`Q ≤ U`).  Nothing is assumed.
3. **`pool_card_ge`** converts `PrimeIntervalSupply` at `L = 2^k` into the *natural
   number* pool bound `1 + killPoolSize k r + D0 ≤ #S`, using `log(2^k) = k log 2`,
   `log 2 ≤ 1`, and `killPoolSize ≤ k²`.
4. **Size bookkeeping.**  `jointQ_le`, `jointB_le` (slotwise `P_j ≤ (2L)^(j+1)`, then
   `Finset.prod_pow_eq_pow_sum` over `killedIdx`), and `2L = 2^(k+1)` turn the two
   schedule inequalities into `B ≤ U`, `Q ≤ U`.  `lt_crt_solution` gets `R > L` from the
   slot-`0` CRT residue (slot `0` is always killed because `r ≥ 1`):
   `R % P₀^c = P₀^(c-1) ≥ P₀ > L`.
5. **`rpow_quarter_X`**: `X^(1/4) = U` *exactly*, which is the whole reason the schedule
   takes `X = U⁴` — AGP's `B ≤ X^(1/4)` becomes the clean `B ≤ U`.
6. **The count.**  `card_agp_le_card_candidates`: `z ↦ z / B` injects AGP's set of primes
   `z ≤ X` with `z ≡ u [B]` into `{m < X/B+1 | (u+mB).Prime ∧ u+mB ≤ X}`, because `u < B`
   pins `z = u + (z/B)·B`.  `count_lower_bound` then turns `X/(2 φ(B) log X)` into
   `(X/B+1)/(16k⁴)`: drop `φ(B) ≤ B`, use `log X = 4k⁴ log 2`, and apply
   `count_real_core` — `(t+1)/(16K) ≤ t/(8Kl)` whenever `t = X/B ≥ 1`, `0 < l ≤ 1`.  Note
   only `log 2 ≤ 1` is needed, so no numeric `log 2` bound is imported; the slack
   `l(t+1) ≤ 2t` is what absorbs the `+1` in `M`.
   (`Real.log_two_gt_d9` *is* used, once, and only to show every exceptional modulus is
   `≥ 2`: `log X = 4k⁴ log 2 ≥ 2` for `k ≥ 1`.)

## Exact next dependency

Prime selection is discharged.  The remaining obligations of the joint Lambert headline
`JointLambertDisjunctivity` are, in order:

1. **The shared binary tail majorant.**  One tail estimate serving every coordinate: with
   `n_m = R + mA`, bound the contribution of the non-prescribed digits so that the
   divisor-count data at slots `j ≠ r` and the survivor value `τ(n_m + r) = 2a` actually
   *pin the digits* of each `E_{b_i}` at the common offset.  The elementary
   divisor-average estimate of §3 (`∑_{m<M} τ(u+mA) ≤ 2M(1 + ½ log Y) + 2√Y` for
   `(u,A) = 1`) is the tool, and it is **not yet formalized**; it is the natural next
   Lean target, and it is purely elementary.  Together with the count proved here
   (`≥ M/(16k⁴)` prime candidates) it gives a surviving index by pigeonhole.
2. **The common-offset digit identity**, wiring the divisor counts `c^(j+1) ∣ τ(n_m+j)`
   and `τ(n_m+r) = 2a` through `evenEncoding` (already proved, `7f05cb2`) to the digit
   cylinders of every base simultaneously, with `c = lcm(bases)` entering via
   `divisor_count_dvd_of_dvd`.
3. **Arbitrarily late occurrences** — immediate from `K` being arbitrary here, once 1–2
   are in place.

Do **not** claim the full joint Lambert theorem: 1 and 2 remain.

## For the verification lap: why this run is finished

**The scoped objective is met.**  `--done-when 'sorry-free:src/NormalNumbers/JointLambertPrimeSelection.lean'`
and the operator override at the top of `DIRECTION.md` ("Stop when
`exists_joint_prime_candidates` is proved") are both satisfied:
`grep -c sorry src/NormalNumbers/JointLambertPrimeSelection.lean` is 0 (the only match is
prose in a docstring), `lake build` is green, and
`#print axioms NormalNumbers.JointLambert.exists_joint_prime_candidates` gives
`[propext, Classical.choice, Quot.sound]`.

**Why the repo-wide sorry gate cannot be cleared by this run.**  The remaining `sorry`s in
`src/` are all pre-existing, designated-open, and explicitly out of scope:

| file | status |
|---|---|
| `SwingC2.lean` (4) | long-standing audit surface |
| `SwingC1Log.lean` (2) | long-standing |
| `SwingC3Rotation.lean` (1) | long-standing |
| `PairDecoupleProve.lean` (1) | deliberately a `sorry`, not an `axiom` — it is a *conjecture* |
| `MahlerDriftOne.lean`, `PrimeLambertOscillation` | named designated-open in `DIRECTION.md` |

The operator override says **"Work only on prime selection and necessary helpers, no side
quests"** and the older CURRENT DIRECTIVE names `MahlerDriftOne` /
`PrimeLambertOscillation` as designated open.  `PairDecoupleProve`'s hole is a conjecture,
not a formalization gap.  So no lap of this run may touch any of them, and the repo-wide
gate is unsatisfiable here by construction — not merely hard.

**The exact ask for the operator.**  Either accept the scoped completion and close the run,
or authorize a new scope.  The next on-path target is already specified above and in
`PENDING_WORK.md`: the elementary §3 divisor-average estimate
`∑_{m<M} τ(u+mA) ≤ 2M(1 + ½ log Y) + 2√Y` for `(u,A)=1`, which is the shared binary tail
majorant and needs no analytic input.
