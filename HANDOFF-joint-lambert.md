# HANDOFF — joint Lambert: §4 common arithmetic progression PROVED

Date: 2026-09-27.  Operator objective recorded at the top of `DIRECTION.md`
(bounded run after `7f05cb2`; target = paper §4 only).

## Result

`NormalNumbers.JointLambert.exists_joint_progression`, in the new
`src/NormalNumbers/JointLambertArithmetic.lean`, is **proved, sorry-free**.

```
#print axioms NormalNumbers.JointLambert.exists_joint_progression
  -- [propext, Classical.choice, Quot.sound]
#print axioms NormalNumbers.JointLambert.exists_joint_progression_nonvacuous
  -- [propext, Classical.choice, Quot.sound]
```

`lake build` is green (9272 jobs).  The module is in the root build
(`src/NormalNumbers.lean:500`).  `evenEncoding` was re-verified unchanged and
axiom-clean before any edit, and was not touched; `git diff 78e6048` on
`JointLambertStatement.lean` and `git diff 7f05cb2` on
`JointLambertEncodingProof.lean` are both empty.

## What the contract says (frozen)

Data, all supplied by the caller (this is the point — the later
exceptional-modulus avoidance chooses the primes; nothing is hard-coded to
consecutive primes):

* `c ≥ 2` (to become `lcm(bases)`), `a ≥ 2`, slots `1 ≤ r < k ≤ L`;
* a prime `q > L` with `jointQ a q = q^(a-1) > r`;
* for each killed slot `j < k`, `j ≠ r`, primes `p j t > L` (`t < j+1`), all
  distinct from one another across slots and all `≠ q`.

Derived: `slotProd p j = ∏_{t<j+1} p j t` (`P_j`), `killedIdx k r = (range k).erase r`,
`killCore c k r p = ∏_j P_j^c`, `jointA = q^a · killCore` (`A`),
`jointB = q · killCore` (`B`), `jointQ = q^(a-1)` (`Q`).

Conclusion: `∃ R u`, with `0 < R < A`, `1 ≤ u < B`,

* `R + r = Q·u`, `A = Q·B`, `u ≡ 1 [MOD q]`, `Nat.Coprime u B`;
* the **exact** CRT residues `R + r ≡ Q [MOD q^a]`, `R + j ≡ P_j^(c-1) [MOD P_j^c]`;
* `c^(j+1) ∣ τ(R + m·A + j)` at every killed slot, for **every** `m`;
* `τ(R + m·A + r) = 2·a` whenever `u + m·B` is prime;
* `Nat.Coprime (R + j) A` for every `k ≤ j < L`.

`τ` is `SwingC2.tau m = m.divisors.card` — real divisor cardinalities.
`divisor_count_dvd_of_dvd : b ∣ c → c^(j+1) ∣ τ n → b^(j+1) ∣ τ n` is the
elementary corollary that prepares `c = lcm(bases)` (the empty-base-set case is
handled separately, later).

No analytic input appears anywhere in the file: no AGP, no `PrimeDensityAP`, no
prime-interval supply.  The only `SwingC2` imports actually used are the proved
`tau`, `tau_mul_coprime`, `tau_prime`, `pow_card_dvd_tau`.

## How it is proved

Four new elementary helpers carry everything:

1. `factorization_eq_of_modEq_unit` — generalizes `SwingC2.factorization_eq_of_modEq`
   from residue `P^e` to `P^e · w` with `P ∤ w`.  This is the step the old scalar
   proof did not need: a CRT condition modulo `P_j^c` reduces at a single prime
   `p = p j t` to `n ≡ p^(c-1) · W^(c-1) [MOD p^c]` with `W` the product of the
   other `j` primes, and the valuation `v_p(n) = c-1` then follows.  Proved by
   `p^e ∣ n` and `¬ p^(e+1) ∣ n` via `Nat.Prime.pow_dvd_iff_le_factorization`.
2. `exists_crt_shifted` — pairwise coprime moduli `M j`, arbitrary shifts `s j`:
   `n + s j ≡ T j [MOD M j]` simultaneously on a class mod `∏ M j`.  Same shape as
   `SwingC2.exists_pin_progression`, but with the target residues free (the scalar
   version hard-wired `q^(b-1)`), which is what lets slot `r` carry `q^a` and the
   killed slots carry `P_j^c` in one system: `M j = if j = r then q^a else P_j^c`,
   `T j = if j = r then Q else P_j^(c-1)`, `s j = j`; `∏_{j<k} M j = A`.
3. `prime_not_dvd_both` — a prime `P` cannot divide both `R+x` and `R+y` for
   distinct `x, y < P`.  This single lemma discharges *all three* coprimality
   claims: `(u,B)=1` (via `p ∣ u ⟹ p ∣ Qu = R+r`, while `p ∣ R+j`), `q ∤ u`, and
   the free tail `(R+j, A)=1` for `k ≤ j < L`.  It is where `q > L` and
   `p j t > L` are used, and nothing else needs them.
4. `tau_prime_pow_mul_prime : τ(q^e·P) = 2(e+1)` for distinct primes — the
   survivor value, generalizing `SwingC2.tau_two_pow_mul_prime` off base 2.

Two places needed care and are worth not "simplifying":

* **`u < B` is not automatic.**  `Q ∣ R+r` and `R < A = QB` only give `u ≤ B`.
  Strictness comes from the residue: if `R+r = A + d` with `d < r`, then
  `(R+r) % q^a = d` since `q^a ∣ A`, whereas the CRT condition forces
  `(R+r) % q^a = Q > r > d`.  Hence `u < B`.  (`hqr : r < jointQ a q` is exactly
  the paper's "`Q > r` eventually", and it is used only here and for `0 < u`.)
* **`0 < R`** uses the slot `j = 0`, which is killed because `r ≥ 1`: `R = 0`
  would force `P_0^c ∣ P_0^(c-1)` with `P_0 ≥ 2`.

Non-vacuity is anchored by `exists_joint_progression_nonvacuous`
(`c = a = 2`, `r = 1`, `k = L = 2`, `q = 3`, single kill prime `5`; then
`A = 225`, `B = 75`, `Q = 3`, `R = 155`, `u = 52`).  The hypothesis bundle is
therefore satisfiable and the theorem is not vacuous.

## Exact next dependency

§4 is now discharged as an arithmetic statement.  The next Lean obligation is the
**prime selection** that feeds it, i.e. kickoff item 2, and it is the first place
an analytic input is unavoidable:

> Produce, from a source-faithful AGP exceptional-modulus hypothesis and a
> prime-interval supply hypothesis (both **explicit named hypotheses**; the old
> vacuous `PrimeDensityAP` must not be used), the data
> `q, p j t` satisfying the hypotheses of `exists_joint_progression` with
> `q, p j t ∈ (L, 2L)` distinct, avoiding the discarded prime of each exceptional
> modulus, together with `log B = O_c(k² log L)` and the count of `m < M` with
> `u + mB` prime.

Concretely the missing pieces, in order:

1. `O(k²)` distinct primes in `(L, 2L)` avoiding a set of `≤ D_0` forbidden
   primes, given `L / log L ≫ k²` — a counting statement about the prime supply,
   stated as a hypothesis, then *used* to build the `p j t` family (note
   `exists_joint_progression` takes the family as a function `ℕ → ℕ → ℕ` with
   validity only on the index set, so a `Finset`-indexed injection suffices).
2. `B ≤ X^{1/4}` and `Q ≤ (2L)^{a-1}` size bookkeeping with
   `k = ⌈4 log₂ log X⌉`, `L = ⌊(log₂ X)²⌋`.
3. The AGP count of prime `u + mB ≤ X`, `m < M = ⌊X/B⌋ + 1`, which needs
   `(u,B) = 1` — already supplied by this theorem.

After that comes §5 (**one** binary tail majorant `T_m` shared by all
coordinates — do not introduce per-coordinate survivor primes or a prime-tuples
hypothesis) and §6 (the common-offset digit identity), and only then may
`JointWords` / `JointLambertDisjunctivity` be claimed.  Nothing about the full
Lambert theorem is claimed now.
