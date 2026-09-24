# HANDOFF 2026-09-24 — swing at C2, lap 18 (the elementary half of CarryLeaf is a theorem)

Branch `wip/swing-c2`, `lake build` **green** (9177 jobs).  Predecessor: `…-lap17.md`.
Target file `src/NormalNumbers/SwingC2.lean` (2 `sorry`s, unchanged) plus the NEW, sorry-free
`src/NormalNumbers/SwingC2Moment.lean`.

## The advance

Lap 17 named `CarryLeaf` as the sole open obligation on the headline path and listed as next
action 1(a) the elementary hyperbola first moment.  **That is now a theorem.**

`SwingC2Moment.tau_sum_AP_le_log` (sorry-free, `#print axioms` = `propext, Classical.choice,
Quot.sound`):

    0 < M → gcd(r,M) = 1 →
      Σ_{1 ≤ n ≤ X, n ≡ r (M)} τ(n)  ≤  2·( (X/M)·(log₂ √X + 2) + √X )

No sieve.  The proof is the two-step hyperbola argument, both steps proved from scratch:

* `card_divisors_le_two_mul_small` — `τ(n) ≤ 2·#{d ∣ n : d ≤ √n}` via the involution `d ↦ n/d`
  (with `n/d ≤ √n` from `n < (√n+1)²`);
* `card_le_of_mod_eq` — a finset of `[0,X]` all of whose elements agree mod `m` has `≤ X/m + 1`
  elements (inject by `x ↦ x/m`).  Applied with `m = d·M`: a divisor `d ≤ √n` of an `n` coprime
  to `M` is itself coprime to `M`, so `{n ≤ X : n ≡ r (M), d ∣ n}` is ONE class mod `dM`
  (`Nat.modEq_and_modEq_iff_modEq_mul`).  This is exactly where `gcd(r,M)=1` is load-bearing.
* `sum_div_le_log` — `Σ_{d ≤ D} ⌊Y/d⌋ ≤ Y·(log₂ D + 2)`, dyadic blocking, proved by induction
  on `k` for `D = 2^k` (each block `(2^k, 2^{k+1}]` contributes `≤ 2^k·⌊Y/2^k⌋ ≤ Y`).

Sanity anchor: `M=5, r=1, X=100` gives LHS `92`, RHS `132` (`#eval`-checked).

## Wired into `SwingC2.lean`

* `tau_sum_AP` — the above restated for `tau`.
* `card_large_tau_le` — **the exceptional-set form**, proved:
  `T · #{n ≤ X : n ≡ r (M), τ(n) ≥ T} ≤ 2((X/M)(log₂√X+2)+√X)`.
  For `T ≍ b^K` and `X` polynomial in `M ≤ 2^{b^{K/2}}` the right side is `≪ X/M`, i.e. almost
  every element of the progression is good.  **`CarryLeaf` over the INTEGERS of the progression
  is therefore no longer open.**
* `TauMomentPrimes` — the residual open half, now a NAMED `Prop` beside the leaf: the same first
  moment restricted to the primes of the progression (Brun–Titchmarsh / Selberg upper bound for
  `Σ_{p ≤ Y, p≡r(M)} τ(cp+e)`, plus a Linnik lower bound for `π(Y;M,r)` so the family is
  non-empty).  Neither ingredient is in mathlib.

## Also landed (lap 18b): the carry side is now PURE PLUMBING, and it is discharged

* `carry_le_of_tau_le` / `carry_le_of_tau_le'` / `carry_lt_of_tau_le` — **if `τ(N+1+k) ≤ A·(k+1)`
  for every `k`, then `4·carry b τ N ≤ 3A`, hence `carry < A` for `A > 0`.**  The `3/4` comes from
  `r/(1−r)² ≤ 3/4` at `b ≥ 3`, so no constant is lost.  `carry_le_sqrt` is the instance
  `A = 2√N+2`.  Note the hypothesis threshold GROWS linearly in `k`, and `τ(m) ≤ 2√m`
  (`tau_le_of_sqrt_small`) already gives it for every `k ≥ 2√N/A`: only `O(√N/A)` shifts need
  real input.
* `TauMomentPrimes b` — restated in the **family** form this forces (a single-shift existence
  statement cannot be union-bounded across a series): one prime `p` of the progression with
  `τ(2^a p + K + 1 + k) ≤ b^K·(k+1)` for ALL `k` at once.
* `carryLeaf_of_tauMomentPrimes` — **proved**.  `CarryLeaf` is no longer open: `carryLeaf_holds`
  is now a theorem modulo `tauMomentPrimes_holds`.

So `src/NormalNumbers/SwingC2.lean`'s headline-path `sorry` has MOVED from `carryLeaf_holds`
(a mix of analysis and number theory) to `tauMomentPrimes_holds` (pure analytic number theory,
a named literature statement).  The analysis is gone.

## The crux now

**`tauMomentPrimes_holds` is the single headline-path `sorry`**, and its content is exactly
"the transfer of the first moment of `τ` from the integers of a progression to its primes",
in the family form (Brun–Titchmarsh upper bound per shift + Linnik lower bound for
`π(Y;M,r)`, union-bounded over the `O(b^{K/2})` undamped shifts).

Next actions:
1. Attack `TauMomentPrimes`.  The cheapest honest route is NOT the sieve but the escape recorded
   in lap 17 §2: if (K2) could be met by a congruence rather than by a prime, `card_large_tau_le`
   alone closes `CarryLeaf`.  Escapes (i) force the cofactor `= 1` by size and (ii) two surviving
   slots are still unrefuted and are route-decisive.
3. `constructionInputs_even` (off path, the QR layer) is unchanged.

## Gotcha recorded

`omega` fails on a goal `2^(k+1) - 2^k = 2^k` when other `2^j`-shaped atoms are in context;
`rw [pow_succ]; generalize (2:ℕ)^k = z; omega` works.
