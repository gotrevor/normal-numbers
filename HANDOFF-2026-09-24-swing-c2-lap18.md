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

## The crux now

**`carryLeaf_holds` still `sorry`, and the gap is exactly `TauMomentPrimes`** — no longer "a
first moment along a progression" (proved) but "the transfer of that first moment from the
integers of a progression to its primes".

Next actions:
1. `carryLeaf_of_tauMomentPrimes` — the plumbing: the carry `Σ_{k≥1} τ(2^a p + K + k)/b^k` is a
   series, so one needs `TauMomentPrimes` simultaneously for the `O(K)` shifts `e = K+k` that
   are not damped by `b^{-k}` (for `k ≥ log_b(2^a p)` the trivial bound `τ(m) ≤ m` suffices).
   A union bound over those `O(b^{K/2})` shifts costs a factor that the density `≪ log/T` can
   absorb; make that explicit.  This is bookkeeping, not new mathematics — worth landing.
2. Attack `TauMomentPrimes`.  The cheapest honest route is NOT the sieve but the escape recorded
   in lap 17 §2: if (K2) could be met by a congruence rather than by a prime, `card_large_tau_le`
   alone closes `CarryLeaf`.  Escapes (i) force the cofactor `= 1` by size and (ii) two surviving
   slots are still unrefuted and are route-decisive.
3. `constructionInputs_even` (off path, the QR layer) is unchanged.

## Gotcha recorded

`omega` fails on a goal `2^(k+1) - 2^k = 2^k` when other `2^j`-shaped atoms are in context;
`rw [pow_succ]; generalize (2:ℕ)^k = z; omega` works.
