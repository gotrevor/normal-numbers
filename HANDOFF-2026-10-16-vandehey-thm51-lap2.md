# Vandehey Theorem 5.1 lap 2: local prime-power order bounds

## Concrete advance

- Proved the odd-prime LTE core of Vandehey Lemma 2.1 in
  `src/NormalNumbers/VandeheyKorobov.lean`:
  `padicValNat_pow_sub_one_le_add_of_odd_prime`.  For fixed `q` with
  `p | b^q - 1`, it shows
  `v_p(b^n - 1) <= v_p(b^q - 1) + v_p(n)`.
- Proved its multiplicative form
  `prime_pow_le_fixedPart_mul_exponent_of_odd`: if
  `p^t | b^n - 1`, then `p^t <= p^{v_p(b^q-1)} n`.
- Proved the exceptional 2-adic companions
  `padicValNat_two_pow_sub_one_le_add` and
  `two_pow_le_fixedPart_mul_exponent`.  The fixed exponent is required to be
  even; 2-adic LTE then absorbs the extra `v_2(b+1)` term.  This closes the
  local arithmetic split identified in lap 1 without assuming the odd-prime
  LTE theorem at `p = 2`.

These four lemmas are sorry-free and are the local factors needed to prove
`div_bigM_le_orderOf`.  The global product/CRT aggregation remains explicit
proof debt in that frozen theorem.

## Verification actually run

- `lake env lean -j 1 src/NormalNumbers/VandeheyKorobov.lean` -- passed; the
  only warning is the disclosed `sorry` in `div_bigM_le_orderOf`.
- `~/personal/bin/lean-green /Users/gotrevor/src/nn-vandehey --target NormalNumbers.VandeheyProof`
  -- `Build completed successfully (8924 jobs)`; final verdict
  `FORMALIZE-TIER GREEN`.

The default high-thread elaborator intermittently hit the container's open-file
limit while loading the large import closure.  `-j 1` was stable; this was an
environmental import failure, not a Lean proof failure.

## Current blocker

Rung 1 is not yet assembled globally.  Set
`L = orderOf (b : ZMod (primeProd P))`, `q = 2*L`, and
`n = orderOf (b : ZMod m)`.  For each `p | m`, one must:

1. map `b^L = 1 (mod primeProd P)` to `ZMod p`, obtaining
   `p | b^q - 1`;
2. use `b^n = 1 (mod m)` to obtain
   `p^{v_p(m)} | b^n - 1`;
3. apply the appropriate local lemma above; and
4. aggregate the prime-power inequalities without multiplying one copy of `n`
   per prime.  The final point requires using that the excess prime powers each
   divide `n` (or an lcm/factorization formulation), not merely multiplying the
   individual inequalities.

## Next highest-value attack

Strengthen the two multiplicative local lemmas from inequalities to divisibility:
`p^(t - beta_p) | n`.  Their LTE proofs already give the exponent inequality,
and `padicValNat_dvd_iff_le` supplies the conversion.  Then factor
`m / bigM b P` prime-by-prime and show it divides `n`; `Nat.le_of_dvd` finishes
`div_bigM_le_orderOf`.  After rung 1 is closed, continue kickoff rung 2 by
instantiating the already-proved Parseval--orbit lemma for the subgroup
`<b> <= (ZMod m)^*`.

Do not call `box done`: `VandeheyProof.lean` still contains the headline
`sorry`, and its axiom gate cannot yet pass.
