# HANDOFF 2026-09-24 — swing at C2, lap 20

Branch `wip/swing-c2`, HEAD `08c7e40`, working tree **clean**, `lake build` **green**
(9177 jobs).  Predecessor: `HANDOFF-2026-09-24-swing-c2-lap19.md` (laps 18a–19).

## Headline of the lap

**The gcd loss — the blocker since lap 18i — is closed, exactly and uniformly.**  The quantity

    τ(gcd(M, 2^a r + K+1+k))     M = killModulus b (ℓ+K)

was bounded by `τ(M)` at lap 18i (fatal) and by `2^{ω(M)}` at lap 18j (fatal, gap `K/log K`).
It is now **proved `≤ 2^k`**, at every shift and for every base — strictly below the `2^k` that
`TauMomentPrimesShift`'s geometric threshold already carries, with `(k+1)b^K/4` untouched.

Alongside it, the whole **integer-level crux is sorry-free**: the shifted first moment along a
progression now has NO hypotheses at all beyond `0 < e < 2^a` and `0 < M`.

## Files

* `src/NormalNumbers/SwingC2.lean` — **4 `sorry`s** (was 2; the rise is the decomposition,
  see "The two leaves"): `survivorLeaf_of_struct`, `tauMomentPrimesShiftStruct_of_primeDensity`
  (both NEW, named, with the attack written out), `shiftedDivisorIncidence_holds` (superseded
  by the new route, kept per the kickoff's never-delete rule), `constructionInputs_even`
  (off path, the QR layer, unchanged since lap 17).
* `src/NormalNumbers/SwingC2Moment.lean` — unchanged, sorry-free.

## The chain now

    ConjC2 ⟸ … ⟸ SurvivorLeaf ⟸ TauMomentPrimesShiftStruct ⟸ PrimeDensityAP
                        (leaf 2)                    (leaf 1)

`PrimeDensityAP` is the ONLY genuinely open input.  Everything else is a theorem.

## Proved this lap (18 green commits, all `#print axioms`-clean)

**Kill-progression structure** — `exists_kill_progression'` now returns five conclusions
(the original two, plus):
3. every prime of `gcd(M, n+1+j₀+e)` is `≤ j₀+e`  (`q ∣ n+c_k` ⟹ `q` divides the positive
   difference `1+j₀+e−c_k`);
4. (`3 ≤ b`) no kill prime divides `n+1+j₀+e` twice, when `j₀+e < q²`;
5. for each kill prime `q` there is a slot offset `c ≤ L` with `q^j ∣ n+1+j₀+e ⟹
   q^j ∣ (1+j₀+e)−c` for all `j ≤ b−1`.
Corollaries: `lt_of_prime_dvd_killModulus`, `coprime_killModulus_shift`,
`factorization_killModulus_le`, `card_divisors_le_two_pow`, `card_divisors_gcd_shift_le`,
`gcd_shift_dvd_window_sq`, `eight_sq_add_le_two_pow`,
**`card_divisors_gcd_shift_le_two_pow`** (the unified `τ(gcd) ≤ 2^{j₀+e−L}`).

**Incidence / moment layer** — `filter_shift_eq_empty`, `sum_card_shift_dvd_le'`,
`filter_shift_eq_empty_even`, `sum_card_shift_dvd_le_odd`, `card_shift_dvd_le_lcm`,
`sum_card_shift_dvd_le_gcd`, **`gcd_dvd_gcd_shift`**, `sum_card_shift_dvd_le_gcd'`,
`tau_two_pow_mul_odd`, `tau_shift_two_adic`/`'`, `tau_shift_sum_AP_odd`,
`tau_shift_sum_AP_odd_gcd`, `tau_shift_sum_AP`, **`tau_shift_sum_AP_gen`**,
`card_large_tau_shift_le`, `exists_good_prime_of_density` (the pigeonhole, extracted).

**Construction layer** — `exists_survivor_exponent_large`, `exists_survivor_data_large`.

## Findings (do not re-derive)

7. **The loss is `τ(gcd(M, c·r+e))` EXACTLY** (`gcd_dvd_gcd_shift` + the fibration of
   `sum_card_shift_dvd_le_gcd`): fibring the incidence sum by `g = gcd(d,M)` and using
   `lcm(d,M) = (d/g)M`, each fibre alone satisfies the full coprime bound, so the total loss
   is the NUMBER of gcds that occur.  No `ω(M)`, no `τ(M)`.
8. **The `b`-free refinement is load-bearing.**  Routing the large-shift regime through the
   obvious `v_q ≤ b` gives `τ ≤ (b+1)^{L log₂(L+k)}`, which fails against `2^k` at the
   crossover for every `b ≥ 13`.  `v_q(gcd) ≤ v_q(D)+1 ≤ 2 v_q(D)` removes the `b`.
9. **The survivor exponent must be pushed up.**  `tau_shift_two_adic` needs `e < 2^a`, but
   `exists_survivor_exponent` allows `a = 0`.  The exponent equation pins `a` only mod `b^ℓ`,
   so `a` is free above any `A` (`exists_survivor_exponent_large`); the residue `r` is chosen
   AFTER `a`, so raising `a` costs nothing.
10. **(K2) cannot avoid primes** (refuted this lap, three ways).  `τ(n+ℓ) ≡ t (mod b^ℓ)` for
    arbitrary `t` requires knowing the factorization exponents.  Pinning valuations at
    auxiliary primes leaves the cofactor free (prescribes only `t = 0`); fixing `τ = τ₀` gives
    a family no denser than the primes; varying `a` with `p` fixed leaves at most one
    admissible `a` in budget, since the valid `a` form an AP mod `lcm(b^ℓ, ord_M 2)` and
    `ord_M 2` can be of size `M`.  So `PrimeDensityAP` is intrinsic to this design.
11. **`PrimeDensityAP` is NOT unconditional.**  The budget `b^K ≳ (log Y)²` caps `log₂ Y` at
    `b^{K/2}`, while `log₂ M ≈ b(ℓ+K+5)^4` is polynomial in `K`.  So `M = exp((log Y)^θ)` with
    `θ` bounded away from `0` — never polylogarithmic in `Y`.  That is inside the classical
    zero-free-region range but OUTSIDE the range where a Landau–Siegel zero can be excluded.
    No choice of parameters inside this design escapes it.

## Next actions, in order

1. **`survivorLeaf_of_struct`** — the mathematics is all in the kernel; this is plumbing.
   Take `exists_kill_progression'` (5 conclusions) and `exists_survivor_data_large` with
   `A = Nat.log 2 (b^(K/4)) `, feed `card_divisors_gcd_shift_le_two_pow` into the `hgcd` slot
   of `TauMomentPrimesShiftStruct`, then run `exists_good_prime_of_density` and
   `carry_le_of_tau_geom`.  Needs `2^a r ≡ n₀+ℓ (mod M)` — add that to
   `exists_survivor_data_large`'s conclusion (the first bullet of its proof already proves it
   for primes `p`; the same computation gives it for `r`).
2. **`tauMomentPrimesShiftStruct_of_primeDensity`** — Markov on `tau_shift_sum_AP_gen`,
   union over shifts by `sum_le_of_geom_bound`, pigeonhole against `PrimeDensityAP`.
   Budget: `b^K ≥ 32(log₂e+1)2^k(log₂D+2)B²` with `B = b^{K/4}`, clears by `b^{K/4}`.
3. **`PrimeDensityAP`** — see finding 11.  Either formalize the classical zero-free region
   (project-scale), or accept the conditional theorem, which is what the kickoff names as the
   swing's main target.

## Gotchas added this lap

* `Nat.ord_proj_*` / `ord_compl` are renamed: `Nat.ordProj_mul_ordCompl_eq_self`,
  `Nat.not_dvd_ordCompl`, `Nat.ordCompl_pos`, `Nat.ordProj_dvd`.
* `Nat.pow_le_iff_le_log` does not exist; it is `Nat.le_log_iff_pow_le`.
* `Nat.factorization_eq_zero_of_non_prime` is `…_of_not_prime`.
* `Finset.sum_image` needs the summand given explicitly (`(f := fun x => …)`); higher-order
  unification fails otherwise.
* After `set D := …`, `omega` treats `D` and its body as DIFFERENT atoms — use `exact`/`le_trans`
  for steps that cross the definition, not `omega`.
