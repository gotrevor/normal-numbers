# HANDOFF c3-mrt 2026-09-25 — laps 7–9

Branch `wip/c3-mrt`.  `lake build` green at both commits; every new result axiom-clean
`[propext, Classical.choice, Quot.sound]`, no `sorry`.  Pure addition (2 new modules).
Prior state: `HANDOFF-c3mrt-2026-09-25-session-wrap.md` (laps 1–6).

## The crux is unchanged

`weylLambertTwist_holds` in `src/NormalNumbers/SwingC3Leaf.lean`.  `ConjC3` remains reduced
axiom-clean to `QuantDepthElliott` (quantitative Elliott, `O(log log log N)` points).

## Lap 7 — `C3MrtPowerfulSum.lean` (handoff item 1, DONE)

`summable_norm_sqfW_div (z) (‖z‖ = 1) : Summable fun d => ‖sqfW z d‖ / d`, i.e.
`∑_{d powerful} ‖z−z²‖^{ω(d)}/d < ∞` — the absolute-convergence certificate for lap 6's
`ω → Ω` bridge, in `Summable` form (stronger than the `tsum < ∞` the handoff asked for).
No Euler product.  Two new ingredients:

* `exists_cube_mul_sq_of_powerful` — every powerful `d > 0` is `a³c²`.
* `two_pow_omega_le_of_powerful` — `2^{ω(d)} ≤ 2·d^{3/8}` for powerful `d`.

The `5/8` exponent in the resulting `2 d^{-5/8}` majorant is forced: `2^{ω(d)}/d = d^{-1/2}`
exactly at `d = 4`, and the bare `1/2` leaves `∑_{a,c}(a³c²)^{-1/2}` divergent in `c`.  The
margin comes only from isolating the prime `2` (hence `primeFactors.erase 2` in the proof).

## Lap 8 — `C3MrtLinearForms.lean` (handoff item 2, DONE for `D = 1`)

* `pow_omegaNat_eq_sum_divisors'` — the **transposed** bridge, `z^{ω(m)} = ∑_{d∣m} g(d) z^{Ω(m/d)}`.
  This orientation is the load-bearing one: the *completely multiplicative* factor gets the
  quotient, so it is the one that ends up on a linear form.
* `sum_over_progression_eq` — the `n < N` with `d ∣ n+1` are exactly `n = dk−1`, `1 ≤ k ≤ N/d`.
* **`sum_pow_omega_shift_eq`** — the substitution lemma:

      ∑_{n<N} F(n) z^{ω(n+1)} = ∑_{d ≤ N} g(d) ∑_{1≤k≤N/d} F(dk−1) z^{Ω(k)} .

* `bridgeTail`, `bridgeTail_tendsto`, **`bridge_truncation_bound`** — for `‖F‖_∞ ≤ 1`,
  cutting the modulus at `d ≤ Y` costs `≤ N · bridgeTail(Y)` with `bridgeTail(Y) → 0`
  **independently of `N`**.  This is exactly where lap 7's summability is spent, and it is
  what makes the substitution usable inside a density statement (choose `Y` from `ε`, then
  `N → ∞`).

Net effect: a **one-shift** `ζ^ω` average is now, rigorously and with a uniform truncation, a
finite sum of `ζ^Ω` averages along the linear forms `k ↦ dk` — the shape
`Erdos67b.NonasymptoticLogElliott` is stated for.

## Lap 9 — `D = 2`, and the coprimality constraint (same module)

* `sum_pow_omega_offset_eq` — the substitution in **general form**: arbitrary finite index set
  `S` of `n`'s and arbitrary offset `c`.  Because `S` is arbitrary the lemma iterates: the
  `i`-th expansion runs *inside* the congruence conditions already imposed by the previous ones.
* `sum_pow_omega_two_shift_eq` — both shifts expanded:

      ∑_{n<N} F(n) z₀^{ω(n+1)} z₁^{ω(n+2)}
        = ∑_{d,e} g₀(d) g₁(e) ∑_{n<N, d∣n+1, e∣n+2} F(n) z₀^{Ω((n+1)/d)} z₁^{Ω((n+2)/e)} .

* **`coprime_of_joint_progression`** — a structural fact the `D = 1` case cannot see: the joint
  system `d ∣ n+1`, `e ∣ n+2` forces `gcd(d,e) ∣ (n+2)−(n+1) = 1`.  So the tuple sum is really
  over **coprime** powerful pairs (`sum_pow_omega_two_shift_eq_coprime`).  This is good news
  twice over: it shrinks the tuple sum, and coprimality is exactly the hypothesis under which
  the joint condition collapses to a single residue class mod `de`, i.e. under which the CRT
  reindexing to two linear forms is available at all.

## NEXT — resume here

0. **CRT reindex (`D = 2`).**  For coprime `d, e` produce `a < de` with
   `(d ∣ n+1 ∧ e ∣ n+2) ↔ n ≡ a (mod de)`, then reindex `n = de·k + a`, turning
   `(n+1)/d` and `(n+2)/e` into the linear forms `(de/d)k + (a+1)/d = ek + (a+1)/d` and
   `dk + (a+2)/e`.  Suggested route: `ZMod (d*e) ≃+* ZMod d × ZMod e` (`ZMod.chineseRemainder`),
   with `d ∣ n+1 ↔ (n : ZMod d) = -1`.  After this the `D = 2` rung is a pure instantiation.
1. ~~**`D`-fold version.**~~  Done for `D = 2` (lap 9); the general `D` needs only the same
   iteration over `Fintype.piFinset`, and  Apply `sum_pow_omega_shift_eq` with
   `F(n) = e(jn/Q) ∏_{1≤i<D} ζ_i^{ω(n+1+i)}` and iterate; the `i`-th application needs the
   shift `n+1+i`, i.e. the same lemma with `n + 1` replaced by `n + 1 + i` (generalise
   `sum_over_progression_eq` to the progression `n ≡ −(1+i) (mod d)` — the reindex is
   `n = dk − 1 − i`, valid once `d ∣ n+1+i`).  Then CRT the `D` moduli into `lcm d_i`, which is
   where the `D` linear forms `(L/d_i)k + (a+1+i)/d_i` appear.  Note the tuple truncation is
   already uniform: each factor contributes its own `bridgeTail`.
2. **Instantiate `Erdos67b.NonasymptoticLogElliott` at `D = 2`.**  Needs its
   `pretentiousDistSqToTwist` hypothesis for `ζ^Ω`; that is the *easier* case of lap 5's
   certificate (`ζ^Ω(p) = ζ`, again constant on primes).  Yields the log-averaged `D = 2` rung.
3. Turán–Kubilius halving (optional, modest; see laps 1–6 wrap).

## Still refuted — DO NOT RETRY

Unchanged from the laps 1–6 wrap: smooth/rough Kubilius split; self-similar recursion; growing
`P`; direct application of Tao's `unitCircleLogElliott`.
