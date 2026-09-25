# HANDOFF c3-mrt 2026-09-25 — laps 7–11

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

## Lap 10 — the CRT reindex: the shifts ARE linear forms (same module)

* `dvd_add_iff_modEq` — `d ∣ n + c ↔ n ≡ M − c (mod d)` for any multiple `M ≥ c` of `d`
  (phrased with a large multiple to keep every residue in `ℕ`).
* **`exists_joint_class`** — for coprime `d, e > 0` there is a single `a < de` with
  `(d ∣ n+1 ∧ e ∣ n+2) ↔ n ≡ a (mod de)`, and `a` itself satisfies both divisibilities.
  Built from `Nat.chineseRemainder` + `Nat.modEq_and_modEq_iff_modEq_mul`.
* `sum_over_class_eq` — reindexing a residue class by its progression variable.
* `shift_div_eq_linear` / `'` — `(dej + a + 1)/d = ej + (a+1)/d`, and the companion for `e`.
* **`inner_sum_linear_forms`** — the payoff:

      ∑_{n<N, d∣n+1, e∣n+2} F(n) z₀^{Ω((n+1)/d)} z₁^{Ω((n+2)/e)}
        = ∑_j F(dej+a) · z₀^{Ω(ej + (a+1)/d)} · z₁^{Ω(dj + (a+2)/e)} .

  Two completely multiplicative unimodular functions, two **linear forms**, one progression
  variable: exactly the hypothesis shape of `Erdos67b.NonasymptoticLogElliott` at two points.

**Status of the `D = 2` chain.**  Every structural step from `ζ^ω`-correlation to
"`ζ^Ω` along linear forms" is now proved and axiom-clean:
`sum_pow_omega_two_shift_eq_coprime` (expand) → `inner_sum_linear_forms` (CRT) →
`bridge_truncation_bound` (truncate, uniformly in `N`).  What remains for the rung is
*analytic*, not structural: feed this into the dependency's log-Elliott theorem.

## Lap 11 — `C3MrtElliottMatch.lean`: the hypotheses of `NonasymptoticLogElliott` checked

The dependency's statement (read at
`.lake/packages/lean-proofs-latest/src/latest/ErdosProblems/Erdos67b/LogElliott.lean:411`) is

    ∀ a₁ a₂ : ℕ, b₁ b₂ : ℤ, 0 < a₁ → 0 < a₂ → a₁b₂ − a₂b₁ ≠ 0 → ∀ ε>0, ∃ A₀ ≥ 2, ∀ A X W …
      IsMultiplicativeOnPositiveInt g₁ → … → ‖elliottLogCorrelation g₁ g₂ a₁ a₂ b₁ b₂ X W‖
        ≤ ε · log W

with `elliottLogCorrelation = ∑_{X/W < n ≤ X} (1/n) g₁(a₁n+b₁) g₂(a₂n+b₂)`.  Two findings:

* **`IsMultiplicativeOnPositiveInt` is COMPLETE multiplicativity** (`g(mn) = g(m)g(n)` for all
  positive `m,n`, no coprimality).  So `z^ω` is excluded and `z^Ω` admitted — the lap-6
  diagnosis is confirmed against the actual Lean statement, not a recollection of it.
  `isMultiplicativeOnPositiveInt_zOmInt`, `norm_zOmInt_le_one` discharge both pointwise
  hypotheses for `zOmInt z = positiveIntExtension (z^Ω)`.
* **The non-degeneracy hypothesis is automatic, with determinant exactly `1`**
  (`linear_forms_det_eq_one`): with `a₁ = e, b₁ = (a+1)/d, a₂ = d, b₂ = (a+2)/e`,
  `a₁b₂ − a₂b₁ = (a+2) − (a+1) = 1` for **every** coprime powerful pair — no exceptional moduli
  to exclude.  This is the same unit determinant that forced coprimality in
  `coprime_of_joint_progression`, seen once in `ℕ` and once in `ℤ`.
* `integerAffine_eq_linear_form` / `zOmInt_integerAffine` — our summand is literally the
  dependency's summand, modulo the harmonic weight.

**The only remaining mismatch is the WEIGHT**, and it is a real one: `elliottLogCorrelation`
carries `1/n` over the log window `X/W < n ≤ X`, while laps 8–10 produce a flat sum over an
initial segment.  See NEXT.

## NEXT — resume here

0'. **Harmonic-weight truncation bound (the live obstruction).**  `bridge_truncation_bound`
   bounds the truncation error by `N · bridgeTail(Y)`, which is useless against a log-averaged
   main term of size `log N`.  Needed: the same bound with harmonic weights, where the
   progression `d ∣ n+1` carries mass `∑_{k ≤ N/d} 1/(dk) ≤ (1 + log N)/d`, giving error
   `(1 + log N) · bridgeTail(Y)` against a main term `≍ log N`.  The `1/d` is already present
   in `bridgeTail`, so the shape is right; this is bookkeeping with `Finset` harmonic sums, not
   new mathematics.  **Do this before attempting the instantiation.**
0. **Instantiate.**  Locate `Erdos67b.NonasymptoticLogElliott` in
   `.lake/packages/lean-proofs-latest`, read its exact statement (linear-form conventions,
   log-average normalisation, the `pretentiousDistSqToTwist` hypothesis), and match it against
   `inner_sum_linear_forms`.  The non-pretentiousness input for `ζ^Ω` is the *easier* case of
   lap 5's certificate (`ζ^Ω(p) = ζ`, constant on primes) — `C3MrtElliottForm.lean`.
   Watch for: the log-average weight `1/n` vs. our flat sum; and the `j`-range
   `{j : dej + a < N}`, which is an initial segment, so partial summation is available.
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
