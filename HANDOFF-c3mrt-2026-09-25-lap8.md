# HANDOFF c3-mrt 2026-09-25 — laps 7–16

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

## Lap 12 — the harmonic-weighted truncation bound (obstruction of lap 11: CLEARED)

* **`bridge_truncation_bound_of_mass`** — the truncation bound in *weighted* form: if the
  weight puts mass `≤ B/d` on the progression of modulus `d`, then cutting at `d ≤ Y` costs at
  most `B · bridgeTail(Y)`.  The flat weight recovers `B = N`; the point is that `B` is now a
  parameter.  The `1/d` in the hypothesis is not an extra assumption — it is the automatic gain
  of summing any weight along a progression of modulus `d`, and it is exactly the `1/d` that
  `bridgeTail` already carries.  That coincidence is why the scheme survives log-averaging at
  all.
* **`harmonic_mass_bound`** — the harmonic weight `‖F(n)‖ ≤ 1/(n+1)` satisfies the hypothesis
  with `B = 1 + log N`: `∑_{k ≤ N/d} 1/(dk) = H_{⌊N/d⌋}/d ≤ (1 + log N)/d`
  (mathlib's `harmonic_le_one_add_log`).

So the truncation error is now `(1 + log N) · bridgeTail(Y)` against a log-averaged main term
of size `≍ log N` — the correct relative size, with `bridgeTail(Y) → 0` chosen from `ε` first.
The weight mismatch named in lap 11 is closed.

## Lap 13 — `C3MrtRungTwo.lean`: weight transfer, and WHAT the rung actually needs

* `sum_inv_sq_le` — `∑_{j≤J} j⁻² ≤ 2 − 1/J`, by telescoping (no appeal to Basel).
* **`weight_transfer`** — replacing the harmonic weight of the *original* variable
  `n = Lj + a` by that of the *progression* variable `j` (scaled by `1/L`) costs at most `2/L`,
  uniformly in the length of the sum and in the summand:
  `∑_j |1/(Lj+a) − 1/(Lj)| = ∑_j a/(Lj(Lj+a)) ≤ (a/L²)∑j⁻² ≤ 2/L`, using `a < L` from
  `exists_joint_class`.  Summed over the finitely many `(d,e)` with `d,e ≤ Y` this is a constant
  `C(Y)` depending on `Y` **but not `N`** — negligible against a main term `≍ log W`, because
  `Y` is chosen from `ε` before `N → ∞`.

**The decisive finding of this lap.**  The general two-point Elliott needed here is NOT proved
anywhere available: `Erdos67b.NonasymptoticLogElliott` is a `Prop`, and in this repo it is the
open, ratified bet `NormalNumbers.ElliottGeneral.nonasymptoticLogElliott` (`ElliottGeneral.lean`,
one `sorry`; Tao, Forum Math. Pi 4 (2016), Thm 1.3).  The dependency proves only
`Erdos67b.unitCircleLogElliott`, which covers `g₂ = conj g₁` along `n` and `n+h` — whereas our
two twists `ζ₀, ζ₁` are independent and our two forms have leading coefficients `e` and `d`.
Even the main term `d = e = 1` of the tuple sum is a *two-function* correlation, so it does not
reduce to the unit-circle case.  **The log-averaged `D = 2` rung is therefore equivalent to the
named open input**, not to something weaker.

## Lap 14 — the window mismatch: an initial segment IS a stack of Elliott windows

* **`elliottLogWindow_pow`** — holding the window ratio fixed at `W = A` and taking `X = A^i`,
  `Erdos67b.elliottLogWindow (A^i) A = Ioc (A^{i−1}) (A^i)` exactly.
* `sum_Ioc_pow_decomp` — those windows tile `(1, A^m]`, so an initial segment is the point
  `j = 1` plus `m` consecutive Elliott windows.
* **`norm_sum_Ioc_pow_le`** — if every window contributes `≤ B`, the initial segment
  `1 ≤ j ≤ A^m` contributes `≤ ‖f 1‖ + m·B`.

Why this is the right shape: Elliott at fixed `A` gives `B = ε log A` per window, so the stack
gives `ε·m·log A = ε·log(A^m)` — a bound **proportional to the log-mass of the segment**, which
is what a log-averaged statement must produce.  The `log A` per window does not accumulate into
anything worse; `m log A` is the log of the *length*, not `m` copies of the answer.  The single
uncovered point `j = 1` carries harmonic weight `1`, an additive `O(1)`.

With this, every mismatch between our sum and `Erdos67b.elliottLogCorrelation` is closed:
shape (lap 10), multiplicativity + non-degeneracy (lap 11), weight class (lap 12), weight
variable (lap 13), window (lap 14).

## Lap 15 — **`initial_segment_bound_of_elliott`**: the conditional rung, assembled

    (helliott : Erdos67b.NonasymptoticLogElliott) → ∀ ε > 0, ∃ A₀ ≥ 2, ∀ A ≥ A₀ at which ζ₀^Ω
    is non-pretentious, ∀ m,
      ‖∑_{1 ≤ j ≤ A^m} (1/j) · ζ₀^{Ω(ej + b₀)} · ζ₁^{Ω(dj + b₁)}‖  ≤  1 + ε · log(A^m).

`ε` times the log-mass of the segment plus an absolute constant: that IS the rung, for the
per-`(d,e)` term.  What is **not** a hypothesis of this theorem: multiplicativity,
unimodularity, and non-degeneracy, all discharged internally from lap 11.  The only hypothesis
left to the caller besides Elliott itself is non-pretentiousness of the first twist — the
genuinely arithmetic input (and the easier case of lap 5's certificate, `ζ^Ω(p) = ζ` being
constant on primes).

Axiom-clean: `[propext, Classical.choice, Quot.sound]`.  Elliott is an explicit hypothesis, so
nothing here rests on `sorryAx`.

## Lap 16 — a REAL gap in lap 15, found by reading `pretentiousDistSq`, and closed

`pretentiousDistSq f g X = ∑_{p ≤ X} (1 − Re(f(p)·conj g(p)))/p`, a sum of terms `≤ 2/p`, so
its size is `O(log log X)`.  Therefore the Elliott hypothesis `A ≤ pretentiousDistSqToTwist … X`
**cannot hold at small `X`**: for fixed `A` it needs `log log X ≳ A`, i.e. `X ≥ A^{i₀}` for a
threshold `i₀ = i₀(A)`.  Lap 15 demanded it at every window including `X = A` — unsatisfiable.

Fixed, and the fix is cheap:

* `sum_Ioc_pow_decomp_from`, **`norm_sum_Ioc_pow_le_from`** — the window stack may start at any
  level `i₀`, with the head `1 ≤ j ≤ A^{i₀}` bounded separately.
* `norm_head_le` — the head's harmonic mass is `≤ 1 + log(A^{i₀})`: a constant depending on `A`
  but **not on `m`**, hence negligible against the main term `≍ m·log A`.
* `initial_segment_bound_of_elliott` restated: non-pretentiousness is now required only at the
  scales `X = A^i` with `i > i₀`, and the conclusion is
  `≤ (1 + log(A^{i₀})) + m·ε·log A`.

This is the same pattern as the `j = 1` point (lap 14) and the weight-transfer constants
(lap 13): everything below the threshold is an `N`-independent constant, absorbed because the
quantifier order is `ε → Y → A → i₀ → N → ∞`.

## NEXT — resume here

0. **Non-pretentiousness for `ζ^Ω`.**  Supply the remaining caller hypothesis:
   `(A:ℝ) ≤ pretentiousDistSqToTwist (restrictToNat (zOmInt ζ₀)) χ t X` for all `q ≤ A`, `χ`,
   `|t| ≤ AX`.  Adapt lap 5's certificate in `C3MrtElliottForm.lean` (which is stated for
   `ζ^{ω_{>P}}`) to `ζ^Ω`; on primes both equal `ζ`, so the prime-sum that `pretentiousDistSq`
   measures is literally the same object — this should be a re-statement, not new analysis.
   Read `ErdosProblems/Erdos67b/Pretentious.lean:60` for the exact definition first.
   **Expect a `log log` ceiling** (lap 16): the achievable bound is
   `dist ≥ c(ζ₀,q)·log log X − O(1)`, so the certificate must be stated as "for every `A` there
   is `i₀` with the hypothesis holding at all `X = A^i`, `i > i₀`" — which is exactly the shape
   `initial_segment_bound_of_elliott` now consumes.  The constant `c` is
   `min over χ mod q ≤ A, t of the density of primes with χ(p)p^{it} ≉ ζ₀`, positive because a
   Dirichlet character cannot equal a fixed constant on a density-1 set of primes.
1. **Sum over the tuple.**  Combine `initial_segment_bound_of_elliott` over `d, e ≤ Y` with
   `sum_pow_omega_two_shift_eq_coprime` + `weight_transfer` + `bridge_truncation_bound_of_mass`.
   The per-pair constants (`1` from `j=1`, `2/L` from the weight transfer) sum to a `C(Y)`
   independent of `N`, so the order of quantifiers is: `ε` → `Y` → `A` → `N → ∞`.
2'. **Instantiate.**  Locate `Erdos67b.NonasymptoticLogElliott` in
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
