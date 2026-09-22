# Prime model: end-to-end assembly of the frozen `KMT_quant₂`

Ren (Fable), 2026-09-22.  **Status: complete paper argument with every constant
fixed; Lean formalisation in progress in `src/NormalNumbers/PrimeModelKMT*.lean`.**
This note is the specification the Lean modules implement.  It builds only on
theorems already proved in the repository; every remaining step is elementary.

## Target (literal frozen statement, `G4WiringSparse.lean`)

For all `S`, `k = J`, `h ≠ 0` with `NontrivialWindow k h`, all `x ≥ 3` and
`1/log log x < ε < 1/2`:

    ‖windowMeanS S k h x‖
      ≤ C₁(k) · ( √log(1/ε) · √(2·recipSumIoc S ⌊x^ε⌋₊ x) + exp(−recipSumLe S ⌊x^ε⌋₊) )
        + C₂(k) · exp(−1/(8 k² ε))

with the explicit constants

    C₁(k) = exp(4k),        C₂(k) = exp(exp(k + 7)).

These satisfy `log C₁(k) = 4k = o(4^k)` and `log log C₂(k) = k + 7 = o(4^k)`, the
two growth hypotheses of `exists_sparse_normal_of_KMT_quant₂`.  The theorem is
uniform in `S` and in `h`: neither enters any constant.

Recall `windowMeanS S k h x = (1/x) ∑_{n<x} ∏_{j<k} e(h · ω_S(n+j+1) / 4^{j+1})`,
so the window sites are `n+1, …, n+k` and site `j+1` carries phase `h/4^{j+1}`.
`NontrivialWindow k h` asserts some `j ∈ [1,k]` has `h/4^j ∉ ℤ`; in particular
`k ≥ 1`.

## Regime split

**R1.** `ε > 1/(7680 k)`.  Then `‖W‖ ≤ 1 ≤ exp(960)·exp(−1/(8k²ε))`
(`brun_large_epsilon_absorbed`), and `exp(960) ≤ C₂(k)`.

**R2 (main).** `ε ≤ 1/(7680 k)`.  Combined with `1/log log x < ε` this forces
`log log x > 7680 k ≥ 7680`, so `x` is astronomically large and every size
condition below is automatic; no separate small-`x` regime is needed.

## Parameters (regime R2)

    y := ⌊x^ε⌋₊ ∈ ℕ,   Q := ∏_{p ≤ k prime} p  (primorial),
    T := x^{1/(4k)},    σ := log x / (4 log y),    R := y^σ = x^{1/4},
    P := {p prime : p ∈ S, k < p ≤ y},   ι := P (as a subtype),  p_i := i.

Facts (all elementary consequences of `log log x > 7680`, `ε log x > log x / log log x`):

- **F1** `x^ε ≥ e³`, hence `y ≥ x^ε − 1 ≥ x^ε / 2 ≥ e²`, `log y ≥ 2`.
- **F2** `1/ε ≤ log x / log y ≤ 2/ε`; hence `1/(4ε) ≤ σ ≤ 1/(2ε)` and
  `σ ≥ 1920 k ≥ 40·log(4^k e^{16k}) + 4`, the two size hypotheses of
  `brun_sifted_count_lower`.
- **F3** `y^σ = exp(σ log y) = x^{1/4}`, so `R² = x^{1/2}`.
- **F4** `⌊T⌋₊^k ≤ T^k = x^{1/4}`; `Q ≤ 4^k` (`primorial_le_4_pow`).
- **F5** `exp(−1/(8k²ε)) ≥ (log x)^{−1/8} ≥ x^{−1/4}` and `≥ 1/x`
  (from `1/ε < log log x`, `k ≥ 1`, `log x ≤ x`).

## Decomposition

Let `z_j := e(h/4^{j+1})` for `j < k`, so `|z_j| = 1` and
`e(h ω/4^{j+1}) = z_j^ω` for `ω ∈ ℕ`.  Write `ω_{≤y}(m) := #{p ∈ S prime, p ≤ y, p ∣ m}`
and `c(m) := ω_S(m) − ω_{≤y}(m) = #{p ∈ S prime, p > y, p ∣ m} ≥ 0`.

    W   := windowMeanS S k h x = (1/x) ∑_{n<x} ∏_j z_j^{ω_S(n+j+1)}
    W_y := (1/x) ∑_{n<x} ∏_j z_j^{ω_{≤y}(n+j+1)}
    M   := model expectation (defined below)

    ‖W‖ ≤ ‖W − W_y‖ + ‖W_y − M‖ + ‖M‖.

### E1: restoring the primes above `y`

For unit complex numbers, `|∏_j a_j − ∏_j b_j| ≤ ∑_j |a_j − b_j|`, and for
`|z| = 1`, `c ∈ ℕ`: `|z^{ω+c} − z^ω| = |z^c − 1| ≤ c·|z − 1| ≤ 2c`.  Hence

    ‖W − W_y‖ ≤ (2/x) ∑_{j<k} ∑_{n<x} c(n+j+1).

For fixed `j`, `∑_{n<x} c(n+j+1) = ∑_{p ∈ S, p > y} #{n < x : p ∣ n+j+1}`.  Only
`p ≤ x + k` contribute.  For `y < p ≤ x`: `#{n<x : p ∣ n+j+1} ≤ x/p + 1 ≤ 2x/p`.
For `x < p ≤ x+k`: at most one `n`, and there are at most `k` such primes.  So

    ‖W − W_y‖ ≤ 4k · recipSumIoc S y x + 2k²/x.                          (E1)

### E2: Cauchy–Schwarz against the interval Mertens bound

`primeRecipSum_le` (module `PrimeModelPrimeDimension`) gives
`∑_{y<p≤x} 1/p ≤ 8 + 12 log(log x / log y) ≤ 8 + 12 log(2/ε) ≤ 36 log(1/ε)`
(F2; `log(1/ε) ≥ log 7680 > 8`).  With `a := recipSumIoc S y x ≤ b := ∑_{y<p≤x} 1/p`,

    a = √a·√a ≤ √a·√b ≤ 6 √a √log(1/ε) ≤ 6 √log(1/ε) √(2a).

Therefore `4k · recipSumIoc S y x ≤ 24k · √log(1/ε) · √(2·recipSumIoc S y x)`.

### E3: `2k²/x ≤ 2k² · exp(−1/(8k²ε))` by F5.

### Phase factorisation

For `p ≤ k`, `p ∣ n+j+1 ⟺ p ∣ (n mod Q) + j + 1` since `p ∣ Q`.  For `p > k`, at
most one `j < k` has `p ∣ n+j+1`, and `hitShift k p n` records it
(`actual_state_sifted_iff` module).  Hence, with `g₁(r) := ∏_{p ∈ S, p ≤ k} ∏_j z_j^{[p ∣ r+j+1]}`
(`|g₁| = 1`) and `Φ(s) := ∏_{i ∈ ι} localPhase k z (s i)`,

    ∏_j z_j^{ω_{≤y}(n+j+1)} = g₁(n mod Q) · Φ(actualState P n).

### Empirical joint law

`ν(r,s) := #{n < x : n mod Q = r ∧ actualState P n = s} / x` on `Fin Q × (ι → Option (Fin k))`.
Partitioning `range x` by the map `n ↦ (n mod Q, actualState P n)` gives `∑ ν = 1` and

    W_y = ∑_{(r,s)} ν(r,s) · g₁(r) Φ(s).

### Model and its expectation

`μ := jointModel (Fin Q) k (primeRecip p)`, i.e. `μ(r,s) = weight(s)/Q`, mass one
(`jointModel_mass_one`).  Define `M := ∑_{(r,s)} μ(r,s) g₁(r) Φ(s)`.  Then

    M = ((1/Q) ∑_r g₁(r)) · ∑_s weight(s) Φ(s)
      = ((1/Q) ∑_r g₁(r)) · ∏_{i∈ι} (1 + A/p_i),      A := ∑_{j<k} (z_j − 1)

by `radical_phase_product_prime`.

### E5: the model phase contracts, uniformly in `h`

Let `j₀ ∈ [1,k]` be the **least** site with `h/4^{j₀} ∉ ℤ`.  Then `h/4^{j₀−1} ∈ ℤ`
(minimality, or `j₀ = 1`), so `h/4^{j₀} = m/4` with `4 ∤ m`, and
`z_{j₀−1} = e(m/4) ∈ {i, −1, −i}`; thus `Re z_{j₀−1} ≤ 0`.  Every other term of
`Re A = ∑_j (Re z_j − 1)` is `≤ 0`, so `Re A ≤ −1`.  Also `|A| ≤ 2k`.

For every `w ∈ ℂ`: `|1+w|² = 1 + (2 Re w + |w|²) ≤ exp(2 Re w + |w|²)`, so
`|1+w| ≤ exp(Re w + |w|²/2)`.  Apply with `w = A/p_i`:

    ‖∏_i (1 + A/p_i)‖ ≤ exp( Re A · ∑_i 1/p_i + (|A|²/2) ∑_i 1/p_i² )
                      ≤ exp( −∑_i 1/p_i + 2k² · (1/k) )
                      = e^{2k} · exp(−∑_{p∈P} 1/p),

using `∑_i 1/p_i² ≤ ∑_{n>k} 1/n² ≤ 1/k` (the `p_i` are distinct naturals `> k`).
Finally `recipSumLe S y = ∑_{p∈P} 1/p + ∑_{p ≤ k, p∈S} 1/p ≤ ∑_{p∈P} 1/p + k`, so

    ‖M‖ ≤ e^{3k} · exp(−recipSumLe S ⌊x^ε⌋₊).                             (E5)

### E4: empirical law versus model on the retained box

For every `r < Q` and every state `s`, with `A_s := stateA P s`, `U_s := stateU P s`:

    x · ν(r,s) = #{n<x : SiftedCond k A_s U_s Q r (stateShift P s) n}       (actual_state_sifted_iff)
              ≥ (1 − 2e^{−σ/2}) · (x/(Q ∏A_s)) ∏_{U_s}(1 − k/p) − R²         (brun_sifted_count_lower)
              = (1 − 2e^{−σ/2}) · x · μ(r,s) − R²                            (state_model_density)

Hypotheses of `brun_sifted_count_lower`: `k ≥ 1`; `y ≥ e²` (F1); `σ ≥ 1920k` and
`σ ≥ 40 log(4^k e^{16k}) + 4` (F2); primes of `A_s ∪ U_s` are `> k` and `≤ y`;
`A_s`, `U_s` disjoint; `Q > 0`, `r < Q`; `Q` coprime to every prime `> k`.

So `ν(r,s) ≥ (1 − η) μ(r,s) − e` with `η := 2e^{−σ/2}`, `e := R²/x`, on the box
`B := univ ×ˢ retainedBox k p T`.  `finite_phase_of_lower_atoms` with `f(r,s) = g₁(r)Φ(s)`:

    ‖W_y − M‖ ≤ 2 μ(Bᶜ) + 2η + 2 |B| e
              ≤ 2 · k e^{20} / T^{1/(2 log y)}  +  4 e^{−σ/2}  +  2 Q ⌊T⌋₊^k R²/x,

by `jointModel_tail` + `radical_box_tail_exp20` and `retainedBox_card_le`.  Each
term is absorbed by `exp(−1/(8k²ε))`:

- `T^{1/(2 log y)} = exp(log x/(8k log y)) ≥ exp(1/(8kε)) ≥ exp(1/(8k²ε))` (F2);
- `4e^{−σ/2} ≤ 4 e^{−1/(8ε)} ≤ 4 e^{−1/(8k²ε)}` (F2);
- `2 Q ⌊T⌋₊^k R²/x ≤ 2·4^k · x^{1/4} x^{1/2} / x = 2·4^k x^{−1/4} ≤ 2·4^k e^{−1/(8k²ε)}` (F3–F5).

## Total

    ‖W‖ ≤ 24k √log(1/ε) √(2 recipSumIoc) + e^{3k} exp(−recipSumLe)
          + (2k² + 2k e^{20} + 4 + 2·4^k) · exp(−1/(8k²ε)).

Since `24k + e^{3k} ≤ e^{4k} = C₁(k)` and `2k² + 2ke^{20} + 4 + 2·4^k ≤ exp(1000+2k)
≤ exp(exp(k+7)) = C₂(k)` (also `exp(960) ≤ C₂(k)` for R1), this is the frozen bound.

## Consequence

`exists_sparse_normal_of_KMT_quant₂ C₁ C₂ h₁ h₂ (this)` yields, unconditionally,

    ∃ S, DecidablePred S ∧ DivergentRecip S ∧ IsNormal 4 (subsetLambert S 4):

a prime set with divergent reciprocal sum whose base-4 Lambert constant is normal.
It does **not** say anything about `G₄` itself or any classical constant.

## Quantifier and indexing audit

- `S` and `h` are universally quantified inside `KMT_quant₂`; the proof never
  specialises them and no constant depends on them.  `Re A ≤ −1` uses only the
  least nontrivial site, whose existence is exactly `NontrivialWindow k h`.
- All shifts are `n+j+1` for `j < k` (`truncTailS`, `hitShift`, `SiftedCond`).
- `recipSumIoc S ⌊x^ε⌋₊ x` sums primes in `(y, x]` with `y = ⌊x^ε⌋₊`, exactly the
  set appearing in E1 after separating `(x, x+k]`.  `recipSumLe S ⌊x^ε⌋₊` sums
  primes `≤ y`, exactly `P ∪ (S-primes ≤ k)`.
- `ε` enters only through F1–F5; every inequality is stated for the actual
  integer `y = ⌊x^ε⌋₊`, never for `x^ε`.
- The sieve level is `R = x^{1/4}` and its remainder `R²`; the progression modulus
  `Q·∏A_s` never appears in an error term (the Brun theorem already absorbed it).
- Nothing is assumed about primes outside `S`: `ι` is the set of `S`-primes in
  `(k, y]`, and the sieve conditions only on those.

## Lean module plan

| Module | Content |
|---|---|
| `PrimeModelPhaseAlgebra` | `norm_one_add_le_exp`, `norm_prod_sub_prod_le`, `norm_pow_sub_one_le`, `sum_inv_sq_le` , `exists_site_re_nonpos` (least nontrivial site), `model_phase_norm_le` |
| `PrimeModelPhaseFactor` | `omegaSN` split at `y`; `phase_eq_residue_mul_state`; E1 |
| `PrimeModelJointLaw` | empirical law, mass one, fibre-sum identity, lower atoms from Brun, E4 |
| `PrimeModelParameters` | F1–F5, E2, E3 and the absorption inequalities (pure real analysis) |
| `PrimeModelKMT` | `KMT_quant₂_of_primeModel`, growth lemmas, `exists_sparse_normal_unconditional` |
