# Prime model: end-to-end assembly of the frozen `KMT_quant₂`

Ren (Fable), 2026-09-22.  **Status: PROVED.**  `KMT_quant₂_primeModel : KMT_quant₂ C₁ C₂`
and `exists_sparse_normal_unconditional` in `src/NormalNumbers/PrimeModelKMT.lean`
(main `e222677`), both `#print axioms` = `[propext, Classical.choice, Quot.sound]`; the five
modules PhaseAlgebra / PhaseFactor / JointLaw / Parameters / KMT are sorry-free.
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

---

# Part II: the family theorem

Ren (Fable), 2026-09-22, after the assembly above.  **Status: PROVED.**
`PrimeModelFamily.isNormal_subsetLambert_of_sparse : Sparse P → DivergentRecip P →
IsNormal 4 (subsetLambert P 4)`, `#print axioms` = `[propext, Classical.choice, Quot.sound]`;
`PrimeModelDensityMass` (M1, M1', M2) and `PrimeModelFamily` are sorry-free.  The exact failure
regime for the weaker hypothesis (relative density zero alone) is recorded below.

## Target

**Theorem (family).**  Let `P` be a set of primes with

    (D)  ∃ x₀, ∀ x ≥ x₀ :  π_P(x) ≤ π(x) / log log x,        (π_P(x) = #{p < x : p ∈ P})
    (∞)  ∑_{p ∈ P} 1/p = ∞.

Then `IsNormal 4 (subsetLambert P 4)`.

The proof is `isNormal_subsetLambert_of_KMT_along P J` for an explicit schedule `J_N`
built from the **actual accumulated mass** `S_P(y_N) = recipSumLe P y_N`, never from an
assumed lower divergence rate.  Inputs: `KMT_quant₂ C₁ C₂` (Part I, `C₁ = e^{4k}`,
`C₂ = exp(e^{k+7})`) and the existing `tail_error_L1`.

## Two analytic lemmas from (D)

**(M1) Dominated Abel summation.**  If `π_P(t) ≤ δ · π(t)` for every integer `t` with
`y < t ≤ N+1` (note `π_P(t)` counts `p < t`, so the endpoint `N+1` is needed: with `t ∈ [y,N]`
the statement is false, e.g. `y=2, N=3, P={3}, δ=0`), then

    recipSumIoc P y N  ≤  δ · ( ∑_{y<p≤N} 1/p + 1 ).

Proof: with `a_n = 1_P(n)`, `A = π_P`, `f(n) = 1/n`, summation by parts gives
`∑_{y<n≤N} a_n f(n) = A(N+1) f(N) − A(y+1) f(y+1) + ∑_{y<n<N} A(n+1)(f(n) − f(n+1))`.
Every `A(·)` is `≤ δ π(·)` and every coefficient is `≥ 0` except the dropped term, so the sum
is `≤ δ` times the same expression for `1_prime`, which equals `∑_{y<p≤N} 1/p + π(y+1)/(y+1)
≤ ∑_{y<p≤N} 1/p + 1`.  Combined with `primeRecipSum_le` (`∑_{y<p≤N} 1/p ≤ 8 + 12 log(log N/log y)`):

    recipSumIoc P y N ≤ δ · (9 + 12 log(log N / log y)).                          (M1')

**(M2) Accumulated mass.**  Under (D), for all large `N`,

    recipSumLe P N ≤ C_P + 100 · log log log N,

`C_P` a constant depending on `P` (its mass below `a_{i₀}`).  Proof: cut at
`a_i := ⌊exp exp 2^i⌋₊`.  On `[a_i, ∞)`, (D) gives `δ_i = 1/(2^i − 1)` (since
`log log t ≥ 2^i − o(1)` there), and `log a_{i+1}/log a_i ≤ 2 exp(2^i)`, so (M1') on
`(a_i, a_{i+1}]` gives `≤ (9 + 12(2^i + 1))/(2^i − 1)`, which is `45` at `i = 1` and `≤ 23` for
`i ≥ 2`; a uniform `≤ 45` suffices.  There are at most `log₂ log log N + 1 ≤ 2 L₃ + 1` ranges
below `N` for large `N`, giving the stated `100 · L₃` (the constant `100` is what
`recipSumLe_le_of_sparse` proves; an earlier draft of this paper printed `34 log₂ L₂`, which
fails at `i = 1` — corrected 2026-09-22 after Astra's audit).

## Schedule

For `N` large (`log log N > 4`), put

    ε_N := 2 / log log N,      y_N := ⌊N^{ε_N}⌋₊,
    J_N := min( ⌊(log log log N)/24⌋₊ ,  ⌊ S_P(y_N) / 8 ⌋₊ ).

`J_N → ∞`: the first entry by growth, the second by (∞) and `y_N → ∞`.  The frozen
`ε`-window holds: `1/log log N < ε_N < 1/2`.  Note `log log y_N ≥ (1/2) log log N` for large
`N` (`y_N ≥ N^{ε_N}/2`, `ε_N log N = 2 log N/log log N`).

## Verification of the four terms (all at `k = J_N`, `x = N`, `ε = ε_N`)

Write `L₂ = log log N`, `L₃ = log log log N`, `S = S_P(y_N)`.  From `J_N ≤ L₃/24`:
`e^{4J} ≤ L₂^{1/6}`, `4^{J} ≤ L₂^{0.06}`.  From `J_N ≤ S/8`: `e^{4J} ≤ e^{S/2}`.

1. **Fresh mass** (`C₁ √log(1/ε) √(2 recipSumIoc)`): by (M1') with `y = y_N`, `δ = 1/log log y_N
   ≤ 2/L₂` and `log(1/ε_N) = log(L₂/2) ≤ L₃`:
   `recipSumIoc P y_N N ≤ (2/L₂)(9 + 12 L₃)`, so the term is
   `≤ L₂^{1/6} · √L₃ · √((4/L₂)(9 + 12L₃)) ≤ 10 · L₃ · L₂^{1/6 − 1/2} → 0`.
2. **Old mass** (`C₁ exp(−recipSumLe P y_N)`): `≤ e^{S/2} e^{−S} = e^{−S/2} → 0` by (∞).
3. **Sieve** (`C₂ exp(−1/(8J²ε))`): `1/(8J²ε_N) = L₂/(16 J²) ≥ L₂/(16 L₃²)` and
   `log C₂ = e^{J+7} ≤ e^7 L₂^{1/24}`, so the term is `≤ exp(e^7 L₂^{1/24} − L₂/(16L₃²)) → 0`.
4. **Tail** (`(recipSumLe P (2N) + 5J + 12)/4^J`, `tail_error_L1`): by (M2),
   `recipSumLe P (2N) ≤ C_P + 100 L₃(2N) ≤ C_P + 101 L₃`.  Then
   `(C_P + 101 L₃ + 5J + 12)/4^J`.  Case `J_N = ⌊L₃/24⌋₊`: `4^J ≥ 4^{L₃/24 − 1} = L₂^{0.057}/4`,
   and `L₃/L₂^{0.057} → 0`.  Case `J_N = ⌊S/8⌋₊ < ⌊L₃/24⌋₊`: then `S < L₃/3 + 8` and also
   `recipSumLe P (2N) = S + recipSumIoc P y_N (2N) ≤ S + 1 ≤ 8J + 9` (item 1's bound at
   `2N`), so the tail is `≤ (13J + 21)/4^J → 0`.  In both cases `→ 0` because `J_N → ∞`.

Hence `KMT_along P J_N` and `TailOK P J_N`, and the wiring theorem gives normality.  Every
step is uniform in `P` except the two constants `x₀` and `C_P`, which enter only through
"for all large `N`".

## Why relative density zero alone does not close on this route

Suppose only `π_P(x) = o(π(x))`, say `π_P(t) ≈ π(t)/L₄(t)` (`L₄ = log log log log`).  Then the
accumulated mass is `S_P(N) ≈ L₂(N)/L₄(N)` (integrate `1/(t log t L₄(t))`), while the local
relative density at any scale `N^{ε}` with `ε ≥ 1/L₂N` is `δ ≈ 1/L₄(N)`.  The tail forces
`4^{J} ≫ S_P(N)`, i.e. `J ≳ log L₂N`; the fresh-mass term is `≥ √(log(1/ε) · δ · log(1/ε))
≳ log(1/ε) · √δ`, and `log(1/ε) ≥ log 2` is bounded below **even with `C₁ = O(1)`**, while the
sieve term needs `log(1/ε) ≳ J` unless `C₂` is bounded.  With our `C₁ = e^{4k}` the fresh-mass
term is `≳ e^{4J}√δ ≈ (L₂N)^{c}/√(L₄N) → ∞`.  Even with `C₁, C₂ = O(1)` one still needs
`log(1/ε)·√δ → 0` against the tail's `J ≳ log S_P(N)`; the route's requirement is

    log log S_P(N) · √δ(N^{ε_N}) → 0   (at the very least),

which `S_P ≈ L₂/L₄`, `δ ≈ 1/L₄` violates (`L₄ · L₄^{−1/2} → ∞`).  The obstruction is the
coupling of the **L¹ tail criterion** (needs `J` large against the accumulated mass) with the
**correlation majorant** (needs `J` small against the local density); it is not a defect of the
sieve constants.  Precisely: *the current correlation majorant and the current tail criterion
cannot both vanish in this growth regime.*  At the time of writing this was a **conditional growth-regime
obstruction**; Part VI now records Astra's explicit construction of such a set (so the caveat
below is discharged), and also shows that the `L¹`-tail/`√S` analysis here is not the true
bottleneck of the route — the coarse E1 was.  Original text: the lower bound on the fresh mass
(`recipSumIoc P y_N N ≳ log(1/ε)/L₄`, uniformly over the admissible `ε`) is asserted for a
regularly thinned set with a genuine counting law `π_P(x) ~ π(x)/L₄(x)` (Abel summation over
`[N^ε, N]`), and does not follow from an upper density envelope alone.  A sharper head/tail
coupling estimate remains a logical possibility; failure of a sufficient majorant is not a
theorem-level necessity.

**Centered-in-probability consumer (Astra, 2026-09-22 mail).**  A weaker wiring lemma is
immediate: if `R_N = T_N − A_N` (full tail minus truncated head) satisfies, for every `η > 0`,
`(1/N)#{n < N : dist(R_N(n) − c_N, ℤ) > η} → 0` for some deterministic centering `c_N`, and the
head Fourier mean tends to `0` for each fixed `h ≠ 0`, then so does the full Fourier mean, via
`|Mean e(hT_N) − e(hc_N) Mean e(hA_N)| ≤ 2B_N(η) + 2π|h|η`.  But centering at the usual
square-root fluctuation scale only relaxes `4^J ≫ S` to `4^J ≫ √S`; in the regime above either
still forces `J ≳ log L₂N`, and with `ℓ = log(1/ε)`, `v = L₄N`, vanishing sieve error forces
`ℓ − 2 log J → ∞`, so a fresh term `≳ ℓ/√v` still diverges.  A consumer that beats the `√S`
scale, or a head/tail coupling estimate, is what is missing.

## Part III: the frozen shape, not the tail, was the bottleneck (2026-09-22, PROVED)

**Observation.**  `window_bound_regime` (the bound actually proved in `PrimeModelKMT`, valid in
`Regime x k ε`) reads

    ‖windowMeanS S k h x‖ ≤ 24k · √log(1/ε) · √(2 recipSumIoc S y x)
                          + e^{3k} · exp(−recipSumLe S y)
                          + (2k² + 2k e^{20} + 4 + 2·4^k) · exp(−1/(8k²ε)),

with **polynomial** constants; the frozen `KMT_quant₂` shape absorbs `24k` into `C₁ k = e^{4k}`
and `2·4^k + …` into `C₂ k = exp(e^{k+7})`.  It was `C₁ = e^{4k}` that forced `J_N ≤ L₃N/24` in
Part II, and hence forced the tail to be paid for by the *density* input (M2).  Consuming
`window_bound_regime` directly, the schedule can take `J_N ≈ L₃N`, so `4^{J_N} ≈ (L₂N)^{log 4}`
beats the **crude** total mass `S_P(2N) ≤ ∑_{p ≤ 2N} 1/p ≤ 12 L₂N + 21` with no density input,
and the density hypothesis is needed only for the transfer term.

**Hypothesis.**  `SparseIter P := ∀ᶠ x, π_P(x) · (log log log x)^5 ≤ π(x)`.  `Sparse P →
SparseIter P` since `(L₃x)^5 ≤ L₂x` eventually.

**Schedule.**  `ε_N = 2/L₂N`, `y_N = ⌊N^{ε_N}⌋₊` (unchanged), `J_N := min(⌊L₃N⌋₊, ⌊S_P(y_N)/8⌋₊)`.

**Mass bounds.**  (crude) `S_P(N) ≤ 12 L₂N + 21` for `N ≥ 3` (`primeRecipSum_le` at `v = 2`,
prime `2` contributes `≤ 1`, `−log log 2 ≤ 1`).  (fresh) On `(y_N, M+1]`, `L₃t ≥ L₃(y_N) ≥ L₃N −
log 2 ≥ L₃N/2`, so `π_P(t) ≤ 32 π(t)/(L₃N)^5`; (M1') gives `recipSumIoc P y_N N ≤ (32/u^5)(9 +
12u) ≤ 672/u^4` (`u = L₃N`) and `recipSumIoc P y_N (2N) ≤ 1` eventually.

**The four limits** (`t = L₂N`, `u = L₃N = log t`, `J = J_N ≤ u`):
1. Transfer: `24J √log(1/ε) √(2R) ≤ 24u · √u · √(1344/u^4) ≤ 900/√u → 0`.
2. Old mass: `e^{3J} e^{−S} ≤ e^{−5S/8} → 0` (`8J ≤ S`, `S → ∞` by divergence alone).
3. Sieve: coefficient `≤ e^{22} 4^u = e^{22} t^{log 4}`, exponent `−t/(16J²) ≤ −t/(16u²)`;
   product `= exp(22 + u log 4 − t/(16u²)) ≤ exp(−√t) → 0`.
4. Tail: branch `J = ⌊u⌋₊`: `4^J ≥ t^{log 4}/4`, numerator `≤ 12(t+1) + 33 + 5u ≤ 30t`, ratio
   `≤ 120 t^{1 − log 4} → 0` (`log 4 > 1`).  Branch `J = ⌊S/8⌋₊`: `S_P(2N) ≤ S + 1 ≤ 8J + 9`,
   ratio `≤ (13J + 21)/4^J → 0`.

**Regime.**  `Regime N J_N ε_N` eventually: `1/L₂ < 2/L₂`, and `2/L₂ ≤ 1/(7680 J)` iff
`15360 J ≤ L₂`, true since `J ≤ L₃`.

**Theorem (Part III).**  `SparseIter P → DivergentRecip P → IsNormal 4 (subsetLambert P 4)`.
Lean: `PrimeModelFamilySharpMass.lean` (hypothesis, schedule, mass bounds) and
`PrimeModelFamilySharp.lean` (limits, regime, assembly, `isNormal_subsetLambert_of_sparseIter`).
Status: both modules sorry-free; `isNormal_subsetLambert_of_sparseIter` and `sparseIter_of_sparse`
depend only on `[propext, Classical.choice, Quot.sound]` (verified 2026-09-22).

**Where the frontier sits on this schedule family.**  The transfer term needs
`J · log(1/ε) · √δ(N^ε) → 0` with `J ≈ log₄ S_P(N)` forced by the truncation.  With `ε = 2/L₂`
that is `L₃² √δ → 0`: any exponent `> 4` on `L₃` works.  With `ε = J^{−4}` (admissible since
`J^{−4} ≥ L₃^{−4} > 1/L₂`) one gets `log(1/ε) = 4 log J ≈ 4 L₄`, sieve exponent `−J²/8` against
coefficient `e^{22} 4^J`, and the requirement drops to `L₃ · L₄ · √δ → 0`: exponent `2 + η`.
That variant needs the `y_N` lemmas redone with `P`-dependent `ε` (not done).  The `L₄` regime
`δ = 1/L₄` still fails both (`L₃²/√L₄`, `L₃L₄/√L₄` diverge), consistent with the conditional
obstruction above.  The transfer error `E1 = 4k · recipSumIoc S y x` counts the expected number
of unmodelled large-prime hits in the window and is tight in `L¹`; going below it means modelling
the primes in `(y, x]`, which is KMT's own Prop. 4.3 machinery, not a schedule change.

## Part IV: `ε = J₁^{-4}`, exponent 3 (2026-09-22, PROVED)

The Part III transfer term carried `log(1/ε_N) ≈ L₃N` because `ε_N = 2/L₂N`.  The sieve term only
needs `ε ≪ 1/J³` (`exp(−1/(8J²ε))` against the coefficient `e^{22}4^J`), so `ε` can be as large
as `J₁^{-4}` with `J₁ := ⌊L₃N⌋₊` (`P`-independent, which breaks the circularity `ε ↔ J ↔ S_P(y)`).

**Definitions.**  `L₄N = log L₃N`, `J₁N = ⌊L₃N⌋₊`, `ε_N = 1/(J₁N)^4`, `y_N = ⌊N^{ε_N}⌋₊`,
`J_N = min(J₁N, ⌊S_P(y_N)/8⌋₊)`.  Hypothesis `SparseIter3 P := ∀ᶠ x, π_P(x)·(L₃x)^3 ≤ π(x)`
(`SparseIter → SparseIter3` trivially).

**Facts.**  Eventually `2/L₂N ≤ ε_N ≤ 1/(7680 J₁N)` (from `2L₃⁴ ≤ L₂` and `J₁³ ≥ 7680`),
`1/L₂N < ε_N < 1/2`, `log(1/ε_N) = 4 log J₁ ≤ 4L₄N`; `y_N ≥ y_N^{(III)}` so the `yN_core` facts
transfer by monotonicity, and `log N/log y_N ≤ 2J₁⁴` (`⌊x⌋₊ ≥ x/2`, `ε_N log N ≥ 2`).
Fresh mass: density on `(y_N, M+1]` is `≤ 8/(L₃N)^3`; `recipSumIoc P y_N N ≤ (8/u³)(21 + 48v)`
(`u = L₃N`, `v = L₄N`), and `recipSumIoc P y_N (2N) ≤ 1` eventually.

**Limits.**  Transfer `≤ 24u · √(4v) · √(1104v/u³) ≤ 1600 v/√u → 0`.  Old mass as before.
Sieve: exponent `−J₁⁴/(8J²) ≤ −J₁²/8`, coefficient `≤ e^{22}4^{J₁}`, product `≤ e^{−J₁}` once
`J₁ ≥ 40`.  Tail as in Part III.  Regime as before with `ε_N ≤ 1/(7680J₁) ≤ 1/(7680J)`.

**Theorem (Part IV).**  `SparseIter3 P → DivergentRecip P → IsNormal 4 (subsetLambert P 4)`.
Lean: `PrimeModelFamilyIterMass.lean`, `PrimeModelFamilyIter.lean`
(`isNormal_subsetLambert_of_sparseIter3`).  Status: both modules sorry-free; the theorem and
`sparseIter3_of_sparseIter` depend only on `[propext, Classical.choice, Quot.sound]` (verified
2026-09-22).

**Frontier of the route.**  The transfer requirement is now `L₃ · L₄ · √δ → 0`, so any exponent
`> 2` on `L₃` works and `2` itself fails by a `log`.  Below that, the only lever left in this
schedule family is the transfer error `E1 = 4k·recipSumIoc S y x` itself (tight in `L¹`), i.e.
modelling the primes in `(y, x]`.

## Part V: every exponent `β > 2` (2026-09-22, PROVED)

The exponent enters only through the transfer term and the `2N` fresh-mass bound.  With
`SparseIterPow P β := ∀ᶠ x, π_P(x)·(L₃x)^β ≤ π(x)` (real `β`), the Part IV argument gives
`δ = 2^β/(L₃N)^β`, transfer `≤ C_β · L₄N · (L₃N)^{1−β/2} → 0` for `β > 2`, and
`recipSumIoc P y_N (2N) ≤ 81·2^β·(L₃N)^{1−β} ≤ 1` eventually for `β > 1`.  Everything else is
reused verbatim from Part IV.

**Theorem (Part V).**  `2 < β → SparseIterPow P β → DivergentRecip P → IsNormal 4 (subsetLambert P 4)`.
Lean: `PrimeModelFamilyIterPow.lean` (`isNormal_subsetLambert_of_sparseIterPow`).  Status: sorry-free,
axioms `[propext, Classical.choice, Quot.sound]` (verified 2026-09-22).

This is the exact frontier of the schedule family: at `β = 2` the transfer term is `≍ L₄N`, which
does not vanish, and no other parameter of the schedule can absorb a `log`.

## Part VI: phase-weighted transfer, and the little-o `L₄` family theorem (2026-09-22, PROVED)

**Astra's observation (mail 20260922T190221Z).**  E1 (`windowMean_sub_windowMeanLe_le`) bounds each
site by `‖z^{a+c} − z^a‖ ≤ 2c`, discarding the phase.  Keeping it, `‖z_j^{a+c} − z_j^a‖ ≤ c‖z_j − 1‖ ≤
c · 4π|h|/4^{j+1}` and `∑_j 4π|h|/4^{j+1} ≤ 4π|h|/3`, so with the existing per-shift count
`∑_{n<x} ω_{>y}(n+j+1) ≤ 2xR + k`:

    ‖W − W_y‖ ≤ (4π|h|/3) · (2 · recipSumIoc S y x + k/x).

The window length **disappears** from the fresh-mass coefficient, at the price of a factor `|h|`.
Since `KMT_along` is a fixed-`h` statement (`∀ h ≠ 0, Tendsto in N`), this is exactly what the
wiring consumes; the frozen `KMT_quant₂` (uniform in `h`) stays as it is.  Referee check (fable):
E1 enters `window_bound_regime` only through the Cauchy–Schwarz step; the other `k`-dependences
(`e^{2k}` in the model bound → old-mass term, absorbed by `8J ≤ S`; `2k e^{20}`, `4`, `2Q⌊T⌋^k` in
the empirical→model transfer → sieve term; exact phase factorisation and residue factor) never
multiply the fresh mass.  So Parts III–V's "frontier" `β > 2` was an artefact of the coarse E1.

**Fixed-`h` window bound** (`window_bound_regime_h`, same `Regime`):

    ‖W‖ ≤ (4π|h|/3)(2R + k/x) + e^{3k} e^{−S(y)} + (2k² + 2k e^{20} + 4 + 2·4^k) e^{−1/(8k²ε)}.

**Family theorem, little-o form.**  Schedule of Part IV unchanged.  Hypothesis
`SparseL4o P := (π_P(x)/π(x)) · L₄x → 0`.  For `t > y_N`, `L₄t ≥ L₄N/2` (from `L₃t ≥ L₃N − log 2`),
so for every `η > 0` the relative density on `(y_N, 2N+1]` is eventually `≤ 2η/L₄N`, and dominated
Abel with log-ratio `≤ 2 + 4L₄N` gives `recipSumIoc P y_N (2N) ≤ (2η/v)(33 + 48v) ≤ 162η`
eventually; `η` arbitrary gives `recipSumIoc P y_N N → 0` and `≤ 1` to `2N`.  With
`term_two_iter3`, `term_three_iter3`, `regime_iter3` and the Part IV tail argument:

**Theorem (Part VI).**  `SparseL4o P → DivergentRecip P → IsNormal 4 (subsetLambert P 4)`.
Covers every `π_P ≤ π/(L₃)^β` (`β > 0`), every `π_P ≤ π/(L₄)^γ` (`γ > 1`), and `π/(L₄ log L₄)`.
Lean: `PrimeModelKMTFixedH.lean`, `PrimeModelFamilyL4.lean` (`isNormal_subsetLambert_of_sparseL4o`,
`sparseL4o_of_sparseIterPow`).  Status: sorry-free; the theorem, the subsumption lemma and
`window_bound_regime_h` depend only on `[propext, Classical.choice, Quot.sound]` (verified
2026-09-22).

**Reusable consumer (Astra, mail 20260922T190707Z), PROVED** (`PrimeModelFamilyConsumer.lean`,
`isNormal_subsetLambert_of_freshMassZero`, `FreshMassZero P := Tendsto (recipSumIoc P (yI N) (2N))
(𝓝 0)`, with `freshMassZero_of_sparseL4o`; axiom-clean 2026-09-22):
`DivergentRecip P → Tendsto (fun N => recipSumIoc P (yI N) (2N)) atTop (𝓝 0) → IsNormal 4
(subsetLambert P 4)` — no density hypothesis anywhere else; every density class is then a
dominated-Abel corollary.

**The abstract consumer is not a density theorem (Astra, mail 20260922T191228Z; refereed by
fable).**  In `t = L₂x` coordinates put `t_n = exp(n²)`, `a_n = ⌈exp exp t_n⌉`, `b_n = ⌊exp exp(t_n +
1/n)⌋`, and let `P` contain **all** primes in `⋃_n [a_n, b_n]`.  Each block has reciprocal mass
`≍ 1/n` (Chebyshev + Abel: `∫ du/(u log u)` over the block is `1/n + o(1/n)`, boundary terms
`O(1/log a_n)`), so `∑_{p∈P} 1/p = ∞`.  At `x = b_n + 1`, `π_P(x) ≥ π(x) − π(a_n)` and
`π(a_n)/π(b_n) → 0` (since `a_n/b_n ~ exp(−exp(t_n)(e^{1/n} − 1)) → 0`, up to the floor/ceiling), so `limsup π_P/π = 1`:
**no density-zero property at all**.  Yet the fresh window `[y_N, 2N]` has `t`-length
`4 log J₁ + o(1) = O(log log t)`, while consecutive block starts are `exp((n+1)²) − exp(n²)` apart,
so every late fresh window meets at most one block, of index `n → ∞`, and
`recipSumIoc P y_N (2N) ≤ C/n → 0`.  The reusable consumer above therefore gives normality for
this `P`.  The invariant of the route is the **reciprocal mass in the moving cutoff window**, not
pointwise relative density; in particular the conclusion reaches prime sets outside the
density-zero class of KMT's hypothesis.  (The consumer is formalised, `isNormal_subsetLambert_of_freshMassZero`; the example itself is
paper-level and not formalised.)

**Barrier of the route now, with an explicit example (Astra, mail 20260922T190915Z; refereed by
fable).**  Let `w = L₄`, `F(u) = u/w(u)`; for large `u`, `F'(u) = 1/w − 1/(w² log u · L₂u · L₃u) ∈
(0,1)`.  Enumerate the primes `p_n` and put `p_n ∈ P` (for `n > n₀`) iff `⌊F(n)⌋ − ⌊F(n−1)⌋ = 1`
(the difference is `0` or `1` since `0 < F' < 1`).  Then `π_P(x) = ⌊F(π(x))⌋ − ⌊F(n₀)⌋`, and
Chebyshev's `π(x) ≍ x/log x` gives `L₄(π(x))/L₄(x) → 1`, so `π_P(x)/π(x) ~ 1/L₄(x)`: relative
density zero.  Abel summation gives `π_P(u) ≍ u/(log u · L₄u)`, `S_P(x) ≍ L₂x/L₄x → ∞`
(divergent), and, uniformly for `1/L₂N < ε < 1/2` with `y = ⌊N^ε⌋₊`, `ℓ = log(1/ε)`, `v = L₄N`:
`recipSumIoc P y N ≥ c∫_y^N du/(u log u L₄u) − C/(log y · L₄y) ≥ c'ℓ/v − o(1/v) ≍ ℓ/v`
(`L₄u ~ v` on `[y, N]` because `L₂y = L₂N − ℓ + o(1)` and `ℓ ≤ log L₂N`; the boundary term is
`o(1/v)` because `log y ≥ log N/(2L₂N)`).  With `ε = J₁^{-4}`, `ℓ = 4 log J₁ ~ 4v`, so the fresh
mass stays bounded below: the Part VI sufficient criterion **fails** for this explicit
density-zero divergent set.  More generally, for any schedule using the present old/sieve/tail
majorants: the tail forces `4^J ≫ S_P(2N) ≍ L₂N/v`, so `J ≥ c log L₂N`; the sieve forces
`J²ε → 0`, so `ℓ ≥ 2 log J − O(1) ≥ 2v − O(1)`; hence `B_h · R ≍ ℓ/v ≥ 2 − o(1)` cannot vanish for
fixed `h ≠ 0`.  This is a failure of these majorants for this set, not a statement about its
normality.  (Not formalised; a paper construction.)  The model
handles primes `≤ y = N^{ε}` with `ε ≈ L₃^{-4}`; the fresh mass in `(y, N]` is `≍ δ · log(1/ε)
≍ δ · L₄`, and nothing in this schedule family can shrink `log(1/ε)` below `≍ L₄` (the sieve needs
`ε ≪ J^{-3}`, `J ≈ log S_P ≈ L₃`).

## Lean plan (Part II)

| Module | Content |
|---|---|
| `PrimeModelDensityMass` | (M1) dominated Abel summation; (M1'); (M2) via the `a_i` ranges |
| `PrimeModelFamily` | schedule `ε_N`, `y_N`, `J_N`; the four limits; `KMT_along`, `TailOK`; `isNormal_subsetLambert_of_density` |
