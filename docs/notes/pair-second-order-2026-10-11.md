# `PairSecondOrder`: the frozen producer is under-hypothesized; a scheduled variant by sieve

Opus (Ren), 2026-10-11, attended.  Paper draft for Astra's referee, **not refereed, not in Lean**.
Companion to `coefmass-bv-ledger-2026-10-11.md`.  The ET chain needs both `SiteFactorizationScheduled`
and a second-order bound.  This note is about the second.

## Finding 1: `SelbergUpperTwoForms` does not directly supply what `pairSecondOrder_of` needs

`PairSecondOrder` bounds `T2 = W − W_y − T1′` by `C · freshBudget²`, and `freshBudget ∝ δ = 1/φ(q)`.
So the bound must carry **δ²**: both fresh primes lie in the class `a mod q`.

`SelbergUpperTwoForms` counts `#{p ≤ x prime : ap + b prime}` with no progression condition on p or
on `ap + b`.  Two things are missing:
- the δ²;
- the shape.  The pair count needs `(mp + Δ)/m′` prime with p in a class mod `qm′`, which is not
  `ap + b` with p the prime variable.

The Lean docstring's own English says "in progressions mod q₀", but the Prop dropped that.  This is
a missing reduction or input, not a counterexample: it does not show the implication is false
(Astra 170505Z).  Believed ~90% that some progression or linear-form input must be added.

## The pair mean, region by region

**Reduction.**  Write `f_j = z_j^{ω_{>y_j}} − 1`.  Then
`T2 = mean[Φ_y (∏(1+f_j) − 1 − Σ f_j)]`.
- Since `|1 + f_j| = 1`, the identity `∏(1+f) − 1 − Σf = Σ_j f_j(∏_{i<j}(1+f_i) − 1)` gives
  `|·| ≤ Σ_{i<j} |f_i||f_j|`.
- `|f_j| ≤ |w_j| ω_j`.
- So `|T2| ≤ Σ_{i<j} |w_i||w_j| mean[ω_i(n+i+1) ω_j(n+j+1)]`.
- Deep sites `j > J₁` are dropped first (ledger 0a), so every `y_j → ∞`.
- `p = p′` would need `p | Δ = j − i < J < y`, so it is impossible.

Put `A = n+i+1`, `B = A + Δ`, and `Z = N^{1/8}` (above `y_head` once u ≥ 2).  Sum over S-prime
pairs `p | A`, `p′ | B`, `p > y_i`, `p′ > y_j`, in dyadic blocks `p ~ P`, `p′ ~ P′`.  Parameters
`γ, w ∈ (0, 1/8)` may depend on q, since every error below only has to be `o(1)` as `N → ∞` at
fixed q.

| region | tool | contribution to the mean |
|---|---|---|
| (1) `pp′ ≤ N^{1−γ}` | CRT: `#{n} = N/(pp′) + O(1)`, at most `N^{1−γ}` pairs | `(Σ 1/p)(Σ 1/p′) + o(1)` ≤ `δ² log s_i log s_j + o(1)` (`hMer`) |
| (2) `pp′ > N^{1−γ}`, `|log(P/P′)| ≥ w log N` | Brun–Titchmarsh for p mod `qp′` (P > P′; symmetric otherwise), cofactor m fixed | `C δ² log(1/w)` |
| (3) `pp′ ≥ N^{1+γ}`, `|log(P/P′)| < w log N` | two-linear-forms upper sieve in t, `(m, m′)` fixed, length `T ≈ PP′/(qN) ≥ N^{γ}/q` | `C δ² w/γ` |
| (4) `N^{1−γ} < pp′ < N^{1+γ}`, `|log(P/P′)| < w log N` | one variable: A has an S-prime in `N^{1/2 ± (γ+w)}` | `C δ (γ + w)` |
| (5) p ≤ Z, p′ > Z (or symmetric) | inside (1) or (2) | `C δ² log s_i` |

**Choice: `γ = w = δ`.**  The total is `mean[ω_i ω_j] ≤ δ² log s_i log s_j + C δ²(1 + log(1/δ)) + o(1)`.

**Region (2).**  Fix `m = A/p ~ N/P` and `p′ ∤ m`.  Then p runs over primes `≤ N/m` in one class
mod `qp′`.  Brun–Titchmarsh (Montgomery–Vaughan) gives `≤ 2(N/m)/(φ(q)(p′−1) log(P/(qP′)))`.  Here
`log(P/(qP′)) ≥ (w/2) log N` eventually.  Summing `1/m` over the dyadic block gives `log 4`.  So
the block is `≤ C δ (δ log 2/log P′)/log(P/(qP′))`.  Summed over dyadic `P′ ≤ P N^{−w}` this is
`(C/log P) log(1/w)`, and over `P` it is `O(log(1/w))`, since the `1/log P` sum over dyadic
`P ∈ (Z, N]` is `O(1)`.

**Region (3).**  Fix `(m, m′)` with `g = gcd(m, m′) | Δ`.  The conditions
`p ≡ a (q)`, `pm + Δ ≡ 0 (m′)` and `p′ = (pm+Δ)/m′ ≡ a (q)` are a union of classes `r mod qm′`.
For each class, `p = r + qm′t` and `p′ = r′ + qmt`.  These are two linear forms in t with
`E = a₁a₂(a₁b₂ − a₂b₁) = −q³mm′Δ`, so `𝔖 ≤ C (E/φ(E))²`.
- The upper sieve gives `≤ C 𝔖 T/log² T` with `T = N/(qmm′)`.
- Summing over `(m, m′)` in the block with `Σ (m/φ(m))²/m ≪ log` and the class count, the block
  is `≤ C δ² (log 2)²/(log T)²`.  The `(q/φ(q))²` from `p ∤ q` turns `1/q²` into `δ²`.
- With `log T = γ′ log N` (`PP′ = N^{1+γ′}`) summed over the near-diagonal blocks, the region is
  `C δ² w/γ`.
- ⚠️ The class count and the `𝔖`-average are sketched, not written out.  Referee target.

**Region (4)** is the anti-diagonal corner `p ≈ p′ ≈ √N`, where every parametrization has length
O(1) per `(m, m′)`.
- Bound the pair count by the multiplicity `≤ 8` (`ω^{>Z} ≤ 8`) times
  `#{n : A has an S-prime in N^{1/2 ± (γ+w)}}`.
- By `hMer`, that count is `≤ N δ log((1/2+γ+w)/(1/2−γ−w)) + o(N) ≤ C N δ (γ + w)`.
- Only one δ survives here.  This is why γ and w must shrink with δ.

**`Δ/φ(Δ)`.**  `E` contains Δ, and `(Δ/φ(Δ))² ≤ C log²(j+2) ≤ C log s_j`, since
`log s_j ≥ (j+1) log 2`.  It is absorbed.

## Conclusion: a scheduled `PairSecondOrder`, not the frozen one

`|T2| ≤ Σ_{i<j}|w_i||w_j| δ²[log s_i log s_j + C(1 + log(1/δ)) log s_j] + o(1)`.

- **On the ET schedule**, `u = ⌈ρ^{−2}⌉`, so `log s_i ≥ log(2u²) ≥ 4 log(1/ρ) ≥ log(1/δ)`.  The
  loss is absorbed: `|T2| ≤ C freshBudget² + ε`, with C absolute.
- **For the frozen all-`u` Prop**, `log(1/δ)` is not bounded by `log s_i log s_j` at small u, so
  this route does not prove it.  It stays a separate gate (~60%, down from 75%).
- The numerics in the Lean docstring fit a slowly growing q-factor.  At fixed N, `|T2|/Fw²` rises
  from 0.18 at q = 3 to 0.37 at q = 61.  That is not proof that the loss is real.
- **Removing the loss** would take equidistribution of the CRT points `n₀(p, p′)/(pp′)` over S-prime
  pairs with `pp′ ≈ N`.  That is Kloosterman fractions `p̄/p′` over primes (the Fouvry–Shparlinski,
  Bourgain–Garaev line): a literature check, not attempted.

## Statement drafts (NOT planted)

```lean
/-- Brun–Titchmarsh in progressions (Montgomery–Vaughan 1973: constant 2), weakened to an
absolute C.  Checked source: K. Ford, *Sieve Methods* lecture notes (2023), Thm 2.7 (via Thm 2.5
with k = 1). -/
def BrunTitchmarshAP : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ k l : ℕ, 1 ≤ k → Nat.Coprime l k → ∀ x : ℝ, (k : ℝ) < x →
    (((Finset.Iic ⌊x⌋₊).filter (fun p => p.Prime ∧ p % k = l % k)).card : ℝ)
      ≤ C * x / ((Nat.totient k : ℝ) * Real.log (x / k))

/-- Upper-bound sieve for two linear forms, uniform in the coefficients.  Source: K. Ford,
*Sieve Methods* lecture notes (2023), Thm 2.5 with k = 2 (constants depend only on k, for
primitive admissible forms).  The general case reduces to it by elementary case splits (Astra
175014Z): a nonprimitive form has ≤ 2 prime hits; a primitive inadmissible pair is obstructed at 2
(≤ 4 hits); otherwise use four sign choices, which preserve |E| and admissibility.  Singular
series ≤ C (E/φ(E))². -/
def UpperSieveTwoLinearForms : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ a₁ a₂ : ℕ, ∀ b₁ b₂ : ℤ, 0 < a₁ → 0 < a₂ →
    (a₁ : ℤ) * a₂ * (a₁ * b₂ - a₂ * b₁) ≠ 0 → ∀ X : ℕ, 3 ≤ X →
      (((Finset.Icc 1 X).filter (fun t : ℕ =>
          ((a₁ : ℤ) * t + b₁).natAbs.Prime ∧ ((a₂ : ℤ) * t + b₂).natAbs.Prime)).card : ℝ)
        ≤ C * (((a₁ * a₂ * (a₁ * b₂ - a₂ * b₁) : ℤ).natAbs : ℝ)
                / Nat.totient (a₁ * a₂ * (a₁ * b₂ - a₂ * b₁) : ℤ).natAbs) ^ 2
            * X / Real.log X ^ 2

/-- **Second order on the Erdős–Turán schedule.**  A SEPARATE statement: the frozen all-`u`
`PairSecondOrder` is unchanged. -/
def PairSecondOrderScheduled : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∃ q₁ : ℕ, ∀ q a : ℕ, 3 ≤ q → q₁ ≤ q → Nat.Coprime a q →
    ∀ h : ℤ, h ≠ 0 → h.natAbs ≤ schedU q → ∀ ε > 0, ∀ᶠ N : ℕ in atTop,
      ‖fullMean (residueClass q a) (winJ N) h N
        - windowMeanLeG (residueClass q a) (winJ N) (cutU (schedU q) N (winJ N)) h N
        - freshOneSite (residueClass q a) (winJ N) (cutU (schedU q) N (winJ N)) h N‖
        ≤ C * freshBudget (1 / (Nat.totient q : ℝ)) h (winJ N) (schedU q) ^ 2 + ε

theorem pairSecondOrderScheduled_of (hBT : BrunTitchmarshAP) (hUS : UpperSieveTwoLinearForms)
    (hMer : MertensAPAsymptotic) : PairSecondOrderScheduled := sorry

theorem cprimeResidueQuad_of_scheduled' (hSF : SiteFactorizationScheduled)
    (hPair : PairSecondOrderScheduled) : CPrimeResidueQuad := sorry
```

**Referee targets:**
1. Finding 1: is the frozen producer really under-hypothesized, or is there a reduction I am
   missing?
2. The region (3) class count and its `𝔖`-average.
3. ~~Is `PairSecondOrder` consumed only at `u = ⌈ρ^{−2}⌉`, `|h| ≤ u`?~~  Checked:
   `docs/CPRIME-SITE-FACTORIZATION-2026-10-01.md` lines 116–125 evaluate `B_h(u)²` only at
   `u = ⌈ρ⁻²⌉`, `h ≤ H = ⌈ρ⁻²⌉`.  The scheduled variant is exactly what the chain uses.  That
   doc's §PairSecondOrder sketch (line 110: "two linear forms in p, primes restricted to a
   progression, singular series bounded on average") does not treat the anti-diagonal corner (4).
4. Whether the corner (4) admits a δ² bound by an elementary route.

**Elaboration check (Opus):** the four Props and two producers above compile in a scratch file
together with the ledger's drafts, with sorry warnings only.  This is elaboration, not meaning.

## Referee (Astra 170505Z): region (3) is still the gate

- **Exact compatibility.**  Put `g = gcd(m, m′) | Δ`, `M = m/g`, `M′ = m′/g`, `D = Δ/g`.
  - Integer solutions with `p, p′ ≡ a (q)` exist iff `q | a(M′ − M) − D`.
  - The solutions are one class mod `qM′`, with primitive slopes `qM′` and `qM`.
  - The nonprimitive modulus `qm′` splits it into g classes.
  - This needs no `(g, q) = 1`.
- **There is no blanket 1/q saving per cofactor block.**  `(m, m′, a, Δ) = (1, 2, 1, 1)` is
  compatible for every q.  The second δ must come from averaging compatible `(M, M′)`.  Blocks with
  bounded cofactors are `o_N(1)` at fixed q.
- **Owed:** the weighted compatibility sum, with its gcd and class-count factors and the
  `(E/φ(E))²` weight, including primes dividing q and Δ.  The claimed `C δ² w/γ` is not
  established until then.
- Region (1) needs a log factor in the crude pair count, which is still `o(N)`.
- Region (4) is sound, and `γ = w = δ` is enough once q₁ gives δ < 1/8.

## Region (3): the weighted compatibility sum (Opus draft, answering 170505Z)

Fix a near-diagonal block `p ~ P`, `p′ ~ P′` with `PP′ = N^{1+γ′}`, `γ′ ≥ γ`, and `Δ = j − i`.

**Parametrize.**  `m = (n+i)/p`, `m′ = (n+j)/p′`, `g = gcd(m, m′) | Δ`, `M = m/g`, `M′ = m′/g`,
`D = Δ/g`.
- From `p′M′ − pM = D` with `p = a + qr`, `p′ = a + qs`: compatibility is `q | a(M′−M) − D`, i.e.
  `M′ ≡ c_M := M + D ā (mod q)` (Astra's exact form).
- The solutions are `p = b₁ + qM′t`, `p′ = b₂ + qMt`, `t ≤ T := 2P/(qM′)`.
- Then `a₁b₂ − a₂b₁ = q(a(M′−M) + q(s₀M′ − r₀M)) = qD`, so `E = q³ M M′ D`.

**Sieve per (M, M′).**  `≤ C (E/φ(E))² T/log² T`, with
`E/φ(E) ≤ (q/φ(q))(M/φ(M))(M′/φ(M′))(D/φ(D))`.
- The `(q/φ(q))²` is genuine.  Both forms are `≡ a ≢ 0 mod ℓ` for `ℓ | q`, so ρ(ℓ) = 0 and the
  local factor is `(1 − 1/ℓ)^{−2}`.
- `log T ≥ γ′ log N − log q`, as before.

**Sum over M′ in its class.**  Write `(n/φ(n))² = Σ_{e|n} η(e)`, η multiplicative, supported on
squarefree e, `η(ℓ) = (ℓ/(ℓ−1))² − 1`.  For `X′ ≥ q`:

    Σ_{M′~X′, M′≡c (q)} (M′/φ(M′))²/M′ ≤ (C/q) · (gcd(c,q)/φ(gcd(c,q)))² + O((log X′)³/X′).

Primes `ℓ | q` with `ℓ ∤ c` never divide M′, so they contribute nothing.

**Sum over M.**  As M runs over a dyadic block (`≥ q` long), `c_M = M + Dā` is equidistributed mod q.
- The extra weight averages to `(1/q) Σ_{c mod q}(gcd(c,q)/φ(gcd(c,q)))^r = ∏_{ℓ|q}(1 + O(1/ℓ²))`.
  This is bounded, even with the `(M′/φ(M′))²` double count from E (r = 4).
- Correlations between M and `c_M` at primes dividing q come only through `ℓ | D`.  They are folded
  into `C(Δ)`.
- `(M/φ(M))²` has bounded average.

**Block total.**  Count `≤ C (q/φ(q))² · (1/q) · (1/q) · N · C(Δ)/log² T`, with
`C(Δ) = Σ_{g|Δ} g^{−1}(D/φ(D))^{O(1)} ≤ C (log log(Δ+3))^{O(1)}`.
- One 1/q comes from T (p in a class), the other from the M′ class (p′ in a class).
- `(q/φ(q))²/q² = 1/φ(q)² = δ²` exactly.
- So the block is `≤ C δ² C(Δ) (log 2)²/(γ′ log N)²`, and summing near-diagonal blocks gives
  `C δ² C(Δ) w/γ`, as claimed in the table.
- `C(Δ) ≤ C log(j+2) ≤ C log s_j` is absorbed by the site weights.

**Edge blocks** (`X′ = N/(gP′) < q`, i.e. `p′ > N/(qΔ)`): the count is at most
`#{n : n+j has an S-prime > N/(qΔ)} ≤ Nδ log(log 2N/log(N/qΔ)) + π(2N) = o(N)` at fixed q.  The
symmetric blocks are handled the same way.

**Controls (Opus, exact):**
- `max_q (1/q)Σ_c (gcd/φ(gcd))²` over `q < 400` and two primorials is 4.31; for the 4th power it
  is 31.5.  Both are bounded, since the per-prime factors are `1 + O(1/ℓ²)`.
- `(q/φ(q))²·φ(q)²/q² = 1` (q = 7 and q = 510510), confirming the δ² normalization.

**Region (1) correction (Astra):** the crude pair count `≤ N^{1−γ} log N` is still `o(N)`.

**Status:** with this sum, regions (1)–(5) give
`mean[ω_i ω_j] ≤ δ² log s_i log s_j + C δ² C(Δ)(1 + log 1/δ) + o(1)`.
`PairSecondOrderScheduled` is believed ~70%.  The class-count averaging is the step to referee.

## Consolidated pair argument (v2, after Astra 171731Z), for final paper review

**Inputs:** `BrunTitchmarshAP`, `UpperSieveTwoLinearForms`, `MertensAPAsymptotic`.
**Target:** `PairSecondOrderScheduled`.  Fix q ≥ q₁ (δ < 1/8 via eventual growth of φ), a,
`1 ≤ |h| ≤ u = schedU q` and ε > 0.

**Step 0: fixed fresh-site cut, before N → ∞.**
- `T2 = mean[Φ_y R_J]` with `R_K = ∏_{j<K}(1+f_j) − 1 − Σ_{j<K} f_j` and `|1 + f_j| = 1`.
- Subtracting and telescoping gives `|R_J − R_L| ≤ 2 Σ_{L≤j<J} |f_j|`.  Exact control: 0
  violations in 2000 random unimodular trials.
- With `|f_j| ≤ |w_j| ω_j` and Mertens over all primes, the tail mean is
  `≤ C|h| 4^{−L}(log u + L) + (deep sites: C|h|4^{−L} log log N … absorbed as in ledger 0a)`.
- Choose `L = L(h, u, ε)` so this is `≤ ε/2`.  Deep sites lie in the tail.
- All retained shifts `Δ = j − i < L` are now fixed.  No uniform-in-J rate is needed below.

**Step 1: reduction.**  `|R_L| ≤ Σ_{i<j<L} |f_i||f_j|`, so
`|T2| ≤ Σ_{i<j<L} |w_i||w_j| mean[ω_i ω_j] + ε/2`.  It remains to bound
`mean[ω_i(n+i+1) ω_j(n+j+1)]` over S-prime pairs `p | n+i+1`, `p′ | n+j+1`, `p > y_i`,
`p′ > y_j`.  Here `p ≠ p′`, since `p | Δ < L < y`.

**Step 2: regions,** in dyadic blocks `p ~ P`, `p′ ~ P′`, with `γ = w = δ`:
- **(1) `pp′ ≤ N^{1−γ}`.**  CRT gives `N/(pp′) + O(1)` per pair, and the pair count is
  `≤ N^{1−γ} log N = o(N)`.  The main term is `(Σ_{y_i<p} 1/p)(Σ_{y_j<p′} 1/p′)`, which is
  `≤ δ² log s_i log s_j + o(1)` by `hMer`.
- **(2) `pp′ > N^{1−γ}`, `|log(P/P′)| ≥ w log N`.**  Fix the cofactor m and apply
  Brun–Titchmarsh for p mod `qp′`.  Then sum the weighted prime reciprocals by partial summation
  on the exponent scale; this avoids invoking a PNT-AP rate per dyadic block.
  - The cutoff exponents are positive and fixed (Step 0).  So `hMer`'s uniform o(1) remainder
    gives `o(1/log N)` per block and `o(1)` in total.
  - The main integral is `C δ² log(1/w) = C δ² log(1/δ)`.
- **(3) `pp′ ≥ N^{1+γ}`, `|log(P/P′)| < w log N`.**
  - Decompose n into shells `n ~ V` (`V ≫ N^{(1+γ)/2}` is the relevant range).  Within a shell,
    `X ~ V/(gP)`, `Y ~ V/(gP′)` and `T ~ P/(qY)`.
  - *Mixed-weight lemma (Astra).*  For `F(n) = (n/φ(n))²`, `H_q(c) = (gcd(c,q)/φ(gcd(c,q)))²`
    and `X ≥ q`: `Σ_{m~X} F(m) H_q(m+c) ≤ C X`, absolute, uniform in c.
    - Proof: Cauchy–Schwarz.  `Σ F² ≤ CX` via the divisor expansion of `(n/φ(n))⁴`, with
      `((p/(p−1))⁴ − 1)/p ≤ 30/p²`.
    - `Σ H_q² ≤ CX` by periods, since `q^{−1} Σ_r H_q(r)² = ∏_{ℓ|q}[1 + ((ℓ/(ℓ−1))⁴ − 1)/ℓ] ≤ C`.
    - No independence between the two weights is assumed.
  - *Inner class.*  `Σ_{n~Y, n≡c (q)} F(n)/n ≤ C H_q(c)/q + C (log 2Y)³/Y`, via `F = Σ_{e|n} η(e)`
    and `η(e) ≤ C 3^{ω(e)}/e`.
  - *Two-variable estimate.*  `Σ_{m~X} Σ_{n~Y, n≡m+c (q)} F(m)F(n)/n ≤ C X/q + C X (log 2Y)³/Y`.
  - *Block.*  Multiply by the sieve prefactor `C (q/φ(q))² (D/φ(D))² P/(q log² T)`, with
    `E = q³MM′D` and ρ(ℓ) = 0 for `ℓ | q`.
    - The main term is `C δ² (V/g) F(D)/log² T`, where `(q/φ(q))²/q² = δ²` exactly.
    - The error is `C (q/φ(q))² (V/(gq)) F(D) (log 2Y)³/(Y log² T)`.  Summed over dyadic Y, the
      `O(log N)` P-blocks and geometric shells, it is `O_{q,Δ,γ}(N/log N)`.
  - *Edges* (`X < q` or `Y < q`, in each shell): one prime exceeds `cV/(qΔ)`, and the other has
    multiplicity ≤ 8 (both exceed `N^{1/8}`).  Mertens plus `π(2V) = o(V)` gives `o(V)`, which sums
    to `o(N)`.
  - *Over blocks:* the strip width is `O(w)` and `∫_γ γ′^{−2} dγ′` gives `C δ² C_Δ w/γ = C δ² C_Δ`,
    with no q-dependence in C.
- **(4) corner `N^{1−γ} < pp′ < N^{1+γ}`, near the diagonal.**  The one-variable bound gives
  `C δ (γ + w) = 2C δ²`.
- **Shift cost.**  `C_Δ = Σ_{g|Δ} g^{−1}((Δ/g)/φ(Δ/g))² ≤ (Δ/φ(Δ))³ ≤ (9/2)Δ`, using
  `Σ_{g|Δ} 1/g ≤ Δ/φ(Δ)` and `(p/(p−1))³ ≤ p` for p ≥ 5.  Exact control over Δ ≤ 5000:
  `max C_Δ/Δ = 2.25` and `max (Δ/φ(Δ))³/Δ = 4.5`.

**Step 3: assembly.**
`mean[ω_i ω_j] ≤ δ² log s_i log s_j + C δ² (1 + C_Δ)(1 + log 1/δ) + o(1)`.
- On the schedule, `log s_i ≥ log(2u²) ≥ 4 log(1/ρ) ≥ c(1 + log 1/δ)`.
- Also `(9/2)Δ ≤ (9/2) j ≤ C log s_j`, since `log s_j ≥ (j+1) log 2`.
- So each retained pair is `≤ C δ² log s_i log s_j + o(1)`, and
  `|T2| ≤ C (Σ_k |w_k| δ log s_k)² + ε = C freshBudget² + ε`, with C absolute.

**Status:**
- Regions (1)–(4) and steps 0–3 are on paper.  Region (3) is accepted by Astra (171731Z),
  conditional on `UpperSieveTwoLinearForms`, whose source theorem is not yet checked.
- Believed ~75%, conditional on that input.
- The frozen all-u `PairSecondOrder` stays separate (~60%).

**Sieve input source (Opus, after 172250Z).**
- `UpperSieveTwoLinearForms` is restated in the Halberstam–Richert Thm 5.7 shape: the extra factor
  is `1 + log log(3|E|)/log X`.  Its `log log 3x` term is absorbed in C.
- Source: HR74 Thm 5.7 as quoted (open access) in arXiv:2308.01152, p. 8, eq. (6) and following.
  That paper also notes the `E/φ(E)` weakening of the singular series.
- **In our use** `E = q³MM′D` with `M, M′ ≤ N`, so `log log 3|E| ≤ log log N + O(1)`.  Also
  `X = T ≥ N^{γ}/q`, so the factor is `1 + o(1)`.
- The book itself is unchecked.  Bordignon–Lee (arXiv:2211.11012) make HR Thm 5.3 explicit, but
  with an F-dependent constant, which is not the coefficient-uniform form needed here.

## Final conditional review (Astra 175014Z): sign-off on paper, with three edits applied

1. **Sieve source checked: Ford, *Sieve Methods* lecture notes (2023), Thm 2.5, p. 19.**
   - Astra checked the page image and proof; Opus re-read the statement from the PDF.  The bound is
     `≪_k S x/log^k x` for distinct admissible primitive forms, with the singular series S over
     `∏ a_i ∏_{i<j}(a_i b_j − a_j b_i)`, uniform in the coefficients.
   - With Astra's case split (above), the original height-free `UpperSieveTwoLinearForms` holds.
     So the HR-5.7-shaped restatement with the `log log 3|E|` factor (5f892eb7) is REVERTED to the
     height-free form, now citing Ford, not unchecked HR theorem numbers.
   - `BrunTitchmarshAP` is Ford Thm 2.7.
2. **Step 0, deep tail written explicitly.**  The tail is
   `≤ C|h|4^{−L}(log u + L) + C|h|4^{−J₁(N)} log log N + o_N(1)`, with
   `J₁(N) = ⌈log₂ log log N⌉`, which eventually lies between L and J.
   - `4^{−J₁} log log N → 0`.
   - The smallest retained frozen cutoff `y_{J₁} = exp(c log N/(u² log log N)) → ∞`, so the
     all-prime Mertens remainder is uniform on the shallow part.
   - Choose L first, then N.
3. **Region (2) keeps the mixed-small-prime term, and uses V-shells.**
   - `C δ² log(1/w)` covers pairs with both primes above `Z = N^{1/8}`.  Pairs with one prime
     below Z add `C δ²(log s_i + log s_j)` (old region (5)).
   - The cofactor sum runs over V-shells, with the same geometric `V/N` summation as region (3).
   - Corrected pre-absorption bound, with an absolute C on the WHOLE expression:

         mean[ω_i ω_j] ≤ C δ² [log s_i log s_j + (1 + C_Δ)(1 + log(1/δ))] + o(1).

   - On the schedule, `log s_i, log s_j ≥ 1` and the absorption in Step 3 is unchanged:
     `|T2| ≤ C freshBudget² + ε`.

**Status:** `pairSecondOrderScheduled_of (hBT) (hUS) (hMer)` has paper-level CONDITIONAL sign-off
from Astra (175014Z), with the displayed quantifiers and an absolute constant.  This does not
cover the Lean implementation, the build, or trunk.  The separate site producer still carries its
BV/TSW dependency.
