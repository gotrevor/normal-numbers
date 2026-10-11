# Coefmass route to `SiteFactorization`: the BV / main-term / character ledger

Opus (Ren), 2026-10-11, attended.  Paper draft for Astra's referee, **not refereed, not in Lean**.
It replaces Mechanism step 1 of `docs/CPRIME-SITE-FACTORIZATION-2026-10-01.md`: the
fundamental-lemma sieve, whose `(2J)^{ω(e)}` multiplicity was the wall.  The replacement is the
Riesz-truncated centered expansion of `coefmass-2026-10-10.md`.  Its model M4 gate is closed on
paper; see that note, "Finite-y proof of uniform M4 for the Riesz cutoff".

## Setup

- Fix a site k.  `T1'_k = mean_{n≤N}[Φ^{≠k}(n)·f(n+k)]`, with `f = F_k − F_{k,y}`, `F = z_k^{Ω_P}`
  and `F_y = z_k^{Ω_{P,≤y_k}}`.
  - The `Ω` forms are completely multiplicative.
  - `ω` ↔ `Ω` goes through the squarefull convolution, as in the 10-01 doc.
- Split `Φ^{≠k} = g₀(n mod Q)·Φ_core(n)`, with `Q = ∏_{p≤2J, p∈P} p`.
  - Q is polylog: `log Q ≤ (1+o(1))·2δJ`, and J ≈ log₂log₂N.
  - Every prime of Q lies in P, so `(Q, q₀) = 1`.
- `P := g₀·Σ_S c_S χ(d_S)`, with `χ(d) = (1 − log d/log D)_+^{k_R}` and `D = N^θ`.
  - θ < 1/4, so that `(QD)⁴ < N^{1−ε}`.
  - S ranges over sets of P-primes in `(2J, D]`.
  - The phases are the sites `j ≠ k` that are active at p (`p ≤ y_j`).
  - `k_R > 9A/2`, with `A = Σ_{j≠k}|w_j|²`.
- Decompose `T1'_k = mean[P(n) f(n+k)] + mean[(Φ^{≠k} − P)(n) f(n+k)]`.  Call the second term **E1**
  and the first the **type-I sum**.

## E1: the residual (TV + M4)

`|E1| ≤ ‖f_k‖_{2,int} · ‖Φ^{≠k} − P‖_{2,int}`.

- `‖f_k‖₂ ≤ C|w_k|·(δ log s_k)^{1/2}`, from `|f| ≤ min(2, |w_k| Ω_{P,(y_k,N]})`.
- The second factor squared is at most:
  - the model energy above the Riesz cutoff, `≤ k_R·C δ/(u²θ)`;
  - plus `O(1/M + M ε)` from the clipped TV test, with `ε ≍ e^{−u}` (Astra's §8 schedule,
    J-free);
  - plus the tails `≤ 8(2 + M4_int + M4_mod)/M`;
  - plus the CRT remainder of `M4_int − M4_mod`, which is `o(1)` for θ < 1/4.
- With `M4 ≤ C(h)` (Riesz bound (R)) and M optimized:
  `‖Φ^{≠k} − P‖₂ ≤ C(h)[(k_R δ)^{1/2}/(u θ^{1/2}) + e^{−u/4}]`.
- Summed over k with `Σ_k |w_k| (log s_k)^{1/2} ≤ C_h (log u)^{1/2}`:

      Σ_k |E1_k| ≤ C_h [ δ (log u)^{1/2}/u + δ^{1/2} (log u)^{1/2} e^{−u/4} ].

- ⚠️ **This is weaker than the frozen statement's `C_h(e^{−u/2} + δ/√u)`.**  The `e^{−u/4}`
  comes from the square root in the clipped-TV transfer.  Proposed fix: restate
  `SiteFactorization` with `C_h(e^{−u/8} + δ/√u)`.
  - The ET chain only needs some `e^{−cu} ≤ Cρ²` at `u = ρ^{−2}`, so it is unaffected.
  - The first term is ≤ δ/√u for large u.
  - Uniformity in q holds, because the `e^{−u/4}` term carries `δ^{1/2} ≤ 1` and needs no δ.

## Type-I sum: an exact progression decomposition

Expanding `φ_p = Σ_{j active} w_j 1[n ≡ −j (p)] − a_p/p` writes P exactly as a sum over
moduli `e = Q·d_T` and residues c:

    P(n) = Σ_{e,c} κ(e,c) 1[n ≡ c (e)],
    κ = g₀(c mod Q) · ∏_{p∈T} w_{j_p} · Σ_{U ∩ T = ∅} χ(d_T d_U) ∏_{p∈U}(−a_p/p) ∏_{p∉T∪U} μ_p.

No CRT remainder enters, because this is an identity in n.

**Coefficient majorant (E2a).**  `Σ_c |κ(e,c)| ≤ Q · W^{ω(d_T)} · ∏_p (|μ_p| + |a_p|/p)`, which is
`≤ Q W^{ω(d_T)} (log y_head)^W` with `W = Σ_{j≠k}|w_j|`.

- The bound holds because `0 ≤ χ ≤ 1`, so the Riesz weight does not change Astra's majorant.
- W is J-free, because the `|w_j|` decay geometrically.  This is where centering beats the old
  sieve: the multiplicity is `W^{ω}`, not `(2J)^{ω}`, and level control comes from the conductor
  cutoff.

**Residues (E2b).**

- Expanded primes: `n ≡ −j (p)` gives `n + k ≡ k − j ≢ 0 (p)`, since `j ≠ k` and `p > 2J`.  So the
  shifted residue is a unit mod `d_T`.
- Q-block: `n + k ≡ 0 (p)` is possible for `p | Q`.  Let `g = gcd(c+k, e)`, which divides Q.
  - e is squarefree and complete multiplicativity gives `f(g m″) = z_k^{Ω(g)} f(m″)`.
  - This holds because `p ≤ 2J ≤ y_k`, so F and F_y agree at p.
  - The residue `(c+k)/g` is coprime to `e/g`.
  - So each such class is a coprime progression mod `e/g` of length `N/g`.  There are at most
    `τ(Q)` values of g.

**BV (E2c, E2d).**  Moduli satisfy `e ≤ Q N^θ ≤ √N/(log N)^B`, and `(e, q₀) = 1`.

- Apply `MultBVResidue` at the lengths `N/g`.  It is uniform in x, and the shift by k is O(1).
- Weighted sum, by Cauchy–Schwarz against the trivial `|Δ_e| ≤ 3N/φ(e)`:

      Σ_e A_e max_c |Δ_e| ≤ (3N Σ_e A_e²/φ(e))^{1/2} (Σ_e max|Δ_e|)^{1/2}
                          ≪ N (log N)^{(W² + 2W + 2·log Q/log log N − A)/2},

  with `A_e = Q W^{ω} (log y)^W`.  Choose A larger; this is o(N).

## E3: character exceptions

- These are handled inside `MultBVResidue` (plain Δ) via `multBVResidue_of`: GS Cor 7.1 gives
  `Δ_A`, and `TwistedSiegelWalfisz` bounds the subtracted small-conductor characters.
- The precondition is that every modulus is coprime to q₀.  It holds because the expanded primes
  and Q's primes all lie in P, and P-primes do not divide q₀.
- The extra character count per e is at most `τ(e)(log N)^B`, and its cost
  `Σ_e A_e τ(e)/φ(e) ≪ (log N)^{O(W)}` is absorbed by choosing A larger.
- Inherited and still owed: TSW's uniformity in y (two-regime argument), believed about 85%.
  The coefmass route does not change this node.

## E4: the main term, as one tilted mean (replaces SD uniformity over e)

The principal parts recombine exactly:

    Σ_{e,c} κ(e,c) · [main of Σ_{n≡c (e)} f(n+k)] = Σ_{m≤N} f(m) Λ(m),
    Λ(m) = E_model[ P | gcd(m, e) for every modulus e ].

This needs **no** Selberg–Delange uniformity over e ≤ N^{3/8}.  The 10-01 open check (d) was
SD at modulus e with many prime factors summed against a polylog ℓ¹ mass.  It would have needed
relative precision `(log N)^{−A}`, which SD does not give.  This rearrangement avoids that.

- **(E4i) Truncation.**  `Λ − Λ_full = E[P − Φ^{≠k} | pattern]`.
  - Conditional expectation contracts L², and `E|Λ|⁴ ≤ M4` by conditional Jensen.
  - So the same E1 argument applies.  It is a TV-legal function of the site-k part of the
    joint state, with a CRT fourth moment.
  - Error ≤ the E1 bound.
- **(E4ii) Full conditional.**  `Λ_full(m) = E[Φ^{≠k}] · τ(m)`, with
  `τ(m) = ∏_{p|m, p∈P, p≤y_head} τ_p`.
  - For `2J < p ≤ y_head`: `τ_p = (1 + a_p^{≠k}/(p−1))^{−1} = 1 + O(W/p)`.
  - For `p ≤ 2J`: τ_p is the bounded small-prime correlation, read off g₀.
- **(E4iii) Assembly.**  `E[Φ^{≠k}]·mean[F_y τ] = W_y` (model) exactly, since τ is the
  site-k/other-site correlation.  So

      mean[f τ] · E[Φ^{≠k}] = W_y · ( M[Fτ]/M[F_y τ] − 1 ).

  - At frozen primes `p ≤ y_k`, F and F_y share the local factor, so τ cancels in the ratio.
  - At fresh primes `p ∈ (y_k, y_head]`, `τ_p = 1 + O(W/p)` changes the ratio by
    `∏(1 + O(W/p²)) = 1 + O(W/y_k)`.  This is the 10-01 doc's `O(1/y_k)`.
  - So the ratio is `s_k^{κ_k} e^{−γκ_k}/Γ(1+κ_k) (1 + o(1))`, i.e. `1 + g(κ_k, s_k)`.
- **Owed:** Selberg–Delange for the tilted F·τ.
  - τ is an N-dependent multiplicative perturbation, with `Σ_p |τ_p − 1|/p ≤ C(h)` uniformly.
    Its small-prime part is bounded.
  - It should sit in Tenenbaum's class `P(z; c₀, δ, M)` with uniform parameters.  Needs a new
    Literature-instantiation Prop, `SelbergDelangeTilted`, about 85%.

## E5: uniformity ledger

| quantity | depends on | J-uniform? |
|---|---|---|
| coefficient mass | `W = Σ|w_j|`, `(log y)^W`, Q | yes (Q polylog) |
| M4 bound (R) | A, k_R | yes |
| TV ε | §8 schedule | yes (Astra) |
| CRT remainders | `(QD)⁴ < N^{1−ε}` | yes |
| BV saving A | free | yes |
| deep sites | J₁ ≈ L3 N if C′'s `y_J ≥ 2J` is needed elsewhere | unchanged |

## What this does and does not claim

- **Claims (draft, about 55%):** `SiteFactorization` with a **two-constant error**,

      limsup_N |T1' − W_y G_h(u)| ≤ C₁(h)·δ/√u + C₂(h)·e^{−u/8},
      C₁(h) ≤ C(1 + log|h|)^m,   C₂(h) ≤ exp(C log²(2 + |h|)),

  follows from `MultBVResidue` (hence GS Cor 7.1 + BV + TSW), `SelbergDelangeTilted`, C′ (5.3)
  on the §8 schedule, and the Riesz M4 bound.  It is uniform in q, u and J.
  - The M4 constant (`e^{O(A)}` with `A ≍ log|h|`, times the `k_R!` factor of (R)) only multiplies
    `e^{−u/4}`, so it lives in C₂.
  - Only `k_R^{1/2} ≍ (log|h|)^{1/2}` reaches C₁, through the energy term, and that is polylog.
  - **ET check:** Erdős–Turán uses `h ≤ H = ρ^{−2} ≍ u`.  So
    `Σ_{h≤H} C₂(h) e^{−u/8}/h ≤ exp(C log² u − u/8) log u → 0`, and the C₁ part is the existing
    `Cρ² log⁵(1/ρ)` computation.
  - The frozen Lean form `C(1 + log|h|)^m (e^{−u/2} + δ/√u)` must be restated in this two-constant
    form.
- **Does not claim:** `PairSecondOrder` (separate, about 75%); anything about G₄; or a Lean
  proof.
- **Owed before trunk:** Astra's referee of E1–E5; the `C_h` growth check above; Lean
  statements for the loosened `SiteFactorization` and `SelbergDelangeTilted`; and a green build.
