# Coefmass route to `SiteFactorization`: the BV / main-term / character ledger

Opus (Ren), 2026-10-11, attended.  Paper draft for Astra's referee, **not refereed, not in Lean**.
Amended after Astra `20261011T130704Z-astra-…`: separate Prop, fresh L² norm, J₁, schedule constants.

> **Referee verdict (Astra `20261011T131444Z`, on 4ea0de39): E4 FAILS as written; repair first.**
> E2's algebra is sound under complete multiplicativity, and E3 is accepted as a consumer of
> `MultBVResidue`.  M4 is untouched.  Repair list, owned by Opus:
> 1. **Normalization.**  The conditional local value is `b_p = 1 + a/(p−1)` on nonhits and `1` on
>    hits; `E[Φ]·τ` is wrong.  Control: p=5, one parity site, target −1 gives 6/25 against the
>    true 1/5.  Use the product of RAW conditional values, never a division by `E Φ` or by a
>    possibly-zero small-prime nonhit value.  Small primes `p ≤ 2J` get a finite decomposition.
> 2. **TV state.**  Λ reads `p | n+k` for `p ∈ (y_k, y_head]`, which the 5.3 state does not record.
>    Augment the state with the target-site label up to `y_head`: one extra coordinate, threshold
>    `N^{1/16}`, `Σ log T/log N ≤ (√2+2)/16 < 1/4`, box tail `≤ e^{20} e^{−u²/16}`.  Prove this
>    augmented version explicitly.
> 3. **Kernel.**  State it term by term: `κ(e,c)·1[gcd(m,e)=g]/φ(e/g)`, with `g = gcd(c+k, e)`.
>    The arithmetic fourth moment comes from expanding the divisibility indicators (conductor
>    `≤ QD`, an extra `2^ω`).  Conditional Jensen alone gives only a model bound.
> 4. **ω vs Ω.**  The gcd split and the tilt use the Ω form.  The frozen problem is ω, so the
>    squarefull-convolution ledger, and its effect on the small-prime model, must be explicit.
> 5. **z-uniformity.**  `MultBVResidue`'s constants depend on z, and `z_k` varies with k.  Either
>    get uniformity on the circle, or cut the fresh-site sum at a fixed `L(h,u,ε)` via its
>    geometric tail before `N → ∞`.  Shifts are then `O(L)`.
> 6. Only after 1–5: a division-free tilted-mean statement with the actual ω and small-prime
>    factors.  That is the faithful SD target.  The `/√p` `SelbergDelangeTilted` draft was not
>    planted.
> The E1 norm comment refers to 4ea0de39 and is already fixed in 8c23db66.
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

- `‖f_k‖₂ ≤ C(|w_k| δ log s_k)^{1/2}`, from `|z^ω − 1|² ≤ 2|w_k| ω_fresh` (Astra).  It is NOT
  `|w_k|(δ log s_k)^{1/2}`, which holds only when `|w_k| ω` is small.  Keep this second `√δ`:
  do not pay the residual with `|f| ≤ 2`.
- The second factor squared is at most:
  - the model energy above the Riesz cutoff, `≤ k_R·C δ/(u²θ)`;
  - plus `O(1/M + M ε)` from the clipped TV test, with `ε ≍ e^{−u}` (Astra's §8 schedule,
    J-free);
  - plus the tails `≤ 8(2 + M4_int + M4_mod)/M`;
  - plus the CRT remainder of `M4_int − M4_mod`, which is `o(1)` for θ < 1/4.
- With `M4 ≤ C(h)` (Riesz bound (R)) and M optimized:
  `‖Φ^{≠k} − P‖₂ ≤ C(h)[(k_R δ)^{1/2}/(u θ^{1/2}) + e^{−u/4}]`.
- Summed over k with `Σ_k |w_k|^{1/2}(2 log u + k log 2)^{1/2} ≤ C L_h (log u + L_h)^{1/2}`,
  where `L_h = 1 + log(1+|h|)`:

      Σ_k |E1_k| ≤ C δ k_R^{1/2} L_h (log u + L_h)^{1/2}/u  +  C δ^{1/2} L_h (log u + L_h)^{1/2} B_h^{1/4} e^{−u/4}.

  On the ET schedule (`u = ⌈ρ^{−2}⌉`, h ≤ H) the first term is `O(ρ³ log²(1/ρ))`, which is below ρ².

- ⚠️ **This does not prove the frozen `SiteFactorization` Prop.**  `e^{−u/4}` comes from the square
  root in the clipped-TV transfer: the squared residual is `Ckδ/u² + C B_h^{1/2} e^{−u/2}`.
  - **Do not weaken the frozen Prop under its old name (Astra).**  State a separate scheduled
    consumer with its real quantifiers, `SiteFactorizationScheduled`.  Alternatively, finish the
    all-(h,u) bookkeeping by splitting `u ≫ L_h log(2+L_h)` (factorial absorbed) from its
    complement (fresh-mass triangle bound at a larger polylog power).  That split needs a
    larger sieve-accuracy parameter; check its product-support budget.
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
- **(E4ii) Full conditional.**  ❌ **Wrong normalization; see the referee box.**  `Λ_full(m) = E[Φ^{≠k}] · τ(m)`, with
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
| deep sites | **J₁ ≈ L3 N required**: at J ≈ log₂log₂N, `y_J < 2J` violates the full-state TV hypotheses.  The truncated phase tail costs `4^{−J₁} δ log log N → 0` | yes, after truncation |
| exceptional characters | inside `MultBVResidue` (E3).  `(e,q₀) = 1` only rules out characters induced from q₀ as the correlation-pole family.  Other small-conductor real characters with conductor dividing e (coprime to q₀) remain, and `TwistedSiegelWalfisz` is the *assumed* bound on their twisted sums, with ineffective constants.  This makes no claim about where exceptional zeros sit (Astra 132048Z) | yes, given TSW |

## What this does and does not claim

- **Claims (draft, about 55%):** `SiteFactorizationScheduled`, a NEW Prop; the frozen
  `SiteFactorization` stays unchanged.  For `u = ⌈ρ^{−2}⌉` and all h ≤ H = ⌈ρ^{−2}⌉,

      limsup_N |T1' − W_y G_h(u)| ≤ C (ρ² + e^{−u/8}),   with C absolute (independent of q, h).

  It follows from `MultBVResidue` (GS Cor 7.1 + BV + TSW), `SelbergDelangeTilted`, C′ (5.3) on
  the §8 schedule with deep-site truncation J₁, and the Riesz M4 bound.
  - **Constants (Astra's check).**  On the schedule, `A, W = O(log u)` and
    `k_R = ⌈9A/2⌉ + 1 = O(log u)`.  So `log B_h ≤ C(1 + log u) log(2 + log u) = o(u)`, uniformly
    over the whole ET sum, and `B_h^{1/4} e^{−u/4} ≤ e^{−u/8}` eventually.
  - The q-dependent N threshold is maximized over the finitely many h ≤ H.
  - This is exactly what `CPrimeResidueQuad`'s chain consumes.  The all-(h,u) frozen Prop remains
    a separate gate (split above).
- **Does not claim:** `PairSecondOrder` (separate, about 75%); anything about G₄; or a Lean
  proof.
- **Owed before trunk:** Astra's referee of E1–E5; the `C_h` growth check above; Lean
  statements for the loosened `SiteFactorization` and `SelbergDelangeTilted`; and a green build.

## Repair 1 (draft, revised after Astra 160352Z): the raw-conditional main term

This replaces E4ii and E4iii.  The notation is that of the referee box.

**Kernel.**  `Λ(m) = Σ_{e,c} κ(e,c) 1[gcd(m,e) = g_{c,e}]/φ(e/g_{c,e})` term by term (item 3).
Split `Λ = C + (Λ − C)`, where C is the same kernel for the UNtruncated `Φ^{≠k}`:

    C(m) = C_small(m mod Q) · ∏_{2J < p ≤ y_head} C_p(m),
    C_p(m) = b_p if p ∤ m,  1 if p | m,   b_p = 1 + a_p/(p−1),   a_p = Σ_{j≠k, p≤y_j} w_j.

The difference `Λ − C` is the truncation residual.  It is handled like E1, on the augmented state
(item 2) and with the indicator-expanded arithmetic fourth moment (item 3).

**Large primes: a division only where it is safe.**  Impose `2J ≥ 2W + 2`, which holds
eventually for fixed h.  Then for `p > 2J`, `b_p ≠ 0`, `|b_p − 1| ≤ W/(p−1)`, and
`|b_p^{−1} − 1| ≤ 2W/p`.  (`2J ≥ W + 2` is NOT enough: W=4, J=3, p=7, a=−4 gives
`|b^{−1} − 1| = 2 > 8/7`; Astra.)  Also `|b_p| ≤ 1`, as a conditional average of unit phases,
so `|B_large| ≤ 1`.  Then

    ∏_{2J<p≤y_head} C_p(m) = B_large · τ(m),   B_large = ∏ b_p,   τ(m) = ∏_{p|m, 2J<p≤y_head} b_p^{−1},

with `|τ_p − 1| ≤ 2W/p`.

**Small primes: a finite decomposition, no division.**  Q is squarefree.  For `g | Q`, put
`C_small(g) = ∏_{p|g} C_p(hit) ∏_{p|Q/g} C_p(nonhit)`.  Here `C_p(hit) = g_p(−k)` is unimodular,
and `C_p(nonhit) = (p−1)^{−1} Σ_{r ≢ −k} g_p(r)` has modulus `≤ 1` and may vanish.  It is never
inverted.  Then

    Σ_{m ∈ (k, N+k]} f(m) C(m) = B_large Σ_{g|Q} C_small(g) Σ_{m ∈ (k, N+k], gcd(m,Q)=g} f(m) τ(m).

Keep the shifted interval `(k, N+k]`.  Replacing it by a prefix is an endpoint error, not an
identity.

**Inner sums (Ω form; the ω translation is item 4).**  `gcd(m,Q) = g` ⟺ `m = g m′` with
`gcd(m′, Q/g) = 1`.  This holds because Q is squarefree and m′ may still carry primes of g.  By
complete multiplicativity of F and F_y, and since they agree at the primes of g ≤ 2J ≤ y_k,
`f(g m′) = F(g) f(m′)` with `F(g) = z_k^{Ω(g)}` unimodular.  ⚠️ It is NOT `f(g) f(m′)`: f is not
multiplicative and `f(g) = 0` for every `g | Q` (Astra's control: frozen g, fresh r, phases −1,
`f(gr) = 2`, `f(g) f(r) = 0`).  τ is supported above 2J, so `τ(g m′) = τ(m′)`.  So each inner sum is
`F(g) Σ_{m′ ∈ (k/g, (N+k)/g], (m′,Q/g)=1} f(m′) τ(m′)`.  That is one tilted mean of f,
with tilt `τ_p` above 2J and `0` at the primes of `Q/g`.

- **The faithful SD target (to state after items 2–5):** a Selberg–Delange asymptotic for
  `z^{Ω_P}·τ·1[(·, Q′) = 1]`, uniform over squarefree `Q′ | Q` and tilts with `|τ_p − 1| ≤ 2W/p`,
  `p > 2J`.  The coprimality costs `Σ_{p|Q′} p^{−1/2} ≤ C√J/log J`.  An error factor
  `exp(C√J)/log N → 0` suffices.
- `F_y` is NOT a κ = 0 SD case: it depends on N through the fixed-power cutoff.  Its mean comes
  from the accepted augmented TV (5.3′): `|F_y C| ≤ 1` is a state function, so
  `mean_arith[F_y C] = E_μ′[F_y C] + O(e^{−u}) + o_N(1)`.  Arithmetic and model means are not
  equal; the tower identity is exact inside the model only.  For the Ω form this waits on item 4's
  valuation ledger, since Ω-valuations are not radical-state measurable.

**Assembly.**

- The g-sum has `2^{ω(Q)}` terms, with `ω(Q) ≤ π(2J)`, weighted by `|C_small(g) F(g)|/g ≤ 1/g`.
  So `Σ_g 1/g ≤ ∏_{p|Q}(1 + 1/p) ≤ C log J`, and the summed SD errors are
  `N (log J) exp(C√J)/log N = o(N)`.
- **Division-free assembly (Astra 160352Z).**  No lower bound on the small-prime frozen mean
  is known; it may vanish.  So never form `M[FC]/M[F_y C]`.  Match Euler factors algebraically
  and state the additive pair (after item 4):

      mean_arith[F C]   = G(κ_k, s_k) · E_μ′[F_y C] + err₁,     G = 1 + g,
      mean_arith[F_y C] = E_μ′[F_y C] + err₂,                   err₂ = O(e^{−u}) + o_N(1),

  - `err₁` collects the SD error over the g-decomposition and the fresh-prime tilt
    `∏_{y_k<p≤y_head}(1 + O(W/p²)) − 1 = O(W/y_k)`.
  - The g-decomposition SD error is `N (log J) e^{C√J}/log N`, which is `o(N)`.
  - Then `E_μ′[F_y C] = E_μ′[F_y Φ^{≠k}]` (tower, in the model) `≈ W_y` up to the C′ TV error.
  - This stays meaningful when a small-prime factor vanishes.
- **Arithmetic M4 mass (Astra's bookkeeping).**  For expanded d, g is confined to Q, so
  `φ(e/g) = φ(Q/g) φ(d)`.  After the gcd-indicator expansion the ℓ¹ mass is at most a Q-factor
  times `(log y)^W Σ_{d≤D} (2W)^{ω(d)}/φ(d) = (log N)^{O_h(1)}`.  CRT then bounds the
  fourth-moment discrepancy by `mass⁴/N`, which is `o(1)`.

**Controls to run before asking for referee:**
- Astra's p=5, one parity site, target −1: the kernel must give the joint local mean `1/5`.
  Here `b = 1/2`, and `C_p(hit) = 1` (other site not hit).  The target phase is −1 on hit, 1 on
  nonhit, so `E[ψ_target·C] = (1/5)(−1)(1) + (4/5)(1)(1/2) = 1/5` ✓.
- The `h = 1` ET-phase case (site j=1 phase i, target k=2, p=5): `C_p(nonhit) = (3+i)/4`.

## Repair 2 (draft for referee): (5.3) on the target-augmented state

Source: `papers/ROUND2-multicutoff-astra.md` §3–5, with the §8 schedule
`y_j = N^{u^{−2}2^{−j}}` and `T_j = N^{2^{−j/2}/16}`.

**Augmented labels.**  Fix the target site k.  For `2J < p ≤ y_head`, put `I′_p = I_p ∪ {k}`
and `d′_p = |I′_p| ≤ d_p + 1`.
- For `p ≤ y_k`, k is already in `I_p`, so `I′_p = I_p`.  It is the same target residue, not a copy.
- Above `y_head`, `I′_p = I_p`, which is empty.

Model μ′: independently over p, label `j ∈ I′_p` with probability `1/p`, `none` with `1 − d′_p/p`.
Forgetting the k-label above `y_k` (k ↦ none) maps μ′ to μ.  So any function of the original
state has the same law under μ and μ′.  In particular P, `Φ^{≠k}` and the Riesz M4 bound are
unchanged.

**Every §3–5 step with `d′_p` for `d_p`:**
- **Atoms (3.4), CRT (5.1):** these use only `d′_p < p` (true: `d′_p ≤ J + 1 < 2J < p`) and the
  `d′_p` admissible residues.  So `|error| ≤ ∏_{p∈E} d′_p`, and the total is `≤ R′²`.
- **Box (3.2), (3.3):** add one radical coordinate `D′_k` = the product of the primes labelled k in
  `(y_k, y_head]`, with `T′ = N^{1/16}`.
  - Its one-site moment bound uses `y_head`: `E D′_k^{1/(2 log y_head)} ≤ e^{20}`.
  - Since `log y_head = log N/(2u²)`, the new tail is `e^{20} exp(−(log N/16)/(2 log y_head))`,
    which is `e^{20} e^{−u²/16}`.
  - Box count: `Σ_j log T_j/log N + 1/16 = (√2+1)/16 + 1/16 = (√2+2)/16 < 1/4`.
- **Split sieve (§4):** bands above `y_k` get `d′_b = d_b + 1`, and `r = 64d′_b + 2u_b + 2l + 4`
  keeps (4.1)–(4.5) verbatim (`λ ≤ 8d′`, `g_p = d′/p < 1/2`).
  - Support (4.6) grows by at most `128 Σ_b log Y_b ≤ 128 Σ_j log y_j ≤ 128 log N/u²`.
  - So `R′ ≤ R · N^{128/u²}`, which is negligible for u past a fixed threshold.
- **Conclusion (5.3′).**  For every complex `|F| ≤ 1` on the augmented state `(r mod Q, p ↦ I′_p-label)`:

      |E_ν′ F − E_μ′ F| ≤ 2e^{20}[Σ_j e^{−log T_j/(2 log y_j)} + e^{−u²/16}] + 4e^{−u}
                          + 2Q ∏_j⌊T_j⌋ ⌊T′⌋ R′²/N.

**What it buys.**
- `Λ(m)` (item 3's kernel) reads `gcd(m, e)` only at primes of moduli: Q, and P-primes ≤ `y_head`.
  The frozen phases use no larger primes, so every modulus has all prime factors ≤ `y_head`
  though `e ≤ QD` and `D ≫ y_head`.  And `p | m = n+k` ⟺ the label at p is k.
- So Λ, C and the clipped test `min(|Λ − C|², M)/M` are functions of the augmented state, and
  (5.3′) transfers them.
- The model fourth moment: `E_μ′|Λ|⁴ ≤ E_μ′|P|⁴ = M4` by conditional Jensen.  The tower identity
  holds in μ′.
- The arithmetic fourth moment: expand `1[gcd(m,e) = g] = Σ_{d | e/g} μ(d) 1[gd | m]` (item 3).
  The conductor is `≤ QD`, the mass grows by `2^{ω(e)}`, and the CRT remainder is
  `≤ (mass)⁴ (QD)⁴/N = o(1)` for θ < 1/4.

**Repair 2: ACCEPTED on paper (Astra 160352Z), for the radical-state model.**  Checks:
`log R′/log N ≤ 406/u² + 4/u`, and the CRT exponent `(√2+2)/16 + 2(406/u² + 4/u) − 1 < 0` for
large absolute u.  It does not make Ω-valuations state-measurable (item 4).
Open within repair 2 at submission: none that I saw.  Referee targets:
- the claim that μ′ marginalizes to μ;
- the moment bound for `D′_k` at the `y_head` scale;
- whether any §4 constant silently used more than `d_b ≤ J`.  It still holds: above `y_k` only
  sites `j < k` are active, so `d′_b ≤ (k−1) + 1 ≤ J`, and `g_p = d′/p < 1/2` since `p > 2J`.

## Item 5 (draft for referee): fixed fresh-site cut, so `MultBVResidue` sees finitely many z

`MultBVResidue`'s constants `B, C` depend on z, and the fresh site's `z_k = e(h/4^k)` varies with
`k ≤ winJ N`.  So cut the FRESH-site sum, not the frozen window, at a fixed `L = L(h, u, ε)`.

- **Tail of `T1′`.**  `|z^n − 1| ≤ n|z − 1|`, so
  `Σ_{k>L} |T1′_k| ≤ Σ_{k>L} |w_k| · mean_n ω_{(y_k, N]}(n+k)`.
  - Mertens for all primes (no AP upper bound needed) gives the mean as
    `≤ log(log N/log y_k) + O(1) = log(u² 2^k) + O(1)`.
  - With `|w_k| ≤ 2π|h| 4^{−k}`, the tail is `≤ C|h| 4^{−L}(log u + L)`.
- **Tail of the main term.**  `|W_y| ≤ 1` and `|g(κ_k, s_k)| ≤ C|κ_k| log s_k` for `k > k_h`, with
  `|κ_k| ≤ δ|w_k|`.  So `|W_y Σ_{k>L} g| ≤ C δ|h| 4^{−L}(log u + L)`.
- **Choice.**  Take L with `C|h| 4^{−L}(log u + L) ≤ ε/2`.  It depends only on h, u, ε, not on
  N or q, and fits the Prop's `+ε` slot.
- **Consequences:**
  - The type-I and main-term analysis runs only for `k ≤ L`.  `MultBVResidue` is used at the
    finitely many `z_1, …, z_L`, and its constants are maximized over them before `N → ∞`.
  - Shifts are `k ≤ L = O_{h,u,ε}(1)`, so the endpoint terms are `O(L)`.
  - The frozen phase `Φ^{≠k}` still carries every site up to `J₁`.  Its phases enter only through
    the coefficient mass W, the M4 constant and (5.3′), which are already uniform.
- **Scheduled Prop.**  With u = ⌈ρ⁻²⌉ and `|h| ≤ u` fixed by q, L depends on (q, ε).  It is still
  chosen before N, as the `∀ᶠ N` quantifier allows.

Referee target: that cutting the fresh site and keeping the frozen window at `J₁` is consistent
with C′'s hypotheses.  Here `k ≤ L` means the target site is always in the retained window.

## Item 4 (draft for referee): stay in ω; the Ω form is used only inside BV

The frozen objects (`omegaLe`, `omegaGt`) are ω-valued, and ω is radical-state measurable.  Ω is
not (Astra 160352Z).  So keep ω everywhere, and touch Ω only where `MultBVResidue` is consumed.

- **Main term (replaces the Ω gcd split of repair 1).**  `F = z^{ω_P}` and `F_y = z^{ω_{P,≤y_k}}`
  are multiplicative, and they agree on every prime power `p^ν` with `p ≤ y_k`.
  - For squarefree Q and `g | Q`: `gcd(m, Q) = g` ⟺ `m = a m″`, with `rad(a) = g`
    (a = the g-part of m, all exponents ≥ 1) and `gcd(m″, Q) = 1`.
  - Then, coprimally, `f(m) = F(a) F(m″) − F_y(a) F_y(m″) = z_k^{ω(g)} f(m″)`, using
    `F(a) = F_y(a) = z_k^{ω_P(g)}`.  It is exact, and τ is supported above 2J.
  - So `Σ_{gcd(m,Q)=g} f τ = z_k^{ω(g)} Σ_{rad(a)=g} Σ_{m″ ∈ (k/a, (N+k)/a], (m″,Q)=1} f(m″) τ(m″)`.
    The a-sum converges: `Σ_{rad(a)=g} 1/a = ∏_{p|g} 1/(p−1)`.  Truncate at `a ≤ A₀` with tail
    `≪ N Σ_{a>A₀, rad(a)|Q} 1/a`, which is → 0 in `A₀` uniformly for Q polylog: count
    `≤ (log A₀)^{ω(Q)}` per dyadic block.  **Uniformity, by Rankin:**
    `Σ_{a>A, rad(a)|Q} 1/a ≤ A^{−1/4} ∏_{p|Q}(1 − p^{−3/4})^{−1} ≤ A^{−1/4} exp(C J^{1/4})`.
    At `A₀ = √N` this is `N^{−1/8} e^{C(log log N)^{1/4}} → 0`.  So keep every `a ≤ √N` exactly
    (each has length `N/a ≥ √N` for the SD step) and bound the rest trivially.
  - The faithful SD target is therefore stated for `z^{ω_P}·τ·1[(·,Q)=1]`, not Ω.
- **Type I (E2) BV in ω form.**  `z^{ω_P} = z^{Ω_P} ∗ h_z`, where `h_z` is multiplicative and
  supported on squarefull b.
  - Locally `h_z(p^ν)` is the `X^ν`-coefficient of `(1 − (1−z)X)(1 − zX)/(1 − X)` for `p ∈ P`, and
    `h = δ_1` off P.  So `|h_z(p^ν)| ≤ 2` and `Σ_b |h_z(b)|/b < ∞`.
  - For a coprime residue c mod e: `ab ≡ c` with `p | b` and `p | e` would force `p | c`, so only
    `(b, e) = 1` terms occur.  Each is a coprime progression for a at length `x/b`.
  - Apply `MultBVResidue` (uniform in x) for `b ≤ B₀`.  The tail `b > B₀` is trivial,
    `≪ x Σ_{b>B₀} |h(b)|/b ≪ x B₀^{−1/2+ε}`.
  - The same applies to `F_y` with `Ω_{≤y}`.  This is a derived lemma
    (`multBVResidueOmega_of : MultBVResidue → MultBVResidueOmega`, believed about 90%), and the
    10-01 doc's "routine".
- **Q-block non-coprime classes (E2b) in ω form.**  Classes with `gcd(c+k, e) = g` use the same
  `m = a m″` decomposition.  The residue of m″ mod `e/g` is `(c+k)/g · (a/g)^{−1}`, which is a unit.
  Coprimality of m″ to g's primes is a union of `φ(g)` coprime classes mod g, so the modulus is e.
- **What changed from repair 1:**
  - no complete multiplicativity is assumed anywhere;
  - `F(g)` becomes `z^{ω(g)}`, which agrees with Astra's `F(g)` in the Ω form since g is
    squarefree;
  - the a-sum is new.

Referee targets: (i) the `rad(a) = g` decomposition and its `A₀`-tail uniformity as ω(Q) grows;
(ii) the `h_z` local factor and its sup bound; (iii) that MultBVResidue's uniformity in x covers
the lengths `x/b`, `b ≤ B₀`.

## Items 4–5 referee (Astra 161128Z) and statement drafts for review (NOT planted)

**Accepted:**
- Item 5, with this proviso: for the original deep sites `k > J₁` use the budgeted
  `C|h| 4^{−J₁} log log N = o(1)`, never `log(log N/log y_k)` with `y_k ≤ 1`.
- The local identity `H_p(X) = 1 + z(1−z)X²/(1−X)`, so `h(p) = 0` and `h(p^ν) = z(1−z)`.  The
  majorant `H(p^ν) = 2`, ν ≥ 2, gives `Σ_{b>B} H(b)/b ≤ C_ε B^{−1/2+ε}`.
- The radical decomposition and its unit residues.

**Corrected (Opus check agrees):**
- **A₀ grows:** `A₀ = (log N)^D`.  By Rankin (σ = 1/2), the tail is
  `≤ A₀^{−1/2} exp(C√J) = (log N)^{−D/2+o(1)}`.  The c382e4d2 choice `A₀ = √N` gave a true tail
  bound but a retained range too long for BV (`x/b` falls to `N^{1/4}`).  The retained `1/a` mass
  is `O(log J)`, and the SD input must be uniform over the lengths `N/a ≥ N/(log N)^D`.
- **ω-BV only at restricted level.**  Split the squarefull convolution at `B₀ = √x`.  Small b:
  `x/b ≥ √x`, so `e ≤ x^θ ≤ √(x/b)/log^B` for θ < 1/4, and `MultBVResidue` applies at `x/b`.
  Large b: trivially `≤ x^θ · x · x^{−1/4+ε/2}`, which is `o(x/(log x)^A)` for θ < 1/4.  Use the
  bounded raw product `|B_large τ| ≤ 1` in the main-term truncation.

**Statement drafts.**  The Lean is for statement review only; nothing is planted.

```lean
/-- Restricted-level BV for the ω form (derived from MultBVResidue; believed ~90%).
Proof: z^{ω_P} = z^{Ω_P} ∗ h_z, H_p = 1 + z(1−z)X²/(1−X); split at b ≤ √x (MultBVResidue at x/b,
moduli e ≤ x^θ ≤ √(x/b)/log^B since θ < 1/4) and b > √x (trivial, x^{θ+3/4+ε/2}).  Coprime c
kills (b, e) > 1.  NOT the full √x/log^B range.  Consumer: the conductor is Q·N^θ and the
length x = N/a with a ≤ (log N)^D, so invoke at θ′ ∈ (θ, 1/4); the strict gap absorbs both. -/
def MultBVOmegaRestricted : Prop :=
  ∀ q₀ a : ℕ, 3 ≤ q₀ → Nat.Coprime a q₀ → ∀ z : ℂ, ‖z‖ = 1 → ∀ θ : ℝ, 0 < θ → θ < 1/4 →
    ∀ A : ℝ, 0 < A → ∃ C : ℝ, 0 < C ∧ ∀ x y : ℕ, 3 ≤ x →
      ∑ e ∈ (Finset.Icc 1 ⌊(x : ℝ) ^ θ⌋₊).filter (fun e => Nat.Coprime e q₀),
        ⨆ c : {c : Fin e // Nat.Coprime c.val e},
          ‖apDiscrepancy (fun n => z ^ omegaLe (residueClass q₀ a) y n) x e c.val.val‖
        ≤ C * x / Real.log x ^ A

/-- Selberg–Delange for z^{ω_P} with a zero set S₀ and a 1/p tilt.  UNPROVED analytic input:
the statement is accepted as faithful (Astra 162350Z), but its uniform instantiation from the SD
source theorem is not checked (analytic continuation and derivative summability of the normalized
series).  Division-free: no small-prime value is inverted; τ = 0 on S₀ encodes coprimality.
Uniform in x ≥ 3 (all lengths N/a), in finite prime sets S₀ through exp(C Σ_{S₀} p^{−1/2}), and
in tilts with |τ_p − 1| ≤ K/p off S₀.  In use: S₀ = ALL primes of Q, since the radical
decomposition leaves (m″, Q) = 1; τ_p = b_p^{−1} on (2J, y_head] and 1 beyond; K = 2W.  Then
Σ_{S₀} p^{−1/2} ≤ C√J, and the factor is (log N)^{o(1)} against a 1/log x error. -/
def SelbergDelangeOmegaTilted : Prop :=
  ∀ q₀ a : ℕ, 3 ≤ q₀ → Nat.Coprime a q₀ → ∀ K : ℝ, 0 ≤ K → ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℂ, ‖z‖ = 1 →
    ∀ (S₀ : Finset ℕ) (τ : ℕ → ℂ), (∀ p ∈ S₀, p.Prime) → (∀ p ∈ S₀, τ p = 0) →
      (∀ p, p.Prime → p ∉ S₀ → ‖τ p - 1‖ ≤ K / p) →
      ∃ L₀ : ℂ,
        Tendsto (fun X : ℕ => ∏ p ∈ (Finset.Icc 1 X).filter Nat.Prime,
          (1 - 1 / (p : ℂ)) ^ (1 + (z - 1) / (Nat.totient q₀ : ℂ)) *
            (1 + τ p * (if p % q₀ = a % q₀ then z else 1) / ((p : ℂ) - 1))) atTop (𝓝 L₀) ∧
        ∀ x : ℕ, 3 ≤ x →
          ‖(∑ n ∈ Finset.Icc 1 x,
                z ^ ((n.primeFactors.filter (fun p => p % q₀ = a % q₀)).card)
                  * ∏ p ∈ n.primeFactors, τ p) / (x : ℂ)
            - L₀ * (Real.log x : ℂ) ^ ((z - 1) / (Nat.totient q₀ : ℂ))
                * (Complex.Gamma (1 + (z - 1) / (Nat.totient q₀ : ℂ)))⁻¹‖
          ≤ C * Real.exp (C * ∑ p ∈ S₀, 1 / Real.sqrt p)
              * Real.log x ^ (((z - 1) / (Nat.totient q₀ : ℂ)).re - 1)

theorem multBVOmegaRestricted_of (h : MultBVResidue) : MultBVOmegaRestricted := sorry
-- superseded by the four-input producer in the next section
-- theorem siteFactorizationScheduled_of (hBV : MultBVOmegaRestricted)
--     (hSD : SelbergDelangeOmegaTilted) : SiteFactorizationScheduled := sorry
```

**Statement-review questions for Astra:**
1. Is the `K/p`-tilt plus zero-set `S₀` family exactly what repair 1 and item 4 consume?  In
   particular: `τ_p = b_p^{−1}` above 2J, 0 on `Q/g`, 1 elsewhere, at lengths `x = N/a`.
2. Should the SD error carry `exp(C Σ_{S₀} p^{−1/2})`, or is a cleaner sufficient form
   `C (1 + |S₀|)^C`?  `|S₀| ≤ π(2J)` would also be `(log N)^{o(1)}`.
3. The producer's hypotheses omit C′'s (5.3′) and the Riesz M4.  They are paper-proved, not
   frozen Props.  Should they become named Props first, so the producer's dependencies are
   honest?  My lean: yes, as `AugmentedJointTV` and `RieszFourthMoment`.

## The two paper-proved inputs as named Props (drafts for review, NOT planted)

This answers question 3 above with drafts, so the producer's dependencies are honest.  Both are
stated without a probability space.  The model expectation of a function of the residues
`n mod p` is the exact average over one CRT period, so the model side is `periodMean` over
`∏ p`, a finite sum.

- **`RieszFourthMoment`** is the (L)–(P)–(B)–(R) theorem of `coefmass-2026-10-10.md`.
  - `ψ_p(n) = ∏_{j : p ≤ y_j, p ∣ n+j+1} z_j` is the local phase, so the frozen product is
    `Φ = ∏_p ψ_p` exactly.  `μ_p` is its period mean.
  - The expansion runs over any finite set P of primes `> 2J`, where the residues `−(j+1)` are
    distinct mod p and `V_p ≤ A/p` holds.  The primes `≤ 2J` stay in the exact Q-block factor,
    which has modulus 1 and leaves `|·|⁴` unchanged.
  - The bound is uniform in J, y, P and K = log D, as (R) states.  Only `C₀` (Mertens) is
    existential.
- **`AugmentedJointTV`** is (5.3′) of repair 2, evaluated on the §8 schedule.
  - On `cutU u N J`: `log T_j/(2 log y_j) = u² 2^{j/2}/32`, so the j-sum is `≤ C e^{−u²/32}`.
    The new coordinate gives `e^{−u²/16}`, and the CRT term is `o(1)` for `u ≥ u₀`.  For
    `u ≥ 32`, all of it is `≤ C e^{−u} + ε` eventually.
  - The state is `(n mod Q, p ↦ augmented label)` with `Q = primorial (2J)`, for the primes of S
    in `(2J, y_head]`, `y_head = cutU u N J 0`.  F factors through the state, `‖F‖ ≤ 1`, and the
    bound is uniform in F and in the target k.
  - It is h-free: the state carries no phase.

```lean
/-- Local phase of prime `p` at `n`: `ψ_p(n) = ∏_{j : p ≤ y_j, p ∣ n+j+1} z_j`. -/
noncomputable def psiP (J : ℕ) (y : Fin J → ℕ) (h : ℤ) (p n : ℕ) : ℂ :=
  ∏ j : Fin J, if p ≤ y j ∧ p ∣ n + j.val + 1 then zPhase h J j else 1

/-- Exact average over one period: the model expectation, by CRT. -/
noncomputable def periodMean (F : ℕ → ℂ) (M : ℕ) : ℂ := (∑ n ∈ Finset.range M, F n) / M

noncomputable def muP (J : ℕ) (y : Fin J → ℕ) (h : ℤ) (p : ℕ) : ℂ :=
  periodMean (psiP J y h p) p

/-- Riesz-truncated centered expansion over a finite prime set `P`:
`Σ_{T ⊆ P} (1 − log d_T/K)_+^k ∏_{p∉T} μ_p ∏_{p∈T} (ψ_p − μ_p)`. -/
noncomputable def rieszCentered (P : Finset ℕ) (J : ℕ) (y : Fin J → ℕ) (h : ℤ) (K : ℝ) (k : ℕ)
    (n : ℕ) : ℂ :=
  ∑ T ∈ P.powerset, ((max 0 (1 - Real.log (∏ p ∈ T, (p : ℝ)) / K)) ^ k : ℝ) *
    ((∏ p ∈ P \ T, muP J y h p) * ∏ p ∈ T, (psiP J y h p n - muP J y h p))

/-- **Riesz fourth moment (paper: Astra, refereed by Opus, 2026-10-11).**  For integer
`k > β = 9A/2`, `A = Σ_j |z_j − 1|²`, the model `‖P_k‖₄` is at most
`(k! e/2π) e^{9C₀A/2} [2^{β/2} π + 2/(k−β)]`, uniformly in `J, y, P, K`. -/
def RieszFourthMoment : Prop :=
  ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ (J : ℕ) (y : Fin J → ℕ) (h : ℤ) (P : Finset ℕ),
    (∀ p ∈ P, p.Prime ∧ 2 * J < p) → ∀ K : ℝ, 1 ≤ K → ∀ k : ℕ,
      let A := ∑ j : Fin J, ‖zPhase h J j - 1‖ ^ 2
      9 * A / 2 < k →
        (∑ n ∈ Finset.range (∏ p ∈ P, p), ‖rieszCentered P J y h K k n‖ ^ 4)
            / (∏ p ∈ P, p : ℕ)
          ≤ ((k.factorial : ℝ) * Real.exp 1 / (2 * Real.pi) * Real.exp (9 * C₀ * A / 2)
              * (2 ^ (9 * A / 4) * Real.pi + 2 / (k - 9 * A / 2))) ^ 4

/-- Augmented label at `p`: the sites `j` with `p ∣ n+j+1` that are active at `p` (`p ≤ y_j`),
plus the target `k`.  For `p > 2J` it has at most one element. -/
def augLabel (J : ℕ) (y : Fin J → ℕ) (k : Fin J) (p n : ℕ) : Finset (Fin J) :=
  Finset.univ.filter (fun j => (p ≤ y j ∨ j = k) ∧ p ∣ n + j.val + 1)

/-- Labelled primes: the primes of `S` in `(2J, Y]`. -/
def labPrimes (S : ℕ → Prop) [DecidablePred S] (J Y : ℕ) : Finset ℕ :=
  (Finset.Ioc (2 * J) Y).filter (fun p => p.Prime ∧ S p)

/-- **Augmented joint TV (repair 2, (5.3′) on the §8 schedule; paper, accepted 160352Z).**
Any `‖F‖ ≤ 1` that factors through `(n mod primorial 2J, p ↦ augLabel p n)` for the labelled
primes up to `y_head` has integer mean within `C e^{−u}` of its model (period) mean. -/
def AugmentedJointTV : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∃ u₀ : ℕ, ∀ q a : ℕ, 3 ≤ q → Nat.Coprime a q → ∀ u : ℕ, u₀ ≤ u →
    ∀ ε > 0, ∀ᶠ N : ℕ in atTop, ∀ k : Fin (winJ N), ∀ F : ℕ → ℂ, (∀ n, ‖F n‖ ≤ 1) →
      (let J := winJ N
       let y := cutU u N J
       let P := labPrimes (residueClass q a) J (y ⟨0, k.pos⟩)
       ∀ n m, n % primorial (2 * J) = m % primorial (2 * J) →
         (∀ p ∈ P, augLabel J y k p n = augLabel J y k p m) → F n = F m) →
      ‖prefixMean F N
        - periodMean F (primorial (2 * winJ N) *
            ∏ p ∈ labPrimes (residueClass q a) (winJ N)
                    (cutU u N (winJ N) ⟨0, k.pos⟩), p)‖
        ≤ C * Real.exp (-(u : ℝ)) + ε

theorem siteFactorizationScheduled_of (hBV : MultBVOmegaRestricted)
    (hSD : SelbergDelangeOmegaTilted) (hTV : AugmentedJointTV) (hM4 : RieszFourthMoment) :
    SiteFactorizationScheduled := sorry
```

**What stays a lemma, not an input:**
- the integer-side M4, which equals the model M4 up to CRT remainders `≤ (mass)⁴ D⁴/N`, for
  θ < 1/4;
- the scalar steps `ResidualNormScale`, `UniformFrequencySuppression` and
  `ScheduledRieszEnergySmall` (Astra's private ledger), which are elementary.

**Referee targets:**
1. Is `Q = primorial (2J)` the Q of `ROUND2-multicutoff-astra.md` §3?  If Q also carries q, the
   key becomes `n mod (q · primorial 2J)`.
2. `AugmentedJointTV` puts `∀ k` and `∀ F` inside `∀ᶠ N`, i.e. uniform in both.  (5.3′) is uniform
   in F by construction; the k-uniformity uses `d′_b ≤ J`.
3. Is `C e^{−u}` (u ≥ 32) the right packaging, or should the Prop keep the raw (5.3′) right-hand
   side and let the producer evaluate it?
4. `RieszFourthMoment` writes `2^{β/2}` as `2^{9A/4}`.  Its hypothesis `2J < p` is stronger than
   the `p > J` that `V_p ≤ A/p` needs.

Control (Opus, exact, J=3, P={7,11,13,17}): with k=0 and K large, `rieszCentered` equals the
ω-form Φ(n) to 5e-16; at k=2, its period mean equals `∏ μ_p` to 3e-14.

**Elaboration check (Opus, 2026-10-11):** every Lean block in the two statement sections compiles.
The check was against the built `NormalNumbers.CPrimeSiteFactorization` in a scratch file
(`lake env lean`, not in the tree), with sorry warnings only.  It shows the statements elaborate,
not that they mean what is intended.

## Statement review (Astra 162350Z) and the producer assembly

**Applied above:**
- the θ′ ∈ (θ, 1/4) consumer note on `MultBVOmegaRestricted`;
- `SelbergDelangeOmegaTilted` gets `0 ≤ K` and prime `S₀`, and its in-use zero set is ALL primes
  of Q.  The radical decomposition leaves `(m″, Q) = 1`; "Q/g" belonged to the superseded Ω split.
- SD is relabelled as an unproved analytic input whose statement is accepted as faithful.  Its
  instantiation from the source theorem (continuation, derivative summability) is unchecked.
- SD keeps `exp(C Σ_{S₀} p^{−1/2})`.

Already consistent:
- **Q** = `primorial (2J)` in `AugmentedJointTV` is ROUND2 §3's Q (line 80: all primes `≤ 2J`).
  The Setup's P-only Q is coarser, so its functions are state functions too.
- **`RieszFourthMoment` carries its h-growth explicitly.**
  - `|w_j| ≤ min(2, 2π|h|4^{−j−1})`, so `A ≤ 4 log₄(2π|h|) + C = O(1 + log|h|)`.
  - With `k = ⌈9A/2⌉ + 1` (so `k − β ≥ 1`), the bound's log is
    `4[log k! + 9C₀A/2 + (9A/4) log 2 + log(π + 2)] = O((1 + log h) log(2 + log h))`.
  - No bare `∃ B(h)` appears.

**Type-I Q-part truncation (Astra item 4), checked independently.**  Put
`E = {n : Q-part(n+k) > A₀}`.
- `#E ≤ Σ_{a>A₀, rad(a)|Q} (N+k)/a ≤ (N+k) A₀^{−1/2} ∏_{p≤2J}(1 − p^{−1/2})^{−1}`, which is
  `≤ (N+k) A₀^{−1/2} e^{C√J}` (Rankin, σ = 1/2).
- Hölder with exponents `(4, ∞, 4/3)` gives `|mean[P f 1_E]| ≤ ‖P‖_{4,int} · 2 · Prob(E)^{3/4}`.
- With `A₀ = (log N)^D` and the arithmetic M4, this is `B_h^{1/4}(log N)^{−3D/8+o(1)} → 0`.
- Only then expand `P·1_{E^c}` into progressions.  Each `a ≤ A₀` with `rad(a) | Q` is one BV
  invocation at length `N/a`.  The number of such a is `≤ ∏_{p≤2J}(1 + log A₀/log p)`, which is
  `exp(O(π(2J) L₃N)) = (log N)^{O(1)}`, absorbed by BV's free A.
- The A₀-tail of the coefficient mass is never paid: that would cost `N^θ`.  Agreed.

**New named input: the model energy above the Riesz cutoff.**  It is elementary.
- The centered terms `c_T` are orthogonal under the period mean: for `T ≠ T′`, a prime in the
  symmetric difference contributes `E φ_p = 0`.
- Also `E|c_T|² = ∏_{p∉T}|μ_p|² ∏_{p∈T} V_p`, and these sum to `∏(|μ_p|² + V_p) = 1`.
- Then `(1 − (1−x)_+^k)² ≤ kx` for `k ≥ 1`, `x ≥ 0`.
- Exact control: J=3, P={7,11,13,17}, four (K, k) pairs.  The period-mean energy equals the
  orthogonal sum to all printed digits, and is `≤ (k/K) Σ V_p log p` (e.g. 0.1866 ≤ 0.2987;
  0.5163 ≤ 2.145).

```lean
/-- **Model energy above the Riesz cutoff (elementary; a proof target, not literature).** -/
def RieszEnergyTail : Prop :=
  ∀ (J : ℕ) (y : Fin J → ℕ) (h : ℤ) (P : Finset ℕ), (∀ p ∈ P, p.Prime) →
    ∀ K : ℝ, 0 < K → ∀ k : ℕ, 1 ≤ k →
      (∑ n ∈ Finset.range (∏ p ∈ P, p),
          ‖(∏ p ∈ P, psiP J y h p n) - rieszCentered P J y h K k n‖ ^ 2) / (∏ p ∈ P, p : ℕ)
        ≤ k / K * ∑ p ∈ P, (1 - ‖muP J y h p‖ ^ 2) * Real.log p

/-- Mertens in progressions, asymptotic form (classical; the repo has only lower-bound rates,
`G4.MertensAP.mertensRate_residueClass`).  It gives the fresh mass
`Σ_{y<p≤x, p≡a} 1/p = δ log(log x/log y) + o(1)` as `y → ∞`. -/
def MertensAPAsymptotic : Prop :=
  ∀ q a : ℕ, 1 ≤ q → Nat.Coprime a q → ∃ M : ℝ, Tendsto (fun x : ℕ =>
    G4.MertensAP.sumInvPrimesIn (residueClass q a) x
      - Real.log (Real.log x) / (Nat.totient q : ℝ)) atTop (𝓝 M)

theorem siteFactorizationScheduled_of' (hBV : MultBVOmegaRestricted)
    (hSD : SelbergDelangeOmegaTilted) (hTV : AugmentedJointTV) (hM4 : RieszFourthMoment)
    (hE : RieszEnergyTail) (hMer : MertensAPAsymptotic) : SiteFactorizationScheduled := sorry
```

**The producer proof, end to end (paper; every input named).**  Fix q ≥ q₁, a unit, and
`1 ≤ |h| ≤ u = schedU q`, with `δ = 1/φ(q)` and `ρ = δ log 2`.  Fix θ < θ′ < 1/4, the Riesz degree
`k_R = ⌈9A/2⌉ + 1`, `D = N^θ` and ε > 0.  Write `J = winJ N` and `y = cutU u N J`.

| step | what | input | size after limsup N |
|---|---|---|---|
| 0a | deep frozen sites `j > J₁ ≈ L₃N` dropped from Φ and from `W_y` | lemma (`|z^ω−1| ≤ ω|w|`, Mertens) | `C|h|4^{−J₁} log log N → 0` |
| 0b | fresh sites `k > L(h,u,ε)` dropped from `T1′` and from `W_y G_h` | lemma (item 5), `hMer` | `≤ ε/2` |
| 1 | `T1′_k = mean[P f(·+k)] + E1_k` | definition | |
| 2 | E1: `‖f_k‖₂ ‖Φ^{≠k} − P‖₂`, with `‖f_k‖₂² ≤ 2|w_k| δ log s_k` | `hMer`; clipped-L² lemma from `hTV` + `hM4` + `hE` + the CRT M4 lemma | `Σ_k ≤ C ρ³ log²(1/ρ) + C B_h^{1/4} e^{−u/4}` |
| 3 | Q-part truncation `1_E` | Hölder lemma + `hM4` + CRT M4 | `→ 0` |
| 4 | `P·1_{E^c}` = progressions; BV error, `a ≤ A₀`, θ′ | `hBV` | `o(1)` |
| 5 | `Λ − C` (truncation residual of the kernel) | as step 2 on the augmented state; conditional Jensen | same as step 2 |
| 6 | `mean[F_y C] = E_μ′[F_y C] + O(e^{−u}) + o(1)` | `hTV` (`|F_y C| ≤ 1` is a state function) | `C e^{−u}` |
| 7 | `mean[F C]` via `m = a m″` and SD at lengths `(N+k)/a` | `hSD` (S₀ = primes of Q, K = 2W), `B_large` and `C_small` outside | `o(1)` errors |
| 8 | Euler-factor matching: `mean[F C] = G(κ_k, s_k) E_μ′[F_y C](1 + O(W/y_k)) + o(1)` | lemma, `hMer` | `o(1)` |
| 9 | `E_μ′[F_y C] = E_μ′[F_y Φ^{≠k}]` = model `W_y`, which is within `C e^{−u}` of `windowMeanLeG` | tower identity in μ′; `hTV` | `C e^{−u} Σ|g_k|` |

**Step 8 in full (division-free).**  Per prime, both sides are local means of the same factor
`C_p`:
- At `p ≤ y_k` both sides have the factor `E_p[F_y C_p] = E_p[F C_p]`, since F and F_y agree.
- At `y_k < p ≤ y_head`, the ratio is `(b_p(1−1/p) + z_p/p)/(b_p(1−1/p) + 1/p) = 1 + (z_p − 1)/p + O(W/p²)`.
- Beyond `y_head`, the SD side has `1 + (z_p − 1)/p` and the model side has 1.
- SD's normalization supplies `∏_{p≤X}(1 − 1/p)^{κ}(log x)^{κ}/Γ(1+κ)`, with `κ = (z_k − 1)δ`.
- Mertens in progressions: `∏_{y_k<p≤X, p∈P}(1 + (z_k − 1)/p) = (log X/log y_k)^{κ}(1 + o(1))`.
- Mertens over all primes: `∏_{p≤X}(1 − 1/p)^κ ~ (e^{−γ}/log X)^κ`.
- So the product is `s_k^κ e^{−γκ}/Γ(1+κ)`, with `s_k = log N/log y_k = u² 2^{k+1}`.  That is
  `1 + g(κ_k, s_k)`, `siteFactor`'s value.  `log(N/a) = log N (1 + O(L₂N/log N))` for `a ≤ A₀`.
- The small-prime factors appear only as the same `C_small(g)` multiplier on both sides, never
  as a divisor.  Only the large-prime ratio is formed, where `b_p ≠ 0` (threshold `2J ≥ 2W + 2`).

**Sum over k ≤ L.**  `T1′ − W_y G_h = Σ_{k≤L}(E1_k + residuals) + (step 6, 9 errors)·Σ_k|g_k| + ε`.
- Steps 2 and 5 sum to `C ρ³ log²(1/ρ) + C δ^{1/2} L_h (log u + L_h)^{1/2} B_h^{1/4} e^{−u/4}`.
- Steps 6 and 9 sum to `C e^{−u} Σ_k |g_k| ≤ C e^{−u} δ L_h log u`.
- On the schedule (`|h| ≤ u`, `log B_h = o(u)`, Astra's `UniformFrequencySuppression`), the total
  is `≤ C(ρ² + e^{−u/8}) + ε` with C absolute.  q₁ is chosen so that `schedU q₁` passes U.

**Dependency honesty.**
- **Named inputs:** `hBV, hSD, hTV, hM4, hE, hMer`.
  - `hSD` is unproved analytic.
  - `hBV` is derived from `MultBVResidue`, whose own TSW node is open.
  - `hTV`, `hM4` and `hE` are paper-proved (`hE` is elementary, a Lean proof target).
  - `hMer` is classical.
- **Proved-dependency lemmas, to be planted as separate named sorries, never folded into the
  producer:**
  - `crtFourthMoment` (integer M4 = model + o(1), θ < 1/4, gcd-indicator expansion);
  - `clippedL2Transfer` (E1 from TV + M4 + energy);
  - `rareQPartHolder` (step 3);
  - `deepSiteTruncation` (0a) and `freshSiteCut` (0b);
  - `eulerFactorMatching` (step 8);
  - Astra's three scalar Props.
- Producer believed ~60%.  The weakest joints:
  - step 7's uniform SD instantiation;
  - step 5's arithmetic fourth moment for Λ (the indicator expansion's mass);
  - step 8's interchange of `X → ∞` with the finite `y_head`.

**Elaboration check (Opus):** every Lean block from "Items 4–5 referee" on compiles in a scratch file.
The imports are `NormalNumbers.CPrimeSiteFactorization` and `NormalNumbers.G4MertensAP`, and
`MertensAPAsymptotic` needs the second.  Only sorry warnings appear.  This is elaboration, not
meaning.
