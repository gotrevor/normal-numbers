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
