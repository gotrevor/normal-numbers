# `TwistedSiegelWalfisz`: uniformity in the cutoff y, by a two-regime split

Opus (Ren), 2026-10-11, attended.  Paper draft for Astra's referee, **not refereed, not in Lean**.
Target: `CPrimeSiteFactorization.TwistedSiegelWalfisz` (frozen, unchanged).  Scope assigned by Astra
`20261011T220855Z`.

## Claim

`TwistedSiegelWalfisz` follows from two inputs that carry no cutoff at all:

- **(SW)** Siegel–Walfisz for a nonprincipal character `ψ` mod `m`: for all `A₁, B₁` there is `C`
  with `|Σ_{p≤u} ψ(p)| ≤ C u/(log u)^{A₁}` whenever `m ≤ (log u)^{B₁}`.  A theorem.
- **(TSW∞)** the `y = ∞` case: `|Σ_{m≤X} z^{Ω_P(m)} χ(m)| ≤ C X/(log X)^{A₁}` for `χ ≠ 1` mod
  `r ≤ (log X)^{B₁}`, `(r, q₀) = 1`, with `C = C(q₀, a, z, A₁, B₁)`.

The cutoff enters only through elementary bookkeeping: for small y the twist by χ is killed by
the trivial character-sum bound, and for large y the y-truncation is a finite-shape convolution
against primes beyond y, which SW controls.  The 10-01 obstruction (`Σ_{p≤y} p^{−σ}` blowing up
on the contour) never arises, because no contour is moved after the truncation.

**Confidence:** about 75% that the argument below is complete as written; the identities are
exact-checked (below).  TSW∞ is a separate literature question (see "Inputs").

## Notation

`P = {p prime : p ≡ a (q₀)}`, `g_y(n) = z^{Ω_{P,≤y}(n)}` (the Lean `omegaMultLe`, multiplicity
counted), `S = S(x, y) = Σ_{n≤x} g_y(n) χ(n)`, `L = log x`, `K = K(A, B)` a large constant fixed
below.  The two regimes are complementary:

- **small:** `log y ≤ L/(K log L)`;
- **large:** `log y > L/(K log L)`.

## Small y: `g_y = 1 ∗ h`, trivial character sums

The Euler factor of `g_y` at `p ∈ P, p ≤ y` is `1/(1 − z p^{−s})`.  Dividing by ζ's leaves `h`
multiplicative, supported on `P_{≤y}`-composed `d`, with `h(p^j) = (z − 1) z^{j−1}`, so
`|h(d)| ≤ 2^{ω(d)}`.  Since χ is completely multiplicative,

    S = Σ_d h(d) χ(d) Σ_{m ≤ x/d} χ(m),   and   |Σ_{m≤X} χ(m)| ≤ r  (χ ≠ 1 mod r).

So `|S| ≤ r · Σ_{d ≤ x, d y-smooth} 2^{ω(d)}`.  Rankin with `η = min(1/2, 1/log y)`: for `p ≤ y`,
`p^η ≤ e` and `p^{1−η} ≥ √p`, so `1/(p^{1−η} − 1) ≤ C₀/p` and

    Σ_{d≤x, y-smooth} 2^{ω(d)} ≤ x^{1−η} Π_{p≤y} (1 + 2/(p^{1−η} − 1)) ≤ C₁ x e^{−ηL} (log y + 2)^{2C₀}.

If `y ≥ e²`, `e^{−ηL} = e^{−L/log y} ≤ L^{−K}`; if `y < e²`, `e^{−ηL} = x^{−1/2}`.  Hence
`|S| ≤ C₁ x L^{B + 2C₀ − K}`, which is `≤ x/L^A` once `K ≥ A + B + 2C₀`.  No use of `(r, q₀) = 1`,
no SW: the regime is elementary (and Lean-friendly).

## Large y: `g_y = G ∗ k`, primes beyond y

Let `G = z^{Ω_P}` (no cutoff).  At `p ∈ P, p > y` the factor of `g_y` is `1/(1 − p^{−s})` against
`G`'s `1/(1 − z p^{−s})`, so `g_y = G ∗ k` with `k` supported on `D_y` (numbers all of whose prime
factors lie in `P ∩ (y, ∞)`) and `k(p^j) = 1 − z`, i.e. `k(d) = (1 − z)^{ω(d)}`.  Then

    S = Σ_{d ∈ D_y} k(d) χ(d) T(x/d),   T(X) = Σ_{m≤X} G(m) χ(m).

Every `d ∈ D_y ∩ [1, x]` has `ω(d) ≤ L/log y < K log L`, and

    Σ_{d ∈ D_y, d≤x} 2^{ω(d)}/d ≤ Π_{y<p≤x} (1 + 2/(p − 1)) ≤ C (L/log y)² ≤ C (K log L)².   (★)

Put `Z = exp(√L)`.

**(i) `d ≤ x/Z`.**  Here `log(x/d) ≥ √L`, so `r ≤ L^B ≤ (log(x/d))^{2B}` and TSW∞ (with
`B₁ = 2B`) gives `|T(x/d)| ≤ C (x/d) L^{−A₁/2}`.  By (★) this part is `≤ C x (log L)² L^{−A₁/2}`;
take `A₁ = 2A + 2`.

**(ii) `d > x/Z`.**  Then `m ≤ x/d < Z`; swap the order:

    Σ_{m<Z} G(m) χ(m) [K_y(x/m) − K_y(x/Z)],   K_y(X) = Σ_{d ∈ D_y, d≤X} k(d) χ(d).

**Lemma (K).**  For `x/Z ≤ X ≤ x`: `|K_y(X)| ≤ 1 + C X (log L)^{A₃+2} L^{−A₃}`.

*Proof.*  Split `d > 1` by its largest prime `p` and that prime's exponent `j`.
- `j ≥ 2`: at most `2 Σ_{p>y} Σ_{j≥2} X/p^j ≤ 4X/y`, and `y > exp(L/(K log L))` beats any power of L.
- `j = 1`: `d = d′p` with `P⁺(d′) < p`, and the sum is
  `(1 − z) Σ_{d′} k(d′) χ(d′) Σ_{p ∈ P, U₁ < p ≤ U₂} χ(p)` with `U₁ = max(y, P⁺(d′))`,
  `U₂ = X/d′`.  Expand `1_P` by characters ψ mod q₀: `χψ` is a nonprincipal character mod `r q₀`
  because `χ ≠ 1` and `(r, q₀) = 1`.  Both endpoints are `≥ y`, so `log u ≥ L/(K log L) ≥ √L`
  and `r q₀ ≤ q₀ L^B ≤ (log u)^{2B+1}`: SW applies at each endpoint, and the prime sum is
  `≤ 2C (X/d′)(log y)^{−A₃} ≤ 2C (X/d′)(K log L / L)^{A₃}`.  Sum over `d′` with (★).  ∎

With `A₃ = A + 2`, part (ii) is `≤ 2Z + C x (log Z)(log L)^{A₃+2} L^{−A₃} ≤ 2Z + C x L^{−A−1/2}`,
and `Z = exp(√L) = o(x/L^A)`.

So in both regimes `|S| ≤ C x/L^A` with `C = C(q₀, a, z, A, B)`, uniform in `y, r, χ`.  The case
`y ≥ x` is the large regime with `D_y ∩ [1, x] = {1}`, i.e. TSW∞ itself.

## Exact checks (identities only)

`tmp/opus-tsw/identities.py` (scratch, not committed): `q₀ = 5, a = 2, r = 7`, χ of order 3,
`z = e^{1.1i}`, `x ∈ {200, 777, 1500}`, `y ∈ {1, 3, 7, 13, 50, 300, 10⁹}`.  Both decompositions
reproduce `S` to `2.7·10⁻¹³`.  Red control: flipping the sign of `k` gives an error of `14.6`.
Partial sums of χ stay `≤ 1 ≤ r` up to `X = 2000`.  These check the algebra, not the asymptotics.

## Inputs, and what is owed

- **SW** is a theorem; in the repo's style it enters as a `Literature` Prop.
- **TSW∞** is the Selberg–Delange-with-characters estimate at `y = ∞`, plus Siegel for possible
  exceptional zeros of the `χψ`.  All `χψ` are nonprincipal, so the generating function
  `L(s, χ) Π_ψ L(s, χψ)^{(z−1)ψ̄(a)/φ(q₀)} × (holomorphic)` has no pole at `s = 1`.  ⚠️ **Source
  RECALLED, not checked:** Granville–Koukoulopoulos, "Beyond the LSD method for the partial sums of
  multiplicative functions" (Ramanujan J., 2019), Thm 1, with `κ = 0` (the `1/Γ(κ − j)` main-term
  coefficients vanish).  The uniformity in `r ≤ (log X)^{B₁}` must be confirmed against the
  source before TSW∞ is planted.  Tenenbaum II.5 is the other candidate; no book text here.
- Owed before Lean: the referee's check of the two regimes; the source check for TSW∞.

## Consequence for the ledger

If accepted, E3's "inherited and still owed: TSW's uniformity in y" becomes "TSW ⇐ SW + TSW∞",
and the ledger's open analytic node shrinks to a cutoff-free, literature-strength statement.
