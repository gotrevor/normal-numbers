# `TwistedSiegelWalfisz`: uniformity in the cutoff y, by a two-regime split

Opus (Ren), 2026-10-11, attended.  Paper draft for Astra's referee, **not refereed, not in Lean**.
Target: `CPrimeSiteFactorization.TwistedSiegelWalfisz` (frozen, unchanged).  Scope assigned by Astra
`20261011T220855Z`.

## ✅ Primary route: direct, from prime Siegel–Walfisz alone (Astra `224341Z`, Opus-checked)

Astra found a shorter proof that needs neither TSW∞ nor Granville–Koukoulopoulos; Opus reviewed it
step by step and accepts it (`20261011T224511Z`).  It supersedes the two-regime route below,
which is kept as a record.

**Largest-prime transfer.**  Let `f` be multiplicative with `|f| ≤ 1`, and `2 ≤ W ≤ X`.  Suppose
every prime interval `W ≤ U < V ≤ X` has `|Σ_{U<p≤V} f(p)| ≤ η V`.  Then

    |Σ_{n≤X} f(n)| ≤ Ψ(X, W) + X/(W − 1) + η X (1 + log X).

Proof: split `n` by its largest prime `p = P⁺(n)`.  If `p ≤ W`, then `n` is `W`-smooth (at most
`Ψ(X, W)` of them).  If `p > W` and `p² | n`, there are at most `X Σ_{p>W} p⁻² ≤ X/(W − 1)`.
Otherwise `n = mp` uniquely, with `p > max(W, P⁺(m))`, and that block is exactly
`Σ_{m≤X/W} f(m) Σ_{max(W,P⁺(m)) < p ≤ X/m} f(p)`.  Drop empty intervals and use `Σ_{m≤X} 1/m ≤ 1 + log X`.

**Application.**  `f(n) = z^{Ω_{P,≤y}(n)} χ(n)` is completely multiplicative, `|f| ≤ 1`, and
`f(p) = χ(p)[1 + (z − 1) 1_P(p) 1_{p≤y}]`.  The cutoff only truncates an interval at `y`.  Expand
`1_P` by characters ψ mod q₀; each `χψ` is nonprincipal mod `r q₀`.  Take `L = log X`,
`W = ⌈e^{√L}⌉`.  Every nonempty endpoint `t ≥ W` has `r q₀ ≤ q₀ L^B ≤ (log t)^{2B+2}`, so SW with
saving `D = 2A + 4` gives `η ≤ C L^{−A−2}`, uniformly in `y, r, χ`, **and in unit z**.  Rankin (for `X` large enough that `η = 1/log W ≤ 1/2`; bounded `X` goes into `C`) gives
`Ψ(X, W) ≤ C X e^{−L/log W} (log W)^{C₀}`, which is `O(X/L^A)`.  Hence `|S| ≤ C X/L^A`, which is
slightly stronger than frozen `TwistedSiegelWalfisz`, whose `C` may depend on `z`.

**Checks.**  The partition passed a finite numerical check, run independently by each of us: Astra on 108
cases, Opus with `tmp/opus-tsw/partition.py` (`X ≤ 2500`, `W ∈ {2, 5, 11, 30}`,
`y ∈ {1, 7, 40, 10⁹}`), error `2.8·10⁻¹³`.  Red control: dropping the `p² | n` block gives `4.66`.

**Status:** TSW ⇐ SW (a theorem; a `Literature` Prop in this repo's style).  Paper-level, refereed
both ways.  Not in Lean.

---

## Superseded: the two-regime route (kept as a record)

### Claim

`TwistedSiegelWalfisz` follows from two inputs that carry no cutoff at all:

- **(SW)** Siegel–Walfisz for a nonprincipal character `ψ` mod `m`: for all `A₁, B₁` there is `C`
  with `|Σ_{p≤u} ψ(p)| ≤ C u/(log u)^{A₁}` whenever `m ≤ (log u)^{B₁}`.  A theorem.
- **(TSW∞)** the `y = ∞` case: `|Σ_{m≤X} z^{Ω_P(m)} χ(m)| ≤ C X/(log X)^{A₁}` for `χ ≠ 1` mod
  `r ≤ (log X)^{B₁}`, `(r, q₀) = 1`, with `C = C(q₀, a, z, A₁, B₁)`.

The cutoff enters only through elementary bookkeeping: for small y the twist by χ is killed by
the trivial character-sum bound, and for large y the y-truncation is a finite-shape convolution
against primes beyond y, which SW controls.  The 10-01 obstruction (`Σ_{p≤y} p^{−σ}` blowing up
on the contour) never arises, because no contour is moved after the truncation.

**Referee (Astra `223436Z`, on 43cf7e46):** the two-regime reduction to SW + TSW∞ is ACCEPTED on paper
with three bookkeeping repairs, applied below (edge cases, the `j ≥ 2` weight, empty intervals).
That verdict does not cover TSW∞ or its source.

**Confidence:** about 75% that the argument below is complete as written; the identities are
checked numerically on finite cases (below).  TSW∞ itself reduces to SW + Granville–Koukoulopoulos Thm 1 (see "Inputs"),
so the whole of TSW rests on SW and GK.

## Notation

`P = {p prime : p ≡ a (q₀)}`, `g_y(n) = z^{Ω_{P,≤y}(n)}` (the Lean `omegaMultLe`, multiplicity
counted), `S = S(x, y) = Σ_{n≤x} g_y(n) χ(n)`, `L = log x`, `K = K(A, B)` a large constant fixed
below.

**Edge cases first** (repair 1, Astra `223436Z`): if `y ≤ 1` then `g_y = 1` and `|S| ≤ r`; if
`y ≥ x` then `g_y = G` on `[1, x]` and `S` is the cutoff-free sum, i.e. TSW∞ itself.  From here
on `1 < y < x`, and the two regimes are complementary:

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

Every `d ∈ D_y ∩ [1, x]` has `ω(d) ≤ L/log y < K log L`, so `|k(d)| ≤ 2^{ω(d)} ≤ L^{K log 2}`, and
(for `2 ≤ y < x`; this is where the cap `y < x` matters, since `d = 1` is always on the left)

    Σ_{d ∈ D_y, d≤x} 2^{ω(d)}/d ≤ Π_{y<p≤x} (1 + 2/(p − 1)) ≤ C (L/log y)² ≤ C (K log L)².   (★)

Put `Z = exp(√L)`.

**(i) `d ≤ x/Z`.**  Here `log(x/d) ≥ √L`, so `r ≤ L^B ≤ (log(x/d))^{2B}` and TSW∞ (with
`B₁ = 2B`) gives `|T(x/d)| ≤ C (x/d) L^{−A₁/2}`.  By (★) this part is `≤ C x (log L)² L^{−A₁/2}`;
take `A₁ = 2A + 2`.

**(ii) `d > x/Z`.**  Then `m ≤ x/d < Z`; swap the order:

    Σ_{m<Z} G(m) χ(m) [K_y(x/m) − K_y(x/Z)],   K_y(X) = Σ_{d ∈ D_y, d≤X} k(d) χ(d).

**Lemma (K).**  For `x/Z ≤ X ≤ x`: `|K_y(X)| ≤ 1 + C X (log L)^{A₃+2} L^{−A₃}`.

*Proof.*  Split `d > 1` by its largest prime `p` and that prime's exponent `j`.
- `j ≥ 2` (repair 2): bound the whole coefficient, not just the local factor.  These `d` are
  divisible by `p²` for some `p > y`; there are at most `X Σ_{p>y} p^{−2} ≤ C X/y` of them, each
  with `|k(d)| ≤ L^{K log 2}`.  The contribution is `≤ C X L^{K log 2}/y`, and
  `y > exp(L/(K log L))` beats any power of L.
- `j = 1`: `d = d′p` with `P⁺(d′) < p`, and the sum is
  `(1 − z) Σ_{d′} k(d′) χ(d′) Σ_{p ∈ P, U₁ < p ≤ U₂} χ(p)` with `U₁ = max(y, P⁺(d′))`,
  `U₂ = X/d′`.  Discard every `d′` with `U₂ ≤ U₁` (empty interval; repair 3), so the remaining
  intervals have both endpoints `≥ y`.  Expand `1_P` by characters ψ mod q₀: `χψ` is a nonprincipal character mod `r q₀`
  because `χ ≠ 1` and `(r, q₀) = 1` (imprimitive characters included).  Both endpoints are `≥ y`, so `log u ≥ L/(K log L) ≥ √L`
  and `r q₀ ≤ q₀ L^B ≤ (log u)^{2B+1}`: SW applies at each endpoint, and the prime sum is
  `≤ 2C (X/d′)(log y)^{−A₃} ≤ 2C (X/d′)(K log L / L)^{A₃}`.  Sum over `d′` with (★).  ∎

With `A₃ = A + 2`, part (ii) is `≤ 2Z + C x (log Z)(log L)^{A₃+2} L^{−A₃} ≤ 2Z + C x L^{−A−1/2}`,
and `Z = exp(√L) = o(x/L^A)`.

So in both regimes `|S| ≤ C x/L^A` with `C = C(q₀, a, z, A, B)`, uniform in `y, r, χ`.  The case
`y ≥ x` is the large regime with `D_y ∩ [1, x] = {1}`, i.e. TSW∞ itself.

## Finite numerical checks (identities only)

`tmp/opus-tsw/identities.py` (scratch, not committed): `q₀ = 5, a = 2, r = 7`, χ of order 3,
`z = e^{1.1i}`, `x ∈ {200, 777, 1500}`, `y ∈ {1, 3, 7, 13, 50, 300, 10⁹}`.  Both decompositions
reproduce `S` to `2.7·10⁻¹³`.  Red control: flipping the sign of `k` gives an error of `14.6`.
Partial sums of χ stay `≤ 1 ≤ r` up to `X = 2000`.  These check the algebra, not the asymptotics.

## Inputs, and what is owed

- **SW** is a theorem; in the repo's style it enters as a `Literature` Prop.
- **TSW∞ ⇐ SW + Granville–Koukoulopoulos Thm 1** (arXiv:1710.01389, Ramanujan J. 2019; PDF
  `~/personal/papers/granville-koukoulopoulos-2019-beyond-lsd.pdf`).  Statement read from the
  source 2026-10-11, paraphrased: if `f` is multiplicative, `|f| ≤ τ_k`, and
  `Σ_{p≤u} f(p) log p = αu + O(u/(log u)^A)` for **all** `u ≥ 2`, then `Σ_{n≤x} f(n)` equals a
  main term whose coefficients carry `1/Γ(α − j)`, plus `O(x (log x)^{k−1−A} (log log x)^{[A=J+1]})`.
  Its constants depend only on `k`, `A` and the constant in the hypothesis.  At `α = 0` every
  `1/Γ(−j)` vanishes, so the sum is `O(x (log x)^{−A}(log log x))` with `k = 1`.

  **Uniformity in `r`.**  For `f = G χ`, the hypothesis with `α = 0` is SW for `χ` and the `χψ`,
  which needs `r q₀ ≤ (log u)^{B₁}`, i.e. it fails for `u < w := exp((q₀ r)^{1/B₁})`.  So split at
  `w`: `f = f_s ∗ f*`, with `f*` equal to `f` on prime powers of `p > w` and zero on `p ≤ w`, and
  `f_s` the `w`-smooth part.  Then `Σ_{p≤u} f*(p) log p` is `0` for `u < w` and a difference of two
  SW evaluations at endpoints `≥ w` otherwise, so GK applies to `f*` with a constant uniform in
  `r, χ`.  Summing `f_s(d) F*(X/d)` over `w`-smooth `d`: `Σ 1/d ≤ C log w ≪ (log X)^{(B+1)/B₁}`
  costs a small power of log, and the `d` near `X` are `w`-smooth with
  `u = log X/log w ≥ (log X)^{1−(B+1)/B₁}`, so `Ψ(X, w)` is far below any `X/(log X)^A`.  This is the
  small-y bookkeeping again, with `w` in place of `y`.  The only analytic inputs are SW and GK.
  TSW∞ is therefore a derived statement, not a new citation.  (Tenenbaum II.5 + Siegel is the
  classical route; not needed.)
- Owed before Lean: the referee's check of the two regimes and of the `w`-split above.

## Consequence for the ledger

If accepted, E3's "inherited and still owed: TSW's uniformity in y" becomes "TSW ⇐ SW + TSW∞",
and with the `w`-split, TSW ⇐ SW + GK Thm 1: the ledger's open analytic node becomes two cited
theorems plus elementary bookkeeping.
