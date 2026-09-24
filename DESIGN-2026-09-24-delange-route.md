# Route analysis for the Leaf-B Delange slot (2026-09-24)

Target: `S(N) = ∑_{n≤N} z^{ω_{>P}(n)} = o(N)` for `|z| = 1`, `z ≠ 1` (hence `Re z < 1`), then the
`e(jm/Q)`-twisted version.

## 0. Probe (probes/delange_slot.py, N = 10^6)

`|S(N)|/N` vs the Euler prediction `∏_{P<p≤N}(1 + (z-1)/p)`:

| P | θ (z = e^{iθ}) | \|mean\| | \|∏\| | ratio |
|---|---|---|---|---|
| 1 | π/2 | 0.271 | 0.068 | 3.97 |
| 5 | π/2 | 0.517 | 0.157 | 3.29 |
| 100 | π | 0.609 | 0.114 | 5.35 |
| 5 | 0.3 | 0.977 | 0.923 | 1.06 |

Ratio is `O(1)` and θ-dependent — exactly the Selberg–Delange constant `1/Γ(z)`-shape.  Decay is
`(log N)^{Re z - 1}`, i.e. *brutally* slow: at `N = 10^6`, `(log N)^{-1} ≈ 0.07`.  Twisted means
(second block of the probe) are uniformly **smaller** than untwisted, as expected: the additive
twist contributes its own cancellation on top.  Nothing here contradicts the statements; they are
true but with no power saving, so no `native_decide` anchor can certify them.

## 1. The Levin–Fainleib backbone (now formalized, exact, sorry-free)

`DelangeSlotIdentity.lean` proves with no analysis at all:

    ∑_{n≤N} h(n) log n  =  ∑_{d≤N} Λ(d) · ∑_{m≤N/d} h(d·m)                     (sum_hfun_mul_log)

and, for `d = p^j`,

    ∑_{m≤X} h(p^j m) = z·S(X) − (z−1)·T_p(X)   (p > P),     = S(X)   (p ≤ P),

where `T_p(X) = ∑_{m≤X, p∣m} h(m)` obeys `‖T_p(X)‖ ≤ X/p`.  Chaining:

    ∑_{n≤N} h(n) log n = z ∑_{d≤N} Λ(d) S(N/d) + E(N),
    ‖E(N)‖ ≤ 2 ∑_{p^j≤N} Λ(p^j)·(N/(p^j·p))  +  2 ∑_{p≤P, p^j≤N} Λ(p^j)·(N/p^j)  =  O_P(N).

(The first piece converges because `∑_p log p / p^2 < ∞`; the second is `O_P(N)` because **P is
fixed** — this is where "f(p)=z is constant on primes > P" is spent.)

Partial summation turns the left side into `S(N) log N − ∫_1^N S(t) dt/t`, and `‖∫‖ ≤ N`.  With
`u = log N`, `σ̃(w) = e^{-w} S(e^w)` (so `‖σ̃‖ ≤ 1`):

    u·σ̃(u) = z ∑_{d≤N} (Λ(d)/d) σ̃(u − log d) + O_P(1).                            (LF)

## 2. Why (LF) does not close by itself — the identified crux

If the Λ-measure could be replaced by Lebesgue, (LF) reads `uσ̃(u) = z∫_0^u σ̃ + O(1)`; setting
`Φ = ∫σ̃` gives `uΦ' = zΦ + O(1)`, so `(u^{-z}Φ)' = u^{-z-1}O(1)`, whence `|Φ(u)| ≪ u^{Re z} + log u`
and `|σ̃(u)| ≪ u^{Re z − 1} + (log u)/u → 0` **for every `Re z < 1`**, both signs of `Re z`.  That is
a complete proof of rung 1 — modulo the replacement.

The replacement costs a Stieltjes error `O(1)·Var_{[0,u]}(σ̃)`, and only `Var(σ̃) ≤ 2u` is free,
giving `O(u)` — which swamps the equation.  **This is the crux.**  Restating it:

> **CRUX-LF.**  `∑_{d≤N} (Λ(d)/d)·σ̃(u − log d) = ∫_0^u σ̃(w) dw + O(1)`, or any substitute that
> keeps the `O(1)` error while retaining the phase of `σ̃` (an inequality on `|σ̃|` is useless: it
> only yields `|σ̃| ≲ 1`).

Sub-routes to CRUX-LF, in order of current preference:

* **(i) Iterate.**  Apply (LF) twice; the double Λ-convolution smooths `σ̃` and the Selberg
  symmetry formula `∑Λ(d)Λ(e)` may absorb the fluctuation.  Untested.
* **(ii) Use PNT with a rate.**  `ψ(x) = x + O(x e^{-c(log x)^{1/10}})` (PNTAnd `MediumPNT`) turns
  the Λ-sum into an integral *if* we can afford the tail `d` near `N`; naive splitting loses
  `N log N`.  Needs the tail handled by the trivial `‖σ̃‖≤1` on a *short* range only — plausible
  with the `e^{-c(log)^{1/10}}` saving down to `d ≤ N/exp((log N)^{1/2})` and Mertens for the rest.
  ⇒ the rest is `∑_{N/Y<d≤N} Λ(d)/d = O(log Y/log N)`... still `O(1)` only when `Y ≤ N^{o(1)}`.
  **Worth a careful bookkeeping pass: this may already be enough.**
* **(iii) Analytic (Selberg–Delange proper).**  `F(s) = ζ(s)^z G(s)` with `G` holomorphic and
  Euler-absolutely-convergent on `Re s > 1/2`; then a **Newman contour with an integrable boundary
  singularity** `|F(s)| ≪ |s−1|^{-Re z}`, `Re z < 1`, gives `∫_1^∞ S(x)x^{-2}dx` convergent, and
  slow oscillation (`|S(x)−S(y)| ≤ |x−y|`) upgrades that to `S(x) = o(x)`.  Inputs available in
  mathlib: `riemannZeta` continuation, `riemannZeta_ne_zero_of_one_le_re`,
  `riemannZeta_residue_one`, `DirichletCharacter.LFunction_ne_zero_of_re_eq_one`.  Cost: build
  `ζ^z` on a simply-connected neighbourhood of `{Re s ≥ 1} \ {1}` + the Euler product for `G` +
  Newman's contour lemma.  Large but every step standard.

## 3. The twist (rung 2)

Additive twist is not multiplicative, so (LF) does not apply directly.  Plan of record: split
`m = s·t` into `P`-smooth × `P`-rough, note the twist only sees `m mod Q`, expand the indicator of
each residue class of `t` mod `Q' | Q` in Dirichlet characters, and run rung-1 machinery on
`t ↦ χ(t) z^{ω(t)}` — a multiplicative function with value `zχ(p)` at `p > P`.  In route (iii) this
is literally `L(s,χ)^z`; in route (i)/(ii) the Λ-identity holds verbatim with `h` replaced by
`χ·h`, and the `χ`-sum over `d ≤ N` is `O(1)` for `χ ≠ χ₀` by Pólya–Vinogradov-free partial
summation.  **Do rung 1 first.**

## Next attack

Bookkeep sub-route (ii) precisely (a half-page of sums) before spending a lap on (iii); if the
`N/Y < d ≤ N` tail really is `O(1)`, rung 1 closes on top of a ported `MediumPNT` and the already-
proved exact identity.
