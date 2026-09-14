# G4: independent checks of lap route deviations

*Ren (host session), 2026-09-14.  Written, deliberately not committed while laps are live — the
next lap may sweep it in.  These are checks of decisions the laps made that depart from the brief;
each is re-derived here rather than taken from the lap's own docstring.*

## 1. Ellipsoid bound replacing the zonotope / Cauchy–Binet step (`aac6cf2`, `G4Ellipsoid.lean`)

**Deviation.**  The brief's §4B routes the neighborhood volume through Cauchy–Binet and the
zonotope volume formula:

    vol(η[A_G, I_g][-1,1]^{H+g}) ≤ (2η)^g √( C(H+g, g) · det(I + A_G A_Gᵀ) )

The lap instead uses: the sup-cube lies in the Euclidean ball of radius √(H+g); the ball maps into
`C(ball)` for `C = √(LLᵀ)`; `C` scales volume by `det C = √det(LLᵀ)`; and a Euclidean `g`-ball of
radius `R` has volume at most `(√(2πe/g)·R)^g` (Gaussian comparison, no Γ needed):

    vol(L''cube) ≤ √det(L Lᵀ) · (√(2πe/g) · √(H+g))^g

**Is this the forbidden move?**  No.  The brief's prohibition is on bounding the zonotope by a
**coordinatewise box**, which discards `det(I + A_G A_Gᵀ)` entirely.  The ellipsoid route keeps
that determinant — it is the whole content of the bound.  What it loses is only the constant in
the shape comparison (ball vs. zonotope).

**How much is lost.**  Taking logs and cancelling the common `√det`, with
`½ log C(H+g,g) ≤ (g/2) log(e(H+g)/g)`:

    zonotope   g·log(2η) + (g/2)·log(e(H+g)/g)
    ellipsoid  g·log η   + (g/2)·log(2π) + (g/2)·log(e(H+g)/g)
    ─────────────────────────────────────────────────────────
    ellipsoid − zonotope = (g/2)·log(2π) − g·log 2
                         = g·(0.91894 − 0.69315) = 0.2258·g

i.e. a factor `e^{0.226 g} = (π/2)^{g/2} ≈ 1.253^g`.

**Verdict: absorbed, the route is sound.**  With `g ≤ H` the loss is `exp(O(H))`, and the draft's
neighborhood budget is `η^{(1−ε)r − d'H} · exp(O(H + r√K))`, whose `r√K` term dominates `O(H)`.
The tube volume still tends to zero.

⚠️ What this check does **not** cover: it assumes `g ≤ H` (the lap's docstring states this as the
application condition).  If a later lap applies the bound with `g` comparable to `r` rather than
`H`, re-run this arithmetic — `exp(0.226 r)` against `exp(O(r√K))` is still fine, but the margin
should be stated, not assumed.

### 1a. Sibling trap the lap found on its own (`5cedf00` handoff)

The lap records a *second*, sharper constraint that §1 above does not cover: bounding the
**ball's volume** by its enclosing sup-cube — `vol(ball_R) ≤ (2R)^g` instead of the Gaussian
comparison `(√(2πe/g)·R)^g` — loses a factor

    (2 / √(2πe/g))^g = (2√(g/(2πe)))^g = exp(Θ(g log g))

which is **not** absorbed by `exp(O(H + r√K))` and would break the budget.  So the Gaussian
comparison is load-bearing, not a convenience.  Independently consistent with §1: the ball→cube
step is the expensive one, the cube→ball step (§1) is the cheap one.  Both directions are now
checked.

## 2. Status claim audit: "all §4B inputs proved" (`5cedf00`)

**Accurate, and not inflated.**  The handoff claims the *inputs* of §4B are proved and lists
`PropB` itself as still open under "Open", along with `PropA`–`PropD`, `PropJackson`, and the §5
schedule.  The conditional wiring theorem's hypotheses are therefore still hypotheses; nothing
has been promoted.  Verified by reading the handoff's own Open section, not the commit subject.

## 3. C3core eliminated — the Shiu-type exponential moment is not needed (`7ea8696`)

**Deviation, in the good direction.**  The brief (§4C) states that "the growing-array moment and
exponential-moment bounds still need proofs", and lap 3 identified the hard half as `C3core`:
`𝔼(1+2λ)^{V(n)}` over the sample, a Shiu-type exponential moment for the active-prime count.
That is a project-scale sieve theorem and is not in mathlib.

The lap replaced it with a degree-`M` polynomial bound, making every term a CRT-transferable
`M`-tuple indicator product on modulus `≤ R^M ≤ X^{1/20}`.  Two inequalities carry it, both
re-derived here:

    (1 + 2θ)^V ≤ e^M        at θ = M/(2V)      since (1 + M/V)^V ≤ e^M          ✓
    k^M ≤ (M/λ)^M · e^{λk}  from (λk)^M/M! ≤ e^{λk}  (one term of the series)
                            and M! ≤ M^M                                        ✓

**Verdict: sound, and it removes an external dependency rather than adding one.**  C3 reduced to
`CRTInput` alone, proved at `c00bc38` as `crt_input` (two-modulus CRT sum factorisation, exact
class counts).  No sieve theorem enters the route at any point.

⚠️ What to re-check at assembly: the non-CRT error terms are claimed `exp(−Θ(M))` with
`M ≍ C·kL`, `C ≥ 10⁴`, against a main term `exp(−cL8^{−K})`.  That comparison has been done on
paper only.  It is the natural place for the eliminated exponential moment to reappear as a
hidden constant, so it wants a Lean-side or hand check before `PropC` is called discharged.
