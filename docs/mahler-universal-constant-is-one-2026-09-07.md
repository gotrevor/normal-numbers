# The universal Mahler constant is `1` — `sup_g M(g,1)/g²` is **not** bounded away from `1` 🎯

Architect session, 2026-09-07.  Answers the open question posed in
`ARCHITECT-2026-09-07-treadmills-and-mahler.md` §2(a).

## BLUF

**`sup_g M(g,1)/g² = 1`.**  The supremum is approached but never attained, and
the bases that approach it are explicit.  Consequently this repo's own
`Mahler.mahler_multiplier_lt` (`M(g,k) < g^(k+1)`, Berend–Boshernitzan's open
question of p. 320, answered here 2026-09-02) is **asymptotically sharp at
`k = 1`**: the constant `1` cannot be lowered.  The "sharp universal constant"
wing named in the handoff is therefore **closed** — there is no `c < 1` to chase.

The previous record `0.840` at `g = 18` was not near the ceiling; it was the
*third rung of a ladder*.  Explicit bases reach `0.9905` (`g = 630`) and
`0.99973` (`g = 26250`).

## The closed form

For the background+burst family with background digit `a = 0` and burst `B`
(`α = B · Σ g^(−i!)`, the family of `MahlerLowerBoundBackground.lean`), target
digit `w = g − 1`:

> **Blocking lemma.**  Digit `g − 1` is absent from position `i` of `m·B` for
> every `i < j` and every `m`  ⟺  `gcd(B, g^j) > g^(j−1)`.

Taking `B = c` a **divisor of `g^j` with `c > g^(j−1)`**, the products `m·c`
climb monotonically through the multiples of `c`, so digit `g − 1` first appears
at position `j` at `m* = ⌈(g−1)·g^j / c⌉`.  Writing `δ = c/g^(j−1) > 1`:

    M(g,1)  ≥  m*  =  ⌈ (g−1)·g / δ ⌉ ,        ratio = (g−1)/(g·δ).

Maximising over `j` and `c` leaves a purely multiplicative quantity:

> **δ\*(g) = min { ∏_{p|g} p^(u_p)  :  u_p ∈ ℤ, u_p ≤ v_p(g), product > 1 }**
>
> **M(g,1) ≥ (g−1)·g / δ\*(g).**

The `u_p` may be arbitrarily negative (take `j` large); only the *positive*
exponents are capped, by the multiplicity of `p` in `g`.  Note `δ\*(g) = p` when
`g = p^e`, which is why prime and prime-power bases are stuck near `1/p`.

## Why the supremum is 1

`δ\*(g)` can be pushed arbitrarily close to `1`.  `log 2 / log 3` is irrational,
so `{a·log 2 + b·log 3 : a,b ∈ ℤ}` is dense in `ℝ`: given `ε > 0` pick integers
`a, b` with `1 < 2^a·3^b < 1 + ε`, and set `g = 2^max(a,1)·3^max(b,1)`.  Then
`δ\*(g) ≤ 2^a 3^b < 1 + ε` and

    M(g,1)/g²  ≥  (g−1) / (g·(1+ε))  →  1.

Combined with `mahler_multiplier_lt` (`M(g,1) < g²`), the supremum is exactly
`1` and is not attained.

The record-holders are the **superparticular smooth ratios** — the commas of
music theory.  An **exhaustive** scan of every 13-smooth `g ≤ 60000` with two or
more prime factors gives the record ladder below; it climbs monotonically to
`0.99975` with no plateau, which is the shape of a supremum of `1`:

| `g` | `δ\*` | relation | ratio bound |
|---|---|---|---|
| 6 | `3/2` | `3/2` | 0.5556 |
| 10 | `5/4` | `5/2²` | 0.7200 |
| 18 | `9/8` | `3²/2³` | 0.8395 |
| 30 | `10/9` | `2·5/3²` | 0.8700 |
| 54 | `9/8` | `3²/2³` | 0.8724 |
| 60 | `10/9` | `2·5/3²` | 0.8850 |
| 66 | `33/32` | `3·11/2⁵` | 0.9550 |
| 130 | `65/64` | `5·13/2⁶` | 0.9770 |
| 390 | `65/64` | `5·13/2⁶` | 0.9821 |
| 630 | `126/125` | `2·3²·7/5³` | 0.9905 |
| 1890 | `126/125` | `2·3²·7/5³` | 0.9915 |
| 1950 | `325/324` | `5²·13/(2²·3⁴)` | 0.9964 |
| 2310 | `385/384` | `5·7·11/(2⁷·3)` | 0.9970 |
| 9240 | `385/384` | `5·7·11/(2⁷·3)` | 0.9973 |
| 10010 | `1001/1000` | `7·11·13/(2³·5³)` | 0.9989 |
| 26250 | `4375/4374` | `5⁴·7/(2·3⁷)` | 0.99973 |
| 52500 | `4375/4374` | `5⁴·7/(2·3⁷)` | 0.99975 |

Two rungs to note: `810` (`81/80`, the syntonic comma, 0.9864) and `360150`
(`2401/2400`, 0.99958) are *not* records only because a smaller `g` already beat
them; both are genuine members of the family.


## Evidence 🔬

Three instruments, agreeing.  **Computation tier throughout — no Lean.**

1. **Against the exact census** (`mahler_exact_M.py`, `g = 2…32`): the closed
   form `(g−1)g/δ\*(g)` **never exceeds** the exact `M(g,1)`, and equals it at
   `g = 2, 3, 4, 6, 8, 9, 10, 12, 14, 15, 16, 18, 20, 22, 24, 26` — every base
   with two distinct prime factors and `δ\* < 2`, plus the prime powers.  It is
   a strict under-estimate at `21, 25, 27, 28, 32` and at primes, where `a ≠ 0`
   witnesses take over.
2. **Direct simulation**, closed form not used: least `m` whose base-`g`
   expansion of `m·B` shows digit `g−1`.
   `g = 18 → 272` (0.83951) · `g = 30 → 783` (0.87000) ·
   `g = 66 → 4160` (0.95501) · `g = 130 → 16512` (0.97704) ·
   `g = 630 → 393125` (0.99049) · `g = 810 → 647200` (0.98643) ·
   `g = 2310 → 5319936` (0.996971, a brute-force scan of 5.3 M multipliers).
   All seven match the closed form exactly.  The last three bases were chosen by
   the exhaustive scan, not by hand, so they are an unbiased test of it.
3. **Exact automaton, independent algorithm**: `M_W(30, 1, W = 29) = 783`
   (141 s, SCC trimmed-product).  Predicted 783.  ⚠️ This is `M_W` for one
   digit; `M(30,1) = max_W M_W ≥ 783`.

⚠️ **What is not established.**  That `M(g,1) = (g−1)g/δ\*(g)` — the 16 exact
agreements make it a strong conjecture, not a theorem, and it is *false-shaped*
at `g = 21, 27, 28, 32` where the true value is larger.  Only the **lower
bound** is claimed, and only on the digit-model of the burst family that
`mahler_universal_screen.py` validates against the exact algorithm.

## What this changes

- 🛑 The hunt for a universal constant `c < 1` is **over**; do not spend
  treadmill laps on it.
- 📌 The residual question is the *rate*: `1 − M(g,1)/g²` as a function of `g`.
  By the ladder it is governed by how well `g`'s prime support approximates `1`
  multiplicatively — a Størmer / linear-forms-in-logarithms question, and a
  genuinely stateable target.
- 🔍 The interesting remaining gap is the **other** direction: `21, 27, 28, 32`
  show the `a = 0` burst family is not optimal at prime powers and at `g` with
  large `δ\*`.  The construction that beats it there is still unidentified, and
  is the same "construction this repo does not have" that the `g = 32`
  refutation named.
