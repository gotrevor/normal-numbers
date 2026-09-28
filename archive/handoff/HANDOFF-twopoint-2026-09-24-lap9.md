# HANDOFF twopoint lap 9 — all four `KataiQuantSharp` obligations are proved; assembly next

## Crux
`twoPointWeightedAvg_all` still `sorry`.  Active work: turning `KataiQuantSharp` — the one cited
`Prop` in the honest chain that genuinely IS a theorem — into kernel mathematics.

## Advance — `src/NormalNumbers/TwoPointKataiRearrange.lean` (no `sorry`, axiom-clean)

**Obligation 2, the rearrangement** (`sum_kataiOmega_mul_complex`), exact for any `F`:

    Σ_{n ≤ N} ω_w(n) · F(n)  =  Σ_{p ≤ w} Σ_{m ≤ ⌊N/p⌋} F(p·m) ,

via `sum_multiples_reindex`: `m ↦ p·m` is a bijection `(0, ⌊N/p⌋] → {n ∈ (0,N] : p ∣ n}`.

**Obligation 3, peeling multiplicativity** (`kataiMultiplicativeError`):

    ‖ Σ_p Σ_m f(pm)a(pm)  −  Σ_p f(p) Σ_m f(m)a(pm) ‖  ≤  2N ,

because `f(pm) = f(p)f(m)` off `p ∣ m`, and the exceptional set has size
`Σ_{p≤w} ⌊N/p²⌋ ≤ N · Σ_{p≤w} 1/p² ≤ N` — the last step is `sum_inv_sq_primes_le_one`, reusing
lap 5's telescoped tail bound at `K = 1`.  This is an `O(N)` term, harmless after dividing by
`N·L(w)` since `1/L(w) → 0`.

## Obligation board — all four now DONE
1. Turán–Kubilius variance — lap 8 (`turanKubilius`, `turanKubilius_abs`).
2. Rearrangement — lap 9.
3. Multiplicativity error — lap 9.
4. Cauchy–Schwarz — lap 7 (`katai_cauchySchwarz`).

## The assembly (lap 10), written out

With `M = Σ_{n≤N} f(n)a(n)` and `L = L(w)`:

    L·‖M‖ ≤ ‖Σ_n ω_w(n) f(n)a(n)‖ + ‖Σ_n (ω_w(n) − L) f(n)a(n)‖
          ≤ ‖Σ_p f(p) Σ_{m≤N/p} f(m)a(pm)‖ + 2N            (obligations 2,3)
            + N√(2L)                                        (obligation 1, ℓ¹ form)

and by obligation 4 with `u p = f p`, `g m = f m`, `C p m = a(pm)·1_{m ≤ N/p}`:

    ‖Σ_p f(p) Σ_m f(m) a(pm)‖² ≤ N·( Σ_p ⌊N/p⌋ + pairSumRaw ) ≤ N·( N·L + pairSumRaw ).

Dividing by `N²L²` and using `(x+y+z)² ≤ 3(x²+y²+z²)`:

    ‖M/N‖² ≤ 3·( 1/L + 2·pairSumRaw/(N·L²)·… + 4/L² + 2/L )  →  the `KataiQuantSharp` shape,

with `pairSum` the normalised `‖fullMean‖` version (a factor `N` apart from `pairSumRaw`).  The
one bookkeeping care point: `fullMean` sums over `range N`, the Kátai work is over `Ioc 0 N`;
they differ by the single term `n = 0`, an `O(1)` shift.

## Confidence
- `twoPointWeightedAvg_all` TRUE: **88%**; suffices for C1 via a correct Kátai step: **5%**.
- `KataiQuantSharp` fully discharged: **85%** (up from 70%; only assembly and the `range`/`Ioc`
  bookkeeping remain, no mathematics).

## Next (lap 10)
Assemble, in `src/NormalNumbers/TwoPointKataiAssemble.lean`.  Expect the constant `C` to come out
explicit (something like `C = 24`); do not tune it — any absolute constant discharges
`KataiQuantSharp` as stated.
