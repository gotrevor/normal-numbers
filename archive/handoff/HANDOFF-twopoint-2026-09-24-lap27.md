# HANDOFF twopoint lap 27 — 2026-09-24

Branch `wip/twopoint-avg`.  Full build 🟢 green (9285 jobs).  New file
`src/NormalNumbers/TwoPointDelange.lean`, **sorry-free**, all declarations trust-triple.

## Where the chain stands

`ConjC1` ⟸ Delange + `MultiElliott` (`conjC1_of_delange_multiElliott`, lap 25), with the Kátai/BSZ
step a theorem and the small-prime half of leaf (D) a theorem (lap 26).  `MultiElliott` is the 🔴
open leaf — cited, not chippable.  So the only *dischargeable* input is the 🟡 `DelangeMean`, and
this lap attacks it.

## The advance — the elementary skeleton of Delange, sorry-free

With `z = e(t)` a `b`-th root of unity `≠ 1` (so `Re z < 1`):

| landed | content |
|---|---|
| `delangeKernel z n` | `h_z = μ * z^ω`: `(z−1)^{ω(n)}` on squarefree `n`, `0` otherwise |
| **`sum_delangeKernel_divisors`** | `Σ_{n ∣ m} h_z(n) = z^{ω(m)}` — the squarefree divisors of `m` are the products of subsets of `m.primeFactors`, so the sum is the powerset expansion of `((z−1)+1)^{ω(m)}` |
| **`sum_zpow_omega_eq`** | hyperbola summation: `Σ_{m ≤ N} z^{ω(m)} = Σ_{n ≤ N} h_z(n)·⌊N/n⌋`, EXACT |
| **`norm_delangeLocal_sq`** | `‖1 + (z−1)r‖² = 1 − 2(1 − Re z)(r − r²)` — an EQUALITY, not an estimate |
| `norm_delangeLocal_le` | hence `‖1 + (z−1)/p‖ ≤ 1 − (1−Re z)/(2p)` for `p ≥ 2` |
| **`prod_delangeLocal_tendsto_zero`** | `‖Π_{p ≤ P}(1+(z−1)/p)‖ → 0`, via the repo's `prod_tendsto_zero_of_norm_le` — the same Mertens engine as leaf (M) |
| **`delangeMean_of_kernel`** | `DelangeKernelMean z` + `DelangeKernelTail z` ⇒ `DelangeMean t` |

The assembly: `⌊N/n⌋/N = 1/n − δ_n/N` with `δ_n ∈ [0,1)` (`cast_div_le`, `sub_one_le_cast_div` from
`TwoPointTuranKubilius.lean`), so
`|E_{m≤N} z^{ω(m)}| ≤ ‖Σ_{n≤N} h_z(n)/n‖ + (1/N)Σ_{n≤N}‖h_z(n)‖`.

## The debt, now two named `Prop`s (nothing faked, no `sorry`)

1. **`DelangeKernelMean z`** : `Σ_{n≤N} h_z(n)/n → 0`.  The *Euler-product* version is now a
   theorem; the gap is a Wirsing/Levin–Fainleib comparison between a truncated multiplicative sum
   and its product.
2. **`DelangeKernelTail z`** : `Σ_{n≤N} μ²(n)‖z−1‖^{ω(n)} = o(N)`.  **TRUE exactly when
   `‖z−1‖ < 1`**, and then elementary: `w^{ω(n)} ≤ w^K + [ω(n) ≤ K]` for `w < 1`, and
   `#{n ≤ N : ω(n) ≤ K} = o(N)` follows from `turanKubilius` (already in kernel).  For
   `‖z−1‖ ≥ 1` it FAILS, and the route must become Halász / Selberg–Delange over the zero-free
   region — `src/PNTPort/` is a sorry-free quantitative-PNT port with `ZetaNoZerosOn1Line`,
   `ZetaZeroFree9`, `MediumPNT`, plus Mellin/contour machinery, so that is available but is a
   multi-lap contour project.

## Next session — start here

1. **Close `DelangeKernelTail` for `‖z−1‖ < 1`** from `turanKubilius`.  Concretely: for `w < 1` and
   any `K`, `Σ_{n≤N} w^{ω(n)} ≤ N w^K + #{n ≤ N : ω(n) ≤ K}`, and Chebyshev on
   `Σ_{n ≤ N}(ω_w(n) − L(w))²  ≤ 2 N L(w)` gives `#{n≤N : ω(n) ≤ K} = o(N)` (choose the truncation
   level `w` in `kataiOmega` so that `L(w) → ∞` slowly).  Watch the gap between `kataiOmega w n`
   (primes `≤ w` only) and `omegaNat n` — `kataiOmega w n ≤ omegaNat n`, which is the direction
   needed.
2. Then `DelangeKernelMean` for the same range (truncated sum vs Euler product).
3. Together those give `DelangeMean t` unconditionally for `‖t‖_{ℝ/ℤ} < 1/6` — a genuine partial
   discharge of the 🟡 axiom.  The remaining `t` need the `PNTPort` contour route.
4. Do NOT re-attack anything on the refuted list (laps 13–26; see `PENDING_WORK.md`).

**Rules honoured.**  `twoPointWeightedAvg_all` untouched.  No edits to `PairDecouple*.lean`,
`SwingC1*.lean`, `CastingOut*.lean`, `Maze.lean`, `papers/`, `agent-mail/`, other KICKOFFs.  All new
code in `src/NormalNumbers/TwoPoint*.lean`; `src/` sorry count unchanged.

## Confidence at lap 27
- `DelangeKernelTail` for `‖z−1‖ < 1` closable in 1–2 laps: **70%**.
- `DelangeKernelMean` for `‖z−1‖ < 1` closable in 2–4 laps: **45%**.
- Full `DelangeMean` (all `t`) from `PNTPort` within this run: **10%**.
