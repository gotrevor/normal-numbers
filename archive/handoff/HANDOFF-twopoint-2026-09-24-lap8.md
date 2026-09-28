# HANDOFF twopoint lap 8 — Turán–Kubilius proved; two of four `KataiQuantSharp` obligations done

## Crux
`twoPointWeightedAvg_all` still `sorry`.  Active work: discharging `KataiQuantSharp`, the one
cited `Prop` in the honest chain (lap 6) that genuinely IS a theorem.  Closing it leaves
`TwoPointPairSumSmall` as the chain's single open leaf.

## Advance — `src/NormalNumbers/TwoPointTuranKubilius.lean` (no `sorry`, axiom-clean)

Over `n ∈ (0, N]` both moments of `ω_w(n) = #{p ≤ w : p ∣ n}` are **exact**:

    Σ_n ω_w(n)  = Σ_{p≤w} ⌊N/p⌋ ,
    Σ_n ω_w(n)² = Σ_{p≠q≤w} ⌊N/pq⌋ + Σ_{p≤w} ⌊N/p⌋ ,

the second because distinct primes are coprime (`joint_count_eq`), both via
`Nat.Ioc_filter_dvd_card_eq_div`.  With `⌊N/p⌋ ∈ [N/p − 1, N/p]` and `Σ_{p≠q} 1/pq ≤ L(w)²` the
square expands with **no hidden constants**:

- `turanKubilius_raw` : `Σ_{n≤N} (ω_w(n) − L(w))² ≤ N·L(w) + 2·L(w)·π(w)`
- `turanKubilius`     : `≤ 2·N·L(w)` once `2π(w) ≤ N` (supplied by `w² ≤ N`, since `π(w) ≤ w`)
- `turanKubilius_abs` : `Σ_{n≤N} |ω_w(n) − L(w)| ≤ N·√(2 L(w))` — the `ℓ¹` form the argument uses

## `KataiQuantSharp` obligation board
1. ~~Turán–Kubilius variance~~ — **DONE** (lap 8).
2. **Rearrangement**: `Σ_{n≤N} ω_w(n) f(n)a(n) = Σ_{p≤w} Σ_{pm≤N} f(pm)a(pm)` — an exact double
   counting (`Finset.sum_comm` over `{(p,n) : p ≤ w, p ∣ n, n ≤ N}` reindexed by `n = pm`).  ← next
3. **Multiplicativity + error**: `f(pm) = f(p)f(m)` when `p ∤ m`; the exceptional set has size
   `Σ_{p≤w} ⌊N/p²⌋ ≤ N·Σ_p 1/p² ≤ N/2`, so it costs `O(N)` — note this is the one place the
   constant is *not* `o(N·L)`, so the `p ∣ m` term must be handled with a little care (it is
   `≤ N·Σ_{p≤w} 1/p²`, and `Σ_p 1/p² < 1/2` absolutely, so it contributes `O(N)` not `O(N·L)` —
   acceptable because the final division is by `N·L(w)` and `1/L(w) → 0`).
4. ~~Cauchy–Schwarz~~ — **DONE** (lap 7, `katai_cauchySchwarz`).

## Confidence
- `twoPointWeightedAvg_all` TRUE: **88%**; suffices for C1 via a correct Kátai step: **5%**.
- `KataiQuantSharp` fully discharged in Lean: **70%** (up from 60%; the two hardest of four
  obligations are done and both came out with clean explicit constants).

## Next (lap 9)
Obligation 2, the rearrangement.  Statement to aim at, in a new
`src/NormalNumbers/TwoPointKataiRearrange.lean`:

    ∑ n ∈ Ioc 0 N, (kataiOmega w n : ℂ) * F n
      = ∑ p ∈ primesLe w, ∑ m ∈ Ioc 0 (N / p), F (p * m)

for any `F : ℕ → ℂ`.  Proof: write `kataiOmega` as a sum of indicators, `Finset.sum_comm`, then
for each `p` reindex `{n ∈ Ioc 0 N : p ∣ n}` by `m ↦ p * m` (`Finset.sum_nbij'` or
`Finset.sum_image`) onto `Ioc 0 (N / p)`.
