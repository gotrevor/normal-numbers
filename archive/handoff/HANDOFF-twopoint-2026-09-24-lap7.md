# HANDOFF twopoint lap 7 — the decisive step of the correction is now kernel-checked

## Crux
`twoPointWeightedAvg_all` still `sorry`.  Laps 4–6's finding (the averaged Kátai criterion
overstates BSZ/Kátai) rested on a hand derivation of the constants.  Lap 7 removes the hand.

## Advance — `src/NormalNumbers/TwoPointKataiCS.lean` (no `sorry`, axiom-clean)

**`katai_cauchySchwarz`**, for `‖u p‖ ≤ 1`, `‖g m‖ ≤ 1`, arbitrary `C : ℕ → ℕ → ℂ`:

    ‖Σ_{p ∈ A} u p · Σ_{m<N} g m · C p m‖²
      ≤ N · ( Σ_{p ∈ A} Σ_{m<N} ‖C p m‖²  +  Σ_{p ≠ q ∈ A} ‖Σ_{m<N} C p m conj(C q m)‖ ) .

Proof route, all formalized: interchange the `p`/`m` order; `ℓ¹` bound by `‖g‖ ≤ 1`;
`sq_sum_le_card_mul_sum_sq` for `ℓ¹ → ℓ²`; then `sum_sq_superposition` — the inner square is
exactly the Gram sum `Σ_{p,q} u_p conj(u_q) · ⟨C_p, C_q⟩` — split into diagonal and off-diagonal.

**Why this settles the run's claim.**  Instantiating `C p m = a(pm)·1_{pm<N}` makes the first
bracketed term `Σ_{p≤w} #{m : pm < N} = Σ_{p≤w} N/p = N·L(w)`.  That is the term that forces the
`L(w)²` denominator on the pair sum.  There is no way to rescale it into `π(w)²`: the diagonal
counts `1/p`, not `1`.  So `KataiQuantSharp`'s shape is the correct one and `KataiQuant`'s (and
hence `KataiOrthogonalityAvg`'s quantifier order) is not — now machine-checked at the step that
decides it, rather than asserted.

## State of the development
- Honest chain (lap 6): `conjC1_of_delange_kataiQuantSharp_pairSumSmall` — `ConjC1` from Delange
  + `KataiQuantSharp` + the single open leaf `TwoPointPairSumSmall`.
- `KataiQuantSharp` remaining obligations, in order:
  1. **Turán–Kubilius**: `E_{n<N} (ω_w(n) − L(w))² ≪ L(w)` for `w² ≤ N`.  ← next
  2. **Rearrangement**: `Σ_{n<N} ω_w(n) f(n)a(n) = Σ_{p≤w} Σ_{pm<N} f(pm)a(pm)` (exact).
  3. **Multiplicativity + `p ∣ m` error**: `f(pm) = f(p)f(m)` off a set of size `Σ_p N/p² ≪ N`.
  4. Assemble with `katai_cauchySchwarz`.  ← DONE this lap

## Confidence
- `twoPointWeightedAvg_all` TRUE: **88%**.
- It suffices for C1 via a correctly-cited Kátai step: **5%** (down from 8%: the obstruction's
  decisive step is now kernel-checked).
- `KataiQuantSharp` itself provable in Lean over the next several laps: **60%** — it is textbook
  mathematics; items 1–3 are counting and rearrangement, no new ideas.

## Next (lap 8)
Turán–Kubilius: `Σ_{n<N} (ω_w(n) − L(w))² ≪ N·L(w)` for `w² ≤ N`.  Expand the square; the cross
terms need `#{n<N : p ∣ n} = N/p + O(1)` and `#{n<N : pq ∣ n} = N/pq + O(1)`, both elementary
(`Nat.card_multiples`-style counting; `PairDecoupleMertens.card_filter_dvd_le/_ge` already have
the one-prime case with explicit error terms).
