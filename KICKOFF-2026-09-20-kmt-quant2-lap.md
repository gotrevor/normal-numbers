# KICKOFF 2026-09-20 — two-constant `KMT_quant₂` (re-freeze; the FL constant must not be assumed o(4^k))

Branch `wip/g5-prime-subset`.  Engine Opus/low.  Why: `papers/kmt-2023-prop43-k-dependence.md` — the
frozen `KMT_quant C` puts one constant on all three terms, so `hgrow` silently demands
`log C_FL(k) = o(4^k)` for the fundamental-lemma constant, which is unverified.  Two constants fix it.
File: `src/NormalNumbers/G4WiringSparse.lean`.  **Do not change any existing statement**; add new ones.

## The ratified new statements (verbatim; only their proofs are yours)

```lean
/-- Two-constant form of `KMT_quant`: `C₁` on the distance terms, `C₂` on the sieve/truncation term
(KMT 2023 (4.7), (4.20), (4.22)); see `papers/kmt-2023-prop43-k-dependence.md`. -/
def KMT_quant₂ (C₁ C₂ : ℕ → ℝ) : Prop :=
  ∀ (S : ℕ → Prop) [DecidablePred S] (J : ℕ) (h : ℤ), h ≠ 0 → NontrivialWindow J h →
    ∀ x : ℕ, 3 ≤ x → ∀ ε : ℝ, 1 / Real.log (Real.log x) < ε → ε < 1 / 2 →
      ‖windowMeanS S J h x‖ ≤ C₁ J *
        (Real.sqrt (Real.log (1 / ε)) * Real.sqrt (2 * recipSumIoc S ⌊(x : ℝ) ^ ε⌋₊ x)
          + Real.exp (- recipSumLe S ⌊(x : ℝ) ^ ε⌋₊))
        + C₂ J * Real.exp (- 1 / (8 * (J : ℝ) ^ 2 * ε))

theorem KMT_quant₂_of_KMT_quant (C : ℕ → ℝ) (h : KMT_quant C) : KMT_quant₂ C C

theorem exists_sparse_normal_of_KMT_quant₂ (C₁ C₂ : ℕ → ℝ)
    (h₁ : Tendsto (fun k : ℕ => Real.log (C₁ k) / 4 ^ k) atTop (𝓝 0))
    (h₂ : Tendsto (fun k : ℕ => Real.log (Real.log (C₂ k)) / 4 ^ k) atTop (𝓝 0))
    (hKMT : KMT_quant₂ C₁ C₂) :
    ∃ (S : ℕ → Prop) (_ : DecidablePred S), DivergentRecip S ∧ IsNormal 4 (subsetLambert S 4)
```

## Leaves, in order (commit a compiling skeleton with named sorries FIRST)

1. `KMT_quant₂_of_KMT_quant`: distribute `C J * (a + b + c) = C J * (a + b) + C J * c`.
2. `structure Good₂ (C₁ C₂ : ℕ → ℝ) : Prop` — copy `Good` with the `terms` field split:
   `terms₁ : Tendsto (fun i => C₁ (D.J i) * (√(log(1/εᵢ))·√(2(δᵢ₋₁+δᵢ)) + exp(−∑_{i'<i−1} δᵢ'))) atTop (𝓝 0)`,
   `terms₂ : Tendsto (fun i => C₂ (D.J i) * exp(−1/(8 Jᵢ² εᵢ))) atTop (𝓝 0)`; keep `sep` with `1 ≤ i`.
3. `BlockData.kmt_along₂ (hKMT : KMT_quant₂ C₁ C₂) (hG : D.Good₂ C₁ C₂) : KMT_along D.set D.sched` —
   copy `kmt_along`'s proof; the bound splits the same way.
4. `exists_good₂ (C₁ C₂) (h₁) (h₂) : ∃ D : BlockData, D.Good₂ C₁ C₂` — reuse `namespace GoodExists`
   with the schedule `JF₂ C₁ C₂ i := Nat.findGreatest (fun J => ∀ J' ≤ J, |C₁ J'| ≤ i^{1/4} ∧ Real.log |C₂ J'| ≤ i/2) i`.
   All fields except `terms₂` and `log_o_pow` are unchanged (same `εᵢ = 1/(8(i+3)³)`, `XF`, `blk`).
   `terms₂`: `|C₂(Jᵢ)| ≤ exp(i/2)` and `1/(8Jᵢ²εᵢ) = (i+3)³/Jᵢ² ≥ i`, so the term is `≤ exp(−i/2)`.
   `log_o_pow`: by maximality at `Jᵢ+1` either `|C₁(Jᵢ+1)| > i^{1/4}` (old argument via `h₁`) or
   `log|C₂(Jᵢ+1)| > i/2` (then `log i < log 2 + log log|C₂(Jᵢ+1)|`, and `h₂` gives `o(4^{Jᵢ+1})`);
   the degenerate `Jᵢ = i` branch as before.  Real.log is `log |·|` in Mathlib — keep the `|·|`.
5. Assemble `exists_sparse_normal_of_KMT_quant₂` exactly as `exists_sparse_normal_of_KMT_quant'`.
6. `#print axioms` of the new theorem must be `[propext, Classical.choice, Quot.sound]`; the file stays
   sorry-free.  `box done --green` only then.  Write `HANDOFF-2026-09-20-kmt-quant2.md`.

Do not touch `G4WiringCRT.lean`, `DyadicToPrefix.lean`, `WeylCriterion.lean`.  Report the advance, not the
sorry count.  If a leaf costs more than ~40 minutes, commit what compiles with a named sorry and say which.
