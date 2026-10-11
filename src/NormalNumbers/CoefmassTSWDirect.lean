/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.CPrimeSiteFactorization

/-!
# `TwistedSiegelWalfisz` from prime Siegel–Walfisz: the largest-prime transfer

The paper proof is `docs/notes/tsw-y-uniformity-2026-10-11.md`, "Primary route" (Astra
2026-10-11, checked by Opus).  It needs no cutoff-free TSW and no Selberg–Delange input.

* `Literature.PrimeCharacterSW`: Siegel–Walfisz for prime sums of a nonprincipal character, at
  moduli up to a power of `log X`.  Classical, with an ineffective constant.
* `largestPrimeTransfer`: an elementary lemma.  Let `f` be multiplicative on coprime arguments with
  `|f| ≤ 1`, and suppose every prime interval above `W` has a small sum.  Then `|Σ_{n≤X} f(n)|` is
  at most the `W`-smooth count, plus `X/(W−1)` for the `n` whose largest prime is repeated, plus
  the harmonic sum of the interval bounds.
* `smoothCount_rankin`: an elementary lemma.  At `W = ⌈exp √log X⌉`, the `W`-smooth integers up to
  `X` are fewer than `X/(log X)^A`, by Rankin and the proved Mertens bound of the
  `Erdos67b.PrimeEstimates` dependency.
* `uniformZTSW_of_primeSW`: the assembly.  On primes,
  `f(p) = χ(p)[1 + (z−1)·1_{p≡a (q₀)}·1_{p≤y}]`.  Expanding the residue-class indicator in
  characters mod `q₀` turns each interval sum into prime sums of the nonprincipal `χψ` mod `r q₀`.
  This gives a bound uniform in `z`, which is stronger than frozen `TwistedSiegelWalfisz`.
* `twistedSiegelWalfisz_of_primeSW`: the frozen target, from SW alone.

The frozen `twistedSiegelWalfisz` (no hypotheses) is unchanged.
-/

namespace NormalNumbers.Literature

/-- **Siegel–Walfisz for prime character sums** (classical; ineffective constant via Siegel's
theorem).  For every `A, B` there is `C` such that every nonprincipal `χ` mod `r ≤ (log X)^B` has
`|Σ_{p≤X} χ(p)| ≤ C X/(log X)^A`.  This is the Siegel–Walfisz theorem for `ψ(x, χ)`, moved to the
unweighted prime sum by partial summation.  ⚠️ No textbook theorem number has been checked yet;
pin one before this is upstreamed. -/
def PrimeCharacterSW : Prop :=
  ∀ A B : ℝ, 0 < A → 0 < B → ∃ C : ℝ, 0 < C ∧
    ∀ X r : ℕ, 3 ≤ X → 1 ≤ r → (r : ℝ) ≤ Real.log X ^ B →
    ∀ χ : DirichletCharacter ℂ r, χ ≠ 1 →
      ‖∑ p ∈ (Finset.Icc 1 X).filter Nat.Prime, χ (p : ZMod r)‖ ≤ C * X / Real.log X ^ A

end NormalNumbers.Literature

namespace NormalNumbers.PrimeModel.SiteFactor

open NormalNumbers.Literature

/-- `Ψ(X, W)`: the integers in `[1, X]` all of whose prime factors are at most `W` (`1` included). -/
noncomputable def smoothCount (X W : ℕ) : ℕ :=
  ((Finset.Icc 1 X).filter (fun n => ∀ p ∈ n.primeFactors, p ≤ W)).card

/-- The largest-prime transfer, as a statement. -/
def LargestPrimeTransfer : Prop :=
  ∀ f : ℕ → ℂ, (∀ n, ‖f n‖ ≤ 1) →
    (∀ a b : ℕ, Nat.Coprime a b → f (a * b) = f a * f b) →
    ∀ X W : ℕ, 3 ≤ X → 2 ≤ W → W ≤ X → ∀ η : ℝ, 0 ≤ η →
      (∀ U V : ℕ, W ≤ U → U ≤ V → V ≤ X →
        ‖∑ p ∈ (Finset.Ioc U V).filter Nat.Prime, f p‖ ≤ η * V) →
      ‖∑ n ∈ Finset.Icc 1 X, f n‖ ≤
        (smoothCount X W : ℝ) + X / ((W : ℝ) - 1) + η * X * (1 + Real.log X)

/-- Elementary; no analytic input.  Paper proof: split `n ≤ X` by its largest prime `p`.
- `p ≤ W`: `n` is counted by `smoothCount X W`.
- `p > W` and `p² ∣ n`: at most `X Σ_{p>W} p⁻² ≤ X/(W−1)` such `n`.
- Otherwise `n = m p` uniquely, with `p > max(W, P⁺(m))` and `Coprime m p`.  That block equals
  `Σ_{m ≤ X/W} f(m) Σ_{max(W,P⁺(m)) < p ≤ X/m} f(p)`.  Empty intervals are dropped; each remaining
  interval is bounded by `η X/m`, and `Σ_{m≤X} 1/m ≤ 1 + log X`.
The partition was checked exactly (`X ≤ 2500`); dropping the repeated-prime block breaks it. -/
theorem largestPrimeTransfer : LargestPrimeTransfer := sorry

/-- Smooth numbers below `exp √log X` are negligible. -/
def SmoothCountRankin : Prop :=
  ∀ A : ℝ, 0 < A → ∃ C : ℝ, 0 < C ∧ ∀ X : ℕ, 3 ≤ X →
    (smoothCount X ⌈Real.exp (Real.sqrt (Real.log X))⌉₊ : ℝ) ≤ C * X / Real.log X ^ A

/-- Elementary.  Rankin with `η = 1/log W`:
`Ψ(X, W) ≤ X^{1−η} Π_{p≤W} (1 − p^{−1+η})⁻¹`.  For `p ≤ W`, `p^η ≤ e` and `p^{−1+η} ≤ 2^{−1/2}`, so
the product is at most `exp(C Σ_{p≤W} 1/p) ≤ C′ (log W)^C` by
`Erdos67b.PrimeEstimates.abs_primeReciprocals_sub_log_log_le`.  Then
`Ψ ≤ C′ X e^{−log X/log W} (log W)^C`, and `log W ≈ √log X`, so this beats every `(log X)^{−A}`. -/
theorem smoothCount_rankin : SmoothCountRankin := sorry

/-- `TwistedSiegelWalfisz` with the constant uniform in the unit `z`. -/
def UniformZTSW : Prop :=
  ∀ q₀ a : ℕ, 3 ≤ q₀ → Nat.Coprime a q₀ → ∀ A B : ℝ, 0 < A → 0 < B →
    ∃ C : ℝ, 0 < C ∧ ∀ z : ℂ, ‖z‖ = 1 →
    ∀ x y r : ℕ, 3 ≤ x → 1 ≤ r → (r : ℝ) ≤ Real.log x ^ B → Nat.Coprime r q₀ →
    ∀ χ : DirichletCharacter ℂ r, χ ≠ 1 →
      ‖∑ n ∈ Finset.Icc 1 x, z ^ omegaMultLe (residueClass q₀ a) y n * χ (n : ZMod r)‖
        ≤ C * x / Real.log x ^ A

/-- The assembly, from SW alone.  `f(n) = z^{Ω_{P,≤y}(n)} χ(n)` is completely multiplicative with
`|f| ≤ 1`.  Apply `largestPrimeTransfer` with `W = ⌈exp √log x⌉` (large `x`; small `x` is
absorbed in `C`).  Interval sums: `f(p) = χ(p)[1 + (z−1)·1_{p≡a (q₀)}·1_{p≤y}]`.  The second
part lives on `(U, min(V, y)]`, which is dropped if empty.  For `p > W > q₀`,
`1_{p≡a} = φ(q₀)⁻¹ Σ_ψ ψ̄(a) ψ(p)`, and `χψ` is nonprincipal mod `r q₀` (CRT; `χ ≠ 1`,
`Coprime r q₀`).  Both endpoints are at least `W`, so `r q₀ ≤ q₀ (log x)^B ≤ (log t)^{2B+2}`.
`PrimeCharacterSW` with `A₁ = 2A + 4` then gives `η ≤ C (log x)^{−A−2}`.  The smooth block is
`smoothCount_rankin`, and the repeated-prime block is `x/(W−1)`. -/
theorem uniformZTSW_of_primeSW (hSW : PrimeCharacterSW) : UniformZTSW := sorry

/-- Quantifier plumbing: the uniform-in-`z` form implies the frozen statement. -/
theorem twistedSiegelWalfisz_of_uniformZ (h : UniformZTSW) : TwistedSiegelWalfisz := by
  intro q₀ a hq ha z hz A B hA hB
  obtain ⟨C, hC, hbound⟩ := h q₀ a hq ha A B hA hB
  exact ⟨C, hC, hbound z hz⟩

/-- **`TwistedSiegelWalfisz` from prime Siegel–Walfisz.**  Paper proof refereed both ways
(Astra `20261011T224341Z`, Opus `20261011T224511Z`). -/
theorem twistedSiegelWalfisz_of_primeSW (hSW : PrimeCharacterSW) : TwistedSiegelWalfisz :=
  twistedSiegelWalfisz_of_uniformZ (uniformZTSW_of_primeSW hSW)

end NormalNumbers.PrimeModel.SiteFactor
