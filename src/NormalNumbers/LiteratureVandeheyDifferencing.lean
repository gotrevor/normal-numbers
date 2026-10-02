/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.G4WiringCRT

/-!
# Vandehey's differencing bound for Korobov sums (cited input)

Vandehey, *Differencing methods for Korobov-type exponential sums*, arXiv:1606.07911,
Theorem 5.1, with the constants given by the recursion displayed on p. 14.  Tier S: transcribed
from `docs/GROWING-PRIME-LOCALIZED-LOG-AUDIT-2026-10-02.md` §1.1, which re-derived the recursion
from Proposition 4.1 and checked it line by line (90%) and checked that nothing in the statement
hides a `P`-dependent constant (85%).  So the statement is uniform in the finite prime set `P`
as written; that uniformity is what the growing-prime campaign consumes.

Faithful, except that `m = 1` is excluded (`2 ≤ m`), which only weakens it.

The `k = 0` case is Vandehey's Lemma 2.3, `(m^{1/2} + M m^{−1/2} N)(1 + log m)`, which comes from
Korobov's complete-sum lemma (the `d = 1` case Vandehey corrects in his Lemma 2.2).
-/

namespace NormalNumbers.Literature.VandeheyDiff

open Finset NormalNumbers.G4

/-- `Q = ∏_{p∈P} p`. -/
def primeProd (P : Finset ℕ) : ℕ := ∏ p ∈ P, p

/-- `M(P) = ∏_{p∈P} p^{β'_p}` with `p^{β'_p} ‖ b^{2·ord(b, Q)} − 1` (Vandehey eq. 3). -/
noncomputable def bigM (b : ℕ) (P : Finset ℕ) : ℕ :=
  ∏ p ∈ P, p ^ padicValNat p (b ^ (2 * orderOf (b : ZMod (primeProd P))) - 1)

/-- `C_{P,x} = ∏_{p∈P} pˣ/(pˣ − 1)` (Vandehey Lemma 4.2). -/
noncomputable def cP (P : Finset ℕ) (x : ℝ) : ℝ :=
  ∏ p ∈ P, (p : ℝ) ^ x / ((p : ℝ) ^ x - 1)

/-- `α_k = 1/(2^{k+2} − 2)`. -/
noncomputable def alpha (k : ℕ) : ℝ := 1 / ((2 : ℝ) ^ (k + 2) - 2)

/-- The exponent pair `(γ_k, ν_k)`: `γ_0 = 0`, `ν_0 = 1`,
`γ_k = (1 + γ + αν)/(2(1+α))`, `ν_k = (1+ν)/2 + (1+γ−ν)α/(2(1+α))`, previous-index values. -/
noncomputable def expPair : ℕ → ℝ × ℝ
  | 0 => (0, 1)
  | k + 1 =>
    let γ := (expPair k).1
    let ν := (expPair k).2
    let α := alpha k
    ((1 + γ + α * ν) / (2 * (1 + α)), (1 + ν) / 2 + (1 + γ - ν) * α / (2 * (1 + α)))

/-- The constant pair `(A_k, B_k)`: `A_0 = 1`, `B_0 = M`,
`A_k = (2^{s+2} Q (A+B) C_{P,α} + 2Q + 2 A M C_{P,1+α})^{1/2}`,
`B_k = (2^{1+α} B M Q^α C_{P,1−α})^{1/2}`, with `s = |P|`, `α = α_{k−1}`. -/
noncomputable def constPair (b : ℕ) (P : Finset ℕ) : ℕ → ℝ × ℝ
  | 0 => (1, bigM b P)
  | k + 1 =>
    let A := (constPair b P k).1
    let B := (constPair b P k).2
    let α := alpha k
    let s : ℝ := P.card
    let Q : ℝ := primeProd P
    let M : ℝ := bigM b P
    (Real.sqrt ((2 : ℝ) ^ (s + 2) * Q * (A + B) * cP P α + 2 * Q + 2 * A * M * cP P (1 + α)),
     Real.sqrt ((2 : ℝ) ^ (1 + α) * B * M * Q ^ α * cP P (1 - α)))

/-- **Vandehey, Theorem 5.1.**  For every base `b ≥ 2`, every finite set `P` of primes coprime
to `b`, every `m ≥ 2` with all prime factors in `P`, every integer `a` coprime to `m`, every
`k` and every `N ≥ 1`:
`|Σ_{n=1}^N e(a bⁿ/m)| ≤ (A_k m^{α_k} N^{γ_k} + B_k m^{−α_k} N^{ν_k}) (1 + log m)^{2^{−k}}`. -/
def VandeheyThm51 : Prop :=
  ∀ (b : ℕ), 2 ≤ b → ∀ (P : Finset ℕ), (∀ p ∈ P, p.Prime ∧ Nat.Coprime p b) →
    ∀ (m : ℕ), 2 ≤ m → (∀ p, p.Prime → p ∣ m → p ∈ P) →
    ∀ (a : ℤ), IsCoprime a (m : ℤ) → ∀ (k N : ℕ), 1 ≤ N →
      ‖∑ n ∈ Icc 1 N, ePhase ((a : ℝ) * (b : ℝ) ^ n / m)‖ ≤
        ((constPair b P k).1 * (m : ℝ) ^ alpha k * (N : ℝ) ^ (expPair k).1
          + (constPair b P k).2 * (m : ℝ) ^ (-alpha k) * (N : ℝ) ^ (expPair k).2)
          * (1 + Real.log m) ^ ((2 : ℝ) ^ (-(k : ℝ)))

end NormalNumbers.Literature.VandeheyDiff
