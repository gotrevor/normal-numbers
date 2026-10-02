/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.TTDyadicBridge

/-!
# Referee pass on `TTEquidistributedDyadic` (2026-10-02)

Report: `docs/TT-DYADIC-REFEREE-2026-10-02.md`.  Verdict: `TTEquidistributedDyadic` is implied
by Tao–Teräväinen arXiv:2512.01739 Theorem 3.1(i), through a short elementary perturbation
argument the paper does not contain.  The trust surface therefore has two layers: TT, and our own
unformalized derivation.  This file splits them.

* `TTEquidistributedReal` — the **literal** transcription of TT Thm 3.1(i): the exceptional set
  `E ⊆ [√X, X]` is charged by `∫_E dt/t`, and the conclusion (3.4) is asked at **every real**
  `N ∈ [√X, X] \ E`.  Asking it at real `N` is what closes the null-set loophole that made
  `TTEquidistributedCorrelation` a theorem.
* `ttEquidistributedDyadic_of_real` — the derivation, **proved** (2026-10-02, via
  `NormalNumbers/TTDyadicBridge.lean`): `TTEquidistributedDyadic` is a theorem from TT verbatim.
* `TTEquidistributedDyadicPow2` — the consumer's actual demand: `binPair_cov_core`
  (`G4Base2PairCov.lean`) instantiates the conclusion only at `N = 2^j`.
* `ttEquidistributedDyadicPow2_of_dyadic` — proved.
-/

open MeasureTheory

namespace NormalNumbers.CastingOut

/-- **Tao–Teräväinen arXiv:2512.01739, Theorem 3.1 case (i), literally** (§3, (3.1), (3.2),
(3.4)).  Faithful-or-weaker: the `O(N L^{-1})` of (3.1) is pinned to `1`; `W ∈ [L^c]`; the shifts
`h₁ ≠ h₂` and residue `b` are naturals `≤ L^c` (paper: integers `O(L^c)`).  The conclusion is at
every **real** `N ∈ [√X, X] \ E`, the sum running over the naturals `N < n ≤ 2N`. -/
def TTEquidistributedReal : Prop :=
  ∃ c Cst : ℝ, 0 < c ∧ 0 < Cst ∧
    ∀ g₁ g₂ : ℕ → ℂ, IsCoprimeMultiplicativeNat g₁ → IsCoprimeMultiplicativeNat g₂ →
      (∀ n, ‖g₁ n‖ ≤ 1) → (∀ n, ‖g₂ n‖ ≤ 1) → (∀ n, (g₁ n).im = 0) →
      ∀ X L : ℝ, 2 ≤ X → 1 ≤ L → L ≤ Real.log X → ∀ δ : ℝ → ℝ,
        (∀ N : ℝ, X ^ (0.4 : ℝ) ≤ N → N ≤ X → ∀ a q : ℕ, 1 ≤ q →
          ‖(∑ n ∈ (Finset.Ioc ⌊N⌋₊ ⌊2 * N⌋₊).filter (fun n => n % q = a % q), g₁ n)
              - (((N / q) * δ N : ℝ) : ℂ)‖ ≤ N / L) →
        (∀ p : ℕ, p.Prime → Real.exp (Real.log X ^ ((1 : ℝ) / 11)) ≤ p →
          (p : ℝ) ≤ Real.exp (Real.log X ^ ((1 : ℝ) / 10)) → g₁ p = 1) →
        ∃ E : Set ℝ, MeasurableSet E ∧ E ⊆ Set.Icc (Real.sqrt X) X ∧
          (∫ t in E, t⁻¹) ≤ Cst * L ^ (-c) * Real.log X ∧
          ∀ N : ℝ, Real.sqrt X ≤ N → N ≤ X → N ∉ E →
            ∀ W b h₁ h₂ : ℕ, 0 < W → (W : ℝ) ≤ L ^ c →
              (h₁ : ℝ) ≤ L ^ c → (h₂ : ℝ) ≤ L ^ c → h₁ ≠ h₂ →
              ‖((W : ℝ) / N : ℝ) •
                  ∑ n ∈ (Finset.Ioc ⌊N⌋₊ ⌊2 * N⌋₊).filter (fun n => n % W = b % W),
                    (g₁ (n + h₁) - ((δ N : ℝ) : ℂ)) * g₂ (n + h₂)‖
                ≤ Cst * L ^ (-c)

/-- **The derivation behind `TTEquidistributedDyadic`** (proved; referee 2026-10-02).  The
formal proof (`TTBridge.dyadic_of_real_core`) uses `c' = min c 1 / 4`, `η = L^{-2c'}`, one-sided
windows `[N, N(1+η)]`, crude term counts, and declares the top scale exceptional; the sketch
below (with `c/2`) is the original plan.

English proof.  Fix `(c, Cst)` from the literal form and put `η := L^{-c/2}`, `c' := c/2`.
(1) *Transfer.*  From (3.1) with `q = 1` (constant `1`), `|δ_N| ≤ 3` and
`|δ_N − δ_{N'}| ≤ 2/L + O(η + 1/N)` whenever `|log N − log N'| ≤ η`.  Moving `N'` (real, `∉ E`)
to a natural `N` with `|log N − log N'| ≤ η` changes `(W/N)·Σ_{N<n≤2N, n≡b (W)}(g₁(n+h₁)−δ)g₂(n+h₂)`
by `O(η + W/N + 1/L)`: `O(ηN/W + 1)` boundary terms of size `≤ 4`, the prefactor ratio, and the
`δ` shift.  (2) *Counting.*  A natural `N ∈ [√X, X)` fails only if `[N e^{−η}, N e^{η}] ∩ [√X, X]`,
of log-length `≥ η`, lies inside `E`; each `t` lies in at most two of the enlarged blocks
`[2^j e^{−η}, 2^{j+1} e^{η}]`, so the failing blocks number `≤ 2·∫_E dt/t / η ≪ L^{−c/2} log X`,
which is `≪ L^{−c/2}·#dyadicScales X` once a scale exists.  (3) The bound at good blocks is
`Cst L^{−c} + O(L^{−c/2})`, and `W, h ≤ L^{c/2} ≤ L^c`.  Small `L` is absorbed by enlarging `Cst`
(then `E` = all scales is admissible). -/
theorem ttEquidistributedDyadic_of_real : TTEquidistributedReal → TTEquidistributedDyadic := by
  rintro ⟨c, Cst, hc, hCst, h⟩
  exact TTBridge.dyadic_of_real_core hc hCst h

/-- **What the consumer uses.**  `binPair_cov_core` instantiates `TTEquidistributedDyadic` only at
the left endpoint `N = 2^j` of each non-exceptional dyadic scale. -/
def TTEquidistributedDyadicPow2 : Prop :=
  ∃ c Cst : ℝ, 0 < c ∧ 0 < Cst ∧
    ∀ g₁ g₂ : ℕ → ℂ, IsCoprimeMultiplicativeNat g₁ → IsCoprimeMultiplicativeNat g₂ →
      (∀ n, ‖g₁ n‖ ≤ 1) → (∀ n, ‖g₂ n‖ ≤ 1) → (∀ n, (g₁ n).im = 0) →
      ∀ X L : ℝ, 2 ≤ X → 1 ≤ L → L ≤ Real.log X → ∀ δ : ℝ → ℝ,
        (∀ N : ℝ, X ^ (0.4 : ℝ) ≤ N → N ≤ X → ∀ a q : ℕ, 1 ≤ q →
          ‖(∑ n ∈ (Finset.Ioc ⌊N⌋₊ ⌊2 * N⌋₊).filter (fun n => n % q = a % q), g₁ n)
              - (((N / q) * δ N : ℝ) : ℂ)‖ ≤ N / L) →
        (∀ p : ℕ, p.Prime → Real.exp (Real.log X ^ ((1 : ℝ) / 11)) ≤ p →
          (p : ℝ) ≤ Real.exp (Real.log X ^ ((1 : ℝ) / 10)) → g₁ p = 1) →
        ∃ E : Finset ℕ, E ⊆ dyadicScales X ∧
          (E.card : ℝ) ≤ Cst * L ^ (-c) * ((dyadicScales X).card : ℝ) ∧
          ∀ j ∈ dyadicScales X, j ∉ E →
            ∀ W b h₁ h₂ : ℕ, 0 < W → (W : ℝ) ≤ L ^ c →
              (h₁ : ℝ) ≤ L ^ c → (h₂ : ℝ) ≤ L ^ c → h₁ ≠ h₂ →
              ‖((W : ℝ) / ((2 ^ j : ℕ) : ℝ) : ℝ) •
                  ∑ n ∈ (Finset.Ioc (2 ^ j) (2 * 2 ^ j)).filter (fun n => n % W = b % W),
                    (g₁ (n + h₁) - ((δ ((2 ^ j : ℕ) : ℝ) : ℝ) : ℂ)) * g₂ (n + h₂)‖
                ≤ Cst * L ^ (-c)

/-- The consumer form is weaker than `TTEquidistributedDyadic` (specialize `N := 2^j`). -/
theorem ttEquidistributedDyadicPow2_of_dyadic :
    TTEquidistributedDyadic → TTEquidistributedDyadicPow2 := by
  rintro ⟨c, Cst, hc, hCst, h⟩
  refine ⟨c, Cst, hc, hCst, fun g₁ g₂ hg₁ hg₂ hb₁ hb₂ him X L hX hL1 hLX δ h31 h32 => ?_⟩
  obtain ⟨E, hEsub, hEcard, hgood⟩ := h g₁ g₂ hg₁ hg₂ hb₁ hb₂ him X L hX hL1 hLX δ h31 h32
  refine ⟨E, hEsub, hEcard, fun j hj hjE W b h₁ h₂ hW hWL hh₁ hh₂ hne => ?_⟩
  exact hgood j hj hjE (2 ^ j) (by push_cast; exact le_rfl)
    (by push_cast; exact pow_lt_pow_right₀ (by norm_num) (by omega)) W b h₁ h₂ hW hWL hh₁ hh₂ hne

end NormalNumbers.CastingOut
