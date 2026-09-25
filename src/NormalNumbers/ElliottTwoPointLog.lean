import NormalNumbers.ElliottGeneral
import NormalNumbers.PairDecoupleTwoPoint

/-!
# The downstream consumer: the logarithmic two-point correlation of `ζ^{ω(pn+1)}`

`DIRECTION.md` item 4 (kickoff `KICKOFF-2026-09-24-elliott-general.md`, "the downstream use").
C1's two-point leaf `NormalNumbers.CastingOut.TwoPointElliott` is the *natural*-density two-point
correlation of `ζ^{ω(pn+1)}` against `conj ζ^{ω(qn+1)}`, `ζ = e(t/b)`.  The published theorem —
Tao 2016, Theorem 1.3, now `NormalNumbers.ElliottGeneral.nonasymptoticLogElliottMult` — gives the
**logarithmically averaged** version, which is what this file states and derives.

* `zetaOmegaInt u` — `ζ^ω` as a function `ℤ → ℂ` vanishing off the positive integers,
  `ζ = e(u)`.  It is multiplicative in the honest coprime sense (`ω` is additive on coprime
  pairs) but **not** completely multiplicative (`ω(p²) = 1 ≠ 2`).  That is exactly why the
  fidelity upgrade of lap 84 was needed: the dependency's `Prop` does not apply to it.
* `UniformlyNonPretentious g` — the Delange-side input, `D(g, χ·n^{is}; X)² → ∞` uniformly over
  all moduli and twists in the admissible range.  Left as a hypothesis here; it is the content of
  the `DelangeSlot*` / `TwoPointDelange*` stack.
* `TwoPointElliottLog b p q t` — the log-averaged two-point statement.
* `twoPointElliottLog_of_nonPretentious` — **the derivation**, from the proved headline.

The passage from the logarithmic average back to `TwoPointElliott`'s natural average is *not* done
here and is not known in general; the kickoff lists only the log version as following.
-/

open Finset Filter Topology
open NormalNumbers.ElliottMultStatement

namespace NormalNumbers.ElliottTwoPointLog

open Erdos67b NormalNumbers.CastingOut

noncomputable section

/-- `ζ^{ω(·)}` with `ζ = e(u)`, extended by zero to the nonpositive integers. -/
def zetaOmegaInt (u : ℝ) (z : ℤ) : ℂ :=
  if 0 < z then phase u ^ omegaNat z.toNat else 0

@[simp] theorem zetaOmegaInt_natCast {u : ℝ} {n : ℕ} (hn : 0 < n) :
    zetaOmegaInt u (n : ℤ) = phase u ^ omegaNat n := by
  simp [zetaOmegaInt, hn, Int.toNat_natCast]

theorem norm_zetaOmegaInt_le (u : ℝ) (z : ℤ) : ‖zetaOmegaInt u z‖ ≤ 1 := by
  unfold zetaOmegaInt
  split_ifs with h
  · simp [norm_pow, norm_phase]
  · simp

/-- `ω` is additive on coprime pairs, so `ζ^ω` is multiplicative in the coprime sense. -/
theorem omegaNat_mul_of_coprime {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (hmn : Nat.Coprime m n) : omegaNat (m * n) = omegaNat m + omegaNat n := by
  classical
  unfold omegaNat
  rw [Nat.primeFactors_mul hm.ne' hn.ne',
    Finset.card_union_of_disjoint hmn.disjoint_primeFactors]

theorem isCoprimeMult_zetaOmegaInt (u : ℝ) : IsCoprimeMultOnPosInt (zetaOmegaInt u) := by
  refine ⟨?_, ?_⟩
  · have h1 : omegaNat 1 = 0 := by simp [omegaNat]
    rw [show ((1 : ℤ)) = ((1 : ℕ) : ℤ) from rfl, zetaOmegaInt_natCast one_pos, h1, pow_zero]
  intro m n hm hn hmn
  have hmnpos : 0 < m * n := Nat.mul_pos hm hn
  rw [zetaOmegaInt_natCast hmnpos, zetaOmegaInt_natCast hm, zetaOmegaInt_natCast hn,
    omegaNat_mul_of_coprime hm hn hmn, pow_add]

theorem isCoprimeMult_conj_zetaOmegaInt (u : ℝ) :
    IsCoprimeMultOnPosInt (fun z => (starRingEnd ℂ) (zetaOmegaInt u z)) := by
  obtain ⟨h1, h2⟩ := isCoprimeMult_zetaOmegaInt u
  refine ⟨by simp [h1], ?_⟩
  intro m n hm hn hmn
  simp only [h2 m n hm hn hmn, map_mul]

/-- **The Delange-side input.**  `g` is non-pretentious to every `χ·n^{is}` with modulus `≤ A` and
`|s| ≤ A·X`, uniformly: for every level `A` the pretentious distance exceeds `A` once `X` is large.
This is what the `DelangeSlot*` stack is for; it is a hypothesis here. -/
def UniformlyNonPretentious (g : ℤ → ℂ) : Prop :=
  ∀ A : ℕ, ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X → ∀ q : ℕ, 0 < q → q ≤ A →
    ∀ χ : DirichletCharacter ℂ q, ∀ s : ℝ, |s| ≤ (A : ℝ) * X →
      (A : ℝ) ≤ pretentiousDistSqToTwist (restrictToNat g) χ s X

/-- **The log-averaged two-point statement for `ζ^{ω(pn+1)}`.**  The logarithmic correlation over
the full window `1 < n ≤ X` is `o(log X)`. -/
def TwoPointElliottLog (b p q : ℕ) (t : ℝ) : Prop :=
  Tendsto (fun X : ℕ =>
      ‖elliottLogCorrelation (zetaOmegaInt (t / b))
        (fun z => (starRingEnd ℂ) (zetaOmegaInt (t / b) z)) p q 1 1 X X‖
        / Real.log (X : ℝ))
    atTop (𝓝 0)

/-- **The derivation.**  Tao's theorem in its honest multiplicative form, applied to `ζ^ω`, gives
the logarithmic two-point correlation along `pn+1`, `qn+1` for distinct `p ≠ q`. -/
theorem twoPointElliottLog_of_nonPretentious {b p q : ℕ} {t : ℝ}
    (hp : 0 < p) (hq : 0 < q) (hpq : p ≠ q)
    (hnp : UniformlyNonPretentious (zetaOmegaInt (t / b))) :
    TwoPointElliottLog b p q t := by
  classical
  set u : ℝ := t / b with hu
  set g₁ : ℤ → ℂ := zetaOmegaInt u with hg₁
  set g₂ : ℤ → ℂ := fun z => (starRingEnd ℂ) (zetaOmegaInt u z) with hg₂
  have hdet : (p : ℤ) * 1 - (q : ℤ) * 1 ≠ 0 := by
    simp only [mul_one, sub_ne_zero]
    exact_mod_cast hpq
  rw [TwoPointElliottLog, Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨A₀, hA₀, hmain⟩ :=
    ElliottGeneral.nonasymptoticLogElliottMult p q 1 1 hp hq hdet (ε / 2) (by positivity)
  obtain ⟨X₀, hX₀⟩ := hnp A₀
  refine ⟨max (max X₀ A₀) 2, ?_⟩
  intro X hX
  have hXX₀ : X₀ ≤ X := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hX
  have hXA₀ : A₀ ≤ X := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hX
  have hX2 : 2 ≤ X := le_trans (le_max_right _ _) hX
  have hlogX : 0 < Real.log (X : ℝ) :=
    Real.log_pos (by exact_mod_cast (by omega : 1 < X))
  have hbound :
      ‖elliottLogCorrelation g₁ g₂ p q 1 1 X X‖ ≤ (ε / 2) * Real.log (X : ℝ) :=
    hmain A₀ X X le_rfl hXA₀ le_rfl g₁ g₂
      (isCoprimeMult_zetaOmegaInt u) (isCoprimeMult_conj_zetaOmegaInt u)
      (fun n => norm_zetaOmegaInt_le u n)
      (fun n => by simpa [hg₂] using norm_zetaOmegaInt_le u n)
      (fun r hr hrA χ s hs => hX₀ X hXX₀ r hr hrA χ s hs)
  have hnn : 0 ≤ ‖elliottLogCorrelation g₁ g₂ p q 1 1 X X‖ / Real.log (X : ℝ) := by positivity
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hnn, div_lt_iff₀ hlogX]
  calc ‖elliottLogCorrelation g₁ g₂ p q 1 1 X X‖ ≤ (ε / 2) * Real.log (X : ℝ) := hbound
    _ < ε * Real.log (X : ℝ) := by nlinarith

end

end NormalNumbers.ElliottTwoPointLog
