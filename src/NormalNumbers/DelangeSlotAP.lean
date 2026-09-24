import NormalNumbers.DelangeSlotChar
import PNTPort.Wiener

/-!
# Rung 2, layer 2: `ψ(x,χ) = o(x)` from the prime number theorem in arithmetic progressions

`DelangeSlotChar.Sgsum_tendsto_zero_of_psi_littleO` reduces the non-principal half of the
twisted slot to the single analytic input `ψ(x,χ) = o(x)`.  This file reduces *that* to the
prime number theorem in arithmetic progressions,

  `ψ(x; q, a) = ∑_{d ≤ x, d ≡ a (q)} Λ d  ~  x / φ(q)`   for `gcd(a,q) = 1`,

which is the **named open leaf** `psiAP_tendsto` below.  Everything else here is proved.

## Why this is the right leaf (route note, 2026-09-24)

`ψ(x,χ)` is complex-valued, so Wiener–Ikehara — which in every available formalisation
(`PrimeNumberTheoremAnd/Wiener.lean`, `WienerIkeharaTheorem''`) requires `0 ≤ f` — cannot be
applied to it directly.  But `Λ` restricted to a residue class **is** nonnegative, and mathlib
already carries exactly the analytic input Wiener–Ikehara needs for it:
`ArithmeticFunction.vonMangoldt.continuousOn_LFunctionResidueClassAux` (the Dirichlet series of
`vonMangoldt.residueClass a` minus its `1/(s-1)` pole, continuous on `re s ≥ 1`) together with
`eqOn_LFunctionResidueClassAux`.  So `psiAP_tendsto` is a *port*, not a new theorem: feed
mathlib's `LFunctionResidueClassAux` to a vendored `WienerIkeharaTheorem''`.  The support files
that `Wiener.lean` needs (`Fourier`, `Sobolev`, `SmoothExistence`) are already vendored in
`src/PNTPort/`.

Note the direction of the reduction: we go *through* residue classes rather than characters,
precisely to keep the Wiener–Ikehara input nonnegative.  Summing back over the class with the
character weights (`psiChar_eq_sum_psiAP`) is elementary, and the cancellation
`∑_{a} χ a = 0` for non-principal `χ` is what kills the main term.
-/

open Finset ArithmeticFunction Filter Topology

namespace NormalNumbers.DelangeSlot

/-- `ψ(X; q, a) = ∑_{d ≤ X, d ≡ a (mod q)} Λ d`. -/
noncomputable def psiAP (q a X : ℕ) : ℝ := ∑ d ∈ (Ioc 0 X).filter (fun d => d % q = a), Λ d

lemma psiAP_nonneg (q a X : ℕ) : 0 ≤ psiAP q a X :=
  Finset.sum_nonneg fun _ _ ↦ vonMangoldt_nonneg

/-- Grouping `ψ(·,χ)` by residue class.  Uses only that `χ` is `q`-periodic. -/
theorem psiChar_eq_sum_psiAP {q : ℕ} (hq : 0 < q) (χ : ℕ → ℂ)
    (hper : ∀ a b : ℕ, a % q = b % q → χ a = χ b) (X : ℕ) :
    psiChar χ X = ∑ a ∈ range q, χ a * (psiAP q a X : ℂ) := by
  classical
  have hmaps : ∀ d ∈ Ioc 0 X, d % q ∈ range q := fun d _ ↦ mem_range.2 (Nat.mod_lt _ hq)
  rw [psiChar, ← Finset.sum_fiberwise_of_maps_to hmaps (fun d => (Λ d : ℂ) * χ d)]
  refine Finset.sum_congr rfl fun a ha ↦ ?_
  have haq : a % q = a := Nat.mod_eq_of_lt (mem_range.1 ha)
  rw [psiAP, Complex.ofReal_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun d hd ↦ ?_
  have hd' : d % q = a := (mem_filter.1 hd).2
  rw [hper d a (by rw [hd', haq])]
  ring

/-- **The named open leaf: PNT in arithmetic progressions.**  For `gcd(a,q) = 1`,
`ψ(X; q, a) / X → 1 / φ(q)`.

This is *not* a new theorem: it is Wiener–Ikehara applied to the nonnegative arithmetic
function `ArithmeticFunction.vonMangoldt.residueClass a`, whose Dirichlet series minus its
pole is mathlib's `vonMangoldt.LFunctionResidueClassAux`, already proved continuous on
`re s ≥ 1` (`continuousOn_LFunctionResidueClassAux`) and equal to the series on `re s > 1`
(`eqOn_LFunctionResidueClassAux`).  The missing piece is a Lean Wiener–Ikehara for
nonnegative coefficients; `PrimeNumberTheoremAnd/Wiener.lean`'s `WienerIkeharaTheorem''` is
the intended source, and its support files (`Fourier`, `Sobolev`, `SmoothExistence`) are
already vendored in `src/PNTPort/`.  See the file header. -/
theorem psiAP_tendsto {q a : ℕ} (hq : 0 < q) (ha : Nat.Coprime a q) (haq : a < q) :
    Tendsto (fun X : ℕ => psiAP q a X / X) atTop (𝓝 (1 / (Nat.totient q : ℝ))) := by
  classical
  set f : ℕ → ℝ := fun n => if n % q = a then Λ n else 0 with hf
  have hcum : ∀ X : ℕ, cumsum f (X + 1) = psiAP q a X := by
    intro X
    have hset : Finset.range (X + 1) = insert 0 (Finset.Ioc 0 X) := by
      ext i; simp
    rw [cumsum, hset, Finset.sum_insert (by simp), psiAP, Finset.sum_filter]
    simp [hf]
  have h := WeakPNT_AP (q := q) (a := a) hq ha haq
  have h1 : Tendsto (fun X : ℕ => psiAP q a X / ((X : ℝ) + 1)) atTop
      (𝓝 (1 / (Nat.totient q : ℝ))) := by
    have := h.comp (Filter.tendsto_add_atTop_nat 1)
    refine this.congr fun X ↦ ?_
    simp only [Function.comp_apply]
    rw [← hf, hcum X]
    push_cast
    ring
  have h2 : Tendsto (fun X : ℕ => ((X : ℝ) + 1) / X) atTop (𝓝 1) := by
    have : Tendsto (fun X : ℕ => 1 + (X : ℝ)⁻¹) atTop (𝓝 (1 + 0)) :=
      tendsto_const_nhds.add (tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop)
    rw [add_zero] at this
    refine this.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with X hX
    have : (0:ℝ) < X := by exact_mod_cast hX
    field_simp
  have h3 := h1.mul h2
  rw [mul_one] at h3
  refine h3.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with X hX
  have hX0 : (0:ℝ) < X := by exact_mod_cast hX
  have hX1 : ((X:ℝ) + 1) ≠ 0 := by positivity
  field_simp

/-- **`ψ(x,χ) = o(x)` for a `q`-periodic `χ` supported on the units with `∑_a χ a = 0`.**
The principal character is exactly the one excluded by `hsum`. -/
theorem psiChar_littleO {q : ℕ} (hq : 0 < q) (χ : ℕ → ℂ)
    (hper : ∀ a b : ℕ, a % q = b % q → χ a = χ b)
    (hzero : ∀ a : ℕ, ¬ Nat.Coprime a q → χ a = 0)
    (hsum : ∑ a ∈ range q, χ a = 0) :
    ∀ ε : ℝ, 0 < ε → ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X → ‖psiChar χ X‖ ≤ ε * X := by
  classical
  -- the normalised sum tends to `(1/φ q) * ∑_a χ a = 0`
  have hlim : Tendsto (fun X : ℕ => psiChar χ X / (X : ℂ)) atTop (𝓝 0) := by
    have hcomp : ∀ X : ℕ, psiChar χ X / (X : ℂ)
        = ∑ a ∈ range q, χ a * ((psiAP q a X / X : ℝ) : ℂ) := by
      intro X
      rw [psiChar_eq_sum_psiAP hq χ hper X, Finset.sum_div]
      refine Finset.sum_congr rfl fun a _ ↦ ?_
      push_cast
      ring
    have hterm : ∀ a ∈ range q,
        Tendsto (fun X : ℕ => χ a * ((psiAP q a X / X : ℝ) : ℂ)) atTop
          (𝓝 (χ a * ((1 / (Nat.totient q : ℝ) : ℝ) : ℂ))) := by
      intro a ha
      by_cases hco : Nat.Coprime a q
      · exact (Complex.continuous_ofReal.continuousAt.tendsto.comp
          (psiAP_tendsto hq hco (mem_range.1 ha))).const_mul _
      · simp [hzero a hco]
    have := tendsto_finset_sum _ hterm
    rw [← Finset.sum_mul] at this
    rw [hsum, zero_mul] at this
    simpa only [hcomp] using this
  -- turn the limit into the ε-form
  intro ε hε
  rw [Metric.tendsto_atTop] at hlim
  obtain ⟨X₁, hX₁⟩ := hlim (ε / 2) (by linarith)
  refine ⟨max X₁ 1, fun X hX ↦ ?_⟩
  have hX1 : 1 ≤ X := le_trans (le_max_right _ _) hX
  have hXR : (1:ℝ) ≤ X := by exact_mod_cast hX1
  have hXpos : (0:ℝ) < X := by linarith
  have h := hX₁ X (le_trans (le_max_left _ _) hX)
  rw [Complex.dist_eq, sub_zero, norm_div, Complex.norm_natCast, div_lt_iff₀ hXpos] at h
  nlinarith

end NormalNumbers.DelangeSlot
