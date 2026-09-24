import NormalNumbers.PrimeLambertFour
import NormalNumbers.Disjunctive

/-!
# Casting out `b − 1`: an abelian statistic that carries touch only at the ends

Conjectures C1–C3 of `CONJECTURES-2026-09-23-casting-out-and-rungs.md`, frozen here as `Prop`s,
together with the provable pieces around them.

* `windowDigitSum_modEq` — casting out nines: a window's digit sum is `⌊b^{n+L}x⌋ − ⌊bⁿx⌋`
  modulo `b − 1`.
* `windowDigitSum_lambert_modEq` — for `x = Σ w(m)/bᵐ` the carries enter only at the two window
  ends: `Σ_{m∈(n,n+L]} w(m) + c_{n+L} − c_n`.  This is why the statistic escapes the refuted Maze row
  "G4 sectors as digit characters", where carries hit every digit.
* `normalCastLaw` — the law of the window digit sum mod `b − 1` for a NORMAL number.  It is
  **not uniform** (`not_castUniform_of_isNormal`): in base 3 a single digit is even with
  probability `2/3`.  The first draft of C1 asked for uniformity; that was false, and the theorem
  records it.  The right target is `CastLaw` (`castLaw_of_isNormal`).
* `ConjC1` (G4 has the normal casting-out law), `ConjC2` (Erdős–Borwein is disjunctive),
  `ConjC3` (G4 is *rich*: every word has positive lower density).  These are statements, not
  theorems.  The bridges `isRich_of_isNormal` and `isDisjunctive_of_isRich` place C3 strictly on
  the ladder between the proved `isDisjunctive_base` and normality.
-/

open Finset Filter Topology NormalNumbers.PrimeLambert

namespace NormalNumbers.CastingOut

/-- Sum of the base-`b` digits with indices `n, …, n+L−1` of `x` (digit `i` sits at position
`i + 1` after the point, as in `digitOf`). -/
noncomputable def windowDigitSum (b : ℕ) (x : ℝ) (n L : ℕ) : ℕ :=
  ∑ i ∈ range L, digitOf b (Int.fract x) (n + i)

/-- **Casting out `b − 1`.** -/
theorem windowDigitSum_modEq (b : ℕ) (hb : 2 ≤ b) (x : ℝ) (n L : ℕ) :
    (windowDigitSum b x n L : ℤ) ≡ ⌊x * (b : ℝ) ^ (n + L)⌋ - ⌊x * (b : ℝ) ^ n⌋
      [ZMOD ((b : ℤ) - 1)] := by
  have hfr : ∀ k : ℕ, ⌊Int.fract x * (b:ℝ)^k⌋ = ⌊x * (b:ℝ)^k⌋ - ⌊x⌋ * (b:ℤ)^k := by
    intro k
    have h : Int.fract x * (b:ℝ)^k = x * (b:ℝ)^k - ((⌊x⌋ * (b:ℤ)^k : ℤ) : ℝ) := by
      push_cast [Int.fract]; ring
    rw [h, Int.floor_sub_intCast]
  have hstep : ∀ k : ℕ, ((digitOf b (Int.fract x) k : ℤ))
      ≡ ⌊Int.fract x * (b:ℝ)^(k+1)⌋ - ⌊Int.fract x * (b:ℝ)^k⌋ [ZMOD ((b:ℤ)-1)] := by
    intro k
    rw [floor_mul_pow_succ b hb _ (Int.fract_nonneg x) k]
    exact Int.modEq_iff_dvd.mpr ⟨⌊Int.fract x * (b:ℝ)^k⌋, by ring⟩
  have hmain : ∀ L : ℕ, ((windowDigitSum b x n L : ℤ))
      ≡ ⌊Int.fract x * (b:ℝ)^(n+L)⌋ - ⌊Int.fract x * (b:ℝ)^n⌋ [ZMOD ((b:ℤ)-1)] := by
    intro L
    induction L with
    | zero => simp [windowDigitSum]
    | succ L ih =>
        have e : (windowDigitSum b x n (L+1) : ℤ)
            = (windowDigitSum b x n L : ℤ) + (digitOf b (Int.fract x) (n+L) : ℤ) := by
          simp [windowDigitSum, Finset.sum_range_succ]
        rw [e]
        have := (ih.add (hstep (n+L)))
        have h2 : (⌊Int.fract x * (b:ℝ)^(n+L)⌋ - ⌊Int.fract x * (b:ℝ)^n⌋)
            + (⌊Int.fract x * (b:ℝ)^(n+L+1)⌋ - ⌊Int.fract x * (b:ℝ)^(n+L)⌋)
            = ⌊Int.fract x * (b:ℝ)^(n+(L+1))⌋ - ⌊Int.fract x * (b:ℝ)^n⌋ := by
          rw [show n + (L+1) = n + L + 1 by omega]; ring
        rw [← h2]
        exact this
  have h := hmain L
  rw [hfr (n+L), hfr n] at h
  refine h.trans ?_
  refine Int.modEq_iff_dvd.mpr ?_
  have hd : ((b:ℤ) - 1) ∣ ((b:ℤ)^L - 1) := by
    simpa using sub_dvd_pow_sub_pow (b:ℤ) 1 L
  obtain ⟨c, hc⟩ := hd
  exact ⟨⌊x⌋ * (b:ℤ)^n * c, by rw [pow_add]; linear_combination (⌊x⌋ * (b:ℤ)^n) * hc⟩

/-- The real number `Σ_m w(m)/bᵐ`. -/
noncomputable def lambertVal (b : ℕ) (w : ℕ → ℕ) : ℝ := ∑' m : ℕ, (w m : ℝ) / (b : ℝ) ^ m

/-- The carry into position `N`: `⌊Σ_{m>N} w(m) b^{N−m}⌋`. -/
noncomputable def carry (b : ℕ) (w : ℕ → ℕ) (N : ℕ) : ℤ :=
  ⌊∑' k : ℕ, (w (N + 1 + k) : ℝ) / (b : ℝ) ^ (k + 1)⌋

/-- **Carries only at the ends.**  For a Lambert-type value with at most linear weights. -/
theorem windowDigitSum_lambert_modEq (b : ℕ) (hb : 2 ≤ b) (w : ℕ → ℕ) (hw : ∀ m, w m ≤ m)
    (n L : ℕ) :
    (windowDigitSum b (lambertVal b w) n L : ℤ) ≡
      (∑ m ∈ Ioc n (n + L), (w m : ℤ)) + carry b w (n + L) - carry b w n
      [ZMOD ((b : ℤ) - 1)] := by
  sorry

/-- `G4_b` is the Lambert value of `ω`. -/
theorem primeLambertAtBase_eq_lambertVal (b : ℕ) :
    primeLambertAtBase b = lambertVal b (fun m => m.primeFactors.card) := by
  sorry

/-- The **Erdős–Borwein constant** in base `b`: `Σ_{n≥1} 1/(bⁿ − 1)`. -/
noncomputable def erdosBorweinAtBase (b : ℕ) : ℝ := ∑' n : ℕ, 1 / ((b : ℝ) ^ (n + 1) - 1)

/-- `Σ_{n≥1} 1/(bⁿ−1) = Σ_m d(m)/bᵐ` (Lambert series of the divisor count). -/
theorem erdosBorweinAtBase_eq_lambertVal (b : ℕ) (hb : 2 ≤ b) :
    erdosBorweinAtBase b = lambertVal b (fun m => m.divisors.card) := by
  sorry

/-- The law of the digit sum of `L` independent uniform base-`b` digits, modulo `b − 1`. -/
noncomputable def normalCastLaw (b L r : ℕ) : ℝ :=
  ((univ.filter (fun v : Fin L → Fin b => (∑ i, (v i : ℕ)) % (b - 1) = r)).card : ℝ) /
    (b : ℝ) ^ L

/-- Closed form: `1/(b−1) + b^{−L}((b−1)[r=0] − 1)/(b−1)`. -/
theorem normalCastLaw_closed (b L r : ℕ) (hb : 3 ≤ b) (hr : r < b - 1) :
    normalCastLaw b L r =
      1 / ((b : ℝ) - 1) + ((b : ℝ) ^ L)⁻¹ * ((if r = 0 then (b : ℝ) - 1 else 0) - 1) / ((b : ℝ) - 1) := by
  sorry

/-- Frequency of windows of length `L` whose digit sum is `≡ r (mod b−1)`, among `n < N`. -/
noncomputable def castFreq (b : ℕ) (x : ℝ) (L r N : ℕ) : ℝ :=
  (((range N).filter (fun n => windowDigitSum b x n L % (b - 1) = r)).card : ℝ) / N

/-- `x` has the casting-out law of a normal number at window length `L`. -/
def CastLaw (b : ℕ) (x : ℝ) (L : ℕ) : Prop :=
  ∀ r < b - 1, Tendsto (castFreq b x L r) atTop (𝓝 (normalCastLaw b L r))

/-- The (false) first draft of C1: window digit sums uniform mod `b − 1`. -/
def CastUniform (b : ℕ) (x : ℝ) (L : ℕ) : Prop :=
  ∀ r < b - 1, Tendsto (castFreq b x L r) atTop (𝓝 (1 / ((b : ℝ) - 1)))

theorem castLaw_of_isNormal (b : ℕ) (hb : 3 ≤ b) (x : ℝ) (hx : IsNormal b x) (L : ℕ) :
    CastLaw b x L := by
  sorry

/-- **The first draft of C1 was false**: no normal number has uniform window digit sums. -/
theorem not_castUniform_of_isNormal (b : ℕ) (hb : 3 ≤ b) (x : ℝ) (hx : IsNormal b x) (L : ℕ)
    (hL : 1 ≤ L) : ¬ CastUniform b x L := by
  sorry

/-- **C1.**  `G4_b` has the casting-out law of a normal number, every base `b ≥ 3`, every `L`. -/
def ConjC1 : Prop := ∀ b, 3 ≤ b → ∀ L, CastLaw b (primeLambertAtBase b) L

/-- **C2.**  The Erdős–Borwein constant is disjunctive in every base `b ≥ 3`. -/
def ConjC2 : Prop := ∀ b, 3 ≤ b → IsDisjunctive b (erdosBorweinAtBase b)

/-- `x` is **rich** in base `b`: every word occurs at a set of positions of positive lower
density. -/
noncomputable def IsRich (b : ℕ) (x : ℝ) : Prop :=
  open Classical in
  ∀ w : List ℕ, (∀ d ∈ w, d < b) → ∃ c : ℝ, 0 < c ∧
    ∀ᶠ N in atTop, c * N ≤ (((range N).filter (fun n => OccursAt b x w n)).card : ℝ)

/-- **C3.**  `G4_b` is rich in every base `b ≥ 3`. -/
def ConjC3 : Prop := ∀ b, 3 ≤ b → IsRich b (primeLambertAtBase b)

theorem isRich_of_isNormal (b : ℕ) (hb : 2 ≤ b) (x : ℝ) (hx : IsNormal b x) : IsRich b x := by
  sorry

theorem isDisjunctive_of_isRich (b : ℕ) (hb : 2 ≤ b) (x : ℝ) (hx : IsRich b x) :
    IsDisjunctive b x := by
  sorry

/-- C1 and C3 both sit below normality of `G4`. -/
theorem conjC1_conjC3_of_normal (h : ∀ b, 3 ≤ b → IsNormal b (primeLambertAtBase b)) :
    ConjC1 ∧ ConjC3 := by
  sorry

end NormalNumbers.CastingOut
