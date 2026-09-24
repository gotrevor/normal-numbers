import NormalNumbers.PairDecoupleTwoPoint

/-!
# The exact peel, on the RATIFIED target's own leaf

Laps 24–25 removed `K → ∞` from the *unshifted* crux `PairDecorr`.  This file does the same for
the shifted crux `ShiftCorrSmall`, which is the leaf of the ratified target `pairDecouple_all`
(`shiftCorrSmall_iff_multiElliott`).

`shiftPairDiff` is the difference of two copies of `pairTail`, and `pairTail_eq_digitTrunc_add`
is exact, so for **every** depth `K`

`shiftPairDiff = shiftDigitTrunc_K + b^{−K}·(Θ_K(N) − Θ_K(N'))`,   `Θ_K = θ_{p·+K} − θ_{q·+K}`,

with no error term.  Hence `ShiftCorrSmall` is *equivalent*, at every fixed `K`, to a `4K`-point
root-of-unity correlation twisted by one unit-modulus weight — no `AdmissibleTrunc`, no growing
depth, `K = 1` allowed.
-/

open Finset Filter Topology

namespace NormalNumbers.CastingOut

/-- The unit-modulus weight left by the `K`-fold peel of the shifted pair difference. -/
noncomputable def shiftPeelWeight (b p q Q c j j' K : ℕ) (t : ℝ) (i : ℕ) : ℂ :=
  phase (t / (b : ℝ) ^ K *
    (shiftPairTail b p q K K (c + (i + j) * Q) - shiftPairTail b p q K K (c + (i + j') * Q)))

lemma norm_shiftPeelWeight (b p q Q c j j' K : ℕ) (t : ℝ) (i : ℕ) :
    ‖shiftPeelWeight b p q Q c j j' K t i‖ = 1 := norm_phase _

/-- **The exact `K`-digit decomposition of the shifted pair difference.** -/
theorem shiftPairDiff_eq_digitTrunc_add (b : ℕ) (hb : 2 ≤ b) (P p q c j j' K i : ℕ) :
    shiftPairDiff b P p q c j j' i
      = shiftDigitTrunc b p q (primorialLe P) c j j' K i
        + (shiftPairTail b p q K K (c + (i + j) * primorialLe P)
            - shiftPairTail b p q K K (c + (i + j') * primorialLe P)) / (b : ℝ) ^ K := by
  rw [shiftPairDiff_eq_pairTail, shiftDigitTrunc,
    pairTail_eq_digitTrunc_add b hb p q K (c + (i + j) * primorialLe P),
    pairTail_eq_digitTrunc_add b hb p q K (c + (i + j') * primorialLe P)]
  ring

/-- **The shifted pair phase factorises EXACTLY at every depth.** -/
theorem phase_shiftPairDiff_factor (b : ℕ) (hb : 2 ≤ b) (t : ℝ) (P p q c j j' K i : ℕ) :
    phase (t * shiftPairDiff b P p q c j j' i)
      = phase (t * shiftDigitTrunc b p q (primorialLe P) c j j' K i)
        * shiftPeelWeight b p q (primorialLe P) c j j' K t i := by
  have hb0 : (0 : ℝ) < (b : ℝ) := by
    have : (2 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
    linarith
  have hsplit : t * shiftPairDiff b P p q c j j' i
      = t * shiftDigitTrunc b p q (primorialLe P) c j j' K i
        + t / (b : ℝ) ^ K *
          (shiftPairTail b p q K K (c + (i + j) * primorialLe P)
            - shiftPairTail b p q K K (c + (i + j') * primorialLe P)) := by
    rw [shiftPairDiff_eq_digitTrunc_add b hb P p q c j j' K i]
    field_simp
  rw [hsplit, phase_add, shiftPeelWeight]

/-- **THE RATIFIED TARGET'S LEAF AT FIXED DEPTH.**  A `4K`-point root-of-unity correlation along
the progression, twisted by one unit-modulus weight.  No admissibility condition on `K`. -/
def ShiftTwoPointWeighted (b p q : ℕ) (t : ℝ) (K : ℕ) : Prop :=
  ∀ P c j j' : ℕ, j ≠ j' →
    Tendsto (fun R : ℕ =>
        ‖∑ i ∈ range R, phase (t * shiftDigitTrunc b p q (primorialLe P) c j j' K i)
          * shiftPeelWeight b p q (primorialLe P) c j j' K t i‖ / R) atTop (𝓝 0)

/-- **The leaf of the ratified target, at every fixed depth, as an equivalence.** -/
theorem shiftCorrSmall_iff_shiftTwoPointWeighted (b : ℕ) (hb : 2 ≤ b) (p q : ℕ) (t : ℝ)
    (K : ℕ) :
    ShiftCorrSmall b p q t ↔ ShiftTwoPointWeighted b p q t K := by
  have key : ∀ P c j j' R : ℕ,
      shiftCorr (largeProg b P p q t c) R j j'
        = ‖∑ i ∈ range R, phase (t * shiftDigitTrunc b p q (primorialLe P) c j j' K i)
            * shiftPeelWeight b p q (primorialLe P) c j j' K t i‖ := by
    intro P c j j' R
    rw [shiftCorr_largeProg]
    congr 1
    exact Finset.sum_congr rfl fun i _ => phase_shiftPairDiff_factor b hb t P p q c j j' K i
  constructor
  · intro h P c j j' hjj
    exact (h P c j j' hjj).congr fun R => by rw [key P c j j' R]
  · intro h P c j j' hjj
    exact (h P c j j' hjj).congr fun R => by rw [key P c j j' R]

/-- **`MultiElliott` — hence the ratified target's leaf — from a FIXED depth.** -/
theorem multiElliott_of_shiftTwoPointWeighted (b : ℕ) (hb : 2 ≤ b) (p q : ℕ) (t : ℝ) (K : ℕ)
    (h : ShiftTwoPointWeighted b p q t K) : MultiElliott b p q t :=
  (shiftCorrSmall_iff_multiElliott b hb p q t).mp
    ((shiftCorrSmall_iff_shiftTwoPointWeighted b hb p q t K).mpr h)

/-- **The ratified chain, on the fixed-depth weighted leaf.**  A new sufficient condition for
`shiftCorr_all` — and hence for `pairDecouple_all` — in which the depth is FIXED and may be `1`. -/
theorem shiftCorr_all_of_shiftTwoPointWeighted (K : ℕ)
    (h : ∀ b : ℕ, 3 ≤ b → ∀ m : ℤ, m ≠ 0 → ¬ ((b : ℤ) ∣ m) →
      ∀ p q : ℕ, p.Prime → q.Prime → p ≠ q →
        ShiftTwoPointWeighted b p q (((m : ℤ) : ℝ) / b) K) :
    ∀ b : ℕ, 3 ≤ b → ∀ m : ℤ, m ≠ 0 → ¬ ((b : ℤ) ∣ m) →
      ∀ p q : ℕ, p.Prime → q.Prime → p ≠ q → ShiftCorrSmall b p q (((m : ℤ) : ℝ) / b) :=
  fun b hb m hm hdvd p q hp hq hpq =>
    (shiftCorrSmall_iff_shiftTwoPointWeighted b (by omega) p q _ K).mpr
      (h b hb m hm hdvd p q hp hq hpq)

/-- **`PairDecouple` from the fixed-depth weighted leaf.**  The ratified target, reached with no
growing truncation depth anywhere in the chain. -/
theorem pairDecouple_all_of_shiftTwoPointWeighted (K : ℕ)
    (h : ∀ b : ℕ, 3 ≤ b → ∀ m : ℤ, m ≠ 0 → ¬ ((b : ℤ) ∣ m) →
      ∀ p q : ℕ, p.Prime → q.Prime → p ≠ q →
        ShiftTwoPointWeighted b p q (((m : ℤ) : ℝ) / b) K) :
    ∀ b : ℕ, 3 ≤ b → ∀ m : ℤ, m ≠ 0 → ¬ ((b : ℤ) ∣ m) →
      ∀ p q : ℕ, p.Prime → q.Prime → p ≠ q → PairDecouple b p q (((m : ℤ) : ℝ) / b) :=
  fun b hb m hm hdvd p q hp hq hpq =>
    pairDecouple_of_largeDecay b p q _ (largeDecay_of_shiftCorr b p q _
      (shiftCorr_all_of_shiftTwoPointWeighted K h b hb m hm hdvd p q hp hq hpq))

end NormalNumbers.CastingOut
