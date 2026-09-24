import NormalNumbers.PairDecoupleAvg

/-!
# `K = 1`, EXACTLY: the crux is a weighted TWO-point correlation, with no truncation error

Directive item 3 ("try to reach `K = 1`"), attacked head-on.

The obstruction recorded against `K = 1` was that the discarded digits are not small:
`E |pairTail − digitTrunc₁| ≍ b^{−1}√(log log R) → ∞` (lap 21's Turán bound makes this exact).
That obstruction is an artefact of *approximating*.  The carry recursion `omegaTail_rec`
(`b·θ_N = ω(N+1) + θ_{N+1}`) gives an **exact** one-digit peel of the pair difference, with no
error term at all:

`t · (θ_{pn+u} − θ_{qn+v}) = (t/b)·(ω(pn+u+1) − ω(qn+v+1)) + (t/b)·(θ_{pn+u+1} − θ_{qn+v+1})`.

Exponentiating, the crux `PairDecorr b t` is **literally** — as an equality of sequences, not an
approximation — the two-point correlation of the non-pretentious multiplicative function
`ζ^ω`, `ζ = e(t/b)`, along the forms `pn+1`, `qn+1`, *twisted by a bounded weight* `W` which is
itself the phase of the once-shifted pair difference at the `b`-times smaller frequency.

So the status of `K = 1` changes: it is not blocked by an unbounded truncation error, it is
blocked by the presence of the weight `W`.  Tao's theorem (*Forum of Math Pi* **4** (2016)) is
exactly the unweighted case of `TwoPointWeighted` in logarithmic average.  What has to be added
is the weight — a strictly better-posed target than "a `2K`-point correlation with `K → ∞`".

Nothing here is an approximation: `pairDecorr_iff_twoPointWeighted` is an *equivalence* proved
from an identity.
-/

open Finset Filter Topology

namespace NormalNumbers.CastingOut

/-- The pair difference of the orbit at independently shifted multiplicative indices. -/
noncomputable def shiftPairTail (b p q u v n : ℕ) : ℝ :=
  omegaTail b (p * n + u) - omegaTail b (q * n + v)

lemma shiftPairTail_zero (b p q n : ℕ) : shiftPairTail b p q 0 0 n = pairTail b p q n := by
  rw [shiftPairTail, pairTail, Nat.add_zero, Nat.add_zero]

/-- **The exact one-digit peel.**  No truncation, no error term: the carry recursion moves one
digit out of the pair difference and divides the frequency by `b`. -/
theorem shiftPairTail_peel (b : ℕ) (hb : 2 ≤ b) (p q u v n : ℕ) :
    (b : ℝ) * shiftPairTail b p q u v n
      = ((omegaNat (p * n + u + 1) : ℝ) - (omegaNat (q * n + v + 1) : ℝ))
        + shiftPairTail b p q (u + 1) (v + 1) n := by
  have h1 := omegaTail_rec b hb (p * n + u)
  have h2 := omegaTail_rec b hb (q * n + v)
  have e1 : p * n + (u + 1) = p * n + u + 1 := by omega
  have e2 : q * n + (v + 1) = q * n + v + 1 := by omega
  rw [shiftPairTail, shiftPairTail, e1, e2, mul_sub, h1, h2]
  ring

/-- **The peel, on the phase.**  `e(t·D_{u,v}) = ζ^{ω(pn+u+1)} · conj(ζ^{ω(qn+v+1)}) · e((t/b)·D_{u+1,v+1})`
with `ζ = e(t/b)`.  An identity of sequences. -/
theorem phase_shiftPairTail_peel (b : ℕ) (hb : 2 ≤ b) (t : ℝ) (p q u v n : ℕ) :
    phase (t * shiftPairTail b p q u v n)
      = phase (t / b * (omegaNat (p * n + u + 1) : ℝ))
        * (starRingEnd ℂ) (phase (t / b * (omegaNat (q * n + v + 1) : ℝ)))
        * phase (t / b * shiftPairTail b p q (u + 1) (v + 1) n) := by
  have hb0 : (b : ℝ) ≠ 0 := by
    have : (2 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
    intro h; rw [h] at this; linarith
  have hpeel := shiftPairTail_peel b hb p q u v n
  have hsplit : t * shiftPairTail b p q u v n
      = t / b * (omegaNat (p * n + u + 1) : ℝ)
        - t / b * (omegaNat (q * n + v + 1) : ℝ)
        + t / b * shiftPairTail b p q (u + 1) (v + 1) n := by
    field_simp
    linear_combination t * hpeel
  rw [hsplit, phase_add, ← phase_mul_conj_phase]

/-- `ζ^ω` in root-of-unity form: the peel really is a multiplicative function of the linear
form. -/
lemma phase_omegaNat_pow (t : ℝ) (m : ℕ) :
    phase (t * (omegaNat m : ℝ)) = phase t ^ omegaNat m := by
  rw [mul_comm, phase_nat_mul]

/-! ### The `K = 1` leaf -/

/-- The bounded weight left behind by one peel: the phase of the once-shifted pair difference at
the `b`-times smaller frequency. -/
noncomputable def peelWeight (b p q : ℕ) (t : ℝ) (n : ℕ) : ℂ :=
  phase (t / b * shiftPairTail b p q 1 1 n)

lemma norm_peelWeight (b p q : ℕ) (t : ℝ) (n : ℕ) : ‖peelWeight b p q t n‖ = 1 :=
  norm_phase _

/-- **THE `K = 1` LEAF.**  A genuine TWO-point Elliott correlation of `ζ^ω`, `ζ = e(t/b)`, along
the forms `pn+1` and `qn+1` — twisted by the bounded weight `peelWeight`.  Tao 2016 is exactly
the case `peelWeight ≡ 1`, in logarithmic average. -/
def TwoPointWeighted (b p q : ℕ) (t : ℝ) : Prop :=
  Tendsto (fun R => fullMean (fun n =>
    phase (t / b) ^ omegaNat (p * n + 1)
      * (starRingEnd ℂ) (phase (t / b) ^ omegaNat (q * n + 1))
      * peelWeight b p q t n) R) atTop (𝓝 0)

lemma pairPhase_eq_twoPoint (b : ℕ) (hb : 2 ≤ b) (t : ℝ) (p q n : ℕ) :
    phase (t * pairTail b p q n)
      = phase (t / b) ^ omegaNat (p * n + 1)
        * (starRingEnd ℂ) (phase (t / b) ^ omegaNat (q * n + 1))
        * peelWeight b p q t n := by
  rw [← shiftPairTail_zero, phase_shiftPairTail_peel b hb t p q 0 0 n, peelWeight]
  simp only [Nat.add_zero, phase_omegaNat_pow]

/-- **`K = 1`, as an EQUIVALENCE.**  The crux is not *approximated* by a two-point correlation —
it *is* one, weighted.  No truncation error is spent, so the `b^{−1}√(log log R)` obstruction
that blocked the `L¹` route to `K = 1` does not arise. -/
theorem pairDecorr_iff_twoPointWeighted (b : ℕ) (hb : 2 ≤ b) (t : ℝ) :
    PairDecorr b t ↔
      ∀ p q : ℕ, p.Prime → q.Prime → p ≠ q → TwoPointWeighted b p q t := by
  constructor
  · intro h p q hp hq hpq
    have := h p q hp hq hpq
    refine this.congr fun R => ?_
    refine congrArg (fun z => z / (R : ℂ)) ?_
    refine Finset.sum_congr rfl fun n _ => ?_
    dsimp only
    rw [← pairPhase_eq_twoPoint b hb t p q n, pairTail]
  · intro h p q hp hq hpq
    have := h p q hp hq hpq
    refine this.congr fun R => ?_
    refine congrArg (fun z => z / (R : ℂ)) ?_
    refine Finset.sum_congr rfl fun n _ => ?_
    dsimp only
    rw [← pairPhase_eq_twoPoint b hb t p q n, pairTail]

/-- **The swing on the `K = 1` leaf.**  `ConjC1` from Delange, Kátai/BSZ, and a *two-point*
weighted correlation. -/
theorem conjC1_of_delange_katai_twoPointWeighted (hDK : KataiOrthogonality)
    (hD : ∀ b : ℕ, 3 ≤ b → ∀ m : ℤ, m ≠ 0 → ¬ ((b : ℤ) ∣ m) → DelangeMean (((m : ℤ) : ℝ) / b))
    (hP : ∀ b : ℕ, 3 ≤ b → ∀ m : ℤ, m ≠ 0 → ¬ ((b : ℤ) ∣ m) →
      ∀ p q : ℕ, p.Prime → q.Prime → p ≠ q → TwoPointWeighted b p q (((m : ℤ) : ℝ) / b)) :
    ConjC1 :=
  conjC1_of_delange_katai hDK hD fun b hb m hm hdvd =>
    (pairDecorr_iff_twoPointWeighted b (by omega) _).mpr (hP b hb m hm hdvd)

end NormalNumbers.CastingOut
