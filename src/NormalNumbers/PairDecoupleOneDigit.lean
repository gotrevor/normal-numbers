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

/-! ### The `K`-fold peel: an EXACT factorisation at every depth

Iterating the peel gives, for **every** `K` and with no error term,

`pairTail = digitTrunc_K + b^{−K}·(θ_{pn+K} − θ_{qn+K})`,

so the pair phase is the `2K`-point root-of-unity product times a unit-modulus weight.  In
particular the leaf needs **no admissibility condition on `K`**: the depth may be held FIXED
(`K = 1` included), and the whole `AdmissibleTrunc` / `log_b log log R` apparatus — which existed
only to make the discarded digits *small* — is bypassed. -/

/-- **The exact `K`-digit decomposition.**  Proved by induction from the one-digit peel alone. -/
theorem pairTail_eq_digitTrunc_add (b : ℕ) (hb : 2 ≤ b) (p q K n : ℕ) :
    pairTail b p q n
      = digitTrunc b p q K n + shiftPairTail b p q K K n / (b : ℝ) ^ K := by
  have hb0 : (0 : ℝ) < (b : ℝ) := by
    have : (2 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
    linarith
  induction K with
  | zero => simp [digitTrunc, shiftPairTail_zero]
  | succ K ih =>
      have hpeel := shiftPairTail_peel b hb p q K K n
      have hd : digitTrunc b p q (K + 1) n
          = digitTrunc b p q K n
            + ((omegaNat (p * n + 1 + K) : ℝ) - (omegaNat (q * n + 1 + K) : ℝ))
              / (b : ℝ) ^ (K + 1) := by
        rw [digitTrunc, digitTrunc, Finset.sum_range_succ]
      have he1 : p * n + K + 1 = p * n + 1 + K := by omega
      have he2 : q * n + K + 1 = q * n + 1 + K := by omega
      rw [he1, he2] at hpeel
      rw [ih, hd]
      have hbK : ((b : ℝ) ^ K) ≠ 0 := by positivity
      field_simp
      linear_combination ((b:ℝ)^K) * hpeel

/-- The unit-modulus weight left by the `K`-fold peel. -/
noncomputable def peelWeightAt (b p q K : ℕ) (t : ℝ) (n : ℕ) : ℂ :=
  phase (t / (b : ℝ) ^ K * shiftPairTail b p q K K n)

lemma norm_peelWeightAt (b p q K : ℕ) (t : ℝ) (n : ℕ) : ‖peelWeightAt b p q K t n‖ = 1 :=
  norm_phase _

lemma peelWeightAt_one (b p q : ℕ) (t : ℝ) (n : ℕ) :
    peelWeightAt b p q 1 t n = peelWeight b p q t n := by
  rw [peelWeightAt, peelWeight, pow_one]

/-- **The pair phase factorises EXACTLY at every depth.**  `2K` root-of-unity powers of `ω` along
the forms `pn+1+k`, `qn+1+k`, times one unit-modulus weight. -/
theorem phase_pairTail_factor (b : ℕ) (hb : 2 ≤ b) (t : ℝ) (p q K n : ℕ) :
    phase (t * pairTail b p q n)
      = (∏ k ∈ range K, (digitRoot b t k ^ omegaNat (p * n + 1 + k)
          * (starRingEnd ℂ) (digitRoot b t k ^ omegaNat (q * n + 1 + k))))
        * peelWeightAt b p q K t n := by
  have hb0 : (0 : ℝ) < (b : ℝ) := by
    have : (2 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
    linarith
  have hsplit : t * pairTail b p q n
      = t * digitTrunc b p q K n + t / (b : ℝ) ^ K * shiftPairTail b p q K K n := by
    rw [pairTail_eq_digitTrunc_add b hb p q K n]
    field_simp
  rw [hsplit, phase_add, phase_digitTrunc, peelWeightAt]

/-- **THE LEAF AT FIXED DEPTH `K`.**  A `2K`-point Elliott correlation twisted by one
unit-modulus weight.  `K = 1` is `TwoPointWeighted`. -/
def MultiElliottWeighted (b p q K : ℕ) (t : ℝ) : Prop :=
  Tendsto (fun R => fullMean (fun n =>
    (∏ k ∈ range K, (digitRoot b t k ^ omegaNat (p * n + 1 + k)
      * (starRingEnd ℂ) (digitRoot b t k ^ omegaNat (q * n + 1 + k))))
      * peelWeightAt b p q K t n) R) atTop (𝓝 0)

/-- **The crux, at EVERY fixed depth, as an equivalence.**  No admissibility hypothesis on `K`:
the identity is exact, so depth `1` is as good as depth `R`. -/
theorem pairDecorr_iff_multiElliottWeighted (b : ℕ) (hb : 2 ≤ b) (t : ℝ) (K : ℕ) :
    PairDecorr b t ↔
      ∀ p q : ℕ, p.Prime → q.Prime → p ≠ q → MultiElliottWeighted b p q K t := by
  have hcongr : ∀ p q : ℕ, ∀ R : ℕ,
      fullMean (fun n => phase (t * (omegaTail b (p * n) - omegaTail b (q * n)))) R
        = fullMean (fun n =>
            (∏ k ∈ range K, (digitRoot b t k ^ omegaNat (p * n + 1 + k)
              * (starRingEnd ℂ) (digitRoot b t k ^ omegaNat (q * n + 1 + k))))
              * peelWeightAt b p q K t n) R := by
    intro p q R
    refine congrArg (fun z => z / (R : ℂ)) (Finset.sum_congr rfl fun n _ => ?_)
    dsimp only
    rw [← phase_pairTail_factor b hb t p q K n, pairTail]
  constructor
  · intro h p q hp hq hpq
    exact ((h p q hp hq hpq).congr (hcongr p q))
  · intro h p q hp hq hpq
    exact ((h p q hp hq hpq).congr fun R => (hcongr p q R).symm)

/-- **All depths are equivalent.**  A direct corollary: whatever depth the literature can reach,
it reaches the crux. -/
theorem multiElliottWeighted_depth_indep (b : ℕ) (hb : 2 ≤ b) (t : ℝ) (K L : ℕ)
    (h : ∀ p q : ℕ, p.Prime → q.Prime → p ≠ q → MultiElliottWeighted b p q K t) :
    ∀ p q : ℕ, p.Prime → q.Prime → p ≠ q → MultiElliottWeighted b p q L t :=
  (pairDecorr_iff_multiElliottWeighted b hb t L).mp
    ((pairDecorr_iff_multiElliottWeighted b hb t K).mpr h)

/-- **The swing at any fixed depth.** -/
theorem conjC1_of_delange_katai_multiElliottWeighted (K : ℕ) (hDK : KataiOrthogonality)
    (hD : ∀ b : ℕ, 3 ≤ b → ∀ m : ℤ, m ≠ 0 → ¬ ((b : ℤ) ∣ m) → DelangeMean (((m : ℤ) : ℝ) / b))
    (hP : ∀ b : ℕ, 3 ≤ b → ∀ m : ℤ, m ≠ 0 → ¬ ((b : ℤ) ∣ m) →
      ∀ p q : ℕ, p.Prime → q.Prime → p ≠ q → MultiElliottWeighted b p q K (((m : ℤ) : ℝ) / b)) :
    ConjC1 :=
  conjC1_of_delange_katai hDK hD fun b hb m hm hdvd =>
    (pairDecorr_iff_multiElliottWeighted b (by omega) _ K).mpr (hP b hb m hm hdvd)

end NormalNumbers.CastingOut
