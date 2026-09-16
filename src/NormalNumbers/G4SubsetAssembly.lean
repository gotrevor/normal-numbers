/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.G4SchedBEAssembly

/-!
# Campaign A, the headline: `c_S(b) = ∑_n ω_S(n)/bⁿ` is disjunctive in base `b ≥ 3`

Given a **Mertens rate** for the prime set `S` — `c·log log N − C ≤ ∑_{p < N, p ∈ S} 1/p` for
some `c > 0` and any `C` — every omitted base-`b` cylinder gets a schedule witness, so
`subsetLambert S b` is disjunctive.

The two free parameters of the schedule absorb the `S`-loss:

* the **outer dimension** `K = 4k₄` may be enlarged beyond the `(b, ℓ)`-forced `Kbℓ b ℓ`
  (`SchedB.hyp_KG`, `SchedB.KG_ge`), which is what makes the cap `Dc ≤ 2^K` reachable for any
  fixed rate `c`;
* the **cutoff exponent** `e` is free above `m₁ b K` (`SchedB.HypE`), and
  `MertensAP.exists_cutoff_subset` buys the schedule's Mertens demand at an exponent inflated
  by the constant factor `Dc ≈ 1/(c log 2)`, which `MertensAP.moment_cap_subset` then checks
  against the moment cap `10⁵·T K·e ≤ 2^{8K²}`.

Specialized to `S = {p : p ≡ a mod q}` with `a` a unit, the rate is
`MertensAP.mertensRate_residueClass` (Mertens in arithmetic progressions, assembled in
`G4MertensAP`), giving `isDisjunctive_residueClass`.
-/

open Finset Real
open scoped BigOperators

namespace NormalNumbers.G4

open PrimeLambert GridParams

variable (S : ℕ → Prop) [DecidablePred S]

lemma smallPrimes_mono {R R' P₀ : ℕ} (h : R ≤ R') : smallPrimes R P₀ ⊆ smallPrimes R' P₀ := by
  intro p hp
  rw [mem_smallPrimes] at hp ⊢
  exact ⟨hp.1, hp.2.1.trans h, hp.2.2⟩

/-- **The schedule witness from a Mertens rate.**  For every base `b ≥ 3`, every cylinder depth
`ℓ ≥ 1` and every word `w`, a rate for `S` produces `ScheduleWitnessS S b ℓ w`. -/
theorem exists_scheduleWitnessS {c C : ℝ} (hmert : MertensAP.MertensRate S c C)
    (b ℓ w : ℕ) (hb : 3 ≤ b) (hℓ : 1 ≤ ℓ) : Nonempty (ScheduleWitnessS S b ℓ w) := by
  classical
  obtain ⟨hc, -⟩ := id hmert
  have hl2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hl2' : Real.log 2 ≤ 1 := by linarith [Real.log_two_lt_d9]
  set X : ℝ := (24 + max C 0 + c) / (c * Real.log 2) with hX
  have hX0 : 0 < X := by rw [hX]; have : (0:ℝ) ≤ max C 0 := le_max_right _ _; positivity
  set Dc : ℕ := ⌈X + 1⌉₊ with hDc
  have hDcge : X + 1 ≤ (Dc : ℝ) := Nat.le_ceil _
  have hDc1 : 1 ≤ Dc := by
    have : (1 : ℝ) ≤ (Dc : ℝ) := by linarith
    exact_mod_cast this
  set k₄ : ℕ := max (SchedB.k₄bℓ b ℓ) Dc with hk₄
  have hk : SchedB.k₄bℓ b ℓ ≤ k₄ := le_max_left _ _
  have hDck : Dc ≤ k₄ := le_max_right _ _
  set K : ℕ := 4 * k₄ with hKdef
  have h : SchedB.Hyp b K := SchedB.hyp_KG hb hℓ hk
  have hK100 : 100 ≤ K := h.hK
  -- the cutoff exponent supplied by the rate
  obtain ⟨e₀, hsum₀, hbnd₀⟩ := MertensAP.exists_cutoff_subset hmert hK100 (SchedB.m₁ b K)
  set e : ℕ := max e₀ (SchedB.m₁ b K) with hedef
  have hlo : SchedB.m₁ b K ≤ e := le_max_right _ _
  have he₀e : e₀ ≤ e := le_max_left _ _
  -- the cap
  have hDle : Dc ≤ 2 ^ K := by
    calc Dc ≤ k₄ := hDck
      _ ≤ 2 ^ k₄ := (Nat.lt_two_pow_self).le
      _ ≤ 2 ^ K := Nat.pow_le_pow_right (by norm_num) (by omega)
  set A : ℕ := SchedB.m₁ b K + K ^ 2 + 1 with hAdef
  have hA1 : (1 : ℝ) ≤ (A : ℝ) := by
    have : 1 ≤ A := by omega
    exact_mod_cast this
  have hA0 : (0 : ℝ) < (A : ℝ) := by linarith
  have hm₁A : (SchedB.m₁ b K : ℝ) ≤ (A : ℝ) := by
    have : SchedB.m₁ b K ≤ A := by omega
    exact_mod_cast this
  have hKA : ((K : ℝ)) ^ 2 ≤ (A : ℝ) := by
    have : K ^ 2 ≤ A := by omega
    have h' : ((K ^ 2 : ℕ) : ℝ) ≤ (A : ℝ) := by exact_mod_cast this
    push_cast at h'; linarith
  have hm₁0 : (0 : ℝ) ≤ (SchedB.m₁ b K : ℝ) := by positivity
  have hCmax : C ≤ max C 0 := le_max_left _ _
  have hCmax0 : (0 : ℝ) ≤ max C 0 := le_max_right _ _
  -- `e₀ ≤ Dc · A`
  have hQ : ((SchedB.m₁ b K : ℝ) * Real.log 2 + 21 * (K : ℝ) ^ 2 + 2 + C + c)
      ≤ (A : ℝ) * (24 + max C 0 + c) := by
    have h1 : (SchedB.m₁ b K : ℝ) * Real.log 2 ≤ (A : ℝ) := by nlinarith
    have h2 : 21 * (K : ℝ) ^ 2 ≤ 21 * (A : ℝ) := by linarith
    have h3 : (2 : ℝ) ≤ 2 * (A : ℝ) := by linarith
    have h4 : C ≤ max C 0 * (A : ℝ) := by nlinarith
    have h5 : c ≤ c * (A : ℝ) := by nlinarith
    nlinarith
  have hbnd : (e₀ : ℝ) ≤ (Dc : ℝ) * (A : ℝ) := by
    have hdiv : ((SchedB.m₁ b K : ℝ) * Real.log 2 + 21 * (K : ℝ) ^ 2 + 2 + C + c)
        / (c * Real.log 2) ≤ (A : ℝ) * X := by
      rw [hX, ← mul_div_assoc, div_le_div_iff₀ (by positivity) (by positivity)]
      exact mul_le_mul_of_nonneg_right hQ (by positivity)
    have hmax : max 0 (((SchedB.m₁ b K : ℝ) * Real.log 2 + 21 * (K : ℝ) ^ 2 + 2 + C + c)
        / (c * Real.log 2)) ≤ (A : ℝ) * X := by
      refine max_le ?_ hdiv
      positivity
    have : (e₀ : ℝ) ≤ (A : ℝ) * X + 1 := by linarith
    nlinarith
  have hele : e ≤ Dc * A := by
    have h1 : e₀ ≤ Dc * A := by
      have : (e₀ : ℝ) ≤ ((Dc * A : ℕ) : ℝ) := by push_cast; linarith
      exact_mod_cast this
    have h2 : SchedB.m₁ b K ≤ Dc * A := by
      calc SchedB.m₁ b K ≤ A := by omega
        _ ≤ Dc * A := Nat.le_mul_of_pos_left _ (by omega)
    omega
  have hhi : SchedB.McE K e ≤ 2 ^ Sched.m₂ K :=
    MertensAP.moment_cap_subset hb h.hbK hK100 hDle hele
  have hE : SchedB.HypE b K e := ⟨h, hlo, hhi⟩
  -- the Mertens supply at the enlarged cutoff
  have hlow : (SchedB.m₁ b K : ℝ) * Real.log 2 - 21 * (K : ℝ) ^ 2 - 4
      ≤ ∑ p ∈ (smallPrimes (SchedB.RE e)
          (gridOf K (Sched.N K) hE.hK1).P₀).filter S, (p : ℝ)⁻¹ := by
    refine hsum₀.trans ?_
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun p _ _ => by positivity)
    intro p hp
    rw [Finset.mem_filter] at hp ⊢
    exact ⟨smallPrimes_mono (Nat.pow_le_pow_right (by norm_num)
      (Nat.pow_le_pow_right (by norm_num) he₀e)) hp.1, hp.2⟩
  exact ⟨SchedB.scheduleWitnessSE S b ℓ w e k₄ hb hℓ hk hE hlow⟩

/-- **Campaign A's headline.**  If the primes of `S` have a Mertens rate — in particular if
`∑_{p ∈ S} 1/p` diverges at the Mertens speed — then `c_S(b) = ∑_n ω_S(n)/bⁿ` is disjunctive in
every base `b ≥ 3`. -/
theorem isDisjunctive_subsetLambert {c C : ℝ} (hmert : MertensAP.MertensRate S c C)
    {b : ℕ} (hb : 3 ≤ b) : IsDisjunctive b (subsetLambert S b) := by
  refine isDisjunctive_subsetLambert_of_witness S b (by omega) fun ℓ w hw homit => ?_
  rcases Nat.eq_zero_or_pos ℓ with hℓ | hℓ
  · exfalso
    subst hℓ
    have hw0 : w = 0 := by simpa using hw
    subst hw0
    have := homit 0
    simp only [Nat.cast_zero, pow_zero, zero_add, div_one] at this
    exact this (orbit_mem_Ico b (subsetLambert S b) 0)
  · exact exists_scheduleWitnessS S hmert b ℓ w hb hℓ

/-! ### Instances -/

/-- The full prime set has a Mertens rate: `log log N − 1 ≤ ∑_{p < N} 1/p` (`G4Mertens`). -/
theorem mertensRate_univ : MertensAP.MertensRate (fun _ => True) 1 1 := by
  refine ⟨one_pos, fun N hN => ?_⟩
  have h := log_log_le_sum_inv_primesBelow N hN
  have heq : MertensAP.sumInvPrimesIn (fun _ => True) N = ∑ p ∈ N.primesBelow, (p : ℝ)⁻¹ := by
    unfold MertensAP.sumInvPrimesIn; simp
  rw [heq, one_mul]
  linarith

/-- **Sanity instance.**  At `S = everything` the prime-subset theorem re-derives
`isDisjunctive_base`: `∑_n ω(n)/bⁿ` is disjunctive in base `b ≥ 3`. -/
theorem isDisjunctive_subsetLambert_univ {b : ℕ} (hb : 3 ≤ b) :
    IsDisjunctive b (primeLambertAtBase b) := by
  have h := isDisjunctive_subsetLambert (fun _ => True) mertensRate_univ hb
  rwa [subsetLambert_univ] at h

/-- **The arithmetic-progression instance.**  For a unit `a` mod `q`, the constant
`c_{q,a}(b) = ∑_n #{p ≡ a (q) : p ∣ n}/bⁿ = ∑_{p ≡ a (q)} 1/(b^p − 1)` is disjunctive in every
base `b ≥ 3`.  The prime-set input is Mertens in arithmetic progressions
(`MertensAP.mertensRate_residueClass`), itself built from mathlib's
`vonMangoldt.LSeries_residueClass_lower_bound`. -/
theorem isDisjunctive_residueClass {q : ℕ} [NeZero q] {a : ZMod q} (ha : IsUnit a)
    {b : ℕ} (hb : 3 ≤ b) :
    IsDisjunctive b (subsetLambert (fun p => (p : ZMod q) = a) b) := by
  obtain ⟨c, C, hmert⟩ := MertensAP.mertensRate_residueClass ha
  exact isDisjunctive_subsetLambert _ hmert hb

/-- The residue-class constant in its closed prime-sum form: `∑_{p ≡ a (q)} 1/(b^p − 1)`. -/
theorem isDisjunctive_residueClass_primeSum {q : ℕ} [NeZero q] {a : ZMod q} (ha : IsUnit a)
    {b : ℕ} (hb : 3 ≤ b) :
    IsDisjunctive b
      (∑' p : ℕ, (if p.Prime ∧ (p : ZMod q) = a then 1 / ((b : ℝ) ^ p - 1) else 0)) := by
  have h := isDisjunctive_residueClass ha hb
  rwa [subsetLambert_eq_tsum_inv (S := fun p => (p : ZMod q) = a) (b := b) (by omega)] at h

end NormalNumbers.G4
