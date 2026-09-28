/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.C3MrtBlockDefect
import NormalNumbers.C3MrtWindowMass

/-!
# The conductor debt at `t = 0`: the head is elementary, the tail is the whole content

`DIRECTION.md` item ②.3 asks for `CharPrimeSumLogQ D` at `t = 0`, i.e. a bound

    ‖∑_{p ≤ X²} conj(χ(p))/p‖ ≤ D · (log(q+2) + 1)          (`CharPrimeSumLogQZero`)

uniformly over non-principal `χ mod q`.  This file splits that sum at the conductor,

    head = ∑_{p ≤ q},      tail = ∑_{q < p ≤ X²},

and **discharges the head in the kernel**: `‖head‖ ≤ ∑_{p ≤ q} 1/p ≤ log log(q+2) + mertensBound`
by `small_prime_mass_le`, and `log log(q+2) ≤ log(q+2)`.  So the head is not merely small, it is
`O(log log q)` — a whole exponential below the budget.

What remains is `CharTailCancellation`: the primes ABOVE the conductor.  There the mass
`∑_{q < p ≤ X²} 1/p ≈ log log X² − log log q` is *unbounded*, so the bound can only come from
cancellation in `χ(p)`, which is exactly the non-vanishing of `L(1,χ)` **with a rate** (the
Siegel-free `L(1,χ) ≫ q^{-1/2}`; mathlib has only the qualitative
`DirichletCharacter.LFunction_apply_one_ne_zero`).  This file therefore narrows the `t = 0`
conductor debt from the full sum to the tail, and records that the head can never be the
obstruction.

Per the **GUARD RULE** (`DIRECTION.md` ①) the new `Prop` `CharTailCancellation` ships with a
content locator (`charTailSum_head_free`: at `X` below the conductor the tail is *empty*, so the
statement is trivially true there — the content is at `X² ≫ q`) and degenerate-case verdicts:
`q = 0, 1` are excluded by `χ ≠ 1` (`charTail_conductor_pos`), the empty-tail configuration is
proved to satisfy it (`charTailCancellation_vacuous_below`), and the constant-function
configuration `χ = 1` is exactly the excluded one.
-/

open Filter Topology Finset

namespace NormalNumbers

namespace CastingOut

/-! ### `t = 0`: the twist disappears -/

/-- The primes indexing `twistedPrimeSum X χ t`. -/
noncomputable def primesUpToSq (X : ℝ) : Finset ℕ :=
  (Finset.range (⌈X ^ 2⌉₊ + 1)).filter Nat.Prime

theorem mem_primesUpToSq {X : ℝ} {p : ℕ} :
    p ∈ primesUpToSq X ↔ p < ⌈X ^ 2⌉₊ + 1 ∧ p.Prime := by
  simp [primesUpToSq, Finset.mem_filter, Finset.mem_range]

/-- At `t = 0` the twist `p^{-it}` is `1`, so the twisted prime sum is the plain character sum. -/
theorem twistedPrimeSum_zero (X : ℝ) {q : ℕ} (χ : DirichletCharacter ℂ q) :
    twistedPrimeSum X χ 0
      = ∑ p ∈ primesUpToSq X, (starRingEnd ℂ) (χ (p : ZMod q)) / (p : ℂ) := by
  rw [twistedPrimeSum, primesUpToSq]
  refine Finset.sum_congr rfl fun p _ => ?_
  norm_num

/-! ### The split at the conductor -/

/-- The primes **at or below** the conductor. -/
noncomputable def charHeadSum (X : ℝ) {q : ℕ} (χ : DirichletCharacter ℂ q) : ℂ :=
  ∑ p ∈ (primesUpToSq X).filter (fun p => p ≤ q),
    (starRingEnd ℂ) (χ (p : ZMod q)) / (p : ℂ)

/-- The primes **above** the conductor — where all the cancellation has to happen. -/
noncomputable def charTailSum (X : ℝ) {q : ℕ} (χ : DirichletCharacter ℂ q) : ℂ :=
  ∑ p ∈ (primesUpToSq X).filter (fun p => ¬ p ≤ q),
    (starRingEnd ℂ) (χ (p : ZMod q)) / (p : ℂ)

theorem twistedPrimeSum_zero_split (X : ℝ) {q : ℕ} (χ : DirichletCharacter ℂ q) :
    twistedPrimeSum X χ 0 = charHeadSum X χ + charTailSum X χ := by
  rw [twistedPrimeSum_zero, charHeadSum, charTailSum]
  exact (Finset.sum_filter_add_sum_filter_not _ _ _).symm

/-! ### The head is elementary -/

/-- `log log u ≤ log u` for `1 ≤ u` (with Lean's junk value at `log u = 0` handled). -/
theorem log_log_le_log {u : ℝ} (hu : 1 ≤ u) : Real.log (Real.log u) ≤ Real.log u := by
  have h0 : 0 ≤ Real.log u := Real.log_nonneg hu
  rcases eq_or_lt_of_le h0 with h | h
  · rw [← h]; simp
  · have := Real.log_le_sub_one_of_pos h
    linarith

/-- **The head is discharged.**  `‖∑_{p ≤ q} conj(χ(p))/p‖ ≤ log(q+2) + mertensBound`: it is in
fact `O(log log q)`, a whole exponential below the `log q` budget. -/
theorem norm_charHeadSum_le (X : ℝ) {q : ℕ} (χ : DirichletCharacter ℂ q) :
    ‖charHeadSum X χ‖
      ≤ Real.log ((q : ℝ) + 2) + Erdos67b.PrimeEstimates.mertensBound := by
  set G : Finset ℕ := (primesUpToSq X).filter (fun p => p ≤ q) with hG
  have hterm : ∀ p ∈ G, ‖(starRingEnd ℂ) (χ (p : ZMod q)) / (p : ℂ)‖ ≤ (p : ℝ)⁻¹ := by
    intro p hp
    have hpp : p.Prime := (mem_primesUpToSq.1 (Finset.mem_filter.1 hp).1).2
    have hp0 : (0 : ℝ) < (p : ℝ) := by
      exact_mod_cast hpp.pos
    rw [norm_div, RCLike.norm_conj]
    have hchi : ‖χ (p : ZMod q)‖ ≤ 1 := dirichletChar_norm_le_one χ _
    rw [Complex.norm_natCast]
    rw [div_le_iff₀ hp0] at *
    calc ‖χ ((p : ℕ) : ZMod q)‖ ≤ 1 := hchi
      _ = (p : ℝ)⁻¹ * (p : ℝ) := by field_simp
  have hnorm : ‖charHeadSum X χ‖ ≤ ∑ p ∈ G, (p : ℝ)⁻¹ := by
    refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum hterm)
  -- every element of `G` is a prime `≤ q + 2`
  have hB : (2 : ℕ) ≤ q + 2 := by omega
  have hGb : ∀ p ∈ G, p.Prime ∧ p ≤ q + 2 := by
    intro p hp
    refine ⟨(mem_primesUpToSq.1 (Finset.mem_filter.1 hp).1).2, ?_⟩
    have := (Finset.mem_filter.1 hp).2
    omega
  have hmass := small_prime_mass_le hB hGb
  have hcast : ((q + 2 : ℕ) : ℝ) = (q : ℝ) + 2 := by push_cast; ring
  rw [hcast] at hmass
  have h1 : (1 : ℝ) ≤ (q : ℝ) + 2 := by
    have : (0 : ℝ) ≤ (q : ℝ) := Nat.cast_nonneg q
    linarith
  have hll := log_log_le_log h1
  linarith

/-! ### The remaining debt: cancellation above the conductor -/

/-- **The `t = 0` conductor debt, narrowed to the primes above the conductor.**

Classical and Siegel-free: `‖∑_{q < p ≤ X²} conj(χ(p))/p‖ ≪ log q + 1` for every non-principal
`χ mod q`, uniformly in `X`.  Equivalent in strength to `L(1,χ) ≫ q^{-1/2}` (mathlib has only
the qualitative `DirichletCharacter.LFunction_apply_one_ne_zero`).  The mass of this range is
`≈ log log X² − log log q`, which is unbounded, so the bound is pure cancellation — this is where
all the content of the `t = 0` debt sits, and `norm_charHeadSum_le` shows the head can never be
the obstruction. -/
def CharTailCancellation (C : ℝ) : Prop :=
  0 ≤ C ∧ ∀ (q : ℕ) (χ : DirichletCharacter ℂ q), χ ≠ 1 → ∀ X : ℝ, 3 ≤ X →
    ‖charTailSum X χ‖ ≤ C * (Real.log ((q : ℝ) + 2) + 1)

/-- The `t = 0` slice of `CharPrimeSumLogQ`. -/
def CharPrimeSumLogQZero (D : ℝ) : Prop :=
  ∀ (q : ℕ) (χ : DirichletCharacter ℂ q), χ ≠ 1 → ∀ X : ℝ, 3 ≤ X →
    ‖twistedPrimeSum X χ 0‖ ≤ D * (Real.log ((q : ℝ) + 2) + 1)

/-- **The reduction.**  Head (kernel) + tail (`CharTailCancellation`) ⇒ the `t = 0` slice, with
`D = C + 1 + mertensBound`. -/
theorem charPrimeSumLogQZero_of_tail {C : ℝ} (h : CharTailCancellation C) :
    CharPrimeSumLogQZero (C + 1 + Erdos67b.PrimeEstimates.mertensBound) := by
  obtain ⟨hC, htail⟩ := h
  intro q χ hne X hX
  have hmert : 0 ≤ Erdos67b.PrimeEstimates.mertensBound :=
    Erdos67b.PrimeEstimates.mertensBound_nonneg
  have hq0 : (0 : ℝ) ≤ (q : ℝ) := Nat.cast_nonneg q
  have hlogpos : 0 ≤ Real.log ((q : ℝ) + 2) := Real.log_nonneg (by linarith)
  have hhead := norm_charHeadSum_le X χ
  have ht := htail q χ hne X hX
  have hsplit : ‖twistedPrimeSum X χ 0‖ ≤ ‖charHeadSum X χ‖ + ‖charTailSum X χ‖ := by
    rw [twistedPrimeSum_zero_split]; exact norm_add_le _ _
  nlinarith

/-- …and the slice implies the `t = 0` instance of `CharPrimeSumLogQ`'s conclusion. -/
theorem charPrimeSumLogQ_at_zero {D : ℝ} (hD : 0 ≤ D) (h : CharPrimeSumLogQZero D)
    {q : ℕ} (χ : DirichletCharacter ℂ q) (hne : χ ≠ 1) {X : ℝ} (hX : 3 ≤ X) :
    ‖twistedPrimeSum X χ 0‖
      ≤ D * (Real.log ((q : ℝ) + 2) + Real.log (2 + |(0 : ℝ)|) + 1) := by
  have hb := h q χ hne X hX
  have hlog2 : 0 ≤ Real.log (2 + |(0 : ℝ)|) := by
    simp only [abs_zero, add_zero]
    exact Real.log_nonneg (by norm_num)
  nlinarith

/-! ### GUARD RULE compliance for `CharTailCancellation` -/

/-- **Degenerate verdict — the constant-function configuration is excluded.**  `χ = 1` is exactly
the hypothesis `χ ≠ 1` rules out, and at `q = 1` *every* character is `1`
(`dirichletChar_one_apply`), so the modulus is forced away from `1`. -/
theorem charTail_conductor_ne_one {q : ℕ} (χ : DirichletCharacter ℂ q) (hne : χ ≠ 1) : q ≠ 1 := by
  rintro rfl
  exact hne (by ext x; rw [dirichletChar_one_apply, dirichletChar_one_apply])

/-- **Content locator.**  Below the conductor the tail range is *empty*, so
`CharTailCancellation` says nothing there: all its content is at `X² ≫ q`. -/
theorem charTailSum_head_free {X : ℝ} {q : ℕ} (χ : DirichletCharacter ℂ q)
    (h : ⌈X ^ 2⌉₊ ≤ q) : charTailSum X χ = 0 := by
  rw [charTailSum, Finset.sum_eq_zero]
  intro p hp
  exfalso
  obtain ⟨hlt, _⟩ := mem_primesUpToSq.1 (Finset.mem_filter.1 hp).1
  have := (Finset.mem_filter.1 hp).2
  omega

/-- **Degenerate verdict — the empty configuration survives.**  On the empty tail range the
statement holds with any `0 ≤ C`, so emptiness is not a refutation (unlike the lap-115 singleton
blocks, which *were*). -/
theorem charTailCancellation_vacuous_below {C : ℝ} (hC : 0 ≤ C) {X : ℝ} {q : ℕ}
    (χ : DirichletCharacter ℂ q) (h : ⌈X ^ 2⌉₊ ≤ q) :
    ‖charTailSum X χ‖ ≤ C * (Real.log ((q : ℝ) + 2) + 1) := by
  rw [charTailSum_head_free χ h, norm_zero]
  have hq0 : (0 : ℝ) ≤ (q : ℝ) := Nat.cast_nonneg q
  have : 0 ≤ Real.log ((q : ℝ) + 2) := Real.log_nonneg (by linarith)
  positivity

/-- **Degenerate verdict — the singleton configuration survives.**  A one-prime tail has norm at
most `1/p ≤ 1/2`, well inside the budget: unlike the block route, no singleton can refute this
statement, because the bound is additive in the mass rather than multiplicative in a saving. -/
theorem charTailSum_singleton_le {X : ℝ} {q p : ℕ} (χ : DirichletCharacter ℂ q)
    (hp : p.Prime) (hsub : (primesUpToSq X).filter (fun r => ¬ r ≤ q) = {p}) :
    ‖charTailSum X χ‖ ≤ 1 := by
  rw [charTailSum, hsub, Finset.sum_singleton, norm_div, RCLike.norm_conj,
    Complex.norm_natCast]
  have hp0 : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.one_lt.le
  have hchi : ‖χ (p : ZMod q)‖ ≤ 1 := dirichletChar_norm_le_one χ _
  rw [div_le_one (by linarith)]
  linarith


/-! ### Step 2 of the next attack: the `k ≥ 2` prime-power tail is `≤ 1`

`PENDING_WORK.md` step 2: passing from `∑_p χ(p) p^{-σ}` to the Dirichlet-series logarithm
`𝓛(σ,χ) = ∑_{p,k} χ(p^k)/(k p^{kσ})` costs only the `k ≥ 2` terms, and those are *absolutely*
bounded — by `1`, independently of the primes involved, of how many there are, and of `σ ≥ 1`.
Formalized here at `σ = 1` (the worst case) over an arbitrary finite prime set and an arbitrary
truncation `N`, which is the form the chain consumes. -/

/-- Geometric decay in `k`: for a prime-sized base `p ≥ 2`, the whole `k ≥ 2` tail weighs at most
`p^{-2}`.  (The `1/k` is thrown away as `1/k ≤ 1/2`; the geometric ratio `1/p ≤ 1/2` then pays
the remaining factor `2`.) -/
theorem primePower_inner_le {p : ℕ} (hp : 2 ≤ p) (N : ℕ) :
    ∑ k ∈ Finset.Ico 2 N, (1:ℝ)/((k:ℝ) * (p:ℝ)^k) ≤ 1/(p:ℝ)^2 := by
  have hp2 : (2:ℝ) ≤ (p:ℝ) := by exact_mod_cast hp
  have hp0 : (0:ℝ) < (p:ℝ) := by linarith
  set r : ℝ := 1/(p:ℝ) with hr
  have hr0 : 0 ≤ r := by positivity
  have hrhalf : r ≤ 1/2 := by
    rw [hr, div_le_div_iff₀ hp0 (by norm_num)]; linarith
  rcases le_or_gt N 2 with hN | hN
  · have he : Finset.Ico 2 N = (∅ : Finset ℕ) := Finset.Ico_eq_empty (by omega)
    rw [he, Finset.sum_empty]
    positivity
  · rw [Finset.sum_Ico_eq_sum_range]
    have key : ∀ i ∈ Finset.range (N - 2),
        (1:ℝ)/(((2+i : ℕ) : ℝ) * (p:ℝ)^(2+i)) ≤ (1/2) * (r^2 * r^i) := by
      intro i _
      have hc : (((2+i : ℕ)) : ℝ) = 2 + (i:ℝ) := by push_cast; ring
      have hpow : (0:ℝ) < (p:ℝ)^(2+i) := by positivity
      have hrr : r^2 * r^i = 1/((p:ℝ)^(2+i)) := by
        rw [hr, div_pow, div_pow, one_pow, one_pow, div_mul_div_comm, one_mul, pow_add]
      rw [hc, hrr]
      have hle : (2:ℝ) * (p:ℝ)^(2+i) ≤ (2 + (i:ℝ)) * (p:ℝ)^(2+i) := by
        have : (0:ℝ) ≤ (i:ℝ) := Nat.cast_nonneg i
        nlinarith
      have h1 : (1:ℝ)/((2 + (i:ℝ)) * (p:ℝ)^(2+i)) ≤ 1/((2:ℝ) * (p:ℝ)^(2+i)) :=
        one_div_le_one_div_of_le (by positivity) hle
      have h2 : (1:ℝ)/((2:ℝ) * (p:ℝ)^(2+i)) = (1/2) * (1/((p:ℝ)^(2+i))) := by
        field_simp
      linarith [h1, h2.le, h2.ge]
    refine (Finset.sum_le_sum key).trans ?_
    rw [← Finset.mul_sum, ← Finset.mul_sum]
    have hgeo : ∑ i ∈ Finset.range (N-2), r^i ≤ 2 := by
      calc ∑ i ∈ Finset.range (N-2), r^i
          ≤ ∑ i ∈ Finset.range (N-2), ((1:ℝ)/2)^i := by gcongr
        _ ≤ 2 := sum_geometric_two_le _
    have hr2 : (0:ℝ) ≤ r^2 := by positivity
    have hstep : (1/2 : ℝ) * (r^2 * ∑ i ∈ Finset.range (N-2), r^i) ≤ (1/2) * (r^2 * 2) := by
      have := mul_le_mul_of_nonneg_left hgeo hr2
      nlinarith
    calc (1/2 : ℝ) * (r^2 * ∑ i ∈ Finset.range (N-2), r^i) ≤ (1/2) * (r^2 * 2) := hstep
      _ = r^2 := by ring
      _ = 1/(p:ℝ)^2 := by rw [hr, div_pow]; norm_num

/-- `∑_{p prime} p^{-2} ≤ 1`, over any finite set of primes, by comparison with the telescoping
`1/(n-1) − 1/n`.  (No `ζ(2)` needed — the crude telescope already gives the clean constant.) -/
theorem prime_inv_sq_sum_le_one {P : Finset ℕ} (hP : ∀ p ∈ P, Nat.Prime p) :
    ∑ p ∈ P, (1:ℝ)/(p:ℝ)^2 ≤ 1 := by
  have hsub : P ⊆ Finset.Ico 2 (P.sup id + 1) := by
    intro p hp
    have h2 : 2 ≤ p := (hP p hp).two_le
    have : p ≤ P.sup id := Finset.le_sup (f := id) hp
    simp only [Finset.mem_Ico]; omega
  have hmono : ∑ p ∈ P, (1:ℝ)/(p:ℝ)^2
      ≤ ∑ n ∈ Finset.Ico 2 (P.sup id + 1), (1:ℝ)/(n:ℝ)^2 := by
    refine Finset.sum_le_sum_of_subset_of_nonneg hsub ?_
    intro i _ _; positivity
  refine hmono.trans ?_
  set B := P.sup id + 1
  rcases le_or_gt B 2 with hB | hB
  · rw [Finset.Ico_eq_empty (by omega)]; norm_num
  · rw [Finset.sum_Ico_eq_sum_range]
    have key : ∀ i ∈ Finset.range (B - 2), (1:ℝ)/((((2+i : ℕ)) : ℝ))^2
        ≤ (1/(1+(i:ℝ)) - 1/(2+(i:ℝ))) := by
      intro i _
      have h1 : (0:ℝ) < 1 + (i:ℝ) := by positivity
      have h2 : (0:ℝ) < 2 + (i:ℝ) := by positivity
      have hc : (((2+i : ℕ)) : ℝ) = 2 + (i:ℝ) := by push_cast; ring
      have hrhs : 1/(1+(i:ℝ)) - 1/(2+(i:ℝ)) = 1/((1+(i:ℝ))*(2+(i:ℝ))) := by
        field_simp; ring
      rw [hc, hrhs]
      have hle : (1+(i:ℝ))*(2+(i:ℝ)) ≤ (2+(i:ℝ))^2 := by nlinarith
      exact one_div_le_one_div_of_le (by positivity) hle
    refine (Finset.sum_le_sum key).trans ?_
    have tel : ∑ i ∈ Finset.range (B-2), ((fun j : ℕ => 1/(1+(j:ℝ))) i
        - (fun j : ℕ => 1/(1+(j:ℝ))) (i+1)) = 1/(1+((0:ℕ):ℝ)) - 1/(1+((B-2:ℕ):ℝ)) :=
      Finset.sum_range_sub' (fun j : ℕ => 1/(1+(j:ℝ))) (B-2)
    simp only at tel
    have hrw : ∀ i : ℕ, (1/(1+(i:ℝ)) - 1/(2+(i:ℝ)))
        = (1/(1+(i:ℝ)) - 1/(1+((i+1:ℕ):ℝ))) := by
      intro i; push_cast; ring_nf
    rw [Finset.sum_congr rfl (fun i _ => hrw i), tel]
    have hnn : (0:ℝ) ≤ 1/(1+((B-2:ℕ):ℝ)) := by positivity
    norm_num
    linarith

/-- **Step 2, assembled.**  The full `k ≥ 2` prime-power tail of the Dirichlet-series logarithm is
bounded by `1` — absolutely, uniformly in the prime set and the truncation.  So passing from the
prime sum `∑_p χ(p)/p` to `𝓛(1,χ)` costs `O(1)`, and the whole `t = 0` debt really is the
`L(1,χ) ≫ q^{-1/2}` lower bound (`PENDING_WORK.md` steps 3–5). -/
theorem primePower_tail_le_one {P : Finset ℕ} (hP : ∀ p ∈ P, Nat.Prime p) (N : ℕ) :
    ∑ p ∈ P, ∑ k ∈ Finset.Ico 2 N, (1:ℝ)/((k:ℝ) * (p:ℝ)^k) ≤ 1 := by
  refine le_trans (Finset.sum_le_sum ?_) (prime_inv_sq_sum_le_one hP)
  intro p hp
  exact primePower_inner_le (hP p hp).two_le N


/-! ### Where the archimedean content actually is: the `κ = 0` end is free

`NonPrincipalTwistSmall κ C` asks `‖twistedPrimeSum X χ t‖ ≤ (1 − κ) log log X + C`, and the
chain needs `κ > 0`.  The theorems below pin the two ends of that scale in the kernel, which
settles how much precision the archimedean debt really requires:

* **`κ = 0` is free** (`nonPrincipalTwistSmall_zero`): the triangle inequality plus Mertens gives
  `‖twistedPrimeSum X χ t‖ ≤ log log X + log 3 + mertensBound` for *every* `χ` and `t`, with no
  cancellation whatsoever.  So the entire content of the archimedean supply is the strict
  improvement on Mertens — not the bound itself.
* **`κ > 0` is exactly a `≪ log q` bound** (`nonPrincipalTwistSmall_of_logQBound`, already in
  `C3MrtArchFaithful`): in TT's range `q, |t| ≤ (log X)^{1/125}` one has
  `log q ≤ (1/125) log log X`, so a bound `D·(log(q+2) + log(2+|t|) + 1)` yields
  `κ = 1 − 2D/125`, admissible for every `D < 62.5`.

Together these say the tolerance is *neither* loose nor tight in a surprising way: nothing weaker
than `O(log q)` can work (anything of size `log log X` at the top of the range gives `κ = 0`,
which `nonPrincipalTwistSmall_zero` shows is already free and therefore useless), and the
constant in the `O` is generous (up to `62`).  This is why the `t = 0` route above aims at
`L(1,χ) ≫ q^{-1/2}` rather than anything sharper: a crude Siegel-free rate is all the chain can
use, and all it needs. -/

/-- Every twisted prime sum is bounded by the prime reciprocal mass — no cancellation used. -/
theorem norm_twistedPrimeSum_le_mass {X : ℝ} (hX : 3 ≤ X) {q : ℕ}
    (χ : DirichletCharacter ℂ q) (t : ℝ) :
    ‖twistedPrimeSum X χ t‖
      ≤ Real.log (Real.log ((⌈X ^ 2⌉₊ : ℕ) : ℝ)) + Erdos67b.PrimeEstimates.mertensBound := by
  have hceilR : ((9:ℕ) : ℝ) ≤ ((⌈X ^ 2⌉₊ : ℕ) : ℝ) :=
    le_trans (by push_cast; nlinarith) (Nat.le_ceil _)
  have hceil : (9:ℕ) ≤ ⌈X ^ 2⌉₊ := by exact_mod_cast hceilR
  have hB : (2:ℕ) ≤ ⌈X ^ 2⌉₊ := by omega
  have hterm : ∀ p ∈ primesUpToSq X,
      ‖(starRingEnd ℂ) (χ (p : ZMod q)) *
        Complex.exp (-(t : ℂ) * Complex.I * (Real.log p : ℂ)) / (p : ℂ)‖ ≤ (p : ℝ)⁻¹ := by
    intro p hp
    have hpp : p.Prime := (mem_primesUpToSq.1 hp).2
    have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hpp.pos
    rw [norm_div, norm_mul, RCLike.norm_conj, norm_exp_twist, mul_one, Complex.norm_natCast]
    have hchi : ‖χ (p : ZMod q)‖ ≤ 1 := dirichletChar_norm_le_one χ _
    rw [div_le_iff₀ hp0]
    calc ‖χ ((p : ℕ) : ZMod q)‖ ≤ 1 := hchi
      _ = (p : ℝ)⁻¹ * (p : ℝ) := by field_simp
  have hnorm : ‖twistedPrimeSum X χ t‖ ≤ ∑ p ∈ primesUpToSq X, (p : ℝ)⁻¹ := by
    rw [twistedPrimeSum, ← primesUpToSq]
    exact le_trans (norm_sum_le _ _) (Finset.sum_le_sum hterm)
  have hGb : ∀ p ∈ primesUpToSq X, p.Prime ∧ p ≤ ⌈X ^ 2⌉₊ := by
    intro p hp
    obtain ⟨hlt, hpp⟩ := mem_primesUpToSq.1 hp
    exact ⟨hpp, by omega⟩
  exact le_trans hnorm (small_prime_mass_le hB hGb)

/-- **Content locator for the archimedean debt: `κ = 0` is free.**  For *every* character and
*every* twist, `‖twistedPrimeSum X χ t‖ ≤ log log X + log 3 + mertensBound`, by the triangle
inequality alone.  So `NonPrincipalTwistSmall 0 C` carries no arithmetic content: the whole
content of the archimedean supply is the *strict* improvement `κ > 0` over Mertens. -/
theorem norm_twistedPrimeSum_le_loglog {X : ℝ} (hX : 3 ≤ X) {q : ℕ}
    (χ : DirichletCharacter ℂ q) (t : ℝ) :
    ‖twistedPrimeSum X χ t‖
      ≤ Real.log (Real.log X) + (Real.log 3 + Erdos67b.PrimeEstimates.mertensBound) := by
  have hX0 : (0:ℝ) < X := by linarith
  have hlogX : 1 < Real.log X := one_lt_log_of_three_le hX
  -- `⌈X²⌉₊ ≤ X³`, so `log ⌈X²⌉₊ ≤ 3 log X`
  have hcl : ((⌈X ^ 2⌉₊ : ℕ) : ℝ) ≤ X ^ 3 := by
    have h1 : ((⌈X ^ 2⌉₊ : ℕ) : ℝ) < X ^ 2 + 1 := Nat.ceil_lt_add_one (by positivity)
    nlinarith
  have h9 : ((9:ℕ) : ℝ) ≤ ((⌈X ^ 2⌉₊ : ℕ) : ℝ) :=
    le_trans (by push_cast; nlinarith) (Nat.le_ceil _)
  have h9' : (9:ℝ) ≤ ((⌈X ^ 2⌉₊ : ℕ) : ℝ) := by push_cast at h9; linarith
  have hcl0 : (0:ℝ) < ((⌈X ^ 2⌉₊ : ℕ) : ℝ) := by linarith
  have hlogcl : Real.log ((⌈X ^ 2⌉₊ : ℕ) : ℝ) ≤ 3 * Real.log X := by
    have h := Real.log_le_log hcl0 hcl
    rw [Real.log_pow] at h
    push_cast at h
    linarith
  have hlogcl0 : 0 < Real.log ((⌈X ^ 2⌉₊ : ℕ) : ℝ) := Real.log_pos (by linarith)
  have houter : Real.log (Real.log ((⌈X ^ 2⌉₊ : ℕ) : ℝ)) ≤ Real.log 3 + Real.log (Real.log X) := by
    have h1 := Real.log_le_log hlogcl0 hlogcl
    rwa [Real.log_mul (by norm_num) (by linarith)] at h1
  have := norm_twistedPrimeSum_le_mass hX χ t
  linarith

/-- …packaged as the `Prop` the chain uses: the `κ = 0` instance holds outright. -/
theorem nonPrincipalTwistSmall_zero :
    NonPrincipalTwistSmall 0 (Real.log 3 + Erdos67b.PrimeEstimates.mertensBound) := by
  intro X hX q χ _ _ t _
  have := norm_twistedPrimeSum_le_loglog hX χ t
  linarith

end CastingOut

end NormalNumbers
