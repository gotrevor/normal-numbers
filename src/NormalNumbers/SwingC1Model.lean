import NormalNumbers.SwingC1CRT

/-!
# Leaf (M): the model term of the `model × decoupling` split

`SwingC1Periodic.lean` writes the `×b`-orbit of `G₄_b` as `θ_n = Σ_p b^{n mod p}/(b^p−1)`, and
`SwingC1CRT.lean` splits a mean along a periodic factor into a *model* term and a *decoupling
defect*.  Here the model term is computed EXACTLY: cutting the primes at `P` and taking
`Q = Π_{p ≤ P} p` for the period,

`periodMean (n ↦ e(h·θ^{(P)}_n)) Q  =  Π_{p ≤ P} localFactor b h p`   (`periodMean_phase_smallTail`)

with the purely local factor `localFactor b h p = (1/p) Σ_{s<p} e(h · b^s/(b^p − 1))`.

This is the CRT statement that over one full period the residues `(n mod p)_{p ≤ P}` are jointly
uniform, and it is the whole reason the model term carries randomness: each local factor is an
average of `p` unit vectors that are NOT all equal (the `s = p−1, p−2, …` terms are near the
fixed roots `e(h/b), e(h/b²), …`), so `‖localFactor‖ ≤ 1 − c_h/p`, and Mertens makes the product
vanish.  Those last two steps are the named leaves `norm_localFactor_le` and
`prod_localFactor_tendsto_zero`.
-/

open Finset Filter Topology

namespace NormalNumbers.CastingOut

/-! ### `e(x) = exp(2πix)` -/

/-- `e(x) = exp(2πix)`. -/
noncomputable def phase (x : ℝ) : ℂ := Complex.exp (2 * Real.pi * Complex.I * (x : ℂ))

@[simp] lemma norm_phase (x : ℝ) : ‖phase x‖ = 1 := by
  have hx : phase x = Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I) := by
    unfold phase; congr 1; push_cast; ring
  rw [hx]; exact Complex.norm_exp_ofReal_mul_I _

lemma phase_add (x y : ℝ) : phase (x + y) = phase x * phase y := by
  unfold phase
  rw [← Complex.exp_add]
  congr 1
  push_cast; ring

lemma phase_sum {ι : Type*} (s : Finset ι) (f : ι → ℝ) :
    phase (∑ i ∈ s, f i) = ∏ i ∈ s, phase (f i) := by
  classical
  induction s using Finset.induction with
  | empty => simp [phase]
  | insert a s ha ih => rw [Finset.sum_insert ha, phase_add, ih, Finset.prod_insert ha]

/-! ### The small-prime part and its period -/

/-- The primes `≤ P`. -/
def primesLe (P : ℕ) : Finset ℕ := (range (P + 1)).filter Nat.Prime

lemma prime_of_mem_primesLe {P p : ℕ} (hp : p ∈ primesLe P) : p.Prime :=
  (Finset.mem_filter.mp hp).2

/-- The primorial `Π_{p ≤ P} p`: the joint period of the primes `≤ P`. -/
def primorialLe (P : ℕ) : ℕ := ∏ p ∈ primesLe P, p

lemma primorialLe_pos (P : ℕ) : 0 < primorialLe P :=
  Finset.prod_pos fun p hp => (prime_of_mem_primesLe hp).pos

/-- Every prime `≤ P` divides the primorial: the primorial is a common period. -/
lemma dvd_primorialLe {P p : ℕ} (hp : p ∈ primesLe P) : p ∣ primorialLe P :=
  Finset.dvd_prod_of_mem _ hp

/-- `θ^{(P)}`, the part of the tail carried by the primes `≤ P`, as a sum over primes. -/
lemma truncTail_eq_sum_primesLe (b P N : ℕ) :
    truncTail b P N = ∑ p ∈ primesLe P, primePeriodicTerm b p N := by
  rw [truncTail, primesLe, Finset.sum_filter]
  refine Finset.sum_congr rfl fun p _ => ?_
  by_cases hp : p.Prime
  · rw [if_pos hp]
  · rw [if_neg hp]; unfold primePeriodicTerm; rw [if_neg hp]

/-- `θ^{(P)}` is `primorialLe P`-periodic. -/
theorem truncTail_add_primorial (b P N : ℕ) :
    truncTail b P (N + primorialLe P) = truncTail b P N := by
  refine truncTail_add_period b P N _ fun p hpP hpp => ?_
  exact dvd_primorialLe (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hpp⟩)

theorem truncTail_add_mul_primorial (b P N r : ℕ) :
    truncTail b P (N + r * primorialLe P) = truncTail b P N := by
  induction r with
  | zero => simp
  | succ r ih =>
      rw [show N + (r + 1) * primorialLe P = (N + r * primorialLe P) + primorialLe P by ring,
        truncTail_add_primorial, ih]

/-! ### The local factor, and the CRT factorisation of the model term -/

/-- `localFactor b h p = (1/p) Σ_{s<p} e(h · b^s/(b^p − 1))`: the `p`-local average. -/
noncomputable def localFactor (b : ℕ) (h : ℝ) (p : ℕ) : ℂ :=
  (∑ s ∈ range p, phase (h * primePeriodicTerm b p s)) / p

lemma norm_localFactor_le_one (b : ℕ) (h : ℝ) (p : ℕ) (hp : 0 < p) :
    ‖localFactor b h p‖ ≤ 1 := by
  have hpr : (0 : ℝ) < p := by exact_mod_cast hp
  rw [localFactor, norm_div, Complex.norm_natCast, div_le_one hpr]
  calc ‖∑ s ∈ range p, phase (h * primePeriodicTerm b p s)‖
      ≤ ∑ s ∈ range p, ‖phase (h * primePeriodicTerm b p s)‖ := norm_sum_le _ _
    _ = p := by simp

/-- **Leaf (M), analytic half done: the model term factorises over the primes.**
Over one full period `Q = Π_{p ≤ P} p` the residues `(n mod p)_{p ≤ P}` are jointly uniform
(CRT), so the mean of `e(h·θ^{(P)})` is the product of the purely local averages. -/
theorem periodMean_phase_truncTail (b P : ℕ) (h : ℝ) :
    periodMean (fun n => phase (h * truncTail b P n)) (primorialLe P)
      = ∏ p ∈ primesLe P, localFactor b h p := by
  classical
  have hres : ∀ n p : ℕ, 0 < p →
      primePeriodicTerm b p n = primePeriodicTerm b p (n % p) := by
    intro n p _
    unfold primePeriodicTerm
    rw [Nat.mod_mod_of_dvd n (dvd_refl p)]
  have hA : ∀ n : ℕ, phase (h * truncTail b P n)
      = ∏ p ∈ primesLe P, phase (h * primePeriodicTerm b p (n % p)) := by
    intro n
    rw [truncTail_eq_sum_primesLe, Finset.mul_sum, phase_sum]
    exact Finset.prod_congr rfl fun p hp => by
      rw [hres n p (prime_of_mem_primesLe hp).pos]
  have hcop : ((primesLe P : Finset ℕ) : Set ℕ).Pairwise Nat.Coprime := by
    intro p hp q hq hne
    exact (Nat.coprime_primes (prime_of_mem_primesLe hp) (prime_of_mem_primesLe hq)).mpr hne
  have hpos : ∀ p ∈ primesLe P, 0 < p := fun p hp => (prime_of_mem_primesLe hp).pos
  rw [periodMean, primorialLe, Finset.sum_congr rfl (fun n _ => hA n),
    sum_range_prod_mod (fun p s => phase (h * primePeriodicTerm b p s)) (primesLe P) hpos hcop,
    Nat.cast_prod, ← Finset.prod_div_distrib]
  rfl

/-! ### The two remaining steps of leaf (M) -/

/-- **Leaf (M)(b).**  Each local factor is an average of `p` unit vectors that are not all equal,
so it is bounded away from `1` at rate `1/p`.

The two far-apart vectors: `s = p − 1 − i` contributes `e(h·b^{−1−i}/(1−b^{−p}))`, which for
`p` large is near the fixed root `e(h/b^{1+i})`; choosing `i` with `0 < |h|/b^{1+i} < 1` (possible
for every `h ≠ 0`) makes it differ from the `s = 0` term `e(h/(b^p−1)) → 1` by a fixed `δ > 0`.
Then `‖(1/p)Σ z_s‖ ≤ 1 − δ²/(4p)` because `‖z₁ + z₂‖ ≤ √(4 − δ²) ≤ 2 − δ²/4`. -/
theorem norm_localFactor_le (b : ℕ) (hb : 2 ≤ b) (h : ℝ) (hh : h ≠ 0) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ p : ℕ in atTop,
      p.Prime → ‖localFactor b h p‖ ≤ 1 - c / p := by
  sorry

/-- **Leaf (M)(c).**  Mertens: `Σ_p 1/p = ∞`, so `Π_{p ≤ P}(1 − c/p) → 0`, hence the model term
vanishes as the cut `P → ∞`.  This is the statement that the small primes alone already
randomise the orbit — the only *unconditional* source of randomness in the whole route. -/
theorem prod_localFactor_tendsto_zero (b : ℕ) (hb : 2 ≤ b) (h : ℝ) (hh : h ≠ 0) :
    Tendsto (fun P => ‖∏ p ∈ primesLe P, localFactor b h p‖) atTop (𝓝 0) := by
  sorry

/-- **Leaf (M), assembled.**  The model term of the split vanishes. -/
theorem periodMean_tendsto_zero (b : ℕ) (hb : 2 ≤ b) (h : ℝ) (hh : h ≠ 0) :
    Tendsto (fun P => ‖periodMean (fun n => phase (h * truncTail b P n)) (primorialLe P)‖)
      atTop (𝓝 0) := by
  simpa only [periodMean_phase_truncTail] using prod_localFactor_tendsto_zero b hb h hh

end NormalNumbers.CastingOut
