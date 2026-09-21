import Mathlib

/-!
# The finite radical model for the prime-model shortcut

This is a *model change*, not a truncation.  At each prime `p` in the window the
state space is `Option (Fin k)`: the state `some j` records "`p` divides `n + j`"
(all higher valuations of `n + j` merged into the same state, so the model is
finite), and `none` records "`p` divides none of `n, n+1, …, n+k-1`".  Masses are

* `none  ↦ 1 - k/p`,
* `some j ↦ 1/p`  (each of the `k` shifts),

which is a genuine probability law exactly when `k ≤ p`.  Distinct primes are
independent, so the global law on `ι → Option (Fin k)` is the product law.

Everything here is a finite algebraic identity: the product law has total mass
one (`radical_mass_one`), complex phase expectations factor over sites
(`radical_phase_product`), and the single-site moment identity
`radical_site_moment` gives

  `E ∏_p (if state_p = some j₀ then t p else 1) = ∏_p (1 + (t p - 1)/p)`,

the shape consumed by the `d_j^α` moment bound.  See
`papers/prime-model-radical.md` for the arithmetic bridge and the residual
analytic obligation (the two-sided sieve fundamental lemma), which is *not*
proved here.

The layer is stated for abstract reciprocal probabilities `q : ι → ℝ`; the
prime-specialised formulas (`q p = 1/p`) are exposed as the `_prime` variants.
-/

set_option linter.unusedSectionVars false

open scoped BigOperators

namespace NormalNumbers.PrimeModel.Radical

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {k : ℕ}

/-! ## Independence: the product-over-sites exchange -/

/-- Independence of the sites: a sum over all state tuples of a product of local
factors is the product of the local sums.  This is the only structural input; all
model identities below are instances of it. -/
theorem sum_pi_prod {R : Type*} [CommRing R] (g : ι → Option (Fin k) → R) :
    ∑ s : ι → Option (Fin k), ∏ i, g i (s i) = ∏ i, ∑ a : Option (Fin k), g i a := by
  rw [Finset.prod_univ_sum]
  exact (Finset.sum_congr (by simp [Fintype.piFinset_univ]) fun _ _ => rfl).symm

/-! ## Local weights -/

/-- Local mass of a radical state at a site with reciprocal probability `q`:
`1 - k*q` for `none`, and `q` for each of the `k` shifts. -/
def localWeight (k : ℕ) (q : ℝ) : Option (Fin k) → ℝ
  | none => 1 - k * q
  | some _ => q

@[simp] lemma localWeight_none (k : ℕ) (q : ℝ) :
    localWeight k q none = 1 - k * q := rfl

@[simp] lemma localWeight_some (k : ℕ) (q : ℝ) (j : Fin k) :
    localWeight k q (some j) = q := rfl

/-- **(1a)** Local weights are nonnegative exactly under the model constraint `k*q ≤ 1`. -/
lemma localWeight_nonneg {q : ℝ} (hq : 0 ≤ q) (hk : (k : ℝ) * q ≤ 1) :
    ∀ a : Option (Fin k), 0 ≤ localWeight k q a := by
  intro a
  cases a with
  | none => simpa using sub_nonneg.mpr hk
  | some j => simpa using hq

/-- **(1b)** Local weights sum to one. -/
lemma localWeight_sum (k : ℕ) (q : ℝ) :
    ∑ a : Option (Fin k), localWeight k q a = 1 := by
  rw [Fintype.sum_option]
  simp [Finset.sum_const, mul_comm]

/-! ## The product law -/

/-- The product (independent-sites) radical law on state tuples. -/
def weight (k : ℕ) (q : ι → ℝ) (s : ι → Option (Fin k)) : ℝ :=
  ∏ i, localWeight k (q i) (s i)

/-- **(2a)** The product law is nonnegative. -/
theorem radical_weight_nonneg {q : ι → ℝ} (hq : ∀ i, 0 ≤ q i)
    (hk : ∀ i, (k : ℝ) * q i ≤ 1) (s : ι → Option (Fin k)) :
    0 ≤ weight k q s :=
  Finset.prod_nonneg fun i _ => localWeight_nonneg (hq i) (hk i) (s i)

/-- **(2b)** The product law has total mass one. -/
theorem radical_mass_one (k : ℕ) (q : ι → ℝ) :
    ∑ s : ι → Option (Fin k), weight k q s = 1 := by
  simpa [weight, localWeight_sum] using
    sum_pi_prod (fun i a => localWeight k (q i) a)

/-! ## Phase expectations -/

/-- Local phase: `1` off the divisibility events, `z j` on the event `some j`. -/
def localPhase (k : ℕ) (z : Fin k → ℂ) : Option (Fin k) → ℂ
  | none => 1
  | some j => z j

@[simp] lemma localPhase_none (k : ℕ) (z : Fin k → ℂ) :
    localPhase k z none = 1 := rfl

@[simp] lemma localPhase_some (k : ℕ) (z : Fin k → ℂ) (j : Fin k) :
    localPhase k z (some j) = z j := rfl

/-- **(3)** The local phase expectation: `1 + (∑_j (z j - 1)) * q`. -/
theorem localPhase_expectation (k : ℕ) (q : ℝ) (z : Fin k → ℂ) :
    ∑ a : Option (Fin k), (localWeight k q a : ℂ) * localPhase k z a
      = 1 + (q : ℂ) * ∑ j, (z j - 1) := by
  rw [Fintype.sum_option]
  simp only [localWeight_none, localPhase_none, localWeight_some, localPhase_some,
    Complex.ofReal_sub, Complex.ofReal_one, Complex.ofReal_mul, Complex.ofReal_natCast,
    mul_one, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, ← Finset.mul_sum]
  ring

/-- **(4)** The global phase expectation factors into the local factors. -/
theorem radical_phase_product (k : ℕ) (q : ι → ℝ) (z : ι → Fin k → ℂ) :
    ∑ s : ι → Option (Fin k),
        (weight k q s : ℂ) * ∏ i, localPhase k (z i) (s i)
      = ∏ i, (1 + (q i : ℂ) * ∑ j, (z i j - 1)) := by
  have h : ∀ s : ι → Option (Fin k),
      (weight k q s : ℂ) * ∏ i, localPhase k (z i) (s i)
        = ∏ i, ((localWeight k (q i) (s i) : ℂ) * localPhase k (z i) (s i)) := by
    intro s
    rw [Finset.prod_mul_distrib, weight, Complex.ofReal_prod]
  simp only [h]
  rw [sum_pi_prod (fun i a => (localWeight k (q i) a : ℂ) * localPhase k (z i) a)]
  exact Finset.prod_congr rfl fun i _ => localPhase_expectation k (q i) (z i)

/-! ## Real moment identities -/

/-- The real multiplier attached to a state: `t j` on the event `some j`, `1` otherwise. -/
def localMult (k : ℕ) (t : Fin k → ℝ) : Option (Fin k) → ℝ
  | none => 1
  | some j => t j

@[simp] lemma localMult_none (k : ℕ) (t : Fin k → ℝ) :
    localMult k t none = 1 := rfl

@[simp] lemma localMult_some (k : ℕ) (t : Fin k → ℝ) (j : Fin k) :
    localMult k t (some j) = t j := rfl

/-- **(5, general form)** The real moment identity with arbitrary per-site,
per-shift multipliers. -/
theorem radical_mult_product (k : ℕ) (q : ι → ℝ) (t : ι → Fin k → ℝ) :
    ∑ s : ι → Option (Fin k), weight k q s * ∏ i, localMult k (t i) (s i)
      = ∏ i, (1 + q i * ∑ j, (t i j - 1)) := by
  have h : ∀ s : ι → Option (Fin k),
      weight k q s * ∏ i, localMult k (t i) (s i)
        = ∏ i, (localWeight k (q i) (s i) * localMult k (t i) (s i)) := by
    intro s; rw [Finset.prod_mul_distrib, weight]
  have hloc : ∀ (q : ℝ) (t : Fin k → ℝ),
      ∑ a : Option (Fin k), localWeight k q a * localMult k t a
        = 1 + q * ∑ j, (t j - 1) := by
    intro q t
    rw [Fintype.sum_option]
    simp only [localWeight_none, localMult_none, localWeight_some, localMult_some,
      mul_one, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, ← Finset.mul_sum]
    ring
  simp only [h]
  rw [sum_pi_prod (fun i a => localWeight k (q i) a * localMult k (t i) a)]
  exact Finset.prod_congr rfl fun i _ => hloc (q i) (t i)

/-- **(5)** The single-site moment identity: a multiplier `t p` acting only on the
event "`p` divides `n + j₀`" for one fixed shift `j₀` has expectation
`∏_p (1 + q p * (t p - 1))`.  With `q p = 1/p` this is `∏_p (1 + (t p - 1)/p)`. -/
theorem radical_site_moment (k : ℕ) (q : ι → ℝ) (j₀ : Fin k) (t : ι → ℝ) :
    ∑ s : ι → Option (Fin k),
        weight k q s * ∏ i, (if s i = some j₀ then t i else 1)
      = ∏ i, (1 + q i * (t i - 1)) := by
  have hrw : ∀ (i : ι) (a : Option (Fin k)),
      (if a = some j₀ then t i else 1)
        = localMult k (fun j => if j = j₀ then t i else 1) a := by
    intro i a
    cases a with
    | none => simp
    | some j => by_cases hj : j = j₀ <;> simp [hj]
  simp only [hrw]
  rw [radical_mult_product k q (fun i j => if j = j₀ then t i else 1)]
  refine Finset.prod_congr rfl fun i _ => ?_
  have hj : ∀ j : Fin k, ((if j = j₀ then t i else 1) - 1)
      = (if j = j₀ then t i - 1 else 0) := by
    intro j; by_cases h : j = j₀ <;> simp [h]
  simp only [hj, Finset.sum_ite_eq' Finset.univ j₀ (fun _ => t i - 1), Finset.mem_univ,
    if_true]

/-- **(5′)** The uniform-multiplier variant: the multiplier acts on *every* shift,
so the per-site factor picks up the full mass `k * q`. -/
theorem radical_site_moment_uniform (k : ℕ) (q : ι → ℝ) (t : ι → ℝ) :
    ∑ s : ι → Option (Fin k),
        weight k q s * ∏ i, (if (s i).isSome then t i else 1)
      = ∏ i, (1 + k * q i * (t i - 1)) := by
  have hrw : ∀ (i : ι) (a : Option (Fin k)),
      (if a.isSome then t i else 1) = localMult k (fun _ => t i) a := by
    intro i a; cases a <;> simp
  simp only [hrw]
  rw [radical_mult_product k q (fun i _ => t i)]
  refine Finset.prod_congr rfl fun i _ => ?_
  have hc : ∑ _j : Fin k, (t i - 1) = (k : ℝ) * (t i - 1) := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [hc]; ring

/-! ## Prime specialisation

The model constraint `k * (1/p) ≤ 1` is exactly `k ≤ p`, so every prime `p > k`
in the window is admissible. -/

/-- Reciprocal probabilities attached to a family of primes. -/
noncomputable def primeRecip (p : ι → ℕ) : ι → ℝ := fun i => (p i : ℝ)⁻¹

lemma primeRecip_nonneg (p : ι → ℕ) (i : ι) : 0 ≤ primeRecip p i :=
  inv_nonneg.mpr (Nat.cast_nonneg _)

/-- Admissibility of a prime site: `k ≤ p` gives `k * (1/p) ≤ 1`. -/
lemma primeRecip_mul_le_one {p : ι → ℕ} (hp : ∀ i, 0 < p i) (hk : ∀ i, k ≤ p i) (i : ι) :
    (k : ℝ) * primeRecip p i ≤ 1 := by
  have hpos : (0 : ℝ) < (p i : ℝ) := by exact_mod_cast hp i
  rw [primeRecip, mul_inv_le_iff₀ hpos, one_mul]
  exact_mod_cast hk i

/-- The prime-specialised law is a probability law. -/
theorem radical_weight_nonneg_prime {p : ι → ℕ} (hp : ∀ i, 0 < p i) (hk : ∀ i, k ≤ p i)
    (s : ι → Option (Fin k)) :
    0 ≤ weight k (primeRecip p) s :=
  radical_weight_nonneg (primeRecip_nonneg p) (primeRecip_mul_le_one hp hk) s

theorem radical_mass_one_prime (k : ℕ) (p : ι → ℕ) :
    ∑ s : ι → Option (Fin k), weight k (primeRecip p) s = 1 :=
  radical_mass_one k _

/-- **(4, prime form)** `E ∏_p φ_p = ∏_p (1 + (∑_j (z_{p,j} - 1))/p)`. -/
theorem radical_phase_product_prime (k : ℕ) (p : ι → ℕ) (z : ι → Fin k → ℂ) :
    ∑ s : ι → Option (Fin k),
        (weight k (primeRecip p) s : ℂ) * ∏ i, localPhase k (z i) (s i)
      = ∏ i, (1 + (∑ j, (z i j - 1)) / (p i : ℂ)) := by
  rw [radical_phase_product k (primeRecip p) z]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [primeRecip]
  push_cast
  rw [div_eq_inv_mul]

/-- **(5, prime form)** `E ∏_p (if p ∣ n + j₀ then t p else 1) = ∏_p (1 + (t p - 1)/p)`. -/
theorem radical_site_moment_prime (k : ℕ) (p : ι → ℕ) (j₀ : Fin k) (t : ι → ℝ) :
    ∑ s : ι → Option (Fin k),
        weight k (primeRecip p) s * ∏ i, (if s i = some j₀ then t i else 1)
      = ∏ i, (1 + (t i - 1) / (p i : ℝ)) := by
  rw [radical_site_moment k (primeRecip p) j₀ t]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [primeRecip, div_eq_inv_mul]

/-! ## Numeric anchors

These evaluate the model sums *independently* of the identities above (by
expanding the state space by hand through `Fin.consEquiv`) and check the
predicted closed forms.  They guard against a mis-stated model: `k = 2`, sites
with reciprocals `1/3, 1/5` (the primes `3, 5` of the `k = 2` instrument). -/

section Anchors

private lemma sum_funUnique (f : (Fin 1 → Option (Fin 2)) → ℝ) :
    ∑ y, f y = ∑ b : Option (Fin 2), f (fun _ => b) :=
  (Equiv.sum_comp (Equiv.funUnique (Fin 1) (Option (Fin 2))).symm f).symm

/-- One site, `q = 1/3`, `t = 2`: predicted `1 + (2-1)/3 = 4/3`. -/
example :
    (∑ s : Fin 1 → Option (Fin 2),
        weight 2 (fun _ => (1:ℝ)/3) s * ∏ i, (if s i = some 0 then (2:ℝ) else 1)) = 4/3 := by
  rw [← Equiv.sum_comp (Equiv.funUnique (Fin 1) (Option (Fin 2))).symm, Fintype.sum_option]
  simp [weight, Fin.sum_univ_two]
  norm_num

example : (1 : ℝ) + (1/3) * ((2:ℝ) - 1) = 4/3 := by norm_num

/-- Two sites, `q = (1/3, 1/5)`, `t = 2`: predicted `(4/3)(6/5) = 8/5`. -/
example :
    (∑ s : Fin 2 → Option (Fin 2),
        weight 2 (fun i => if i = 0 then (1:ℝ)/3 else 1/5) s
          * ∏ i, (if s i = some 0 then (2:ℝ) else 1)) = 8/5 := by
  rw [← Equiv.sum_comp (Fin.consEquiv (fun _ : Fin 2 => Option (Fin 2))),
    Fintype.sum_prod_type]
  rw [Finset.sum_congr rfl fun x _ => sum_funUnique _]
  simp only [Fintype.sum_option]
  simp [weight, Fin.prod_univ_two, Fin.consEquiv]
  norm_num

example : ((1:ℝ) + (2 - 1)/3) * ((1:ℝ) + (2 - 1)/5) = 8/5 := by norm_num

/-- Total mass over the nine two-site states is one. -/
example :
    (∑ s : Fin 2 → Option (Fin 2),
        weight 2 (fun i => if i = 0 then (1:ℝ)/3 else 1/5) s) = 1 := by
  rw [← Equiv.sum_comp (Fin.consEquiv (fun _ : Fin 2 => Option (Fin 2))),
    Fintype.sum_prod_type]
  rw [Finset.sum_congr rfl fun x _ => sum_funUnique _]
  simp only [Fintype.sum_option]
  simp [weight, Fin.prod_univ_two, Fin.consEquiv]
  norm_num

end Anchors

end NormalNumbers.PrimeModel.Radical
