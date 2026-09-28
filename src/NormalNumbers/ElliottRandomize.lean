import NormalNumbers.ElliottLadder

/-!
# The two-point unimodular cover

This is the replacement for the **refuted** unimodularisation step of leaf 2
(`NormalNumbers.ElliottLadder.nonasymptotic_of_affineCM`).  See `DIRECTION.md` → CURRENT DIRECTIVE
item 0 and `PENDING_WORK.md` → "Reflection — 2026-09-25" for the counterexample that kills the
Dirichlet-convolution route `‖g̃‖ = 1 ⋆ v`: its truncation level would have to be fixed *before*
the function, and a convergent series with uniformly bounded sum need not have uniformly small
tails across a family.

The replacement is exact and finite.  Every point of the closed unit disc is the **midpoint of two
unimodular numbers**,
`lift b z = phase z * (‖z‖ ± i √(1 - ‖z‖²))`,  `lift true z + lift false z = 2 z`,
and applying this independently at each maximal prime power `p^k ≤ Y` writes a `1`-bounded
multiplicative `g` as the *average* of unimodular multiplicative functions, exactly on `[1, Y]`.

**Why the target is `Multiplicative` and not `CompletelyMultiplicative`.**  A unimodular
completely multiplicative cover would need a unimodular random variable `V` with `E[V^k] = r^k`
for every `k`; the unique such law on the circle is the Poisson kernel `P_r(θ)dθ/2π`, which has no
finite support.  Aiming at a merely multiplicative cover asks for **one** moment per prime power,
`E[Z] = z`, which the two-point law supplies exactly.  Complete multiplicativity is recovered
afterwards by the squarefull convolution `u = U ⋆ μŨ`, whose tail bound
`∑_d ‖u d‖/d ≤ ∏_p (1 + 2/(p(p-1))) ≤ e²` is an *absolute* constant — which is precisely the
uniformity the `v`-expansion lacked.

A third property of `lift` is what makes the pretentious transfer deterministic rather than
probabilistic: the perturbation `i √(1-‖z‖²) · phase z` is orthogonal to `z`, so

`(lift b z * conj z).re = ‖z‖²`  for **both** signs `b`,

whence `pretentiousDistSq g (cover ω) X = ∑_{p ≤ X} (1 - ‖g p‖²)/p` for *every* `ω`.

## Main results

* `lift_add_lift`, `norm_lift`, `re_lift_mul_conj` — the scalar facts.
* `cover_one`, `cover_mul_of_coprime`, `norm_cover` — `cover g Y ω` is a unimodular multiplicative
  function of `ℕ`.
* `sum_cover` — `∑_ω cover g Y ω m = 2^(Y+1) * g m` for `0 < m ≤ Y`: the averaging identity.
-/

open scoped BigOperators ComplexConjugate
open Finset

namespace NormalNumbers.ElliottRandomize

noncomputable section

/-! ## The two unimodular lifts of a point of the closed unit disc -/

/-- The unimodular phase of a complex number (`1` at the origin, where the phase is undefined). -/
def phase (z : ℂ) : ℂ := if z = 0 then 1 else z / (‖z‖ : ℂ)

@[simp] theorem phase_zero : phase 0 = 1 := by simp [phase]

theorem norm_phase (z : ℂ) : ‖phase z‖ = 1 := by
  by_cases hz : z = 0
  · simp [phase, hz]
  · have hn : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz
    simp [phase, hz, norm_div, hn]

/-- The defining property of the phase: `z = phase z * ‖z‖`. -/
theorem phase_mul_norm (z : ℂ) : phase z * (‖z‖ : ℂ) = z := by
  by_cases hz : z = 0
  · simp [hz]
  · have hn : ((‖z‖ : ℝ) : ℂ) ≠ 0 := by
      simpa using (norm_ne_zero_iff.mpr hz)
    rw [phase, if_neg hz, div_mul_cancel₀ _ hn]

/-- `phase z * conj z = ‖z‖` — the phase cancels against the conjugate. -/
theorem phase_mul_conj (z : ℂ) : phase z * conj z = (‖z‖ : ℂ) := by
  by_cases hz : z = 0
  · simp [hz]
  · have hn : ((‖z‖ : ℝ) : ℂ) ≠ 0 := by
      simpa using (norm_ne_zero_iff.mpr hz)
    have hzz : z * conj z = ((‖z‖ : ℝ) : ℂ) * ((‖z‖ : ℝ) : ℂ) := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
      push_cast
      ring
    rw [phase, if_neg hz, div_mul_eq_mul_div, hzz, mul_div_assoc, div_self hn, mul_one]

/-- The sign attached to a Boolean. -/
def sgn (b : Bool) : ℝ := if b then 1 else -1

theorem sgn_sq (b : Bool) : sgn b ^ 2 = 1 := by cases b <;> simp [sgn] <;> norm_num

/-- **The two unimodular lifts of `z`.**  For `‖z‖ ≤ 1` both have modulus one and their average
is `z`. -/
def lift (b : Bool) (z : ℂ) : ℂ :=
  phase z * ((‖z‖ : ℂ) + ((sgn b * Real.sqrt (1 - ‖z‖ ^ 2) : ℝ) : ℂ) * Complex.I)

/-- **The averaging identity.**  `z` is the midpoint of its two lifts. -/
theorem lift_add_lift (z : ℂ) : lift true z + lift false z = 2 * z := by
  have hz := phase_mul_norm z
  have expand : lift true z + lift false z = phase z * (‖z‖ : ℂ) * 2 := by
    simp only [lift, sgn, if_true, if_false]
    push_cast
    ring
  rw [expand, hz]
  ring

/-- **Both lifts are unimodular.** -/
theorem norm_lift {z : ℂ} (hz : ‖z‖ ≤ 1) (b : Bool) : ‖lift b z‖ = 1 := by
  have hsq : Real.sqrt (1 - ‖z‖ ^ 2) ^ 2 = 1 - ‖z‖ ^ 2 := by
    refine Real.sq_sqrt ?_
    nlinarith [norm_nonneg z]
  have hcore : ‖((‖z‖ : ℂ) + ((sgn b * Real.sqrt (1 - ‖z‖ ^ 2) : ℝ) : ℂ) * Complex.I)‖ = 1 := by
    rw [show ((‖z‖ : ℝ) : ℂ) + ((sgn b * Real.sqrt (1 - ‖z‖ ^ 2) : ℝ) : ℂ) * Complex.I =
        Complex.mk (‖z‖) (sgn b * Real.sqrt (1 - ‖z‖ ^ 2)) by
      apply Complex.ext <;> simp]
    rw [Complex.norm_def, Complex.normSq_mk]
    have : ‖z‖ * ‖z‖ + sgn b * Real.sqrt (1 - ‖z‖ ^ 2) *
        (sgn b * Real.sqrt (1 - ‖z‖ ^ 2)) = 1 := by
      nlinarith [sgn_sq b, hsq]
    rw [this, Real.sqrt_one]
  rw [lift, norm_mul, norm_phase, one_mul, hcore]

/-- **The pretentious-transfer identity.**  The perturbation is orthogonal to `z`, so *both*
lifts see the same real part against `conj z`. -/
theorem re_lift_mul_conj (z : ℂ) (b : Bool) : (lift b z * conj z).re = ‖z‖ ^ 2 := by
  have h : lift b z * conj z =
      ((‖z‖ : ℂ) + ((sgn b * Real.sqrt (1 - ‖z‖ ^ 2) : ℝ) : ℂ) * Complex.I) * (‖z‖ : ℂ) := by
    rw [lift]
    rw [mul_comm (phase z) _, mul_assoc, phase_mul_conj]
  rw [h]
  simp [Complex.add_re, Complex.mul_re, Complex.mul_im]
  ring

/-! ## The maximal prime powers of a natural number -/

/-- `ppIndex m` is the set `{p ^ v_p(m) : p ∣ m}` of maximal prime powers dividing `m`. -/
def ppIndex (m : ℕ) : Finset ℕ :=
  m.primeFactors.image fun p => p ^ m.factorization p

@[simp] theorem ppIndex_one : ppIndex 1 = ∅ := by simp [ppIndex]

theorem injOn_primePow (m : ℕ) :
    Set.InjOn (fun p => p ^ m.factorization p) m.primeFactors := by
  intro p hp q hq hpq
  have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
  have hqp : q.Prime := Nat.prime_of_mem_primeFactors hq
  have hkp : 0 < m.factorization p := by
    refine Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp ?_)
    rw [Nat.support_factorization]
    exact hp
  have hdvd : p ∣ q ^ m.factorization q := by
    have : p ∣ p ^ m.factorization p := dvd_pow_self p hkp.ne'
    simpa [hpq] using this
  exact (Nat.prime_dvd_prime_iff_eq hpp hqp).mp (hpp.dvd_of_dvd_pow hdvd)

/-- A multiplicative function is the product of its values at the maximal prime powers. -/
theorem prod_ppIndex {β : Type*} [CommMonoid β] (f : ℕ → β)
    (hmul : ∀ x y : ℕ, Nat.Coprime x y → f (x * y) = f x * f y) (hone : f 1 = 1)
    {m : ℕ} (hm : m ≠ 0) :
    ∏ i ∈ ppIndex m, f i = f m := by
  rw [ppIndex, Finset.prod_image (fun p hp q hq h => injOn_primePow m hp hq h)]
  rw [Nat.multiplicative_factorization f hmul hone hm, Finsupp.prod]
  exact (Finset.prod_congr (Nat.support_factorization (n := m)) fun p _ => rfl).symm

theorem ppIndex_mul_of_coprime {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) (h : Nat.Coprime m n) :
    ppIndex (m * n) = ppIndex m ∪ ppIndex n := by
  have hfact : (m * n).factorization = m.factorization + n.factorization :=
    Nat.factorization_mul hm hn
  have hpf : (m * n).primeFactors = m.primeFactors ∪ n.primeFactors :=
    Nat.primeFactors_mul hm hn
  have hdisj : Disjoint m.primeFactors n.primeFactors := Nat.Coprime.disjoint_primeFactors h
  have hm' : ∀ p ∈ m.primeFactors, (m * n).factorization p = m.factorization p := by
    intro p hp
    have hpn : p ∉ n.primeFactors := Finset.disjoint_left.mp hdisj hp
    have hz0 : n.factorization p = 0 := by
      rw [← Finsupp.notMem_support_iff, Nat.support_factorization]
      exact hpn
    simp [hfact, hz0]
  have hn' : ∀ p ∈ n.primeFactors, (m * n).factorization p = n.factorization p := by
    intro p hp
    have hpm : p ∉ m.primeFactors := Finset.disjoint_right.mp hdisj hp
    have hz0 : m.factorization p = 0 := by
      rw [← Finsupp.notMem_support_iff, Nat.support_factorization]
      exact hpm
    simp [hfact, hz0]
  rw [ppIndex, ppIndex, ppIndex, hpf, Finset.image_union]
  congr 1
  · exact Finset.image_congr fun p hp => by rw [hm' p hp]
  · exact Finset.image_congr fun p hp => by rw [hn' p hp]

theorem disjoint_ppIndex_of_coprime {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0)
    (h : Nat.Coprime m n) : Disjoint (ppIndex m) (ppIndex n) := by
  rw [Finset.disjoint_left]
  rintro i him hin
  simp only [ppIndex, Finset.mem_image] at him hin
  obtain ⟨p, hp, rfl⟩ := him
  obtain ⟨q, hq, hq'⟩ := hin
  have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
  have hqp : q.Prime := Nat.prime_of_mem_primeFactors hq
  have hkp : 0 < m.factorization p := by
    refine Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp ?_)
    rw [Nat.support_factorization]
    exact hp
  have hdvd : q ∣ p ^ m.factorization p := by
    have hk : 0 < n.factorization q := by
      refine Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp ?_)
      rw [Nat.support_factorization]
      exact hq
    have : q ∣ q ^ n.factorization q := dvd_pow_self q hk.ne'
    rw [hq'] at this
    exact this
  have hqp' : q = p := (Nat.prime_dvd_prime_iff_eq hqp hpp).mp (hqp.dvd_of_dvd_pow hdvd)
  subst hqp'
  exact (Nat.Coprime.disjoint_primeFactors h |> Finset.disjoint_left.mp) hp hq

theorem mem_ppIndex_le {m i : ℕ} (hm : m ≠ 0) (hi : i ∈ ppIndex m) : i ≤ m := by
  simp only [ppIndex, Finset.mem_image] at hi
  obtain ⟨p, hp, rfl⟩ := hi
  exact Nat.le_of_dvd (Nat.pos_of_ne_zero hm) (Nat.ordProj_dvd m p)

/-! ## The cover -/

variable (g : ℕ → ℂ) (Y : ℕ)

/-- **The two-point unimodular cover.**  For each `ω : Fin (Y+1) → Bool`, `cover g Y ω` is a
unimodular multiplicative function of `ℕ`; averaged over `ω` it reproduces `g` on `[1, Y]`. -/
def cover (ω : Fin (Y + 1) → Bool) (m : ℕ) : ℂ :=
  ∏ i : Fin (Y + 1), (if (i : ℕ) ∈ ppIndex m then lift (ω i) (g i) else 1)

@[simp] theorem cover_one (ω : Fin (Y + 1) → Bool) : cover g Y ω 1 = 1 := by
  simp [cover]

theorem norm_cover (hg : ∀ n : ℕ, ‖g n‖ ≤ 1) (ω : Fin (Y + 1) → Bool) (m : ℕ) :
    ‖cover g Y ω m‖ = 1 := by
  rw [cover, norm_prod]
  refine Finset.prod_eq_one fun i _ => ?_
  by_cases hi : (i : ℕ) ∈ ppIndex m
  · simp [hi, norm_lift (hg i) (ω i)]
  · simp [hi]

theorem cover_mul_of_coprime (ω : Fin (Y + 1) → Bool) {m n : ℕ}
    (hm : m ≠ 0) (hn : n ≠ 0) (h : Nat.Coprime m n) :
    cover g Y ω (m * n) = cover g Y ω m * cover g Y ω n := by
  rw [cover, cover, cover, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  by_cases him : (i : ℕ) ∈ ppIndex m
  · have hin : (i : ℕ) ∉ ppIndex n :=
      Finset.disjoint_left.mp (disjoint_ppIndex_of_coprime hm hn h) him
    have : (i : ℕ) ∈ ppIndex (m * n) := by
      rw [ppIndex_mul_of_coprime hm hn h]; exact Finset.mem_union_left _ him
    simp [this, him, hin]
  · by_cases hin : (i : ℕ) ∈ ppIndex n
    · have : (i : ℕ) ∈ ppIndex (m * n) := by
        rw [ppIndex_mul_of_coprime hm hn h]; exact Finset.mem_union_right _ hin
      simp [this, him, hin]
    · have : (i : ℕ) ∉ ppIndex (m * n) := by
        rw [ppIndex_mul_of_coprime hm hn h]
        simp [him, hin]
      simp [this, him, hin]

/-- **The averaging identity.**  Summing the cover over all `2^(Y+1)` sign patterns returns
`2^(Y+1) * g m`, for every `1 ≤ m ≤ Y`. -/
theorem sum_cover (hmul : ∀ x y : ℕ, Nat.Coprime x y → g (x * y) = g x * g y) (hone : g 1 = 1)
    {m : ℕ} (hm : m ≠ 0) (hmY : m ≤ Y) :
    ∑ ω : Fin (Y + 1) → Bool, cover g Y ω m = 2 ^ (Y + 1) * g m := by
  have key : ∑ ω : Fin (Y + 1) → Bool, cover g Y ω m =
      ∏ i : Fin (Y + 1), ∑ b : Bool, (if (i : ℕ) ∈ ppIndex m then lift b (g i) else 1) := by
    rw [Fintype.prod_sum (fun (i : Fin (Y + 1)) (b : Bool) =>
      (if (i : ℕ) ∈ ppIndex m then lift b (g i) else 1))]
    rfl
  have step : ∀ i : Fin (Y + 1),
      (∑ b : Bool, (if (i : ℕ) ∈ ppIndex m then lift b (g i) else 1)) =
        2 * (if (i : ℕ) ∈ ppIndex m then g (i : ℕ) else 1) := by
    intro i
    rw [Fintype.sum_bool]
    by_cases hi : (i : ℕ) ∈ ppIndex m
    · simp only [hi, if_true]
      exact lift_add_lift (g i)
    · simp only [hi, if_false]
      norm_num
  have hsub : ppIndex m ⊆ Finset.range (Y + 1) := by
    intro i hi
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le ((mem_ppIndex_le hm hi).trans hmY))
  have hfin : ∏ i : Fin (Y + 1), (if (i : ℕ) ∈ ppIndex m then g (i : ℕ) else 1) = g m := by
    calc ∏ i : Fin (Y + 1), (if (i : ℕ) ∈ ppIndex m then g (i : ℕ) else 1)
        = ∏ j ∈ Finset.range (Y + 1), (if j ∈ ppIndex m then g j else 1) :=
          (Finset.prod_range fun j => (if j ∈ ppIndex m then g j else 1)).symm
      _ = ∏ j ∈ Finset.range (Y + 1) ∩ ppIndex m, g j := Finset.prod_ite_mem _ _ _
      _ = ∏ j ∈ ppIndex m, g j := by rw [Finset.inter_eq_right.mpr hsub]
      _ = g m := prod_ppIndex g hmul hone hm
  rw [key, Finset.prod_congr rfl fun i _ => step i, Finset.prod_mul_distrib, hfin]
  simp


/-- At a prime `p ≤ Y` the cover is literally one of the two lifts of `g p`. -/
theorem cover_prime {p : ℕ} (hp : p.Prime) (hpY : p ≤ Y) (ω : Fin (Y + 1) → Bool) :
    cover g Y ω p = lift (ω ⟨p, Nat.lt_succ_of_le hpY⟩) (g p) := by
  have hpp : ppIndex p = {p} := by
    rw [ppIndex, Nat.Prime.primeFactors hp]
    simp [Nat.Prime.factorization hp]
  rw [cover]
  rw [Finset.prod_eq_single (⟨p, Nat.lt_succ_of_le hpY⟩ : Fin (Y + 1))]
  · simp [hpp]
  · intro i _ hi
    have : (i : ℕ) ≠ p := by
      intro h
      exact hi (Fin.ext h)
    simp [hpp, this]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- **The deterministic pretentious-transfer identity at a prime.**  Both signs give the same
real part, so the cover's distance to `g` does not depend on `ω` at all. -/
theorem re_cover_prime_mul_conj {p : ℕ} (hp : p.Prime) (hpY : p ≤ Y)
    (ω : Fin (Y + 1) → Bool) : (cover g Y ω p * conj (g p)).re = ‖g p‖ ^ 2 := by
  rw [cover_prime g Y hp hpY ω]
  exact re_lift_mul_conj (g p) _

/-! ## The averaging identity for the logarithmic correlation -/

open Erdos67b

/-- The zero-extension of the cover averages to the zero-extension of `g`, at every integer
argument `≤ Y` (both sides vanish at nonpositive arguments). -/
theorem sum_posExt_cover
    (hmul : ∀ x y : ℕ, Nat.Coprime x y → g (x * y) = g x * g y) (hone : g 1 = 1)
    {m : ℤ} (hm : m ≤ (Y : ℤ)) :
    ∑ ω : Fin (Y + 1) → Bool, positiveIntExtension (cover g Y ω) m
      = 2 ^ (Y + 1) * positiveIntExtension g m := by
  by_cases hpos : 0 < m
  · have hle : m.toNat ≤ Y := by omega
    have hne : m.toNat ≠ 0 := by omega
    have h1 : ∀ ω : Fin (Y + 1) → Bool,
        positiveIntExtension (cover g Y ω) m = cover g Y ω m.toNat := by
      intro ω; simp [positiveIntExtension, hpos]
    have h2 : positiveIntExtension g m = g m.toNat := by simp [positiveIntExtension, hpos]
    simp only [h1, h2]
    exact sum_cover g Y hmul hone hne hle
  · have h1 : ∀ ω : Fin (Y + 1) → Bool,
        positiveIntExtension (cover g Y ω) m = 0 := by
      intro ω; simp [positiveIntExtension, hpos]
    have h2 : positiveIntExtension g m = 0 := by simp [positiveIntExtension, hpos]
    simp [h1, h2]

/-- **The correlation is the average of the covers' correlations.** -/
theorem sum_sum_elliottLogCorrelation_cover (g₁ g₂ : ℕ → ℂ) (Y : ℕ)
    (h1mul : ∀ x y : ℕ, Nat.Coprime x y → g₁ (x * y) = g₁ x * g₁ y) (h1one : g₁ 1 = 1)
    (h2mul : ∀ x y : ℕ, Nat.Coprime x y → g₂ (x * y) = g₂ x * g₂ y) (h2one : g₂ 1 = 1)
    {a₁ a₂ : ℕ} {b₁ b₂ : ℤ} {X W : ℕ}
    (hY₁ : ∀ n ∈ elliottLogWindow X W, integerAffine a₁ b₁ n ≤ (Y : ℤ))
    (hY₂ : ∀ n ∈ elliottLogWindow X W, integerAffine a₂ b₂ n ≤ (Y : ℤ)) :
    ∑ ω₁ : Fin (Y + 1) → Bool, ∑ ω₂ : Fin (Y + 1) → Bool,
        elliottLogCorrelation (positiveIntExtension (cover g₁ Y ω₁))
          (positiveIntExtension (cover g₂ Y ω₂)) a₁ a₂ b₁ b₂ X W
      = (2 ^ (Y + 1) : ℂ) * 2 ^ (Y + 1) *
          elliottLogCorrelation (positiveIntExtension g₁) (positiveIntExtension g₂)
            a₁ a₂ b₁ b₂ X W := by
  classical
  simp only [elliottLogCorrelation]
  have swap1 : ∀ ω₁ : Fin (Y + 1) → Bool,
      (∑ ω₂ : Fin (Y + 1) → Bool, ∑ n ∈ elliottLogWindow X W,
          (harmonicWeight n : ℂ) * positiveIntExtension (cover g₁ Y ω₁) (integerAffine a₁ b₁ n) *
            positiveIntExtension (cover g₂ Y ω₂) (integerAffine a₂ b₂ n))
        = ∑ n ∈ elliottLogWindow X W, ∑ ω₂ : Fin (Y + 1) → Bool,
          (harmonicWeight n : ℂ) * positiveIntExtension (cover g₁ Y ω₁) (integerAffine a₁ b₁ n) *
            positiveIntExtension (cover g₂ Y ω₂) (integerAffine a₂ b₂ n) :=
    fun _ => Finset.sum_comm
  calc ∑ ω₁ : Fin (Y + 1) → Bool, ∑ ω₂ : Fin (Y + 1) → Bool, ∑ n ∈ elliottLogWindow X W,
          (harmonicWeight n : ℂ) * positiveIntExtension (cover g₁ Y ω₁) (integerAffine a₁ b₁ n) *
            positiveIntExtension (cover g₂ Y ω₂) (integerAffine a₂ b₂ n)
      = ∑ ω₁ : Fin (Y + 1) → Bool, ∑ n ∈ elliottLogWindow X W, ∑ ω₂ : Fin (Y + 1) → Bool,
          (harmonicWeight n : ℂ) * positiveIntExtension (cover g₁ Y ω₁) (integerAffine a₁ b₁ n) *
            positiveIntExtension (cover g₂ Y ω₂) (integerAffine a₂ b₂ n) :=
        Finset.sum_congr rfl fun ω₁ _ => swap1 ω₁
    _ = ∑ n ∈ elliottLogWindow X W, ∑ ω₁ : Fin (Y + 1) → Bool, ∑ ω₂ : Fin (Y + 1) → Bool,
          (harmonicWeight n : ℂ) * positiveIntExtension (cover g₁ Y ω₁) (integerAffine a₁ b₁ n) *
            positiveIntExtension (cover g₂ Y ω₂) (integerAffine a₂ b₂ n) := Finset.sum_comm
    _ = ∑ n ∈ elliottLogWindow X W, ((2 ^ (Y + 1) : ℂ) * 2 ^ (Y + 1)) *
          ((harmonicWeight n : ℂ) * positiveIntExtension g₁ (integerAffine a₁ b₁ n) *
            positiveIntExtension g₂ (integerAffine a₂ b₂ n)) := by
        refine Finset.sum_congr rfl fun n hn => ?_
        have e₁ := sum_posExt_cover g₁ Y h1mul h1one (hY₁ n hn)
        have e₂ := sum_posExt_cover g₂ Y h2mul h2one (hY₂ n hn)
        rw [← Finset.sum_mul_sum, ← Finset.mul_sum, e₁, e₂]
        ring
    _ = (2 ^ (Y + 1) : ℂ) * 2 ^ (Y + 1) * ∑ n ∈ elliottLogWindow X W,
          ((harmonicWeight n : ℂ) * positiveIntExtension g₁ (integerAffine a₁ b₁ n) *
            positiveIntExtension g₂ (integerAffine a₂ b₂ n)) := by
        rw [Finset.mul_sum]

/-- **The decisive corollary.**  The correlation of a pair of `1`-bounded multiplicative functions
is dominated by the correlation of a pair of *unimodular* multiplicative functions, which are
moreover lifts of the originals at every prime `≤ Y` — so the pretentious hypothesis transfers. -/
theorem exists_cover_pair_ge (g₁ g₂ : ℕ → ℂ) (Y : ℕ)
    (h1mul : ∀ x y : ℕ, Nat.Coprime x y → g₁ (x * y) = g₁ x * g₁ y) (h1one : g₁ 1 = 1)
    (h1b : ∀ n : ℕ, ‖g₁ n‖ ≤ 1)
    (h2mul : ∀ x y : ℕ, Nat.Coprime x y → g₂ (x * y) = g₂ x * g₂ y) (h2one : g₂ 1 = 1)
    (h2b : ∀ n : ℕ, ‖g₂ n‖ ≤ 1)
    {a₁ a₂ : ℕ} {b₁ b₂ : ℤ} {X W : ℕ}
    (hY₁ : ∀ n ∈ elliottLogWindow X W, integerAffine a₁ b₁ n ≤ (Y : ℤ))
    (hY₂ : ∀ n ∈ elliottLogWindow X W, integerAffine a₂ b₂ n ≤ (Y : ℤ)) :
    ∃ u₁ u₂ : ℕ → ℂ,
      (u₁ 1 = 1) ∧ (∀ x y : ℕ, Nat.Coprime x y → u₁ (x * y) = u₁ x * u₁ y) ∧
      (∀ n : ℕ, ‖u₁ n‖ = 1) ∧
      (u₂ 1 = 1) ∧ (∀ x y : ℕ, Nat.Coprime x y → u₂ (x * y) = u₂ x * u₂ y) ∧
      (∀ n : ℕ, ‖u₂ n‖ = 1) ∧
      (∀ p : ℕ, p.Prime → p ≤ Y → (u₁ p * conj (g₁ p)).re = ‖g₁ p‖ ^ 2) ∧
      (∀ p : ℕ, p.Prime → p ≤ Y → (u₂ p * conj (g₂ p)).re = ‖g₂ p‖ ^ 2) ∧
      ‖elliottLogCorrelation (positiveIntExtension g₁) (positiveIntExtension g₂)
          a₁ a₂ b₁ b₂ X W‖ ≤
        ‖elliottLogCorrelation (positiveIntExtension u₁) (positiveIntExtension u₂)
          a₁ a₂ b₁ b₂ X W‖ := by
  classical
  set C : ℝ := ‖elliottLogCorrelation (positiveIntExtension g₁) (positiveIntExtension g₂)
      a₁ a₂ b₁ b₂ X W‖ with hC
  set N : ℕ := 2 ^ (Y + 1) with hN
  have hsum := sum_sum_elliottLogCorrelation_cover g₁ g₂ Y h1mul h1one h2mul h2one hY₁ hY₂
  have hcard : (Fintype.card (Fin (Y + 1) → Bool)) = N := by
    simp [hN, Fintype.card_fun]
  -- the triangle inequality on the double sum
  have hkey : ((N : ℝ) * N) * C ≤
      ∑ ω₁ : Fin (Y + 1) → Bool, ∑ ω₂ : Fin (Y + 1) → Bool,
        ‖elliottLogCorrelation (positiveIntExtension (cover g₁ Y ω₁))
          (positiveIntExtension (cover g₂ Y ω₂)) a₁ a₂ b₁ b₂ X W‖ := by
    have : ((N : ℝ) * N) * C =
        ‖∑ ω₁ : Fin (Y + 1) → Bool, ∑ ω₂ : Fin (Y + 1) → Bool,
          elliottLogCorrelation (positiveIntExtension (cover g₁ Y ω₁))
            (positiveIntExtension (cover g₂ Y ω₂)) a₁ a₂ b₁ b₂ X W‖ := by
      rw [hsum, hC, norm_mul, norm_mul]
      push_cast
      simp [hN]
    rw [this]
    exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun ω₁ _ => norm_sum_le _ _)
  -- pigeonhole
  have hne : (Finset.univ : Finset ((Fin (Y + 1) → Bool) × (Fin (Y + 1) → Bool))).Nonempty :=
    Finset.univ_nonempty
  have hflat : ∑ ω₁ : Fin (Y + 1) → Bool, ∑ ω₂ : Fin (Y + 1) → Bool,
        ‖elliottLogCorrelation (positiveIntExtension (cover g₁ Y ω₁))
          (positiveIntExtension (cover g₂ Y ω₂)) a₁ a₂ b₁ b₂ X W‖
      = ∑ q : (Fin (Y + 1) → Bool) × (Fin (Y + 1) → Bool),
        ‖elliottLogCorrelation (positiveIntExtension (cover g₁ Y q.1))
          (positiveIntExtension (cover g₂ Y q.2)) a₁ a₂ b₁ b₂ X W‖ := by
    rw [Fintype.sum_prod_type]
  have hconst : ∑ _q : (Fin (Y + 1) → Bool) × (Fin (Y + 1) → Bool), C = ((N : ℝ) * N) * C := by
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [Fintype.card_prod, hcard]
    push_cast
    ring
  have hle : ∑ _q : (Fin (Y + 1) → Bool) × (Fin (Y + 1) → Bool), C
      ≤ ∑ q : (Fin (Y + 1) → Bool) × (Fin (Y + 1) → Bool),
        ‖elliottLogCorrelation (positiveIntExtension (cover g₁ Y q.1))
          (positiveIntExtension (cover g₂ Y q.2)) a₁ a₂ b₁ b₂ X W‖ := by
    rw [hconst, ← hflat]
    exact hkey
  obtain ⟨q, -, hq⟩ := Finset.exists_le_of_sum_le hne hle
  refine ⟨cover g₁ Y q.1, cover g₂ Y q.2, cover_one g₁ Y q.1,
    fun x y h => ?_, fun n => ?_, cover_one g₂ Y q.2, fun x y h => ?_, fun n => ?_,
    fun p hp hpY => ?_, fun p hp hpY => ?_, hq⟩
  · rcases Nat.eq_zero_or_pos x with rfl | hx
    · simp [Nat.coprime_zero_left] at h
      subst h
      simp [cover_one]
    · rcases Nat.eq_zero_or_pos y with rfl | hy
      · simp [Nat.coprime_zero_right] at h
        subst h
        simp [cover_one]
      · exact cover_mul_of_coprime g₁ Y q.1 hx.ne' hy.ne' h
  · exact norm_cover g₁ Y h1b q.1 n
  · rcases Nat.eq_zero_or_pos x with rfl | hx
    · simp [Nat.coprime_zero_left] at h
      subst h
      simp [cover_one]
    · rcases Nat.eq_zero_or_pos y with rfl | hy
      · simp [Nat.coprime_zero_right] at h
        subst h
        simp [cover_one]
      · exact cover_mul_of_coprime g₂ Y q.2 hx.ne' hy.ne' h
  · exact norm_cover g₂ Y h2b q.2 n
  · exact re_cover_prime_mul_conj g₁ Y hp hpY q.1
  · exact re_cover_prime_mul_conj g₂ Y hp hpY q.2

end

end NormalNumbers.ElliottRandomize
