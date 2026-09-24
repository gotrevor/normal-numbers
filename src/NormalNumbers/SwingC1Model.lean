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

/-! ### Elementary geometry of unit vectors and phases -/

/-- Two unit vectors a fixed distance apart have a short sum:
`‖z‖ = ‖w‖ = 1`, `d ≤ ‖z − w‖` gives `‖z + w‖ ≤ 2 − d²/4`. -/
lemma norm_add_le_of_norm_sub_ge {z w : ℂ} (hz : ‖z‖ = 1) (hw : ‖w‖ = 1)
    {d : ℝ} (hd0 : 0 ≤ d) (hd : d ≤ ‖z - w‖) : ‖z + w‖ ≤ 2 - d ^ 2 / 4 := by
  have hpar : ‖z + w‖ ^ 2 + ‖z - w‖ ^ 2 = 2 * (‖z‖ ^ 2 + ‖w‖ ^ 2) :=
    parallelogram_law_with_norm ℝ z w
  rw [hz, hw] at hpar
  have hsub2 : ‖z - w‖ ≤ 2 := by
    calc ‖z - w‖ ≤ ‖z‖ + ‖w‖ := norm_sub_le _ _
      _ = 2 := by rw [hz, hw]; ring
  have hd2 : d ≤ 2 := le_trans hd hsub2
  have hsq : ‖z + w‖ * ‖z + w‖ ≤ 4 - d * d := by nlinarith [norm_nonneg (z - w)]
  nlinarith [norm_nonneg (z + w)]

lemma norm_phase_sub_phase (x y : ℝ) : ‖phase x - phase y‖ = ‖phase (x - y) - 1‖ := by
  have : phase x - phase y = phase y * (phase (x - y) - 1) := by
    rw [mul_sub, mul_one, ← phase_add]; ring_nf
  rw [this, norm_mul, norm_phase, one_mul]

/-- `‖e(u) − 1‖ ≤ 4π|u|` whenever `2π|u| ≤ 1`. -/
lemma norm_phase_sub_one_le {u : ℝ} (hu : 2 * Real.pi * |u| ≤ 1) :
    ‖phase u - 1‖ ≤ 4 * Real.pi * |u| := by
  have hz : ‖(2 * (Real.pi : ℂ) * Complex.I * (u : ℂ))‖ = 2 * Real.pi * |u| := by
    rw [norm_mul, norm_mul, norm_mul]
    simp [Complex.norm_I, abs_of_pos Real.pi_pos]
  have := Complex.norm_exp_sub_one_le (x := 2 * (Real.pi : ℂ) * Complex.I * (u : ℂ))
    (by rw [hz]; exact hu)
  rw [hz] at this
  calc ‖phase u - 1‖ = ‖Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (u : ℂ)) - 1‖ := rfl
    _ ≤ 2 * (2 * Real.pi * |u|) := this
    _ = 4 * Real.pi * |u| := by ring

/-- `e(t) ≠ 1` for `0 < |t| < 1`. -/
lemma phase_ne_one {t : ℝ} (ht0 : t ≠ 0) (ht1 : |t| < 1) : phase t ≠ 1 := by
  intro hcon
  rw [phase, Complex.exp_eq_one_iff] at hcon
  obtain ⟨n, hn⟩ := hcon
  have h2 : ((t : ℂ)) = (n : ℂ) := by field_simp at hn; linear_combination hn
  have ht : t = (n : ℝ) := by exact_mod_cast h2
  rcases eq_or_ne n 0 with rfl | hn0
  · simp [ht] at ht0
  · have : (1 : ℝ) ≤ |(n : ℝ)| := by
      rw [← Int.cast_abs]
      exact_mod_cast Int.one_le_abs (by omega)
    rw [ht] at ht1; linarith

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
  classical
  have hb1 : (1 : ℝ) < (b : ℝ) := by exact_mod_cast hb
  have hbpos : (0 : ℝ) < (b : ℝ) := by linarith
  have hπ : (0 : ℝ) < Real.pi := Real.pi_pos
  -- a fixed nonzero frequency `t` with `|t| < 1/2`
  obtain ⟨i, hi⟩ := pow_unbounded_of_one_lt (2 * |h|) hb1
  have hbi : (2 : ℝ) * |h| < (b : ℝ) ^ (1 + i) := by
    have : (b : ℝ) ^ i ≤ (b : ℝ) ^ (1 + i) :=
      pow_le_pow_right₀ hb1.le (by omega)
    linarith
  set t : ℝ := h / (b : ℝ) ^ (1 + i) with ht_def
  have hbiPos : (0 : ℝ) < (b : ℝ) ^ (1 + i) := by positivity
  have ht0 : t ≠ 0 := by
    rw [ht_def]; exact div_ne_zero hh (ne_of_gt hbiPos)
  have habs : |t| = |h| / (b : ℝ) ^ (1 + i) := by
    rw [ht_def, abs_div, abs_of_pos hbiPos]
  have ht_half : |t| < 1 / 2 := by
    rw [habs, div_lt_iff₀ hbiPos]; linarith
  -- the separation `δ`
  set δ : ℝ := ‖phase t - 1‖ with hδ_def
  have hδpos : 0 < δ := by
    rw [hδ_def, norm_pos_iff, sub_ne_zero]
    exact phase_ne_one ht0 (by linarith [ht_half, abs_nonneg t])
  refine ⟨δ ^ 2 / 16, by positivity, ?_⟩
  set M : ℝ := |t| + |h| + 1 with hM_def
  have hMpos : 0 < M := by
    have := abs_nonneg t; have := abs_nonneg h; rw [hM_def]; linarith
  obtain ⟨N₀, hN₀⟩ := exists_nat_gt (64 * Real.pi * M / δ + 2 * Real.pi * M)
  refine Filter.eventually_atTop.mpr ⟨max N₀ (i + 2), fun p hp hpp => ?_⟩
  have hpN : N₀ ≤ p := le_trans (le_max_left _ _) hp
  have hpi2 : i + 2 ≤ p := le_trans (le_max_right _ _) hp
  have hppos : 0 < p := by omega
  have hpR : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hppos
  have hbig : 64 * Real.pi * M / δ + 2 * Real.pi * M < (p : ℝ) :=
    lt_of_lt_of_le hN₀ (by exact_mod_cast hpN)
  have hMd : 0 ≤ 64 * Real.pi * M / δ := by positivity
  have hM2 : 0 ≤ 2 * Real.pi * M := by positivity
  have hbig1 : 64 * Real.pi * M / δ < (p : ℝ) := by linarith
  have hbig2 : 2 * Real.pi * M < (p : ℝ) := by linarith
  -- `b^p − 1 ≥ p`
  set K : ℝ := (b : ℝ) ^ p - 1 with hK_def
  have hpowb : ((p : ℝ) + 1) ≤ (b : ℝ) ^ p := by
    have h1 : (p : ℝ) + 1 ≤ (2 : ℝ) ^ p := by
      have := Nat.lt_two_pow_self (n := p)
      have : (p : ℝ) + 1 ≤ ((2 ^ p : ℕ) : ℝ) := by exact_mod_cast Nat.succ_le_of_lt this
      simpa using this
    have h2 : (2 : ℝ) ^ p ≤ (b : ℝ) ^ p :=
      pow_le_pow_left₀ (by norm_num) (by exact_mod_cast hb) p
    linarith
  have hKp : (p : ℝ) ≤ K := by rw [hK_def]; linarith
  have hKpos : (0 : ℝ) < K := lt_of_lt_of_le hpR hKp
  have hKne : (b : ℝ) ^ p - 1 ≠ 0 := by rw [← hK_def]; exact ne_of_gt hKpos
  -- the two terms of the local average
  set s₁ : ℕ := p - 1 - i with hs1_def
  have hs1lt : s₁ < p := by omega
  have hs1ne : (0 : ℕ) ≠ s₁ := by omega
  have hterm : ∀ s : ℕ, s < p → primePeriodicTerm b p s = (b : ℝ) ^ s / K := by
    intro s hs
    rw [primePeriodicTerm, if_pos hpp, Nat.mod_eq_of_lt hs, hK_def]
  -- the top term is close to `e(t)`
  have hpowsplit : (b : ℝ) ^ s₁ = (b : ℝ) ^ p / (b : ℝ) ^ (1 + i) := by
    rw [eq_div_iff (ne_of_gt hbiPos), ← pow_add]
    congr 1
    omega
  have hdiff1 : h * primePeriodicTerm b p s₁ - t = t / K := by
    rw [hterm s₁ hs1lt, ht_def, hpowsplit, hK_def]
    field_simp
    ring
  -- quantitative closeness
  have hclose : ∀ x : ℝ, |x| ≤ M → ‖phase (x / K) - 1‖ ≤ δ / 4 := by
    intro x hx
    have hxK : |x / K| ≤ M / (p : ℝ) := by
      rw [abs_div, abs_of_pos hKpos, div_le_div_iff₀ hKpos hpR]
      nlinarith [abs_nonneg x, hMpos, hpR, hKp, hx]
    have hkey2 : 2 * Real.pi * (M / (p : ℝ)) ≤ 1 := by
      have e : 2 * Real.pi * (M / (p : ℝ)) = (2 * Real.pi * M) / (p : ℝ) := by ring
      rw [e, div_le_one hpR]; linarith
    have hkey4 : 4 * Real.pi * (M / (p : ℝ)) ≤ δ / 4 := by
      have e : 4 * Real.pi * (M / (p : ℝ)) = (4 * Real.pi * M) / (p : ℝ) := by ring
      rw [e, div_le_div_iff₀ hpR (by norm_num : (0:ℝ) < 4)]
      have hpd : 64 * Real.pi * M < δ * (p : ℝ) := by
        rw [div_lt_iff₀ hδpos] at hbig1; linarith
      nlinarith [hMpos, Real.pi_pos]
    have hm2 : 2 * Real.pi * |x / K| ≤ 2 * Real.pi * (M / (p : ℝ)) :=
      mul_le_mul_of_nonneg_left hxK (by positivity)
    have hm4 : 4 * Real.pi * |x / K| ≤ 4 * Real.pi * (M / (p : ℝ)) :=
      mul_le_mul_of_nonneg_left hxK (by positivity)
    have := norm_phase_sub_one_le (u := x / K) (by linarith)
    linarith
  have hMt : |t| ≤ M := by rw [hM_def]; linarith [abs_nonneg h]
  have hMh : |h| ≤ M := by rw [hM_def]; linarith [abs_nonneg t]
  set z₁ : ℂ := phase (h * primePeriodicTerm b p s₁) with hz1_def
  set z₀ : ℂ := phase (h * primePeriodicTerm b p 0) with hz0_def
  have hc1 : ‖z₁ - phase t‖ ≤ δ / 4 := by
    rw [hz1_def, norm_phase_sub_phase, hdiff1]; exact hclose t hMt
  have hc0 : ‖z₀ - 1‖ ≤ δ / 4 := by
    have hp0 : phase 0 = 1 := by simp [phase]
    have hzz : z₀ - 1 = phase (h * primePeriodicTerm b p 0) - phase 0 := by
      rw [hz0_def, hp0]
    rw [hzz, norm_phase_sub_phase, sub_zero, hterm 0 hppos]
    have : h * ((b : ℝ) ^ 0 / K) = h / K := by
      rw [pow_zero, mul_one_div]
    rw [this]; exact hclose h hMh
  -- separation
  have hsep : δ / 2 ≤ ‖z₁ - z₀‖ := by
    have htri : δ ≤ ‖phase t - z₁‖ + ‖z₁ - z₀‖ + ‖z₀ - 1‖ := by
      have he : phase t - 1 = (phase t - z₁) + (z₁ - z₀) + (z₀ - 1) := by ring
      calc δ = ‖phase t - 1‖ := hδ_def
        _ = ‖(phase t - z₁) + (z₁ - z₀) + (z₀ - 1)‖ := by rw [he]
        _ ≤ ‖(phase t - z₁) + (z₁ - z₀)‖ + ‖z₀ - 1‖ := norm_add_le _ _
        _ ≤ ‖phase t - z₁‖ + ‖z₁ - z₀‖ + ‖z₀ - 1‖ := by
            have := norm_add_le (phase t - z₁) (z₁ - z₀); linarith
    have : ‖phase t - z₁‖ = ‖z₁ - phase t‖ := norm_sub_rev _ _
    linarith [hc1, hc0, this]
  have hpair : ‖z₁ + z₀‖ ≤ 2 - δ ^ 2 / 16 := by
    have := norm_add_le_of_norm_sub_ge (z := z₁) (w := z₀) (norm_phase _) (norm_phase _)
      (d := δ / 2) (by linarith) hsep
    calc ‖z₁ + z₀‖ ≤ 2 - (δ / 2) ^ 2 / 4 := this
      _ = 2 - δ ^ 2 / 16 := by ring
  -- split the sum
  have hsub : ({0, s₁} : Finset ℕ) ⊆ range p := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact Finset.mem_range.mpr hppos
    · exact Finset.mem_range.mpr hs1lt
  have hcard : (range p \ ({0, s₁} : Finset ℕ)).card = p - 2 := by
    rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hsub, Finset.card_range, Finset.card_insert_of_notMem (by simpa using hs1ne),
      Finset.card_singleton]
  have hrest : ‖∑ s ∈ range p \ ({0, s₁} : Finset ℕ), phase (h * primePeriodicTerm b p s)‖
      ≤ ((p : ℝ) - 2) := by
    calc ‖∑ s ∈ range p \ ({0, s₁} : Finset ℕ), phase (h * primePeriodicTerm b p s)‖
        ≤ ∑ s ∈ range p \ ({0, s₁} : Finset ℕ), ‖phase (h * primePeriodicTerm b p s)‖ :=
          norm_sum_le _ _
      _ = ((p - 2 : ℕ) : ℝ) := by simp [hcard]
      _ = ((p : ℝ) - 2) := by
          have : (2 : ℕ) ≤ p := by omega
          rw [Nat.cast_sub this]; norm_num
  have hsum : ‖∑ s ∈ range p, phase (h * primePeriodicTerm b p s)‖ ≤ (p : ℝ) - δ ^ 2 / 16 := by
    rw [← Finset.sum_sdiff hsub, Finset.sum_pair hs1ne]
    calc ‖(∑ s ∈ range p \ ({0, s₁} : Finset ℕ), phase (h * primePeriodicTerm b p s))
            + (phase (h * primePeriodicTerm b p 0) + phase (h * primePeriodicTerm b p s₁))‖
        ≤ ‖∑ s ∈ range p \ ({0, s₁} : Finset ℕ), phase (h * primePeriodicTerm b p s)‖
            + ‖phase (h * primePeriodicTerm b p 0) + phase (h * primePeriodicTerm b p s₁)‖ :=
          norm_add_le _ _
      _ ≤ ((p : ℝ) - 2) + (2 - δ ^ 2 / 16) := by
          have hcomm : ‖z₀ + z₁‖ = ‖z₁ + z₀‖ := by rw [add_comm]
          rw [← hz0_def, ← hz1_def]
          linarith [hrest, hpair, hcomm]
      _ = (p : ℝ) - δ ^ 2 / 16 := by ring
  rw [localFactor, norm_div, Complex.norm_natCast, div_le_iff₀ hpR]
  have : (1 - δ ^ 2 / 16 / (p : ℝ)) * (p : ℝ) = (p : ℝ) - δ ^ 2 / 16 := by
    field_simp
  rw [this]
  exact hsum

set_option maxHeartbeats 1600000 in
/-- **Mertens drives any `1 − c/p` product to zero.**  If a family of local factors is bounded by
`1` everywhere and by `1 − c/p` for all large primes, its partial products over the primes `≤ P`
tend to `0` — because `Σ_p 1/p = ∞`.  This is the shared engine of leaf (M) and of the pair
factors of `SwingC1Pair.lean`. -/
theorem prod_tendsto_zero_of_norm_le (F : ℕ → ℂ) (hF1 : ∀ p : ℕ, 0 < p → ‖F p‖ ≤ 1)
    {c : ℝ} (hc : 0 < c) (hev : ∀ᶠ p : ℕ in atTop, p.Prime → ‖F p‖ ≤ 1 - c / p) :
    Tendsto (fun P => ‖∏ p ∈ primesLe P, F p‖) atTop (𝓝 0) := by
  classical
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hev
  set g : ℕ → ℝ := Set.indicator {p | p.Prime} (fun n => (1 : ℝ) / n) with hg_def
  have hgnn : ∀ n, 0 ≤ g n := by
    intro n
    rw [hg_def]
    exact Set.indicator_nonneg (fun m _ => by positivity) n
  have hgval : ∀ n : ℕ, g n = if n.Prime then (1 : ℝ) / n else 0 := by
    intro n
    rw [hg_def, Set.indicator_apply]
    simp
  have hdiv : Tendsto (fun n => ∑ i ∈ range n, g i) atTop atTop :=
    (not_summable_iff_tendsto_nat_atTop_of_nonneg hgnn).mp
      (by rw [hg_def]; exact not_summable_one_div_on_primes)
  set SS : ℕ → ℝ := fun n => ∑ i ∈ range n, g i with hSS_def
  set C : ℝ := SS N with hC_def
  -- the partial sum of prime reciprocals up to `P` is exactly `SS (P+1)`
  have hSSeq : ∀ P : ℕ, SS (P + 1) = ∑ p ∈ primesLe P, (1 : ℝ) / p := by
    intro P
    rw [hSS_def, primesLe, Finset.sum_filter]
    exact Finset.sum_congr rfl fun n _ => hgval n
  -- the product bound
  have hbound : ∀ P : ℕ, ‖∏ p ∈ primesLe P, F p‖
      ≤ Real.exp (-(c * (SS (P + 1) - C))) := by
    intro P
    set v : ℕ → ℝ := fun p => if N ≤ p then -(c / p) else 0 with hv_def
    have hstep : ‖∏ p ∈ primesLe P, F p‖
        ≤ ∏ p ∈ primesLe P, Real.exp (v p) := by
      rw [norm_prod]
      refine Finset.prod_le_prod (fun p _ => norm_nonneg _) (fun p hp => ?_)
      by_cases hpN : N ≤ p
      · have h1 : ‖F p‖ ≤ 1 - c / p := hN p hpN (prime_of_mem_primesLe hp)
        have h2 : 1 - c / (p : ℝ) ≤ Real.exp (-(c / p)) := by
          have := Real.add_one_le_exp (-(c / (p : ℝ)))
          linarith
        rw [hv_def]; simp only [if_pos hpN]; linarith
      · have h1 : ‖F p‖ ≤ 1 := hF1 p (prime_of_mem_primesLe hp).pos
        rw [hv_def]; simp only [if_neg hpN, Real.exp_zero]; exact h1
    have hprodexp : ∏ p ∈ primesLe P, Real.exp (v p) = Real.exp (∑ p ∈ primesLe P, v p) :=
      (Real.exp_sum _ _).symm
    have hsumv : ∑ p ∈ primesLe P, v p
        = -(c * ∑ p ∈ (primesLe P).filter (fun p => N ≤ p), (1 : ℝ) / p) := by
      rw [Finset.sum_filter, Finset.mul_sum, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun p _ => ?_
      by_cases hpN : N ≤ p
      · rw [hv_def]; simp only [if_pos hpN]; rw [mul_one_div]
      · rw [hv_def]; simp only [if_neg hpN]; ring
    -- the small primes drop at most `C`
    have hsmall : ∑ p ∈ (primesLe P).filter (fun p => ¬ N ≤ p), (1 : ℝ) / p ≤ C := by
      have heq : ∑ p ∈ (primesLe P).filter (fun p => ¬ N ≤ p), (1 : ℝ) / p
          = ∑ p ∈ (primesLe P).filter (fun p => ¬ N ≤ p), g p := by
        refine Finset.sum_congr rfl fun x hx => ?_
        simp only [Finset.mem_filter] at hx
        rw [hgval, if_pos (prime_of_mem_primesLe hx.1)]
      rw [heq, hC_def, hSS_def]
      refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun i _ _ => hgnn i)
      intro x hx
      simp only [Finset.mem_filter] at hx
      obtain ⟨-, hx2⟩ := hx
      exact Finset.mem_range.mpr (by omega)
    have hsplit : ∑ p ∈ (primesLe P).filter (fun p => N ≤ p), (1 : ℝ) / p
        + ∑ p ∈ (primesLe P).filter (fun p => ¬ N ≤ p), (1 : ℝ) / p
        = SS (P + 1) := by
      rw [hSSeq P, Finset.sum_filter_add_sum_filter_not]
    have hTge : SS (P + 1) - C
        ≤ ∑ p ∈ (primesLe P).filter (fun p => N ≤ p), (1 : ℝ) / p := by
      linarith [hsplit, hsmall]
    calc ‖∏ p ∈ primesLe P, F p‖
        ≤ ∏ p ∈ primesLe P, Real.exp (v p) := hstep
      _ = Real.exp (∑ p ∈ primesLe P, v p) := hprodexp
      _ = Real.exp (-(c * ∑ p ∈ (primesLe P).filter (fun p => N ≤ p), (1 : ℝ) / p)) := by
          rw [hsumv]
      _ ≤ Real.exp (-(c * (SS (P + 1) - C))) := by
          apply Real.exp_le_exp.mpr
          have : c * (SS (P + 1) - C)
              ≤ c * ∑ p ∈ (primesLe P).filter (fun p => N ≤ p), (1 : ℝ) / p :=
            mul_le_mul_of_nonneg_left hTge hc.le
          linarith
  -- and the bound tends to zero
  have h1 : Tendsto (fun P : ℕ => SS (P + 1)) atTop atTop :=
    hdiv.comp (tendsto_add_atTop_nat 1)
  have h2 : Tendsto (fun P : ℕ => c * (SS (P + 1) - C)) atTop atTop := by
    have h1' : Tendsto (fun P : ℕ => SS (P + 1) - C) atTop atTop := by
      simpa [sub_eq_add_neg] using tendsto_atTop_add_const_right atTop (-C) h1
    exact Filter.Tendsto.const_mul_atTop hc h1'
  have h3 : Tendsto (fun P : ℕ => Real.exp (-(c * (SS (P + 1) - C)))) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp h2)
  exact squeeze_zero (fun P => norm_nonneg _) hbound h3

/-- **Leaf (M)(c).**  Mertens: `Σ_p 1/p = ∞`, so `Π_{p ≤ P}(1 − c/p) → 0`, hence the model term
vanishes as the cut `P → ∞`.  This is the statement that the small primes alone already
randomise the orbit — the only *unconditional* source of randomness in the whole route. -/
theorem prod_localFactor_tendsto_zero (b : ℕ) (hb : 2 ≤ b) (h : ℝ) (hh : h ≠ 0) :
    Tendsto (fun P => ‖∏ p ∈ primesLe P, localFactor b h p‖) atTop (𝓝 0) := by
  obtain ⟨c, hc, hev⟩ := norm_localFactor_le b hb h hh
  exact prod_tendsto_zero_of_norm_le (localFactor b h)
    (fun p hp => norm_localFactor_le_one b h p hp) hc hev

/-- **Leaf (M), assembled.**  The model term of the split vanishes. -/
theorem periodMean_tendsto_zero (b : ℕ) (hb : 2 ≤ b) (h : ℝ) (hh : h ≠ 0) :
    Tendsto (fun P => ‖periodMean (fun n => phase (h * truncTail b P n)) (primorialLe P)‖)
      atTop (𝓝 0) := by
  simpa only [periodMean_phase_truncTail] using prod_localFactor_tendsto_zero b hb h hh

end NormalNumbers.CastingOut
