import NormalNumbers.DelangeSlotMaster

/-!
# Rung 2, layer 5: the additive twist

Assembles `charSum_tendsto_zero` (master dichotomy) with the unfolding identity
`sum_mul_left_expand` into the twisted mean
`∑_{m ≤ N} e(jm/Q) z^{ω_{>P}(m)} = o(N)`.

Route (see `HANDOFF-2026-09-24-delange-rung1-done-rung2-assembly.md`):

1. `isCharLike_dirichlet` — a `DirichletCharacter ℂ M` is `IsCharLike M`.
2. `innerTwist_tendsto_zero` — for character-like `κ` and any `c ≠ 0`,
   `∑_{m ≤ y} κ(m) z^{ω_{>P}(c·m)} = o(y)`, by `sum_mul_left_expand` + `charSum_tendsto_zero`.
3. `coprimeClass_tendsto_zero` — orthogonality turns the indicator of a *unit* residue class
   mod `Q'` into an average of characters, giving `∑_{m ≤ y, m ≡ b [Q']} z^{ω_{>P}(c·m)} = o(y)`.
4. `classSum_reindex` — `m = e·m'` with `e = gcd(a,Q)`, `Q' = Q/e`, `b = a/e` moves a *general*
   residue class mod `Q` to a *unit* class mod `Q'`.  This is why no induction on `Q` is needed.
5. The headline: regroup `∑_{m ≤ N}` by `m % Q`.
-/

open Finset Filter Topology Complex Real

namespace NormalNumbers.DelangeSlot

/-! ### Step 1: Dirichlet characters are character-like -/

lemma isCharLike_dirichlet {M : ℕ} (hM : 0 < M) (χ : DirichletCharacter ℂ M) :
    IsCharLike M (fun n : ℕ => χ (n : ZMod M)) where
  pos := hM
  mul := by intro a b; push_cast; exact map_mul _ _ _
  per := by
    intro a b hab
    have : (a : ZMod M) = (b : ZMod M) := (ZMod.natCast_eq_natCast_iff' a b M).2 hab
    rw [this]
  zero := by
    intro n hn
    refine χ.map_nonunit ?_
    rw [ZMod.isUnit_iff_coprime]
    exact hn
  norm_le := by
    intro n
    have := DirichletCharacter.norm_le_one χ (n : ZMod M)
    simpa using this

/-! ### Step 2: the inner twisted sum -/

/-- For character-like `κ` and any fixed `c ≠ 0`, the mean of `κ(m)·z^{ω_{>P}(c·m)}`
tends to `0`. -/
theorem innerTwist_tendsto_zero {M : ℕ} {κ : ℕ → ℂ} (h : IsCharLike M κ) {z : ℂ}
    (hz : ‖z‖ = 1) (hz1 : z ≠ 1) (P : ℕ) {c : ℕ} (hc : c ≠ 0) :
    Tendsto (fun y : ℕ => (∑ m ∈ Ioc 0 y, κ m * hfun z P (c * m)) / (y : ℂ)) atTop (𝓝 0) := by
  classical
  have hrw : ∀ y : ℕ, (∑ m ∈ Ioc 0 y, κ m * hfun z P (c * m)) / (y : ℂ)
      = ∑ U ∈ (bigPrimes P c).powerset, (z - 1) ^ U.card
          * (Sgsum (fun n => κ n * chiZero (∏ p ∈ U, p) n) z P y / (y : ℂ)) := by
    intro y
    rw [sum_mul_left_expand hc κ z P y, Finset.sum_div]
    exact Finset.sum_congr rfl fun U _ ↦ by ring
  simp only [hrw]
  have : Tendsto (fun y : ℕ => ∑ U ∈ (bigPrimes P c).powerset, (z - 1) ^ U.card
      * (Sgsum (fun n => κ n * chiZero (∏ p ∈ U, p) n) z P y / (y : ℂ))) atTop
      (𝓝 (∑ U ∈ (bigPrimes P c).powerset, (0 : ℂ))) := by
    refine tendsto_finsetSum _ fun U hU ↦ ?_
    have hprod : 0 < ∏ p ∈ U, p := by
      refine Finset.prod_pos fun p hp ↦ ?_
      have hpU : p ∈ bigPrimes P c := (Finset.mem_powerset.1 hU) hp
      exact (Nat.prime_of_mem_primeFactors (Finset.mem_filter.1 hpU).1).pos
    have := charSum_tendsto_zero (h.mul_chiZero hprod) hz hz1 P
    simpa using this.const_mul ((z - 1) ^ U.card)
  simpa using this

/-! ### Step 3: a unit residue class mod `Q'` -/

/-- **Orthogonality indicator.**  For `b` coprime to `Q'`, the indicator of the residue class
`b` mod `Q'` is the character average `(φ Q')⁻¹ ∑_χ χ(b⁻¹) χ(m)`. -/
lemma indicator_eq_char_avg {Q' : ℕ} (hQ' : 0 < Q') {b : ℕ} (hb : Nat.Coprime b Q') (m : ℕ) :
    (if m % Q' = b % Q' then (1 : ℂ) else 0)
      = ((Nat.totient Q' : ℂ))⁻¹ * ∑ χ : DirichletCharacter ℂ Q',
          χ ((b : ZMod Q')⁻¹) * χ ((m : ZMod Q')) := by
  classical
  have : NeZero Q' := ⟨hQ'.ne'⟩
  have hu : IsUnit (b : ZMod Q') := (ZMod.isUnit_iff_coprime b Q').2 hb
  rw [DirichletCharacter.sum_char_inv_mul_char_eq ℂ hu ((m : ZMod Q'))]
  have hφ : (Nat.totient Q' : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.2 hQ').ne'
  have hiff : ((b : ZMod Q') = (m : ZMod Q')) ↔ (m % Q' = b % Q') := by
    rw [ZMod.natCast_eq_natCast_iff']
    exact eq_comm
  by_cases h : m % Q' = b % Q'
  · rw [if_pos h, if_pos (hiff.2 h), inv_mul_cancel₀ hφ]
  · rw [if_neg h, if_neg (fun hc => h (hiff.1 hc)), mul_zero]

/-- **The unit-class sum.**  For `b` coprime to `Q'` and any `c ≠ 0`, the count-weighted sum
of `z^{ω_{>P}(c·m)}` over `m ≡ b (mod Q')` is `o(y)`. -/
theorem coprimeClass_tendsto_zero {Q' : ℕ} (hQ' : 0 < Q') {b : ℕ} (hb : Nat.Coprime b Q')
    {z : ℂ} (hz : ‖z‖ = 1) (hz1 : z ≠ 1) (P : ℕ) {c : ℕ} (hc : c ≠ 0) :
    Tendsto (fun y : ℕ =>
        (∑ m ∈ (Ioc 0 y).filter (fun m => m % Q' = b % Q'), hfun z P (c * m)) / (y : ℂ))
      atTop (𝓝 0) := by
  classical
  have : NeZero Q' := ⟨hQ'.ne'⟩
  have hrw : ∀ y : ℕ,
      (∑ m ∈ (Ioc 0 y).filter (fun m => m % Q' = b % Q'), hfun z P (c * m)) / (y : ℂ)
      = ((Nat.totient Q' : ℂ))⁻¹ * ∑ χ : DirichletCharacter ℂ Q',
          χ ((b : ZMod Q')⁻¹)
            * ((∑ m ∈ Ioc 0 y, (fun n : ℕ => χ ((n : ZMod Q'))) m * hfun z P (c * m))
                / (y : ℂ)) := by
    intro y
    rw [Finset.sum_filter]
    have : ∀ m ∈ Ioc 0 y, (if m % Q' = b % Q' then hfun z P (c * m) else 0)
        = ((Nat.totient Q' : ℂ))⁻¹ * ∑ χ : DirichletCharacter ℂ Q',
            χ ((b : ZMod Q')⁻¹) * (χ ((m : ZMod Q')) * hfun z P (c * m)) := by
      intro m _
      have h1 : (if m % Q' = b % Q' then hfun z P (c * m) else 0)
          = (if m % Q' = b % Q' then (1:ℂ) else 0) * hfun z P (c * m) := by
        by_cases h : m % Q' = b % Q' <;> simp [h]
      rw [h1, indicator_eq_char_avg hQ' hb m, mul_assoc, Finset.sum_mul]
      refine congrArg _ (Finset.sum_congr rfl fun χ _ ↦ ?_)
      ring
    rw [Finset.sum_congr rfl this, ← Finset.mul_sum, Finset.sum_comm, mul_div_assoc,
      Finset.sum_div]
    refine congrArg _ (Finset.sum_congr rfl fun χ _ ↦ ?_)
    rw [← Finset.mul_sum, mul_div_assoc]
  simp only [hrw]
  have hlim : Tendsto (fun y : ℕ => ∑ χ : DirichletCharacter ℂ Q',
      χ ((b : ZMod Q')⁻¹)
        * ((∑ m ∈ Ioc 0 y, (fun n : ℕ => χ ((n : ZMod Q'))) m * hfun z P (c * m))
            / (y : ℂ))) atTop (𝓝 (∑ _χ : DirichletCharacter ℂ Q', (0 : ℂ))) := by
    refine tendsto_finsetSum _ fun χ _ ↦ ?_
    have := innerTwist_tendsto_zero (isCharLike_dirichlet hQ' χ) hz hz1 P hc
    simpa using this.const_mul (χ ((b : ZMod Q')⁻¹))
  simpa using hlim.const_mul ((Nat.totient Q' : ℂ))⁻¹


/-! ### Step 4: a general residue class reindexes to a unit class -/

section Reindex

variable {Q : ℕ}

/-- **The reindexing.**  With `e = gcd(a,Q)`, `Q' = Q/e`, `b = a/e`, the map `m ↦ m/e` is a
bijection from `{m ≤ N : m ≡ a [Q]}` onto `{m' ≤ N/e : m' ≡ b [Q']}`, and `gcd(b,Q') = 1`.
This is the step that removes any need for induction on `Q`. -/
theorem classSum_reindex (hQ : 0 < Q) {a : ℕ} (ha : a < Q) (F : ℕ → ℂ) (N : ℕ) :
    ∑ m ∈ (Ioc 0 N).filter (fun m => m % Q = a), F m
      = ∑ m' ∈ (Ioc 0 (N / Nat.gcd a Q)).filter
            (fun m' => m' % (Q / Nat.gcd a Q) = (a / Nat.gcd a Q) % (Q / Nat.gcd a Q)),
          F (Nat.gcd a Q * m') := by
  classical
  set e : ℕ := Nat.gcd a Q with he
  have he0 : 0 < e := Nat.gcd_pos_of_pos_right a hQ
  have heQ : e ∣ Q := Nat.gcd_dvd_right a Q
  have hea : e ∣ a := Nat.gcd_dvd_left a Q
  set Q' : ℕ := Q / e with hQ'def
  set b : ℕ := a / e with hbdef
  have hQfac : Q = e * Q' := (Nat.mul_div_cancel' heQ).symm
  have hafac : a = e * b := (Nat.mul_div_cancel' hea).symm
  have hQ'0 : 0 < Q' := Nat.div_pos (Nat.le_of_dvd hQ heQ) he0
  have hbQ' : b < Q' := by
    have : e * b < e * Q' := by rw [← hafac, ← hQfac]; exact ha
    exact lt_of_mul_lt_mul_left this (Nat.zero_le e)
  have hbmod : b % Q' = b := Nat.mod_eq_of_lt hbQ'
  -- divisibility of members of the class
  have hdvd : ∀ m : ℕ, m % Q = a → e ∣ m := by
    intro m hm
    have := Nat.div_add_mod m Q
    rw [hm] at this
    exact this ▸ Dvd.dvd.add (Dvd.dvd.mul_right heQ _) hea
  have hmodkey : ∀ m₁ : ℕ, (e * m₁) % Q = e * (m₁ % Q') := by
    intro m₁; rw [hQfac, Nat.mul_mod_mul_left]
  refine Finset.sum_nbij' (fun m => m / e) (fun m' => e * m') ?_ ?_ ?_ ?_ ?_
  · intro m hm
    obtain ⟨hm1, hm2⟩ := Finset.mem_filter.1 hm
    obtain ⟨hm0, hmN⟩ := Finset.mem_Ioc.1 hm1
    have hed : e ∣ m := hdvd m hm2
    refine Finset.mem_filter.2 ⟨Finset.mem_Ioc.2 ⟨?_, Nat.div_le_div_right hmN⟩, ?_⟩
    · exact Nat.div_pos (Nat.le_of_dvd hm0 hed) he0
    · rw [hbmod]
      obtain ⟨m₁, rfl⟩ := hed
      rw [Nat.mul_div_cancel_left _ he0]
      have := hmodkey m₁
      rw [hm2, hafac] at this
      exact (Nat.eq_of_mul_eq_mul_left he0 this).symm
  · intro m' hm'
    obtain ⟨hm1, hm2⟩ := Finset.mem_filter.1 hm'
    obtain ⟨hm0, hmN⟩ := Finset.mem_Ioc.1 hm1
    rw [hbmod] at hm2
    refine Finset.mem_filter.2 ⟨Finset.mem_Ioc.2 ⟨Nat.mul_pos he0 hm0, ?_⟩, ?_⟩
    · rw [mul_comm]
      exact (Nat.le_div_iff_mul_le he0).1 hmN
    · rw [hmodkey m', hm2, ← hafac]
  · intro m hm
    exact Nat.mul_div_cancel' (hdvd m (Finset.mem_filter.1 hm).2)
  · intro m' _
    exact Nat.mul_div_cancel_left _ he0
  · intro m hm
    rw [Nat.mul_div_cancel' (hdvd m (Finset.mem_filter.1 hm).2)]

/-- `gcd(a/e, Q/e) = 1` where `e = gcd(a,Q)`. -/
lemma coprime_div_gcd (hQ : 0 < Q) (a : ℕ) :
    Nat.Coprime (a / Nat.gcd a Q) (Q / Nat.gcd a Q) :=
  Nat.coprime_div_gcd_div_gcd (Nat.gcd_pos_of_pos_right a hQ)

end Reindex


/-! ### Step 5: a general residue class is `o(N)` -/

theorem classSum_tendsto_zero {Q : ℕ} (hQ : 0 < Q) {a : ℕ} (ha : a < Q) {z : ℂ}
    (hz : ‖z‖ = 1) (hz1 : z ≠ 1) (P : ℕ) :
    Tendsto (fun N : ℕ =>
        (∑ m ∈ (Ioc 0 N).filter (fun m => m % Q = a), hfun z P m) / (N : ℂ)) atTop (𝓝 0) := by
  classical
  set e : ℕ := Nat.gcd a Q with he
  have he0 : 0 < e := Nat.gcd_pos_of_pos_right a hQ
  set Q' : ℕ := Q / e with hQ'def
  set b : ℕ := a / e with hbdef
  have hQ'0 : 0 < Q' := Nat.div_pos (Nat.le_of_dvd hQ (Nat.gcd_dvd_right a Q)) he0
  have hb : Nat.Coprime b Q' := Nat.coprime_div_gcd_div_gcd he0
  set num : ℕ → ℂ := fun y =>
    ∑ m' ∈ (Ioc 0 y).filter (fun m' => m' % Q' = b % Q'), hfun z P (e * m') with hnum
  have hG : Tendsto (fun y : ℕ => num y / (y : ℂ)) atTop (𝓝 0) :=
    coprimeClass_tendsto_zero hQ'0 hb hz hz1 P he0.ne'
  have hdivTop : Tendsto (fun N : ℕ => N / e) atTop atTop :=
    tendsto_atTop_atTop.2 fun c => ⟨c * e, fun n hn => (Nat.le_div_iff_mul_le he0).2 hn⟩
  have hcomp : Tendsto (fun N : ℕ => ‖num (N / e) / ((N / e : ℕ) : ℂ)‖) atTop (𝓝 0) := by
    have := (hG.comp hdivTop)
    simpa using this.norm
  refine squeeze_zero_norm (fun N => ?_) hcomp
  have heq : ∑ m ∈ (Ioc 0 N).filter (fun m => m % Q = a), hfun z P m = num (N / e) :=
    classSum_reindex hQ ha (hfun z P) N
  rw [heq]
  rcases Nat.eq_zero_or_pos (N / e) with hy | hy
  · have : num (N / e) = 0 := by rw [hnum, hy]; simp
    simp [this]
  · have hyN : (N / e) ≤ N := Nat.div_le_self _ _
    have hN0 : 0 < N := lt_of_lt_of_le hy hyN
    rw [norm_div, norm_div, Complex.norm_natCast, Complex.norm_natCast]
    refine div_le_div_of_nonneg_left (norm_nonneg _) (by exact_mod_cast hy) ?_
    exact_mod_cast hyN

/-! ### Step 6: the headline -/

/-- The additive twist is constant on residue classes mod `Q`. -/
lemma exp_twist_of_mod {Q : ℕ} (hQ : 0 < Q) (j : ℤ) {m a : ℕ} (hm : m % Q = a) :
    Complex.exp (2 * Real.pi * Complex.I * j * m / Q)
      = Complex.exp (2 * Real.pi * Complex.I * j * a / Q) := by
  obtain ⟨k, hk⟩ : ∃ k : ℕ, m = Q * k + a :=
    ⟨m / Q, by rw [← hm]; exact (Nat.div_add_mod m Q).symm⟩
  subst hk
  have hQ0 : (Q : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hQ.ne'
  have hsplit : 2 * (Real.pi : ℂ) * Complex.I * j * ((Q * k + a : ℕ) : ℂ) / Q
      = ((j * k : ℤ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)
        + 2 * (Real.pi : ℂ) * Complex.I * j * (a : ℂ) / Q := by
    push_cast
    field_simp
  rw [hsplit, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, one_mul]

theorem twisted_tendsto_zero {Q : ℕ} (hQ : 0 < Q) (j : ℤ) {z : ℂ} (hz : ‖z‖ = 1) (hz1 : z ≠ 1)
    (P : ℕ) :
    Tendsto (fun N : ℕ =>
        (∑ m ∈ Ioc 0 N, Complex.exp (2 * Real.pi * Complex.I * j * m / Q) * hfun z P m) / (N : ℂ))
      atTop (𝓝 0) := by
  classical
  have hmaps : ∀ N : ℕ, ∀ m ∈ Ioc 0 N, m % Q ∈ range Q := fun _ m _ ↦
    mem_range.2 (Nat.mod_lt _ hQ)
  have hrw : ∀ N : ℕ,
      (∑ m ∈ Ioc 0 N, Complex.exp (2 * Real.pi * Complex.I * j * m / Q) * hfun z P m) / (N : ℂ)
      = ∑ a ∈ range Q, Complex.exp (2 * Real.pi * Complex.I * j * a / Q)
          * ((∑ m ∈ (Ioc 0 N).filter (fun m => m % Q = a), hfun z P m) / (N : ℂ)) := by
    intro N
    rw [← Finset.sum_fiberwise_of_maps_to (hmaps N)
      (fun m => Complex.exp (2 * Real.pi * Complex.I * j * m / Q) * hfun z P m),
      Finset.sum_div]
    refine Finset.sum_congr rfl fun a _ ↦ ?_
    have hcls : ∀ m ∈ (Ioc 0 N).filter (fun m => m % Q = a),
        Complex.exp (2 * Real.pi * Complex.I * j * m / Q) * hfun z P m
          = Complex.exp (2 * Real.pi * Complex.I * j * a / Q) * hfun z P m := fun m hm => by
      rw [exp_twist_of_mod hQ j (Finset.mem_filter.1 hm).2]
    rw [Finset.sum_congr rfl hcls, ← Finset.mul_sum]
    exact mul_div_assoc _ _ _
  simp only [hrw]
  have hlim : Tendsto (fun N : ℕ => ∑ a ∈ range Q,
      Complex.exp (2 * Real.pi * Complex.I * j * a / Q)
        * ((∑ m ∈ (Ioc 0 N).filter (fun m => m % Q = a), hfun z P m) / (N : ℂ)))
      atTop (𝓝 (∑ _a ∈ range Q, (0 : ℂ))) := by
    refine tendsto_finsetSum _ fun a ha ↦ ?_
    have := classSum_tendsto_zero hQ (mem_range.1 ha) (z := z) hz hz1 P
    simpa using this.const_mul (Complex.exp (2 * Real.pi * Complex.I * j * a / Q))
  simpa using hlim


end NormalNumbers.DelangeSlot
