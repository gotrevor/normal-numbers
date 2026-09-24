import NormalNumbers.DelangeSlotPrincipal

/-!
# Rung 2, layer 4: the master dichotomy

Both halves of rung 2 are now proved:

* `Sgsum_tendsto_zero_of_psi_littleO` (+ `psiChar_littleO`, `psiAP_tendsto`) handles any
  `κ` whose sum over a period vanishes;
* `sigmaMeang_chiZero_tendsto_zero` handles the principal character.

This file merges them into **one** statement, `charSum_tendsto_zero`, covering every completely
multiplicative periodic `κ` supported on the units.  The dichotomy is elementary orthogonality:
if `κ b ≠ 1` for some unit `b`, then multiplying the period sum by `κ b` permutes the summands,
so the period sum is `0`; otherwise `κ` *is* `chiZero M` on the nose.

This is what makes the additive twist reachable without ever constructing the `m = s·t`
(`Q`-primary × `Q`-coprime) factorisation: every function that arises when the additive
character is unfolded — a Dirichlet character times principal characters mod various primes —
is again a completely multiplicative periodic function supported on units, i.e. an instance of
`charSum_tendsto_zero`.
-/

open Finset ArithmeticFunction Filter Topology

namespace NormalNumbers.DelangeSlot

/-- A completely multiplicative `M`-periodic function supported on the units mod `M`,
of modulus one there: exactly a Dirichlet character mod `M` viewed on `ℕ`. -/
structure IsCharLike (M : ℕ) (κ : ℕ → ℂ) : Prop where
  pos : 0 < M
  mul : ∀ a b : ℕ, κ (a * b) = κ a * κ b
  per : ∀ a b : ℕ, a % M = b % M → κ a = κ b
  zero : ∀ n : ℕ, ¬ Nat.Coprime n M → κ n = 0
  norm_le : ∀ n : ℕ, ‖κ n‖ ≤ 1

/-- **Orthogonality.**  If `κ` is not identically `1` on the units, its sum over a period
vanishes. -/
theorem IsCharLike.sum_eq_zero {M : ℕ} {κ : ℕ → ℂ} (h : IsCharLike M κ)
    {b : ℕ} (hb : Nat.Coprime b M) (hb1 : κ b ≠ 1) :
    ∑ a ∈ range M, κ a = 0 := by
  classical
  have hM : NeZero M := ⟨h.pos.ne'⟩
  have hbu : IsUnit (b : ZMod M) := (ZMod.isUnit_iff_coprime b M).2 hb
  obtain ⟨u, hu⟩ := hbu
  set key : ℕ → ℕ := fun a => (b * a) % M with hkey
  set inv : ℕ → ℕ := fun a => (((u⁻¹ : (ZMod M)ˣ) : ZMod M) * (a : ZMod M)).val with hinv
  have hcast : ∀ a : ℕ, ((key a : ℕ) : ZMod M) = (b : ZMod M) * (a : ZMod M) := by
    intro a; simp [hkey, ZMod.natCast_mod]
  have hcastinv : ∀ a : ℕ, ((inv a : ℕ) : ZMod M)
      = ((u⁻¹ : (ZMod M)ˣ) : ZMod M) * (a : ZMod M) := by
    intro a; simp [hinv, ZMod.natCast_val, ZMod.cast_id]
  have hkey_mem : ∀ a ∈ range M, key a ∈ range M := fun a _ ↦
    mem_range.2 (Nat.mod_lt _ h.pos)
  have hinv_mem : ∀ a ∈ range M, inv a ∈ range M := fun a _ ↦
    mem_range.2 (ZMod.val_lt _)
  have hleft : ∀ a ∈ range M, inv (key a) = a := by
    intro a ha
    have ha' : a < M := mem_range.1 ha
    have : ((inv (key a) : ℕ) : ZMod M) = (a : ZMod M) := by
      rw [hcastinv, hcast, ← hu, ← mul_assoc, ← Units.val_mul, inv_mul_cancel,
        Units.val_one, one_mul]
    have h2 := congrArg ZMod.val this
    rwa [ZMod.val_natCast_of_lt (mem_range.1 (hinv_mem _ (hkey_mem a ha))),
      ZMod.val_natCast_of_lt ha'] at h2
  have hright : ∀ a ∈ range M, key (inv a) = a := by
    intro a ha
    have ha' : a < M := mem_range.1 ha
    have : ((key (inv a) : ℕ) : ZMod M) = (a : ZMod M) := by
      rw [hcast, hcastinv, ← hu, ← mul_assoc, ← Units.val_mul, mul_inv_cancel,
        Units.val_one, one_mul]
    have h2 := congrArg ZMod.val this
    rwa [ZMod.val_natCast_of_lt (mem_range.1 (hkey_mem _ (hinv_mem a ha))),
      ZMod.val_natCast_of_lt ha'] at h2
  have hswap : ∑ a ∈ range M, κ a = ∑ a ∈ range M, κ (key a) :=
    (Finset.sum_nbij' key inv hkey_mem hinv_mem hleft hright (fun _ _ ↦ rfl)).symm
  have hmulsum : ∑ a ∈ range M, κ (key a) = κ b * ∑ a ∈ range M, κ a := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ ↦ ?_
    rw [← h.mul]
    exact h.per (key a) (b * a) (by simp [hkey, Nat.mod_mod])
  have hS : ∑ a ∈ range M, κ a = κ b * ∑ a ∈ range M, κ a := hswap.trans hmulsum
  have hfac : (1 - κ b) * ∑ a ∈ range M, κ a = 0 := by
    rw [sub_mul, one_mul, ← hS, sub_self]
  rcases mul_eq_zero.1 hfac with h' | h'
  · exact absurd (sub_eq_zero.1 h').symm hb1
  · exact h'

/-- **The master statement.**  For any character-like `κ` and any unimodular `z ≠ 1`, the mean
of `κ · z^{ω_{>P}}` tends to `0`. -/
theorem charSum_tendsto_zero {M : ℕ} {κ : ℕ → ℂ} (h : IsCharLike M κ) {z : ℂ}
    (hz : ‖z‖ = 1) (hz1 : z ≠ 1) (P : ℕ) :
    Tendsto (fun N : ℕ => Sgsum κ z P N / (N : ℂ)) atTop (𝓝 0) := by
  by_cases hprin : ∀ b : ℕ, Nat.Coprime b M → κ b = 1
  · -- `κ` is literally `chiZero M`
    have hκ : κ = chiZero M := by
      funext n
      by_cases hc : Nat.Coprime n M
      · rw [hprin n hc, chiZero, if_pos hc]
      · rw [h.zero n hc, chiZero, if_neg hc]
    have := sigmaMeang_chiZero_tendsto_zero hz hz1 P (Q := M) h.pos.ne'
    simpa [hκ, sigmaMeang] using this
  · push_neg at hprin
    obtain ⟨b, hb, hb1⟩ := hprin
    exact Sgsum_tendsto_zero_of_psi_littleO h.mul h.norm_le hz
      (psiChar_littleO h.pos κ h.per h.zero (h.sum_eq_zero hb hb1))


/-! ### Character-like closure properties -/

lemma isCharLike_chiZero {d : ℕ} (hd : 0 < d) : IsCharLike d (chiZero d) where
  pos := hd
  mul := chiZero_mul d
  per := by
    intro a b hab
    have : Nat.gcd a d = Nat.gcd b d := by
      rw [Nat.gcd_comm a d, Nat.gcd_comm b d, Nat.gcd_rec d a, Nat.gcd_rec d b, hab]
    simp only [chiZero, Nat.Coprime, this]
  zero := fun n hn => by simp [chiZero, hn]
  norm_le := norm_chiZero_le d

lemma IsCharLike.mul_chiZero {M : ℕ} {κ : ℕ → ℂ} (h : IsCharLike M κ) {d : ℕ} (hd : 0 < d) :
    IsCharLike (M * d) (fun n => κ n * chiZero d n) where
  pos := Nat.mul_pos h.pos hd
  mul := by
    intro a b
    rw [h.mul, chiZero_mul]; ring
  per := by
    intro a b hab
    have hM : a % M = b % M := by
      have h1 : a % (M * d) % M = a % M := Nat.mod_mod_of_dvd a ⟨d, rfl⟩
      have h2 : b % (M * d) % M = b % M := Nat.mod_mod_of_dvd b ⟨d, rfl⟩
      rw [← h1, ← h2, hab]
    have hd' : a % d = b % d := by
      have h1 : a % (M * d) % d = a % d := Nat.mod_mod_of_dvd a ⟨M, mul_comm M d⟩
      have h2 : b % (M * d) % d = b % d := Nat.mod_mod_of_dvd b ⟨M, mul_comm M d⟩
      rw [← h1, ← h2, hab]
    rw [h.per a b hM, (isCharLike_chiZero hd).per a b hd']
  zero := by
    intro n hn
    by_cases h1 : Nat.Coprime n M
    · have h2 : ¬ Nat.Coprime n d := fun h2 => hn (Nat.Coprime.mul_right h1 h2)
      rw [(isCharLike_chiZero hd).zero n h2, mul_zero]
    · rw [h.zero n h1, zero_mul]
  norm_le := by
    intro n
    rw [norm_mul]
    exact mul_le_one₀ (h.norm_le n) (norm_nonneg _) (norm_chiZero_le d n)

/-! ### Unfolding `z^{ω_{>P}(c·m)}` into principal characters

The identity that removes the need for a `Q`-primary / `Q`-coprime factorisation of `m`:
whether a prime `p` divides `m` is itself the principal character mod `p`. -/

/-- For a prime `p`, `chiZero p m` is the indicator of `p ∤ m`. -/
lemma chiZero_prime_eq {p : ℕ} (hp : p.Prime) (m : ℕ) :
    chiZero p m = if p ∣ m then 0 else 1 := by
  have key : Nat.Coprime m p ↔ ¬ p ∣ m := by
    rw [Nat.coprime_comm]; exact hp.coprime_iff_not_dvd
  rw [chiZero]
  by_cases h : p ∣ m
  · rw [if_neg (fun hc => (key.1 hc) h), if_pos h]
  · rw [if_pos (key.2 h), if_neg h]

/-- The large prime factors of `c`. -/
noncomputable def bigPrimes (P c : ℕ) : Finset ℕ := c.primeFactors.filter (fun p => P < p)

/-- `ω_{>P}(c·m) = ω_{>P}(m) + #{p ∈ bigPrimes P c : p ∤ m}`. -/
lemma omegaLarge_mul_left {c m : ℕ} (hc : c ≠ 0) (hm : m ≠ 0) (P : ℕ) :
    omegaLarge P (c * m)
      = omegaLarge P m + ((bigPrimes P c).filter (fun p => ¬ p ∣ m)).card := by
  classical
  set A : Finset ℕ := c.primeFactors.filter (fun p => P < p) with hA
  set B : Finset ℕ := m.primeFactors.filter (fun p => P < p) with hB
  have hAB : A \ B = (bigPrimes P c).filter (fun p => ¬ p ∣ m) := by
    ext q
    simp only [hA, hB, bigPrimes, Finset.mem_sdiff, Finset.mem_filter, Nat.mem_primeFactors]
    constructor
    · rintro ⟨⟨hq, hP⟩, hnot⟩
      exact ⟨⟨hq, hP⟩, fun hdvd => hnot ⟨⟨hq.1, hdvd, hm⟩, hP⟩⟩
    · rintro ⟨⟨hq, hP⟩, hnd⟩
      exact ⟨⟨hq, hP⟩, fun hh => hnd hh.1.2.1⟩
  have hpf : (c * m).primeFactors = c.primeFactors ∪ m.primeFactors := Nat.primeFactors_mul hc hm
  rw [omegaLarge, omegaLarge, hpf, Finset.filter_union, ← hA, ← hB, Finset.union_comm,
    ← Finset.union_sdiff_self_eq_union, Finset.card_union_of_disjoint Finset.disjoint_sdiff, hAB]


lemma prod_chiZero {U : Finset ℕ} (m : ℕ) :
    ∏ p ∈ U, chiZero p m = chiZero (∏ p ∈ U, p) m := by
  classical
  by_cases hall : ∀ p ∈ U, Nat.Coprime m p
  · have : Nat.Coprime m (∏ p ∈ U, p) := Nat.Coprime.prod_right hall
    rw [chiZero, if_pos this]
    exact Finset.prod_eq_one fun p hp => by rw [chiZero, if_pos (hall p hp)]
  · push_neg at hall
    obtain ⟨p, hpU, hp⟩ := hall
    have h0 : chiZero p m = 0 := by rw [chiZero, if_neg hp]
    have hnc : ¬ Nat.Coprime m (∏ q ∈ U, q) := by
      intro hc
      exact hp (Nat.Coprime.coprime_dvd_right (Finset.dvd_prod_of_mem _ hpU) hc)
    rw [chiZero, if_neg hnc, Finset.prod_eq_zero hpU h0]

/-- **The unfolding identity.**  `z^{ω_{>P}(c·m)}` as a finite combination of
`χ₀^{(d)}(m) · z^{ω_{>P}(m)}` over squarefree `d ∣ c` built from the primes of `c` above `P`. -/
theorem hfun_mul_left_expand {c : ℕ} (hc : c ≠ 0) (z : ℂ) (P m : ℕ) (hm : m ≠ 0) :
    hfun z P (c * m)
      = ∑ U ∈ (bigPrimes P c).powerset, (z - 1) ^ U.card * (chiZero (∏ p ∈ U, p) m
          * hfun z P m) := by
  classical
  set S : Finset ℕ := bigPrimes P c with hS
  have hprime : ∀ p ∈ S, p.Prime := by
    intro p hp
    exact Nat.prime_of_mem_primeFactors (Finset.mem_filter.1 hp).1
  -- the product form
  have hfac : ∀ p ∈ S, (z - 1) * chiZero p m + (1 : ℂ) = if p ∣ m then 1 else z := by
    intro p hp
    rw [chiZero_prime_eq (hprime p hp)]
    by_cases h : p ∣ m <;> simp [h]
  have hprod : ∏ p ∈ S, ((z - 1) * chiZero p m + (1 : ℂ))
      = z ^ (S.filter (fun p => ¬ p ∣ m)).card := by
    rw [Finset.prod_congr rfl hfac, Finset.prod_ite]
    simp
  have hpow : hfun z P (c * m) = hfun z P m * z ^ (S.filter (fun p => ¬ p ∣ m)).card := by
    rw [hfun, hfun, omegaLarge_mul_left hc hm P, pow_add, hS]
  -- expand the product over subsets
  have hexp : ∏ p ∈ S, ((z - 1) * chiZero p m + (1:ℂ))
      = ∑ U ∈ S.powerset, ∏ p ∈ U, ((z - 1) * chiZero p m) := by
    rw [Finset.prod_add (fun p => (z - 1) * chiZero p m) (fun _ : ℕ => (1:ℂ)) S]
    refine Finset.sum_congr rfl fun U hU ↦ ?_
    rw [Finset.prod_const_one, mul_one]
  rw [hpow, ← hprod, hexp, Finset.mul_sum]
  refine Finset.sum_congr rfl fun U hU ↦ ?_
  rw [Finset.prod_mul_distrib, Finset.prod_const, prod_chiZero]
  ring

/-- **The expansion of a twisted-by-`c` character sum.** -/
theorem sum_mul_left_expand {c : ℕ} (hc : c ≠ 0) (κ : ℕ → ℂ) (z : ℂ) (P y : ℕ) :
    ∑ m ∈ Ioc 0 y, κ m * hfun z P (c * m)
      = ∑ U ∈ (bigPrimes P c).powerset, (z - 1) ^ U.card
          * Sgsum (fun n => κ n * chiZero (∏ p ∈ U, p) n) z P y := by
  classical
  have hterm : ∀ m ∈ Ioc 0 y, κ m * hfun z P (c * m)
      = ∑ U ∈ (bigPrimes P c).powerset,
          (z - 1) ^ U.card * (κ m * chiZero (∏ p ∈ U, p) m * hfun z P m) := by
    intro m hm
    have hm0 : m ≠ 0 := (mem_Ioc.1 hm).1.ne'
    rw [hfun_mul_left_expand hc z P m hm0, Finset.mul_sum]
    exact Finset.sum_congr rfl fun U _ ↦ by ring
  rw [Finset.sum_congr rfl hterm, Finset.sum_comm]
  refine Finset.sum_congr rfl fun U _ ↦ ?_
  rw [Sgsum, Finset.mul_sum]
  exact Finset.sum_congr rfl fun m _ ↦ by rw [gfun]

end NormalNumbers.DelangeSlot
