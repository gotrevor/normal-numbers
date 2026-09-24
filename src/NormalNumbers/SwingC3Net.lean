/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.SwingC3Lambert

/-!
# Nets on the circle: a perturbed grid meets every long enough arc

Leaf A of `SwingC3Rotation.lean` (`exists_rotationCover`) needs exactly this geometric fact.
The CRT steering of `SwingC3Split.exists_crt_pattern` produces rotation constants of the shape

`θ_k = C + k·b^{−ℓ'} + ρ_k`,  `0 ≤ ρ_k ≤ ε`,

— an exact grid of spacing `b^{−ℓ'}`, perturbed by the *uncontrolled* contribution of the window
slots beyond `ℓ'`.  `exists_perturbed_grid_mem_Ico` says such a family still meets every arc of
length `> b^{−ℓ'} + ε`, so it is a net, and that is all the covering argument needs.  This is
precisely why the route asks for a **net** and not for the exact grid that `LargeTailLaw`
demanded: the perturbation `ρ` is what killed the exact-grid version.
-/

open Finset

namespace NormalNumbers

/-- **An exact grid meets every arc longer than its spacing.**  The `m` points
`fract (c + k/m)`, `k < m`, form a coset of the `1/m`-grid on the circle, so any arc
`[α, α+len) ⊆ [0,1)` with `len > 1/m` contains one of them. -/
theorem exists_grid_mem_Ico {m : ℕ} (hm : 0 < m) (c α len : ℝ) (hα : 0 ≤ α)
    (hlen : 1 / (m : ℝ) < len) (hαlen : α + len ≤ 1) :
    ∃ k, k < m ∧ Int.fract (c + (k : ℝ) / m) ∈ Set.Ico α (α + len) := by
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  set s : ℝ := Int.fract (α - c) with hsdef
  have hs0 : 0 ≤ s := Int.fract_nonneg _
  have hs1 : s < 1 := Int.fract_lt_one _
  set k0 : ℤ := ⌈s * (m : ℝ)⌉ with hk0def
  have hlo : s * (m : ℝ) ≤ (k0 : ℝ) := Int.le_ceil _
  have hhi : (k0 : ℝ) < s * (m : ℝ) + 1 := Int.ceil_lt_add_one _
  have hk0nn : (0 : ℤ) ≤ k0 := Int.ceil_nonneg (by positivity)
  have hk0le : k0 ≤ (m : ℤ) := by
    rw [hk0def, Int.ceil_le]
    push_cast
    nlinarith
  set j : ℕ := k0.toNat with hjdef
  have hjcast : ((j : ℤ) : ℝ) = (k0 : ℝ) := by
    rw [hjdef, Int.toNat_of_nonneg hk0nn]
  have hjR : (j : ℝ) = (k0 : ℝ) := by exact_mod_cast hjcast
  have hjle : j ≤ m := by
    have : (k0 : ℤ) ≤ (m : ℤ) := hk0le
    omega
  set δ : ℝ := (j : ℝ) / m - s with hδdef
  have hδ0 : 0 ≤ δ := by
    rw [hδdef, sub_nonneg, le_div_iff₀ hmR, hjR]
    linarith
  have hδhi : δ < 1 / (m : ℝ) := by
    rw [hδdef, sub_lt_iff_lt_add, div_lt_iff₀ hmR, hjR]
    have : (1 : ℝ) / (m : ℝ) * (m : ℝ) = 1 := by field_simp
    nlinarith
  -- the grid point at index `j` lands at `α + δ`
  have hfr : Int.fract (c + (j : ℝ) / m) = α + δ := by
    have hrw : c + (j : ℝ) / m = (α + δ) - ((⌊α - c⌋ : ℤ) : ℝ) := by
      rw [hδdef, hsdef, Int.fract]
      ring
    rw [hrw, Int.fract_sub_intCast, Int.fract_eq_self]
    constructor
    · linarith
    · linarith
  have hmem : (α + δ) ∈ Set.Ico α (α + len) := ⟨by linarith, by linarith⟩
  rcases lt_or_eq_of_le hjle with hjlt | hjeq
  · exact ⟨j, hjlt, by rw [hfr]; exact hmem⟩
  · refine ⟨0, hm, ?_⟩
    have hone : (j : ℝ) / m = 1 := by rw [hjeq]; field_simp
    have : c + ((0 : ℕ) : ℝ) / m = (c + (j : ℝ) / m) - ((1 : ℤ) : ℝ) := by
      rw [hone]; push_cast; ring
    rw [this, Int.fract_sub_intCast, hfr]
    exact hmem

/-- **A perturbed grid is still a net.**  Shifting each grid point forward by at most `ε`
costs exactly `ε` of arc length. -/
theorem exists_perturbed_grid_mem_Ico {m : ℕ} (hm : 0 < m) (c α len ε : ℝ) (ρ : ℕ → ℝ)
    (hρ0 : ∀ k, 0 ≤ ρ k) (hρ : ∀ k, ρ k ≤ ε) (hα : 0 ≤ α)
    (hlen : 1 / (m : ℝ) + ε < len) (hαlen : α + len ≤ 1) :
    ∃ k, k < m ∧ Int.fract (c + (k : ℝ) / m + ρ k) ∈ Set.Ico α (α + len) := by
  have hε : 0 ≤ ε := le_trans (hρ0 0) (hρ 0)
  obtain ⟨k, hk, hmem⟩ :=
    exists_grid_mem_Ico hm c α (len - ε) hα (by linarith) (by linarith)
  refine ⟨k, hk, ?_⟩
  obtain ⟨h1, h2⟩ := hmem
  have hsplit : c + (k : ℝ) / m + ρ k
      = (Int.fract (c + (k : ℝ) / m) + ρ k) + ((⌊c + (k : ℝ) / m⌋ : ℤ) : ℝ) := by
    rw [Int.fract]; ring
  rw [hsplit, Int.fract_add_intCast, Int.fract_eq_self.2]
  · exact ⟨by linarith [hρ0 k], by linarith [hρ k]⟩
  · exact ⟨by linarith [hρ0 k], by linarith [hρ k]⟩

/-! ### The head/remainder split of `tailSmall`

The CRT steering controls `ω_{≤P}(a+j)` only for `j ≤ L`.  The rest of the window contributes
the perturbation `ρ` of `exists_perturbed_grid_mem_Ico`, and it is bounded by
`π(P)·b^{−L}/(b−1)` because `ω_{≤P} ≤ π(P)` pointwise. -/

/-- `π(P)`, the number of primes `≤ P`. -/
def piCount (P : ℕ) : ℕ := ((range (P + 1)).filter Nat.Prime).card

lemma omegaSmall_le_piCount (P m : ℕ) : omegaSmall P m ≤ piCount P := by
  classical
  unfold omegaSmall piCount
  refine Finset.card_le_card fun p hp => ?_
  simp only [Finset.mem_filter, Nat.mem_primeFactors, mem_range] at hp ⊢
  exact ⟨by omega, hp.1.1⟩

/-- **The window head plus a small remainder.**  `tailSmall P b n` is its first `L` terms plus a
remainder in `[0, π(P)·b^{−L}/(b−1)]`. -/
theorem tailSmall_head_rem {b : ℕ} (hb : 2 ≤ b) (P n L : ℕ) :
    ∃ r : ℝ, tailSmall P b n
        = (∑ i ∈ range L, (omegaSmall P (n + i + 1) : ℝ) / (b : ℝ) ^ (i + 1)) + r
      ∧ 0 ≤ r ∧ r ≤ (piCount P : ℝ) / ((b : ℝ) ^ L * ((b : ℝ) - 1)) := by
  have hbR : (2 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
  have hb0 : (0 : ℝ) < (b : ℝ) := by linarith
  have hb1 : (1 : ℝ) < (b : ℝ) := by linarith
  set f : ℕ → ℝ := fun i => (omegaSmall P (n + i + 1) : ℝ) / (b : ℝ) ^ (i + 1) with hf
  have hsum : Summable f := summable_tailOf hb (omegaSmall_le_omegaR P) n
  have hsplit := hsum.sum_add_tsum_nat_add L
  refine ⟨∑' i : ℕ, f (i + L), ?_, ?_, ?_⟩
  · rw [tailSmall]
    exact hsplit.symm
  · exact tsum_nonneg fun i => by rw [hf]; positivity
  · -- majorise by the geometric series with constant `π(P)`
    set K : ℝ := (piCount P : ℝ) with hK
    have hK0 : 0 ≤ K := by rw [hK]; positivity
    have hmaj : Summable (fun i : ℕ => K / (b : ℝ) ^ (i + L + 1)) := by
      have : Summable (fun i : ℕ => K * ((1 / (b : ℝ)) ^ i * (1 / (b : ℝ)) ^ (L + 1))) :=
        ((summable_geometric_of_lt_one (by positivity)
          (by rw [div_lt_one hb0]; linarith)).mul_right _).mul_left K
      refine this.congr fun i => ?_
      rw [div_pow, div_pow, one_pow, one_pow]
      rw [show i + L + 1 = i + (L + 1) by ring, pow_add]
      field_simp
      ring
    have hle : ∑' i : ℕ, f (i + L) ≤ ∑' i : ℕ, K / (b : ℝ) ^ (i + L + 1) := by
      refine Summable.tsum_le_tsum (fun i => ?_) ((summable_nat_add_iff L).2 hsum) hmaj
      simp only [hf]
      have h1 : (omegaSmall P (n + (i + L) + 1) : ℝ) ≤ K := by
        rw [hK]; exact_mod_cast omegaSmall_le_piCount P _
      have h2 : (0 : ℝ) < (b : ℝ) ^ (i + L + 1) := by positivity
      gcongr
    refine hle.trans (le_of_eq ?_)
    have hgeo : ∑' i : ℕ, ((1 : ℝ) / (b : ℝ)) ^ i = (b : ℝ) / ((b : ℝ) - 1) := by
      rw [tsum_geometric_of_lt_one (by positivity) (by rw [div_lt_one hb0]; linarith)]
      field_simp
    have hrw : ∀ i : ℕ, K / (b : ℝ) ^ (i + L + 1)
        = (K / (b : ℝ) ^ (L + 1)) * ((1 : ℝ) / (b : ℝ)) ^ i := by
      intro i
      rw [div_pow, one_pow, show i + L + 1 = i + (L + 1) by ring, pow_add]
      field_simp
    rw [tsum_congr hrw, tsum_mul_left, hgeo]
    field_simp
    ring

/-! ### CRT steering with a prescribed residue on the small primes

`SwingC3Split.exists_crt_pattern` steers the primes `> L`.  The primes `≤ L` can divide two of
`a+1, …, a+L` and cannot be steered, but they can be PINNED: fixing `a` modulo `R = ∏_{p ≤ L} p`
makes their contribution to each window slot a constant, independent of the steering. -/

/-- `exists_crt_pattern` with an extra congruence `a ≡ a₀ [MOD R]`, `R` coprime to every
steering prime. -/
theorem exists_crt_pattern_mod (L : ℕ) (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    (hSL : ∀ p ∈ S, L < p) (f : ℕ → ℕ) (hf1 : ∀ p ∈ S, 1 ≤ f p) (hfL : ∀ p ∈ S, f p ≤ L)
    (R : ℕ) (hR : 0 < R) (hcop : ∀ p ∈ S, ¬ p ∣ R) (a₀ : ℕ) :
    ∃ a : ℕ, a ≡ a₀ [MOD R] ∧ ∀ p ∈ S, ∀ j, 1 ≤ j → j ≤ L → (p ∣ a + j ↔ j = f p) := by
  classical
  obtain ⟨a₁, ha₁⟩ := exists_crt_pattern L S hS hSL f hf1 hfL
  set D : ℕ := ∏ p ∈ S, p with hD
  have hDR : Nat.Coprime D R := by
    rw [hD]
    refine Nat.Coprime.prod_left fun p hp => ?_
    exact (Nat.Prime.coprime_iff_not_dvd (hS p hp)).2 (hcop p hp)
  obtain ⟨a, haD, haR⟩ := Nat.chineseRemainder hDR a₁ a₀
  refine ⟨a, haR, fun p hp j hj1 hjL => ?_⟩
  have hpD : p ∣ D := Finset.dvd_prod_of_mem _ hp
  have hmod : a ≡ a₁ [MOD p] := Nat.ModEq.of_dvd hpD haD
  have hshift : a + j ≡ a₁ + j [MOD p] := hmod.add_right j
  have : p ∣ a + j ↔ p ∣ a₁ + j := by
    constructor
    · intro hdvd
      exact (Nat.modEq_zero_iff_dvd).1 (hshift.symm.trans ((Nat.modEq_zero_iff_dvd).2 hdvd))
    · intro hdvd
      exact (Nat.modEq_zero_iff_dvd).1 (hshift.trans ((Nat.modEq_zero_iff_dvd).2 hdvd))
  rw [this]
  exact ha₁ p hp j hj1 hjL

/-! ### The steered window count -/

lemma omegaSmall_eq_card_filter {P m : ℕ} (hm : m ≠ 0) :
    omegaSmall P m = ((range (P + 1)).filter (fun p => p.Prime ∧ p ∣ m)).card := by
  classical
  unfold omegaSmall
  congr 1
  ext p
  simp only [Finset.mem_filter, Nat.mem_primeFactors, mem_range]
  constructor
  · rintro ⟨⟨hp, hpm, -⟩, hle⟩; exact ⟨by omega, hp, hpm⟩
  · rintro ⟨hlt, hp, hpm⟩; exact ⟨⟨hp, hpm, hm⟩, by omega⟩

/-- **The steered window count.**  If every prime `≤ L` divides `a` (i.e. `a ≡ 0` modulo the
primorial of `L`) and the primes in `(L, P]` are steered by `f`, then for each window slot
`j ∈ [1, L]` the small-prime count at `a+j` is a constant depending only on `j`, plus the number
of steering primes assigned to slot `j`. -/
theorem omegaSmall_steered {P L a j : ℕ} {f : ℕ → ℕ} (S : Finset ℕ) (hLP : L ≤ P)
    (hSdef : ∀ p, p ∈ S ↔ (L < p ∧ p ≤ P ∧ p.Prime))
    (hRa : ∀ p, p ≤ L → p.Prime → p ∣ a)
    (hsteer : ∀ p ∈ S, ∀ i, 1 ≤ i → i ≤ L → (p ∣ a + i ↔ i = f p))
    (hj1 : 1 ≤ j) (hjL : j ≤ L) :
    omegaSmall P (a + j)
      = ((range (L + 1)).filter (fun p => p.Prime ∧ p ∣ j)).card
        + (S.filter (fun p => f p = j)).card := by
  classical
  have hkey : (range (P + 1)).filter (fun p => p.Prime ∧ p ∣ (a + j))
      = ((range (L + 1)).filter (fun p => p.Prime ∧ p ∣ j)) ∪ (S.filter (fun p => f p = j)) := by
    ext p
    simp only [Finset.mem_union, Finset.mem_filter, mem_range]
    constructor
    · rintro ⟨hpP, hp, hdvd⟩
      rcases le_or_gt p L with hle | hgt
      · exact Or.inl ⟨by omega, hp, (Nat.dvd_add_right (hRa p hle hp)).1 hdvd⟩
      · have hpS : p ∈ S := (hSdef p).2 ⟨hgt, by omega, hp⟩
        exact Or.inr ⟨hpS, ((hsteer p hpS j hj1 hjL).1 hdvd).symm⟩
    · rintro (⟨hpL, hp, hdvd⟩ | ⟨hpS, hfp⟩)
      · exact ⟨by omega, hp, (Nat.dvd_add_right (hRa p (by omega) hp)).2 hdvd⟩
      · obtain ⟨hgt, hleP, hp⟩ := (hSdef p).1 hpS
        exact ⟨by omega, hp, (hsteer p hpS j hj1 hjL).2 hfp.symm⟩
  have hdisj : Disjoint ((range (L + 1)).filter (fun p => p.Prime ∧ p ∣ j))
      (S.filter (fun p => f p = j)) := by
    refine Finset.disjoint_left.2 fun p hp hp' => ?_
    simp only [Finset.mem_filter, mem_range] at hp hp'
    obtain ⟨hgt, -, -⟩ := (hSdef p).1 hp'.1
    omega
  rw [omegaSmall_eq_card_filter (by omega), hkey, Finset.card_union_of_disjoint hdisj]

/-! ### Block assignment: the steering digits

To put `d j` steering primes into window slot `j+1`, split the available primes into blocks of
the prescribed sizes.  The leftover primes go into the dummy slot `L+1`, which lies outside the
controlled window. -/

/-- **Block assignment.**  A finset splits into blocks of prescribed sizes (plus a leftover
block `L+1` and an overflow label `L+2`) as soon as the sizes fit. -/
theorem exists_slot_assignment : ∀ (L : ℕ) (S : Finset ℕ) (d : ℕ → ℕ),
    (∑ i ∈ range L, d i) ≤ S.card →
      ∃ f : ℕ → ℕ, (∀ p ∈ S, 1 ≤ f p ∧ f p ≤ L + 1) ∧
        ∀ j, 1 ≤ j → j ≤ L → (S.filter (fun p => f p = j)).card = d (j - 1) := by
  classical
  intro L
  induction L with
  | zero =>
      intro S d _
      exact ⟨fun _ => 1, fun p _ => ⟨le_refl 1, le_refl 1⟩, fun j hj1 hj0 => absurd hj1 (by omega)⟩
  | succ L ih =>
      intro S d hcard
      have hsplit : ∑ i ∈ range (L + 1), d i = (∑ i ∈ range L, d i) + d L :=
        Finset.sum_range_succ _ _
      have hdL : d L ≤ S.card := by omega
      obtain ⟨T, hTS, hTcard⟩ := Finset.exists_subset_card_eq hdL
      have hcard' : (∑ i ∈ range L, d i) ≤ (S \ T).card := by
        rw [Finset.card_sdiff_of_subset hTS, hTcard]
        omega
      obtain ⟨f', hf'range, hf'count⟩ := ih (S \ T) d hcard'
      refine ⟨fun p => if p ∈ T then L + 1 else (if f' p = L + 1 then L + 2 else f' p), ?_, ?_⟩
      · intro p hp
        by_cases hpT : p ∈ T
        · simp [hpT]
        · have hp' : p ∈ S \ T := Finset.mem_sdiff.2 ⟨hp, hpT⟩
          obtain ⟨h1, h2⟩ := hf'range p hp'
          by_cases hf : f' p = L + 1 <;> simp [hpT, hf] <;> omega
      · intro j hj1 hjL
        rcases eq_or_lt_of_le hjL with hjeq | hjlt
        · -- the new block: exactly `T`
          have : S.filter (fun p => (if p ∈ T then L + 1 else
              (if f' p = L + 1 then L + 2 else f' p)) = j) = T := by
            ext p
            simp only [Finset.mem_filter]
            constructor
            · rintro ⟨hpS, hval⟩
              by_contra hpT
              rw [if_neg hpT] at hval
              have hp' : p ∈ S \ T := Finset.mem_sdiff.2 ⟨hpS, hpT⟩
              obtain ⟨h1, h2⟩ := hf'range p hp'
              by_cases hf : f' p = L + 1
              · rw [if_pos hf] at hval; omega
              · rw [if_neg hf] at hval; omega
            · intro hpT
              exact ⟨hTS hpT, by rw [if_pos hpT]; omega⟩
          rw [this, hTcard]
          congr 1
          omega
        · -- an old block, untouched
          have : S.filter (fun p => (if p ∈ T then L + 1 else
              (if f' p = L + 1 then L + 2 else f' p)) = j)
              = (S \ T).filter (fun p => f' p = j) := by
            ext p
            simp only [Finset.mem_filter, Finset.mem_sdiff]
            constructor
            · rintro ⟨hpS, hval⟩
              by_cases hpT : p ∈ T
              · rw [if_pos hpT] at hval; omega
              · rw [if_neg hpT] at hval
                by_cases hf : f' p = L + 1
                · rw [if_pos hf] at hval; omega
                · rw [if_neg hf] at hval; exact ⟨⟨hpS, hpT⟩, hval⟩
            · rintro ⟨⟨hpS, hpT⟩, hval⟩
              refine ⟨hpS, ?_⟩
              rw [if_neg hpT, if_neg (by omega : ¬ f' p = L + 1), hval]
          rw [this]
          exact hf'count j hj1 (by omega)

/-! ### The prime supply

The steering needs `K = (b−1)·L` primes in `(L, P]`, and the *remainder* bound of
`tailSmall_head_rem` needs `π(P)` to stay linear in `L`.  Taking `P` minimal gives both: the
window holds exactly `K` primes, so `π(P) ≤ L + K`. -/

lemma piCount_le (L : ℕ) : piCount L ≤ L := by
  classical
  unfold piCount
  have hsub : (range (L + 1)).filter Nat.Prime ⊆ Finset.Icc 2 L := by
    intro p hp
    simp only [Finset.mem_filter, mem_range] at hp
    exact Finset.mem_Icc.2 ⟨hp.2.two_le, by omega⟩
  calc ((range (L + 1)).filter Nat.Prime).card ≤ (Finset.Icc 2 L).card :=
        Finset.card_le_card hsub
    _ = L + 1 - 2 := by rw [Nat.card_Icc]
    _ ≤ L := by omega

/-- There are arbitrarily many primes above any bound. -/
lemma exists_prime_window_aux (L : ℕ) : ∀ K : ℕ,
    ∃ P, L ≤ P ∧ K ≤ ((Finset.Ioc L P).filter Nat.Prime).card := by
  classical
  intro K
  induction K with
  | zero => exact ⟨L, le_refl L, Nat.zero_le _⟩
  | succ K ih =>
      obtain ⟨P, hLP, hcard⟩ := ih
      obtain ⟨q, hqP, hq⟩ := Nat.exists_infinite_primes (P + 1)
      refine ⟨q, by omega, ?_⟩
      have hsub : insert q ((Finset.Ioc L P).filter Nat.Prime)
          ⊆ (Finset.Ioc L q).filter Nat.Prime := by
        intro x hx
        rcases Finset.mem_insert.1 hx with rfl | hx
        · exact Finset.mem_filter.2 ⟨Finset.mem_Ioc.2 ⟨by omega, le_refl _⟩, hq⟩
        · simp only [Finset.mem_filter, Finset.mem_Ioc] at hx ⊢
          exact ⟨⟨hx.1.1, by omega⟩, hx.2⟩
      have hnot : q ∉ (Finset.Ioc L P).filter Nat.Prime := by
        simp only [Finset.mem_filter, Finset.mem_Ioc]
        rintro ⟨⟨-, h⟩, -⟩
        omega
      calc K + 1 ≤ ((Finset.Ioc L P).filter Nat.Prime).card + 1 := by omega
        _ = (insert q ((Finset.Ioc L P).filter Nat.Prime)).card :=
            (Finset.card_insert_of_notMem hnot).symm
        _ ≤ _ := Finset.card_le_card hsub

/-- **The prime window.**  For every `L` and `K` there is a `P ≥ L` with exactly `K` primes in
`(L, P]`, hence `π(P) ≤ L + K`. -/
theorem exists_prime_window (L K : ℕ) :
    ∃ P, L ≤ P ∧ ((Finset.Ioc L P).filter Nat.Prime).card = K ∧ piCount P ≤ L + K := by
  classical
  have hex : ∃ P, L ≤ P ∧ K ≤ ((Finset.Ioc L P).filter Nat.Prime).card :=
    exists_prime_window_aux L K
  obtain ⟨hLP, hge⟩ := Nat.find_spec hex
  have hmin : ∀ m, m < Nat.find hex →
      ¬ (L ≤ m ∧ K ≤ ((Finset.Ioc L m).filter Nat.Prime).card) :=
    fun m hm => Nat.find_min hex hm
  have hle : ((Finset.Ioc L (Nat.find hex)).filter Nat.Prime).card ≤ K := by
    rcases eq_or_lt_of_le hLP with hPL | hPL
    · have hempty : (Finset.Ioc L (Nat.find hex)).filter Nat.Prime = ∅ := by
        rw [← hPL]; simp
      rw [hempty]; simp
    · have hlt : ((Finset.Ioc L (Nat.find hex - 1)).filter Nat.Prime).card < K := by
        by_contra hcon
        exact hmin (Nat.find hex - 1) (by omega) ⟨by omega, by omega⟩
      have hsub : (Finset.Ioc L (Nat.find hex)).filter Nat.Prime
          ⊆ insert (Nat.find hex) ((Finset.Ioc L (Nat.find hex - 1)).filter Nat.Prime) := by
        intro x hx
        simp only [Finset.mem_filter, Finset.mem_Ioc] at hx
        rcases eq_or_lt_of_le hx.1.2 with rfl | hxP
        · exact Finset.mem_insert_self _ _
        · refine Finset.mem_insert_of_mem ?_
          simp only [Finset.mem_filter, Finset.mem_Ioc]
          exact ⟨⟨hx.1.1, by omega⟩, hx.2⟩
      calc ((Finset.Ioc L (Nat.find hex)).filter Nat.Prime).card
          ≤ (insert (Nat.find hex)
              ((Finset.Ioc L (Nat.find hex - 1)).filter Nat.Prime)).card :=
            Finset.card_le_card hsub
        _ ≤ ((Finset.Ioc L (Nat.find hex - 1)).filter Nat.Prime).card + 1 :=
            Finset.card_insert_le _ _
        _ ≤ K := by omega
  refine ⟨Nat.find hex, hLP, le_antisymm hle hge, ?_⟩
  have hpi : piCount (Nat.find hex)
      ≤ piCount L + ((Finset.Ioc L (Nat.find hex)).filter Nat.Prime).card := by
    unfold piCount
    have hsub : (range (Nat.find hex + 1)).filter Nat.Prime
        ⊆ ((range (L + 1)).filter Nat.Prime)
            ∪ ((Finset.Ioc L (Nat.find hex)).filter Nat.Prime) := by
      intro x hx
      simp only [Finset.mem_filter, mem_range, Finset.mem_union, Finset.mem_Ioc] at hx ⊢
      rcases le_or_gt x L with h | h
      · exact Or.inl ⟨by omega, hx.2⟩
      · exact Or.inr ⟨⟨h, by omega⟩, hx.2⟩
    calc ((range (Nat.find hex + 1)).filter Nat.Prime).card
        ≤ (((range (L + 1)).filter Nat.Prime)
            ∪ ((Finset.Ioc L (Nat.find hex)).filter Nat.Prime)).card :=
          Finset.card_le_card hsub
      _ ≤ _ := Finset.card_union_le _ _
  have hpl := piCount_le L
  have := le_antisymm hle hge
  omega

end NormalNumbers