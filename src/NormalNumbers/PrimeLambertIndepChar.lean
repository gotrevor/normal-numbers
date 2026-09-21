import NormalNumbers.PrimeLambertMoments

/-!
# The CRT factorization of the independent model's characteristic function

`IndepCharDecay C` (draft (13)+(15)) asks that `‖indepAvg C N e(q·)‖ → 0`, where `indepAvg` is the
average of `e(q S_N(r))` over a uniform residue `r` modulo `∏_{p small} p`.  The draft proves this
by *factorizing*: since `S_N = ∑_{p small} X_p` and `X_p` is `p`-periodic, the Chinese Remainder
Theorem makes the `X_p` independent under a uniform residue, so

  `indepAvg e(q·) = ∏_{p small} localChar p`,   `localChar p = (1/p) ∑_{u<p} e(q X_p(u))`,

and each local factor is a `p`-average of a phase, bounded away from `1` in modulus whenever `X_p`
is non-constant mod `p`.  `IndepCharDecay` is then a divergence statement for `∑_p (1 − ‖localChar p‖)`
— a Mertens-type sum — rather than anything about the arithmetic sample.

This file supplies the factorization and the wiring from it to `IndepCharDecay`; it is
**sorry-free**.  The pointwise Euler-product identity `e(q S_N(n)) = ∏_p e(q X_p(n))` is exact
(`e_smallSum_eq_prod`), and the CRT step `indepAvg_e_eq_prod` is proved from a general
Chinese-Remainder product formula for periodic functions over pairwise coprime moduli
(`sum_range_mul_of_coprime`, `sum_prod_of_pairwise_coprime`), which may be of independent use.

Net effect on the research map: `IndepCharDecay C` — one of the three obligations of
`MomentChain` → `SmallPrimeDecay` → `phaseOscillation` — is now *equivalent* to a statement about
the local factors alone (`indepCharDecay_of_localChar`), with no arithmetic sample in sight:
`∏_{p small} ‖localChar p‖ → 0`, i.e. divergence of the Mertens-type sum
`∑_{p small} (1 − ‖localChar p‖)`.
-/

open Filter Topology Finset Complex
open scoped BigOperators

namespace NormalNumbers.PrimeLambert

lemma e_zero : e 0 = 1 := by unfold e; simp

/-- `e` turns finite sums into finite products. -/
lemma e_sum {ι : Type*} (s : Finset ι) (f : ι → ℝ) :
    e (∑ i ∈ s, f i) = ∏ i ∈ s, e (f i) := by
  classical
  induction s using Finset.induction with
  | empty => simp [e_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, e_mul, ih]

/-! ### The Chinese-Remainder product formula -/

/-- **Two-modulus CRT reindexing.**  For coprime `a, m` the map `r ↦ (r % a, r % m)` is a
bijection `range (a*m) → range a ×ˢ range m`, so a product of a `a`-periodic and an `m`-periodic
function sums to the product of the two sums. -/
lemma sum_range_mul_of_coprime {a m : ℕ} (ha : 0 < a) (hm : 0 < m) (hcop : Nat.Coprime a m)
    (G H : ℕ → ℂ) :
    ∑ r ∈ range (a * m), G (r % a) * H (r % m)
      = (∑ u ∈ range a, G u) * (∑ v ∈ range m, H v) := by
  rw [Finset.sum_mul_sum, ← Finset.sum_product']
  refine Finset.sum_nbij (fun r => (r % a, r % m)) ?_ ?_ ?_ ?_
  · intro r _
    simp only [Finset.mem_product, Finset.mem_range]
    exact ⟨Nat.mod_lt _ ha, Nat.mod_lt _ hm⟩
  · intro x hx y hy hxy
    simp only [Finset.mem_coe, Finset.mem_range] at hx hy
    simp only [Prod.mk.injEq] at hxy
    have h1 : x ≡ y [MOD a] := hxy.1
    have h2 : x ≡ y [MOD m] := hxy.2
    have h3 : x ≡ y [MOD a * m] :=
      (Nat.modEq_and_modEq_iff_modEq_mul hcop).mp ⟨h1, h2⟩
    have := h3
    unfold Nat.ModEq at this
    rwa [Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy] at this
  · rintro ⟨b1, b2⟩ hb
    simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, Finset.mem_range] at hb
    obtain ⟨hb1, hb2⟩ := hb
    obtain ⟨k, hk1, hk2⟩ := Nat.chineseRemainder hcop b1 b2
    have hx : k % (a * m) ∈ (range (a * m) : Finset ℕ) := by
      rw [Finset.mem_range]; exact Nat.mod_lt _ (Nat.mul_pos ha hm)
    refine ⟨k % (a * m), Finset.mem_coe.mpr hx, ?_⟩
    have hA : k % (a * m) % a = b1 := by
      rw [Nat.mod_mod_of_dvd _ (⟨m, rfl⟩ : a ∣ a * m)]
      have hh : k % a = b1 % a := hk1
      rw [hh, Nat.mod_eq_of_lt hb1]
    have hM : k % (a * m) % m = b2 := by
      rw [Nat.mod_mod_of_dvd _ (⟨a, by ring⟩ : m ∣ a * m)]
      have hh : k % m = b2 % m := hk2
      rw [hh, Nat.mod_eq_of_lt hb2]
    simp only [Prod.mk.injEq]
    exact ⟨hA, hM⟩
  · intro r _
    rfl

/-- **CRT product formula.**  For a finite set of pairwise coprime moduli, the sum over one full
period of a product of periodic functions factorizes. -/
lemma sum_prod_of_pairwise_coprime :
    ∀ (s : Finset ℕ), (∀ p ∈ s, 0 < p) → (s : Set ℕ).Pairwise Nat.Coprime →
      ∀ F : ℕ → ℕ → ℂ, (∀ p ∈ s, ∀ r : ℕ, F p r = F p (r % p)) →
        ∑ r ∈ range (∏ p ∈ s, p), ∏ p ∈ s, F p r = ∏ p ∈ s, ∑ u ∈ range p, F p u := by
  classical
  intro s
  induction s using Finset.induction with
  | empty => intro _ _ _ _; simp
  | insert a t ha ih =>
    intro hpos hcop F hper
    set m := ∏ p ∈ t, p with hm
    have hapos : 0 < a := hpos a (Finset.mem_insert_self a t)
    have hmpos : 0 < m := Finset.prod_pos (fun p hp => hpos p (Finset.mem_insert_of_mem hp))
    have ham : Nat.Coprime a m := by
      refine Nat.Coprime.prod_right (fun p hp => ?_)
      exact hcop (Finset.mem_insert_self a t) (Finset.mem_insert_of_mem hp)
        (fun h => ha (h ▸ hp))
    have hprod : ∏ p ∈ insert a t, p = a * m := by rw [Finset.prod_insert ha]
    -- the `t`-part depends on `r` only through `r % m`
    have hH : ∀ r : ℕ, ∏ p ∈ t, F p r = ∏ p ∈ t, F p (r % m) := by
      intro r
      refine Finset.prod_congr rfl (fun p hp => ?_)
      have hdvd : p ∣ m := Finset.dvd_prod_of_mem _ hp
      rw [hper p (Finset.mem_insert_of_mem hp) r,
        hper p (Finset.mem_insert_of_mem hp) (r % m), Nat.mod_mod_of_dvd _ hdvd]
    have hlhs : ∑ r ∈ range (∏ p ∈ insert a t, p), ∏ p ∈ insert a t, F p r
        = ∑ r ∈ range (a * m), F a (r % a) * (∏ p ∈ t, F p (r % m)) := by
      rw [hprod]
      refine Finset.sum_congr rfl (fun r _ => ?_)
      rw [Finset.prod_insert ha, hper a (Finset.mem_insert_self a t) r, hH r]
    rw [hlhs, sum_range_mul_of_coprime hapos hmpos ham
      (fun u => F a u) (fun v => ∏ p ∈ t, F p v)]
    rw [Finset.prod_insert ha]
    congr 1
    exact ih (fun p hp => hpos p (Finset.mem_insert_of_mem hp))
      (hcop.mono (by simpa using Finset.coe_subset.mpr (Finset.subset_insert a t)))
      F (fun p hp => hper p (Finset.mem_insert_of_mem hp))

/-- The local factor at a small prime `p`: the average of `e(q X_p)` over one residue period. -/
noncomputable def localChar {q : ℤ} (C : Chain q) (N : ℕ) (p : ℕ) : ℂ :=
  avg (range p) (fun u : ℕ => e (q * primePart (C.c N) (C.K N) (C.S N).J p (u : ℤ)))

/-- **Exact Euler product, pointwise**: the small-prime phase is the product of its local phases. -/
theorem e_smallSum_eq_prod {q : ℤ} (C : Chain q) (N : ℕ) (n : ℤ) :
    e (q * smallSum C N n)
      = ∏ p ∈ (C.S N).small, e (q * primePart (C.c N) (C.K N) (C.S N).J p n) := by
  unfold smallSum classSum
  rw [Finset.mul_sum, e_sum]

/-- **CRT factorization of the independent model.**  Under a uniform residue modulo
`∏_{p small} p` the local variables `X_p` are independent, so the characteristic function is the
product of the local ones.  This is draft §5.3's "independent model" statement, made exact.

Proved from the CRT product formula `sum_prod_of_pairwise_coprime`. -/
theorem indepAvg_e_eq_prod {q : ℤ} (C : Chain q) (N : ℕ) :
    indepAvg C N (fun x => e (q * x)) = ∏ p ∈ (C.S N).small, localChar C N p := by
  set F : ℕ → ℕ → ℂ :=
    fun p r => e (q * primePart (C.c N) (C.K N) (C.S N).J p (r : ℤ)) with hF
  have hper : ∀ p ∈ (C.S N).small, ∀ r : ℕ, F p r = F p (r % p) := by
    intro p _ r
    simp only [hF]
    congr 2
    refine primePart_congr _ _ _ p _ _ ?_
    refine ⟨(r / p : ℕ), ?_⟩
    have : (r : ℤ) = (p : ℤ) * ((r / p : ℕ) : ℤ) + ((r % p : ℕ) : ℤ) := by
      exact_mod_cast congrArg (Nat.cast : ℕ → ℤ) (Nat.div_add_mod r p).symm
    omega
  have hpos : ∀ p ∈ (C.S N).small, 0 < p := fun p hp => ((C.S N).prime_small p hp).pos
  have hcop : ((C.S N).small : Set ℕ).Pairwise Nat.Coprime := by
    intro x hx y hy hxy
    exact (Nat.coprime_primes ((C.S N).prime_small x hx) ((C.S N).prime_small y hy)).mpr hxy
  have hcrt := sum_prod_of_pairwise_coprime (C.S N).small hpos hcop F hper
  have hM : (∏ p ∈ (C.S N).small, p) = modulus C N := rfl
  rw [hM] at hcrt
  unfold indepAvg avg localChar avg
  rw [Finset.card_range]
  have hnum : ∑ r ∈ range (modulus C N), e (q * smallSum C N (r : ℤ))
      = ∑ r ∈ range (modulus C N), ∏ p ∈ (C.S N).small, F p r :=
    Finset.sum_congr rfl (fun r _ => e_smallSum_eq_prod C N (r : ℤ))
  rw [hnum, hcrt]
  rw [Finset.prod_div_distrib]
  congr 1
  simp only [Finset.card_range]
  rw [← Nat.cast_prod]
  rfl

/-- Consequently the modulus of the independent characteristic function is the product of the
moduli of the local factors. -/
theorem norm_indepAvg_e_eq_prod {q : ℤ} (C : Chain q) (N : ℕ) :
    ‖indepAvg C N (fun x => e (q * x))‖ = ∏ p ∈ (C.S N).small, ‖localChar C N p‖ := by
  rw [indepAvg_e_eq_prod, norm_prod]

/-- **Wiring**: `IndepCharDecay` is exactly a statement about the local factors — no reference to
the arithmetic sample survives. -/
theorem indepCharDecay_of_localChar {q : ℤ} (C : Chain q)
    (h : Tendsto (fun N => ∏ p ∈ (C.S N).small, ‖localChar C N p‖) atTop (𝓝 0)) :
    IndepCharDecay C := by
  refine h.congr (fun N => ?_)
  rw [norm_indepAvg_e_eq_prod]

/-- Each local factor has modulus at most `1`. -/
theorem norm_localChar_le_one {q : ℤ} (C : Chain q) (N : ℕ) {p : ℕ} (hp : 0 < p) :
    ‖localChar C N p‖ ≤ 1 := by
  unfold localChar avg
  rw [norm_div, Complex.norm_natCast, Finset.card_range]
  have hpr : (0:ℝ) < p := by exact_mod_cast hp
  rw [div_le_one hpr]
  calc ‖∑ u ∈ range p, e (q * primePart (C.c N) (C.K N) (C.S N).J p (u : ℤ))‖
      ≤ ∑ u ∈ range p, ‖e (q * primePart (C.c N) (C.K N) (C.S N).J p (u : ℤ))‖ := norm_sum_le _ _
    _ = p := by
        rw [Finset.sum_congr rfl (fun u _ => norm_e _), Finset.sum_const, Finset.card_range,
          nsmul_eq_mul, mul_one]

/-! ### The local factors are bounded away from one

`IndepCharDecay` now reads `∏_{p small} ‖localChar p‖ → 0`.  What makes a factor useful is a
*defect*: `‖localChar p‖ ≤ 1 − (defect)/p`.  The elementary source of a defect is that two of the
`p` local phases differ — one pair of unequal unimodular summands already costs the average
`‖z_a − z_b‖²/(4p)`, by the parallelogram law. -/

/-- Two unequal unimodular summands cost a sum of unimodular terms a definite amount. -/
lemma norm_add_le_two_sub (x y : ℂ) (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) :
    ‖x + y‖ ≤ 2 - ‖x - y‖ ^ 2 / 4 := by
  have hpar : ‖x + y‖ ^ 2 + ‖x - y‖ ^ 2 = 2 * (‖x‖ ^ 2 + ‖y‖ ^ 2) :=
    parallelogram_law_with_norm ℝ x y
  rw [hx, hy] at hpar
  have hs : 0 ≤ ‖x + y‖ := norm_nonneg _
  nlinarith [hpar, hs, sq_nonneg (‖x + y‖ - 2)]

/-- **Defect bound.**  A sum of unimodular terms over a finite set loses `‖z a − z b‖²/4`
from the trivial bound as soon as two of its terms differ. -/
lemma norm_sum_le_card_sub {ι : Type*} [DecidableEq ι] {P : Finset ι} (z : ι → ℂ)
    (hz : ∀ i ∈ P, ‖z i‖ = 1) {a b : ι} (ha : a ∈ P) (hb : b ∈ P) (hab : a ≠ b) :
    ‖∑ i ∈ P, z i‖ ≤ (P.card : ℝ) - ‖z a - z b‖ ^ 2 / 4 := by
  have hsub : ({a, b} : Finset ι) ⊆ P := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl <;> assumption
  have hcard2 : ({a, b} : Finset ι).card = 2 := by rw [Finset.card_pair hab]
  have hcardle : 2 ≤ P.card := by
    have := Finset.card_le_card hsub
    omega
  have hsplit : ∑ i ∈ P, z i = ∑ i ∈ P \ {a, b}, z i + ∑ i ∈ ({a, b} : Finset ι), z i :=
    (Finset.sum_sdiff hsub).symm
  have hpair : ∑ i ∈ ({a, b} : Finset ι), z i = z a + z b := Finset.sum_pair hab
  have hrest : ‖∑ i ∈ P \ {a, b}, z i‖ ≤ ((P \ {a, b}).card : ℝ) := by
    calc ‖∑ i ∈ P \ {a, b}, z i‖ ≤ ∑ i ∈ P \ {a, b}, ‖z i‖ := norm_sum_le _ _
      _ = ((P \ {a, b}).card : ℝ) := by
          rw [Finset.sum_congr rfl (fun i hi => hz i (Finset.mem_sdiff.mp hi).1),
            Finset.sum_const, nsmul_eq_mul, mul_one]
  have hcardsd : ((P \ {a, b}).card : ℝ) = (P.card : ℝ) - 2 := by
    have : (P \ {a, b}).card = P.card - 2 := by
      rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hsub, hcard2]
    rw [this]
    have : ((P.card - 2 : ℕ) : ℝ) = (P.card : ℝ) - 2 := by
      have := hcardle; push_cast [Nat.cast_sub hcardle]; ring
    exact this
  have hab' := norm_add_le_two_sub (z a) (z b) (hz a ha) (hz b hb)
  calc ‖∑ i ∈ P, z i‖ ≤ ‖∑ i ∈ P \ {a, b}, z i‖ + ‖z a + z b‖ := by
        rw [hsplit, hpair]; exact norm_add_le _ _
    _ ≤ ((P.card : ℝ) - 2) + (2 - ‖z a - z b‖ ^ 2 / 4) := by
        rw [← hcardsd]; exact add_le_add hrest hab'
    _ = (P.card : ℝ) - ‖z a - z b‖ ^ 2 / 4 := by ring

/-- **The local defect.**  If the local variable `X_p` takes two phases that differ at
`u ≠ v` mod `p`, the local factor is bounded away from `1` by `‖·‖²/(4p)`. -/
theorem norm_localChar_le_one_sub {q : ℤ} (C : Chain q) (N : ℕ) {p : ℕ} (hp : 0 < p)
    {u v : ℕ} (hu : u < p) (hv : v < p) (huv : u ≠ v) :
    ‖localChar C N p‖
      ≤ 1 - ‖e (q * primePart (C.c N) (C.K N) (C.S N).J p (u : ℤ))
              - e (q * primePart (C.c N) (C.K N) (C.S N).J p (v : ℤ))‖ ^ 2 / (4 * p) := by
  have hpr : (0:ℝ) < p := by exact_mod_cast hp
  unfold localChar avg
  rw [norm_div, Complex.norm_natCast, Finset.card_range]
  rw [div_le_iff₀ hpr]
  have hbd := norm_sum_le_card_sub
    (P := range p) (fun r : ℕ => e (q * primePart (C.c N) (C.K N) (C.S N).J p (r : ℤ)))
    (fun i _ => norm_e _) (Finset.mem_range.mpr hu) (Finset.mem_range.mpr hv) huv
  rw [Finset.card_range] at hbd
  refine hbd.trans (le_of_eq ?_)
  field_simp

end NormalNumbers.PrimeLambert
