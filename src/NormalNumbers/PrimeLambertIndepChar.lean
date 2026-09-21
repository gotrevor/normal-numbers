import NormalNumbers.PrimeLambertMoments
import NormalNumbers.PrimeLambertLarge

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

/-! ### The defect in closed form

`‖e x − e y‖ = 2|sin π(x−y)|`, so the local defect is a sine of the phase gap and the bound
becomes `‖localChar p‖ ≤ 1 − sin²(π q (X_p(u) − X_p(v)))/p`. -/

lemma norm_e_sub_one_eq (t : ℝ) : ‖e t - 1‖ = 2 * |Real.sin (Real.pi * t)| := by
  have hexp : e t - 1
      = ((Real.cos (2 * Real.pi * t) - 1 : ℝ) : ℂ)
        + ((Real.sin (2 * Real.pi * t) : ℝ) : ℂ) * Complex.I := by
    unfold e
    rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
    push_cast
    ring
  rw [hexp, Complex.norm_add_mul_I]
  have hpy := Real.sin_sq_add_cos_sq (Real.pi * t)
  have hcos : Real.cos (2 * Real.pi * t) = 1 - 2 * Real.sin (Real.pi * t) ^ 2 := by
    rw [show 2 * Real.pi * t = 2 * (Real.pi * t) by ring, Real.cos_two_mul]
    nlinarith [hpy]
  have hs : Real.sin (2 * Real.pi * t) ^ 2 = 1 - Real.cos (2 * Real.pi * t) ^ 2 := by
    nlinarith [Real.sin_sq_add_cos_sq (2 * Real.pi * t)]
  have hkey : (Real.cos (2 * Real.pi * t) - 1) ^ 2 + Real.sin (2 * Real.pi * t) ^ 2
      = (2 * |Real.sin (Real.pi * t)|) ^ 2 := by
    rw [hs, hcos]
    have habs : |Real.sin (Real.pi * t)| ^ 2 = Real.sin (Real.pi * t) ^ 2 := sq_abs _
    nlinarith [habs]
  rw [hkey, Real.sqrt_sq (by positivity)]

lemma norm_e_sub_e (x y : ℝ) : ‖e x - e y‖ = 2 * |Real.sin (Real.pi * (x - y))| := by
  have hfac : e x - e y = e y * (e (x - y) - 1) := by
    rw [mul_sub, ← e_mul, mul_one, show y + (x - y) = x by ring]
  rw [hfac, norm_mul, norm_e, one_mul, norm_e_sub_one_eq]

/-- **The local defect in closed form.** -/
theorem norm_localChar_le_one_sub_sin {q : ℤ} (C : Chain q) (N : ℕ) {p : ℕ} (hp : 0 < p)
    {u v : ℕ} (hu : u < p) (hv : v < p) (huv : u ≠ v) :
    ‖localChar C N p‖
      ≤ 1 - Real.sin (Real.pi * (q * (primePart (C.c N) (C.K N) (C.S N).J p (u : ℤ)
              - primePart (C.c N) (C.K N) (C.S N).J p (v : ℤ)))) ^ 2 / p := by
  have hpr : (0:ℝ) < p := by exact_mod_cast hp
  have hbd := norm_localChar_le_one_sub C N hp hu hv huv
  refine hbd.trans (le_of_eq ?_)
  rw [norm_e_sub_e]
  have harg : (q : ℝ) * primePart (C.c N) (C.K N) (C.S N).J p (u : ℤ)
      - (q : ℝ) * primePart (C.c N) (C.K N) (C.S N).J p (v : ℤ)
      = (q : ℝ) * (primePart (C.c N) (C.K N) (C.S N).J p (u : ℤ)
          - primePart (C.c N) (C.K N) (C.S N).J p (v : ℤ)) := by ring
  rw [harg]
  have habs : |Real.sin (Real.pi * ((q : ℝ) *
      (primePart (C.c N) (C.K N) (C.S N).J p (u : ℤ)
        - primePart (C.c N) (C.K N) (C.S N).J p (v : ℤ))))| ^ 2
      = Real.sin (Real.pi * ((q : ℝ) *
      (primePart (C.c N) (C.K N) (C.S N).J p (u : ℤ)
        - primePart (C.c N) (C.K N) (C.S N).J p (v : ℤ)))) ^ 2 := sq_abs _
  rw [mul_pow, habs]
  field_simp
  ring

/-- **Qualitative form**: a local factor has modulus `< 1` as soon as the `q`-phase gap between
two residues is not an integer. -/
theorem norm_localChar_lt_one {q : ℤ} (C : Chain q) (N : ℕ) {p : ℕ} (hp : 0 < p)
    {u v : ℕ} (hu : u < p) (hv : v < p) (huv : u ≠ v)
    (hgap : Real.sin (Real.pi * (q * (primePart (C.c N) (C.K N) (C.S N).J p (u : ℤ)
              - primePart (C.c N) (C.K N) (C.S N).J p (v : ℤ)))) ≠ 0) :
    ‖localChar C N p‖ < 1 := by
  have hpr : (0:ℝ) < p := by exact_mod_cast hp
  have hbd := norm_localChar_le_one_sub_sin C N hp hu hv huv
  have hpos : 0 < Real.sin (Real.pi * (q * (primePart (C.c N) (C.K N) (C.S N).J p (u : ℤ)
      - primePart (C.c N) (C.K N) (C.S N).J p (v : ℤ)))) ^ 2 := by positivity
  have : 0 < Real.sin (Real.pi * (q * (primePart (C.c N) (C.K N) (C.S N).J p (u : ℤ)
      - primePart (C.c N) (C.K N) (C.S N).J p (v : ℤ)))) ^ 2 / p := by positivity
  linarith

/-! ### Evaluating a local variable

For a prime `p` larger than all the moduli involved, each pair `(a, i) ∈ support × [K,J)` pins a
single residue class `n ≡ s_a − (i+1) d_a (mod p)`.  A residue hit by no pair gives `X_p = 0`; a
residue hit by exactly one pair `(a₀, i₀)` gives `X_p = c(a₀)/2^{i₀+1}`.  So the local defect at
such a prime is the explicit sine `sin²(π q c(a₀) 2^{−(i₀+1)})`. -/

/-- A residue hit by exactly one `(a₀,i₀)` has `X_p = c(a₀)/2^{i₀+1}`. -/
theorem primePart_eq_single {c : TConfig} {K J p : ℕ} {n : ℤ} {a₀ : ℕ × ℤ} {i₀ : ℕ}
    (ha₀ : a₀ ∈ c.support) (hi₀ : i₀ ∈ Ico K J)
    (hhit : (p : ℤ) ∣ n + ((i₀ : ℤ) + 1) * a₀.1 - a₀.2)
    (hother : ∀ a ∈ c.support, ∀ i ∈ Ico K J, (a, i) ≠ (a₀, i₀) →
      ¬ (p : ℤ) ∣ n + ((i : ℤ) + 1) * a.1 - a.2) :
    primePart c K J p n = (c a₀ : ℝ) / 2 ^ (i₀ + 1) := by
  classical
  unfold primePart Finsupp.sum
  rw [Finset.sum_eq_single_of_mem a₀ ha₀ ?_]
  · dsimp only
    have hinner : ∑ i ∈ Ico K J,
        (if (p : ℤ) ∣ n + ((i : ℤ) + 1) * a₀.1 - a₀.2 then (1 : ℝ) / 2 ^ (i + 1) else 0)
        = (1 : ℝ) / 2 ^ (i₀ + 1) := by
      rw [Finset.sum_eq_single_of_mem i₀ hi₀ ?_]
      · exact if_pos hhit
      · intro i hi hne
        exact if_neg (hother a₀ ha₀ i hi (by simp [hne]))
    rw [hinner]
    ring
  · intro a ha hne
    dsimp only
    have : ∑ i ∈ Ico K J,
        (if (p : ℤ) ∣ n + ((i : ℤ) + 1) * a.1 - a.2 then (1 : ℝ) / 2 ^ (i + 1) else 0) = 0 :=
      Finset.sum_eq_zero (fun i hi => if_neg (hother a ha i hi (by simp [hne])))
    rw [this, mul_zero]

/-- **The explicit local defect at a large prime.**  If the residues `u` and `v` (mod `p`)
respectively hit exactly one pair `(a₀,i₀)` and no pair at all, the local factor obeys
`‖localChar p‖ ≤ 1 − sin²(π q c(a₀) 2^{−(i₀+1)})/p` — a bound with no arithmetic left in it. -/
theorem norm_localChar_le_of_single {q : ℤ} (C : Chain q) (N : ℕ) {p : ℕ} (hp : 0 < p)
    {u v : ℕ} (hu : u < p) (hv : v < p) (huv : u ≠ v)
    {a₀ : ℕ × ℤ} {i₀ : ℕ} (ha₀ : a₀ ∈ (C.c N).support) (hi₀ : i₀ ∈ Ico (C.K N) (C.S N).J)
    (hhit : (p : ℤ) ∣ (u : ℤ) + ((i₀ : ℤ) + 1) * a₀.1 - a₀.2)
    (hother : ∀ a ∈ (C.c N).support, ∀ i ∈ Ico (C.K N) (C.S N).J, (a, i) ≠ (a₀, i₀) →
      ¬ (p : ℤ) ∣ (u : ℤ) + ((i : ℤ) + 1) * a.1 - a.2)
    (hfree : ∀ a ∈ (C.c N).support, ∀ i ∈ Ico (C.K N) (C.S N).J,
      ¬ (p : ℤ) ∣ (v : ℤ) + ((i : ℤ) + 1) * a.1 - a.2) :
    ‖localChar C N p‖
      ≤ 1 - Real.sin (Real.pi * (q * ((C.c N) a₀ : ℝ) / 2 ^ (i₀ + 1))) ^ 2 / p := by
  have hbd := norm_localChar_le_one_sub_sin C N hp hu hv huv
  rw [primePart_eq_single ha₀ hi₀ hhit hother,
    primePart_eq_zero _ _ _ _ _ (by rintro ⟨a, ha, i, hi, hd⟩; exact hfree a ha i hi hd)] at hbd
  refine hbd.trans (le_of_eq ?_)
  congr 3
  ring

/-! ### Both residues exist at a large prime

`X_p` is determined by the `|support| · (J−K)` residue classes `s_a − (i+1)d_a (mod p)`.  Once `p`
exceeds that count a *free* residue exists (`exists_free_residue`), and once `p` separates the
classes a *single-hit* residue exists (`exists_single_hit_residue`).  Together with
`norm_localChar_le_of_single` this makes the defect at such a prime unconditional. -/

/-- The residue class pinned by a pair `(a, i)`. -/
def hitResidue (p : ℕ) (a : ℕ × ℤ) (i : ℕ) : ℕ := ((a.2 - ((i : ℤ) + 1) * a.1) % p).toNat

lemma hitResidue_lt {p : ℕ} (hp : 0 < p) (a : ℕ × ℤ) (i : ℕ) : hitResidue p a i < p := by
  have hppos : (0:ℤ) < p := by exact_mod_cast hp
  have h := Int.emod_nonneg (a.2 - ((i : ℤ) + 1) * a.1) (ne_of_gt hppos)
  have h2 := Int.emod_lt_of_pos (a.2 - ((i : ℤ) + 1) * a.1) hppos
  unfold hitResidue
  omega

lemma dvd_iff_eq_hitResidue {p : ℕ} (hp : 0 < p) {v : ℕ} (hv : v < p) (a : ℕ × ℤ) (i : ℕ) :
    (p : ℤ) ∣ (v : ℤ) + ((i : ℤ) + 1) * a.1 - a.2 ↔ v = hitResidue p a i := by
  have hppos : (0:ℤ) < p := by exact_mod_cast hp
  have hvz : (0:ℤ) ≤ (v:ℤ) := Int.natCast_nonneg v
  have hvlt : (v:ℤ) < (p:ℤ) := by exact_mod_cast hv
  have hvmod : ((v:ℤ)) % p = (v:ℤ) := Int.emod_eq_of_lt hvz hvlt
  have hnn := Int.emod_nonneg (a.2 - ((i : ℤ) + 1) * a.1) (ne_of_gt hppos)
  constructor
  · intro hdvd
    have hd : (p:ℤ) ∣ (a.2 - ((i:ℤ)+1) * a.1) - (v:ℤ) := by
      have := dvd_neg.mpr hdvd
      rwa [show -((v:ℤ) + ((i:ℤ)+1) * a.1 - a.2) = (a.2 - ((i:ℤ)+1) * a.1) - (v:ℤ) by ring] at this
    have hmod : ((v:ℤ)) % p = (a.2 - ((i:ℤ)+1) * a.1) % p := Int.modEq_iff_dvd.mpr hd
    rw [hvmod] at hmod
    unfold hitResidue
    omega
  · intro hveq
    subst hveq
    have hmod : ((hitResidue p a i : ℕ) : ℤ) = (a.2 - ((i:ℤ)+1) * a.1) % p := by
      unfold hitResidue; omega
    have hd : (p:ℤ) ∣ (a.2 - ((i:ℤ)+1) * a.1) - ((hitResidue p a i : ℕ) : ℤ) := by
      rw [hmod]
      exact Int.dvd_self_sub_emod
    have := dvd_neg.mpr hd
    rwa [show -((a.2 - ((i:ℤ)+1) * a.1) - ((hitResidue p a i : ℕ) : ℤ))
      = ((hitResidue p a i : ℕ) : ℤ) + ((i:ℤ)+1) * a.1 - a.2 by ring] at this

/-- **A free residue exists** once `p` exceeds the number of pairs. -/
theorem exists_free_residue {c : TConfig} {K J p : ℕ}
    (hp : (c.support ×ˢ Ico K J).card < p) :
    ∃ v < p, ∀ a ∈ c.support, ∀ i ∈ Ico K J,
      ¬ (p : ℤ) ∣ (v : ℤ) + ((i : ℤ) + 1) * a.1 - a.2 := by
  classical
  have hppos : 0 < p := lt_of_le_of_lt (Nat.zero_le _) hp
  set Bad : Finset ℕ := (range p).filter
    (fun v => ∃ a ∈ c.support, ∃ i ∈ Ico K J,
      (p : ℤ) ∣ (v : ℤ) + ((i : ℤ) + 1) * a.1 - a.2) with hBad
  have hsub : Bad ⊆ (c.support ×ˢ Ico K J).image (fun x => hitResidue p x.1 x.2) := by
    intro v hv
    rw [hBad, Finset.mem_filter, Finset.mem_range] at hv
    obtain ⟨hvp, a, ha, i, hi, hdvd⟩ := hv
    exact Finset.mem_image.mpr ⟨(a, i), Finset.mem_product.mpr ⟨ha, hi⟩,
      ((dvd_iff_eq_hitResidue hppos hvp a i).mp hdvd).symm⟩
  have hcard : Bad.card < p :=
    lt_of_le_of_lt (le_trans (Finset.card_le_card hsub) Finset.card_image_le) hp
  have hex : ∃ v ∈ range p, v ∉ Bad := by
    by_contra hcon
    push Not at hcon
    have hle := Finset.card_le_card (show range p ⊆ Bad from hcon)
    rw [Finset.card_range] at hle
    omega
  obtain ⟨v, hv, hvn⟩ := hex
  refine ⟨v, Finset.mem_range.mp hv, fun a ha i hi hdvd => hvn ?_⟩
  rw [hBad, Finset.mem_filter]
  exact ⟨hv, a, ha, i, hi, hdvd⟩

/-- **A single-hit residue exists** once `p` separates the classes of the other pairs from
`(a₀, i₀)`. -/
theorem exists_single_hit_residue {c : TConfig} {K J p : ℕ} (hp : 0 < p)
    {a₀ : ℕ × ℤ} {i₀ : ℕ}
    (hsep : ∀ a ∈ c.support, ∀ i ∈ Ico K J, (a, i) ≠ (a₀, i₀) →
      hitResidue p a i ≠ hitResidue p a₀ i₀) :
    ∃ u < p, (p : ℤ) ∣ (u : ℤ) + ((i₀ : ℤ) + 1) * a₀.1 - a₀.2 ∧
      ∀ a ∈ c.support, ∀ i ∈ Ico K J, (a, i) ≠ (a₀, i₀) →
        ¬ (p : ℤ) ∣ (u : ℤ) + ((i : ℤ) + 1) * a.1 - a.2 := by
  refine ⟨hitResidue p a₀ i₀, hitResidue_lt hp a₀ i₀, ?_, ?_⟩
  · exact (dvd_iff_eq_hitResidue hp (hitResidue_lt hp a₀ i₀) a₀ i₀).mpr rfl
  · intro a ha i hi hne hdvd
    exact hsep a ha i hi hne
      ((dvd_iff_eq_hitResidue hp (hitResidue_lt hp a₀ i₀) a i).mp hdvd).symm

/-! ### Assembling: `IndepCharDecay` from a divergent defect sum

`∏(1 − δ_p) ≤ exp(−∑ δ_p)`, so a divergent sum of local defects over any subfamily of the small
primes kills the whole product.  This is the last analytic step of `IndepCharDecay`: what remains
afterwards is a *counting* statement about how many small primes carry a defect. -/

/-- Local defects on any subfamily control the whole product. -/
theorem prod_norm_localChar_le_exp {q : ℤ} (C : Chain q) (N : ℕ) (Good : Finset ℕ)
    (hsub : Good ⊆ (C.S N).small) (δ : ℕ → ℝ) (hδ0 : ∀ p ∈ Good, 0 ≤ δ p)
    (hδ : ∀ p ∈ Good, ‖localChar C N p‖ ≤ 1 - δ p) :
    ∏ p ∈ (C.S N).small, ‖localChar C N p‖ ≤ Real.exp (-∑ p ∈ Good, δ p) := by
  classical
  have hsplit : ∏ p ∈ (C.S N).small, ‖localChar C N p‖
      = (∏ p ∈ (C.S N).small \ Good, ‖localChar C N p‖) * ∏ p ∈ Good, ‖localChar C N p‖ :=
    (Finset.prod_sdiff hsub).symm
  have hrest : (∏ p ∈ (C.S N).small \ Good, ‖localChar C N p‖) ≤ 1 :=
    Finset.prod_le_one (fun p _ => norm_nonneg _)
      (fun p hp => norm_localChar_le_one C N
        ((C.S N).prime_small p (Finset.mem_sdiff.mp hp).1).pos)
  have hgoodnn : (0:ℝ) ≤ ∏ p ∈ Good, ‖localChar C N p‖ :=
    Finset.prod_nonneg (fun p _ => norm_nonneg _)
  have hgood : (∏ p ∈ Good, ‖localChar C N p‖) ≤ Real.exp (-∑ p ∈ Good, δ p) := by
    have hstep : ∀ p ∈ Good, ‖localChar C N p‖ ≤ Real.exp (-δ p) := by
      intro p hp
      refine (hδ p hp).trans ?_
      have := Real.add_one_le_exp (-δ p)
      linarith
    calc (∏ p ∈ Good, ‖localChar C N p‖) ≤ ∏ p ∈ Good, Real.exp (-δ p) :=
          Finset.prod_le_prod (fun p _ => norm_nonneg _) hstep
      _ = Real.exp (-∑ p ∈ Good, δ p) := by
          rw [← Real.exp_sum, ← Finset.sum_neg_distrib]
  rw [hsplit]
  calc (∏ p ∈ (C.S N).small \ Good, ‖localChar C N p‖) * ∏ p ∈ Good, ‖localChar C N p‖
      ≤ 1 * ∏ p ∈ Good, ‖localChar C N p‖ :=
        mul_le_mul_of_nonneg_right hrest hgoodnn
    _ = ∏ p ∈ Good, ‖localChar C N p‖ := one_mul _
    _ ≤ Real.exp (-∑ p ∈ Good, δ p) := hgood

/-- **`IndepCharDecay` from a divergent defect sum.**  This is the final reduction: the
obligation holds as soon as, along the chain, *some* subfamily of the small primes carries local
defects whose sum diverges.  Combined with `norm_localChar_le_of_single`, `exists_free_residue`
and `exists_single_hit_residue`, the defects are explicit sines and what is left is a count of
class-separating small primes — no analysis. -/
theorem indepCharDecay_of_defect_sum {q : ℤ} (C : Chain q) (Good : ℕ → Finset ℕ)
    (δ : ℕ → ℕ → ℝ) (hsub : ∀ N, Good N ⊆ (C.S N).small)
    (hδ0 : ∀ N, ∀ p ∈ Good N, 0 ≤ δ N p)
    (hδ : ∀ N, ∀ p ∈ Good N, ‖localChar C N p‖ ≤ 1 - δ N p)
    (hdiv : Tendsto (fun N => ∑ p ∈ Good N, δ N p) atTop atTop) :
    IndepCharDecay C := by
  refine indepCharDecay_of_localChar C ?_
  refine squeeze_zero (fun N => Finset.prod_nonneg (fun p _ => norm_nonneg _))
    (fun N => prod_norm_localChar_le_exp C N (Good N) (hsub N) (δ N) (hδ0 N) (hδ N)) ?_
  exact Real.tendsto_exp_atBot.comp (tendsto_neg_atBot_iff.mpr hdiv)

/-! ### The fully assembled reduction

Everything above combines into a statement of `IndepCharDecay` with **no analysis in it**: pick,
at each `N`, one atom `a₀` and one site `i₀` of the configuration, and a family of small primes
that are bigger than the pair count and separate the residue classes.  Then `IndepCharDecay`
follows from divergence of `∑_p siteDefect / p` — a Mertens-type count. -/

/-- The site defect `sin²(π q c(a) 2^{−(i+1)})`: nonzero exactly when `q c(a) 2^{−(i+1)} ∉ ℤ`. -/
noncomputable def siteDefect (q : ℤ) (w : ℤ) (i : ℕ) : ℝ :=
  Real.sin (Real.pi * (q * (w : ℝ) / 2 ^ (i + 1))) ^ 2

lemma siteDefect_nonneg (q w : ℤ) (i : ℕ) : 0 ≤ siteDefect q w i := sq_nonneg _

/-- A prime at which the local variable `X_p` is controlled by a single atom-site pair. -/
def SeparatingAt {q : ℤ} (C : Chain q) (N : ℕ) (a₀ : ℕ × ℤ) (i₀ : ℕ) (p : ℕ) : Prop :=
  ((C.c N).support ×ˢ Ico (C.K N) (C.S N).J).card < p ∧
    ∀ a ∈ (C.c N).support, ∀ i ∈ Ico (C.K N) (C.S N).J, (a, i) ≠ (a₀, i₀) →
      hitResidue p a i ≠ hitResidue p a₀ i₀

/-- At a separating prime the local factor carries the full site defect. -/
theorem norm_localChar_le_of_separating {q : ℤ} (C : Chain q) (N : ℕ) {a₀ : ℕ × ℤ} {i₀ : ℕ}
    (ha₀ : a₀ ∈ (C.c N).support) (hi₀ : i₀ ∈ Ico (C.K N) (C.S N).J)
    {p : ℕ} (hsep : SeparatingAt C N a₀ i₀ p) :
    ‖localChar C N p‖ ≤ 1 - siteDefect q ((C.c N) a₀) i₀ / p := by
  obtain ⟨hbig, hclass⟩ := hsep
  have hppos : 0 < p := lt_of_le_of_lt (Nat.zero_le _) hbig
  obtain ⟨u, hu, hhit, hother⟩ := exists_single_hit_residue (c := C.c N) (K := C.K N)
    (J := (C.S N).J) hppos hclass
  obtain ⟨v, hv, hfree⟩ := exists_free_residue (c := C.c N) (K := C.K N) (J := (C.S N).J) hbig
  have huv : u ≠ v := by
    rintro rfl
    exact hfree a₀ ha₀ i₀ hi₀ hhit
  exact norm_localChar_le_of_single C N hppos hu hv huv ha₀ hi₀ hhit hother hfree

/-- **The fully assembled reduction of `IndepCharDecay`.** -/
theorem indepCharDecay_of_separating {q : ℤ} (C : Chain q)
    (a₀ : ℕ → ℕ × ℤ) (i₀ : ℕ → ℕ) (Good : ℕ → Finset ℕ)
    (ha₀ : ∀ N, a₀ N ∈ (C.c N).support)
    (hi₀ : ∀ N, i₀ N ∈ Ico (C.K N) (C.S N).J)
    (hsub : ∀ N, Good N ⊆ (C.S N).small)
    (hsep : ∀ N, ∀ p ∈ Good N, SeparatingAt C N (a₀ N) (i₀ N) p)
    (hdiv : Tendsto (fun N => ∑ p ∈ Good N, siteDefect q ((C.c N) (a₀ N)) (i₀ N) / p)
      atTop atTop) :
    IndepCharDecay C := by
  refine indepCharDecay_of_defect_sum C Good
    (fun N p => siteDefect q ((C.c N) (a₀ N)) (i₀ N) / p) hsub ?_ ?_ hdiv
  · intro N p _
    exact div_nonneg (siteDefect_nonneg _ _ _) (Nat.cast_nonneg p)
  · intro N p hp
    exact norm_localChar_le_of_separating C N (ha₀ N) (hi₀ N) (hsep N p hp)

/-! ### `IndepMomentSmall` by the same local machinery

`|S_N| ≤ #small · ‖c‖₁ 2^{−K}` pointwise (`abs_classSum_le_card`), so every moment of the
independent model is bounded by that power and `IndepMomentSmall` becomes an explicit growth
condition on `M_N` against `#small · ‖c‖₁ 2^{−K}` — the draft's `M_N ≫ V_N`, with no model
computation left. -/

/-- The uniform pointwise bound on the small-prime sum. -/
noncomputable def momentBound {q : ℤ} (C : Chain q) (N : ℕ) : ℝ :=
  ((C.S N).small.card : ℝ) * (l1 (C.c N) / 2 ^ (C.K N))

lemma momentBound_nonneg {q : ℤ} (C : Chain q) (N : ℕ) : 0 ≤ momentBound C N := by
  unfold momentBound
  exact mul_nonneg (Nat.cast_nonneg _) (div_nonneg (l1_nonneg _) (by positivity))

theorem abs_smallSum_le {q : ℤ} (C : Chain q) (N : ℕ) (n : ℤ) :
    |smallSum C N n| ≤ momentBound C N := by
  unfold smallSum momentBound
  refine (abs_classSum_le_card _ _ _ _ _).trans ?_
  have hc : ((activePrimes (C.c N) (C.K N) (C.S N).J (C.S N).small n).card : ℝ)
      ≤ ((C.S N).small.card : ℝ) := by
    have := Finset.card_filter_le (C.S N).small
      (fun p => ∃ a ∈ (C.c N).support, ∃ i ∈ Ico (C.K N) (C.S N).J,
        (p : ℤ) ∣ n + ((i : ℤ) + 1) * a.1 - a.2)
    exact_mod_cast this
  exact mul_le_mul_of_nonneg_right hc (div_nonneg (l1_nonneg _) (by positivity))

/-- Every moment of the independent model is bounded by the pointwise bound to that power. -/
theorem abs_rIndepAvg_pow_le {q : ℤ} (C : Chain q) (N M : ℕ) :
    |rIndepAvg C N (fun x => x ^ M)| ≤ momentBound C N ^ M := by
  have hmod : 0 < modulus C N := modulus_pos C N
  have hcard : (0:ℝ) < ((range (modulus C N)).card : ℝ) := by
    rw [Finset.card_range]; exact_mod_cast hmod
  unfold rIndepAvg ravg
  rw [abs_div, abs_of_pos hcard, div_le_iff₀ hcard]
  calc |∑ r ∈ range (modulus C N), smallSum C N (r : ℤ) ^ M|
      ≤ ∑ r ∈ range (modulus C N), |smallSum C N (r : ℤ) ^ M| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ r ∈ range (modulus C N), momentBound C N ^ M := by
        refine Finset.sum_le_sum (fun r _ => ?_)
        rw [abs_pow]
        exact pow_le_pow_left₀ (abs_nonneg _) (abs_smallSum_le C N _) M
    _ = momentBound C N ^ M * ((range (modulus C N)).card : ℝ) := by
        rw [Finset.sum_const, nsmul_eq_mul]; ring

/-- **`IndepMomentSmall` from an explicit growth condition.** -/
theorem indepMomentSmall_of_growth {q : ℤ} (C : Chain q) (M : ℕ → ℕ)
    (h : Tendsto (fun N => (2 * Real.pi * |(q : ℝ)|) ^ M N / ((M N).factorial : ℝ)
      * momentBound C N ^ M N) atTop (𝓝 0)) :
    IndepMomentSmall C M := by
  refine squeeze_zero_norm (fun N => ?_) h
  have hcoeff : (0:ℝ) ≤ (2 * Real.pi * |(q : ℝ)|) ^ M N / ((M N).factorial : ℝ) := by
    have := Real.pi_pos; positivity
  simp only [Int.cast_abs]
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hcoeff]
  exact mul_le_mul_of_nonneg_left (abs_rIndepAvg_pow_le C N (M N)) hcoeff

end NormalNumbers.PrimeLambert
