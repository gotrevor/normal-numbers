import NormalNumbers.TwoPointKataiAssemble

/-!
# The Kátai step as a THEOREM: C1 from Delange plus one open leaf

`katai_master` (lap 10) is the Kátai/BSZ inequality, proved in kernel.  `KataiQuantSharp`
(lap 4) was a *hypothesis* of the same shape, carried through `TwoPointHonestChain` as an
assumption.  This file removes that assumption: it normalises `katai_master` into the mean
form and derives the whole swing from it, so the only remaining input beyond Delange is an
honest open leaf about the truncated pair Gram sum.

The normalisation.  Write `L = L(w)`, `G = kataiPairGram a w N`, `A = ‖E_{n<N} f(n)a(n)‖`.
Dividing `katai_master` by `N·L` and using `L ≥ 1/2`, `L ≤ N`, `N ≥ w² ≥ 4`:

    A  ≤  8√2 · L^{-1/2}  +  √2 · √( G / (N L²) ) ,    hence
    A² ≤  256 · ( 1/L  +  G / (N L²) ) .

So the honest leaf is `G(w(N), N) = o(N · L(w(N))²)` along a slowly growing cutoff: the
truncated Gram mass must be `o` of the diagonal mass squared over `L`.  Everything else in the
chain is kernel-checked.
-/

open Finset Filter Topology

namespace NormalNumbers.CastingOut

lemma kataiPairGram_nonneg (a : ℕ → ℂ) (w N : ℕ) : 0 ≤ kataiPairGram a w N := by
  refine Finset.sum_nonneg fun p _ => Finset.sum_nonneg fun q _ => ?_
  split
  · exact le_rfl
  · exact norm_nonneg _

lemma primesLe_subset_Icc (w : ℕ) : primesLe w ⊆ Finset.Icc 2 w := by
  intro p hp
  have hprime := prime_of_mem_primesLe hp
  have hmem : p ∈ Finset.range (w + 1) := (Finset.mem_filter.mp hp).1
  simp only [Finset.mem_range] at hmem
  exact Finset.mem_Icc.mpr ⟨hprime.two_le, by omega⟩

lemma card_primesLe_le (w : ℕ) : (primesLe w).card ≤ w - 1 := by
  have := Finset.card_le_card (primesLe_subset_Icc w)
  simpa using this

/-- `L(w) ≥ 1/2` for `w ≥ 2` (the prime `2` alone). -/
lemma kataiPrimeRecip_ge_half {w : ℕ} (hw : 2 ≤ w) : (1 : ℝ) / 2 ≤ kataiPrimeRecip w := by
  have h2 : (2 : ℕ) ∈ primesLe w :=
    Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), Nat.prime_two⟩
  have hnn : ∀ p ∈ primesLe w, (0 : ℝ) ≤ 1 / p := fun p _ => by positivity
  calc (1 : ℝ) / 2 = (1 : ℝ) / ((2 : ℕ) : ℝ) := by norm_num
    _ ≤ _ := Finset.single_le_sum hnn h2

/-- `L(w) ≤ w`: crude, but enough. -/
lemma kataiPrimeRecip_le_self (w : ℕ) : kataiPrimeRecip w ≤ (w : ℝ) := by
  have hterm : ∀ p ∈ primesLe w, (1 : ℝ) / p ≤ 1 / 2 := by
    intro p hp
    have := (prime_of_mem_primesLe hp).two_le
    have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast this
    exact one_div_le_one_div_of_le (by norm_num) hp2
  calc kataiPrimeRecip w ≤ ∑ _p ∈ primesLe w, (1 : ℝ) / 2 := Finset.sum_le_sum hterm
    _ = ((primesLe w).card : ℝ) / 2 := by rw [Finset.sum_const]; ring
    _ ≤ ((w : ℝ)) / 2 := by
        have : ((primesLe w).card : ℝ) ≤ (w : ℝ) := by
          have := card_primesLe_le w
          have : (primesLe w).card ≤ w := le_trans this (Nat.sub_le _ _)
          exact_mod_cast this
        linarith
    _ ≤ (w : ℝ) := by
        have : (0 : ℝ) ≤ (w : ℝ) := Nat.cast_nonneg w
        linarith



/-! ### The normalisation: from `katai_master` to a mean-square bound -/

lemma range_eq_insert_Ioc (N : ℕ) : Finset.range (N + 1) = insert 0 (Finset.Ioc 0 N) := by
  ext m
  simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Ioc]
  omega

lemma norm_sum_range_le (g : ℕ → ℂ) (N : ℕ) (hg : ∀ n, ‖g n‖ ≤ 1) :
    ‖∑ n ∈ Finset.range N, g n‖ ≤ ‖∑ n ∈ Finset.Ioc 0 N, g n‖ + 2 := by
  classical
  have hins : ∑ n ∈ Finset.range (N + 1), g n = g 0 + ∑ n ∈ Finset.Ioc 0 N, g n := by
    rw [range_eq_insert_Ioc, Finset.sum_insert (by simp)]
  have hsucc : ∑ n ∈ Finset.range (N + 1), g n = ∑ n ∈ Finset.range N, g n + g N :=
    Finset.sum_range_succ g N
  have hEq : ∑ n ∈ Finset.range N, g n = g 0 + ∑ n ∈ Finset.Ioc 0 N, g n - g N := by
    rw [← hins, hsucc]; ring
  rw [hEq]
  calc ‖g 0 + ∑ n ∈ Finset.Ioc 0 N, g n - g N‖
      ≤ ‖g 0 + ∑ n ∈ Finset.Ioc 0 N, g n‖ + ‖g N‖ := norm_sub_le _ _
    _ ≤ ‖g 0‖ + ‖∑ n ∈ Finset.Ioc 0 N, g n‖ + ‖g N‖ := by
        linarith [norm_add_le (g 0) (∑ n ∈ Finset.Ioc 0 N, g n)]
    _ ≤ _ := by linarith [hg 0, hg N]

/-- The purely real normalisation step: from the shape `katai_master` produces to a
mean-square bound.  Stated on plain reals so the arithmetic is atom-clean. -/
lemma katai_normalise (A NN L G : ℝ) (hA : 0 ≤ A) (hL : (1:ℝ)/2 ≤ L) (hNN : (4:ℝ) ≤ NN)
    (hLN : L ≤ NN) (hG : 0 ≤ G)
    (hmaster : L * (A * NN) ≤ Real.sqrt ((NN + 1) * (NN * L + G)) + 2 * NN
        + NN * Real.sqrt (2 * L) + 2 * L) :
    A ^ 2 ≤ 256 * (1 / L + G / (NN * L ^ 2)) := by
  have hLpos : 0 < L := by linarith
  have hNpos : 0 < NN := by linarith
  set s := Real.sqrt L with hsdef
  set r := Real.sqrt NN with hrdef
  set g := Real.sqrt G with hgdef
  have hs2 : s ^ 2 = L := Real.sq_sqrt hLpos.le
  have hr2 : r ^ 2 = NN := Real.sq_sqrt hNpos.le
  have hg2 : g ^ 2 = G := Real.sq_sqrt hG
  have hspos : 0 < s := Real.sqrt_pos.mpr hLpos
  have hrpos : 0 < r := Real.sqrt_pos.mpr hNpos
  have hgnn : 0 ≤ g := Real.sqrt_nonneg _
  clear_value s r g
  clear hsdef hrdef hgdef
  have hroot2 : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hroot2pos : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hsge : (1:ℝ) ≤ Real.sqrt 2 * s := by nlinarith [hs2, hroot2, hL, hspos, hroot2pos]
  have hsr : s ^ 2 ≤ r ^ 2 := by rw [hs2, hr2]; exact hLN
  have h2L : Real.sqrt (2 * L) = Real.sqrt 2 * s := by
    rw [← hs2, Real.sqrt_mul (by norm_num), Real.sqrt_sq hspos.le]
  have hbig : Real.sqrt ((NN + 1) * (NN * L + G)) ≤ NN * (Real.sqrt 2 * s) + Real.sqrt 2 * r * g := by
    have hrhsnn : 0 ≤ NN * (Real.sqrt 2 * s) + Real.sqrt 2 * r * g := by positivity
    have ha2 : (NN * (Real.sqrt 2 * s)) ^ 2 = 2 * NN ^ 2 * L := by
      rw [mul_pow, mul_pow, hroot2, hs2]; ring
    have hb2 : (Real.sqrt 2 * r * g) ^ 2 = 2 * NN * G := by
      rw [mul_pow, mul_pow, hroot2, hr2, hg2]
    have hcross : 0 ≤ 2 * (NN * (Real.sqrt 2 * s)) * (Real.sqrt 2 * r * g) := by positivity
    have hle : (NN + 1) * (NN * L + G) ≤ (NN * (Real.sqrt 2 * s) + Real.sqrt 2 * r * g) ^ 2 := by
      have hexp : (NN * (Real.sqrt 2 * s) + Real.sqrt 2 * r * g) ^ 2
          = 2 * NN ^ 2 * L + 2 * NN * G
            + 2 * (NN * (Real.sqrt 2 * s)) * (Real.sqrt 2 * r * g) := by
        rw [add_sq, ha2, hb2]; ring
      rw [hexp]
      nlinarith [hNN, hG, hLpos]
    calc Real.sqrt ((NN + 1) * (NN * L + G))
        ≤ Real.sqrt ((NN * (Real.sqrt 2 * s) + Real.sqrt 2 * r * g) ^ 2) := Real.sqrt_le_sqrt hle
      _ = _ := Real.sqrt_sq hrhsnn
  rw [h2L] at hmaster
  set c := Real.sqrt 2 * s with hcdef
  have hcpos : 0 < c := mul_pos hroot2pos hspos
  have h3 : L * (A * NN) ≤ NN * c + Real.sqrt 2 * r * g + 2 * NN + NN * c + 2 * L := by
    linarith [hbig]
  rw [← hs2, ← hr2] at h3
  have haux : 2 * r ^ 2 + 2 * s ^ 2 ≤ 6 * c * r ^ 2 := by
    nlinarith [hsge, hsr, hrpos, hcpos]
  have hkey : A * (s ^ 2 * r ^ 2) ≤ 8 * c * r ^ 2 + Real.sqrt 2 * r * g := by
    nlinarith [h3, haux]
  have hden : (0 : ℝ) < s ^ 2 * r ^ 2 := by positivity
  have hAle : A ≤ 8 * Real.sqrt 2 * (1 / s) + Real.sqrt 2 * (g / (r * s ^ 2)) := by
    have hrw : 8 * Real.sqrt 2 * (1 / s) + Real.sqrt 2 * (g / (r * s ^ 2))
        = (8 * c * r ^ 2 + Real.sqrt 2 * r * g) / (s ^ 2 * r ^ 2) := by
      rw [hcdef]; field_simp
    rw [hrw, le_div_iff₀ hden]
    exact hkey
  have hu : (1 / s) ^ 2 = 1 / L := by rw [div_pow, one_pow, hs2]
  have hv : (g / (r * s ^ 2)) ^ 2 = G / (NN * L ^ 2) := by
    rw [div_pow, mul_pow, hg2, hr2, hs2]
  have hunn : (0 : ℝ) ≤ 1 / s := by positivity
  have hvnn : (0 : ℝ) ≤ g / (r * s ^ 2) := by positivity
  have hsq : A ^ 2 ≤ 256 * ((1 / s) ^ 2 + (g / (r * s ^ 2)) ^ 2) := by
    nlinarith [hAle, hA, hunn, hvnn, hroot2, hroot2pos,
      sq_nonneg (1 / s - g / (r * s ^ 2))]
  rw [hu, hv] at hsq
  exact hsq

/-- **THE KÁTAI STEP, IN MEAN-SQUARE FORM — A THEOREM, NOT A HYPOTHESIS.**

    ‖E_{n<N} f(n) a(n)‖² ≤ 256 · ( 1/L(w) + kataiPairGram a w N / (N · L(w)²) ).

Compare `KataiQuantSharp`, which assumes exactly this shape with the full-range `pairSum` in
place of the truncated Gram sum.  Here nothing is assumed. -/
theorem katai_mean_sq (a f : ℕ → ℂ) (ha : ∀ n, ‖a n‖ ≤ 1) (hf : ∀ n, ‖f n‖ ≤ 1)
    (hmul : ∀ m n : ℕ, Nat.Coprime m n → f (m * n) = f m * f n)
    (w N : ℕ) (hw : 2 ≤ w) (hN : ((w : ℝ)) ^ 2 ≤ (N : ℝ)) :
    ‖fullMean (fun n => f n * a n) N‖ ^ 2
      ≤ 256 * (1 / kataiPrimeRecip w
          + kataiPairGram a w N / ((N : ℝ) * (kataiPrimeRecip w) ^ 2)) := by
  classical
  set L := kataiPrimeRecip w with hLdef
  set G := kataiPairGram a w N with hGdef
  have hGnn : 0 ≤ G := kataiPairGram_nonneg a w N
  have hL2 : (1 : ℝ) / 2 ≤ L := kataiPrimeRecip_ge_half hw
  have hLpos : 0 < L := by linarith
  have hwN : w ^ 2 ≤ N := by exact_mod_cast hN
  have hNpos : 0 < N := by nlinarith [hwN, hw]
  have hNR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hNpos
  have hN4 : (4 : ℝ) ≤ (N : ℝ) := by
    have : (4 : ℕ) ≤ N := le_trans (by nlinarith) hwN
    exact_mod_cast this
  have hLw : L ≤ (w : ℝ) := kataiPrimeRecip_le_self w
  have hwR : (1 : ℝ) ≤ (w : ℝ) := by exact_mod_cast (by omega : 1 ≤ w)
  have hLN : L ≤ (N : ℝ) := by nlinarith [hLw, hN, hwR]
  have hcard : 2 * (primesLe w).card ≤ N := by
    have h1 := card_primesLe_le w
    have : 2 * (w - 1) ≤ w ^ 2 := by
      have hw1 : w - 1 ≤ w := Nat.sub_le _ _
      nlinarith [hw, hw1]
    omega
  have hmaster := katai_master w N a f ha hf hmul hcard
  rw [← hLdef, ← hGdef] at hmaster
  have hgnorm : ∀ n, ‖f n * a n‖ ≤ 1 := by
    intro n
    rw [norm_mul]
    nlinarith [hf n, ha n, norm_nonneg (f n), norm_nonneg (a n)]
  have hMS := norm_sum_range_le (fun n => f n * a n) N hgnorm
  set A := ‖fullMean (fun n => f n * a n) N‖ with hAdef
  have hAnn : 0 ≤ A := norm_nonneg _
  have hAN : A * (N : ℝ) = ‖∑ n ∈ Finset.range N, f n * a n‖ := by
    rw [hAdef, fullMean, norm_div, Complex.norm_natCast]
    field_simp
  have hfinal : L * (A * (N : ℝ)) ≤ Real.sqrt (((N : ℝ) + 1) * ((N : ℝ) * L + G))
      + 2 * (N : ℝ) + (N : ℝ) * Real.sqrt (2 * L) + 2 * L := by
    rw [hAN]
    have h1 : L * ‖∑ n ∈ Finset.range N, f n * a n‖
        ≤ L * (‖∑ n ∈ Finset.Ioc 0 N, f n * a n‖ + 2) :=
      mul_le_mul_of_nonneg_left hMS hLpos.le
    nlinarith [hmaster, hLpos, h1]
  exact katai_normalise A (N : ℝ) L G hAnn hL2 hN4 hLN hGnn hfinal

/-! ### The swing, with the Kátai step no longer a hypothesis -/

/-- **THE REMAINING OPEN LEAF.**  Along a slowly growing cutoff `w(N)`, the truncated pair
Gram mass is `o(N · L(w(N))²)`.  This is exactly what the kernel-checked Kátai inequality
consumes — no more, no less. -/
def PairGramSmallGrowing (a : ℕ → ℂ) : Prop :=
  ∃ w : ℕ → ℕ, Tendsto w atTop atTop ∧
    (∀ᶠ N : ℕ in atTop, 2 ≤ w N ∧ ((w N : ℝ)) ^ 2 ≤ (N : ℝ)) ∧
    Tendsto (fun N => kataiPairGram a (w N) N / ((N : ℝ) * (kataiPrimeRecip (w N)) ^ 2))
      atTop (𝓝 0)

/-- The swing, now resting on a theorem rather than on `KataiQuantSharp`. -/
theorem tendsto_fullMean_of_gram (a f : ℕ → ℂ)
    (ha : ∀ n, ‖a n‖ ≤ 1) (hf : ∀ n, ‖f n‖ ≤ 1)
    (hmul : ∀ m n : ℕ, Nat.Coprime m n → f (m * n) = f m * f n)
    (hP : PairGramSmallGrowing a) :
    Tendsto (fun N => fullMean (fun n => f n * a n) N) atTop (𝓝 0) := by
  obtain ⟨w, hw, hslow, hpair⟩ := hP
  set M : ℕ → ℂ := fun N => fullMean (fun n => f n * a n) N with hM
  have hL : Tendsto (fun N => 1 / kataiPrimeRecip (w N)) atTop (𝓝 0) := by
    simpa [Pi.inv_def] using (tendsto_kataiPrimeRecip.comp hw).inv_tendsto_atTop
  have hmaj : Tendsto (fun N => 256 * (1 / kataiPrimeRecip (w N)
      + kataiPairGram a (w N) N / ((N : ℝ) * (kataiPrimeRecip (w N)) ^ 2))) atTop (𝓝 0) := by
    simpa using (hL.add hpair).const_mul (256 : ℝ)
  have hsq : Tendsto (fun N => ‖M N‖ ^ 2) atTop (𝓝 0) := by
    refine squeeze_zero' (Filter.Eventually.of_forall fun N => by positivity) ?_ hmaj
    filter_upwards [hslow] with N hN
    exact katai_mean_sq a f ha hf hmul (w N) N hN.1 hN.2
  have hs : Tendsto (fun N => Real.sqrt (‖M N‖ ^ 2)) atTop (𝓝 0) := by simpa using hsq.sqrt
  rw [tendsto_zero_iff_norm_tendsto_zero]
  exact hs.congr fun N => Real.sqrt_sq (norm_nonneg _)

/-- The two-point instance of the leaf. -/
def TwoPointPairGramSmall (b : ℕ) (t : ℝ) : Prop :=
  PairGramSmallGrowing (fun n => phase (t * omegaTail b n))

theorem shiftIndep_of_pairGramSmall (b : ℕ) (t : ℝ)
    (hD : DelangeMean t) (hP : TwoPointPairGramSmall b t) : ShiftIndep b t := by
  set a : ℕ → ℂ := fun n => phase (t * omegaTail b n) with ha
  set f : ℕ → ℂ := fun n => phase (t * (omegaNat n : ℝ)) with hf
  have hanorm : ∀ n, ‖a n‖ ≤ 1 := fun n => le_of_eq (norm_phase _)
  have hfnorm : ∀ n, ‖f n‖ ≤ 1 := fun n => le_of_eq (norm_phase _)
  have hmul : ∀ m n : ℕ, Nat.Coprime m n → f (m * n) = f m * f n := fun m n h =>
    phase_omegaNat_multiplicative t m n h
  have hDKc : Tendsto (fun N => fullMean (fun n => f n * a n) N) atTop (𝓝 0) :=
    tendsto_fullMean_of_gram a f hanorm hfnorm hmul hP
  have hshift : Tendsto (fun N => fullMean (fun n => f (n + 1) * a (n + 1)) N) atTop (𝓝 0) :=
    tendsto_fullMean_shift (g := fun n => f n * a n)
      (fun n => by rw [norm_mul]; nlinarith [hfnorm n, hanorm n, norm_nonneg (f n),
        norm_nonneg (a n)]) hDKc
  set A : ℕ → ℂ := fun n => phase (t * (omegaNat (n + 1) : ℝ)) with hA
  set B : ℕ → ℂ := fun n => phase (t * omegaTail b (n + 1)) with hB
  have hBnorm : ∀ N, ‖fullMean B N‖ ≤ 1 := fun N =>
    norm_fullMean_le_one B N (fun m => le_of_eq (norm_phase _))
  have hprod : Tendsto (fun N => (fullMean A N) * (fullMean B N)) atTop (𝓝 0) := by
    rw [NormedAddGroup.tendsto_nhds_zero]
    intro ε hε
    filter_upwards [(NormedAddGroup.tendsto_nhds_zero.mp hD) ε hε] with N hN
    calc ‖(fullMean A N) * (fullMean B N)‖ = ‖fullMean A N‖ * ‖fullMean B N‖ := norm_mul _ _
      _ ≤ ‖fullMean A N‖ * 1 := by
          nlinarith [hBnorm N, norm_nonneg (fullMean A N), norm_nonneg (fullMean B N)]
      _ = ‖fullMean A N‖ := by ring
      _ < ε := hN
  have hfin := hshift.sub hprod
  rw [sub_zero] at hfin
  exact hfin

/-- **C1 FROM DELANGE PLUS ONE LEAF.**  The Kátai/BSZ step is no longer assumed anywhere:
`katai_master` and `katai_mean_sq` are theorems.  What remains open is `TwoPointPairGramSmall`
alone. -/
theorem conjC1_of_delange_pairGramSmall
    (hD : ∀ b : ℕ, 3 ≤ b → ∀ m : ℤ, m ≠ 0 → ¬ ((b : ℤ) ∣ m) → DelangeMean (((m : ℤ) : ℝ) / b))
    (hP : ∀ b : ℕ, 3 ≤ b → ∀ m : ℤ, m ≠ 0 → ¬ ((b : ℤ) ∣ m) →
      TwoPointPairGramSmall b (((m : ℤ) : ℝ) / b)) :
    ConjC1 :=
  conjC1_of_weylMean fun b hb m hm hdvd =>
    weylMean_tendsto_zero_of b (by omega) ((m : ℤ) : ℝ) (hD b hb m hm hdvd)
      (shiftIndep_of_pairGramSmall b (((m : ℤ) : ℝ) / b) (hD b hb m hm hdvd) (hP b hb m hm hdvd))

end NormalNumbers.CastingOut
