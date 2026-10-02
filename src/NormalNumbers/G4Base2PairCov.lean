/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.G4Base2Supply
import NormalNumbers.G4Base2Pair

/-!
# N6 core: bin-pair cross moments from TT 3.1(i) (dyadic)

TT applied once per bin pair at `X_T = 2^{101·2^{mE}} = Y^{101}`, `L = log X_T / C₅`; the union of
the exceptional scales is avoided by `exists_good_x`; each good block is `block_bound` +
`shifted_mean_le` (N5); the sample average is `abs_avg_le_blocks`.
-/

open Finset

namespace NormalNumbers.G4.Base2

lemma dyBase_of_mem {k n : ℕ} (hn : n ∈ Ioc (2 ^ k) (2 ^ (k + 1))) : dyBase n = 2 ^ k := by
  rw [mem_Ioc] at hn
  unfold dyBase
  congr 1
  rw [Nat.log_eq_iff (Or.inr ⟨by norm_num, by omega⟩)]
  constructor <;> omega

lemma abs_re_binInd_le (I : Finset ℕ) (n : ℕ) : |(binInd I n).re| ≤ 1 := by
  unfold binInd; split_ifs <;> simp

/-- **One good block.**  TT's bound `T` and the N5 error `E` at `N = 2^k` give the centred
bin-pair block bound. -/
theorem good_block_bound (I I' : Finset ℕ) (P₀ b₀ k h₁ h₂ : ℕ) (hP₀ : 0 < P₀) (hb : b₀ < P₀)
    (hh : h₁ ≤ 2 ^ k) {T E : ℝ} (hE : 0 ≤ E)
    (hδ : |binDelta I (2 ^ k)| ≤ 3) (hδ' : |binDelta I' (2 ^ k)| ≤ 3)
    (hTT : ‖(((P₀ : ℝ) / ((2 ^ k : ℕ) : ℝ) : ℝ) : ℝ) •
        ∑ n ∈ (Ioc (2 ^ k) (2 * 2 ^ k)).filter (fun n => n % P₀ = b₀ % P₀),
          (binInd I (n + h₁) - ((binDelta I ((2 ^ k : ℕ) : ℝ) : ℝ) : ℂ)) * binInd I' (n + h₂)‖ ≤ T)
    (hN5 : ‖(∑ n ∈ (Ioc (2 ^ k) (2 * 2 ^ k)).filter (fun n => n % P₀ = (b₀ + h₁) % P₀),
          binInd I n) - (((((2 ^ k : ℕ) : ℝ) / P₀) * binDelta I ((2 ^ k : ℕ) : ℝ) : ℝ) : ℂ)‖ ≤ E) :
    |(P₀ : ℝ) / 2 ^ k * blockSum2 (fun n =>
        ((binInd I (n + h₁)).re - binDelta I (dyBase n))
        * ((binInd I' (n + h₂)).re - binDelta I' (dyBase n))) P₀ b₀ k|
      ≤ T + 3 * ((P₀ : ℝ) / 2 ^ k * (E + 2 * h₁ + 6)) := by
  have hcast : ((2 ^ k : ℕ) : ℝ) = (2 : ℝ) ^ k := by push_cast; ring
  rw [hcast] at hTT hN5
  have hbmod : b₀ % P₀ = b₀ := Nat.mod_eq_of_lt hb
  set s := (Ioc (2 ^ k) (2 * 2 ^ k)).filter (fun n => n % P₀ = b₀ % P₀) with hs
  have hblk : blockSum2 (fun n =>
        ((binInd I (n + h₁)).re - binDelta I (dyBase n))
        * ((binInd I' (n + h₂)).re - binDelta I' (dyBase n))) P₀ b₀ k
      = ∑ n ∈ s, ((binInd I (n + h₁)).re - binDelta I (2 ^ k))
          * ((binInd I' (n + h₂)).re - binDelta I' (2 ^ k)) := by
    unfold blockSum2
    rw [hs, hbmod, show 2 * 2 ^ k = 2 ^ (k + 1) by ring]
    refine sum_congr rfl fun n hn => ?_
    dsimp only
    rw [dyBase_of_mem (mem_filter.1 hn).1]
  rw [hblk]
  refine block_bound s (fun n => (binInd I n).re) (fun n => (binInd I' n).re) h₁ h₂ ?_ ?_ hδ'
    (by positivity)
  · have h := norm_TT_eq s (binInd I) (binInd I') (binInd_im I) (binInd_im I')
      (binDelta I (2 ^ k)) ((P₀ : ℝ) / 2 ^ k) h₁ h₂
    rw [h] at hTT
    exact hTT
  · have hsm := shifted_mean_le (fun n => (binInd I n).re) (abs_re_binInd_le I) (2 ^ k) P₀ b₀ h₁
      hP₀ (by positivity) hh (D := 3) hδ (E := E) ?_
    · push_cast at hsm; rw [hs]; norm_num at hsm ⊢; exact hsm
    · have hre : (∑ m ∈ (Ioc (2 ^ k) (2 * 2 ^ k)).filter (fun m => m % P₀ = (b₀ + h₁) % P₀),
          (binInd I m).re) - ((2 ^ k : ℕ) : ℝ) / P₀ * binDelta I (2 ^ k)
          = ((∑ n ∈ (Ioc (2 ^ k) (2 * 2 ^ k)).filter (fun n => n % P₀ = (b₀ + h₁) % P₀),
            binInd I n) - ((((2 : ℝ) ^ k / P₀) * binDelta I (2 ^ k) : ℝ) : ℂ)).re := by
        rw [Complex.sub_re, Complex.re_sum, Complex.ofReal_re]; push_cast; ring
      have him : ((∑ n ∈ (Ioc (2 ^ k) (2 * 2 ^ k)).filter (fun n => n % P₀ = (b₀ + h₁) % P₀),
            binInd I n) - ((((2 : ℝ) ^ k / P₀) * binDelta I (2 ^ k) : ℝ) : ℂ)).im = 0 := by
        rw [Complex.sub_im, Complex.im_sum, Complex.ofReal_im]; simp [binInd_im]
      rw [hre]
      exact (Complex.abs_re_eq_norm.2 him).trans_le hN5

open Filter Topology in
lemma ev_L {c : ℝ} (hc : 0 < c) (A η : ℝ) (hη : 0 < η) {C₅ : ℝ} (hC₅ : 1 ≤ C₅) (X₀ : ℝ) :
    ∀ᶠ L in atTop, 1 ≤ L ∧ A ≤ L ^ c ∧ A * L ^ (-c) < η ∧ A / L < η ∧
      (C₅ * L) ^ ((1 : ℝ) / 10) ≤ C₅ * L / 101 ∧ X₀ ≤ Real.exp (C₅ * L) := by
  have h1 : ∀ᶠ L : ℝ in atTop, 1 ≤ L := eventually_ge_atTop 1
  have h2 : ∀ᶠ L : ℝ in atTop, A ≤ L ^ c := (tendsto_rpow_atTop hc).eventually_ge_atTop A
  have h3 : ∀ᶠ L : ℝ in atTop, A * L ^ (-c) < η := by
    have t : Tendsto (fun L : ℝ => A * L ^ (-c)) atTop (𝓝 0) := by
      simpa using (tendsto_rpow_neg_atTop hc).const_mul A
    exact t.eventually (gt_mem_nhds hη)
  have h4 : ∀ᶠ L : ℝ in atTop, A / L < η := by
    have t : Tendsto (fun L : ℝ => A / L) atTop (𝓝 0) := tendsto_const_nhds.div_atTop tendsto_id
    exact t.eventually (gt_mem_nhds hη)
  have hu : Tendsto (fun L : ℝ => C₅ * L) atTop atTop :=
    tendsto_id.const_mul_atTop (by linarith)
  have h5 : ∀ᶠ L : ℝ in atTop, (C₅ * L) ^ ((1 : ℝ) / 10) ≤ C₅ * L / 101 := by
    have t := ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 9 / 10)).comp hu).eventually_ge_atTop 101
    filter_upwards [t, hu.eventually_gt_atTop 0] with L hL hpos
    simp only [Function.comp] at hL
    have hsplit : C₅ * L = (C₅ * L) ^ ((1 : ℝ) / 10) * (C₅ * L) ^ ((9 : ℝ) / 10) := by
      rw [← Real.rpow_add hpos]; norm_num
    have hp : 0 ≤ (C₅ * L) ^ ((1 : ℝ) / 10) := Real.rpow_nonneg hpos.le _
    rw [le_div_iff₀ (by norm_num)]
    calc (C₅ * L) ^ ((1 : ℝ) / 10) * 101 ≤ (C₅ * L) ^ ((1 : ℝ) / 10) * (C₅ * L) ^ ((9 : ℝ) / 10) :=
          mul_le_mul_of_nonneg_left hL hp
      _ = C₅ * L := hsplit.symm
  have h6 : ∀ᶠ L : ℝ in atTop, X₀ ≤ Real.exp (C₅ * L) :=
    (Real.tendsto_exp_atTop.comp hu).eventually_ge_atTop X₀
  filter_upwards [h1, h2, h3, h4, h5, h6] with L a b c d e f
  exact ⟨a, b, c, d, e, f⟩

lemma log_two_pow (a : ℕ) : Real.log ((2 : ℝ) ^ a) = a * Real.log 2 := by
  rw [Real.log_pow]

lemma two_pow_rpow_div (m : ℕ) :
    ((2 : ℝ) ^ (101 * 2 ^ m)) ^ ((1 : ℝ) / 101) = (2 : ℝ) ^ (2 ^ m) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), ← Real.rpow_natCast]
  congr 1; push_cast; ring

lemma two_pow_rpow_le {a j : ℕ} {t : ℝ} (ht : 0 ≤ t) (h : t * a ≤ j) :
    ((2 : ℝ) ^ a) ^ t ≤ (2 : ℝ) ^ j := by
  rw [← Real.rpow_natCast 2 a, ← Real.rpow_mul (by norm_num), ← Real.rpow_natCast 2 j]
  exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)

lemma mem_dyadicScales_two_pow {a j : ℕ} (h1 : a ≤ 2 * j) (h2 : j + 1 ≤ a) :
    j ∈ CastingOut.dyadicScales ((2 : ℝ) ^ a) := by
  unfold CastingOut.dyadicScales
  rw [mem_filter, mem_range]
  have hlog : Real.logb 2 ((2 : ℝ) ^ a) = a := by
    rw [← Real.rpow_natCast, Real.logb_rpow (by norm_num) (by norm_num)]
  refine ⟨?_, ?_, ?_⟩
  · rw [hlog, Nat.ceil_natCast]; omega
  · rw [Real.sqrt_le_left (by positivity)]
    rw [← pow_mul]
    exact pow_le_pow_right₀ (by norm_num) (by omega)
  · exact pow_le_pow_right₀ (by norm_num) h2

lemma card_dyadicScales_two_pow (a : ℕ) :
    (CastingOut.dyadicScales ((2 : ℝ) ^ a)).card ≤ a + 1 := by
  unfold CastingOut.dyadicScales
  have hlog : Real.logb 2 ((2 : ℝ) ^ a) = a := by
    rw [← Real.rpow_natCast, Real.logb_rpow (by norm_num) (by norm_num)]
  refine (card_filter_le _ _).trans ?_
  rw [card_range, hlog, Nat.ceil_natCast]

/-- **N6 core.**  From TT 3.1(i) (dyadic) and N5 (`binInd_ap_mean`).  75%. -/
theorem binPair_cov (htt : CastingOut.TTEquidistributedDyadic) (K N : ℕ) (hK : 1 ≤ K)
    {ε₂ : ℝ} (hε : 0 < ε₂) (Bmax : ℕ) : ∃ e₀ : ℕ, ∀ e, e₀ ≤ e → ∀ B ≤ Bmax,
      ∀ bins : Fin B → Finset ℕ, (∀ ℓ, ∀ p ∈ bins ℓ, p.Prime ∧ SchedB.YE K e < p) → (∀ ℓ, mass (bins ℓ) ≤ 1) →
      ∃ x : ℕ, 100 * 2 ^ SchedB.mE K e ≤ x ∧ x ≤ 101 * 2 ^ SchedB.mE K e ∧
        ∀ ℓ ℓ' : Fin B, ∀ i j : (gridOf K N hK).Idx, i ≠ j →
          |((apSample (2 ^ x) (gridOf K N hK).P₀ (gridOf K N hK).b₀).card : ℝ)⁻¹ *
            ∑ n ∈ apSample (2 ^ x) (gridOf K N hK).P₀ (gridOf K N hK).b₀,
              ((binInd (bins ℓ) (n + shiftAL (gridOf K N hK).B (gridOf K N hK).Q
                  (gridOf K N hK).D₀ i)).re - binDelta (bins ℓ) (dyBase n))
              * ((binInd (bins ℓ') (n + shiftAL (gridOf K N hK).B (gridOf K N hK).Q
                  (gridOf K N hK).D₀ j)).re - binDelta (bins ℓ') (dyBase n))| ≤ ε₂ := by
  classical
  obtain ⟨c, Cst, hc, hCst, hTT⟩ := htt
  obtain ⟨C₅', X₀, hC₅', h5⟩ := binInd_ap_mean
  set C₅ : ℝ := max C₅' 1 with hC₅def
  have hC₅1 : 1 ≤ C₅ := le_max_right _ _
  have hC₅C : C₅' ≤ C₅ := le_max_left _ _
  set G := gridOf K N hK with hG
  set P₀ : ℕ := G.P₀ with hP₀def
  have hP₀ : 0 < P₀ := G.P₀_pos
  have hb₀ : G.b₀ < P₀ := G.b₀_lt_P₀
  set Hs : ℕ := (K + N) * gridDm K N with hHs
  have hρle : ∀ i : G.Idx, shiftAL G.B G.Q G.D₀ i ≤ Hs := fun i => gridOf.shiftAL_le hK i
  set η : ℝ := ε₂ / 6 with hη
  have hη0 : 0 < η := by positivity
  obtain ⟨J₀, hJ₀⟩ := exists_pow_lt_of_lt_one (show 0 < ε₂ / 96 by positivity)
    (show (1 / 2 : ℝ) < 1 by norm_num)
  -- asymptotics in `L`
  have hevL : ∀ᶠ L : ℝ in Filter.atTop,
      (1 ≤ L ∧ ((P₀ + Hs : ℕ) : ℝ) ≤ L ^ c ∧ ((P₀ + Hs : ℕ) : ℝ) * L ^ (-c) < η ∧
        ((P₀ + Hs : ℕ) : ℝ) / L < η ∧ (C₅ * L) ^ ((1 : ℝ) / 10) ≤ C₅ * L / 101 ∧
        X₀ ≤ Real.exp (C₅ * L)) ∧
      (1 ≤ L ∧ (J₀ * Bmax ^ 2 * Cst * 102 + 1 : ℝ) ≤ L ^ c ∧
        (J₀ * Bmax ^ 2 * Cst * 102 + 1 : ℝ) * L ^ (-c) < 1 ∧
        (J₀ * Bmax ^ 2 * Cst * 102 + 1 : ℝ) / L < 1 ∧ (C₅ * L) ^ ((1 : ℝ) / 10) ≤ C₅ * L / 101 ∧
        X₀ ≤ Real.exp (C₅ * L)) ∧
      (1 ≤ L ∧ (Cst + 3 * P₀ : ℝ) ≤ L ^ c ∧ (Cst + 3 * P₀ : ℝ) * L ^ (-c) < η / 4 ∧
        (Cst + 3 * P₀ : ℝ) / L < η / 4 ∧ (C₅ * L) ^ ((1 : ℝ) / 10) ≤ C₅ * L / 101 ∧
        X₀ ≤ Real.exp (C₅ * L)) :=
    (ev_L hc _ η hη0 hC₅1 X₀).and ((ev_L hc _ 1 one_pos hC₅1 X₀).and
      (ev_L hc _ (η / 4) (by positivity) hC₅1 X₀))
  have hLm : Filter.Tendsto (fun m : ℕ => (101 * 2 ^ m * Real.log 2) / C₅) Filter.atTop
      Filter.atTop := by
    have h2 : Filter.Tendsto (fun m : ℕ => (2 : ℝ) ^ m) Filter.atTop Filter.atTop :=
      tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
    have hl : (0 : ℝ) < 101 * Real.log 2 / C₅ := by
      have := Real.log_pos (show (1 : ℝ) < 2 by norm_num); positivity
    refine (h2.const_mul_atTop hl).congr fun m => ?_
    ring
  obtain ⟨m₀, hm₀⟩ := Filter.eventually_atTop.1 (hLm.eventually hevL)
  set Z : ℕ := J₀ + Hs + 2 * P₀ + ⌈12 * P₀ * (2 * Hs + 6) / η⌉₊ + ⌈288 * P₀ / ε₂⌉₊ + 1 with hZ
  refine ⟨m₀ + Z, fun e he B hB bins hbins hmass => ?_⟩
  set m := SchedB.mE K e with hm
  have hme : e ≤ m := by rw [hm]; unfold SchedB.mE; omega
  have hm2 : m < 2 ^ m := Nat.lt_two_pow_self
  have hmZ : Z ≤ 2 ^ m := by omega
  obtain ⟨⟨hL1, hPL, -, hPL', hsm, hX₀⟩, ⟨-, -, hJL, -, -, -⟩, ⟨-, -, hCL, hCL', -, -⟩⟩ :=
    hm₀ m (by omega)
  set L : ℝ := 101 * 2 ^ m * Real.log 2 / C₅ with hL
  set a : ℕ := 101 * 2 ^ m with ha
  set XT : ℝ := (2 : ℝ) ^ a with hXT
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogXT : Real.log XT = C₅ * L := by
    rw [hXT, log_two_pow, hL, ha]; push_cast; field_simp
  have hLpos : 0 < L := by linarith
  have hYreal : ((SchedB.YE K e : ℕ) : ℝ) = (2 : ℝ) ^ (2 ^ m) := by
    unfold SchedB.YE; push_cast; rfl
  have hXT2 : (2 : ℝ) ≤ XT := by
    rw [hXT]
    calc (2 : ℝ) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ a := pow_le_pow_right₀ (by norm_num) (by rw [ha]; have := Nat.one_le_two_pow (n := m); omega)
  have hX₀XT : X₀ ≤ XT := by
    rw [← Real.exp_log (show 0 < XT by positivity), hlogXT]; exact hX₀
  have hXTY : XT ^ ((1 : ℝ) / 101) ≤ ((SchedB.YE K e : ℕ) : ℝ) := by
    rw [hYreal, hXT, ha, two_pow_rpow_div]
  have hbinsR : ∀ ℓ, ∀ p ∈ bins ℓ, p.Prime ∧ ((SchedB.YE K e : ℕ) : ℝ) < p := fun ℓ p hp =>
    ⟨(hbins ℓ p hp).1, by exact_mod_cast (hbins ℓ p hp).2⟩
  -- TT's hypothesis (3.1) for each bin, with `L`
  have h31 : ∀ ℓ, ∀ N' : ℝ, XT ^ (0.4 : ℝ) ≤ N' → N' ≤ XT → ∀ a' q : ℕ, 1 ≤ q →
      ‖(∑ n ∈ (Ioc ⌊N'⌋₊ ⌊2 * N'⌋₊).filter (fun n => n % q = a' % q), binInd (bins ℓ) n)
          - (((N' / q) * binDelta (bins ℓ) N' : ℝ) : ℂ)‖ ≤ N' / L := by
    intro ℓ N' hN1 hN2 a' q hq
    refine (h5 XT hX₀XT _ hXTY (bins ℓ) (hbinsR ℓ) N' hN1 hN2 a' q hq).trans ?_
    have hN0 : 0 ≤ N' := le_trans (Real.rpow_nonneg (by positivity) _) hN1
    rw [hlogXT]
    refine div_le_div_of_nonneg_left hN0 hLpos ?_
    rw [le_div_iff₀ hC₅']
    nlinarith
  -- small primes: `g_ℓ(p) = 1`
  have hsmall : ∀ ℓ, ∀ p : ℕ, p.Prime → Real.exp (Real.log XT ^ ((1 : ℝ) / 11)) ≤ p →
      (p : ℝ) ≤ Real.exp (Real.log XT ^ ((1 : ℝ) / 10)) → binInd (bins ℓ) p = 1 := by
    intro ℓ p hp _ hp2
    have hpY : (p : ℝ) ≤ ((SchedB.YE K e : ℕ) : ℝ) := by
      refine hp2.trans ?_
      rw [hlogXT, hYreal]
      have : C₅ * L / 101 = 2 ^ m * Real.log 2 := by rw [hL]; field_simp
      calc Real.exp ((C₅ * L) ^ ((1 : ℝ) / 10)) ≤ Real.exp (C₅ * L / 101) :=
            Real.exp_le_exp.2 hsm
        _ = (2 : ℝ) ^ (2 ^ m) := by
            rw [this]
            have h := log_two_pow (2 ^ m)
            push_cast at h
            rw [← h, Real.exp_log (by positivity)]
    unfold binInd
    rw [if_neg]
    rintro ⟨q, hq, hqp⟩
    have hq' := hbinsR ℓ q hq
    have : q = p := (Nat.prime_dvd_prime_iff_eq hq'.1 hp).1 hqp
    subst this
    linarith [hq'.2]
  -- TT, once per bin pair
  have hE : ∀ pr : Fin B × Fin B, ∃ E : Finset ℕ, E ⊆ CastingOut.dyadicScales XT ∧
      (E.card : ℝ) ≤ Cst * L ^ (-c) * ((CastingOut.dyadicScales XT).card : ℝ) ∧
      ∀ j ∈ CastingOut.dyadicScales XT, j ∉ E →
        ∀ N' : ℕ, (2 : ℝ) ^ j ≤ (N' : ℝ) → (N' : ℝ) < 2 ^ (j + 1) →
          ∀ W b h₁ h₂ : ℕ, 0 < W → (W : ℝ) ≤ L ^ c →
            (h₁ : ℝ) ≤ L ^ c → (h₂ : ℝ) ≤ L ^ c → h₁ ≠ h₂ →
            ‖((W : ℝ) / (N' : ℝ) : ℝ) •
                ∑ n ∈ (Finset.Ioc N' (2 * N')).filter (fun n => n % W = b % W),
                  (binInd (bins pr.1) (n + h₁) - ((binDelta (bins pr.1) (N' : ℝ) : ℝ) : ℂ))
                    * binInd (bins pr.2) (n + h₂)‖
              ≤ Cst * L ^ (-c) := fun pr =>
    hTT (binInd (bins pr.1)) (binInd (bins pr.2))
      (binInd_isCoprimeMultiplicative _ fun p hp => (hbins pr.1 p hp).1)
      (binInd_isCoprimeMultiplicative _ fun p hp => (hbins pr.2 p hp).1)
      (norm_binInd_le _) (norm_binInd_le _) (binInd_im _) XT L hXT2 hL1
      (by rw [hlogXT]; nlinarith) (binDelta (bins pr.1)) (h31 pr.1) (hsmall pr.1)
  choose Ef hEsub hEcard hEgood using hE
  set U := univ.biUnion Ef with hU
  sorry

end NormalNumbers.G4.Base2
