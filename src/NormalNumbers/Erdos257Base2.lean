/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.LiteratureTTEquidistributed
import NormalNumbers.LiteratureTTEquidistributedDefect
import NormalNumbers.G4VeryLargeCov
import NormalNumbers.G4SubsetWitnessCov
import NormalNumbers.G4Base2Cov
import NormalNumbers.G4Base2PairCov
import NormalNumbers.G4Base2Sched

/-!
# Erdős #257 at base 2 for prime subsets (campaign launched 2026-10-02)

The base-`≥ 3` theorem `G4.isDisjunctive_subsetLambert` fails at `b = 2` exactly at the
very-large-prime step: the frame bounds the primes above `Y` pointwise, and `rowL1 2 K = 1`
(`rowL1_two`, `one_le_rowMass_two`).  Tao–Teräväinen's irrationality of `Σ ω(n)/2ⁿ` needs the same
input and get it from a two-point correlation estimate, their Theorem 3.1(i), applied to "avoids
every prime in bin `ℓ`" indicators.  Those stay equidistributed when the bins are cut down to
`S`-primes, so the route transfers to `ω_S`, with a Mertens rate replacing their variance lower
bound.

Audit and route: `docs/ERDOS257-BASE2-SUBSET-AUDIT-2026-10-02.md` (§4, lemmas N1-N8; the
mathematics closes 75%, reachable in days 50%).  Interface first: `VeryLargeCov` replaces the
pointwise bound by a second-moment one (N1 `blockSum_sq_le_of_cov`, N2
`gridFrameW_subset_propD_of_cov`).

## Frozen statements (do not edit; prove them)

* `isDisjunctive_subsetLambert_two`, conditional on `CastingOut.TTEquidistributedDyadic` only
  (re-frozen 2026-10-02 by the operator: the first transcription,
  `TTEquidistributedCorrelation`, is vacuous, `ttEquidistributedCorrelation_trivially_true`).
* `erdos257_primeSubset`: Erdős #257 for `A = S` itself, any prime set with a Mertens rate.
* `erdos257_residueClass`: the residue-class instance.

## Guard rule

**Content locator.**  `S` = all primes, irrationality only, is Tao–Teräväinen's theorem; the new
content is disjunctivity (stronger than irrationality, new even for all primes) and proper prime
subsets.  **Degenerate cases.**  A finite `S` gives a rational constant and fails the Mertens rate;
`b ≥ 3` is the existing theorem, so the case split at `b = 2` is where the content is.
-/

namespace NormalNumbers.Erdos257

open G4

variable {S : ℕ → Prop} [DecidablePred S]

/-- **The very-large covariance supply near the `SchedB` scales** (`Y = 2^{2^{mE}}`, and a
power-of-two `X = 2^x` with `100·2^{mE} ≤ x ≤ 101·2^{mE}`, so `Y^{100} ≤ X ≤ Y^{101}`): for every
grid of the schedule family, `κ` can be made arbitrarily small by taking the cutoff exponent `e`
large, with the fixed variance budget `V = 20000` (`ω_{S,>Y}(m) ≤ 102` for `m ≤ Mx`).

**Why `X` is chosen, not fixed** (found 2026-10-02 lap 3): TT's dyadic conclusion may fail on a
fraction `Cst·L^{-c}` of scales, which can include the top block `(X/2, X]` carrying half the
sample.  So `X` must be picked among `≈ 2^{mE}` candidate powers of two whose top `J₀` blocks are
all good scales; a union bound over the `B²` bin pairs leaves one. -/
def VeryLargeCovSupply (S : ℕ → Prop) [DecidablePred S] : Prop :=
  ∀ K N : ℕ, ∀ hK : 1 ≤ K, ∀ κ : ℝ, 0 < κ → ∃ e₀ : ℕ, ∀ e, e₀ ≤ e →
    ∃ x : ℕ, 100 * 2 ^ SchedB.mE K e ≤ x ∧ x ≤ 101 * 2 ^ SchedB.mE K e ∧
      VeryLargeCov S (gridOf K N hK) (2 ^ x) (SchedB.YE K e) 20000 κ

lemma aux_B {κ B Bm : ℝ} (hκ : 0 < κ) (h0 : 0 ≤ B) (h : B ≤ Bm) :
    B ^ 2 * (κ / (2 * (Bm ^ 2 + 1))) ≤ κ / 2 := by
  rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
  have : B ^ 2 ≤ Bm ^ 2 + 1 := by nlinarith
  nlinarith

lemma aux_e {s t θ κ : ℝ} (hκ : 0 < κ) (hs : s ≤ 10 * θ) (ht : t ≤ κ / (4 * 323)) (hθ : θ ≤ κ / 20000) :
    (2 * 111 + 101 : ℝ) * (s + t) ≤ κ / 2 := by
  linarith

/-- **N3–N6: the covariance supply from Tao–Teräväinen 3.1(i)** (dyadic form).  Route: bins of
`S ∩ (Y, Mx]` of harmonic mass `≤ 1/B` (N3), `ω_{S,>Y} = Σ_ℓ (1 − g_ℓ) + err` (N4), TT's
hypothesis (3.1) for the bin indicators `g_ℓ` via the rough-number count (N5), and averaging the
dyadic-block conclusion over `[0, X)` with the bad scales charged pointwise (N6).
`κ ≪ B²·(log X)^{-c} + A/B`, so `κ → 0` as `e → ∞` with `B` chosen late.  No Mertens rate is
needed.  75% (audit §4). -/
theorem veryLargeCovSupply_of_TT (htt : CastingOut.TTEquidistributedDyadic) :
    VeryLargeCovSupply S := by
  classical
  intro K N hK κ hκ
  obtain ⟨C₆, hC₆, hErr⟩ := Base2.avg_binErr_le
  obtain ⟨Y₀, hY₀⟩ := Base2.sum_inv_vlPrimes_le S
  set G := gridOf K N hK with hG
  set θ : ℝ := min (κ / 20000) (1 / 2) with hθ
  have hθ0 : 0 < θ := lt_min (by positivity) (by norm_num)
  have hθ1 : θ ≤ 1 / 2 := min_le_right _ _
  have hθκ : θ ≤ κ / 20000 := min_le_left _ _
  set Bmax : ℕ := ⌈5 / θ⌉₊ + 1 with hBmax
  set ε₂ : ℝ := κ / (2 * ((Bmax : ℝ) ^ 2 + 1)) with hε₂
  have hε₂0 : 0 < ε₂ := by positivity
  obtain ⟨e₁, he₁⟩ := Base2.binPair_cov htt K N hK hε₂0 Bmax
  set c₀ : ℕ := (K + N) * gridDm K N with hc₀
  obtain ⟨Λ, hΛ⟩ : ∃ Λ : ℝ, Λ = 4 * 323 * C₆ * G.P₀ / κ := ⟨_, rfl⟩
  set Z : ℕ := Y₀ + ⌈1 / θ⌉₊ + G.P₀ + c₀ + ⌈2 * Λ⌉₊ + 2 with hZ
  refine ⟨max e₁ Z, fun e he => ?_⟩
  have he₁e : e₁ ≤ e := le_trans (le_max_left _ _) he
  have hZe : Z ≤ e := le_trans (le_max_right _ _) he
  set Y := SchedB.YE K e with hYdef
  -- size of `Y`
  have hmE : e ≤ SchedB.mE K e := by unfold SchedB.mE; omega
  have hpow : SchedB.mE K e < 2 ^ SchedB.mE K e := Nat.lt_two_pow_self
  have hYge : 2 ^ SchedB.mE K e ≤ Y := by
    rw [hYdef]; unfold SchedB.YE; exact (Nat.lt_two_pow_self).le
  have hYe : e ≤ Y := by omega
  have hYZ : Z ≤ Y := le_trans hZe hYe
  have hY2 : 2 ≤ Y := by omega
  have hYY₀ : Y₀ ≤ Y := by omega
  have hP₀Y : G.P₀ < Y := by omega
  have hc₀Y : c₀ ≤ Y := by omega
  have hYθ : 1 / θ ≤ (Y : ℝ) := by
    have h1 : 1 / θ ≤ (⌈1 / θ⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : ⌈1 / θ⌉₊ ≤ Y := by omega
    have h3 : ((⌈1 / θ⌉₊ : ℕ) : ℝ) ≤ (Y : ℝ) := by exact_mod_cast h2
    linarith
  have hlogY : 2 * Λ ≤ 2 * Real.log Y := by
    have h1 : 2 * Λ ≤ (⌈2 * Λ⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : ⌈2 * Λ⌉₊ ≤ 2 ^ SchedB.mE K e := by omega
    have h3 : Real.log Y = (2 ^ SchedB.mE K e : ℕ) * Real.log 2 := by
      rw [hYdef]; unfold SchedB.YE; push_cast; rw [Real.log_pow]; push_cast; ring
    have h4 : ((⌈2 * Λ⌉₊ : ℕ) : ℝ) ≤ ((2 ^ SchedB.mE K e : ℕ) : ℝ) := by exact_mod_cast h2
    have h5 : (1 / 2 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
    have h6 : (0 : ℝ) ≤ ((2 ^ SchedB.mE K e : ℕ) : ℝ) := by positivity
    rw [h3]; nlinarith
  -- the very-large primes and their bins
  set M : ℕ := Y ^ 101 + c₀ with hM
  have hMle : M ≤ Y ^ 102 := by
    have : c₀ ≤ Y ^ 101 * (Y - 1) := by
      have h1 : 1 ≤ Y ^ 101 := Nat.one_le_pow _ _ (by omega)
      have h2 : 1 ≤ Y - 1 := by omega
      calc c₀ ≤ Y := hc₀Y
        _ = Y * 1 := by omega
        _ ≤ Y ^ 101 * (Y - 1) := Nat.mul_le_mul (Nat.le_self_pow (by norm_num) _) h2
    have h3 : Y ^ 102 = Y ^ 101 * (Y - 1) + Y ^ 101 := by
      rw [pow_succ]; zify [show 1 ≤ Y by omega]; ring
    omega
  have hMle' : M ≤ Y ^ 101 + Y ^ 100 := by
    have : c₀ ≤ Y ^ 100 := le_trans hc₀Y (Nat.le_self_pow (by norm_num) _)
    omega
  have hY2_100 : 2 * Y ≤ Y ^ 100 := by
    calc 2 * Y ≤ Y * Y := Nat.mul_le_mul_right _ hY2
      _ = Y ^ 2 := (sq Y).symm
      _ ≤ Y ^ 100 := Nat.pow_le_pow_right (by omega) (by norm_num)
  have hlt102 : Y ^ 101 + Y ^ 100 < Y ^ 102 := by
    have h0 : 0 < Y ^ 100 := Nat.pow_pos (by omega)
    have e1 : Y ^ 101 + Y ^ 100 = (Y + 1) * Y ^ 100 := by ring
    have e2 : Y ^ 102 = (Y * Y) * Y ^ 100 := by ring
    rw [e1, e2]
    have : Y + 1 < Y * Y := by
      have := Nat.mul_le_mul_right Y hY2
      omega
    exact Nat.mul_lt_mul_of_pos_right this h0
  set Q := Base2.vlPrimes S Y G.P₀ M with hQ
  have hQp : ∀ p ∈ Q, p.Prime ∧ Y < p := fun p hp => by
    rw [hQ, Base2.vlPrimes, Finset.mem_filter] at hp; exact ⟨hp.2.1, hp.2.2.2.2⟩
  have hQθ : ∀ p ∈ Q, (p : ℝ)⁻¹ ≤ θ := by
    intro p hp
    have hpY : (Y : ℝ) < p := by exact_mod_cast (hQp p hp).2
    have hY0 : (0 : ℝ) < Y := by positivity
    rw [inv_le_comm₀ (by linarith) hθ0]
    rw [one_div] at hYθ; linarith
  obtain ⟨B, bins, hdisj, hcover, hmassθ, hBle⟩ := Base2.exists_bins Q hθ0 hQθ
  have hmassQ : Base2.mass Q ≤ 5 := hY₀ Y G.P₀ M hYY₀ hMle
  have hmassQ' : Base2.mass Q = ∑ ℓ, Base2.mass (bins ℓ) := by
    rw [← hcover, Base2.mass, Finset.sum_biUnion]
    · rfl
    · intro ℓ _ ℓ' _ h; exact hdisj ℓ ℓ' h
  have hBB : B ≤ Bmax := by
    have h1 : (B : ℝ) ≤ 5 / θ + 1 := by
      refine hBle.trans ?_
      gcongr
    have h2 : 5 / θ ≤ (⌈5 / θ⌉₊ : ℝ) := Nat.le_ceil _
    have h3 : (B : ℝ) < ((⌈5 / θ⌉₊ + 1 + 1 : ℕ) : ℝ) := by push_cast; linarith
    have : B < ⌈5 / θ⌉₊ + 1 + 1 := by exact_mod_cast h3
    omega
  have hbinp : ∀ ℓ, ∀ p ∈ bins ℓ, p.Prime ∧ Y < p := fun ℓ p hp =>
    hQp p (hcover ▸ Finset.mem_biUnion.2 ⟨ℓ, Finset.mem_univ _, hp⟩)
  obtain ⟨x, hx1, hx2, hpair⟩ := he₁ e he₁e B hBB bins hbinp (fun ℓ => (hmassθ ℓ).trans (by linarith))
  refine ⟨x, hx1, hx2, ?_⟩
  -- sizes at `X = 2^x`
  have hXY : Y ^ 100 ≤ 2 ^ x := by
    rw [hYdef]; unfold SchedB.YE; rw [← pow_mul]
    exact Nat.pow_le_pow_right (by norm_num) (by rw [mul_comm]; exact hx1)
  have hXle : 2 ^ x ≤ Y ^ 101 := by
    rw [hYdef]; unfold SchedB.YE; rw [← pow_mul]
    exact Nat.pow_le_pow_right (by norm_num) (by rw [mul_comm]; exact hx2)
  have hY100 : Y ≤ Y ^ 100 := Nat.le_self_pow (by norm_num) _
  have hYX : Y ≤ 2 ^ x := le_trans hY100 hXY
  have hMn : ∀ n ∈ apSample (2 ^ x) G.P₀ G.b₀, ∀ i : G.Idx,
      n + shiftAL G.B G.Q G.D₀ i ≤ M := by
    intro n hn i
    have h := gridOf.add_shiftAL_le hK hn i
    have : 2 ^ x + (K + N) * gridDm K N ≤ M := by rw [hM, hc₀]; omega
    exact h.trans this
  set ε₁ : ℝ := ∑ ℓ, Base2.mass (bins ℓ) ^ 2 + C₆ * G.P₀ / Real.log Y with hε₁
  have hlogpos : 0 < Real.log Y := Real.log_pos (by exact_mod_cast (by omega : 1 < Y))
  have hε₁0 : 0 ≤ ε₁ := by
    have : ∀ ℓ, 0 ≤ Base2.mass (bins ℓ) ^ 2 := fun ℓ => sq_nonneg _
    have : 0 ≤ C₆ * G.P₀ / Real.log Y := by positivity
    have : 0 ≤ ∑ ℓ, Base2.mass (bins ℓ) ^ 2 := Finset.sum_nonneg fun ℓ _ => sq_nonneg _
    linarith
  have hcov := Base2.veryLargeCov_of_bins S G (2 ^ x) Y M bins hdisj hcover
    (fun ℓ p hp => (hbinp ℓ p hp).1) hMn
    (fun n hn i => Base2.omegaVLS_le S hY2 (lt_of_le_of_lt (hMn n hn i) (by
      exact lt_of_le_of_lt hMle' hlt102)))
    (fun ℓ => (hmassθ ℓ).trans (by linarith)) (by rw [← hmassQ']; exact hmassQ) hε₁0
    (fun i => hErr (2 ^ x) Y G.P₀ G.b₀ _ B bins G.P₀_pos G.b₀_lt_P₀ hP₀Y hYX
      ((gridOf.shiftAL_le hK i).trans (le_trans hc₀Y hYX)) (by omega) hdisj hbinp) hpair
  -- κ' ≤ κ
  obtain ⟨μ, hV, hC⟩ := hcov
  refine ⟨μ, hV, fun i j hij => (hC i j hij).trans ?_⟩
  have hmass0 : ∀ ℓ, 0 ≤ Base2.mass (bins ℓ) := fun ℓ =>
    Finset.sum_nonneg fun p _ => by positivity
  have hsq : ∑ ℓ, Base2.mass (bins ℓ) ^ 2 ≤ 10 * θ := by
    calc ∑ ℓ, Base2.mass (bins ℓ) ^ 2 ≤ ∑ ℓ, 2 * θ * Base2.mass (bins ℓ) :=
          Finset.sum_le_sum fun ℓ _ => by
            rw [sq]; exact mul_le_mul_of_nonneg_right (hmassθ ℓ) (hmass0 ℓ)
      _ = 2 * θ * Base2.mass Q := by rw [← Finset.mul_sum, hmassQ']
      _ ≤ 2 * θ * 5 := by gcongr
      _ = 10 * θ := by ring
  have hC6 : C₆ * G.P₀ / Real.log Y ≤ κ / (4 * 323) := by
    rw [div_le_div_iff₀ hlogpos (by norm_num)]
    have : Λ ≤ Real.log Y := by linarith
    rw [hΛ, div_le_iff₀ hκ] at this
    linarith
  have hB2 : (B : ℝ) ^ 2 * ε₂ ≤ κ / 2 :=
    aux_B hκ (Nat.cast_nonneg B) (by exact_mod_cast hBB)
  have : (2 * 111 + 101 : ℝ) * ε₁ ≤ κ / 2 := aux_e hκ hsq hC6 hθκ
  linarith

/-- **N3–N6, effective: the covariance supply from Tao–Teräväinen 3.1(i).**  Same route as
`veryLargeCovSupply_of_TT`, with every threshold made explicit: the TT/N5 constants
`c, Cst, C₅, X₀, Y₀, C₆` are absolute, and every other demand (`L^c ≥ P₀ + shift`,
`Cst·L^{-c}·J₀·B² < 1`, `log Y ≥ C₆P₀/κ`, …) is polynomial in `P₀·(shift+1)·2^t`.
Needed because `SchedB.HypE` caps the cutoff (`SchedB.moment_cap_two`).  Route: replace the
filter step `ev_L` in `binPair_cov` by an explicit threshold `L ≥ D·(2u)^k`.  80%. -/
theorem veryLargeCovSupplyEff_of_TT (htt : CastingOut.TTEquidistributedDyadic) :
    SchedB.VeryLargeCovSupplyEff S := by
  sorry

/-- **N6 + N7: the base-2 schedule witness with the covariance interface.** -/
theorem exists_scheduleWitnessSC_two (htt : CastingOut.TTEquidistributedDyadic)
    {c C : ℝ} (hm : MertensAP.MertensRate S c C) (ℓ w : ℕ) (hℓ : 1 ≤ ℓ) :
    Nonempty (ScheduleWitnessSC S 2 ℓ w) :=
  SchedB.exists_scheduleWitnessSC_two_of_supplyEff S (veryLargeCovSupplyEff_of_TT htt) hm ℓ w hℓ

/-- **Base-2 disjunctivity of `Σ_{p∈S} 1/(2ᵖ − 1)`** for any prime set with a Mertens rate,
conditional on Tao–Teräväinen Theorem 3.1(i).  75% (audit). -/
theorem isDisjunctive_subsetLambert_two (htt : CastingOut.TTEquidistributedDyadic)
    {c C : ℝ} (hm : MertensAP.MertensRate S c C) :
    IsDisjunctive 2 (PrimeLambert.subsetLambert S 2) := by
  refine isDisjunctive_subsetLambert_of_witnessC S 2 le_rfl fun ℓ w hw homit => ?_
  rcases Nat.eq_zero_or_pos ℓ with hℓ | hℓ
  · exfalso
    subst hℓ
    have hw0 : w = 0 := by simpa using hw
    subst hw0
    have := homit 0
    simp only [Nat.cast_zero, pow_zero, zero_add, div_one] at this
    exact this (orbit_mem_Ico 2 (PrimeLambert.subsetLambert S 2) 0)
  · exact exists_scheduleWitnessSC_two htt hm ℓ w hℓ

/-- **Erdős #257 for a prime set `A = S`** with a Mertens rate. -/
theorem erdos257_primeSubset (htt : CastingOut.TTEquidistributedDyadic)
    {c C : ℝ} (hm : MertensAP.MertensRate S c C) :
    Irrational (∑' n : kMulPrimes S 1, (1 : ℝ) / (2 ^ n.1 - 1)) := by
  rw [← subsetLambert_two_pow_eq le_rfl, pow_one]
  exact IsDisjunctive.irrational (isDisjunctive_subsetLambert_two htt hm)

/-- **Erdős #257 for the primes `≡ a (mod q)`.** -/
theorem erdos257_residueClass (htt : CastingOut.TTEquidistributedDyadic)
    {q : ℕ} [NeZero q] {a : ZMod q} (ha : IsUnit a) :
    Irrational (∑' n : kMulPrimes (fun p => (p : ZMod q) = a) 1, (1 : ℝ) / (2 ^ n.1 - 1)) := by
  obtain ⟨c, C, hm⟩ := MertensAP.mertensRate_residueClass ha
  exact erdos257_primeSubset htt hm

end NormalNumbers.Erdos257
