/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.G4SchedBEAssembly
import NormalNumbers.G4SubsetWitnessCov
import NormalNumbers.G4SubsetAssembly

/-!
# N7: the base-2 schedule

The base-`b ≥ 3` schedule (`SchedB.scheduleWitnessSE`) is reused at `b = 2` by keeping its
**parameter layer at `b = 3`** (`HypE 3 K e`: the cutoff floor `m₁ 3 K ≤ e` and the moment cap)
and redoing only the fields where the base enters:

* `hM`, `hB`: the cylinder count `(2^ℓ − 1)^M` with `M = MG 2 ℓ K` (`gridB_bound` is
  base-general);
* `hbig`: at `b = 2`, `rowL1 = 1`, `rowL2 = 2^{-K}/3`; the very-large primes enter through the
  covariance bound with `V = 20000`, `κ = 2^{-K}`;
* `hfar`: `farBound 2` at the larger sample `X = 2^x ∈ [XE, XE·Y]`;
* `hbudget`: monotone in the frequency seed (`freqSeed 3 K ≤ freqSeed 2 K`) and in the sample
  size, so it follows from the `b = 3` budget.

**The cap.**  `HypE` caps `e` by `10⁵·T K·e ≤ 2^{8K²}`, so the covariance supply must be
*effective*: `VeryLargeCovSupplyEff` asks for it at every `e` with `A·Z^A ≤ 2^e`,
`Z = P₀·(shift + 1)·⌈1/κ⌉`, `A` absolute.  Since `log P₀ ≤ K^{20K+17}`, that fits under the cap
for `K` large (found 2026-10-02 lap 4: the ineffective `∃ e₀` form cannot feed the schedule).
-/

open Finset Real
open scoped BigOperators Nat

namespace NormalNumbers.G4

open PrimeLambert GridParams

namespace SchedB

open Sched (N J T logP₀Nat m₂ Dj)

/-! ### The cylinder count at `b = 2` -/

lemma MG_lo' {b ℓ K : ℕ} (hb : 2 ≤ b) (hℓ : 1 ≤ ℓ) :
    (K : ℝ) / 4 * Real.log 2 ≤ (MG b ℓ K : ℝ) * ℓ * Real.log b := by
  have hlb : 0 < Real.log b := Real.log_pos (by exact_mod_cast (show 1 < b by omega))
  have hℓr : (1 : ℝ) ≤ ℓ := by exact_mod_cast hℓ
  have hden : 0 < 4 * (ℓ : ℝ) * Real.log b := by positivity
  have h := Nat.le_ceil ((K : ℝ) * Real.log 2 / (4 * ℓ * Real.log b))
  unfold MG
  rw [div_le_iff₀ hden] at h
  nlinarith

lemma MG_hi' {b ℓ K : ℕ} (hb : 2 ≤ b) (hℓ : 1 ≤ ℓ) :
    (MG b ℓ K : ℝ) * ℓ * Real.log b ≤ (K : ℝ) / 4 * Real.log 2 + ℓ * Real.log b := by
  have hlb : 0 < Real.log b := Real.log_pos (by exact_mod_cast (show 1 < b by omega))
  have hℓr : (1 : ℝ) ≤ ℓ := by exact_mod_cast hℓ
  have hden : 0 < 4 * (ℓ : ℝ) * Real.log b := by positivity
  have hnn : 0 ≤ (K : ℝ) * Real.log 2 / (4 * ℓ * Real.log b) := by
    have := Real.log_pos (show (1:ℝ) < 2 by norm_num); positivity
  have h := Nat.ceil_lt_add_one hnn
  unfold MG
  have h' : (⌈(K : ℝ) * Real.log 2 / (4 * ℓ * Real.log b)⌉₊ : ℝ) * (4 * ℓ * Real.log b)
      < (K : ℝ) * Real.log 2 + 4 * ℓ * Real.log b := by
    have := mul_lt_mul_of_pos_right h hden
    rwa [add_mul, div_mul_cancel₀ _ hden.ne', one_mul] at this
  nlinarith [h']

lemma hM_holds' {b ℓ K k₄ : ℕ} (hb : 2 ≤ b) (hℓ : 1 ≤ ℓ) (hK4 : K = 4 * k₄) :
    1 / ((b : ℝ) ^ ℓ) ^ MG b ℓ K ≤ (1 / 2 : ℝ) ^ k₄ := by
  have hbr : (1 : ℝ) < b := by exact_mod_cast (show 1 < b by omega)
  have hlo := MG_lo' (K := K) hb hℓ
  have hK4' : (K : ℝ) / 4 = k₄ := by rw [hK4]; push_cast; ring
  rw [hK4'] at hlo
  have e1 : ((b : ℝ) ^ ℓ) ^ MG b ℓ K = Real.exp ((MG b ℓ K : ℝ) * ℓ * Real.log b) := by
    rw [← pow_mul, ← Real.rpow_natCast, Real.rpow_def_of_pos (by linarith)]
    push_cast; ring_nf
  have e2 : (2 : ℝ) ^ k₄ = Real.exp ((k₄ : ℝ) * Real.log 2) := by
    rw [← Real.rpow_natCast, Real.rpow_def_of_pos (by norm_num), mul_comm]
  rw [one_div_pow, e1, one_div, one_div, e2]
  exact inv_anti₀ (Real.exp_pos _) (Real.exp_le_exp.2 hlo)

lemma KG_ge_two {ℓ k₄ : ℕ} (hk : k₄bℓ 3 ℓ ≤ k₄) :
    8464 * ℓ ^ 2 * 2 ^ (2 * ℓ) * Nat.clog 2 2 ^ 2 ≤ 4 * k₄ := by
  have hc : Nat.clog 2 2 = 1 := by
    have := Nat.clog_pow 2 1 (by norm_num)
    simpa using this
  rw [hc, one_pow, mul_one]
  unfold k₄bℓ at hk
  have h1 : 2 ^ (2 * ℓ) ≤ 3 ^ (2 * ℓ + 2) :=
    (Nat.pow_le_pow_left (by norm_num) _).trans (Nat.pow_le_pow_right (by norm_num) (by omega))
  calc 8464 * ℓ ^ 2 * 2 ^ (2 * ℓ) ≤ 8464 * ℓ ^ 2 * 3 ^ (2 * ℓ + 2) :=
        Nat.mul_le_mul_left _ h1
    _ ≤ k₄ := hk
    _ ≤ 4 * k₄ := by omega

lemma rowL1_two' (K : ℕ) : rowL1 ((2 : ℕ) : ℝ) K = 1 := by
  unfold rowL1; norm_num

lemma rowL2_two' (K : ℕ) : rowL2 ((2 : ℕ) : ℝ) K = (1 / 2 : ℝ) ^ K / 3 := by
  unfold rowL2; norm_num

lemma sq_le_two_pow' {k : ℕ} (hk : 25 ≤ k) : 2048 * k ^ 2 ≤ 2 ^ k := by
  induction k, hk using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
    rw [pow_succ 2 n]
    have : (n + 1) ^ 2 ≤ 2 * n ^ 2 := by nlinarith
    nlinarith

/-- **`hbig` at `b = 2`**, with the covariance term `V = 20000`, `κ = 2^{-K}`, at any sample
`X = 2^x ≥ XE`. -/
theorem hbig_two {K k₄ e x : ℕ} (hK4 : K = 4 * k₄) (h : HypE 3 K e)
    (hx : 100 * 2 ^ mE K e ≤ x) :
    Real.sqrt (4 * (1 + Real.log (Nat.log 2 (YE K e)) - Real.log (Nat.log 2 (RE e)))
          * rowL2 ((2 : ℕ) : ℝ) K
        + 2 * (YE K e : ℝ) ^ 2 * (rowL1 ((2 : ℕ) : ℝ) K) ^ 2
          / ((apSample (2 ^ x) (gridOf K (N K) h.hK1).P₀ (gridOf K (N K) h.hK1).b₀).card : ℝ))
      + Real.sqrt (rowL2 ((2 : ℕ) : ℝ) K * 20000 + rowL1 ((2 : ℕ) : ℝ) K ^ 2 * (1 / 2 : ℝ) ^ K)
      ≤ (1 / 8 : ℝ) * ((1 / K : ℝ) * (1 / 2 : ℝ) ^ k₄) := by
  have hK := h.base.hK
  have hk : 25 ≤ k₄ := by omega
  have hKr : (100 : ℝ) ≤ K := by exact_mod_cast hK
  have hKk : (K : ℝ) = 4 * k₄ := by rw [hK4]; push_cast; ring
  rw [rowL1_two', rowL2_two']
  set G := gridOf K (N K) h.hK1 with hG
  set a : ℝ := (1 / 2 : ℝ) ^ k₄ with ha
  have ha0 : 0 < a := by positivity
  have ha4 : (1 / 2 : ℝ) ^ K = a ^ 4 := by rw [ha, ← pow_mul, hK4, mul_comm]
  rw [ha4]
  have hfac := dyadic_factor_leE K e
  -- the sample term
  set m := mE K e with hm
  have hKm : K ≤ 2 ^ m := by
    have : K * (K ^ 2) ^ K ≤ 2 ^ m := Kr_le_two_pow_mE h
    have : K ≤ K * (K ^ 2) ^ K := Nat.le_mul_of_pos_right _ (by positivity)
    omega
  have hP₀ : (G.P₀ : ℝ) ≤ (2 : ℝ) ^ (2 * 2 ^ m) := P₀_le_two_powE h
  have hP₀pos : (0 : ℝ) < G.P₀ := by exact_mod_cast G.P₀_pos
  have hXle : 2 * G.P₀ ≤ 2 ^ x := by
    have h1 : ((2 * G.P₀ : ℕ) : ℝ) ≤ ((2 ^ x : ℕ) : ℝ) := by
      push_cast
      calc 2 * (G.P₀ : ℝ) ≤ 2 * (2 : ℝ) ^ (2 * 2 ^ m) := by gcongr
        _ = (2 : ℝ) ^ (2 * 2 ^ m + 1) := by rw [pow_succ]; ring
        _ ≤ (2 : ℝ) ^ x := pow_le_pow_right₀ (by norm_num) (by omega)
    exact_mod_cast h1
  have hcard := Sched.card_apSample_ge_half (2 ^ x) G.P₀ G.b₀ G.P₀_pos G.b₀_lt_P₀ hXle
  have hcard0 : (0 : ℝ) < (apSample (2 ^ x) G.P₀ G.b₀).card := by
    refine lt_of_lt_of_le ?_ hcard; push_cast; positivity
  have hY : (YE K e : ℝ) = (2 : ℝ) ^ (2 ^ m) := by unfold YE; push_cast; rfl
  have hsamp : 2 * (YE K e : ℝ) ^ 2 * 1 ^ 2 / (apSample (2 ^ x) G.P₀ G.b₀).card ≤ a ^ 4 := by
    rw [div_le_iff₀ hcard0, hY]
    have h2x : (2 : ℝ) ^ x ≥ (2 : ℝ) ^ (100 * 2 ^ m) := pow_le_pow_right₀ (by norm_num) hx
    have hc' : (2 : ℝ) ^ x / (2 * G.P₀) ≤ (apSample (2 ^ x) G.P₀ G.b₀).card := by
      have := hcard; push_cast at this; exact this
    -- `a⁴ · 2^x/(2P₀) ≥ 2·Y²`
    have key : 2 * ((2 : ℝ) ^ 2 ^ m) ^ 2 * (2 * G.P₀) ≤ a ^ 4 * (2 : ℝ) ^ x := by
      have e1 : 2 * ((2 : ℝ) ^ 2 ^ m) ^ 2 * (2 * (2 : ℝ) ^ (2 * 2 ^ m))
          = (2 : ℝ) ^ (4 * 2 ^ m + 2) := by
        rw [← pow_mul]; rw [show 4 * 2 ^ m + 2 = 2 ^ m * 2 + 2 * 2 ^ m + 2 by ring]
        rw [pow_add, pow_add]; ring
      have e2 : a ^ 4 * (2 : ℝ) ^ (K + (4 * 2 ^ m + 2)) = (2 : ℝ) ^ (4 * 2 ^ m + 2) := by
        rw [← ha4, pow_add, ← mul_assoc, ← mul_pow]; norm_num
      calc 2 * ((2 : ℝ) ^ 2 ^ m) ^ 2 * (2 * G.P₀)
          ≤ 2 * ((2 : ℝ) ^ 2 ^ m) ^ 2 * (2 * (2 : ℝ) ^ (2 * 2 ^ m)) := by gcongr
        _ = a ^ 4 * (2 : ℝ) ^ (K + (4 * 2 ^ m + 2)) := by rw [e1, e2]
        _ ≤ a ^ 4 * (2 : ℝ) ^ x := by
            gcongr
            · norm_num
            · omega
    have hP2 : (0 : ℝ) < 2 * G.P₀ := by positivity
    calc 2 * ((2 : ℝ) ^ 2 ^ m) ^ 2 * 1 ^ 2 = 2 * ((2 : ℝ) ^ 2 ^ m) ^ 2 * (2 * G.P₀) / (2 * G.P₀) := by
          field_simp
      _ ≤ a ^ 4 * (2 : ℝ) ^ x / (2 * G.P₀) := by gcongr
      _ = a ^ 4 * ((2 : ℝ) ^ x / (2 * G.P₀)) := by ring
      _ ≤ a ^ 4 * (apSample (2 ^ x) G.P₀ G.b₀).card := by gcongr
  -- term 1 ≤ 4K a², term 2 ≤ 84 a²
  have ht1 : Real.sqrt (4 * (1 + Real.log (Nat.log 2 (YE K e)) - Real.log (Nat.log 2 (RE e)))
        * (a ^ 4 / 3) + 2 * (YE K e : ℝ) ^ 2 * 1 ^ 2 / (apSample (2 ^ x) G.P₀ G.b₀).card)
      ≤ 4 * K * a ^ 2 := by
    rw [Real.sqrt_le_iff]
    refine ⟨by positivity, ?_⟩
    have hf0 : 0 ≤ 1 + Real.log (Nat.log 2 (YE K e)) - Real.log (Nat.log 2 (RE e)) := by
      have h1 : Real.log (Nat.log 2 (RE e)) ≤ Real.log (Nat.log 2 (YE K e)) := by
        rw [natLog_YE, natLog_RE]
        apply Real.log_le_log (by positivity)
        exact_mod_cast Nat.pow_le_pow_right (by norm_num) (e_le_mE K e)
      linarith
    have : 4 * (1 + Real.log (Nat.log 2 (YE K e)) - Real.log (Nat.log 2 (RE e))) * (a ^ 4 / 3)
        ≤ 4 * (1 + 6 * (K : ℝ) ^ 2) * (a ^ 4 / 3) := by gcongr
    have ha4' : 0 ≤ a ^ 4 := by positivity
    have hK2 : (1 : ℝ) ≤ (K : ℝ) ^ 2 := by nlinarith
    have hm := mul_le_mul_of_nonneg_left hK2 ha4'
    have e : (4 * (K : ℝ) * a ^ 2) ^ 2 = 16 * (K : ℝ) ^ 2 * a ^ 4 := by ring
    rw [e]
    nlinarith
  have ht2 : Real.sqrt (a ^ 4 / 3 * 20000 + 1 ^ 2 * a ^ 4) ≤ 84 * a ^ 2 := by
    rw [Real.sqrt_le_iff]
    refine ⟨by positivity, ?_⟩
    have ha4' : 0 ≤ a ^ 4 := by positivity
    nlinarith
  have hfin : 4 * K * a ^ 2 + 84 * a ^ 2 ≤ (1 / 8 : ℝ) * ((1 / K : ℝ) * a) := by
    have hb := sq_le_two_pow' hk
    have hbr : (2048 : ℝ) * k₄ ^ 2 ≤ 2 ^ k₄ := by exact_mod_cast hb
    have e : a = 1 / (2 : ℝ) ^ k₄ := by rw [ha, one_div_pow]
    have hKpos : (0 : ℝ) < K := by linarith
    rw [show (1 / 8 : ℝ) * ((1 / K : ℝ) * a) = a / (8 * K) by field_simp]
    rw [le_div_iff₀ (by positivity)]
    have : (4 * K + 84) * 8 * K * a ≤ 1 := by
      rw [e, mul_one_div, div_le_one (by positivity), hKk]
      have hk' : (25 : ℝ) ≤ k₄ := by exact_mod_cast hk
      nlinarith
    nlinarith
  linarith

/-- `4K·A ≤ 2^{50K²+1}`: the far-tail numerator with room to spare against `2^N = 2^{100K²}`. -/
lemma four_mul_le_two_pow_NE' {b K e : ℕ} (h : HypE b K e) :
    4 * K * (logP₀Nat K + mE K e + 2 * J K + 13) ≤ 2 ^ (50 * K ^ 2 + 1) := by
  have hK := h.base.hK
  have hhalf := four_mul_le_two_pow_half h.base
  have hm2 : m₂ K ≤ m b K := by unfold m; omega
  have h1 : 4 * K * (logP₀Nat K + m₂ K + 2 * J K + 13) ≤ 2 ^ (50 * K ^ 2) := by
    refine le_trans ?_ hhalf
    exact Nat.mul_le_mul_left _ (by omega)
  have hT1 : 1 ≤ T K := Sched.T_pos (by omega)
  have hecap : e ≤ 2 ^ m₂ K := by
    have := h.hi
    unfold McE at this
    have : e ≤ 100000 * T K * e := Nat.le_mul_of_pos_left _ (by positivity)
    omega
  have hKlt : K < 2 ^ K := Nat.lt_two_pow_self
  have h4K : 4 * K ≤ 2 ^ (K + 2) := by
    calc 4 * K ≤ 4 * 2 ^ K := by omega
      _ = 2 ^ (K + 2) := by rw [pow_add]; ring
  have h2 : 4 * K * e ≤ 2 ^ (50 * K ^ 2) := by
    have hm2' : m₂ K = 8 * K ^ 2 := rfl
    calc 4 * K * e ≤ 2 ^ (K + 2) * 2 ^ m₂ K := Nat.mul_le_mul h4K hecap
      _ = 2 ^ (K + 2 + m₂ K) := by rw [← pow_add]
      _ ≤ 2 ^ (50 * K ^ 2) := by
          refine Nat.pow_le_pow_right (by norm_num) ?_
          rw [hm2']
          nlinarith
  have hsplit : 4 * K * (logP₀Nat K + mE K e + 2 * J K + 13)
      = 4 * K * (logP₀Nat K + m₂ K + 2 * J K + 13) + 4 * K * e := by
    unfold mE; ring
  have : 2 ^ (50 * K ^ 2) + 2 ^ (50 * K ^ 2) = 2 ^ (50 * K ^ 2 + 1) := by
    rw [pow_succ]; ring
  omega

/-- `farC` at a sample `2^x` with `x ≤ 101·2^{mE}`. -/
theorem farC_le_two {b K e x : ℕ} (h : HypE b K e) (hx1 : 100 * 2 ^ mE K e ≤ x)
    (hx2 : x ≤ 101 * 2 ^ mE K e) :
    farC (gridOf K (N K) h.hK1) (2 ^ x) (gridDm K (N K)) ≤ logP₀Nat K + mE K e + 10 := by
  have hK := h.base.hK
  set G := gridOf K (N K) h.hK1 with hG
  set m := mE K e with hm
  have hP₀ : (0 : ℝ) < G.P₀ := by exact_mod_cast G.P₀_pos
  have hXE : XE K e ≤ 2 ^ x := Nat.pow_le_pow_right (by norm_num) hx1
  have h2P : 2 * G.P₀ ≤ 2 ^ x := (two_mul_P₀_le_XE h).trans hXE
  have hcard := Sched.card_apSample_ge_half (2 ^ x) G.P₀ G.b₀ G.P₀_pos G.b₀_lt_P₀ h2P
  have hcard0 : (0 : ℝ) < (apSample (2 ^ x) G.P₀ G.b₀).card := by
    refine lt_of_lt_of_le ?_ hcard; push_cast; positivity
  have hDm : gridDm K (N K) ≤ 2 ^ x := (gridDm_le_XE h).trans hXE
  have hDmX : (gridDm K (N K) : ℝ) ≤ ((2 ^ x : ℕ) : ℝ) := by exact_mod_cast hDm
  have hP₀exp := Sched.P₀_le_exp (K := K) (by omega)
  unfold farC
  have h1 : (((2 ^ x + gridDm K (N K) : ℕ) : ℝ) / (apSample (2 ^ x) G.P₀ G.b₀).card)
      ≤ 4 * G.P₀ := by
    push_cast
    rw [div_le_iff₀ hcard0]
    have hc' : ((2 ^ x : ℕ) : ℝ) / (2 * G.P₀) ≤ (apSample (2 ^ x) G.P₀ G.b₀).card := hcard
    push_cast at hDmX hc'
    calc (2 : ℝ) ^ x + gridDm K (N K) ≤ 2 * 2 ^ x := by linarith
      _ = 4 * G.P₀ * ((2 : ℝ) ^ x / (2 * G.P₀)) := by field_simp; ring
      _ ≤ 4 * G.P₀ * (apSample (2 ^ x) G.P₀ G.b₀).card := by gcongr
  have h1' : Real.log (((2 ^ x + gridDm K (N K) : ℕ) : ℝ) / (apSample (2 ^ x) G.P₀ G.b₀).card)
      ≤ 2 + logP₀Nat K := by
    have hpos : (0 : ℝ) < ((2 ^ x + gridDm K (N K) : ℕ) : ℝ) / (apSample (2 ^ x) G.P₀ G.b₀).card := by
      push_cast; positivity
    calc Real.log (((2 ^ x + gridDm K (N K) : ℕ) : ℝ) / (apSample (2 ^ x) G.P₀ G.b₀).card)
        ≤ Real.log (4 * G.P₀) := Real.log_le_log hpos h1
      _ = Real.log 4 + Real.log G.P₀ := Real.log_mul (by norm_num) hP₀.ne'
      _ ≤ 2 + logP₀Nat K := by
          have ha : Real.log 4 ≤ 2 := by
            have : (4 : ℝ) ≤ Real.exp 2 := by
              have := Real.add_one_le_exp (1 : ℝ)
              have h2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
              rw [h2]; nlinarith [Real.exp_pos 1]
            calc Real.log 4 ≤ Real.log (Real.exp 2) := Real.log_le_log (by norm_num) this
              _ = 2 := Real.log_exp 2
          have hb : Real.log G.P₀ ≤ logP₀Nat K := by
            calc Real.log G.P₀ ≤ Real.log (Real.exp (logP₀Nat K)) := Real.log_le_log hP₀ hP₀exp
              _ = logP₀Nat K := Real.log_exp _
          linarith
  have h2 : Real.log (Real.log ((2 ^ x + gridDm K (N K) : ℕ) : ℝ) + 1) ≤ m + 8 := by
    have hl2 : Real.log 2 ≤ 1 := by linarith [Real.log_two_lt_d9]
    have hl2' : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hge1 : (1 : ℝ) ≤ ((2 ^ x + gridDm K (N K) : ℕ) : ℝ) := by
      have : 1 ≤ 2 ^ x + gridDm K (N K) := by have := Nat.one_le_two_pow (n := x); omega
      exact_mod_cast this
    have hlogX : Real.log ((2 ^ x + gridDm K (N K) : ℕ) : ℝ) ≤ (2 : ℝ) ^ (m + 7) := by
      have hle : ((2 ^ x + gridDm K (N K) : ℕ) : ℝ) ≤ (2 : ℝ) ^ (x + 1) := by
        push_cast at hDmX ⊢
        rw [pow_succ]; linarith
      calc Real.log ((2 ^ x + gridDm K (N K) : ℕ) : ℝ)
          ≤ Real.log ((2 : ℝ) ^ (x + 1)) := Real.log_le_log (by linarith) hle
        _ = (x + 1 : ℕ) * Real.log 2 := by rw [Real.log_pow]
        _ ≤ (x + 1 : ℕ) := by
            have : (0 : ℝ) ≤ (x + 1 : ℕ) := by positivity
            nlinarith
        _ ≤ (2 : ℝ) ^ (m + 7) := by
            have : x + 1 ≤ 2 ^ (m + 7) := by
              rw [pow_add]
              have : 1 ≤ 2 ^ m := Nat.one_le_two_pow
              omega
            exact_mod_cast this
    have hpos : (0 : ℝ) < Real.log ((2 ^ x + gridDm K (N K) : ℕ) : ℝ) + 1 := by
      have := Real.log_nonneg hge1
      linarith
    calc Real.log (Real.log ((2 ^ x + gridDm K (N K) : ℕ) : ℝ) + 1)
        ≤ Real.log ((2 : ℝ) ^ (m + 8)) := by
          apply Real.log_le_log hpos
          have : (1 : ℝ) ≤ (2 : ℝ) ^ (m + 7) := one_le_pow₀ (by norm_num)
          rw [pow_succ]
          linarith
      _ = (m + 8 : ℕ) * Real.log 2 := by rw [Real.log_pow]
      _ ≤ (m + 8 : ℕ) := by
          have : (0 : ℝ) ≤ (m + 8 : ℕ) := by positivity
          nlinarith
      _ = m + 8 := by push_cast; ring
  linarith

/-- **`hfar` at `b = 2`**, at the sample `2^x`. -/
theorem hfar_two {b K k₄ e x : ℕ} (hK4 : K = 4 * k₄) (h : HypE b K e)
    (hx1 : 100 * 2 ^ mE K e ≤ x) (hx2 : x ≤ 101 * 2 ^ mE K e) :
    (2 : ℝ) ^ K / Real.log 2 * farBound ((2 : ℕ) : ℝ) (K + N K)
        (farC (gridOf K (N K) h.hK1) (2 ^ x) (gridDm K (N K)))
      ≤ (1 / 8 : ℝ) * ((1 / K : ℝ) * (1 / 2 : ℝ) ^ k₄) := by
  have hK := h.base.hK
  have hfarC := farC_le_two h hx1 hx2
  set C := farC (gridOf K (N K) h.hK1) (2 ^ x) (gridDm K (N K)) with hC
  have hl2 : (2 / 3 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hl2' : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hKr : (100 : ℝ) ≤ K := by exact_mod_cast hK
  have hKpos : (0 : ℝ) < K := by linarith
  set A : ℕ := logP₀Nat K + mE K e + 2 * J K + 13 with hA
  have hA1 : (1 : ℝ) ≤ A := by have : 1 ≤ A := by omega
                               exact_mod_cast this
  have hJ : (J K : ℝ) = K + N K := by unfold J; push_cast; ring
  have hbr : C + 2 * ((K + N K : ℕ) : ℝ) + 2 + 2 ≤ 2 * (A : ℝ) := by
    rw [hA]; push_cast; rw [hJ] at *; linarith
  have hN := four_mul_le_two_pow_NE' h
  have hk : 25 ≤ k₄ := by omega
  -- `64·K·A·2^{k₄} ≤ 2^N`
  have hNbig : 64 * (4 * K * A) * 2 ^ k₄ ≤ 2 ^ N K := by
    calc 64 * (4 * K * A) * 2 ^ k₄ ≤ 2 ^ 6 * 2 ^ (50 * K ^ 2 + 1) * 2 ^ k₄ := by
          gcongr; norm_num
      _ = 2 ^ (6 + (50 * K ^ 2 + 1) + k₄) := by rw [← pow_add, ← pow_add]
      _ ≤ 2 ^ N K := by
          refine Nat.pow_le_pow_right (by norm_num) ?_
          unfold Sched.N; nlinarith
  have hNr : (64 : ℝ) * (4 * K * A) * 2 ^ k₄ ≤ 2 ^ N K := by exact_mod_cast hNbig
  have e1 : (2 : ℝ) ^ K / Real.log 2 * farBound ((2 : ℕ) : ℝ) (K + N K) C
      = (C + 2 * ((K + N K : ℕ) : ℝ) + 2 + 2) / (2 ^ N K * Real.log 2) := by
    unfold farBound
    push_cast
    rw [one_div_pow, pow_add]
    field_simp
    ring
  rw [e1, div_le_iff₀ (by positivity)]
  have ha : (1 / 2 : ℝ) ^ k₄ * 2 ^ k₄ = 1 := by rw [← mul_pow]; norm_num
  have hpk : (0 : ℝ) < 2 ^ k₄ := by positivity
  set a : ℝ := (1 / 2 : ℝ) ^ k₄ with hadef
  have hC0 : 0 ≤ C + 2 * ((K + N K : ℕ) : ℝ) + 2 + 2 := by
    have := farC_nonneg (gridOf K (N K) h.hK1) (2 ^ x)
      (apSample_nonempty_of_le _ _ _ (gridOf K (N K) h.hK1).P₀_pos
        (gridOf K (N K) h.hK1).b₀_lt_P₀ ((two_mul_P₀_le_XE h).trans
          (Nat.pow_le_pow_right (by norm_num) hx1))) (gridDm K (N K))
    positivity
  -- RHS = a/(8K)·2^N·log 2 ≥ a/(8K)·64·4KA·2^{k₄}·(2/3) = 64/3·... ≥ 2A
  have : (1 / 8 : ℝ) * ((1 / K : ℝ) * a) * (2 ^ N K * Real.log 2)
      ≥ (1 / 8 : ℝ) * ((1 / K : ℝ) * a) * ((64 : ℝ) * (4 * K * A) * 2 ^ k₄ * (2 / 3)) := by
    gcongr
  have e2 : (1 / 8 : ℝ) * ((1 / K : ℝ) * a) * ((64 : ℝ) * (4 * K * A) * 2 ^ k₄ * (2 / 3))
      = 64 / 3 * A * (a * 2 ^ k₄) := by field_simp; ring
  rw [e2, ha] at this
  linarith

/-- `smallPrimeBound` is antitone in the sample size and in the frequency seed. -/
lemma smallPrimeBound_anti (sm : Finset ℕ) (T R M : ℕ) {Psz Psz' : ℕ} (lam' lam : ℝ) {θ θ' : ℝ}
    (hP : 0 < Psz) (hPP : Psz ≤ Psz') (hθ : θ ≤ θ') (hsm : ∀ p ∈ sm, 0 < p) :
    smallPrimeBound sm T R M Psz' lam' lam θ' ≤ smallPrimeBound sm T R M Psz lam' lam θ := by
  unfold smallPrimeBound
  have hPr : (0 : ℝ) < Psz := by exact_mod_cast hP
  have hPPr : (Psz : ℝ) ≤ Psz' := by exact_mod_cast hPP
  have h1 : Real.exp (-∑ p ∈ sm, 4 * θ' / p) ≤ Real.exp (-∑ p ∈ sm, 4 * θ / p) := by
    apply Real.exp_le_exp.2
    apply neg_le_neg
    apply Finset.sum_le_sum
    intro p hp
    have : (0 : ℝ) < p := by exact_mod_cast hsm p hp
    gcongr
  have h2 : 2 * (R : ℝ) ^ M / Psz' ≤ 2 * (R : ℝ) ^ M / Psz := by
    apply div_le_div_of_nonneg_left (by positivity) hPr hPPr
  have hc0 : (0 : ℝ) ≤ ((sm.powerset.filter (fun T' => T'.Nonempty ∧ T'.card ≤ M)).card : ℝ) := by
    positivity
  have hd0 : (0 : ℝ) ≤ 2 * (2 * Real.exp 1 / M) ^ M * (sm.card : ℝ) ^ M := by
    rcases Nat.eq_zero_or_pos M with hM | hM
    · subst hM; simp
    · have : (0 : ℝ) < M := by exact_mod_cast hM
      positivity
  have h3 := mul_le_mul_of_nonneg_left h2 (show (0 : ℝ) ≤ 2 ^ M by positivity)
  have h4 := mul_le_mul_of_nonneg_left h3 hc0
  have h5 := mul_le_mul_of_nonneg_left h2 hd0
  have e5 : ∀ Q : ℝ, 2 * (2 * Real.exp 1 / M) ^ M * (sm.card : ℝ) ^ M * Q
      = 2 * (2 * Real.exp 1 / M) ^ M * (sm.card : ℝ) ^ M * Q := fun Q => rfl
  nlinarith [h1, h4, h5]

lemma apSample_mono {X X' : ℕ} (h : X ≤ X') (P₀ a : ℕ) : apSample X P₀ a ⊆ apSample X' P₀ a := by
  intro n hn
  unfold apSample at hn ⊢
  rw [mem_filter, mem_range] at hn ⊢
  exact ⟨by omega, hn.2⟩

lemma freqSeed_three_le_two (K : ℕ) : freqSeed ((3 : ℕ) : ℝ) K ≤ freqSeed ((2 : ℕ) : ℝ) K := by
  unfold freqSeed
  push_cast
  have h1 : (2 / (3 : ℝ) ^ 2) ^ K ≤ (2 / (2 : ℝ) ^ 2) ^ K :=
    pow_le_pow_left₀ (by norm_num) (by norm_num) _
  have h2 : (1 / (3 : ℝ) ^ 4) ≤ 1 / (2 : ℝ) ^ 4 := by norm_num
  exact mul_le_mul h2 h1 (by positivity) (by norm_num)

variable (S : ℕ → Prop) [DecidablePred S]

/-- **`hbudget` at `b = 2`**, at the sample `2^x ≥ XE`, from the `b = 3` budget. -/
theorem hbudget_two {K k₄ e x : ℕ} (hK4 : K = 4 * k₄) (h : HypE 3 K e)
    (hx1 : 100 * 2 ^ mE K e ≤ x)
    (hlow : (m₁ 3 K : ℝ) * Real.log 2 - 21 * (K : ℝ) ^ 2 - 4
      ≤ ∑ p ∈ (smallPrimes (RE e) (gridOf K (N K) h.hK1).P₀).filter S, (p : ℝ)⁻¹) :
    (1 / 8 : ℝ) + ((1 / 8 : ℝ) + (1 / 8 : ℝ))
      + 2 * (1 / ((1 / K : ℝ) * (1 / 2 : ℝ) ^ k₄ * Real.sqrt ((Dj K k₄ : ℕ) + 1)))
      + (((2 * Dj K k₄ + 1) ^ ((K ^ 2) ^ K) : ℕ) : ℝ)
        * smallPrimeBound ((smallPrimes (RE e) (gridOf K (N K) h.hK1).P₀).filter S)
            (Fintype.card (gridOf K (N K) h.hK1).Idx) (RE e) (McE K e)
            (apSample (2 ^ x) (gridOf K (N K) h.hK1).P₀ (gridOf K (N K) h.hK1).b₀).card
            (Real.exp 1) (13 / 2) (freqSeed ((2 : ℕ) : ℝ) K) < 1 := by
  have hsub : (smallPrimes (RE e) (gridOf K (N K) h.hK1).P₀).filter S
      ⊆ smallPrimes (RE e) (gridOf K (N K) h.hK1).P₀ := Finset.filter_subset _ _
  have hbud := hbudget_holdsE_gen (k₄ := k₄) hK4 h hsub hlow
  have hc : Fintype.card (gridOf K (N K) h.hK1).Idx = T K := gridOf.card_Idx h.hK1
  rw [hc]
  refine lt_of_le_of_lt ?_ hbud
  gcongr
  apply smallPrimeBound_anti
  · exact (sample_nonemptyE h).card_pos
  · exact Finset.card_le_card (apSample_mono (Nat.pow_le_pow_right (by norm_num) hx1) _ _)
  · exact freqSeed_three_le_two K
  · intro p hp
    exact (mem_smallPrimes.1 (hsub hp)).1.pos

/-- **The base-2 schedule witness.**  The `b = 3` parameter layer at cutoff `e`, the base-2
cylinder count, and a very-large covariance bound at a sample `2^x`, `x ∈ [100, 101]·2^{mE}`. -/
noncomputable def scheduleWitnessSC2 (ℓ w e k₄ x : ℕ) (hℓ : 1 ≤ ℓ) (hk : k₄bℓ 3 ℓ ≤ k₄)
    (hE : HypE 3 (4 * k₄) e)
    (hlow : (m₁ 3 (4 * k₄) : ℝ) * Real.log 2 - 21 * ((4 * k₄ : ℕ) : ℝ) ^ 2 - 4
      ≤ ∑ p ∈ (smallPrimes (RE e)
          (gridOf (4 * k₄) (Sched.N (4 * k₄)) hE.hK1).P₀).filter S, (p : ℝ)⁻¹)
    (hx1 : 100 * 2 ^ mE (4 * k₄) e ≤ x) (hx2 : x ≤ 101 * 2 ^ mE (4 * k₄) e)
    (hcov : VeryLargeCov S (gridOf (4 * k₄) (Sched.N (4 * k₄)) hE.hK1) (2 ^ x) (YE (4 * k₄) e) 20000
      ((1 / 2 : ℝ) ^ (4 * k₄))) :
    ScheduleWitnessSC S 2 ℓ w :=
  let K := 4 * k₄
  have hK4 : K = 4 * k₄ := rfl
  have h : Hyp 3 K := hE.base
  have hK100 : 100 ≤ K := h.hK
  have hK1 : 1 ≤ K := h.hK1
  have hKr : (100 : ℝ) ≤ K := by exact_mod_cast hK100
  { G := gridOf K (N K) hK1
    hK := by show 0 < K; omega
    hr := Nat.one_le_pow _ _ (by show 0 < K ^ 2; positivity)
    X := 2 ^ x
    hne := by
      obtain ⟨n, hn⟩ := sample_nonemptyE hE
      exact ⟨n, apSample_mono (Nat.pow_le_pow_right (by norm_num) hx1) _ _ hn⟩
    η := (1 / 2 : ℝ) ^ k₄
    hη := by positivity
    ε := 1 / (K : ℝ)
    hε := by positivity
    hε1 := by rw [div_lt_one (by linarith)]; linarith
    M := MG 2 ℓ K
    hM := hM_holds' (b := 2) (le_refl 2) hℓ hK4
    Lg := (((K ^ 2) ^ K : ℕ) : ℝ) * (Real.log 2 + 23 * Real.sqrt K)
    hlog := by
      have h := log_det_one_add_tensorGram_le' hK1
      push_cast
      exact h
    δ₁ := 1 / 8
    hδ₁ := by norm_num
    hB := by
      intro g hglo hghi
      have hr : (gridOf K (N K) hK1).rDim = (K ^ 2) ^ K := rfl
      have hH : (gridOf K (N K) hK1).hDim = (K ^ 2 + 1) ^ K := rfl
      rw [hr] at hglo hghi
      rw [hr, hH]
      have hη : ((1 / 2 : ℝ) ^ k₄) ^ 4 ≤ (1 / 2 : ℝ) ^ K := by
        rw [← pow_mul, hK4, mul_comm]
      exact gridB_bound (bb := 2) (le_refl 2) hℓ (KG_ge_two hk)
        (MG_lo' (K := 4 * k₄) (le_refl 2) hℓ) (MG_hi' (K := 4 * k₄) (le_refl 2) hℓ)
        (by positivity) hη le_rfl hglo hghi
    R := RE e
    hR := RE_ge_two e
    Y := YE K e
    hRY := RE_le_YE K e
    D := Dj K k₄
    hN := hN_holds (b := 2) (le_refl 2) hK4 hK100
    Mc := McE K e
    hMc := McE_pos hE
    lam' := Real.exp 1
    hlam' := Real.one_le_exp zero_le_one
    lam := 13 / 2
    hlam := by norm_num
    V := 20000
    κ := (1 / 2 : ℝ) ^ K
    hV := by norm_num
    hκ := by positivity
    hcov := hcov
    Dm := gridDm K (N K)
    hDm := gridOf.d_le hK1
    δbig := 1 / 8
    δfar := 1 / 8
    hbig := hbig_two (x := x) hK4 hE hx1
    hfar := hfar_two (x := x) hK4 hE hx1 hx2
    hbudget := hbudget_two S (x := x) hK4 hE hx1 hlow }

/-! ### The effective covariance supply and the choice of `(k₄, e)` -/

/-- **The very-large covariance supply, effective form.**  One absolute `A` such that at every
cutoff exponent `e` with `A·(P₀·(shift + 1)·2^t)^A ≤ 2^e` there is a power-of-two sample
`2^x`, `x ∈ [100, 101]·2^{mE}`, carrying `VeryLargeCov` with `V = 20000` and any
`κ ≥ 2^{-t}`.  The ineffective form (`∃ e₀`) cannot feed the schedule, whose moment cap bounds
`e` by `2^{8K²}/(10⁵ T)`. -/
def VeryLargeCovSupplyEff : Prop :=
  ∃ A : ℕ, ∀ K N : ℕ, ∀ hK : 1 ≤ K, ∀ κ : ℝ, ∀ t : ℕ, (1 / 2 : ℝ) ^ t ≤ κ → ∀ e : ℕ,
    A * ((gridOf K N hK).P₀ * ((K + N) * gridDm K N + 1) * 2 ^ t) ^ A ≤ 2 ^ e →
    ∃ x : ℕ, 100 * 2 ^ mE K e ≤ x ∧ x ≤ 101 * 2 ^ mE K e ∧
      VeryLargeCov S (gridOf K N hK) (2 ^ x) (YE K e) 20000 κ

/-- The size `P₀·(shift + 1)·2^K` in bits. -/
lemma sizeZ_le {K : ℕ} (hK : 100 ≤ K) :
    (gridOf K (N K) (by omega)).P₀ * ((K + N K) * gridDm K (N K) + 1) * 2 ^ K
      ≤ 2 ^ (4 * logP₀Nat K + 2 * (K + N K) + K) := by
  have hK1 : 1 ≤ K := by omega
  set L := logP₀Nat K
  have hP : ((gridOf K (N K) hK1).P₀ : ℝ) ≤ (2 : ℝ) ^ (2 * L) :=
    (Sched.P₀_le_exp hK1).trans (Sched.exp_nat_le_two_pow L)
  have hD : (gridDm K (N K) : ℝ) ≤ (2 : ℝ) ^ (2 * L) := by
    have h1 : (gridDm K (N K) : ℝ) ≤ gridP₀Bound K (N K) := by
      exact_mod_cast Sched.gridDm_le_gridP₀Bound K (N K) hK1
    have hpos : (0 : ℝ) < gridP₀Bound K (N K) := lt_of_lt_of_le
      (by exact_mod_cast gridDm_pos K (N K)) h1
    have h2 : (gridP₀Bound K (N K) : ℝ) ≤ Real.exp L := by
      calc (gridP₀Bound K (N K) : ℝ) = Real.exp (Real.log (gridP₀Bound K (N K))) :=
            (Real.exp_log hpos).symm
        _ ≤ _ := Real.exp_le_exp.2 (Sched.log_gridP₀Bound_le hK1)
    exact h1.trans (h2.trans (Sched.exp_nat_le_two_pow L))
  have hKN : 2 * (K + N K) ≤ 2 ^ (2 * (K + N K)) := by
    have := Nat.lt_two_pow_self (n := 2 * (K + N K)); omega
  have hKNr : (2 : ℝ) * ((K + N K : ℕ) : ℝ) ≤ (2 : ℝ) ^ (2 * (K + N K)) := by exact_mod_cast hKN
  have hD1 : (1 : ℝ) ≤ gridDm K (N K) := by exact_mod_cast gridDm_pos K (N K)
  have hKN1 : (1 : ℝ) ≤ ((K + N K : ℕ) : ℝ) := by
    have : 1 ≤ K + N K := by omega
    exact_mod_cast this
  have hmid : (((K + N K) * gridDm K (N K) + 1 : ℕ) : ℝ)
      ≤ (2 : ℝ) ^ (2 * (K + N K)) * (2 : ℝ) ^ (2 * L) := by
    push_cast
    have : ((K : ℝ) + N K) * gridDm K (N K) + 1 ≤ 2 * ((K : ℝ) + N K) * gridDm K (N K) := by
      push_cast at hKN1; nlinarith
    push_cast at hKNr
    calc ((K : ℝ) + N K) * gridDm K (N K) + 1 ≤ 2 * ((K : ℝ) + N K) * gridDm K (N K) := this
      _ ≤ (2 : ℝ) ^ (2 * (K + N K)) * (2 : ℝ) ^ (2 * L) := by gcongr
  have hfin : (((gridOf K (N K) hK1).P₀ * ((K + N K) * gridDm K (N K) + 1) * 2 ^ K : ℕ) : ℝ)
      ≤ (((2 ^ (4 * L + 2 * (K + N K) + K)) : ℕ) : ℝ) := by
    rw [Nat.cast_mul, Nat.cast_mul]
    calc ((gridOf K (N K) hK1).P₀ : ℝ) * (((K + N K) * gridDm K (N K) + 1 : ℕ) : ℝ)
          * ((2 ^ K : ℕ) : ℝ)
        ≤ (2 : ℝ) ^ (2 * L) * ((2 : ℝ) ^ (2 * (K + N K)) * (2 : ℝ) ^ (2 * L)) * (2 : ℝ) ^ K := by
          push_cast; gcongr
          push_cast at hmid; exact hmid
      _ = (((2 ^ (4 * L + 2 * (K + N K) + K)) : ℕ) : ℝ) := by
          push_cast; rw [← pow_add, ← pow_add, ← pow_add]; ring_nf
  exact_mod_cast hfin

/-- The moment cap at the inflated cutoff. -/
lemma moment_cap_two {k₄ e : ℕ} (hk : 25 ≤ k₄) (he : e ≤ 2 ^ (4 * k₄) * (4 * k₄) ^ (84 * k₄ + 20)) :
    100000 * T (4 * k₄) * e ≤ 2 ^ m₂ (4 * k₄) := by
  set K := 4 * k₄ with hK
  have hK100 : 100 ≤ K := by omega
  have hT := Sched.T_le hK100
  have hKk : K ≤ 2 ^ k₄ := by
    have := k₄_bound_one hk; omega
  have h1 : 100000 * T K * e ≤ 2 ^ 17 * (K ^ (3 * K + 3) * (2 ^ K * K ^ (84 * k₄ + 20))) := by
    calc 100000 * T K * e ≤ 2 ^ 17 * T K * e := by gcongr; norm_num
      _ ≤ 2 ^ 17 * K ^ (3 * K + 3) * (2 ^ K * K ^ (84 * k₄ + 20)) := by gcongr
      _ = _ := by ring
  have h2 : K ^ (3 * K + 3) * K ^ (84 * k₄ + 20) ≤ 2 ^ (k₄ * (96 * k₄ + 23)) := by
    rw [← pow_add, pow_mul]
    calc K ^ (3 * K + 3 + (84 * k₄ + 20)) ≤ (2 ^ k₄) ^ (3 * K + 3 + (84 * k₄ + 20)) :=
          Nat.pow_le_pow_left hKk _
      _ = (2 ^ k₄) ^ (96 * k₄ + 23) := by rw [hK]; ring_nf
  calc 100000 * T K * e ≤ 2 ^ 17 * (K ^ (3 * K + 3) * (2 ^ K * K ^ (84 * k₄ + 20))) := h1
    _ = 2 ^ 17 * 2 ^ K * (K ^ (3 * K + 3) * K ^ (84 * k₄ + 20)) := by ring
    _ ≤ 2 ^ 17 * 2 ^ K * 2 ^ (k₄ * (96 * k₄ + 23)) := by gcongr
    _ = 2 ^ (17 + K + k₄ * (96 * k₄ + 23)) := by rw [← pow_add, ← pow_add]
    _ ≤ 2 ^ m₂ K := by
        refine Nat.pow_le_pow_right (by norm_num) ?_
        unfold m₂; rw [hK]; nlinarith

/-- The inflated cutoff stays under `2^K·K^{21K+20}`. -/
lemma e_bound_two {k₄ A Dc e₀ : ℕ} (hk : 25 ≤ k₄) (hA : A ≤ k₄) (hDc : Dc ≤ k₄)
    (h : Hyp 3 (4 * k₄))
    (he₀ : e₀ ≤ Dc * (m₁ 3 (4 * k₄) + (4 * k₄) ^ 2 + 1)) :
    max (max e₀ (m₁ 3 (4 * k₄)))
        (A + A * (4 * logP₀Nat (4 * k₄) + 2 * (4 * k₄ + Sched.N (4 * k₄)) + 4 * k₄))
      ≤ 2 ^ (4 * k₄) * (4 * k₄) ^ (84 * k₄ + 20) := by
  set K := 4 * k₄ with hK
  have hK100 : 100 ≤ K := by omega
  have hm₁ := m₁_le h
  have hL := Sched.logP₀Nat_le hK100
  have hN := Sched.N_le hK100
  have hKpow : 1 ≤ K ^ (3 * K + 3) := Nat.one_le_pow _ _ (by omega)
  have hDcK : Dc ≤ 2 ^ K := by
    have := Nat.lt_two_pow_self (n := K); omega
  have hp1 : K ^ (3 * K + 3) ≤ K ^ (84 * k₄ + 20) :=
    Nat.pow_le_pow_right (by omega) (by omega)
  have hp2 : K ^ 2 ≤ K ^ (3 * K + 3) := Nat.pow_le_pow_right (by omega) (by omega)
  have hp3 : K ^ 3 ≤ K ^ (20 * K + 17) := Nat.pow_le_pow_right (by omega) (by omega)
  have hp4 : K ≤ K ^ (20 * K + 17) := Nat.le_self_pow (by omega) _
  have hp5 : K ^ (20 * K + 17) * K ^ 2 ≤ K ^ (84 * k₄ + 20) := by
    rw [← pow_add]; exact Nat.pow_le_pow_right (by omega) (by omega)
  have h2K : 1 ≤ 2 ^ K := Nat.one_le_two_pow
  -- branch 1
  have b1 : e₀ ≤ 2 ^ K * K ^ (84 * k₄ + 20) := by
    have : m₁ 3 K + K ^ 2 + 1 ≤ K ^ (84 * k₄ + 20) := by
      have : 3 * K ^ (3 * K + 3) ≤ K * K ^ (3 * K + 3) := Nat.mul_le_mul_right _ (by omega)
      have : K * K ^ (3 * K + 3) ≤ K ^ (84 * k₄ + 20) := by
        rw [← pow_succ']; exact Nat.pow_le_pow_right (by omega) (by omega)
      omega
    calc e₀ ≤ Dc * (m₁ 3 K + K ^ 2 + 1) := he₀
      _ ≤ 2 ^ K * K ^ (84 * k₄ + 20) := Nat.mul_le_mul hDcK this
  have b2 : m₁ 3 K ≤ 2 ^ K * K ^ (84 * k₄ + 20) := by
    have := Nat.le_mul_of_pos_left (K ^ (84 * k₄ + 20)) (show 0 < 2 ^ K by positivity)
    omega
  have b3 : A + A * (4 * logP₀Nat K + 2 * (K + N K) + K) ≤ 2 ^ K * K ^ (84 * k₄ + 20) := by
    have hw : 1 + (4 * logP₀Nat K + 2 * (K + N K) + K) ≤ 10 * K ^ (20 * K + 17) := by omega
    have hAK : A ≤ K := by omega
    have : A + A * (4 * logP₀Nat K + 2 * (K + N K) + K)
        = A * (1 + (4 * logP₀Nat K + 2 * (K + N K) + K)) := by ring
    rw [this]
    calc A * (1 + (4 * logP₀Nat K + 2 * (K + N K) + K)) ≤ K * (10 * K ^ (20 * K + 17)) :=
          Nat.mul_le_mul hAK hw
      _ ≤ K * (K * K ^ (20 * K + 17)) :=
          Nat.mul_le_mul_left K (Nat.mul_le_mul_right _ (by omega))
      _ = K ^ 2 * K ^ (20 * K + 17) := by ring
      _ ≤ K ^ (84 * k₄ + 20) := by rw [mul_comm]; exact hp5
      _ ≤ 2 ^ K * K ^ (84 * k₄ + 20) := Nat.le_mul_of_pos_left _ (by positivity)
  exact max_le (max_le b1 b2) b3

/-- **N7 from the effective supply.** -/
theorem exists_scheduleWitnessSC_two_of_supplyEff (hsup : VeryLargeCovSupplyEff S)
    {c C : ℝ} (hmert : MertensAP.MertensRate S c C) (ℓ w : ℕ) (hℓ : 1 ≤ ℓ) :
    Nonempty (ScheduleWitnessSC S 2 ℓ w) := by
  classical
  obtain ⟨A, hA⟩ := hsup
  obtain ⟨hc, -⟩ := id hmert
  have hl2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hl2' : Real.log 2 ≤ 1 := by linarith [Real.log_two_lt_d9]
  set X : ℝ := (24 + max C 0 + c) / (c * Real.log 2) with hX
  have hX0 : 0 < X := by rw [hX]; have : (0:ℝ) ≤ max C 0 := le_max_right _ _; positivity
  set Dc : ℕ := ⌈X + 1⌉₊ with hDc
  have hDcge : X + 1 ≤ (Dc : ℝ) := Nat.le_ceil _
  have hDc1 : 1 ≤ Dc := by
    have : (1 : ℝ) ≤ (Dc : ℝ) := by linarith
    exact_mod_cast this
  set k₄ : ℕ := max (max (k₄bℓ 3 ℓ) Dc) (A + 25) with hk₄
  have hk : k₄bℓ 3 ℓ ≤ k₄ := le_trans (le_max_left _ _) (le_max_left _ _)
  have hDck : Dc ≤ k₄ := le_trans (le_max_right _ _) (le_max_left _ _)
  have hAk : A + 25 ≤ k₄ := le_max_right _ _
  set K : ℕ := 4 * k₄ with hKdef
  have h : Hyp 3 K := hyp_KG (by norm_num) hℓ hk
  have hK100 : 100 ≤ K := h.hK
  obtain ⟨e₀, hsum₀, hbnd₀⟩ := MertensAP.exists_cutoff_subset hmert hK100 (m₁ 3 K)
  obtain ⟨M1, hM1⟩ : ∃ M1, m₁ 3 K = M1 := ⟨_, rfl⟩
  rw [hM1] at hsum₀ hbnd₀
  set Am : ℕ := M1 + K ^ 2 + 1 with hAmdef
  have hAmK : M1 ≤ Am ∧ K ^ 2 ≤ Am ∧ 1 ≤ Am := by omega
  have hAmeq : Am = M1 + K ^ 2 + 1 := rfl
  clear_value Am
  have hA1 : (1 : ℝ) ≤ (Am : ℝ) := by exact_mod_cast hAmK.2.2
  have hm₁A : (M1 : ℝ) ≤ (Am : ℝ) := by exact_mod_cast hAmK.1
  have hKA : ((K : ℝ)) ^ 2 ≤ (Am : ℝ) := by
    have h' : ((K ^ 2 : ℕ) : ℝ) ≤ (Am : ℝ) := by exact_mod_cast hAmK.2.1
    push_cast at h'; linarith
  have hm₁0 : (0 : ℝ) ≤ (M1 : ℝ) := Nat.cast_nonneg _
  have hCmax : C ≤ max C 0 := le_max_left _ _
  have hCmax0 : (0 : ℝ) ≤ max C 0 := le_max_right _ _
  have hQ : ((M1 : ℝ) * Real.log 2 + 21 * (K : ℝ) ^ 2 + 2 + C + c)
      ≤ (Am : ℝ) * (24 + max C 0 + c) := by
    have h1 : (M1 : ℝ) * Real.log 2 ≤ (Am : ℝ) :=
      (mul_le_of_le_one_right hm₁0 hl2').trans hm₁A
    have h2 : 21 * (K : ℝ) ^ 2 ≤ 21 * (Am : ℝ) := by linarith
    have h3 : (2 : ℝ) ≤ 2 * (Am : ℝ) := by linarith
    have h4 : C ≤ max C 0 * (Am : ℝ) := hCmax.trans (le_mul_of_one_le_right hCmax0 hA1)
    have h5 : c ≤ c * (Am : ℝ) := le_mul_of_one_le_right hc.le hA1
    have e : (Am : ℝ) * (24 + max C 0 + c) = 24 * Am + max C 0 * Am + c * Am := by ring
    rw [e]; linarith
  have hbnd : (e₀ : ℝ) ≤ (Dc : ℝ) * (Am : ℝ) := by
    have hdiv : ((M1 : ℝ) * Real.log 2 + 21 * (K : ℝ) ^ 2 + 2 + C + c)
        / (c * Real.log 2) ≤ (Am : ℝ) * X := by
      rw [hX, ← mul_div_assoc, div_le_div_iff₀ (by positivity) (by positivity)]
      exact mul_le_mul_of_nonneg_right hQ (by positivity)
    have hmax : max 0 (((M1 : ℝ) * Real.log 2 + 21 * (K : ℝ) ^ 2 + 2 + C + c)
        / (c * Real.log 2)) ≤ (Am : ℝ) * X := by
      refine max_le ?_ hdiv
      positivity
    have : (e₀ : ℝ) ≤ (Am : ℝ) * X + 1 := by linarith
    nlinarith
  have he₀ : e₀ ≤ Dc * Am := by
    have : (e₀ : ℝ) ≤ ((Dc * Am : ℕ) : ℝ) := by push_cast; linarith
    exact_mod_cast this
  set w₂ : ℕ := 4 * logP₀Nat K + 2 * (K + N K) + K with hw₂
  set e : ℕ := max (max e₀ (m₁ 3 K)) (A + A * w₂) with hedef
  have hele := e_bound_two (k₄ := k₄) (A := A) (Dc := Dc) (e₀ := e₀) (by omega) (by omega)
    hDck h (by rw [hM1, ← hAmeq]; exact he₀)
  have hhi : McE K e ≤ 2 ^ m₂ K := moment_cap_two (by omega) hele
  have hlo : m₁ 3 K ≤ e := le_trans (le_max_right _ _) (le_max_left _ _)
  have he₀e : e₀ ≤ e := le_trans (le_max_left _ _) (le_max_left _ _)
  have hE : HypE 3 K e := ⟨h, hlo, hhi⟩
  have hlow : (m₁ 3 K : ℝ) * Real.log 2 - 21 * ((K : ℕ) : ℝ) ^ 2 - 4
      ≤ ∑ p ∈ (smallPrimes (RE e) (gridOf K (N K) hE.hK1).P₀).filter S, (p : ℝ)⁻¹ := by
    rw [hM1]
    refine hsum₀.trans ?_
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun p _ _ => by positivity)
    intro p hp
    rw [Finset.mem_filter] at hp ⊢
    exact ⟨smallPrimes_mono (Nat.pow_le_pow_right (by norm_num)
      (Nat.pow_le_pow_right (by norm_num) he₀e)) hp.1, hp.2⟩
  -- the supply's threshold
  have hZ := sizeZ_le hK100
  have hthr : A * ((gridOf K (N K) hE.hK1).P₀ * ((K + N K) * gridDm K (N K) + 1) * 2 ^ K) ^ A
      ≤ 2 ^ e := by
    calc A * ((gridOf K (N K) hE.hK1).P₀ * ((K + N K) * gridDm K (N K) + 1) * 2 ^ K) ^ A
        ≤ 2 ^ A * (2 ^ w₂) ^ A :=
          Nat.mul_le_mul (Nat.lt_two_pow_self).le (Nat.pow_le_pow_left hZ _)
      _ = 2 ^ (A + A * w₂) := by rw [← pow_mul, ← pow_add, mul_comm w₂]
      _ ≤ 2 ^ e := Nat.pow_le_pow_right (by norm_num) (le_max_right _ _)
  obtain ⟨x, hx1, hx2, hcov⟩ := hA K (N K) hE.hK1 ((1 / 2 : ℝ) ^ K) K le_rfl e hthr
  exact ⟨scheduleWitnessSC2 S ℓ w e k₄ x hℓ hk hE hlow hx1 hx2 hcov⟩

end SchedB

end NormalNumbers.G4
