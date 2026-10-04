/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.RealDefs
import NormalNumbers.ReciprocalNormal
import NormalNumbers.SwingC1Log
import NormalNumbers.G4EntropyStable
import NormalNumbers.WallRational
import NormalNumbers.ExplicitPQ
import NormalNumbers.CantorLiouvilleAll

/-!
# New siblings for the barrier library

Standard counterexamples a normality argument must survive, stated here because the repo had no
Lean form of them.  Each is a known (or near-folklore) fact, first frozen with a `sorry`, a
confidence and an English construction, and now proved; `Barriers.lean` registers them as
`proved` barriers.

Two constructions differ from the frozen English sketches.  Sibling (a) uses the *counter word*
(block `j` = the `K` bits of `j mod 2^K`, period `K·2^K`) instead of a de Bruijn word: it is
exactly uniform on every length-`≤ K` window per period, with a two-line bijection in place of an
Euler-circuit argument.  Sibling (b) starts from a Borel normal number in base `b`, proved here
from the DEL second-moment criterion for Lebesgue measure (the repo had unconditional base-`b`
normal numbers only for `3 ∤ b`).

* `exists_rat_isNormalUpTo_not_isNormal`: correct statistics for every word of length `≤ k`,
  not normal.  Guards mechanisms that check finitely many orders.
* `exists_isLogNormal_not_isSimplyNormal`: normal under logarithmic averaging, not even simply
  normal under natural averaging.  Guards lane E2 (the log rung is distinct) and C1-log.
* `exists_normal_prefix_limit_not_normal`: normal numbers agreeing with a non-normal one on
  ever-longer prefixes.  Guards soft diagonal and limit arguments.
* `tsum_two_pow_div_fermat`: a rational Lambert-type series.  Guards irrationality mechanisms.
* `not_exists_prime_nonresidue_71`: the drift-one arithmetic crux is false at `p = 71`
  (proved).
-/

namespace NormalNumbers.Barriers.Siblings

open Filter Topology Finset

/-! ## Order-`k` statistics do not give normality -/

/-- **Normality up to order `k`**: the normality limit of `IsNormalSequence`, for words of length
at most `k` only. -/
def IsNormalUpTo (b k : ℕ) (s : ℕ → ℕ) : Prop :=
  ∀ w : List ℕ, w ≠ [] → w.length ≤ k → (∀ d ∈ w, d < b) →
    Tendsto (fun n => (countOccurrences w ((List.range n).map s) : ℝ) / n) atTop
      (𝓝 ((b : ℝ) ^ w.length)⁻¹)

/-! ### The counter word

Block `j` of length `K` holds the `K` low bits of `j mod 2^K`, least significant first; the
period is `K·2^K`.  The window at `j·K + r` reads bits `r, …, K−1` of `j` and then the low bits of
`j + 1`, i.e. the low bits of `gwin K r j`, and `gwin K r` permutes `[0, 2^K)`.  So every word of
length `m ≤ K` occurs exactly `2^{K−m}` times at each offset `r`: an exactly uniform period, which
is all the de Bruijn construction was used for. -/

namespace CounterWord


/-- Counter sequence: block `j` (length `K`) holds the `K` low bits of `j mod 2^K`, LSB first. -/
def ctr (K n : ℕ) : ℕ := (n / K % 2 ^ K) / 2 ^ (n % K) % 2

/-- The window at `j*K + r` read as a number: high bits of `j`, then low bits of `j+1`. -/
def gwin (K r j : ℕ) : ℕ := j / 2 ^ r + ((j + 1) % 2 ^ r) * 2 ^ (K - r)

lemma add_mul_two_pow_mod_two (a y e : ℕ) (he : 1 ≤ e) : (a + y * 2 ^ e) % 2 = a % 2 := by
  obtain ⟨e', rfl⟩ : ∃ e', e = e' + 1 := ⟨e - 1, by omega⟩
  rw [pow_succ, ← mul_assoc, Nat.add_mul_mod_self_right]

lemma mod_two_pow_div_mod_two (x n e : ℕ) (h : e < n) :
    (x % 2 ^ n) / 2 ^ e % 2 = x / 2 ^ e % 2 := by
  obtain ⟨d, rfl⟩ : ∃ d, n = e + (d + 1) := ⟨n - e - 1, by omega⟩
  rw [pow_add 2 e (d + 1)]
  conv_rhs => rw [← Nat.mod_add_div x (2 ^ e * 2 ^ (d + 1))]
  rw [mul_assoc, Nat.add_mul_div_left _ _ (by positivity), mul_comm (2 ^ (d + 1)),
    add_mul_two_pow_mod_two _ _ _ (by omega)]

lemma ctr_eq_gwin (K r t j : ℕ) (hr : r < K) (ht : t < K) (hj : j < 2 ^ K) :
    ctr K (j * K + r + t) = gwin K r j / 2 ^ t % 2 := by
  have hK : 0 < K := by omega
  unfold ctr gwin
  have hjr : j / 2 ^ r < 2 ^ (K - r) := by
    rw [Nat.div_lt_iff_lt_mul (by positivity), ← pow_add, Nat.sub_add_cancel hr.le]; exact hj
  by_cases hc : r + t < K
  · have h1 : (j * K + r + t) / K = j := by
      rw [add_assoc, Nat.mul_comm, Nat.mul_add_div hK, Nat.div_eq_of_lt hc]; simp
    have h2 : (j * K + r + t) % K = r + t := by
      rw [add_assoc, Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt hc]
    rw [h1, h2, Nat.mod_eq_of_lt hj]
    have : (2 : ℕ) ^ (K - r) = 2 ^ t * 2 ^ (K - r - t) := by rw [← pow_add]; congr 1; omega
    rw [this, mul_comm (2 ^ t), ← mul_assoc, Nat.add_mul_div_right _ _ (by positivity),
      add_mul_two_pow_mod_two _ _ _ (by omega), Nat.div_div_eq_div_mul, ← pow_add]
  · set e := r + t - K with he
    have h1 : (j * K + r + t) / K = j + 1 := by
      rw [show j * K + r + t = e + K * (j + 1) by rw [he]; ring_nf; omega,
        Nat.add_mul_div_left _ _ hK, Nat.div_eq_of_lt (by omega)]; simp
    have h2 : (j * K + r + t) % K = e := by
      rw [show j * K + r + t = e + K * (j + 1) by rw [he]; ring_nf; omega,
        Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]
    rw [h1, h2, mod_two_pow_div_mod_two _ _ _ (by omega)]
    have ht' : (2 : ℕ) ^ t = 2 ^ (K - r) * 2 ^ e := by rw [← pow_add]; congr 1; omega
    rw [ht', ← Nat.div_div_eq_div_mul, Nat.add_mul_div_right _ _ (by positivity),
      Nat.div_eq_of_lt hjr, zero_add, mod_two_pow_div_mod_two _ _ _ (by omega)]

lemma gwin_lt (K r j : ℕ) (hr : r ≤ K) (hj : j < 2 ^ K) : gwin K r j < 2 ^ K := by
  unfold gwin
  have hjr : j / 2 ^ r < 2 ^ (K - r) := by
    rw [Nat.div_lt_iff_lt_mul (by positivity), ← pow_add, Nat.sub_add_cancel hr]; exact hj
  have hy : (j + 1) % 2 ^ r < 2 ^ r := Nat.mod_lt _ (by positivity)
  have hK : (2 : ℕ) ^ K = 2 ^ r * 2 ^ (K - r) := by rw [← pow_add, Nat.add_sub_cancel' hr]
  rw [hK]
  calc j / 2 ^ r + (j + 1) % 2 ^ r * 2 ^ (K - r) < 2 ^ (K - r) + (j + 1) % 2 ^ r * 2 ^ (K - r) := by omega
    _ = ((j + 1) % 2 ^ r + 1) * 2 ^ (K - r) := by ring
    _ ≤ 2 ^ r * 2 ^ (K - r) := Nat.mul_le_mul_right _ hy

lemma gwin_injOn (K r : ℕ) (hr : r ≤ K) :
    Set.InjOn (gwin K r) (range (2 ^ K) : Set ℕ) := by
  intro j1 hj1 j2 hj2 h
  replace hj1 : j1 < 2 ^ K := by simpa using hj1
  replace hj2 : j2 < 2 ^ K := by simpa using hj2
  unfold gwin at h
  have hlt : ∀ j, j < 2 ^ K → j / 2 ^ r < 2 ^ (K - r) := fun j hj => by
    rw [Nat.div_lt_iff_lt_mul (by positivity), ← pow_add, Nat.sub_add_cancel hr]; exact hj
  have hp : 0 < 2 ^ (K - r) := by positivity
  have ha : j1 / 2 ^ r = j2 / 2 ^ r := by
    have := congrArg (· % 2 ^ (K - r)) h
    simpa [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (hlt _ hj1),
      Nat.mod_eq_of_lt (hlt _ hj2)] using this
  have hy : (j1 + 1) % 2 ^ r = (j2 + 1) % 2 ^ r := by
    have := congrArg (· / 2 ^ (K - r)) h
    rwa [Nat.add_mul_div_right _ _ hp, Nat.div_eq_of_lt (hlt _ hj1),
      Nat.add_mul_div_right _ _ hp, Nat.div_eq_of_lt (hlt _ hj2), zero_add, zero_add] at this
  have hc : j1 % 2 ^ r = j2 % 2 ^ r := Nat.ModEq.add_right_cancel' 1 hy
  rw [← Nat.div_add_mod j1 (2 ^ r), ← Nat.div_add_mod j2 (2 ^ r), ha, hc]

/-- Bits of `v` against a binary word, as a low-bits residue. -/
lemma bits_iff_mod (w : List ℕ) (hw : ∀ d ∈ w, d < 2) (v : ℕ) :
    (∀ t < w.length, v / 2 ^ t % 2 = w.getD t 0) ↔ v % 2 ^ w.length = Nat.ofDigits 2 w := by
  induction w generalizing v with
  | nil => simp [Nat.mod_one]
  | cons a w ih =>
    have ha : a < 2 := hw a (by simp)
    have ih' := ih (fun d hd => hw d (by simp [hd])) (v / 2)
    rw [Nat.ofDigits_cons, List.length_cons, pow_succ', Nat.mod_mul]
    constructor
    · intro h
      have h0 := h 0 (by simp)
      have hrest : ∀ t < w.length, v / 2 / 2 ^ t % 2 = w.getD t 0 := by
        intro t ht
        have := h (t + 1) (by simp; omega)
        rwa [pow_succ', ← Nat.div_div_eq_div_mul] at this
      have := ih'.1 hrest
      simp at h0
      omega
    · intro h t ht
      have hv : v % 2 = a ∧ v / 2 % 2 ^ w.length = Nat.ofDigits 2 w := by
        have : v % 2 < 2 := Nat.mod_lt _ (by norm_num)
        omega
      rcases t with _ | t
      · simpa using hv.1
      · rw [pow_succ', ← Nat.div_div_eq_div_mul]
        simpa using (ih'.2 hv.2) t (by simp at ht; omega)

lemma card_mod_eq (K m W : ℕ) (hm : m ≤ K) (hW : W < 2 ^ m) :
    ((range (2 ^ K)).filter (fun v => v % 2 ^ m = W)).card = 2 ^ (K - m) := by
  have hK : (2 : ℕ) ^ K = 2 ^ (K - m) * 2 ^ m := by rw [← pow_add, Nat.sub_add_cancel hm]
  have : (range (2 ^ K)).filter (fun v => v % 2 ^ m = W) =
      (range (2 ^ (K - m))).image (fun q => q * 2 ^ m + W) := by
    ext v
    simp only [mem_filter, mem_range, mem_image]
    constructor
    · rintro ⟨hv, hvW⟩
      refine ⟨v / 2 ^ m, ?_, ?_⟩
      · rw [Nat.div_lt_iff_lt_mul (by positivity), ← hK]; exact hv
      · rw [← hvW, mul_comm]; exact Nat.div_add_mod v _
    · rintro ⟨q, hq, rfl⟩
      refine ⟨?_, ?_⟩
      · rw [hK]
        calc q * 2 ^ m + W < (q + 1) * 2 ^ m := by nlinarith
          _ ≤ 2 ^ (K - m) * 2 ^ m := Nat.mul_le_mul_right _ hq
      · rw [add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hW]
  rw [this, card_image_of_injective _ (fun a b h => by
    simpa using (Nat.add_right_cancel h : a * 2 ^ m = b * 2 ^ m)), card_range]

/-- Window counts at a fixed offset `r`. -/
lemma card_offset (K r : ℕ) (hr : r < K) (w : List ℕ) (hw : ∀ d ∈ w, d < 2)
    (hm : w.length ≤ K) :
    ((range (2 ^ K)).filter (fun j => MatchesAt (ctr K) w (j * K + r))).card
      = 2 ^ (K - w.length) := by
  have hW : Nat.ofDigits 2 w < 2 ^ w.length := Nat.ofDigits_lt_base_pow_length (by norm_num) hw
  rw [← card_mod_eq K w.length _ hm hW]
  have himg : (range (2 ^ K)).image (gwin K r) = range (2 ^ K) := by
    apply eq_of_subset_of_card_le
    · intro v hv; simp only [mem_image, mem_range] at hv ⊢
      obtain ⟨j, hj, rfl⟩ := hv; exact gwin_lt K r j hr.le hj
    · rw [card_image_of_injOn (gwin_injOn K r hr.le)]
  conv_rhs => rw [← himg]
  rw [filter_image, card_image_of_injOn ((gwin_injOn K r hr.le).mono (fun x hx => by simp at hx ⊢; exact hx.1))]
  congr 1
  apply filter_congr
  intro j hj
  rw [mem_range] at hj
  rw [← bits_iff_mod w hw]
  unfold MatchesAt
  refine forall_congr' fun t => imp_congr_right fun ht => ?_
  rw [← ctr_eq_gwin K r t j hr (by omega) hj, add_assoc]

lemma sum_range_mul_split (f : ℕ → ℕ) (a K : ℕ) :
    ∑ n ∈ range (a * K), f n = ∑ j ∈ range a, ∑ r ∈ range K, f (j * K + r) := by
  induction a with
  | zero => simp
  | succ a ih => rw [add_mul, one_mul, sum_range_add, ih, sum_range_succ]

/-- Per-period window count. -/
lemma card_period (K : ℕ) (w : List ℕ) (hw : ∀ d ∈ w, d < 2)
    (hm : w.length ≤ K) :
    ((range (2 ^ K * K)).filter (MatchesAt (ctr K) w)).card = K * 2 ^ (K - w.length) := by
  rw [card_eq_sum_ones, sum_filter, sum_range_mul_split, sum_comm]
  have : ∀ r ∈ range K, (∑ j ∈ range (2 ^ K), if MatchesAt (ctr K) w (j * K + r) then 1 else 0)
      = 2 ^ (K - w.length) := by
    intro r hr
    rw [← sum_filter, ← card_eq_sum_ones, card_offset K r (mem_range.1 hr) w hw hm]
  rw [sum_congr rfl this, sum_const, card_range, smul_eq_mul]


lemma ctr_add_period (K n : ℕ) (hK : 0 < K) : ctr K (n + 2 ^ K * K) = ctr K n := by
  unfold ctr
  rw [Nat.add_mul_div_right _ _ hK, Nat.add_mul_mod_self_right, Nat.add_mod_right]

lemma matchesAt_add_period (K n : ℕ) (hK : 0 < K) (w : List ℕ) :
    MatchesAt (ctr K) w (n + 2 ^ K * K) ↔ MatchesAt (ctr K) w n := by
  unfold MatchesAt
  refine forall_congr' fun t => imp_congr_right fun _ => ?_
  rw [show n + 2 ^ K * K + t = n + t + 2 ^ K * K by ring, ctr_add_period K _ hK]

lemma sum_periodic (P : ℕ) (f : ℕ → ℕ) (hper : ∀ n, f (n + P) = f n) (q ρ : ℕ) :
    ∑ i ∈ range (q * P + ρ), f i = q * ∑ i ∈ range P, f i + ∑ i ∈ range ρ, f i := by
  have hshift : ∀ q i, f (q * P + i) = f i := by
    intro q; induction q with
    | zero => simp
    | succ q ih => intro i; rw [add_mul, one_mul, add_right_comm, hper, ih]
  have hq : ∀ q, ∑ i ∈ range (q * P), f i = q * ∑ i ∈ range P, f i := by
    intro q; induction q with
    | zero => simp
    | succ q ih => rw [add_mul, one_mul, sum_range_add, ih]; simp only [hshift]; ring
  rw [sum_range_add, hq]; simp only [hshift]

lemma tendsto_periodic (P : ℕ) (hP : 0 < P) (f : ℕ → ℕ) (hf1 : ∀ n, f n ≤ 1)
    (hper : ∀ n, f (n + P) = f n) :
    Tendsto (fun n : ℕ => ((∑ i ∈ range n, f i : ℕ) : ℝ) / n) atTop
      (𝓝 (((∑ i ∈ range P, f i : ℕ) : ℝ) / P)) := by
  set c := ∑ i ∈ range P, f i with hc
  have hcP : c ≤ P := by
    calc c ≤ ∑ i ∈ range P, 1 := sum_le_sum fun i _ => hf1 i
      _ = P := by simp
  have hPr : (0 : ℝ) < P := by exact_mod_cast hP
  have hbound : ∀ n : ℕ, |((∑ i ∈ range n, f i : ℕ) : ℝ) - n * (c / P)| ≤ P := by
    intro n
    have hn : n = n / P * P + n % P := by rw [Nat.div_add_mod']
    have hρ : n % P < P := Nat.mod_lt _ hP
    have hS := sum_periodic P f hper (n / P) (n % P)
    rw [← hn] at hS
    have hr : ∑ i ∈ range (n % P), f i ≤ n % P := by
      calc ∑ i ∈ range (n % P), f i ≤ ∑ i ∈ range (n % P), 1 := sum_le_sum fun i _ => hf1 i
        _ = n % P := by simp
    rw [hS]
    have hnR : (n : ℝ) = (n / P : ℕ) * P + (n % P : ℕ) := by exact_mod_cast hn
    rw [hnR]
    push_cast
    have e1 : ((n / P : ℕ) * (P : ℝ) + (n % P : ℕ)) * (c / P) = (n / P : ℕ) * c + (n % P : ℕ) * c / P := by
      field_simp
    rw [e1, abs_le]
    have hcR : (c : ℝ) ≤ P := by exact_mod_cast hcP
    have hrR : ((∑ i ∈ range (n % P), f i : ℕ) : ℝ) ≤ (n % P : ℕ) := by exact_mod_cast hr
    have hρR : ((n % P : ℕ) : ℝ) < P := by exact_mod_cast hρ
    have h0 : (0 : ℝ) ≤ (n % P : ℕ) * c / P := by positivity
    have h1 : (n % P : ℕ) * (c : ℝ) / P ≤ (n % P : ℕ) := by
      rw [div_le_iff₀ hPr]; exact mul_le_mul_of_nonneg_left hcR (by positivity)
    have h2 : (0 : ℝ) ≤ ((∑ i ∈ range (n % P), f i : ℕ) : ℝ) := by positivity
    have hcS : (c : ℝ) = ∑ x ∈ range P, (f x : ℝ) := by rw [hc]; push_cast; rfl
    constructor <;> push_cast at hrR h2 ⊢ <;> rw [← hcS] <;> linarith
  have hlim : Tendsto (fun n : ℕ => (P : ℝ) / n) atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat _
  have hl1 : Tendsto (fun n : ℕ => (c : ℝ) / P - P / n) atTop (𝓝 ((c : ℝ) / P)) := by
    simpa using hlim.const_sub ((c : ℝ) / P)
  have hl2 : Tendsto (fun n : ℕ => (c : ℝ) / P + P / n) atTop (𝓝 ((c : ℝ) / P)) := by
    simpa using hlim.const_add ((c : ℝ) / P)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hl1 hl2 ?_ ?_
  · filter_upwards [eventually_gt_atTop 0] with n hn
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    have := (abs_le.1 (hbound n)).1
    rw [sub_le_iff_le_add, ← add_div, le_div_iff₀ hnR]
    nlinarith
  · filter_upwards [eventually_gt_atTop 0] with n hn
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    have := (abs_le.1 (hbound n)).2
    rw [div_le_iff₀ hnR, add_mul, div_mul_cancel₀ _ hnR.ne']
    nlinarith

lemma isNormalUpTo_ctr (k : ℕ) : IsNormalUpTo 2 k (ctr (k + 1)) := by
  intro w hw hlen hd
  set K := k + 1
  have hK : 0 < K := Nat.succ_pos k
  have hm : w.length ≤ K := by omega
  set f : ℕ → ℕ := fun i => if MatchesAt (ctr K) w i then 1 else 0 with hf
  have hP : 0 < 2 ^ K * K := by positivity
  have hT := tendsto_periodic (2 ^ K * K) hP f (fun n => by simp only [hf]; split_ifs <;> simp)
    (fun n => by simp only [hf, matchesAt_add_period K n hK w])
  have hcount : ∀ n, ∑ i ∈ range n, f i = ((range n).filter (MatchesAt (ctr K) w)).card := by
    intro n; rw [card_eq_sum_ones, sum_filter]
  rw [hcount, card_period K w hd hm] at hT
  have hval : ((K * 2 ^ (K - w.length) : ℕ) : ℝ) / ((2 ^ K * K : ℕ) : ℝ) = ((2 : ℝ) ^ w.length)⁻¹ := by
    have hpow : (2 : ℝ) ^ K = 2 ^ (K - w.length) * 2 ^ w.length := by
      rw [← pow_add, Nat.sub_add_cancel hm]
    push_cast
    rw [hpow]
    have : (K : ℝ) ≠ 0 := by exact_mod_cast hK.ne'
    field_simp
  rw [hval] at hT
  simp only [hcount] at hT
  have hb := fun n => card_filter_matchesAt_le (ctr K) w hw n
  have hlow := hT.sub (tendsto_const_div_atTop_nhds_zero_nat (w.length : ℝ))
  rw [sub_zero] at hlow
  push_cast at hT hlow ⊢
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le hlow hT ?_ ?_
  · intro n
    simp only
    rw [← sub_div]
    gcongr
    have := (hb n).2
    have : ((((range n).filter (MatchesAt (ctr K) w)).card : ℕ) : ℝ) ≤
        (countOccurrences w ((List.range n).map (ctr K)) : ℕ) + (w.length : ℕ) := by
      exact_mod_cast this
    linarith
  · intro n
    simp only
    gcongr
    exact_mod_cast (hb n).1


lemma properDigits_ctr (K : ℕ) (hK : 0 < K) : ProperDigits 2 (ctr K) := by
  intro N
  refine ⟨N * (2 ^ K * K), Nat.le_mul_of_pos_right _ (by positivity), ?_⟩
  unfold ctr
  rw [show N * (2 ^ K * K) = N * 2 ^ K * K by ring, Nat.mul_div_cancel _ hK, Nat.mul_mod_left]
  simp

lemma realOfDigits_periodic (s : ℕ → ℕ) (hs : ∀ i, s i < 2) (P : ℕ) (hP : 0 < P)
    (hper : ∀ n, s (n + P) = s n) :
    realOfDigits 2 s = (∑ i ∈ range P, (s i : ℝ) / 2 ^ (i + 1)) * 2 ^ P / (2 ^ P - 1) := by
  have hsum : Summable (fun i : ℕ => (s i : ℝ) / (2 : ℝ) ^ (i + 1)) := by
    refine Summable.of_nonneg_of_le (fun i => by positivity) (fun i => ?_)
      summable_geometric_two
    have : (s i : ℝ) ≤ 1 := by exact_mod_cast Nat.lt_succ_iff.mp (hs i)
    rw [div_le_iff₀ (by positivity), one_div, inv_pow, pow_succ]
    field_simp
    linarith
  have hsplit := hsum.sum_add_tsum_nat_add P
  have htail : ∑' i, (s (i + P) : ℝ) / (2 : ℝ) ^ (i + P + 1) =
      (∑' i, (s i : ℝ) / (2 : ℝ) ^ (i + 1)) / 2 ^ P := by
    rw [← tsum_div_const]
    congr 1; funext i
    rw [hper, show i + P + 1 = (i + 1) + P by ring, pow_add, div_div]
  unfold realOfDigits
  push_cast at hsplit htail ⊢
  set x := ∑' i, (s i : ℝ) / (2 : ℝ) ^ (i + 1)
  rw [htail] at hsplit
  have h2 : (1 : ℝ) < 2 ^ P := one_lt_pow₀ (by norm_num) hP.ne'
  rw [eq_div_iff (by linarith)]
  have : (2 : ℝ) ^ P ≠ 0 := by positivity
  field_simp at hsplit
  linarith

end CounterWord

/-- **Sibling (a).**  For every `k` some rational has the correct frequency for every binary word
of length `≤ k`, and no rational is normal.

Confidence 99%.  Construction: let `D_k` be a binary de Bruijn word of order `k` (length `2^k`,
every length-`k` word occurs exactly once cyclically) and `q = D_k / (2^{2^k} − 1)`, whose
expansion is `D_k` repeated.  A length-`k` word occurs once per period, so its frequency is
`2^{−k}`; a word of length `j < k` extends to `2^{k−j}` words of length `k`, so its frequency is
`2^{−j}`.  A purely periodic sequence of period `p` has at most `p` distinct words of each length,
so some word of length `m` with `2^m > p` never occurs and `q` is not normal.  (`D_k` contains
both digits for `k ≥ 1`, so the expansion has no `1^∞` tail; `k = 0` is vacuous.) -/
theorem exists_rat_isNormalUpTo_not_isNormal (k : ℕ) :
    ∃ q : ℚ, IsNormalUpTo 2 k (digitOf 2 (Int.fract (q : ℝ))) ∧ ¬ IsNormal 2 (q : ℝ) := by
  set K := k + 1
  have hK : 0 < K := Nat.succ_pos k
  have hs : ∀ i, CounterWord.ctr K i < 2 := fun i => Nat.mod_lt _ (by norm_num)
  have hP : 0 < 2 ^ K * K := by positivity
  set S : ℚ := ∑ i ∈ range (2 ^ K * K), (CounterWord.ctr K i : ℚ) / 2 ^ (i + 1)
  refine ⟨S * 2 ^ (2 ^ K * K) / (2 ^ (2 ^ K * K) - 1), ?_, ExplicitPQ.not_isNormal_two_ratCast _⟩
  have hq : ((S * 2 ^ (2 ^ K * K) / (2 ^ (2 ^ K * K) - 1) : ℚ) : ℝ) = realOfDigits 2 (CounterWord.ctr K) := by
    rw [CounterWord.realOfDigits_periodic (CounterWord.ctr K) hs _ hP (fun n => CounterWord.ctr_add_period K n hK)]
    simp [S]
  have hmem := realOfDigits_mem_Ico 2 le_rfl (CounterWord.ctr K) hs (CounterWord.properDigits_ctr K hK)
  rw [hq, Int.fract_eq_self.2 hmem, digitOf_realOfDigits 2 le_rfl _ hs (CounterWord.properDigits_ctr K hK)]
  exact CounterWord.isNormalUpTo_ctr k

/-! ## Logarithmic averaging is a strictly weaker rung -/

open Classical in
/-- Logarithmic frequency of the word `w` among the first `n` start positions of `s`: occurrences
at `i` weigh `1/(i+1)`, normalised by the harmonic sum. -/
noncomputable def logOccFreq (w : List ℕ) (s : ℕ → ℕ) (n : ℕ) : ℝ :=
  (∑ i ∈ range n, if (∀ j (hj : j < w.length), s (i + j) = w[j]) then (1 : ℝ) / (i + 1) else 0) /
    ∑ i ∈ range n, (1 : ℝ) / (i + 1)

/-- **Logarithmic normality** of a real number in base `b`: every word's logarithmic frequency
in the digits of `Int.fract x` tends to `b^{−|w|}`. -/
def IsLogNormal (b : ℕ) (x : ℝ) : Prop :=
  ∀ w : List ℕ, w ≠ [] → (∀ d ∈ w, d < b) →
    Tendsto (logOccFreq w (digitOf b (Int.fract x))) atTop (𝓝 ((b : ℝ) ^ w.length)⁻¹)

/-! ### The log-normal witness

A Borel normal number in base `b` (`exists_isNormal`: the Davenport–Erdős–LeVeque criterion
`ae_isNormal_of_secondMoment` for Lebesgue measure on `[0,1]`, where the second moment of the
Weyl sum is exactly `N`), with its digits zeroed on the blocks `[N_J, 2N_J)`, `N_J = 2^{2^J}`.
The windows meeting a block carry harmonic weight `≤ (3m+4)` per block (`block_weight`), and at
most `√(log₂ n + 1) + 1` blocks start below `n` (`J_le_of_NJ_le`), against harmonic sum
`≥ log(n+1)` (`ratio_tendsto`). -/

namespace LogNormalWitness


section Borel
open MeasureTheory Filter Topology DecayAeNormal

lemma integral_ee_int (m : ℤ) :
    ∫ x in (0:ℝ)..1, ee (m * x) = if m = 0 then 1 else 0 := by
  split_ifs with hm
  · simp [hm, ee]
  · have hc : (2 * Real.pi * Complex.I * m) ≠ 0 := by
      simp [Real.pi_ne_zero, Complex.I_ne_zero, hm]
    have : (fun x : ℝ => ee (m * x)) = fun x : ℝ => Complex.exp ((2 * Real.pi * Complex.I * m) * x) := by
      funext x; simp only [ee]; push_cast; ring_nf
    rw [this, integral_exp_mul_complex hc]
    have h1 : Complex.exp (2 * Real.pi * Complex.I * m) = 1 := by
      rw [show 2 * Real.pi * Complex.I * (m:ℂ) = m * (2 * Real.pi * Complex.I) by ring]
      exact Complex.exp_int_mul_two_pi_mul_I m
    simp [h1]


instance : IsProbabilityMeasure (volume.restrict (Set.Icc (0:ℝ) 1)) :=
  ⟨by simp [Measure.restrict_apply]⟩

lemma ee_mul_conj (a c : ℝ) : ee a * (starRingEnd ℂ) (ee c) = ee (a - c) := by
  simp only [ee, ← Complex.exp_conj, ← Complex.exp_add]
  congr 1
  simp [Complex.conj_ofReal, map_ofNat]
  ring

lemma secondMoment_unif (b : ℕ) (hb : 2 ≤ b) (h : ℤ) (hh : h ≠ 0) (N : ℕ) :
    ∫ ω, ‖∑ k ∈ Finset.range N, ee (h * (b : ℝ) ^ k * ω)‖ ^ 2 ∂(volume.restrict (Set.Icc (0:ℝ) 1))
      = N := by
  set μ := volume.restrict (Set.Icc (0:ℝ) 1)
  have hcont : ∀ m : ℤ, Integrable (fun ω : ℝ => ee (m * ω)) μ := fun m =>
    (Continuous.integrableOn_Icc (by unfold ee; fun_prop))
  have hpt : ∀ ω : ℝ, ((‖∑ k ∈ Finset.range N, ee (h * (b : ℝ) ^ k * ω)‖ ^ 2 : ℝ) : ℂ) =
      ∑ k ∈ Finset.range N, ∑ l ∈ Finset.range N,
        ee (((h * (b : ℤ) ^ k - h * (b : ℤ) ^ l : ℤ) : ℝ) * ω) := by
    intro ω
    rw [← Complex.normSq_eq_norm_sq, ← Complex.mul_conj, map_sum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
    rw [ee_mul_conj]; congr 1; push_cast; ring
  have hint : ∀ m : ℤ, ∫ ω, ee (m * ω) ∂μ = if m = 0 then 1 else 0 := by
    intro m
    rw [← integral_ee_int m, intervalIntegral.integral_of_le zero_le_one,
      ← integral_Icc_eq_integral_Ioc]
  apply Complex.ofReal_injective
  rw [← integral_complex_ofReal]
  simp_rw [hpt]
  rw [integral_finsetSum _ fun k _ => integrable_finsetSum _ fun l _ => hcont _]
  simp_rw [integral_finsetSum _ fun l _ => hcont _]
  simp_rw [hint]
  have hinj : ∀ k l : ℕ, (h * (b : ℤ) ^ k - h * (b : ℤ) ^ l = 0 ↔ k = l) := by
    intro k l
    rw [sub_eq_zero, mul_right_inj' hh]
    constructor
    · intro e
      exact Nat.pow_right_injective hb (by exact_mod_cast e)
    · rintro rfl; rfl
  simp_rw [hinj]
  simp
  rw [Finset.filter_true_of_mem fun x hx => Finset.mem_range.1 hx, Finset.card_range]

theorem exists_isNormal (b : ℕ) (hb : 2 ≤ b) : ∃ x : ℝ, IsNormal b x := by
  have hae := CantorLiouvilleAll.ae_isNormal_of_secondMoment (volume.restrict (Set.Icc (0:ℝ) 1))
    hb id measurable_id (fun j => (j + 1) ^ 2)
    (fun a c hac => by simp only; gcongr)
    ?_ ?_
  · exact (hae.exists).imp fun x hx => hx
  · have : (fun j : ℕ => (((j + 1 + 1) ^ 2 : ℕ) : ℝ) / (((j + 1) ^ 2 : ℕ) : ℝ)) =
        fun j : ℕ => (1 + 1 / ((j : ℝ) + 1)) ^ 2 := by
      funext j; push_cast; field_simp
    simp only [this]
    have h0 : Tendsto (fun j : ℕ => 1 / ((j : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    simpa using ((h0.const_add 1).pow 2)
  · intro h hh
    simp only [id, secondMoment_unif b hb h hh]
    have : (fun j : ℕ => (((j + 1) ^ 2 : ℕ) : ℝ) / (((j + 1) ^ 2 : ℕ) : ℝ) ^ 2) =
        fun j : ℕ => 1 / ((j : ℝ) + 1) ^ 2 := by
      funext j; push_cast; field_simp
    simp only [this]
    exact (summable_nat_add_iff 1).2 (Real.summable_one_div_nat_pow.2 one_lt_two) |>.congr
      fun j => by push_cast; ring


end Borel

open Filter Topology Finset

/-- Start of the `J`-th zero block. -/
def NJ (J : ℕ) : ℕ := 2 ^ (2 ^ J)

def InBlk (i : ℕ) : Prop := ∃ J, NJ J ≤ i ∧ i < 2 * NJ J

open Classical in
noncomputable def zeroed (t : ℕ → ℕ) (i : ℕ) : ℕ := if InBlk i then 0 else t i

lemma sq_le_two_pow_add_one (J : ℕ) : J * J ≤ 2 ^ J + 1 := by
  induction J with
  | zero => simp
  | succ J ih =>
    rcases Nat.lt_or_ge J 3 with h | h
    · interval_cases J <;> simp
    · have h2 : 2 * J + 1 ≤ 2 ^ J := by
        clear ih
        induction J, h using Nat.le_induction with
        | base => norm_num
        | succ J hJ ihJ => rw [pow_succ]; omega
      rw [pow_succ]; nlinarith

lemma J_le_of_NJ_le {J M : ℕ} (h : NJ J ≤ M) : J ≤ Nat.sqrt (Nat.log 2 M + 1) := by
  rw [Nat.le_sqrt]
  have h1 : 2 ^ J ≤ Nat.log 2 M := by
    exact Nat.le_log_of_pow_le (by norm_num) h
  have := sq_le_two_pow_add_one J
  omega

lemma block_weight (N m : ℕ) (hN : 1 ≤ N) :
    ∑ i ∈ Ico (N - m) (2 * N), (1 : ℝ) / (i + 1) ≤ 3 * m + 4 := by
  rcases Nat.lt_or_ge N (2 * m) with h | h
  · calc ∑ i ∈ Ico (N - m) (2 * N), (1 : ℝ) / (i + 1) ≤ ∑ i ∈ Ico (N - m) (2 * N), (1 : ℝ) :=
          sum_le_sum fun i _ => by
            rw [div_le_one (by positivity)]; linarith [(Nat.cast_nonneg i : (0:ℝ) ≤ i)]
      _ = ((2 * N - (N - m) : ℕ) : ℝ) := by simp
      _ ≤ 3 * m + 4 := by
          have : 2 * N - (N - m) ≤ 3 * m := by omega
          exact_mod_cast (by omega : 2 * N - (N - m) ≤ 3 * m + 4)
  · have hlow : ∀ i ∈ Ico (N - m) (2 * N), (1 : ℝ) / (i + 1) ≤ 2 / N := by
      intro i hi
      rw [mem_Ico] at hi
      have : (N : ℝ) ≤ 2 * ((i : ℝ) + 1) := by
        have : N ≤ 2 * (i + 1) := by omega
        exact_mod_cast this
      rw [div_le_div_iff₀ (by positivity) (by positivity)]; linarith
    calc ∑ i ∈ Ico (N - m) (2 * N), (1 : ℝ) / (i + 1) ≤ ∑ i ∈ Ico (N - m) (2 * N), (2 : ℝ) / N :=
          sum_le_sum hlow
      _ = ((2 * N - (N - m) : ℕ) : ℝ) * (2 / N) := by simp
      _ ≤ (2 * N : ℝ) * (2 / N) := by
          gcongr; exact_mod_cast (by omega : 2 * N - (N - m) ≤ 2 * N)
      _ = 4 := by field_simp; ring
      _ ≤ 3 * m + 4 := by have : (0 : ℝ) ≤ m := Nat.cast_nonneg m; linarith

def Bad (m i : ℕ) : Prop := ∃ j < m, InBlk (i + j)

open Classical in
lemma bad_weight_le (m n : ℕ) :
    ∑ i ∈ (range n).filter (Bad m), (1 : ℝ) / (i + 1)
      ≤ (3 * m + 4) * (Nat.sqrt (Nat.log 2 (n + m) + 1) + 1) := by
  set S := Nat.sqrt (Nat.log 2 (n + m) + 1)
  set I : ℕ → Finset ℕ := fun J => Ico (NJ J - m) (2 * NJ J)
  have hcover : ∀ i ∈ (range n).filter (Bad m), (1 : ℝ) / (i + 1) ≤
      ∑ J ∈ range (S + 1), if i ∈ I J then (1 : ℝ) / (i + 1) else 0 := by
    intro i hi
    rw [mem_filter, mem_range] at hi
    obtain ⟨hin, j, hj, J, h1, h2⟩ := hi
    have hJ : J ∈ range (S + 1) := by
      rw [mem_range, Nat.lt_succ_iff]; exact J_le_of_NJ_le (by omega)
    have hiI : i ∈ I J := by simp only [I, mem_Ico]; omega
    calc (1 : ℝ) / (i + 1) = if i ∈ I J then (1 : ℝ) / (i + 1) else 0 := by rw [if_pos hiI]
      _ ≤ _ := single_le_sum (f := fun J => if i ∈ I J then (1 : ℝ) / (i + 1) else 0)
          (fun J _ => by split_ifs <;> positivity) hJ
  calc ∑ i ∈ (range n).filter (Bad m), (1 : ℝ) / (i + 1)
      ≤ ∑ i ∈ (range n).filter (Bad m), ∑ J ∈ range (S + 1),
          if i ∈ I J then (1 : ℝ) / (i + 1) else 0 := sum_le_sum hcover
    _ = ∑ J ∈ range (S + 1), ∑ i ∈ (range n).filter (Bad m),
          if i ∈ I J then (1 : ℝ) / (i + 1) else 0 := sum_comm
    _ ≤ ∑ J ∈ range (S + 1), ((3 * m + 4 : ℕ) : ℝ) := by
        refine sum_le_sum fun J _ => ?_
        rw [sum_ite_mem]
        calc ∑ i ∈ (range n).filter (Bad m) ∩ I J, (1 : ℝ) / (i + 1)
            ≤ ∑ i ∈ I J, (1 : ℝ) / (i + 1) :=
              sum_le_sum_of_subset_of_nonneg inter_subset_right (fun _ _ _ => by positivity)
          _ ≤ 3 * m + 4 := block_weight _ m (Nat.one_le_two_pow)
          _ = ((3 * m + 4 : ℕ) : ℝ) := by push_cast; ring
    _ = (3 * m + 4) * (S + 1) := by simp; ring


lemma harmonic_ge (n : ℕ) : Real.log (n + 1) ≤ ∑ i ∈ range n, (1 : ℝ) / (i + 1) := by
  have := log_add_one_le_harmonic n
  push_cast [harmonic] at this
  simpa [one_div] using this

lemma ratio_tendsto (m : ℕ) (C : ℝ) (hC : 0 ≤ C) :
    Tendsto (fun n : ℕ => C * ((Nat.sqrt (Nat.log 2 (n + m) + 1) : ℝ) + 1) /
      ∑ i ∈ range n, (1 : ℝ) / (i + 1)) atTop (𝓝 0) := by
  set L : ℕ → ℝ := fun n => Real.log (n + 1)
  have hL : Tendsto L atTop atTop := by
    refine Real.tendsto_log_atTop.comp ?_
    exact tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
  have hlim : Tendsto (fun n => 3 * C / Real.sqrt (L n)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (Real.tendsto_sqrt_atTop.comp hL)
  have hlog2 : (0.69 : ℝ) < Real.log 2 := by
    have := Real.log_two_gt_d9; linarith
  refine squeeze_zero' (Eventually.of_forall fun n => ?_) ?_ hlim
  · exact div_nonneg (by positivity) (sum_nonneg fun i _ => by positivity)
  · filter_upwards [hL.eventually_ge_atTop 1, eventually_ge_atTop m, eventually_ge_atTop 1]
      with n hL1 hnm hn1
    have hH := harmonic_ge n
    have hLpos : 0 < L n := by linarith
    -- Nat.log 2 (n+m) ≤ 3 L
    have hk : ((Nat.log 2 (n + m) : ℕ) : ℝ) ≤ 3 * L n := by
      have h1 : (2 : ℝ) ^ (Nat.log 2 (n + m)) ≤ ((n + m : ℕ) : ℝ) := by
        exact_mod_cast Nat.pow_log_le_self 2 (by omega)
      have h2 : ((n + m : ℕ) : ℝ) ≤ ((n : ℝ) + 1) ^ 2 := by
        push_cast; nlinarith [(Nat.cast_le.2 hnm : (m : ℝ) ≤ n)]
      have h3 : (Nat.log 2 (n + m) : ℝ) * Real.log 2 ≤ 2 * L n := by
        rw [← Real.log_pow, show 2 * L n = Real.log (((n : ℝ) + 1) ^ 2) by
          simp only [L]; rw [Real.log_pow]; push_cast; ring]
        exact Real.log_le_log (by positivity) (h1.trans h2)
      nlinarith
    have hsq : ((Nat.sqrt (Nat.log 2 (n + m) + 1) : ℕ) : ℝ) ≤ 2 * Real.sqrt (L n) := by
      have hs := Nat.sqrt_le' (Nat.log 2 (n + m) + 1)
      have hs' : ((Nat.sqrt (Nat.log 2 (n + m) + 1) : ℕ) : ℝ) ^ 2 ≤ 4 * L n := by
        have : (((Nat.sqrt (Nat.log 2 (n + m) + 1)) ^ 2 : ℕ) : ℝ) ≤
            ((Nat.log 2 (n + m) + 1 : ℕ) : ℝ) := by exact_mod_cast hs
        push_cast at this; linarith
      rw [show 2 * Real.sqrt (L n) = Real.sqrt (4 * L n) by
        rw [Real.sqrt_mul (by norm_num), show (4:ℝ) = 2 ^ 2 by norm_num,
          Real.sqrt_sq (by norm_num)]]
      exact Real.le_sqrt_of_sq_le hs'
    have hsL : 1 ≤ Real.sqrt (L n) := by rw [Real.one_le_sqrt]; exact hL1
    have hsqL : Real.sqrt (L n) * Real.sqrt (L n) = L n := Real.mul_self_sqrt hLpos.le
    have hHpos : 0 < ∑ i ∈ range n, (1 : ℝ) / (i + 1) := by linarith
    rw [div_le_div_iff₀ hHpos (by positivity)]
    calc C * (((Nat.sqrt (Nat.log 2 (n + m) + 1) : ℕ) : ℝ) + 1) * Real.sqrt (L n)
        ≤ C * (3 * Real.sqrt (L n)) * Real.sqrt (L n) := by gcongr; linarith
      _ = 3 * C * L n := by rw [mul_assoc, mul_assoc, hsqL]; ring
      _ ≤ 3 * C * ∑ i ∈ range n, (1 : ℝ) / (i + 1) := by gcongr


lemma cond_iff (u : ℕ → ℕ) (w : List ℕ) (i : ℕ) :
    (∀ j (hj : j < w.length), u (i + j) = w[j]) ↔ MatchesAt u w i := by
  unfold MatchesAt
  refine forall_congr' fun j => ?_
  constructor
  · intro h hj; rw [h hj, List.getD_eq_getElem]
  · intro h hj; rw [h hj, List.getD_eq_getElem]

open Classical in
lemma logOccFreq_eq (u : ℕ → ℕ) (w : List ℕ) (n : ℕ) :
    logOccFreq w u n = (∑ i ∈ range n, if MatchesAt u w i then (1 : ℝ) / (i + 1) else 0) /
      ∑ i ∈ range n, (1 : ℝ) / (i + 1) := by
  unfold logOccFreq
  simp_rw [cond_iff]

open Classical in
lemma tendsto_logOcc_of_normal (b : ℕ) (hb : 2 ≤ b) (z : ℝ) (hz : IsNormal b z) (w : List ℕ)
    (hw0 : w ≠ []) (hw : ∀ d ∈ w, d < b) :
    Tendsto (fun n => (∑ i ∈ range n,
        if MatchesAt (digitOf b (Int.fract z)) w i then (1 : ℝ) / (i + 1) else 0) /
      ∑ i ∈ range n, (1 : ℝ) / (i + 1)) atTop (𝓝 ((b : ℝ) ^ w.length)⁻¹) := by
  set a : ℕ → ℝ := fun i => if MatchesAt (digitOf b (Int.fract z)) w i then 1 else 0
  have h := CastingOut.tendsto_matchesAt_freq b hb z hz w hw0 hw
  have h' : Tendsto (fun N => (∑ n ∈ range N, a n) / N) atTop (𝓝 ((b : ℝ) ^ w.length)⁻¹) := by
    refine h.congr fun N => ?_
    simp only [a, sum_boole]
  refine (CastingOut.tendsto_logAvg_of_tendsto_avg a _ h').congr fun N => ?_
  congr 1
  refine sum_congr rfl fun i _ => ?_
  simp only [a]; split_ifs <;> simp

open Classical in
theorem isLogNormal_zeroed (b : ℕ) (hb : 2 ≤ b) (z : ℝ) (hz : IsNormal b z) (w : List ℕ)
    (hw0 : w ≠ []) (hw : ∀ d ∈ w, d < b) :
    Tendsto (logOccFreq w (zeroed (digitOf b (Int.fract z)))) atTop
      (𝓝 ((b : ℝ) ^ w.length)⁻¹) := by
  set t := digitOf b (Int.fract z)
  set u := zeroed t
  set m := w.length
  set H : ℕ → ℝ := fun n => ∑ i ∈ range n, (1 : ℝ) / (i + 1)
  set fu : ℕ → ℝ := fun i => if MatchesAt u w i then (1 : ℝ) / (i + 1) else 0
  set ft : ℕ → ℝ := fun i => if MatchesAt t w i then (1 : ℝ) / (i + 1) else 0
  have ht := tendsto_logOcc_of_normal b hb z hz w hw0 hw
  have hagree : ∀ i, ¬ Bad m i → (MatchesAt u w i ↔ MatchesAt t w i) := by
    intro i hi
    unfold MatchesAt
    refine forall_congr' fun j => imp_congr_right fun hj => ?_
    have : ¬ InBlk (i + j) := fun hb' => hi ⟨j, hj, hb'⟩
    simp only [u, zeroed, if_neg this]
  have hdiff : ∀ n, |(∑ i ∈ range n, fu i) - ∑ i ∈ range n, ft i| ≤
      ∑ i ∈ (range n).filter (Bad m), (1 : ℝ) / (i + 1) := by
    intro n
    rw [← sum_sub_distrib, sum_filter]
    refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun i _ => ?_)
    split_ifs with hbad
    · have hp : (0:ℝ) ≤ (i:ℝ) + 1 := by positivity
      simp only [fu, ft]; split_ifs <;> simp [abs_of_nonneg hp, hp]
    · simp only [fu, ft, hagree i hbad]; simp
  have hrat := ratio_tendsto m (3 * m + 4) (by positivity)
  have hzero : Tendsto (fun n => (∑ i ∈ range n, fu i) / H n - (∑ i ∈ range n, ft i) / H n)
      atTop (𝓝 0) := by
    refine squeeze_zero_norm (fun n => ?_) hrat
    rw [Real.norm_eq_abs, ← sub_div, abs_div,
      abs_of_nonneg (show (0:ℝ) ≤ H n from sum_nonneg fun i _ => by positivity)]
    gcongr
    exact (hdiff n).trans (bad_weight_le m n)
  have := hzero.add ht
  rw [zero_add] at this
  refine this.congr fun n => ?_
  rw [logOccFreq_eq]
  simp only [H, fu, ft]
  ring


lemma two_mul_NJ_tendsto : Tendsto (fun J => 2 * NJ J) atTop atTop := by
  refine tendsto_atTop_mono (fun J => ?_) tendsto_id
  have h1 := Nat.lt_two_pow_self (n := J)
  have h2 := Nat.lt_two_pow_self (n := 2 ^ J)
  unfold NJ; simp only [id]; omega

lemma NJ_tendsto : Tendsto NJ atTop atTop := by
  refine tendsto_atTop_mono (fun J => ?_) tendsto_id
  have h1 := Nat.lt_two_pow_self (n := J)
  have h2 := Nat.lt_two_pow_self (n := 2 ^ J)
  unfold NJ; simp only [id]; omega

end LogNormalWitness

/-- **Sibling (b).**  In every base some number is normal under logarithmic averaging, in
particular log-simply-normal in the `SwingC1Log` sense, without being simply normal.  So the log
rung of lane E2 is genuinely weaker, and a log-averaged mechanism must not conclude a
natural-average statement.

Confidence 95% (folklore; natural-density convergence implies logarithmic, not conversely).
Construction: start from a normal `z` and set to `0` its digits on the blocks `[N_j, 2N_j)` with
`N_j = 2^{2^j}`.  The blocks up to `N` carry harmonic weight `O(j) = O(log log N)` against
`log N`, so log frequencies are those of `z`, which are normal because Cesàro convergence implies
logarithmic convergence.  At `n = 2N_j` the digit `0` has natural frequency `≥ 1/2 + (1/2)/b`,
so `x` is not simply normal. -/
theorem exists_isLogNormal_not_isSimplyNormal (b : ℕ) (hb : 2 ≤ b) :
    ∃ x : ℝ, IsLogNormal b x ∧ CastingOut.SimplyNormalLog b x ∧
      ¬ ReciprocalNormal.IsSimplyNormal b x := by
  classical
  obtain ⟨z, hz⟩ := LogNormalWitness.exists_isNormal b hb
  set t := digitOf b (Int.fract z) with htdef
  have hb0 : 0 < b := by omega
  have ht : ∀ i, t i < b := fun i => Nat.mod_lt _ hb0
  set u := LogNormalWitness.zeroed t with hudef
  have hu : ∀ i, u i < b := fun i => by
    simp only [u, LogNormalWitness.zeroed]; split_ifs
    · exact hb0
    · exact ht i
  have hblk : ∀ J i, LogNormalWitness.NJ J ≤ i → i < 2 * LogNormalWitness.NJ J → u i = 0 := fun J i h1 h2 => by
    simp only [u, LogNormalWitness.zeroed]; exact if_pos (show LogNormalWitness.InBlk i from ⟨J, h1, h2⟩)
  have hp : ProperDigits b u := by
    intro N
    refine ⟨LogNormalWitness.NJ N, ?_, ?_⟩
    · have := Nat.lt_two_pow_self (n := N)
      have := Nat.lt_two_pow_self (n := 2 ^ N)
      unfold LogNormalWitness.NJ; omega
    · rw [hblk N (LogNormalWitness.NJ N) le_rfl (by unfold LogNormalWitness.NJ; have := Nat.one_le_two_pow (n := 2 ^ N); omega)]
      omega
  set x := realOfDigits b u
  have hx : digitOf b (Int.fract x) = u := by
    rw [Int.fract_eq_self.2 (realOfDigits_mem_Ico b hb u hu hp)]
    exact digitOf_realOfDigits b hb u hu hp
  have hlog : IsLogNormal b x := by
    intro w hw0 hw
    rw [hx]
    exact LogNormalWitness.isLogNormal_zeroed b hb z hz w hw0 hw
  refine ⟨x, hlog, ?_, ?_⟩
  · intro d hd
    have := hlog [d] (by simp) (by simpa using hd)
    simp only [List.length_singleton, pow_one] at this
    refine this.congr fun N => ?_
    unfold CastingOut.digitFreqLog
    rw [LogNormalWitness.logOccFreq_eq, sum_filter]
    congr 1
    refine sum_congr rfl fun i _ => ?_
    congr 1
    simp [MatchesAt]
  · intro hsn
    have hS := hsn 1 (by omega)
    rw [hx] at hS
    have hT := hz [1] (by simp) (by simp; omega)
    simp only [List.length_singleton, pow_one] at hT
    -- counts
    set Cu : ℕ → ℕ := fun n => countOccurrences [1] ((List.range n).map u)
    set Ct : ℕ → ℕ := fun n => countOccurrences [1] ((List.range n).map t)
    have hkey : ∀ J, Cu (2 * LogNormalWitness.NJ J) ≤ Ct (LogNormalWitness.NJ J) + 1 := by
      intro J
      have h1 := (card_filter_matchesAt_le u [1] (by simp) (2 * LogNormalWitness.NJ J)).1
      have h2 := (card_filter_matchesAt_le t [1] (by simp) (LogNormalWitness.NJ J)).2
      have hsub : (range (2 * LogNormalWitness.NJ J)).filter (MatchesAt u [1]) ⊆
          (range (LogNormalWitness.NJ J)).filter (MatchesAt t [1]) := by
        intro i hi
        simp only [mem_filter, mem_range, MatchesAt, List.length_singleton, Nat.lt_one_iff,
          forall_eq, add_zero, List.getD_cons_zero] at hi ⊢
        obtain ⟨hi1, hi2⟩ := hi
        have hlt : i < LogNormalWitness.NJ J := by
          by_contra hc
          rw [hblk J i (by omega) hi1] at hi2; exact absurd hi2 (by norm_num)
        refine ⟨hlt, ?_⟩
        have hnb : ¬ LogNormalWitness.InBlk i := by
          intro hin; simp only [u, LogNormalWitness.zeroed, if_pos hin] at hi2; exact absurd hi2 (by norm_num)
        simpa [u, LogNormalWitness.zeroed, if_neg hnb] using hi2
      have := card_le_card hsub
      simp only [Cu, Ct]; simp at h2; omega
    have hS' := hS.comp LogNormalWitness.two_mul_NJ_tendsto
    have hT' := hT.comp LogNormalWitness.NJ_tendsto
    have hup : Tendsto (fun J => ((Ct (LogNormalWitness.NJ J) : ℝ) / LogNormalWitness.NJ J) / 2 + 1 / (2 * (LogNormalWitness.NJ J : ℝ))) atTop
        (𝓝 ((b : ℝ)⁻¹ / 2 + 0)) := by
      refine (hT'.div_const 2).add ?_
      have : Tendsto (fun J => (2 * (LogNormalWitness.NJ J : ℝ))) atTop atTop :=
        (tendsto_natCast_atTop_atTop.comp LogNormalWitness.NJ_tendsto).const_mul_atTop (by norm_num)
      refine this.inv_tendsto_atTop.congr fun J => ?_
      simp
    have hle := le_of_tendsto_of_tendsto' hS' hup (fun J => by
      simp only [Function.comp]
      have hN : (0 : ℝ) < LogNormalWitness.NJ J := by unfold LogNormalWitness.NJ; positivity
      have := hkey J
      have hc : (Cu (2 * LogNormalWitness.NJ J) : ℝ) ≤ Ct (LogNormalWitness.NJ J) + 1 := by exact_mod_cast this
      rw [div_le_iff₀ (by push_cast; positivity)]
      field_simp
      push_cast
      nlinarith)
    have hbpos : (0 : ℝ) < (b : ℝ)⁻¹ := by positivity
    linarith

/-! ## Limits of normal numbers -/

/-- **Sibling (c).**  Normal numbers can agree with a non-normal number (here `0`) on prefixes of
unbounded length.  So a diagonal argument that only matches ever-longer prefixes of normal stages
proves nothing; it must control the Weyl means on the windows between stages.

Confidence 99%.  Construction: take a normal `z ∈ (0,1)` and zero its first `M_j = j` digits;
changing finitely many digits does not change any limiting frequency. -/
theorem exists_normal_prefix_limit_not_normal :
    ∃ x : ℕ → ℝ, (∀ j, IsNormal 2 (x j)) ∧
      (∀ j i, i < j → digitOf 2 (Int.fract (x j)) i = 0) ∧ ¬ IsNormal 2 0 := by

  obtain ⟨z, hz0, hz1, hz⟩ := G4Entropy.exists_isNormal_mem_Ico
  refine ⟨fun j => z / (2 : ℝ) ^ j, fun j => by
    simpa using WallRational.isNormal_div_pow 2 le_rfl z j hz, fun j i hij => ?_, ExplicitPQ.not_isNormal_two_zero⟩
  have hp : (0 : ℝ) < 2 ^ j := by positivity
  have hle : z / 2 ^ j ≤ z := div_le_self hz0 (one_le_pow₀ (by norm_num))
  have hf : Int.fract (z / (2 : ℝ) ^ j) = z / 2 ^ j :=
    Int.fract_eq_self.2 ⟨by positivity, by linarith⟩
  simp only [digitOf, hf]
  have : ⌊z / (2 : ℝ) ^ j * ((2 : ℕ) : ℝ) ^ (i + 1)⌋ = 0 := by
    rw [Int.floor_eq_zero_iff]
    refine ⟨by positivity, ?_⟩
    have h2 : ((2 : ℕ) : ℝ) ^ (i + 1) ≤ 2 ^ j := by
      push_cast; exact pow_le_pow_right₀ (by norm_num) hij
    calc z / 2 ^ j * ((2 : ℕ) : ℝ) ^ (i + 1) ≤ z / 2 ^ j * 2 ^ j :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = z := by field_simp
      _ < 1 := hz1
  rw [this]; rfl

/-! ## A rational Lambert-type series -/

/-- **Sibling (d).**  A Lambert-type series over the doubling set is rational:
`Σ_{k≥0} 2^k/(2^{2^k}+1) = 1`.  So an irrationality mechanism for Lambert sums
`Σ_{n∈A} a_n/(b^n ± 1)` must use something about `A` or the weights that fails here.

Confidence 100% (classical).  Proof: `1/(x−1) − 2^{k+1}/(x^{2^{k+1}}−1)` telescopes, since
`1/(y−1) − 2/(y²−1) = 1/(y+1)` with `y = x^{2^k}` gives
`2^k/(x^{2^k}−1) − 2^{k+1}/(x^{2^{k+1}}−1) = 2^k/(x^{2^k}+1)`; at `x = 2` the tail
`2^{k+1}/(2^{2^{k+1}}−1) → 0`. -/
theorem tsum_two_pow_div_fermat :
    ∑' k : ℕ, (2 : ℝ) ^ k / (2 ^ (2 ^ k) + 1) = 1 := by

  set f : ℕ → ℝ := fun k => 2 ^ k / (2 ^ (2 ^ k) - 1) with hfdef
  have hy : ∀ k : ℕ, (1 : ℝ) < 2 ^ (2 ^ k) := fun k => one_lt_pow₀ (by norm_num) (by positivity)
  have hterm : ∀ k, (2 : ℝ) ^ k / (2 ^ (2 ^ k) + 1) = f k - f (k + 1) := by
    intro k
    have h1 := hy k
    have hsq : (2 : ℝ) ^ (2 ^ (k + 1)) = (2 ^ (2 ^ k)) ^ 2 := by
      rw [← pow_mul, pow_succ]
    simp only [hfdef, hsq]
    have ha : (2 : ℝ) ^ (2 ^ k) - 1 ≠ 0 := by linarith
    have hb : (2 : ℝ) ^ (2 ^ k) + 1 ≠ 0 := by linarith
    have hc : ((2 : ℝ) ^ (2 ^ k)) ^ 2 - 1 ≠ 0 := by nlinarith
    field_simp
    ring
  have hf0 : f 0 = 1 := by norm_num [hfdef]
  have hlim : Tendsto f atTop (𝓝 0) := by
    have hg : Tendsto (fun n : ℕ => 2 * (1 / 2 : ℝ) ^ n) atTop (𝓝 0) := by
      simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0:ℝ) ≤ 1/2)
        (by norm_num)).const_mul 2
    refine squeeze_zero' (Eventually.of_forall fun n => ?_) ?_ hg
    · exact div_nonneg (by positivity) (by linarith [hy n])
    · filter_upwards [eventually_ge_atTop 1] with n hn
      have hpow : (4 : ℝ) ^ n ≤ 2 ^ (2 ^ n) := by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_mul]
        apply pow_le_pow_right₀ (by norm_num)
        have : 2 * n ≤ 2 ^ n := by
          induction n with
          | zero => simp
          | succ m ih =>
            rcases Nat.eq_zero_or_pos m with rfl | hm
            · simp
            · have := ih hm; rw [pow_succ]; omega
        linarith
      have h4 : (2 : ℝ) ≤ 4 ^ n := by
        calc (2:ℝ) ≤ 4 ^ 1 := by norm_num
          _ ≤ 4 ^ n := pow_le_pow_right₀ (by norm_num) hn
      have hden : (4 : ℝ) ^ n / 2 ≤ 2 ^ (2 ^ n) - 1 := by linarith
      simp only [hfdef]
      rw [div_le_iff₀ (by linarith)]
      calc (2 : ℝ) ^ n = 2 * (1 / 2) ^ n * (4 ^ n / 2) := by
            rw [show (4:ℝ) = 2 * 2 by norm_num, mul_pow, div_pow]; field_simp; simp
        _ ≤ 2 * (1 / 2) ^ n * (2 ^ (2 ^ n) - 1) :=
            mul_le_mul_of_nonneg_left hden (by positivity)
  have hsum : HasSum (fun k : ℕ => (2 : ℝ) ^ k / (2 ^ (2 ^ k) + 1)) 1 := by
    rw [hasSum_iff_tendsto_nat_of_nonneg (fun k => by positivity)]
    have : (fun n => ∑ k ∈ range n, (2 : ℝ) ^ k / (2 ^ (2 ^ k) + 1)) = fun n => 1 - f n := by
      funext n
      simp only [hterm]
      rw [Finset.sum_range_sub', hf0]
    rw [this]
    simpa using hlim.const_sub 1
  exact hsum.tsum_eq

/-! ## The drift-one arithmetic crux fails at `71` -/

/-- **Sibling (proved).**  The statement of `DriftOne.exists_prime_nonresidue` is false at
`p = 71`: the primes in `(71/3, 71/2)` are `29` and `31`, and `71` is a square mod both
(`71 ≡ 10²` mod 29, `71 ≡ 3²` mod 31).  So any proof must use `p ≥ 73`. -/
theorem not_exists_prime_nonresidue_71 :
    ¬ ∃ q, q.Prime ∧ 71 < 3 * q ∧ 2 * q < 71 ∧ ¬ q ∣ 71 + 1 ∧
      ¬ IsSquare ((71 : ℕ) : ZMod q) := by
  rintro ⟨q, hq, h1, h2, -, hns⟩
  apply hns
  have hlo : 23 < q := by omega
  have hhi : q < 36 := by omega
  interval_cases q <;> norm_num at hq
  · exact ⟨10, by decide⟩
  · exact ⟨3, by decide⟩

end NormalNumbers.Barriers.Siblings
