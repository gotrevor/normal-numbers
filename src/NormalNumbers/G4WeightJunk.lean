/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.G4WeightInterface
import NormalNumbers.G4CRTInput

/-!
# G5: the junk of an interface weight on the sample progression

For `w_c = ω + excess c` the disjunctivity proof keeps `ω`'s three-range decomposition and must
carry `excess c` in the §4D remainder.  On the progression `n ≡ b₀ (mod P₀)` the excess splits
exactly, prime by prime, into

* the **frozen** part `∑_{p ∣ P₀} c_p (min(v_p(m), v_p(P₀)) − 1)` — a function of `m mod P₀`
  (`frozenExcess_congr`), so constant on the progression and absorbed by the translate `γ`; and
* the **junk** `∑_p c_p (v_p(m) − E'_p)₊`, `E'_p = max(v_p(P₀), 1)` — the valuations beyond
  what the modulus fixes.

The junk is where the weight's arithmetic costs something, and the cost is a sample mean
(`sum_junk_le`): for `P = {n < X : n ≡ b₀ (P₀)}` and any shift `ρ`,

  `∑_{n∈P} junk(n+ρ) ≤ C · ( (X/P₀) · (∑_{p∣P₀} 1/(p−1) + 1) + √(X+ρ) · log₂(X+ρ) )`.

The mechanism is one-congruence counting: `p^{E'_p+u} ∣ n + ρ` cuts the progression to a single
residue class modulo `P₀ · p^{E'_p+u−v_p(P₀)}`, so its count is `≤ X/(P₀ p^{E'_p+u−v_p(P₀)}) + 1`;
summing the geometric series in `u` gives `1/(p−1)` for `p ∣ P₀` and `1/(p(p−1))` otherwise, and
the `+1`s are only as many as prime powers `p^{≥2} ≤ X+ρ`.  Against `|P| ≥ X/(2P₀)` the mean is
`O(C (log ω(P₀) + 1))` plus `O(P₀ √X log X / X)`, i.e. `O(C log log P₀)` — far below the
`(b/2)^K εη` the §4D budget allows once `rowL1` is factored in.
-/

open Finset
open scoped BigOperators

namespace NormalNumbers.PrimeLambert

open NormalNumbers.G4

/-! ### The split -/

/-- `E'_p = max(v_p(P₀), 1)`: the depth the modulus fixes (at least one). -/
def frozenDepth (P₀ p : ℕ) : ℕ := max (P₀.factorization p) 1

lemma one_le_frozenDepth (P₀ p : ℕ) : 1 ≤ frozenDepth P₀ p := le_max_right _ _

lemma frozenDepth_of_not_dvd {P₀ p : ℕ} (h : ¬ p ∣ P₀) : frozenDepth P₀ p = 1 := by
  unfold frozenDepth
  rw [Nat.factorization_eq_zero_of_not_dvd h]; rfl

lemma frozenDepth_of_mem {P₀ p : ℕ} (h : p ∈ P₀.primeFactors) :
    frozenDepth P₀ p = P₀.factorization p := by
  unfold frozenDepth
  have := (Nat.mem_primeFactors.1 h).1.factorization_pos_of_dvd (Nat.mem_primeFactors.1 h).2.2
    (Nat.mem_primeFactors.1 h).2.1
  omega

/-- The junk: `∑_{p ∣ m} c_p (v_p(m) − E'_p)₊`. -/
noncomputable def junk (c : ℕ → ℕ) (P₀ m : ℕ) : ℝ :=
  ∑ p ∈ m.primeFactors, (c p : ℝ) * ((m.factorization p - frozenDepth P₀ p : ℕ) : ℝ)

/-- The frozen excess: `∑_{p ∣ P₀} c_p (min(v_p(m), v_p(P₀)) − 1)₊`. -/
noncomputable def frozenExcess (c : ℕ → ℕ) (P₀ m : ℕ) : ℝ :=
  ∑ p ∈ P₀.primeFactors, (c p : ℝ) * ((min (m.factorization p) (P₀.factorization p) - 1 : ℕ) : ℝ)

/-- **The exact split** `excess = frozen + junk`. -/
theorem excess_eq_frozen_add_junk (c : ℕ → ℕ) {P₀ : ℕ} (hP₀ : P₀ ≠ 0) {m : ℕ} (hm : m ≠ 0) :
    excess c m = frozenExcess c P₀ m + junk c P₀ m := by
  classical
  rw [excess_eq]
  -- the pointwise identity on `m.primeFactors`
  have hpt : ∀ p ∈ m.primeFactors,
      (c p : ℝ) * ((m.factorization p : ℝ) - 1)
        = (c p : ℝ) * ((min (m.factorization p) (frozenDepth P₀ p) - 1 : ℕ) : ℝ)
          + (c p : ℝ) * ((m.factorization p - frozenDepth P₀ p : ℕ) : ℝ) := by
    intro p hp
    have h1 : 1 ≤ m.factorization p :=
      ((Nat.mem_primeFactors.1 hp).1.dvd_iff_one_le_factorization hm).1
        (Nat.mem_primeFactors.1 hp).2.1
    have hE := one_le_frozenDepth P₀ p
    rw [← mul_add]
    congr 1
    have : ((m.factorization p : ℝ) - 1) = ((m.factorization p - 1 : ℕ) : ℝ) := by
      rw [Nat.cast_sub h1]; simp
    rw [this]
    norm_cast
    omega
  rw [Finset.sum_congr rfl hpt, Finset.sum_add_distrib]
  unfold junk frozenExcess
  congr 1
  -- both frozen sums equal the sum over the union
  have hzero : ∀ {n p : ℕ}, p ∉ n.primeFactors → n.factorization p = 0 := fun {n p} h =>
    Finsupp.notMem_support_iff.1 (by rwa [Nat.support_factorization])
  have hA : ∑ p ∈ m.primeFactors,
      (c p : ℝ) * ((min (m.factorization p) (frozenDepth P₀ p) - 1 : ℕ) : ℝ)
      = ∑ p ∈ m.primeFactors ∪ P₀.primeFactors,
          (c p : ℝ) * ((min (m.factorization p) (frozenDepth P₀ p) - 1 : ℕ) : ℝ) := by
    refine Finset.sum_subset Finset.subset_union_left fun p _ hpm => ?_
    rw [hzero hpm]; simp
  have hB : ∑ p ∈ P₀.primeFactors,
      (c p : ℝ) * ((min (m.factorization p) (P₀.factorization p) - 1 : ℕ) : ℝ)
      = ∑ p ∈ m.primeFactors ∪ P₀.primeFactors,
          (c p : ℝ) * ((min (m.factorization p) (frozenDepth P₀ p) - 1 : ℕ) : ℝ) := by
    rw [← Finset.sum_subset Finset.subset_union_right (f := fun p =>
      (c p : ℝ) * ((min (m.factorization p) (frozenDepth P₀ p) - 1 : ℕ) : ℝ))]
    · exact Finset.sum_congr rfl fun p hp => by rw [frozenDepth_of_mem hp]
    · intro p _ hpP
      have h0 := hzero hpP
      unfold frozenDepth
      rw [h0]
      simp
  rw [hA, hB]

/-! ### The frozen part is a function of `m mod P₀` -/

/-- `min(v_p(m), v_p(P₀))` depends on `m` only modulo `P₀`. -/
lemma min_factorization_congr {P₀ m m' p : ℕ} (hp : p.Prime) (hm : m ≠ 0) (hm' : m' ≠ 0)
    (h : m ≡ m' [MOD P₀]) :
    min (m.factorization p) (P₀.factorization p) = min (m'.factorization p) (P₀.factorization p) := by
  -- `p^k ∣ m ↔ p^k ∣ m'` for every `k ≤ v_p(P₀)`
  have key : ∀ k, k ≤ P₀.factorization p → (p ^ k ∣ m ↔ p ^ k ∣ m') := by
    intro k hk
    have hdvd : p ^ k ∣ P₀ := (Nat.pow_dvd_pow p hk).trans (Nat.ordProj_dvd P₀ p)
    exact h.dvd_iff hdvd
  apply le_antisymm
  · refine le_min ?_ (min_le_right _ _)
    have h1 : p ^ (min (m.factorization p) (P₀.factorization p)) ∣ m :=
      (hp.pow_dvd_iff_le_factorization hm).2 (min_le_left _ _)
    exact (hp.pow_dvd_iff_le_factorization hm').1 ((key _ (min_le_right _ _)).1 h1)
  · refine le_min ?_ (min_le_right _ _)
    have h1 : p ^ (min (m'.factorization p) (P₀.factorization p)) ∣ m' :=
      (hp.pow_dvd_iff_le_factorization hm').2 (min_le_left _ _)
    exact (hp.pow_dvd_iff_le_factorization hm).1 ((key _ (min_le_right _ _)).2 h1)

/-- **The frozen excess is constant on the progression**: if `n ≡ n' (mod P₀)` then
`frozenExcess c P₀ (n + ρ) = frozenExcess c P₀ (n' + ρ)`. -/
theorem frozenExcess_congr (c : ℕ → ℕ) {P₀ n n' ρ : ℕ} (h : n % P₀ = n' % P₀)
    (hn : n + ρ ≠ 0) (hn' : n' + ρ ≠ 0) :
    frozenExcess c P₀ (n + ρ) = frozenExcess c P₀ (n' + ρ) := by
  unfold frozenExcess
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [min_factorization_congr (Nat.mem_primeFactors.1 hp).1 hn hn' (Nat.ModEq.add_right ρ h)]

/-! ### The junk as a sum of prime-power indicators -/

/-- `junk c P₀ m = ∑_{p ≤ N} ∑_{1 ≤ u ≤ N} c_p · 1[p^{E'_p+u} ∣ m]` for `0 < m ≤ N`. -/
lemma junk_eq_sum_ind (c : ℕ → ℕ) (P₀ : ℕ) {m N : ℕ} (hm : m ≠ 0) (hmN : m ≤ N) :
    junk c P₀ m = ∑ p ∈ (N + 1).primesBelow, ∑ u ∈ Icc 1 N,
      (c p : ℝ) * (if p ^ (frozenDepth P₀ p + u) ∣ m then 1 else 0) := by
  classical
  unfold junk
  -- extend the outer sum from `m.primeFactors` to `(N+1).primesBelow`
  have hsub : m.primeFactors ⊆ (N + 1).primesBelow := fun p hp =>
    Nat.mem_primesBelow.2 ⟨by have := Nat.le_of_mem_primeFactors hp; omega,
      (Nat.mem_primeFactors.1 hp).1⟩
  have hzero : ∀ {p : ℕ}, p ∉ m.primeFactors → m.factorization p = 0 := fun {p} h =>
    Finsupp.notMem_support_iff.1 (by rwa [Nat.support_factorization])
  rw [Finset.sum_subset hsub (fun p _ hpm => by rw [hzero hpm]; simp)]
  refine Finset.sum_congr rfl fun p hp => ?_
  have hpp := (Nat.mem_primesBelow.1 hp).2
  rw [← Finset.mul_sum, Finset.sum_boole]
  congr 1
  have hlt : m.factorization p < m := Nat.factorization_lt p hm
  have hfilt : (Icc 1 N).filter (fun u => p ^ (frozenDepth P₀ p + u) ∣ m)
      = Icc 1 (m.factorization p - frozenDepth P₀ p) := by
    ext u
    simp only [Finset.mem_filter, Finset.mem_Icc]
    rw [hpp.pow_dvd_iff_le_factorization hm]
    omega
  rw [hfilt, Nat.card_Icc, Nat.add_sub_cancel]

/-! ### One-congruence counting on the progression -/

/-- A set of naturals `≤ M`, pairwise congruent modulo `L > 0`, has at most `M/L + 1` elements. -/
lemma card_le_of_pairwise_modEq {T : Finset ℕ} {M L : ℕ} (hL : 0 < L) (hM : ∀ k ∈ T, k ≤ M)
    (hmod : ∀ k ∈ T, ∀ k' ∈ T, k ≡ k' [MOD L]) : T.card ≤ M / L + 1 := by
  have hinj : Set.InjOn (fun k => k / L) (T : Set ℕ) := by
    intro k hk k' hk' hkk'
    have h1 := hmod k hk k' hk'
    simp only at hkk'
    have e1 := Nat.div_add_mod k L
    have e2 := Nat.div_add_mod k' L
    rw [hkk'] at e1
    unfold Nat.ModEq at h1
    omega
  have himg : T.image (fun k => k / L) ⊆ Finset.range (M / L + 1) := by
    intro x hx
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.1 hx
    exact Finset.mem_range.2 (Nat.lt_succ_of_le (Nat.div_le_div_right (hM k hk)))
  calc T.card = (T.image (fun k => k / L)).card := (Finset.card_image_of_injOn hinj).symm
    _ ≤ (Finset.range (M / L + 1)).card := Finset.card_le_card himg
    _ = M / L + 1 := Finset.card_range _

/-- `gcd(p^a, P₀) = p^j` with `j ≤ v_p(P₀)`, so `p^a / gcd ≥ p^{a − v_p(P₀)}`. -/
lemma pow_div_gcd_ge {p a P₀ : ℕ} (hp : p.Prime) (hP₀ : P₀ ≠ 0) :
    p ^ (a - P₀.factorization p) ≤ p ^ a / Nat.gcd (p ^ a) P₀ := by
  obtain ⟨j, hja, hj⟩ := (Nat.dvd_prime_pow hp).1 (Nat.gcd_dvd_left (p ^ a) P₀)
  have hjP : p ^ j ∣ P₀ := hj ▸ Nat.gcd_dvd_right _ _
  have hjE : j ≤ P₀.factorization p := (hp.pow_dvd_iff_le_factorization hP₀).1 hjP
  rw [hj, Nat.pow_div hja hp.pos]
  exact Nat.pow_le_pow_right hp.pos (by omega)

/-- **One-congruence count.**  The sample points with `p^{E'_p+u} ∣ n + ρ` number at most
`X/(P₀ · p^{E'_p+u−v_p(P₀)}) + 1`. -/
theorem card_filter_pow_dvd_le {X P₀ b₀ ρ p : ℕ} (hp : p.Prime) (hP₀ : 0 < P₀) (u : ℕ) :
    ((((apSample X P₀ b₀).filter
        (fun n => p ^ (frozenDepth P₀ p + u) ∣ n + ρ)).card : ℕ) : ℝ)
      ≤ (X : ℝ) / (P₀ * p ^ (frozenDepth P₀ p + u - P₀.factorization p)) + 1 := by
  classical
  set q := p ^ (frozenDepth P₀ p + u) with hq
  set L := q / Nat.gcd q P₀ with hL
  set S := (apSample X P₀ b₀).filter (fun n => q ∣ n + ρ) with hS
  have hq0 : 0 < q := pow_pos hp.pos _
  have hLge : p ^ (frozenDepth P₀ p + u - P₀.factorization p) ≤ L := pow_div_gcd_ge hp hP₀.ne'
  have hL0 : 0 < L := lt_of_lt_of_le (pow_pos hp.pos _) hLge
  -- the quotients `n / P₀` are pairwise congruent modulo `L`
  have hmodS : ∀ n ∈ S, n % P₀ = b₀ := fun n hn =>
    (Finset.mem_filter.1 (Finset.mem_filter.1 hn).1).2
  have hdivS : ∀ n ∈ S, q ∣ n + ρ := fun n hn => (Finset.mem_filter.1 hn).2
  have hltS : ∀ n ∈ S, n < X := fun n hn =>
    Finset.mem_range.1 (Finset.mem_filter.1 (Finset.mem_filter.1 hn).1).1
  have hinj : Set.InjOn (fun n => n / P₀) (S : Set ℕ) := by
    intro n hn n' hn' h
    simp only at h
    have e1 := Nat.div_add_mod n P₀
    have e2 := Nat.div_add_mod n' P₀
    rw [hmodS n hn, h] at e1
    rw [hmodS n' hn'] at e2
    omega
  set T := S.image (fun n => n / P₀) with hT
  have hcard : S.card = T.card := (Finset.card_image_of_injOn hinj).symm
  have hTle : ∀ k ∈ T, k ≤ X / P₀ := by
    intro k hk
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.1 hk
    exact Nat.div_le_div_right (hltS n hn).le
  have hTmod : ∀ k ∈ T, ∀ k' ∈ T, k ≡ k' [MOD L] := by
    intro k hk k' hk'
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.1 hk
    obtain ⟨n', hn', rfl⟩ := Finset.mem_image.1 hk'
    have h1 : n + ρ ≡ n' + ρ [MOD q] :=
      (Nat.modEq_zero_iff_dvd.2 (hdivS n hn)).trans (Nat.modEq_zero_iff_dvd.2 (hdivS n' hn')).symm
    have h2 : n ≡ n' [MOD q] := Nat.ModEq.add_right_cancel' ρ h1
    have h3 : P₀ * (n / P₀) + b₀ ≡ P₀ * (n' / P₀) + b₀ [MOD q] := by
      have e1 : P₀ * (n / P₀) + b₀ = n := by
        have := Nat.div_add_mod n P₀; rw [hmodS n hn] at this; exact this
      have e2 : P₀ * (n' / P₀) + b₀ = n' := by
        have := Nat.div_add_mod n' P₀; rw [hmodS n' hn'] at this; exact this
      rw [e1, e2]; exact h2
    have h4 : P₀ * (n / P₀) ≡ P₀ * (n' / P₀) [MOD q] := Nat.ModEq.add_right_cancel' b₀ h3
    exact Nat.ModEq.cancel_left_div_gcd hq0 h4
  have hmain := card_le_of_pairwise_modEq hL0 hTle hTmod
  have hLr : (p : ℝ) ^ (frozenDepth P₀ p + u - P₀.factorization p) ≤ L := by exact_mod_cast hLge
  have hP₀r : (0 : ℝ) < P₀ := by exact_mod_cast hP₀
  have hpr : (0 : ℝ) < (p : ℝ) ^ (frozenDepth P₀ p + u - P₀.factorization p) := by
    have : (0 : ℝ) < p := by exact_mod_cast hp.pos
    positivity
  calc ((S.card : ℕ) : ℝ) = ((T.card : ℕ) : ℝ) := by rw [hcard]
    _ ≤ (((X / P₀ / L + 1 : ℕ) : ℕ) : ℝ) := by exact_mod_cast hmain
    _ = (((X / P₀ / L : ℕ) : ℕ) : ℝ) + 1 := by push_cast; ring
    _ ≤ (((X / P₀ : ℕ) : ℕ) : ℝ) / L + 1 := by gcongr; exact Nat.cast_div_le
    _ ≤ (X : ℝ) / P₀ / L + 1 := by gcongr; exact Nat.cast_div_le
    _ ≤ (X : ℝ) / P₀ / (p : ℝ) ^ (frozenDepth P₀ p + u - P₀.factorization p) + 1 := by
        gcongr
    _ = _ := by rw [div_div]

/-! ### Elementary sums -/

/-- `∑_{1 ≤ u ≤ L} p^{−u} ≤ 1/(p−1)` for `p ≥ 2`. -/
lemma sum_inv_pow_Icc_le {p : ℕ} (hp : 2 ≤ p) (L : ℕ) :
    ∑ u ∈ Icc 1 L, (1 / (p : ℝ)) ^ u ≤ 1 / ((p : ℝ) - 1) := by
  have hpr : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have hx0 : (0 : ℝ) ≤ 1 / (p : ℝ) := by positivity
  have hx1 : 1 / (p : ℝ) < 1 := by rw [div_lt_one (by linarith)]; linarith
  rw [← Finset.Ico_add_one_right_eq_Icc]
  refine (geom_sum_Ico_le_of_lt_one hx0 hx1).trans (le_of_eq ?_)
  field_simp

/-- `∑_{n=2}^{N} 1/(n(n−1)) = 1 − 1/N` for `N ≥ 1`. -/
lemma sum_inv_mul_pred_Icc (N : ℕ) (hN : 1 ≤ N) :
    ∑ n ∈ Icc 2 N, 1 / ((n : ℝ) * ((n : ℝ) - 1)) = 1 - 1 / (N : ℝ) := by
  induction N with
  | zero => omega
  | succ k ih =>
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp
    · rw [Finset.sum_Icc_succ_top (by omega), ih hk]
      have hk' : (0 : ℝ) < k := by exact_mod_cast hk
      have hk1 : ((k + 1 : ℕ) : ℝ) = (k : ℝ) + 1 := by push_cast; ring
      rw [hk1]
      have : (k : ℝ) + 1 - 1 = k := by ring
      rw [this]
      field_simp
      ring

lemma sum_inv_mul_pred_le (N : ℕ) : ∑ n ∈ Icc 2 N, 1 / ((n : ℝ) * ((n : ℝ) - 1)) ≤ 1 := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp
  · rw [sum_inv_mul_pred_Icc N hN]
    have : (0 : ℝ) ≤ 1 / (N : ℝ) := by positivity
    linarith

/-- `∑_{p ∈ S} 1/(p−1) ≤ H_{|S|}` for any finite set of naturals `≥ 2`. -/
lemma sum_inv_pred_le_harmonic (S : Finset ℕ) (hS : ∀ p ∈ S, 2 ≤ p) :
    ∑ p ∈ S, 1 / ((p : ℝ) - 1) ≤ ∑ i ∈ Finset.range S.card, 1 / ((i : ℝ) + 1) := by
  classical
  induction S using Finset.induction_on_max with
  | empty => simp
  | insert a S hlt ih =>
    have haS : a ∉ S := fun h => lt_irrefl a (hlt a h)
    have hS' : ∀ p ∈ S, 2 ≤ p := fun p hp => hS p (Finset.mem_insert_of_mem hp)
    have ha : 2 ≤ a := hS a (Finset.mem_insert_self _ _)
    -- `S ⊆ Ico 2 a`, so `|S| ≤ a − 2`, i.e. `|S| + 1 ≤ a − 1`
    have hcard : S.card ≤ a - 2 := by
      have : S ⊆ Finset.Ico 2 a := fun p hp => Finset.mem_Ico.2 ⟨hS' p hp, hlt p hp⟩
      have := Finset.card_le_card this
      rwa [Nat.card_Ico] at this
    rw [Finset.sum_insert haS, Finset.card_insert_of_notMem haS, Finset.sum_range_succ]
    have h1 : 1 / ((a : ℝ) - 1) ≤ 1 / ((S.card : ℝ) + 1) := by
      have : (S.card : ℝ) + 1 ≤ (a : ℝ) - 1 := by
        have : S.card + 2 ≤ a := by omega
        have : ((S.card + 2 : ℕ) : ℝ) ≤ a := by exact_mod_cast this
        push_cast at this; linarith
      exact one_div_le_one_div_of_le (by positivity) this
    linarith [ih hS']

/-- `H_n ≤ 1 + log n`. -/
lemma sum_inv_range_le_log (n : ℕ) :
    ∑ i ∈ Finset.range n, 1 / ((i : ℝ) + 1) ≤ 1 + Real.log n := by
  have h := harmonic_le_one_add_log n
  have e : ((harmonic n : ℚ) : ℝ) = ∑ i ∈ Finset.range n, 1 / ((i : ℝ) + 1) := by
    simp [harmonic, Rat.cast_sum, one_div]
  rwa [e] at h

/-! ### The sample mean of the junk -/

/-- The count `#{n ∈ P : p^{E'_p+u} ∣ n + ρ}`. -/
noncomputable def junkCount (X P₀ b₀ ρ p u : ℕ) : ℝ :=
  (((apSample X P₀ b₀).filter (fun n => p ^ (frozenDepth P₀ p + u) ∣ n + ρ)).card : ℝ)

lemma junkCount_nonneg (X P₀ b₀ ρ p u : ℕ) : 0 ≤ junkCount X P₀ b₀ ρ p u := by
  unfold junkCount; positivity

lemma junkCount_eq_zero {X P₀ b₀ ρ p u : ℕ} (hρ : 1 ≤ ρ)
    (h : X + ρ < p ^ (frozenDepth P₀ p + u)) :
    junkCount X P₀ b₀ ρ p u = 0 := by
  unfold junkCount
  rw [Finset.filter_eq_empty_iff.2, Finset.card_empty, Nat.cast_zero]
  intro n hn hd
  have hnX : n < X := Finset.mem_range.1 (Finset.mem_filter.1 hn).1
  have := Nat.le_of_dvd (by omega) hd
  omega

/-- The junk sum over the sample as a sum of counts over prime powers. -/
lemma sum_junk_eq_sum_junkCount (c : ℕ → ℕ) {X P₀ b₀ ρ : ℕ} (hρ : 1 ≤ ρ) :
    ∑ n ∈ apSample X P₀ b₀, junk c P₀ (n + ρ)
      = ∑ pu ∈ (X + ρ + 1).primesBelow ×ˢ Icc 1 (X + ρ),
          (c pu.1 : ℝ) * junkCount X P₀ b₀ ρ pu.1 pu.2 := by
  classical
  have h1 : ∀ n ∈ apSample X P₀ b₀, junk c P₀ (n + ρ)
      = ∑ pu ∈ (X + ρ + 1).primesBelow ×ˢ Icc 1 (X + ρ),
          (c pu.1 : ℝ) * (if pu.1 ^ (frozenDepth P₀ pu.1 + pu.2) ∣ n + ρ then 1 else 0) := by
    intro n hn
    have hnX : n < X := Finset.mem_range.1 (Finset.mem_filter.1 hn).1
    rw [junk_eq_sum_ind c P₀ (N := X + ρ) (by omega) (by omega), Finset.sum_product]
  rw [Finset.sum_congr rfl h1, Finset.sum_comm]
  refine Finset.sum_congr rfl fun pu _ => ?_
  unfold junkCount
  rw [← Finset.mul_sum, Finset.sum_boole]

/-- The prime powers `p^{E'_p+u} ≤ N` (`u ≥ 1`) are few: `p ≤ √N` and `u ≤ log₂ N`. -/
lemma card_filter_pow_le {N P₀ : ℕ} :
    (((N + 1).primesBelow ×ˢ Icc 1 N).filter
        (fun pu : ℕ × ℕ => pu.1 ^ (frozenDepth P₀ pu.1 + pu.2) ≤ N)).card
      ≤ (Nat.sqrt N + 1) * Nat.log 2 N := by
  classical
  have hsub : ((N + 1).primesBelow ×ˢ Icc 1 N).filter
        (fun pu : ℕ × ℕ => pu.1 ^ (frozenDepth P₀ pu.1 + pu.2) ≤ N)
      ⊆ Finset.range (Nat.sqrt N + 1) ×ˢ Icc 1 (Nat.log 2 N) := by
    intro pu hpu
    obtain ⟨hmem, hle⟩ := Finset.mem_filter.1 hpu
    obtain ⟨hp, hu⟩ := Finset.mem_product.1 hmem
    have hpp := (Nat.mem_primesBelow.1 hp).2
    have hu1 := (Finset.mem_Icc.1 hu).1
    have hE := one_le_frozenDepth P₀ pu.1
    refine Finset.mem_product.2 ⟨Finset.mem_range.2 (Nat.lt_succ_of_le ?_), Finset.mem_Icc.2 ⟨hu1, ?_⟩⟩
    · rw [Nat.le_sqrt']
      calc pu.1 ^ 2 ≤ pu.1 ^ (frozenDepth P₀ pu.1 + pu.2) :=
            Nat.pow_le_pow_right hpp.pos (by omega)
        _ ≤ N := hle
    · refine Nat.le_log_of_pow_le (by norm_num) ?_
      calc 2 ^ pu.2 ≤ pu.1 ^ pu.2 := Nat.pow_le_pow_left hpp.two_le _
        _ ≤ pu.1 ^ (frozenDepth P₀ pu.1 + pu.2) := Nat.pow_le_pow_right hpp.pos (by omega)
        _ ≤ N := hle
  calc _ ≤ (Finset.range (Nat.sqrt N + 1) ×ˢ Icc 1 (Nat.log 2 N)).card := Finset.card_le_card hsub
    _ = (Nat.sqrt N + 1) * Nat.log 2 N := by
        rw [Finset.card_product, Finset.card_range, Nat.card_Icc]; rfl

/-- The geometric series at one prime: `∑_{1≤u≤L} p^{−(E'_p+u−v_p(P₀))} ≤ p^{−(E'_p−v_p(P₀))}/(p−1)`. -/
lemma sum_inv_pow_shift_le {p : ℕ} (hp : p.Prime) (P₀ L : ℕ) :
    ∑ u ∈ Icc 1 L, 1 / ((p : ℝ) ^ (frozenDepth P₀ p + u - P₀.factorization p))
      ≤ (1 / (p : ℝ)) ^ (frozenDepth P₀ p - P₀.factorization p) * (1 / ((p : ℝ) - 1)) := by
  have hE : P₀.factorization p ≤ frozenDepth P₀ p := le_max_left _ _
  have hpr : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have h1 : ∀ u, 1 / ((p : ℝ) ^ (frozenDepth P₀ p + u - P₀.factorization p))
      = (1 / (p : ℝ)) ^ (frozenDepth P₀ p - P₀.factorization p) * (1 / (p : ℝ)) ^ u := by
    intro u
    rw [show frozenDepth P₀ p + u - P₀.factorization p
        = (frozenDepth P₀ p - P₀.factorization p) + u by omega, pow_add, one_div_pow, one_div_pow,
      one_div_mul_one_div]
  simp_rw [h1]
  rw [← Finset.mul_sum]
  exact mul_le_mul_of_nonneg_left (sum_inv_pow_Icc_le hp.two_le L) (by positivity)

/-- The prime-by-prime main term: `1/(p−1)` for `p ∣ P₀`, `1/(p(p−1))` otherwise. -/
lemma main_term_le {p : ℕ} (hp : p.Prime) (P₀ : ℕ) (hP₀ : P₀ ≠ 0) :
    (1 / (p : ℝ)) ^ (frozenDepth P₀ p - P₀.factorization p) * (1 / ((p : ℝ) - 1))
      = if p ∣ P₀ then 1 / ((p : ℝ) - 1) else 1 / ((p : ℝ) * ((p : ℝ) - 1)) := by
  split_ifs with h
  · rw [frozenDepth_of_mem (Nat.mem_primeFactors.2 ⟨hp, h, hP₀⟩), Nat.sub_self, pow_zero, one_mul]
  · rw [frozenDepth_of_not_dvd h, Nat.factorization_eq_zero_of_not_dvd h, Nat.sub_zero, pow_one,
      one_div_mul_one_div]

/-- **The sample sum of the junk.**  For `P = {n < X : n ≡ b₀ (P₀)}` and any shift `ρ ≥ 1`,

  `∑_{n∈P} junk(n+ρ) ≤ C·( (X/P₀)·(∑_{p∣P₀} 1/(p−1) + 1) + (√(X+ρ)+1)·log₂(X+ρ) )`. -/
theorem sum_junk_le (c : ℕ → ℕ) {C : ℝ} (hC : ∀ p, (c p : ℝ) ≤ C)
    {X P₀ b₀ ρ : ℕ} (hP₀ : 0 < P₀) (hρ : 1 ≤ ρ) :
    ∑ n ∈ apSample X P₀ b₀, junk c P₀ (n + ρ)
      ≤ C * ((X : ℝ) / P₀ * (∑ p ∈ P₀.primeFactors, 1 / ((p : ℝ) - 1) + 1)
          + (((Nat.sqrt (X + ρ) + 1) * Nat.log 2 (X + ρ) : ℕ) : ℝ)) := by
  classical
  set N := X + ρ with hN
  set pb := (N + 1).primesBelow with hpb
  set A := (pb ×ˢ Icc 1 N).filter
    (fun pu : ℕ × ℕ => pu.1 ^ (frozenDepth P₀ pu.1 + pu.2) ≤ N) with hA
  have hC0 : 0 ≤ C := (by positivity : (0:ℝ) ≤ c 0).trans (hC 0)
  have hP₀r : (0 : ℝ) < P₀ := by exact_mod_cast hP₀
  rw [sum_junk_eq_sum_junkCount c hρ]
  -- restrict to `A`: outside it the count vanishes
  have hres : ∑ pu ∈ pb ×ˢ Icc 1 N, (c pu.1 : ℝ) * junkCount X P₀ b₀ ρ pu.1 pu.2
      = ∑ pu ∈ A, (c pu.1 : ℝ) * junkCount X P₀ b₀ ρ pu.1 pu.2 := by
    rw [hA, Finset.sum_filter]
    refine Finset.sum_congr rfl fun pu _ => ?_
    split_ifs with h
    · rfl
    · rw [junkCount_eq_zero hρ (by omega), mul_zero]
  rw [hres]
  -- term-by-term bound on `A`
  have hterm : ∀ pu ∈ A, (c pu.1 : ℝ) * junkCount X P₀ b₀ ρ pu.1 pu.2
      ≤ C * (1 / ((pu.1 : ℝ) ^ (frozenDepth P₀ pu.1 + pu.2 - P₀.factorization pu.1)) * ((X : ℝ) / P₀)
          + 1) := by
    intro pu hpu
    have hpp := (Nat.mem_primesBelow.1 (Finset.mem_product.1 (Finset.mem_filter.1 hpu).1).1).2
    have hcount := card_filter_pow_dvd_le (X := X) (b₀ := b₀) (ρ := ρ) hpp hP₀ pu.2
    have hpr : (0 : ℝ) < (pu.1 : ℝ) ^ (frozenDepth P₀ pu.1 + pu.2 - P₀.factorization pu.1) := by
      have : (0 : ℝ) < pu.1 := by exact_mod_cast hpp.pos
      positivity
    have hcount' : junkCount X P₀ b₀ ρ pu.1 pu.2
        ≤ 1 / ((pu.1 : ℝ) ^ (frozenDepth P₀ pu.1 + pu.2 - P₀.factorization pu.1)) * ((X : ℝ) / P₀)
          + 1 := by
      unfold junkCount
      refine hcount.trans (le_of_eq ?_)
      field_simp
    calc (c pu.1 : ℝ) * junkCount X P₀ b₀ ρ pu.1 pu.2
        ≤ C * junkCount X P₀ b₀ ρ pu.1 pu.2 :=
          mul_le_mul_of_nonneg_right (hC _) (junkCount_nonneg _ _ _ _ _ _)
      _ ≤ _ := mul_le_mul_of_nonneg_left hcount' hC0
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, mul_one]
  refine mul_le_mul_of_nonneg_left (add_le_add ?_ ?_) hC0
  · -- the main term: extend from `A` to the full product and sum the geometric series
    have hext : ∑ pu ∈ A, 1 / ((pu.1 : ℝ) ^ (frozenDepth P₀ pu.1 + pu.2 - P₀.factorization pu.1))
          * ((X : ℝ) / P₀)
        ≤ ∑ pu ∈ pb ×ˢ Icc 1 N,
          1 / ((pu.1 : ℝ) ^ (frozenDepth P₀ pu.1 + pu.2 - P₀.factorization pu.1)) * ((X : ℝ) / P₀) :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun pu _ _ => by positivity
    refine hext.trans ?_
    rw [← Finset.sum_mul, Finset.sum_product, mul_comm]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    have hgeo : ∀ p ∈ pb, ∑ u ∈ Icc 1 N,
          1 / ((p : ℝ) ^ (frozenDepth P₀ p + u - P₀.factorization p))
        ≤ if p ∣ P₀ then 1 / ((p : ℝ) - 1) else 1 / ((p : ℝ) * ((p : ℝ) - 1)) := by
      intro p hp
      have hpp := (Nat.mem_primesBelow.1 hp).2
      rw [← main_term_le hpp P₀ hP₀.ne']
      exact sum_inv_pow_shift_le hpp P₀ N
    refine (Finset.sum_le_sum hgeo).trans ?_
    rw [Finset.sum_ite, ]
    refine add_le_add ?_ ?_
    · -- `p ∣ P₀`: a subsum of `∑_{p ∈ P₀.primeFactors}`
      refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun p hp _ => ?_
      · intro p hp
        obtain ⟨hp1, hp2⟩ := Finset.mem_filter.1 hp
        exact Nat.mem_primeFactors.2 ⟨(Nat.mem_primesBelow.1 hp1).2, hp2, hP₀.ne'⟩
      · have := (Nat.mem_primeFactors.1 hp).1.two_le
        have : (2 : ℝ) ≤ p := by exact_mod_cast this
        have : (0 : ℝ) < (p : ℝ) - 1 := by linarith
        positivity
    · -- `p ∤ P₀`: a subsum of the telescoping sum
      refine (Finset.sum_le_sum_of_subset_of_nonneg (t := Icc 2 N) ?_ fun n hn _ => ?_).trans
        (sum_inv_mul_pred_le N)
      · intro p hp
        obtain ⟨hp1, _⟩ := Finset.mem_filter.1 hp
        have h1 := Nat.mem_primesBelow.1 hp1
        exact Finset.mem_Icc.2 ⟨h1.2.two_le, by omega⟩
      · have := (Finset.mem_Icc.1 hn).1
        have : (2 : ℝ) ≤ n := by exact_mod_cast this
        have : (0 : ℝ) < (n : ℝ) - 1 := by linarith
        positivity
  · -- the `+1`s
    exact_mod_cast card_filter_pow_le (N := N) (P₀ := P₀)

end NormalNumbers.PrimeLambert
