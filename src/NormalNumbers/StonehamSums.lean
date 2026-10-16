/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.Stoneham
import NormalNumbers.ReciprocalNormal
import NormalNumbers.StonehamSixFailure
import NormalNumbers.EquidistTransfer

/-!
# Sums of Stoneham constants

The pair `α₂,₃`, `α₄,₃` is arithmetically coupled: after putting the two series
over powers of four, the `k`-th coefficient is an integer because
`3^(k+1) ∣ 2^(3^k) + 1`.  Consequently the binary expansion of their sum has zero windows of
asymptotic relative length `1/3`, obstructing even simple normality.  We also
prove that `α₄,₃` is 4-normal and hence 2-normal, making this an explicit pair
of binary-normal numbers whose sum is not simply normal.
-/

namespace NormalNumbers

open ReciprocalNormal
open Filter Topology

/-- The Stoneham constant `α_{B,c} = Σ_{m≥1} 1/(c^m · B^(c^m))`. -/
noncomputable def stonehamAlpha (B c : ℕ) : ℝ :=
  ∑' n : ℕ, 1 / ((c : ℝ) ^ (n + 1) * (B : ℝ) ^ (c ^ (n + 1)))

theorem stonehamAlpha_two_three : stonehamAlpha 2 3 = stoneham23 := by
  rfl

/-- The combined summand of `α₂,₃ + α₄,₃`. -/
noncomputable def stonehamSumTerm (j : ℕ) : ℝ :=
  1 / ((3 : ℝ) ^ (j + 1) * 2 ^ (3 ^ (j + 1))) +
    1 / ((3 : ℝ) ^ (j + 1) * 4 ^ (3 ^ (j + 1)))

/-- The LTE divisibility which makes every regrouped Stoneham summand an integer block. -/
theorem three_pow_succ_dvd_two_pow_three_pow_add_one (k : ℕ) :
    3 ^ (k + 1) ∣ 2 ^ (3 ^ k) + 1 := by
  have hv := padicValNat.pow_add_pow (p := 3) (x := 2) (y := 1)
    (by decide) (by norm_num) (by norm_num) (Odd.pow (by decide) : Odd (3 ^ k))
  norm_num [padicValNat.prime_pow] at hv
  exact (padicValNat_dvd_iff_le (by positivity)).2 (by omega)

theorem summable_stonehamAlpha_four_three_term : Summable fun j : ℕ =>
    1 / ((3 : ℝ) ^ (j + 1) * 4 ^ (3 ^ (j + 1))) := by
  apply Summable.of_nonneg_of_le (fun _ => by positivity) (fun j => ?_) summable_sterm
  unfold sterm
  apply div_le_div_of_nonneg_left one_pos.le (by positivity)
  gcongr
  norm_num

/-! ### Base-four Stoneham dynamics -/

/-- The integer orbit state for `α₄,₃` at time `n` in window `M`. -/
def stonehamFourState (M n : ℕ) : ℕ :=
  (∑ m ∈ Finset.Icc 1 M, 3 ^ (M - m) * 4 ^ (n - 3 ^ m)) % 3 ^ M

/-- The base-four state is multiplied by four at each step. -/
theorem stonehamFourState_succ (M n : ℕ) (hM : 1 ≤ M) (hn : 3 ^ M ≤ n) :
    stonehamFourState M (n + 1) = 4 * stonehamFourState M n % 3 ^ M := by
  unfold stonehamFourState
  have hsum : ∑ m ∈ Finset.Icc 1 M, 3 ^ (M - m) * 4 ^ (n + 1 - 3 ^ m)
      = 4 * ∑ m ∈ Finset.Icc 1 M, 3 ^ (M - m) * 4 ^ (n - 3 ^ m) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun m hm => ?_
    have hm' : m ≤ M := (Finset.mem_Icc.mp hm).2
    have h3m : 3 ^ m ≤ n :=
      le_trans (Nat.pow_le_pow_right (by norm_num) hm') hn
    have : n + 1 - 3 ^ m = (n - 3 ^ m) + 1 := by omega
    rw [this, pow_succ]
    ring
  rw [hsum, Nat.mul_mod, Nat.mul_mod 4 (_ % 3 ^ M), Nat.mod_mod_of_dvd _ dvd_rfl]

/-- The initial state in each base-four window is prime to three. -/
theorem stonehamFourState_unit (M : ℕ) (hM : 1 ≤ M) :
    ¬ 3 ∣ stonehamFourState M (3 ^ M) := by
  unfold stonehamFourState
  rw [Nat.dvd_mod_iff (dvd_pow_self 3 (by omega : M ≠ 0))]
  obtain ⟨M', rfl⟩ : ∃ M', M = M' + 1 := ⟨M - 1, by omega⟩
  have hins : Finset.Icc 1 (M' + 1) = insert (M' + 1) (Finset.Icc 1 M') := by
    ext u
    simp only [Finset.mem_Icc, Finset.mem_insert]
    omega
  rw [hins, Finset.sum_insert (by simp [Finset.mem_Icc])]
  simp only [Nat.sub_self, pow_zero, mul_one]
  intro hdvd
  have hdvd_sum : 3 ∣ ∑ m ∈ Finset.Icc 1 M',
      3 ^ (M' + 1 - m) * 4 ^ (3 ^ (M' + 1) - 3 ^ m) := by
    refine Finset.dvd_sum fun m hm => ?_
    have hm' : m ≤ M' := (Finset.mem_Icc.mp hm).2
    exact Dvd.dvd.mul_right (dvd_pow_self 3 (by omega)) _
  omega

/-- In window `M`, the base-four orbit is its rational state plus a positive
tail bounded by `1 / 3 ^ (M + 1)`, hence strictly smaller than twice that
quantity. -/
theorem stonehamFourState_approx (M n : ℕ) (hM : 1 ≤ M)
    (hn : 3 ^ M ≤ n) (hn' : n < 3 ^ (M + 1)) :
    (stonehamFourState M n : ℝ) / 3 ^ M < orbit 4 (stonehamAlpha 4 3) n ∧
      orbit 4 (stonehamAlpha 4 3) n
        < (stonehamFourState M n : ℝ) / 3 ^ M + 2 / 3 ^ (M + 1) := by
  have h3M : (0 : ℝ) < 3 ^ M := by positivity
  have h3M1 : (0 : ℝ) < 3 ^ (M + 1) := by positivity
  set t : ℕ → ℝ := fun j =>
    1 / ((3 : ℝ) ^ (j + 1) * 4 ^ (3 ^ (j + 1))) with ht
  set g : ℕ → ℝ := fun j => (4 : ℝ) ^ n * t j with hg
  have ht_sum : Summable t := by
    simpa only [ht] using summable_stonehamAlpha_four_three_term
  have hg_sum : Summable g := ht_sum.mul_left _
  have hg_pos : ∀ j, 0 < g j := fun j => by
    simp only [hg, ht]
    positivity
  have hmul : stonehamAlpha 4 3 * (4 : ℝ) ^ n = ∑' j, g j := by
    rw [tsum_mul_left, mul_comm]
    rfl
  have hshift_sum : Summable fun j => g (j + M) :=
    (summable_nat_add_iff M).2 hg_sum
  have hsplit : ∑' j, g j
      = (∑ j ∈ Finset.range M, g j) + ∑' j, g (j + M) :=
    (hg_sum.sum_add_tsum_nat_add M).symm
  set T : ℝ := ∑' j, g (j + M) with hT
  set S : ℕ := ∑ m ∈ Finset.Icc 1 M,
    3 ^ (M - m) * 4 ^ (n - 3 ^ m) with hS
  have hHead : (∑ j ∈ Finset.range M, g j) = (S : ℝ) / 3 ^ M := by
    rw [hS]
    push_cast
    rw [Finset.sum_div,
      show Finset.Icc 1 M = Finset.Ico 1 (M + 1) from by
        ext u
        simp only [Finset.mem_Icc, Finset.mem_Ico]
        omega,
      Finset.sum_Ico_eq_sum_range]
    simp only [Nat.add_sub_cancel]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hjM : j < M := Finset.mem_range.mp hj
    have h3le : 3 ^ (1 + j) ≤ n :=
      le_trans (Nat.pow_le_pow_right (by norm_num) (by omega)) hn
    have h4 : (4 : ℝ) ^ (n - 3 ^ (1 + j)) * 4 ^ (3 ^ (1 + j)) = 4 ^ n := by
      rw [← pow_add]
      congr 1
      omega
    have h3 : (3 : ℝ) ^ (M - (1 + j)) * 3 ^ (1 + j) = 3 ^ M := by
      rw [← pow_add]
      congr 1
      omega
    simp only [hg, ht]
    rw [mul_one_div, div_eq_div_iff (by positivity) h3M.ne']
    rw [← h4, ← h3]
    ring
  have hT_pos : 0 < T := by
    rw [hT]
    exact Summable.tsum_pos hshift_sum (fun j => (hg_pos _).le) 0 (hg_pos _)
  have hT_le : T ≤ 1 / 3 ^ (M + 1) := by
    set d : ℝ := (4 : ℝ) ^ n /
      (3 ^ (M + 1) * 4 ^ (3 ^ (M + 1))) with hd
    have hterm : ∀ j, g (j + M) ≤ d * (1 / 2) ^ j := by
      intro j
      have hexp : 3 ^ (M + 1) + j ≤ 3 ^ (j + M + 1) := by
        have hj3 : j + 1 ≤ 3 ^ j := Nat.lt_pow_self (by norm_num)
        have hP : 1 ≤ 3 ^ (M + 1) := Nat.one_le_pow _ _ (by norm_num)
        calc
          3 ^ (M + 1) + j ≤ 3 ^ (M + 1) * (j + 1) := by nlinarith
          _ ≤ 3 ^ (M + 1) * 3 ^ j := Nat.mul_le_mul_left _ hj3
          _ = 3 ^ (j + M + 1) := by
            rw [← pow_add]
            congr 1
            omega
      have hkey : (3 : ℝ) ^ (M + 1) * 4 ^ (3 ^ (M + 1)) * 2 ^ j
          ≤ 3 ^ (j + M + 1) * 4 ^ (3 ^ (j + M + 1)) := by
        have h3 : (3 : ℝ) ^ (M + 1) ≤ 3 ^ (j + M + 1) :=
          pow_le_pow_right₀ (by norm_num) (by omega)
        have h24 : (2 : ℝ) ^ j ≤ 4 ^ j := by gcongr <;> norm_num
        have h4 : (4 : ℝ) ^ (3 ^ (M + 1)) * 2 ^ j
            ≤ 4 ^ (3 ^ (j + M + 1)) := by
          calc
            (4 : ℝ) ^ (3 ^ (M + 1)) * 2 ^ j
                ≤ 4 ^ (3 ^ (M + 1)) * 4 ^ j :=
              mul_le_mul_of_nonneg_left h24 (by positivity)
            _ = 4 ^ (3 ^ (M + 1) + j) := (pow_add _ _ _).symm
            _ ≤ 4 ^ (3 ^ (j + M + 1)) :=
              pow_le_pow_right₀ (by norm_num) hexp
        calc
          (3 : ℝ) ^ (M + 1) * 4 ^ (3 ^ (M + 1)) * 2 ^ j
              = 3 ^ (M + 1) * (4 ^ (3 ^ (M + 1)) * 2 ^ j) := by ring
          _ ≤ 3 ^ (j + M + 1) * 4 ^ (3 ^ (j + M + 1)) :=
            mul_le_mul h3 h4 (by positivity) (by positivity)
      simp only [hg, ht, hd]
      rw [mul_one_div, div_pow, one_pow, div_mul_div_comm, mul_one]
      exact div_le_div_of_nonneg_left (by positivity) (by positivity) hkey
    have hgeom : Summable fun j : ℕ => d * (1 / 2) ^ j :=
      (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left d
    have hle := hshift_sum.tsum_le_tsum hterm hgeom
    rw [hT]
    refine le_trans hle ?_
    rw [tsum_mul_left, tsum_geometric_two, hd]
    have h4n : (4 : ℝ) ^ n * 2 ≤ 4 ^ (3 ^ (M + 1)) := by
      calc
        (4 : ℝ) ^ n * 2 ≤ 4 ^ n * 4 := by
          gcongr
          norm_num
        _ = 4 ^ (n + 1) := by rw [pow_succ]
        _ ≤ 4 ^ (3 ^ (M + 1)) :=
          pow_le_pow_right₀ (by norm_num) (by omega)
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    calc
      (4 : ℝ) ^ n * 2 ≤ 4 ^ (3 ^ (M + 1)) := h4n
      _ = 1 / 3 ^ (M + 1) *
          (3 ^ (M + 1) * 4 ^ (3 ^ (M + 1))) := by field_simp
  have hstate : stonehamFourState M n = S % 3 ^ M := rfl
  have hstate_lt : stonehamFourState M n < 3 ^ M := by
    rw [hstate]
    exact Nat.mod_lt _ (pow_pos (by norm_num) M)
  have hcast : (S : ℝ) / 3 ^ M
      = ((S / 3 ^ M : ℕ) : ℝ) + (stonehamFourState M n : ℝ) / 3 ^ M := by
    have h := Nat.div_add_mod S (3 ^ M)
    rw [hstate]
    have hSr : (S : ℝ) = (3 : ℝ) ^ M * ((S / 3 ^ M : ℕ) : ℝ)
        + ((S % 3 ^ M : ℕ) : ℝ) := by
      exact_mod_cast h.symm
    rw [hSr]
    field_simp
  have hy_nonneg : 0 ≤ (stonehamFourState M n : ℝ) / 3 ^ M + T := by
    positivity
  have hy_lt : (stonehamFourState M n : ℝ) / 3 ^ M + T < 1 := by
    have h1 : (stonehamFourState M n : ℝ) ≤ (3 : ℝ) ^ M - 1 := by
      have hle : (stonehamFourState M n : ℕ) + 1 ≤ 3 ^ M := hstate_lt
      have hleR := (Nat.cast_le (α := ℝ)).2 hle
      push_cast at hleR
      linarith
    have h3 : (1 : ℝ) / 3 ^ (M + 1) < 1 / 3 ^ M := by
      apply div_lt_div_of_pos_left one_pos h3M
      exact pow_lt_pow_right₀ (by norm_num) (by omega)
    have hsplit1 : ((3 : ℝ) ^ M - 1) / 3 ^ M + 1 / 3 ^ M = 1 := by
      field_simp
      ring
    have hdiv : (stonehamFourState M n : ℝ) / 3 ^ M
        ≤ ((3 : ℝ) ^ M - 1) / 3 ^ M := by gcongr
    linarith
  have horb : orbit 4 (stonehamAlpha 4 3) n
      = (stonehamFourState M n : ℝ) / 3 ^ M + T := by
    unfold orbit
    have hb4 : ((4 : ℕ) : ℝ) = (4 : ℝ) := by norm_num
    rw [hb4, hmul, hsplit, hHead, hcast, add_assoc, Int.fract_natCast_add]
    exact Int.fract_eq_self.mpr ⟨hy_nonneg, hy_lt⟩
  constructor
  · rw [horb]
    linarith
  · rw [horb]
    have h2x : (2 : ℝ) / 3 ^ (M + 1) = 2 * (1 / 3 ^ (M + 1)) := by ring
    have hxpos : (0 : ℝ) < 1 / 3 ^ (M + 1) := by positivity
    rw [h2x]
    linarith

/-- A one-sided visit bound for a segment of a multiplication-by-four orbit
modulo `3 ^ M`.

The period has length `3 ^ (M - 1)`, only one third of the ambient residue
ring.  For the strong hot-spot lemma that fixed index is harmless: injectivity
within one period and the crude ambient interval count already give the
required `O(length)` upper bound.  Thus no exact classification or counting
of the orbit's residue class modulo three is needed. -/
theorem segment_visit_upper_four (M : ℕ) (hM : 1 ≤ M) (u : ℕ)
    (hu : ¬ 3 ∣ u) (a c : ℝ) (ha : 0 ≤ a) (hac : a ≤ c) (hc : c ≤ 1)
    (ℓ : ℕ) :
    (((Finset.range ℓ).filter fun j =>
        ((u * 4 ^ j % 3 ^ M : ℕ) : ℝ) / 3 ^ M ∈ Set.Ico a c).card : ℝ)
      ≤ (ℓ / 3 ^ (M - 1) + 1) *
          (3 * (c - a) * 3 ^ (M - 1) + 2) := by
  classical
  set ord : ℕ := 3 ^ (M - 1) with horddef
  have hordpos : 0 < ord := by positivity
  have hPpos : 0 < (3 : ℕ) ^ M := pow_pos (by norm_num) M
  set f : ℕ → ℕ := fun r => u * 4 ^ r % 3 ^ M with hf
  -- `4` has period `ord` modulo `3 ^ M`.
  have h4ord : 4 ^ ord ≡ 1 [MOD 3 ^ M] := by
    have h := two_pow_modEq_one (M - 1)
    have hM' : M - 1 + 1 = M := by omega
    rw [hM'] at h
    calc
      4 ^ ord = (2 ^ 2) ^ ord := by norm_num
      _ = 2 ^ (2 * ord) := by rw [pow_mul]
      _ ≡ 1 [MOD 3 ^ M] := by simpa [horddef] using h
  have hper : ∀ j : ℕ, f j = f (j % ord) := by
    intro j
    show u * 4 ^ j % 3 ^ M = u * 4 ^ (j % ord) % 3 ^ M
    conv_lhs => rw [← Nat.div_add_mod j ord]
    rw [pow_add, pow_mul]
    have step : (4 ^ ord) ^ (j / ord) * 4 ^ (j % ord)
        ≡ 1 ^ (j / ord) * 4 ^ (j % ord) [MOD 3 ^ M] :=
      Nat.ModEq.mul_right _ (h4ord.pow _)
    have hfin := step.mul_left u
    simp only [one_pow, one_mul] at hfin
    exact hfin
  set p : ℕ → Prop := fun r => ((f r : ℕ) : ℝ) / 3 ^ M ∈ Set.Ico a c with hp
  have hcongr : ((Finset.range ℓ).filter fun j =>
        ((u * 4 ^ j % 3 ^ M : ℕ) : ℝ) / 3 ^ M ∈ Set.Ico a c)
      = (Finset.range ℓ).filter fun j => p (j % ord) := by
    refine Finset.filter_congr fun j _ => ?_
    have hj := hper j
    simp only [hf] at hj
    simp only [hp, hf, ← hj]
  rw [hcongr]
  -- Inflate the segment to an integral number of periods.
  have hlift : ℓ ≤ (ℓ / ord + 1) * ord := by
    calc
      ℓ = ord * (ℓ / ord) + ℓ % ord := (Nat.div_add_mod ℓ ord).symm
      _ ≤ ord * (ℓ / ord) + ord :=
        Nat.add_le_add_left (Nat.mod_lt ℓ hordpos).le _
      _ = (ℓ / ord + 1) * ord := by ring
  have hcard1 : ((Finset.range ℓ).filter fun j => p (j % ord)).card
      ≤ (ℓ / ord + 1) * ((Finset.range ord).filter p).card := by
    calc
      ((Finset.range ℓ).filter fun j => p (j % ord)).card
          ≤ (((Finset.range ((ℓ / ord + 1) * ord)).filter
              fun j => p (j % ord))).card :=
            Finset.card_le_card (Finset.filter_subset_filter _ (by
              intro x hx
              exact Finset.mem_range.mpr
                (lt_of_lt_of_le (Finset.mem_range.mp hx) hlift)))
      _ = (ℓ / ord + 1) * ((Finset.range ord).filter p).card :=
        card_filter_mod_pred _ _ hordpos p
  -- Embed one period into the ambient integer interval.  Unlike the base-2
  -- proof, we deliberately do not count only the occupied residue class.
  set pl : ℕ := ⌈a * 3 ^ M⌉₊ with hpl
  set qu : ℕ := ⌈c * 3 ^ M⌉₊ with hqu
  have h3MR : (0 : ℝ) < 3 ^ M := by positivity
  have hplqu : pl ≤ qu := Nat.ceil_le_ceil (by nlinarith)
  have hucop : Nat.Coprime u (3 ^ M) := by
    exact Nat.Coprime.pow_right _
      (Nat.coprime_comm.mp ((Nat.prime_three.coprime_iff_not_dvd).mpr hu))
  have hmaps : ∀ r ∈ (Finset.range ord).filter p, f r ∈ Finset.Ico pl qu := by
    intro r hr
    obtain ⟨-, hpr⟩ := Finset.mem_filter.mp hr
    obtain ⟨hlo, hhi⟩ := hpr
    rw [Finset.mem_Ico]
    constructor
    · rw [hpl]
      apply Nat.ceil_le.mpr
      rw [le_div_iff₀ h3MR] at hlo
      linarith
    · have h1 : ((f r : ℕ) : ℝ) < c * 3 ^ M := by
        rw [div_lt_iff₀ h3MR] at hhi
        linarith
      have h2 : ((f r : ℕ) : ℝ) < (qu : ℝ) :=
        lt_of_lt_of_le h1 (Nat.le_ceil _)
      exact_mod_cast h2
  have hinj : Set.InjOn f ((Finset.range ord).filter p) := by
    intro r hr s hs hrs
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_range] at hr hs
    have hz : ((u * 4 ^ r : ℕ) : ZMod (3 ^ M)) =
        ((u * 4 ^ s : ℕ) : ZMod (3 ^ M)) := by
      rw [ZMod.natCast_eq_natCast_iff]
      show u * 4 ^ r % 3 ^ M = u * 4 ^ s % 3 ^ M
      exact hrs
    push_cast at hz
    set U : (ZMod (3 ^ M))ˣ := ZMod.unitOfCoprime u hucop with hU
    have hUcoe : (U : ZMod (3 ^ M)) = (u : ℕ) := ZMod.coe_unitOfCoprime _ _
    have h4eq : ((4 : ZMod (3 ^ M))) ^ r = (4 : ZMod (3 ^ M)) ^ s := by
      have hcg := congrArg
        (fun x => ((U⁻¹ : (ZMod (3 ^ M))ˣ) : ZMod (3 ^ M)) * x) hz
      simpa [← hUcoe, ← mul_assoc, Units.inv_mul] using hcg
    have hunit : fourUnit M ^ r = fourUnit M ^ s := by
      apply Units.ext
      push_cast [fourUnit, twoUnit, ZMod.coe_unitOfCoprime]
      norm_num at h4eq ⊢
      exact h4eq
    have hordM : orderOf (fourUnit M) = ord := by
      rw [horddef]
      exact orderOf_fourUnit M hM
    exact pow_injOn_Iio_orderOf (x := fourUnit M)
      (by rw [hordM]; exact hr.1 : r ∈ Set.Iio (orderOf (fourUnit M)))
      (by rw [hordM]; exact hs.1 : s ∈ Set.Iio (orderOf (fourUnit M))) hunit
  have hcard2 : ((Finset.range ord).filter p).card ≤ (Finset.Ico pl qu).card :=
    Finset.card_le_card_of_injOn f hmaps hinj
  have hquR : (qu : ℝ) < c * 3 ^ M + 1 := by
    rw [hqu]
    exact Nat.ceil_lt_add_one (by nlinarith)
  have hplR : a * 3 ^ M ≤ (pl : ℝ) := by
    rw [hpl]
    exact Nat.le_ceil _
  have hsubR : ((qu - pl : ℕ) : ℝ) ≤ (c - a) * 3 ^ M + 1 := by
    rw [Nat.cast_sub hplqu]
    nlinarith
  have hordR : ((ord : ℕ) : ℝ) = 3 ^ (M - 1) := by
    rw [horddef]
    norm_num
  have h3M_split : (3 : ℝ) ^ M = 3 * 3 ^ (M - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  have hperR : (((Finset.range ord).filter p).card : ℝ)
      ≤ 3 * (c - a) * 3 ^ (M - 1) + 2 := by
    have hc2 : (((Finset.range ord).filter p).card : ℝ)
        ≤ ((qu - pl : ℕ) : ℝ) := by
      exact_mod_cast hcard2.trans_eq (Nat.card_Ico pl qu)
    rw [h3M_split] at hsubR
    nlinarith
  have hcard1R : (((Finset.range ℓ).filter fun j => p (j % ord)).card : ℝ)
      ≤ ((ℓ / ord + 1 : ℕ) : ℝ) *
          (((Finset.range ord).filter p).card : ℝ) := by
    exact_mod_cast hcard1
  have hdivR : ((ℓ / ord : ℕ) : ℝ) + 1
      ≤ (ℓ : ℝ) / 3 ^ (M - 1) + 1 := by
    have h := Nat.cast_div_le (m := ℓ) (n := ord) (α := ℝ)
    rw [hordR] at h
    linarith
  have hpernn : (0 : ℝ) ≤ 3 * (c - a) * 3 ^ (M - 1) + 2 := by
    have : 0 ≤ c - a := sub_nonneg.mpr hac
    positivity
  calc
    (((Finset.range ℓ).filter fun j => p (j % ord)).card : ℝ)
        ≤ ((ℓ / ord + 1 : ℕ) : ℝ) *
            (((Finset.range ord).filter p).card : ℝ) := hcard1R
    _ ≤ ((ℓ / ord + 1 : ℕ) : ℝ) *
          (3 * (c - a) * 3 ^ (M - 1) + 2) := by
      apply mul_le_mul_of_nonneg_left hperR
      positivity
    _ ≤ ((ℓ : ℝ) / 3 ^ (M - 1) + 1) *
          (3 * (c - a) * 3 ^ (M - 1) + 2) := by
      apply mul_le_mul_of_nonneg_right _ hpernn
      push_cast
      exact hdivR

/-- `α₄,₃` lies in `[0,1)`. -/
theorem stonehamAlpha_four_three_mem_Ico :
    stonehamAlpha 4 3 ∈ Set.Ico (0 : ℝ) 1 := by
  constructor
  · unfold stonehamAlpha
    exact tsum_nonneg fun j => by positivity
  · have hle : ∀ j : ℕ,
        1 / ((3 : ℝ) ^ (j + 1) * 4 ^ (3 ^ (j + 1))) ≤ sterm j := by
      intro j
      unfold sterm
      apply div_le_div_of_nonneg_left one_pos.le (by positivity)
      gcongr
      norm_num
    have hsum := summable_stonehamAlpha_four_three_term.tsum_le_tsum hle summable_sterm
    exact lt_of_le_of_lt hsum stoneham23_mem_Ico.2

/-- Across a window, the base-four state follows multiplication by `4`. -/
theorem stonehamFourState_window (M : ℕ) (hM : 1 ≤ M) (j : ℕ) :
    stonehamFourState M (3 ^ M + j) =
      stonehamFourState M (3 ^ M) * 4 ^ j % 3 ^ M := by
  have hPpos : 0 < 3 ^ M := pow_pos (by norm_num) M
  induction j with
  | zero =>
      rw [add_zero, pow_zero, mul_one]
      exact (Nat.mod_eq_of_lt (Nat.mod_lt _ hPpos)).symm
  | succ j ih =>
      have hstep : 3 ^ M + (j + 1) = (3 ^ M + j) + 1 := by omega
      rw [hstep, stonehamFourState_succ M _ hM (by omega), ih]
      have hcong :=
        (Nat.mod_modEq (stonehamFourState M (3 ^ M) * 4 ^ j) (3 ^ M)).mul_left 4
      calc
        4 * (stonehamFourState M (3 ^ M) * 4 ^ j % 3 ^ M) % 3 ^ M
            = 4 * (stonehamFourState M (3 ^ M) * 4 ^ j) % 3 ^ M := hcong
        _ = stonehamFourState M (3 ^ M) * 4 ^ (j + 1) % 3 ^ M := by
          rw [pow_succ]
          ring_nf

/-- Visits of an initial segment of a base-four Stoneham window. -/
theorem stonehamFour_window_visit_bound (M : ℕ) (hM : 1 ≤ M) (a c : ℝ)
    (ha : 0 ≤ a) (hac : a ≤ c) (hc : c ≤ 1) (ℓ : ℕ)
    (hℓ : ℓ ≤ 2 * 3 ^ M) :
    (((Finset.range ℓ).filter fun j =>
        orbit 4 (stonehamAlpha 4 3) (3 ^ M + j) ∈ Set.Ico a c).card : ℝ)
      ≤ ((ℓ : ℝ) / 3 ^ (M - 1) + 1) *
          (3 * (c - a + 2 / 3 ^ (M + 1)) * 3 ^ (M - 1) + 2) := by
  classical
  set u : ℕ := stonehamFourState M (3 ^ M) with hu
  have huu : ¬ 3 ∣ u := stonehamFourState_unit M hM
  set a' : ℝ := max 0 (a - 2 / 3 ^ (M + 1)) with ha'
  have ha'0 : 0 ≤ a' := le_max_left _ _
  have ha'c : a' ≤ c := by
    apply max_le (le_trans ha hac)
    have : (0 : ℝ) < 2 / 3 ^ (M + 1) := by positivity
    linarith
  have hsub : ((Finset.range ℓ).filter fun j =>
        orbit 4 (stonehamAlpha 4 3) (3 ^ M + j) ∈ Set.Ico a c)
      ⊆ (Finset.range ℓ).filter fun j =>
        ((u * 4 ^ j % 3 ^ M : ℕ) : ℝ) / 3 ^ M ∈ Set.Ico a' c := by
    intro j hj
    simp only [Finset.mem_filter, Finset.mem_range, Set.mem_Ico] at hj ⊢
    obtain ⟨hjℓ, hlo, hhi⟩ := hj
    have hn : 3 ^ M ≤ 3 ^ M + j := by omega
    have hn' : 3 ^ M + j < 3 ^ (M + 1) := by
      have hpow : (3 : ℕ) ^ (M + 1) = 3 * 3 ^ M := by
        rw [pow_succ]
        ring
      omega
    obtain ⟨happ1, happ2⟩ :=
      stonehamFourState_approx M (3 ^ M + j) hM hn hn'
    rw [stonehamFourState_window M hM j, ← hu] at happ1 happ2
    refine ⟨hjℓ, ?_, ?_⟩
    · apply max_le
      · positivity
      · linarith
    · linarith
  calc
    (((Finset.range ℓ).filter fun j =>
        orbit 4 (stonehamAlpha 4 3) (3 ^ M + j) ∈ Set.Ico a c).card : ℝ)
        ≤ (((Finset.range ℓ).filter fun j =>
          ((u * 4 ^ j % 3 ^ M : ℕ) : ℝ) / 3 ^ M ∈ Set.Ico a' c).card : ℝ) := by
          exact_mod_cast Finset.card_le_card hsub
    _ ≤ ((ℓ : ℝ) / 3 ^ (M - 1) + 1) *
          (3 * (c - a') * 3 ^ (M - 1) + 2) :=
      segment_visit_upper_four M hM u huu a' c ha'0 ha'c hc ℓ
    _ ≤ ((ℓ : ℝ) / 3 ^ (M - 1) + 1) *
          (3 * (c - a + 2 / 3 ^ (M + 1)) * 3 ^ (M - 1) + 2) := by
      have hwid : c - a' ≤ c - a + 2 / 3 ^ (M + 1) := by
        have : a - 2 / 3 ^ (M + 1) ≤ a' := le_max_right _ _
        linarith
      have hordnn : (0 : ℝ) ≤ 3 ^ (M - 1) := by positivity
      have hfac : (0 : ℝ) ≤ (ℓ : ℝ) / 3 ^ (M - 1) + 1 := by positivity
      apply mul_le_mul_of_nonneg_left _ hfac
      nlinarith [hwid, hordnn]

/-- A simplified bound for a base-four cylinder of length `4⁻ᵏ` in one
Stoneham window. -/
theorem stonehamFour_per_window_bound (k M ℓ : ℕ) (hMk : 2 * k + 3 ≤ M)
    (hℓ : ℓ ≤ 2 * 3 ^ M) (a c : ℝ) (ha : 0 ≤ a) (hac : a ≤ c)
    (hc : c ≤ 1) (hca : c - a = 1 / 4 ^ k) :
    (((Finset.range ℓ).filter fun j =>
        orbit 4 (stonehamAlpha 4 3) (3 ^ M + j) ∈ Set.Ico a c).card : ℝ)
      ≤ 6 * (1 / 4 ^ k) * ℓ + 8 * (1 / 4 ^ k) * 3 ^ (M - 1) := by
  have hM : 1 ≤ M := by omega
  have hord : (0 : ℝ) < 3 ^ (M - 1) := by positivity
  have h4k : (0 : ℝ) < 4 ^ k := by positivity
  have hlam : (0 : ℝ) < 1 / 4 ^ k := by positivity
  have herr : (2 : ℝ) / 3 ^ (M + 1) ≤ 1 / 4 ^ k := by
    rw [div_le_div_iff₀ (by positivity) h4k]
    have hp : (4 : ℝ) ^ k ≤ 9 ^ k := pow_le_pow_left₀ (by norm_num) (by norm_num) k
    have hpow : (9 : ℝ) ^ k = 3 ^ (2 * k) := by
      rw [show (9 : ℝ) = 3 ^ 2 by norm_num, pow_mul]
    calc
      (2 : ℝ) * 4 ^ k ≤ 3 * 9 ^ k := by nlinarith
      _ = 3 ^ (2 * k + 1) := by rw [hpow, pow_succ]; ring
      _ ≤ 3 ^ (M + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
      _ = 1 * 3 ^ (M + 1) := (one_mul _).symm
  have h7 : (7 : ℝ) ≤ 1 / 4 ^ k * 3 ^ (M - 1) := by
    rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ h4k]
    have h9 : (3 : ℝ) ^ (2 * k + 2) = 9 * 9 ^ k := by
      rw [pow_add, pow_mul]
      norm_num
      ring
    calc
      (7 : ℝ) * 4 ^ k ≤ 9 * 9 ^ k := by
        have hp : (4 : ℝ) ^ k ≤ 9 ^ k :=
          pow_le_pow_left₀ (by norm_num) (by norm_num) k
        nlinarith
      _ = 3 ^ (2 * k + 2) := h9.symm
      _ ≤ 3 ^ (M - 1) :=
        pow_le_pow_right₀ (by norm_num) (by omega)
  have hlo : (ℓ : ℝ) / 3 ^ (M - 1) ≤ 6 := by
    rw [div_le_iff₀ hord]
    have hcast : ((2 * 3 ^ M : ℕ) : ℝ) = 2 * 3 ^ M := by
      push_cast
      ring
    have h1 : (ℓ : ℝ) ≤ 2 * 3 ^ M := by
      calc
        (ℓ : ℝ) ≤ ((2 * 3 ^ M : ℕ) : ℝ) := by exact_mod_cast hℓ
        _ = 2 * 3 ^ M := hcast
    have h3M : (3 : ℝ) ^ M = 3 * 3 ^ (M - 1) := by
      rw [← pow_succ']
      congr 1
      omega
    nlinarith
  have hbase := stonehamFour_window_visit_bound M hM a c ha hac hc ℓ hℓ
  rw [hca] at hbase
  refine le_trans hbase ?_
  set w : ℝ := 1 / 4 ^ k + 2 / 3 ^ (M + 1) with hw
  set ord : ℝ := 3 ^ (M - 1) with horddef
  set L : ℝ := (ℓ : ℝ) / ord with hL
  have hLnn : 0 ≤ L := by positivity
  have hw2 : w ≤ 2 * (1 / 4 ^ k) := by rw [hw]; linarith
  have hwnn : 0 ≤ w := by rw [hw]; positivity
  have hexp : (L + 1) * (3 * w * ord + 2)
      = 3 * w * (L * ord) + 2 * L + 3 * w * ord + 2 := by ring
  have hLord : L * ord = (ℓ : ℝ) := by
    rw [hL]
    field_simp
  rw [hexp, hLord]
  have t1 : 3 * w * (ℓ : ℝ) ≤ 6 * (1 / 4 ^ k) * ℓ := by
    nlinarith [mul_le_mul_of_nonneg_right hw2 (show (0 : ℝ) ≤ ℓ by positivity)]
  have t2 : 2 * L ≤ 12 := by
    rw [hL, horddef]
    linarith
  have t3 : 3 * w * ord ≤ 6 * (1 / 4 ^ k) * ord := by
    nlinarith [mul_le_mul_of_nonneg_right hw2 hord.le]
  have tabsorb : (14 : ℝ) ≤ 2 * (1 / 4 ^ k) * ord := by
    rw [horddef]
    nlinarith
  linarith

/-- The Stoneham constant `α₄,₃` is normal in base four.  The proof uses only
the index-three ambient-residue upper bound for each period, not exact
equidistribution inside the multiplication-by-four orbit. -/
theorem isNormal_four_stonehamAlpha_four_three :
    IsNormal 4 (stonehamAlpha 4 3) := by
  classical
  apply isNormal_of_visit_upper_bound 4 (by norm_num) (stonehamAlpha 4 3) 15
  intro k m hm
  have hfr : Int.fract (stonehamAlpha 4 3) = stonehamAlpha 4 3 :=
    Int.fract_eq_self.mpr stonehamAlpha_four_three_mem_Ico
  have hb4 : ((4 : ℕ) : ℝ) = (4 : ℝ) := by norm_num
  rw [hfr, hb4]
  set a : ℝ := (m : ℝ) / 4 ^ k with hadef
  set c : ℝ := ((m : ℝ) + 1) / 4 ^ k with hcdef
  have h4k : (0 : ℝ) < 4 ^ k := by positivity
  have hm' : (m : ℝ) + 1 ≤ 4 ^ k := by
    have hmn : (m + 1 : ℕ) ≤ 4 ^ k := hm
    exact_mod_cast hmn
  have ha : 0 ≤ a := by rw [hadef]; positivity
  have hac : a ≤ c := by
    rw [hadef, hcdef]
    gcongr
    linarith
  have hc1 : c ≤ 1 := by
    rw [hcdef, div_le_one h4k]
    exact hm'
  have hca : c - a = 1 / 4 ^ k := by
    rw [hadef, hcdef]
    ring
  set M0 : ℕ := 2 * k + 3 with hM0def
  refine Filter.eventually_atTop.mpr ⟨3 ^ M0 * 4 ^ k + 1, fun N hN => ?_⟩
  have h3M0 : 27 ≤ 3 ^ M0 := by
    calc
      (27 : ℕ) = 3 ^ 3 := by norm_num
      _ ≤ 3 ^ M0 := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h4k1 : 1 ≤ 4 ^ k := Nat.one_le_pow _ _ (by norm_num)
  have hN2 : 2 ≤ N := by
    have := Nat.mul_le_mul h3M0 h4k1
    omega
  set Mmax : ℕ := Nat.log 3 (N - 1) with hMdef
  set P : ℕ → Prop := fun n =>
    orbit 4 (stonehamAlpha 4 3) n ∈ Set.Ico a c with hP
  have hsplit : (Finset.range N).filter P ⊆
      ((Finset.range (3 ^ M0)).filter P) ∪
        (Finset.Icc M0 Mmax).biUnion
          (fun M => (Finset.Ico (3 ^ M) (min N (3 ^ (M + 1)))).filter P) := by
    intro n hn
    simp only [Finset.mem_filter, Finset.mem_range] at hn
    obtain ⟨hnN, hPn⟩ := hn
    rcases Nat.lt_or_ge n (3 ^ M0) with hsmall | hbig
    · exact Finset.mem_union_left _
        (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hsmall, hPn⟩)
    · refine Finset.mem_union_right _ (Finset.mem_biUnion.mpr
        ⟨Nat.log 3 n, ?_, ?_⟩)
      · rw [Finset.mem_Icc]
        constructor
        · calc
            M0 = Nat.log 3 (3 ^ M0) := (Nat.log_pow (by norm_num) M0).symm
            _ ≤ Nat.log 3 n := Nat.log_mono_right hbig
        · rw [hMdef]
          exact Nat.log_mono_right (by omega)
      · rw [Finset.mem_filter, Finset.mem_Ico]
        have hn0 : n ≠ 0 := by
          have h1 : 1 ≤ 3 ^ M0 := Nat.one_le_pow _ _ (by norm_num)
          omega
        exact ⟨⟨Nat.pow_log_le_self 3 hn0,
          lt_min hnN (Nat.lt_pow_succ_log_self (by norm_num) n)⟩, hPn⟩
  have hcards : ((Finset.range N).filter P).card
      ≤ 3 ^ M0 + ∑ M ∈ Finset.Icc M0 Mmax,
          ((Finset.Ico (3 ^ M) (min N (3 ^ (M + 1)))).filter P).card := by
    calc
      ((Finset.range N).filter P).card
          ≤ (((Finset.range (3 ^ M0)).filter P) ∪
              (Finset.Icc M0 Mmax).biUnion
                (fun M =>
                  (Finset.Ico (3 ^ M) (min N (3 ^ (M + 1)))).filter P)).card :=
            Finset.card_le_card hsplit
      _ ≤ ((Finset.range (3 ^ M0)).filter P).card
            + ((Finset.Icc M0 Mmax).biUnion
                (fun M =>
                  (Finset.Ico (3 ^ M) (min N (3 ^ (M + 1)))).filter P)).card :=
            Finset.card_union_le _ _
      _ ≤ 3 ^ M0 + ∑ M ∈ Finset.Icc M0 Mmax,
            ((Finset.Ico (3 ^ M) (min N (3 ^ (M + 1)))).filter P).card :=
          add_le_add ((Finset.card_filter_le _ _).trans (Finset.card_range _).le)
            Finset.card_biUnion_le
  have hwin : ∀ M ∈ Finset.Icc M0 Mmax,
      (((Finset.Ico (3 ^ M) (min N (3 ^ (M + 1)))).filter P).card : ℝ)
        ≤ 6 * (1 / 4 ^ k) *
            ((min N (3 ^ (M + 1)) - 3 ^ M : ℕ) : ℝ)
          + 8 * (1 / 4 ^ k) * 3 ^ (M - 1) := by
    intro M hMmem
    obtain ⟨hMlo, hMhi⟩ := Finset.mem_Icc.mp hMmem
    have hℓ : min N (3 ^ (M + 1)) - 3 ^ M ≤ 2 * 3 ^ M := by
      have hmr : min N (3 ^ (M + 1)) ≤ 3 ^ (M + 1) := min_le_right _ _
      have h3 : (3 : ℕ) ^ (M + 1) = 3 * 3 ^ M := by
        rw [pow_succ]
        ring
      omega
    rw [card_filter_Ico_shift]
    have hbound := stonehamFour_per_window_bound k M
      (min N (3 ^ (M + 1)) - 3 ^ M) (by omega) hℓ a c ha hac hc1 hca
    simpa [hP] using hbound
  have hlog : (3 : ℕ) ^ Mmax ≤ N - 1 := by
    rw [hMdef]
    exact Nat.pow_log_le_self 3 (by omega)
  have hsum1 : ∑ M ∈ Finset.Icc M0 Mmax,
      ((min N (3 ^ (M + 1)) - 3 ^ M : ℕ) : ℝ) ≤ N :=
    sum_window_len_le N M0 Mmax (fun M hMm => by
      obtain ⟨-, h2⟩ := Finset.mem_Icc.mp hMm
      calc
        (3 : ℕ) ^ M ≤ 3 ^ Mmax := Nat.pow_le_pow_right (by norm_num) h2
        _ ≤ N - 1 := hlog
        _ ≤ N := by omega)
  have hsum2 : ∑ M ∈ Finset.Icc M0 Mmax, (3 : ℝ) ^ (M - 1) ≤ N := by
    calc
      ∑ M ∈ Finset.Icc M0 Mmax, (3 : ℝ) ^ (M - 1)
          ≤ ∑ M ∈ Finset.Icc M0 Mmax, (2 * (3 : ℝ) ^ (M - 1)) := by
            exact Finset.sum_le_sum fun M _ => by
              have : (0 : ℝ) ≤ 3 ^ (M - 1) := by positivity
              linarith
      _ ≤ (N : ℝ) := sum_ord_le M0 Mmax (by omega) N (by positivity) (by
        have h1 : (3 : ℕ) ^ Mmax ≤ N := le_trans hlog (by omega)
        exact_mod_cast h1)
  have hcardsR : (((Finset.range N).filter P).card : ℝ)
      ≤ 3 ^ M0 + ∑ M ∈ Finset.Icc M0 Mmax,
          (((Finset.Ico (3 ^ M) (min N (3 ^ (M + 1)))).filter P).card : ℝ) := by
    exact_mod_cast hcards
  have hchain : (((Finset.range N).filter P).card : ℝ)
      ≤ 3 ^ M0 + 14 * (1 / 4 ^ k) * N := by
    have hs := Finset.sum_le_sum hwin
    have hexp : ∑ M ∈ Finset.Icc M0 Mmax,
        (6 * (1 / 4 ^ k) *
            ((min N (3 ^ (M + 1)) - 3 ^ M : ℕ) : ℝ)
          + 8 * (1 / 4 ^ k) * 3 ^ (M - 1))
        = 6 * (1 / 4 ^ k) *
            (∑ M ∈ Finset.Icc M0 Mmax,
              ((min N (3 ^ (M + 1)) - 3 ^ M : ℕ) : ℝ))
          + 8 * (1 / 4 ^ k) *
            (∑ M ∈ Finset.Icc M0 Mmax, (3 : ℝ) ^ (M - 1)) := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    have b1 : 6 * (1 / 4 ^ k) *
        (∑ M ∈ Finset.Icc M0 Mmax,
          ((min N (3 ^ (M + 1)) - 3 ^ M : ℕ) : ℝ))
        ≤ 6 * (1 / 4 ^ k) * N := by
      apply mul_le_mul_of_nonneg_left hsum1
      positivity
    have b2 : 8 * (1 / 4 ^ k) *
        (∑ M ∈ Finset.Icc M0 Mmax, (3 : ℝ) ^ (M - 1))
        ≤ 8 * (1 / 4 ^ k) * N := by
      apply mul_le_mul_of_nonneg_left hsum2
      positivity
    calc
      (((Finset.range N).filter P).card : ℝ)
          ≤ 3 ^ M0 + ∑ M ∈ Finset.Icc M0 Mmax,
              (((Finset.Ico (3 ^ M) (min N (3 ^ (M + 1)))).filter P).card : ℝ) :=
            hcardsR
      _ ≤ 3 ^ M0 +
          (6 * (1 / 4 ^ k) * N + 8 * (1 / 4 ^ k) * N) := by
            have hs2 := le_trans hs (le_of_eq hexp)
            linarith [hs2, b1, b2]
      _ = 3 ^ M0 + 14 * (1 / 4 ^ k) * N := by ring
  have hNpos : (0 : ℝ) < N := by
    have : (0 : ℕ) < N := by omega
    exact_mod_cast this
  have hvc : (visitCount (orbit 4 (stonehamAlpha 4 3)) a c N : ℝ)
      = (((Finset.range N).filter P).card : ℝ) := rfl
  rw [div_le_iff₀ hNpos, hvc]
  have hNb : (3 : ℝ) ^ M0 ≤ 1 / 4 ^ k * N := by
    rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ h4k]
    have h1 : (3 ^ M0 * 4 ^ k : ℕ) ≤ N := by omega
    calc
      (3 : ℝ) ^ M0 * 4 ^ k = ((3 ^ M0 * 4 ^ k : ℕ) : ℝ) := by
        push_cast
        ring
      _ ≤ N := by exact_mod_cast h1
  calc
    (((Finset.range N).filter P).card : ℝ)
        ≤ 3 ^ M0 + 14 * (1 / 4 ^ k) * N := hchain
    _ ≤ 1 / 4 ^ k * N + 14 * (1 / 4 ^ k) * N := by linarith
    _ = 15 / 4 ^ k * N := by ring

/-- `α₄,₃` is also normal in base two, by descent from the power base
`4 = 2²`. -/
theorem isNormal_two_stonehamAlpha_four_three :
    IsNormal 2 (stonehamAlpha 4 3) := by
  apply isNormal_of_isNormal_pow (b := 2) (K := 2) (by norm_num) (by norm_num)
  norm_num
  exact isNormal_four_stonehamAlpha_four_three

theorem summable_stonehamSumTerm : Summable stonehamSumTerm := by
  exact summable_sterm.add summable_stonehamAlpha_four_three_term

/-- The two Stoneham series combine termwise into `stonehamSumTerm`. -/
theorem stoneham_sum_eq_tsum :
    stonehamAlpha 2 3 + stonehamAlpha 4 3 = ∑' j, stonehamSumTerm j := by
  rw [stonehamAlpha_two_three]
  unfold stoneham23 stonehamAlpha stonehamSumTerm
  exact (summable_sterm.tsum_add summable_stonehamAlpha_four_three_term).symm

/-- Once scaled past its right endpoint, a combined summand is an integer binary block. -/
theorem stonehamSumTerm_scaled_eq_block (j p : ℕ) (hp : 2 * 3 ^ (j + 1) ≤ p) :
    (2 : ℝ) ^ p * stonehamSumTerm j =
      (2 ^ (p - 2 * 3 ^ (j + 1)) *
        ((2 ^ (3 ^ (j + 1)) + 1) / 3 ^ (j + 1)) : ℕ) := by
  have hdvd : 3 ^ (j + 1) ∣ 2 ^ (3 ^ (j + 1)) + 1 :=
    (pow_dvd_pow 3 (by omega : j + 1 ≤ j + 2)).trans
      (three_pow_succ_dvd_two_pow_three_pow_add_one (j + 1))
  set q : ℕ := (2 ^ (3 ^ (j + 1)) + 1) / 3 ^ (j + 1) with hq
  have hqN : 3 ^ (j + 1) * q = 2 ^ (3 ^ (j + 1)) + 1 := by
    rw [hq]
    exact Nat.mul_div_cancel' hdvd
  have hqR : (3 : ℝ) ^ (j + 1) * q = 2 ^ (3 ^ (j + 1)) + 1 := by
    exact_mod_cast hqN
  have hpow : (2 : ℝ) ^ (p - 2 * 3 ^ (j + 1)) * 2 ^ (2 * 3 ^ (j + 1)) = 2 ^ p := by
    rw [← pow_add]
    congr 1
    omega
  change (2 : ℝ) ^ p *
      (1 / (3 ^ (j + 1) * 2 ^ (3 ^ (j + 1))) +
        1 / (3 ^ (j + 1) * 4 ^ (3 ^ (j + 1)))) = _
  rw [show (4 : ℝ) ^ (3 ^ (j + 1)) = 2 ^ (2 * 3 ^ (j + 1)) by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_mul]]
  rw [show ((2 ^ (p - 2 * 3 ^ (j + 1)) * q : ℕ) : ℝ) =
      (2 : ℝ) ^ (p - 2 * 3 ^ (j + 1)) * q by push_cast; rfl]
  field_simp
  rw [← hpow]
  rw [show (2 : ℝ) ^ (2 * 3 ^ (j + 1)) =
      2 ^ (3 ^ (j + 1)) * 2 ^ (3 ^ (j + 1)) by
    rw [← pow_add]; congr 1; omega]
  have hscaled := congrArg (fun z : ℝ =>
    2 ^ (p - 2 * 3 ^ (j + 1)) * 2 ^ (3 ^ (j + 1)) *
      (2 ^ (3 ^ (j + 1)) * 2 ^ (3 ^ (j + 1))) * z) hqR
  linear_combination -hscaled

/-- Later combined summands decrease at least geometrically. -/
theorem stonehamSumTerm_shift_le (k j : ℕ) :
    stonehamSumTerm (j + k) ≤ stonehamSumTerm k * (1 / 2 : ℝ) ^ j := by
  have hexp : 3 ^ (k + 1) + j ≤ 3 ^ (j + k + 1) := by
    have hj3 : j + 1 ≤ 3 ^ j := Nat.lt_pow_self (by norm_num)
    have hP : 1 ≤ 3 ^ (k + 1) := Nat.one_le_pow _ _ (by norm_num)
    calc
      3 ^ (k + 1) + j ≤ 3 ^ (k + 1) * (j + 1) := by nlinarith
      _ ≤ 3 ^ (k + 1) * 3 ^ j := Nat.mul_le_mul_left _ hj3
      _ = 3 ^ (j + k + 1) := by rw [← pow_add]; congr 1; omega
  have hkey2 : (3 : ℝ) ^ (k + 1) * 2 ^ (3 ^ (k + 1)) * 2 ^ j
      ≤ 3 ^ (j + k + 1) * 2 ^ (3 ^ (j + k + 1)) := by
    have h3 : (3 : ℝ) ^ (k + 1) ≤ 3 ^ (j + k + 1) :=
      pow_le_pow_right₀ (by norm_num) (by omega)
    have h2 : (2 : ℝ) ^ (3 ^ (k + 1)) * 2 ^ j ≤ 2 ^ (3 ^ (j + k + 1)) := by
      rw [← pow_add]
      exact pow_le_pow_right₀ one_le_two hexp
    calc
      (3 : ℝ) ^ (k + 1) * 2 ^ (3 ^ (k + 1)) * 2 ^ j =
          3 ^ (k + 1) * (2 ^ (3 ^ (k + 1)) * 2 ^ j) := by ring
      _ ≤ 3 ^ (j + k + 1) * 2 ^ (3 ^ (j + k + 1)) :=
        mul_le_mul h3 h2 (by positivity) (by positivity)
  have hkey4 : (3 : ℝ) ^ (k + 1) * 4 ^ (3 ^ (k + 1)) * 2 ^ j
      ≤ 3 ^ (j + k + 1) * 4 ^ (3 ^ (j + k + 1)) := by
    have h3 : (3 : ℝ) ^ (k + 1) ≤ 3 ^ (j + k + 1) :=
      pow_le_pow_right₀ (by norm_num) (by omega)
    have h24 : (2 : ℝ) ^ j ≤ 4 ^ j := by gcongr <;> norm_num
    have h4 : (4 : ℝ) ^ (3 ^ (k + 1)) * 2 ^ j ≤ 4 ^ (3 ^ (j + k + 1)) := by
      calc
        (4 : ℝ) ^ (3 ^ (k + 1)) * 2 ^ j ≤ 4 ^ (3 ^ (k + 1)) * 4 ^ j :=
          mul_le_mul_of_nonneg_left h24 (by positivity)
        _ = 4 ^ (3 ^ (k + 1) + j) := (pow_add _ _ _).symm
        _ ≤ 4 ^ (3 ^ (j + k + 1)) := pow_le_pow_right₀ (by norm_num) hexp
    calc
      (3 : ℝ) ^ (k + 1) * 4 ^ (3 ^ (k + 1)) * 2 ^ j =
          3 ^ (k + 1) * (4 ^ (3 ^ (k + 1)) * 2 ^ j) := by ring
      _ ≤ 3 ^ (j + k + 1) * 4 ^ (3 ^ (j + k + 1)) :=
        mul_le_mul h3 h4 (by positivity) (by positivity)
  have hs2 : 1 / ((3 : ℝ) ^ (j + k + 1) * 2 ^ (3 ^ (j + k + 1))) ≤
      1 / (3 ^ (k + 1) * 2 ^ (3 ^ (k + 1))) * (1 / 2) ^ j := by
    rw [div_pow, one_pow, div_mul_div_comm, one_mul]
    exact div_le_div_of_nonneg_left (by positivity) (by positivity) hkey2
  have hs4 : 1 / ((3 : ℝ) ^ (j + k + 1) * 4 ^ (3 ^ (j + k + 1))) ≤
      1 / (3 ^ (k + 1) * 4 ^ (3 ^ (k + 1))) * (1 / 2) ^ j := by
    rw [div_pow, one_pow, div_mul_div_comm, one_mul]
    exact div_le_div_of_nonneg_left (by positivity) (by positivity) hkey4
  unfold stonehamSumTerm
  exact (add_le_add hs2 hs4).trans_eq (by ring)

/-- At the left edge of a zero window, twice the scaled tail majorant is below one. -/
theorem stonehamSumTerm_scaled_lt_half (k p : ℕ) (hp : p ≤ 3 ^ (k + 1)) :
    2 * ((2 : ℝ) ^ p * stonehamSumTerm k) < 1 := by
  have hpow : (2 : ℝ) ^ p ≤ 2 ^ (3 ^ (k + 1)) :=
    pow_le_pow_right₀ one_le_two hp
  have hthreeN : 3 ≤ 3 ^ (k + 1) := by
    calc
      3 = 3 ^ 1 := by norm_num
      _ ≤ 3 ^ (k + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hthree : (3 : ℝ) ≤ 3 ^ (k + 1) := by exact_mod_cast hthreeN
  have height : (8 : ℝ) ≤ 2 ^ (3 ^ (k + 1)) := by
    calc
      (8 : ℝ) = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ (3 ^ (k + 1)) := pow_le_pow_right₀ one_le_two hthreeN
  have hfirst : (2 : ℝ) ^ p *
      (1 / (3 ^ (k + 1) * 2 ^ (3 ^ (k + 1)))) ≤ 1 / 3 := by
    calc
      (2 : ℝ) ^ p * (1 / (3 ^ (k + 1) * 2 ^ (3 ^ (k + 1)))) ≤
          2 ^ (3 ^ (k + 1)) * (1 / (3 ^ (k + 1) * 2 ^ (3 ^ (k + 1)))) :=
        mul_le_mul_of_nonneg_right hpow (by positivity)
      _ = 1 / (3 : ℝ) ^ (k + 1) := by field_simp
      _ ≤ 1 / 3 := one_div_le_one_div_of_le (by norm_num) hthree
  have hfourpow : (4 : ℝ) ^ (3 ^ (k + 1)) =
      2 ^ (3 ^ (k + 1)) * 2 ^ (3 ^ (k + 1)) := by
    rw [show (4 : ℝ) = 2 * 2 by norm_num, mul_pow]
  have hsecond : (2 : ℝ) ^ p *
      (1 / (3 ^ (k + 1) * 4 ^ (3 ^ (k + 1)))) ≤ 1 / 24 := by
    calc
      (2 : ℝ) ^ p * (1 / (3 ^ (k + 1) * 4 ^ (3 ^ (k + 1)))) ≤
          2 ^ (3 ^ (k + 1)) * (1 / (3 ^ (k + 1) * 4 ^ (3 ^ (k + 1)))) :=
        mul_le_mul_of_nonneg_right hpow (by positivity)
      _ = 1 / ((3 : ℝ) ^ (k + 1) * 2 ^ (3 ^ (k + 1))) := by
        rw [hfourpow]
        field_simp
      _ ≤ 1 / 24 := by
        apply one_div_le_one_div_of_le (by norm_num)
        nlinarith
  unfold stonehamSumTerm
  nlinarith [hfirst, hsecond]

theorem stonehamSumTerm_le_geom (j : ℕ) :
    stonehamSumTerm j ≤ (1 / 12 : ℝ) * (1 / 2) ^ j := by
  have hs : sterm j ≤ (1 / 24 : ℝ) * (1 / 2) ^ j := by
    unfold sterm
    rw [div_pow, one_pow, mul_one_div, div_div]
    apply div_le_div_of_nonneg_left one_pos.le (by positivity)
    have h3 : (3 : ℝ) ≤ 3 ^ (j + 1) :=
      le_self_pow₀ (by norm_num) (by omega)
    have h2 : (2 : ℝ) ^ (j + 3) ≤ 2 ^ (3 ^ (j + 1)) := by
      apply pow_le_pow_right₀ one_le_two
      calc
        j + 3 ≤ 3 * (j + 1) := by omega
        _ ≤ 3 ^ (j + 1) := by
          calc
            3 * (j + 1) ≤ 3 * 3 ^ j := by
              have : j + 1 ≤ 3 ^ j := Nat.lt_pow_self (by norm_num)
              omega
            _ = 3 ^ (j + 1) := (pow_succ' 3 j).symm
    calc
      (24 : ℝ) * 2 ^ j = 3 * 2 ^ (j + 3) := by ring
      _ ≤ 3 ^ (j + 1) * 2 ^ (3 ^ (j + 1)) :=
        mul_le_mul h3 h2 (by positivity) (by positivity)
  have hf : 1 / ((3 : ℝ) ^ (j + 1) * 4 ^ (3 ^ (j + 1))) ≤ sterm j := by
    unfold sterm
    apply div_le_div_of_nonneg_left one_pos.le (by positivity)
    gcongr
    norm_num
  unfold stonehamSumTerm
  unfold sterm at hs hf
  nlinarith [hs, hf]

/-- The sum lies in `[0,1)`, so `digitOf` reads it without an integer-part correction. -/
theorem stoneham_sum_mem_Ico :
    stonehamAlpha 2 3 + stonehamAlpha 4 3 ∈ Set.Ico (0 : ℝ) 1 := by
  rw [stoneham_sum_eq_tsum]
  constructor
  · exact tsum_nonneg fun j => by unfold stonehamSumTerm; positivity
  · have hgeom : Summable fun j : ℕ => (1 / 12 : ℝ) * (1 / 2) ^ j :=
      (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left _
    have hle := summable_stonehamSumTerm.tsum_le_tsum stonehamSumTerm_le_geom hgeom
    rw [tsum_mul_left, tsum_geometric_two] at hle
    linarith

/-- `α₂,₃ + α₄,₃ = Σ_k ((2^(3^k)+1)/3^k)·4^(−3^k)` is a sum of disjoint integer blocks
(`3^(k+1) ∣ 2^(3^k) + 1`, lifting the exponent), so its binary digits vanish on
`[2·3^k, 3^(k+1))` (0-indexed `digitOf`). -/
theorem digitOf_stoneham_sum_eq_zero (k i : ℕ) (h₁ : 2 * 3 ^ k ≤ i) (h₂ : i < 3 ^ (k + 1)) :
    digitOf 2 (Int.fract (stonehamAlpha 2 3 + stonehamAlpha 4 3)) i = 0 := by
  set x : ℝ := stonehamAlpha 2 3 + stonehamAlpha 4 3 with hx
  set p : ℕ := i + 1 with hp
  have hp_le : p ≤ 3 ^ (k + 1) := by omega
  have hxfrac : Int.fract x = x := Int.fract_eq_self.mpr stoneham_sum_mem_Ico
  set g : ℕ → ℝ := fun j => (2 : ℝ) ^ p * stonehamSumTerm j with hg
  have hgsum : Summable g := summable_stonehamSumTerm.mul_left _
  have hmul : x * (2 : ℝ) ^ p = ∑' j, g j := by
    rw [hx, stoneham_sum_eq_tsum, tsum_mul_left, mul_comm]
  have hshift : Summable fun j => g (j + k) := (summable_nat_add_iff k).2 hgsum
  have hsplit : ∑' j, g j = (∑ j ∈ Finset.range k, g j) + ∑' j, g (j + k) :=
    (hgsum.sum_add_tsum_nat_add k).symm
  set T : ℝ := ∑' j, g (j + k) with hT
  set A : ℕ := ∑ j ∈ Finset.range k,
    2 ^ (p - 2 * 3 ^ (j + 1)) *
      ((2 ^ (3 ^ (j + 1)) + 1) / 3 ^ (j + 1)) with hA
  have hHead : (∑ j ∈ Finset.range k, g j) = (A : ℝ) := by
    rw [hA]
    push_cast
    refine Finset.sum_congr rfl fun j hj => ?_
    have hjk : j < k := Finset.mem_range.mp hj
    have hjpow : 3 ^ (j + 1) ≤ 3 ^ k :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [hg]
    simpa only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] using
      stonehamSumTerm_scaled_eq_block j p (by omega)
  have hAeven : 2 ∣ A := by
    rw [hA]
    refine Finset.dvd_sum fun j hj => ?_
    have hjk : j < k := Finset.mem_range.mp hj
    have hjpow : 3 ^ (j + 1) ≤ 3 ^ k :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    have hexp : 0 < p - 2 * 3 ^ (j + 1) := by omega
    exact Dvd.dvd.mul_right (dvd_pow_self 2 hexp.ne') _
  have hT0 : 0 ≤ T := by
    rw [hT]
    exact tsum_nonneg fun j => by
      simp only [hg]
      exact mul_nonneg (pow_nonneg (by norm_num) _) (by unfold stonehamSumTerm; positivity)
  have hTlt : T < 1 := by
    have hterm : ∀ j, g (j + k) ≤ g k * (1 / 2 : ℝ) ^ j := by
      intro j
      simp only [hg]
      calc
        (2 : ℝ) ^ p * stonehamSumTerm (j + k) ≤
            2 ^ p * (stonehamSumTerm k * (1 / 2 : ℝ) ^ j) :=
          mul_le_mul_of_nonneg_left (stonehamSumTerm_shift_le k j) (by positivity)
        _ = (2 ^ p * stonehamSumTerm k) * (1 / 2 : ℝ) ^ j := by ring
    have hgeom : Summable fun j : ℕ => g k * (1 / 2 : ℝ) ^ j :=
      (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left _
    have hle := hshift.tsum_le_tsum hterm hgeom
    rw [hT]
    refine lt_of_le_of_lt hle ?_
    rw [tsum_mul_left, tsum_geometric_two, hg]
    simpa [mul_comm] using stonehamSumTerm_scaled_lt_half k p hp_le
  have hval : x * (2 : ℝ) ^ p = (A : ℝ) + T := by
    rw [hmul, hsplit, hHead]
  have hfl : ⌊x * (2 : ℝ) ^ p⌋ = (A : ℤ) := by
    rw [hval, Int.floor_eq_iff]
    constructor <;> push_cast <;> linarith
  unfold digitOf
  rw [hxfrac, show ((2 : ℕ) : ℝ) = (2 : ℝ) by norm_num, ← hp, hfl,
    Int.toNat_natCast, Nat.mod_eq_zero_of_dvd hAeven]

/-- Hence the zero frequency is pushed toward `2/3` at `n = 3^(k+1)`. -/
theorem not_isSimplyNormal_stoneham_sum :
    ¬ IsSimplyNormal 2 (stonehamAlpha 2 3 + stonehamAlpha 4 3) := by
  classical
  intro hnormal
  let x := stonehamAlpha 2 3 + stonehamAlpha 4 3
  let s : ℕ → ℕ := digitOf 2 (Int.fract x)
  let Z : ℕ → ℕ := fun n => ((Finset.range n).filter fun i => s i = 0).card
  have hcount (n : ℕ) : countOccurrences [0] ((List.range n).map s) = Z n :=
    Failures.countOccurrences_zero_eq_card s n
  have hlim : Tendsto (fun n => (Z n : ℝ) / n) atTop (nhds (1 / 2 : ℝ)) := by
    simpa [x, s, hcount, Z] using hnormal 0 (by norm_num)
  rw [Metric.tendsto_atTop] at hlim
  obtain ⟨K, hK⟩ := hlim (1 / 100) (by norm_num)
  let k := max K 1
  let n₁ := 2 * 3 ^ k
  let n₂ := 3 ^ (k + 1)
  have hkK : K ≤ k := le_max_left _ _
  have hkpos : 0 < k := lt_of_lt_of_le (by norm_num) (le_max_right K 1)
  have hkpow : k ≤ 3 ^ k := (Nat.lt_pow_self (by norm_num)).le
  have hn₁K : K ≤ n₁ := by dsimp [n₁]; omega
  have hn₂K : K ≤ n₂ := by
    dsimp [n₂]
    exact hkK.trans (hkpow.trans (Nat.pow_le_pow_right (by norm_num) (by omega)))
  have hn₁₂ : n₁ ≤ n₂ := by
    dsimp [n₁, n₂]
    rw [pow_succ]
    omega
  have hforced : ∀ i, i ∈ Finset.Ico n₁ n₂ → s i = 0 := by
    intro i hi
    rw [Finset.mem_Ico] at hi
    exact digitOf_stoneham_sum_eq_zero k i hi.1 hi.2
  have hstep : Z n₁ + (n₂ - n₁) ≤ Z n₂ := by
    have hdisj : Disjoint ((Finset.range n₁).filter fun i => s i = 0)
        (Finset.Ico n₁ n₂) := by
      rw [Finset.disjoint_left]
      intro a ha hb
      rw [Finset.mem_filter, Finset.mem_range] at ha
      rw [Finset.mem_Ico] at hb
      omega
    have hsub : ((Finset.range n₁).filter fun i => s i = 0) ∪ Finset.Ico n₁ n₂
        ⊆ (Finset.range n₂).filter fun i => s i = 0 := by
      intro a ha
      rw [Finset.mem_union] at ha
      rw [Finset.mem_filter, Finset.mem_range]
      rcases ha with ha | ha
      · rw [Finset.mem_filter, Finset.mem_range] at ha
        exact ⟨ha.1.trans_le hn₁₂, ha.2⟩
      · rw [Finset.mem_Ico] at ha
        exact ⟨ha.2, hforced a (Finset.mem_Ico.mpr ha)⟩
    have hc := Finset.card_le_card hsub
    simpa [Z, Finset.card_union_of_disjoint hdisj, Nat.card_Ico] using hc
  have h₁ := hK n₁ hn₁K
  have h₂ := hK n₂ hn₂K
  rw [Real.dist_eq, abs_lt] at h₁ h₂
  have hn₁pos : (0 : ℝ) < n₁ := by positivity
  have hn₂pos : (0 : ℝ) < n₂ := by positivity
  have e₁ : (1 / 2 - 1 / 100) * (n₁ : ℝ) < Z n₁ := by
    have hx : (1 / 2 - 1 / 100 : ℝ) < (Z n₁ : ℝ) / n₁ := by linarith [h₁.1]
    rwa [lt_div_iff₀ hn₁pos] at hx
  have e₂ : (Z n₂ : ℝ) < (1 / 2 + 1 / 100) * n₂ := by
    have hx : (Z n₂ : ℝ) / n₂ < (1 / 2 + 1 / 100 : ℝ) := by linarith [h₂.2]
    rwa [div_lt_iff₀ hn₂pos] at hx
  have e₃ : (Z n₁ : ℝ) + ((n₂ : ℝ) - n₁) ≤ Z n₂ := by
    have hc := (Nat.cast_le (α := ℝ)).2 hstep
    push_cast [Nat.cast_sub hn₁₂] at hc
    linarith
  have hn₁ : (n₁ : ℝ) = 2 * (3 : ℝ) ^ k := by simp [n₁]
  have hn₂ : (n₂ : ℝ) = 3 * (3 : ℝ) ^ k := by
    push_cast
    simp [n₂, pow_succ]
    ring
  have hkR : (0 : ℝ) < (3 : ℝ) ^ k := by positivity
  rw [hn₁] at e₁ e₃
  rw [hn₂] at e₂ e₃
  nlinarith

/-- The coupled Stoneham sum is not binary normal.  This is the exact obstruction behind the
failure of the proposed "normal Stoneham pieces remain normal after addition" route. -/
theorem not_isNormal_stoneham_sum :
    ¬ IsNormal 2 (stonehamAlpha 2 3 + stonehamAlpha 4 3) := by
  exact fun h => not_isSimplyNormal_stoneham_sum (isSimplyNormal_of_isNormal h)

/-- Two explicitly binary-normal Stoneham constants whose sum is not even
simply normal. -/
theorem stoneham_pair_normal_not_isSimplyNormal_sum :
    IsNormal 2 (stonehamAlpha 2 3) ∧
      IsNormal 2 (stonehamAlpha 4 3) ∧
        ¬ IsSimplyNormal 2 (stonehamAlpha 2 3 + stonehamAlpha 4 3) := by
  refine ⟨?_, isNormal_two_stonehamAlpha_four_three,
    not_isSimplyNormal_stoneham_sum⟩
  rw [stonehamAlpha_two_three]
  exact isNormal_two_stoneham23

end NormalNumbers
