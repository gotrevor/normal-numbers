/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.CantorLiouville
import NormalNumbers.LevinSparse
import NormalNumbers.SchedFamily

/-!
# The exact normality profile of the Cantor–Liouville points: `IsNormal b x ↔ ¬ 3 ∣ b`

Strengthens Bugeaud 10.37 (`CantorLiouville.exists_computable_liouville_mem_cantorSet_isNormal_two`)
to: there is a computable `e` with `x = cantorLiouvilleReal e ∈ cantorSet`, `x` Liouville, and
for every base `b ≥ 2`, `IsNormal b x ↔ ¬ 3 ∣ b`
(`exists_computable_liouville_mem_cantorSet_normalProfile`).

## The true statement, and the contrast with Cassels

Cassels (1959; Schmidt 1960 independently) proved that for the Cantor measure `μ_K`, almost
every point of `K` is normal to **every base that is not a power of 3**, including `6, 12, 15, …`
(`Literature.Cassels1959`, stated with `μ_K` = the law of `pt (fun _ => true)`).  For *our*
points the profile is different: the forced zero-runs `[a_k, (k+2)a_k)` needed for the Liouville
property make `bʲx` lie within `b⁻¹` of an integer for a fraction `→ 1` of `j ≤ N_k` whenever
`3 ∣ b`, for **every** coin sequence (`not_isNormal_of_three_dvd`).  So the profile is
`¬ 3 ∣ b`, not "`b` is not a power of 3"; base `6` separates them (`not_isNormal_six`).

## Mechanism (bases coprime to 3)

`CantorLiouville.secondMoment_le` with `2ᵏ → bᵏ`.  The base-2 arithmetic input was that `2`
generates `(ℤ/3ᴹ)ˣ`.  For general `b` coprime to 3, with `t = v₃(b² − 1)` (`tb`), `⟨b²⟩` is the
congruence subgroup `1 + 3ᵗℤ` mod `3ᴹ` (3-adic `1 + 3ℤ₃` is procyclic), so the orbit `c·bᵐ`
covers a union of full residue classes mod `3ᵗ`, each lifted uniformly.  The digit-by-digit
`three_point` induction of `residue_sum_le` then runs from position `t` instead of `1`: a constant
loss `(3/2)ᵗ` (`sum_Hf_le_b`).  Pairs with large `v₃(bᵈ − 1)` stay rare by LTE,
`v₃(bᵈ − 1) ≤ t + v₃(d)` (`padicValNat_pow_sub_one_le`): another constant `3ᵗ`.  Both are
absorbed by `3ᵗ < b²`, giving the constant `16 b⁶ |h|` in `secondMoment_le_b`.

## Difficulty check (known-false siblings)

* `3 ∣ b` (incl. `b = 3, 6, 9, 12`): must fail, and the mechanism refuses it — `sum_Hf_le_b`
  needs `b` a unit mod 3 (for `3 ∣ b`, `c·bᵐ` has `v₃ ≥ m`, so `Hf` sees only the shifted
  zeros, cf. `tdig_mul_three_pow`).  The failure is proved separately and for every `ω`
  (`not_isNormal_of_three_dvd`, via `fract_lt_of_mem_run`).
* `b = 4, 16`: covered both directly and via base 2.  `b = 10, 28` (`b ≡ 1 mod 9`, small orbit
  mod `3ᴹ`): `t = 2, 3`; only the constant changes.

## Status

All leaves proved; the computable headline uses only `propext`, `Classical.choice`,
`Quot.sound`.  The family derandomizer is `SchedFamily.exists_computable_normal_sched_family'`
(base `b` runs at resolution `n / H b`, `H b ≥ 74016 (κ b + 1)(Zc + 1) 2ᵇ`, so all bases at one
stage cost `O((J+1)^{-2})`).
-/

open MeasureTheory Filter Topology

namespace NormalNumbers.CantorLiouvilleAll

open CantorLiouville DecayAeNormal ExplicitSquare CantorSelfSimilar

/-! ## Cited contrast -/

namespace Literature

/-- **Cassels 1959** (J. W. S. Cassels, *On a problem of Steinhaus about normal numbers*, Colloq.
Math. 7 (1959) 95–101; independently W. M. Schmidt, *On normal numbers*, Pacific J. Math. 10
(1960) 661–672): almost every point of the middle-third Cantor set for the Cantor measure is
normal to every base that is not a power of `3`.  The Cantor measure is the law of
`pt (fun _ => true)` under fair coins (all ternary digits `0`/`2`, independent, uniform).
Recorded only as the contrast to `not_isNormal_six`; nothing here uses it. -/
def Cassels1959 : Prop :=
  ∀ᵐ ω ∂coinMeasure, ∀ b : ℕ, 2 ≤ b → (∀ k : ℕ, b ≠ 3 ^ k) → IsNormal b (pt (fun _ => true) ω)

end Literature

/-! ## Arithmetic: bases coprime to 3 -/

/-- The 3-adic defect `t = v₃(b² − 1)` of a base coprime to 3 (`t = 1` for `b = 2`). -/
def tb (b : ℕ) : ℕ := padicValNat 3 (b ^ 2 - 1)

theorem three_dvd_sq_sub_one {b : ℕ} (h3 : ¬ 3 ∣ b) : 3 ∣ b ^ 2 - 1 := by
  have : b % 3 = 1 ∨ b % 3 = 2 := by omega
  apply Nat.dvd_of_mod_eq_zero
  apply Nat.sub_mod_eq_zero_of_mod_eq
  rw [Nat.pow_mod]; rcases this with h | h <;> rw [h]

theorem padicValNat_sq_pow_sub_one {b : ℕ} (hb : 2 ≤ b) (h3 : ¬ 3 ∣ b) {d : ℕ} (hd : d ≠ 0) :
    padicValNat 3 ((b ^ 2) ^ d - 1) = tb b + padicValNat 3 d := by
  have := padicValNat.pow_sub_pow (p := 3) (x := b ^ 2) (y := 1) (by decide) (by nlinarith)
    (by simpa using three_dvd_sq_sub_one h3)
    (fun h => h3 (Nat.prime_three.dvd_of_dvd_pow h)) (n := d) hd
  simpa [tb] using this

/-- **LTE bound.**  Confidence 95%.

English proof.  `b² ≡ 1 mod 3`.  If `b ≡ 1 mod 3`: Mathlib's `padicValNat.pow_sub_pow`
(odd prime, `3 ∣ b − 1`, `3 ∤ b`) gives `v₃(bᵈ − 1) = v₃(b − 1) + v₃(d) ≤ v₃(b² − 1) + v₃(d)`
(as `b − 1 ∣ b² − 1`).  If `b ≡ 2 mod 3`: for odd `d`, `bᵈ ≡ 2 mod 3`, so `v₃ = 0`; for
`d = 2d'`, apply LTE to `(b²)^{d'} − 1`: `v₃ = v₃(b² − 1) + v₃(d') ≤ t + v₃(d)`. -/
theorem padicValNat_pow_sub_one_le {b : ℕ} (hb : 2 ≤ b) (h3 : ¬ 3 ∣ b) {d : ℕ} (hd : d ≠ 0) :
    padicValNat 3 (b ^ d - 1) ≤ tb b + padicValNat 3 d := by
  rw [← padicValNat_sq_pow_sub_one hb h3 hd]
  have hne : (b ^ 2) ^ d - 1 ≠ 0 := by
    have : 2 ≤ (b ^ 2) ^ d := le_trans (by nlinarith) (Nat.le_self_pow hd _)
    omega
  rw [← padicValNat_dvd_iff_le hne]
  refine (pow_padicValNat_dvd).trans ?_
  have := Nat.sub_dvd_pow_sub_pow (x := b ^ d) (y := 1) (n := 2)
  rwa [one_pow, ← pow_mul, mul_comm, pow_mul] at this


/-- `3ᵗ < b²`, so every constant `3^{O(t)}` is `b^{O(1)}`. -/
theorem three_pow_tb_lt {b : ℕ} (hb : 2 ≤ b) : 3 ^ tb b < b ^ 2 := by
  have hne : b ^ 2 - 1 ≠ 0 := by
    have : 4 ≤ b ^ 2 := by nlinarith
    omega
  have h1 : 3 ^ tb b ≤ b ^ 2 - 1 := Nat.le_of_dvd (by omega) pow_padicValNat_dvd
  have : 1 ≤ b ^ 2 := by nlinarith
  omega

theorem posSet_card_succ (free : ℕ → Bool) (v k : ℕ) (hk : 1 ≤ k) :
    (posSet free v (k + 1)).card =
        (posSet free v k).card + (if free (v + k) = true then 1 else 0) := by
  unfold posSet
  rw [show v + (k + 1) = (v + k) + 1 by ring, Finset.range_add_one, Finset.filter_insert]
  by_cases hf : free (v + k) = true
  · rw [if_pos ⟨by omega, hf⟩, Finset.card_insert_of_notMem (by simp), if_pos hf]
  · rw [if_neg (fun h => hf h.2), if_neg hf, add_zero]

theorem posSet_card_le (free : ℕ → Bool) (v k : ℕ) : (posSet free v k).card ≤ k - 1 := by
  unfold posSet
  have : (Finset.range (v + k)).filter (fun p => v + 1 ≤ p ∧ free p = true) ⊆ Finset.Ico (v + 1) (v + k) := by
    intro p hp; simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico] at hp ⊢; omega
  have := Finset.card_le_card this
  rw [Nat.card_Ico] at this; omega

/-- Residue bound from level `t`. -/
theorem residue_sum_from (free : ℕ → Bool) (v t : ℕ) (ht : 1 ≤ t) : ∀ n r : ℕ,
    ∑ w ∈ Finset.range (3 ^ n), Hf free v (t + n) ((3 ^ t * w + r : ℕ) : ℝ) ≤
      3 ^ n * (2 / 3 : ℝ) ^ (posSet free v (t + n)).card * (3 / 2 : ℝ) ^ (posSet free v t).card := by
  intro n
  induction n with
  | zero =>
    intro r
    simp only [pow_zero, Finset.range_one, Finset.sum_singleton, add_zero, one_mul]
    rw [← mul_pow, show (2 / 3 : ℝ) * (3 / 2) = 1 by norm_num, one_pow]
    exact Hf_le_one _ _ _ _
  | succ n ih =>
    intro r
    set k := t + n
    have hk : 1 ≤ k := by omega
    rw [show t + (n + 1) = k + 1 by omega, pow_succ, sum_range_mul_eq, Finset.sum_comm]
    have hstep : ∀ w ∈ Finset.range (3 ^ n),
        ∑ s ∈ Finset.range 3, Hf free v (k + 1) ((3 ^ t * (3 ^ n * s + w) + r : ℕ) : ℝ) ≤
        (if free (v + k) = true then 2 else 3) * Hf free v k ((3 ^ t * w + r : ℕ) : ℝ) := by
      intro w _
      have hrw : ∀ s : ℕ, ((3 ^ t * (3 ^ n * s + w) + r : ℕ) : ℝ) =
          ((3 ^ t * w + r : ℕ) : ℝ) + 3 ^ k * (s : ℤ) := by
        intro s; push_cast; simp only [k]; rw [pow_add]; ring
      have hper : ∀ s : ℕ, Hf free v k ((3 ^ t * (3 ^ n * s + w) + r : ℕ) : ℝ) =
          Hf free v k ((3 ^ t * w + r : ℕ) : ℝ) := by
        intro s; rw [hrw, Hf_periodic]
      simp_rw [Hf_succ free v k hk, hper, ← Finset.mul_sum]
      rw [mul_comm]
      gcongr
      · exact Hf_nonneg _ _ _ _
      by_cases hf : free (v + k) = true
      · simp only [hf, if_true]
        have := three_point (2 * Real.pi * (3 ^ v * ((3 ^ t * w + r : ℕ) : ℝ)) / 3 ^ (v + k + 1))
        refine le_of_eq_of_le (Finset.sum_congr rfl fun s _ => ?_) this
        congr 2
        rw [hrw]
        push_cast
        field_simp
        ring
      · simp [hf]
    refine (Finset.sum_le_sum hstep).trans ?_
    rw [← Finset.mul_sum, posSet_card_succ free v k hk]
    have := ih r
    by_cases hf : free (v + k) = true
    · simp only [hf, if_true]
      calc (2 : ℝ) * _ ≤ 2 * (3 ^ n * (2 / 3 : ℝ) ^ (posSet free v k).card *
            (3 / 2 : ℝ) ^ (posSet free v t).card) := by gcongr
        _ = _ := by rw [pow_succ, pow_succ]; ring
    · simp only [hf, if_false, Bool.false_eq_true, add_zero]
      calc (3 : ℝ) * _ ≤ 3 * (3 ^ n * (2 / 3 : ℝ) ^ (posSet free v k).card *
            (3 / 2 : ℝ) ^ (posSet free v t).card) := by gcongr
        _ = _ := by rw [pow_succ]; ring

/-- Partial periods of a periodic nonnegative sequence. -/
theorem sum_periodic_le (g : ℕ → ℝ) (hg : ∀ m, 0 ≤ g m) (P : ℕ) (hP : 0 < P)
    (hper : ∀ m, g (m + P) = g m) (B : ℝ) (hB : ∑ m ∈ Finset.range P, g m ≤ P * B) (K : ℕ) :
    ∑ m ∈ Finset.range K, g m ≤ (K + P) * B := by
  have hper' : ∀ q m, g (P * q + m) = g m := by
    intro q m
    induction q with
    | zero => simp
    | succ q ih => rw [show P * (q + 1) + m = (P * q + m) + P by ring, hper, ih]
  have hB0 : 0 ≤ B := by
    have : 0 ≤ ∑ m ∈ Finset.range P, g m := Finset.sum_nonneg fun m _ => hg m
    have hPr : (0 : ℝ) < P := by exact_mod_cast hP
    nlinarith
  set q := K / P + 1
  have hKq : K ≤ P * q := by
    have := Nat.lt_div_mul_add (a := K) hP
    simp only [q]; nlinarith [Nat.div_add_mod K P, Nat.mod_lt K hP]
  calc ∑ m ∈ Finset.range K, g m ≤ ∑ m ∈ Finset.range (P * q), g m :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.2 hKq) (fun m _ _ => hg m)
    _ = q * ∑ m ∈ Finset.range P, g m := by
        rw [sum_range_mul_eq]; simp_rw [hper']; simp
    _ ≤ q * (P * B) := by gcongr
    _ ≤ _ := by
        rw [← mul_assoc]
        gcongr
        have h1 : (K / P) * P ≤ K := Nat.div_mul_le_self K P
        have : ((K / P : ℕ) : ℝ) * P ≤ K := by exact_mod_cast h1
        simp only [q]; push_cast; linarith

theorem one_le_tb {b : ℕ} (hb : 2 ≤ b) (h3 : ¬ 3 ∣ b) : 1 ≤ tb b := by
  have hne : b ^ 2 - 1 ≠ 0 := by have : 4 ≤ b ^ 2 := by nlinarith
                                 omega
  exact one_le_padicValNat_of_dvd hne (three_dvd_sq_sub_one h3)

theorem coprime_three_pow {x : ℕ} (hx : ¬ 3 ∣ x) (k : ℕ) : Nat.Coprime x (3 ^ k) :=
  Nat.Coprime.pow_right _ ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 hx).symm

theorem three_pow_dvd_sq_pow_sub_one {b : ℕ} (hb : 2 ≤ b) (h3 : ¬ 3 ∣ b) {k d : ℕ} (hd : d ≠ 0) :
    3 ^ k ∣ (b ^ 2) ^ d - 1 ↔ k ≤ tb b + padicValNat 3 d := by
  have hne : (b ^ 2) ^ d - 1 ≠ 0 := by
    have : 2 ≤ (b ^ 2) ^ d := le_trans (by nlinarith) (Nat.le_self_pow hd _)
    omega
  rw [padicValNat_dvd_iff_le hne, padicValNat_sq_pow_sub_one hb h3 hd]

theorem sq_pow_modEq_one {b : ℕ} (m : ℕ) : (b ^ 2) ^ m ≡ 1 [MOD 3 ^ tb b] := by
  have h1 : b ^ 2 ≡ 1 [MOD 3 ^ tb b] := by
    rcases Nat.eq_zero_or_pos b with rfl | hb
    · simp [tb, Nat.modEq_one]
    refine ((Nat.modEq_iff_dvd' (Nat.one_le_pow _ _ hb)).2 pow_padicValNat_dvd).symm
  simpa using h1.pow m

theorem orbit_sum_eq (free : ℕ → Bool) {b : ℕ} (hb : 2 ≤ b) (h3 : ¬ 3 ∣ b) (v n x : ℕ)
    (hx : ¬ 3 ∣ x) :
    ∑ m ∈ Finset.range (3 ^ n), Hf free v (tb b + n) ((x * (b ^ 2) ^ m : ℕ) : ℝ) =
      ∑ w ∈ Finset.range (3 ^ n), Hf free v (tb b + n) ((3 ^ tb b * w + x % 3 ^ tb b : ℕ) : ℝ) := by
  set t := tb b
  set k := t + n
  set Q := 3 ^ k
  have hQ : Q = 3 ^ t * 3 ^ n := pow_add _ _ _
  have htQ : 3 ^ t ∣ Q := ⟨_, hQ⟩
  set φ : ℕ → ℕ := fun m => (x * (b ^ 2) ^ m % Q) / 3 ^ t
  have hmod : ∀ m, (x * (b ^ 2) ^ m % Q) % 3 ^ t = x % 3 ^ t := by
    intro m
    rw [Nat.mod_mod_of_dvd _ htQ]
    have := (sq_pow_modEq_one (b := b) m).mul_left x
    rw [mul_one] at this
    exact this
  have hrec : ∀ m, x * (b ^ 2) ^ m % Q = 3 ^ t * φ m + x % 3 ^ t := by
    intro m; rw [← hmod m]; exact (Nat.div_add_mod _ _).symm
  have hmaps : ∀ m ∈ Finset.range (3 ^ n), φ m ∈ Finset.range (3 ^ n) := by
    intro m _
    simp only [Finset.mem_range, φ]
    rw [Nat.div_lt_iff_lt_mul (by positivity)]
    calc _ < Q := Nat.mod_lt _ (by positivity)
      _ = _ := by rw [hQ, mul_comm]
  have hinj : Set.InjOn φ (Finset.range (3 ^ n) : Set ℕ) := by
    have key : ∀ m m', m < m' → m' < 3 ^ n → φ m ≠ φ m' := by
      intro m m' hmm' hm' heq
      have h1 : x * (b ^ 2) ^ m ≡ x * (b ^ 2) ^ m * (b ^ 2) ^ (m' - m) [MOD Q] := by
        rw [mul_assoc, ← pow_add, Nat.add_sub_cancel' hmm'.le]
        unfold Nat.ModEq; rw [hrec, hrec, heq]
      have hcop : Nat.Coprime Q (x * (b ^ 2) ^ m) :=
        (Nat.Coprime.mul_left (coprime_three_pow hx k)
          (Nat.Coprime.pow_left _ (Nat.Coprime.pow_left _ (coprime_three_pow h3 k)))).symm
      have h2 : 1 ≡ (b ^ 2) ^ (m' - m) [MOD Q] :=
        Nat.ModEq.cancel_left_of_coprime hcop (by simpa using h1)
      have hd : m' - m ≠ 0 := by omega
      have h4 := (three_pow_dvd_sq_pow_sub_one hb h3 hd).1
        ((Nat.modEq_iff_dvd' (Nat.one_le_pow _ _ (by positivity))).1 h2)
      have h5 : 3 ^ padicValNat 3 (m' - m) ≤ m' - m := Nat.le_of_dvd (by omega) pow_padicValNat_dvd
      have h6 : 3 ^ n ≤ 3 ^ padicValNat 3 (m' - m) := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    intro m hm m' hm' heq
    simp only [Finset.coe_range, Set.mem_Iio] at hm hm'
    by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · exact key m m' h hm' heq
    · exact key m' m h hm heq.symm
  refine Finset.sum_nbij φ hmaps hinj
    (Finset.surjOn_of_injOn_of_card_le _ hmaps hinj le_rfl) ?_
  intro m _
  rw [← hrec, Hf_mod]

/-- **Coset version of `sum_Hf_le`.**  Confidence 85%.

English proof.  Write `L = orderOf (b : ZMod 3^{j+1}) ≤ φ(3^{j+1}) = 2·3ʲ`; the summand has
period `L` in `m` (`Hf_periodic`, as in `sum_Hf_le`), so it suffices to show one period sums to
`≤ L (3/2)ᵗ (2/3)^{|posSet|}`.  If `j + 1 < t` this is trivial: `|posSet| ≤ j < t` and `Hf ≤ 1`.
Otherwise `⟨b²⟩ = 1 + 3ᵗℤ` in `(ℤ/3^{j+1})ˣ` (`b² = 1 + 3ᵗu`, `3 ∤ u`; the subgroup
`1 + 3ᵗℤ` is cyclic of order `3^{j+1−t}` and `b²` has exactly that order), so `⟨b⟩` is a union of
`L / 3^{j+1−t}` residue classes mod `3ᵗ`, and one period of `c·bᵐ mod 3^{j+1}` enumerates the
coset `c⟨b⟩` once.  For a fixed class `r mod 3ᵗ`, the `residue_sum_le` induction from `k = t`
(not `k = 1`) gives `Σ_{u ≡ r} Hf free v (j+1) u ≤ 3^{j+1−t} (2/3)^{#free in [v+t, v+j]}` (each
step fixes the lower digits and uses `three_point` on the new top digit).  The positions of
`posSet` below `v + t` number `≤ t − 1`. -/
theorem sum_Hf_le_b (free : ℕ → Bool) {b : ℕ} (hb : 2 ≤ b) (h3 : ¬ 3 ∣ b) (v j c : ℕ)
    (hc : ¬ 3 ∣ c) (N : ℕ) :
    ∑ m ∈ Finset.range N, Hf free v (j + 1) ((c * b ^ m : ℕ) : ℝ) ≤
      (N + 2 * 3 ^ j) * (3 / 2 : ℝ) ^ tb b * (2 / 3 : ℝ) ^ (posSet free v (j + 1)).card := by
  set t := tb b
  have ht := one_le_tb hb h3
  set ck := (posSet free v (j + 1)).card
  have hck := posSet_card_le free v (j + 1)
  have hf0 : ∀ u, 0 ≤ Hf free v (j + 1) u := fun u => Hf_nonneg _ _ _ _
  by_cases hjt : j + 1 < t
  · have h1 : ∑ m ∈ Finset.range N, Hf free v (j + 1) ((c * b ^ m : ℕ) : ℝ) ≤ N := by
      refine (Finset.sum_le_sum fun m _ => Hf_le_one free v (j + 1) _).trans ?_
      simp
    have h2 : (1 : ℝ) ≤ (3 / 2 : ℝ) ^ t * (2 / 3 : ℝ) ^ ck := by
      have : (2 / 3 : ℝ) ^ t ≤ (2 / 3 : ℝ) ^ ck :=
        pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
      have e : (3 / 2 : ℝ) ^ t * (2 / 3 : ℝ) ^ t = 1 := by rw [← mul_pow]; norm_num
      nlinarith [pow_pos (by norm_num : (0:ℝ) < 3 / 2) t]
    have h3' : (0 : ℝ) ≤ 2 * 3 ^ j := by positivity
    rw [mul_assoc]
    nlinarith
  push Not at hjt
  obtain ⟨n, hn⟩ : ∃ n, j + 1 = t + n := ⟨j + 1 - t, by omega⟩
  set P := 3 ^ n
  set B : ℝ := (2 / 3 : ℝ) ^ ck * (3 / 2 : ℝ) ^ (posSet free v t).card
  have hB0 : 0 ≤ B := by positivity
  set g : ℕ → ℕ → ℝ := fun x m => Hf free v (j + 1) ((x * (b ^ 2) ^ m : ℕ) : ℝ)
  have hgK : ∀ x, ¬ 3 ∣ x → ∀ K, ∑ m ∈ Finset.range K, g x m ≤ (K + P) * B := by
    intro x hx K
    refine sum_periodic_le (g x) (fun m => hf0 _) P (by positivity) ?_ B ?_ K
    · intro m
      obtain ⟨s, hs⟩ := (three_pow_dvd_sq_pow_sub_one hb h3 (k := j + 1) (d := P)
        (by positivity)).2 (by simp [P]; omega)
      have hP1 : 1 ≤ (b ^ 2) ^ P := Nat.one_le_pow _ _ (by positivity)
      have : x * (b ^ 2) ^ (m + P) = x * (b ^ 2) ^ m + 3 ^ (j + 1) * (x * (b ^ 2) ^ m * s) := by
        rw [pow_add, show (b ^ 2) ^ P = 3 ^ (j + 1) * s + 1 by omega]; ring
      simp only [g]
      rw [this]
      have := Hf_periodic free v (j + 1) ((x * (b ^ 2) ^ m : ℕ) : ℝ) ((x * (b ^ 2) ^ m * s : ℕ) : ℤ)
      rw [← this]; congr 1; push_cast; ring
    · simp only [g]
      rw [hn, orbit_sum_eq free hb h3 v n x hx, ← hn]
      have := residue_sum_from free v t ht n (x % 3 ^ t)
      rw [← hn] at this
      refine this.trans (le_of_eq ?_)
      simp only [B, P]; push_cast; ring
  set N' := (N + 1) / 2
  have hNN : N ≤ 2 * N' := by omega
  have hsplit : ∑ m ∈ Finset.range N, Hf free v (j + 1) ((c * b ^ m : ℕ) : ℝ) ≤
      ∑ m ∈ Finset.range N', g c m + ∑ m ∈ Finset.range N', g (c * b) m := by
    refine (Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.2 hNN)
      (fun m _ _ => hf0 _)).trans (le_of_eq ?_)
    rw [sum_range_mul_eq, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun m _ => ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, g]
    congr 3 <;> ring
  have hcb : ¬ 3 ∣ c * b := fun h => ((Nat.Prime.dvd_mul Nat.prime_three).1 h).elim hc h3
  have hct := posSet_card_le free v t
  have hBle : B ≤ (2 / 3 : ℝ) ^ ck * (3 / 2 : ℝ) ^ (t - 1) := by
    simp only [B]; gcongr; norm_num
  have hPj : (P : ℝ) ≤ 3 ^ j := by
    have : P ≤ 3 ^ j := Nat.pow_le_pow_right (by norm_num) (by omega)
    exact_mod_cast this
  have hN' : (2 * N' : ℝ) ≤ N + 1 := by
    have : 2 * N' ≤ N + 1 := by omega
    exact_mod_cast this
  have h3j : (1 : ℝ) ≤ 3 ^ j := one_le_pow₀ (by norm_num)
  have ht' : (3 / 2 : ℝ) ^ t = (3 / 2 : ℝ) ^ (t - 1) * (3 / 2) := by
    rw [← pow_succ]; congr 1; omega
  refine hsplit.trans ((add_le_add (hgK c hc N') (hgK (c * b) hcb N')).trans ?_)
  rw [ht']
  have hX : (0 : ℝ) ≤ (2 / 3 : ℝ) ^ ck * (3 / 2 : ℝ) ^ (t - 1) := by positivity
  have hN0 : (0 : ℝ) ≤ N := by positivity
  calc ((N' : ℝ) + P) * B + ((N' : ℝ) + P) * B = (2 * N' + 2 * P) * B := by ring
    _ ≤ (2 * N' + 2 * P) * ((2 / 3 : ℝ) ^ ck * (3 / 2 : ℝ) ^ (t - 1)) := by gcongr
    _ ≤ (N + 2 * 3 ^ j) * (3 / 2) * ((2 / 3 : ℝ) ^ ck * (3 / 2 : ℝ) ^ (t - 1)) := by
        gcongr; linarith
    _ = _ := by ring


theorem good_shift_b (free : ℕ → Bool) {b : ℕ} (hb : 2 ≤ b) (h3 : ¬ 3 ∣ b) (M N : ℕ)
    (hMN : 3 ^ M ≤ N) (c : ℕ) (hc : c ≠ 0)
    (hv : padicValNat 3 c + 1 ≤ freeCount free M / 2) :
    ∑ m ∈ Finset.range N, Bf free M ((c * b ^ m : ℕ) : ℝ) ≤
      2 * N * (3 / 2 : ℝ) ^ tb b * (2 / 3 : ℝ) ^ (freeCount free M / 2) := by
  obtain ⟨v, c', hc', hcc⟩ := Nat.exists_eq_pow_mul_and_not_dvd hc 3 (by norm_num)
  have hvv : padicValNat 3 c = v := by
    rw [hcc, padicValNat.mul (by positivity) (by rintro rfl; simp at hc'),
      padicValNat.prime_pow, padicValNat.eq_zero_of_not_dvd hc', add_zero]
  rw [hvv] at hv
  have hFM : freeCount free M ≤ M := by
    unfold freeCount; exact (Finset.card_filter_le _ _).trans (by simp)
  obtain ⟨j, hj⟩ : ∃ j, M = v + (j + 1) := ⟨M - v - 1, by omega⟩
  have hterm : ∀ m, Bf free M ((c * b ^ m : ℕ) : ℝ) ≤ Hf free v (j + 1) ((c' * b ^ m : ℕ) : ℝ) := by
    intro m
    have := Bf_le_Hf free v (j + 1) ((c' * b ^ m : ℕ) : ℝ)
    rw [← hj] at this
    refine le_of_eq_of_le ?_ this
    congr 1; rw [hcc]; push_cast; ring
  have hcard := freeCount_le free v (j + 1)
  rw [← hj] at hcard
  have hL : (2 * 3 ^ j : ℝ) ≤ N := by
    have : 2 * 3 ^ j ≤ 3 ^ M := by
      rw [hj, pow_add, pow_succ]; nlinarith [Nat.one_le_pow v 3 (by norm_num), Nat.one_le_pow j 3 (by norm_num)]
    exact_mod_cast this.trans hMN
  calc _ ≤ ∑ m ∈ Finset.range N, Hf free v (j + 1) ((c' * b ^ m : ℕ) : ℝ) :=
        Finset.sum_le_sum fun m _ => hterm m
    _ ≤ (N + 2 * 3 ^ j) * (3 / 2 : ℝ) ^ tb b * (2 / 3 : ℝ) ^ (posSet free v (j + 1)).card :=
        sum_Hf_le_b free hb h3 v j c' hc' N
    _ ≤ (2 * N) * (3 / 2 : ℝ) ^ tb b * (2 / 3 : ℝ) ^ (freeCount free M / 2) := by
        gcongr ?_ * _ * ?_
        · linarith
        · exact pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)

theorem bad_count_b {b : ℕ} (hb : 2 ≤ b) (h3 : ¬ 3 ∣ b) (e W N : ℕ) :
    ((Finset.Ico 1 N).filter (fun m => W ≤ e + padicValNat 3 (b ^ m - 1))).card ≤
      N / 3 ^ (W - e - tb b) := by
  rw [← Nat.Ioc_filter_dvd_card_eq_div]
  refine Finset.card_le_card ?_
  intro m hm
  simp only [Finset.mem_filter, Finset.mem_Ico, Finset.mem_Ioc] at hm ⊢
  refine ⟨⟨by omega, by omega⟩, ?_⟩
  have h1 := padicValNat_pow_sub_one_le hb h3 (d := m) (by omega)
  exact (padicValNat_dvd_iff_le (by omega)).2 (by omega)

theorem secondMoment_expand_b (free : ℕ → Bool) (b : ℕ) (h : ℤ) (M N : ℕ) :
    ∫ ω, ‖∑ k ∈ Finset.range N, ee (h * (b : ℝ) ^ k * pt free ω)‖ ^ 2 ∂coinMeasure ≤
      ∑ n ∈ Finset.range N, ∑ m ∈ Finset.range N, Bf free M (h * ((b : ℝ) ^ n - (b : ℝ) ^ m)) := by
  have hG := measurable_pt free
  have hint : ∀ ξ : ℝ, Integrable (fun ω => ee (ξ * pt free ω)) coinMeasure := fun ξ =>
    Integrable.of_bound ((measurable_ee.comp (hG.const_mul ξ)).aestronglyMeasurable) 1
      (Eventually.of_forall fun ω => (norm_ee _).le)
  have hexp : ∀ ω, ((‖∑ k ∈ Finset.range N, ee (h * (b : ℝ) ^ k * pt free ω)‖ ^ 2 : ℝ) : ℂ) =
      ∑ n ∈ Finset.range N, ∑ m ∈ Finset.range N,
        ee ((h * ((b : ℝ) ^ n - (b : ℝ) ^ m)) * pt free ω) := by
    intro ω
    rw [sq_norm_sum_ee (fun k => h * (b : ℝ) ^ k * pt free ω)]
    refine Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun m _ => ?_
    congr 1; ring
  have hI : ((∫ ω, ‖∑ k ∈ Finset.range N, ee (h * (b : ℝ) ^ k * pt free ω)‖ ^ 2 ∂coinMeasure : ℝ) : ℂ) =
      ∑ n ∈ Finset.range N, ∑ m ∈ Finset.range N,
        ∫ ω, ee ((h * ((b : ℝ) ^ n - (b : ℝ) ^ m)) * pt free ω) ∂coinMeasure := by
    rw [← integral_complex_ofReal]
    simp_rw [hexp]
    rw [integral_finsetSum _ fun n _ => integrable_finsetSum _ fun m _ => hint _]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [integral_finsetSum _ fun m _ => hint _]
  have := congrArg Complex.re hI
  rw [Complex.ofReal_re] at this
  rw [this]
  refine (Complex.re_le_norm _).trans ((norm_sum_le _ _).trans ?_)
  refine Finset.sum_le_sum fun n _ => (norm_sum_le _ _).trans ?_
  exact Finset.sum_le_sum fun m _ => charFun_real M free _

theorem secondMoment_le_explicit_b (free : ℕ → Bool) {b : ℕ} (hb : 2 ≤ b) (h3 : ¬ 3 ∣ b) (h : ℤ)
    (hh : h ≠ 0) (N : ℕ) (hN : 1 ≤ N) :
    ∫ ω, ‖∑ k ∈ Finset.range N, ee (h * (b : ℝ) ^ k * pt free ω)‖ ^ 2 ∂coinMeasure ≤
      (N : ℝ) ^ 2 * (N : ℝ) ^ (-(1 / 2 : ℝ)) +
        3 * (3 ^ (padicValNat 3 h.natAbs + tb b) + 2 * (3 / 2 : ℝ) ^ tb b) * (N : ℝ) ^ 2 *
          Real.exp (-(Real.log (3 / 2) / 2) * freeCount free (Nat.log 3 N / 2)) := by
  set e := padicValNat 3 h.natAbs
  set t := tb b
  set M := Nat.log 3 N / 2
  set F := freeCount free M
  set W := F / 2
  have hb1 : (1 : ℝ) ≤ b := by exact_mod_cast (by omega : 1 ≤ b)
  have hMN : 3 ^ M ≤ N :=
    (Nat.pow_le_pow_right (by norm_num) (Nat.div_le_self _ _)).trans
      (Nat.pow_log_le_self 3 (by omega))
  set G : ℕ → ℕ → ℝ := fun d m => Bf free M (h * ((b : ℝ) ^ d - 1) * (b : ℝ) ^ m)
  have hpair := pair_sum_le (fun n m => Bf free M (h * ((b : ℝ) ^ n - (b : ℝ) ^ m))) G
    (fun d m => Bf_nonneg _ _ _) (fun n => Bf_le_one _ _ _)
    (fun n m hmn => le_of_eq (by
      simp only [G]; congr 1
      rw [show (b : ℝ) ^ n = (b : ℝ) ^ (n - m) * (b : ℝ) ^ m by rw [← pow_add]; congr 1; omega]; ring))
    (fun n m hmn => le_of_eq (by
      simp only [G]; rw [← Bf_neg]; congr 1
      rw [show (b : ℝ) ^ m = (b : ℝ) ^ (m - n) * (b : ℝ) ^ n by rw [← pow_add]; congr 1; omega]; ring)) N
  set P := (2 / 3 : ℝ) ^ W
  set T := (3 / 2 : ℝ) ^ t
  have hT : 0 ≤ T := by positivity
  have hshift : ∀ d ∈ Finset.Ico 1 N, ∑ m ∈ Finset.range N, G d m ≤
      (if W ≤ e + padicValNat 3 (b ^ d - 1) then (N : ℝ) else 0) + 2 * N * T * P := by
    intro d hd
    simp only [Finset.mem_Ico] at hd
    have hd1 : 1 ≤ b ^ d - 1 := by
      have : 2 ≤ b ^ d := le_trans hb (Nat.le_self_pow (by omega) b)
      omega
    split_ifs with hbad
    · refine (Finset.sum_le_sum fun m _ => Bf_le_one free M _).trans ?_
      have : (0 : ℝ) ≤ 2 * N * T * P := by positivity
      simp; linarith
    · rw [zero_add]
      set c := h.natAbs * (b ^ d - 1)
      have hc : c ≠ 0 := Nat.mul_ne_zero (Int.natAbs_ne_zero.2 hh) (by omega)
      have hv : padicValNat 3 c = e + padicValNat 3 (b ^ d - 1) :=
        padicValNat.mul (Int.natAbs_ne_zero.2 hh) (by omega)
      refine le_of_eq_of_le (Finset.sum_congr rfl fun m _ => ?_)
        (good_shift_b free hb h3 M N hMN c hc (by omega))
      simp only [G]
      rw [← Bf_abs]
      congr 1
      have hd2 : (0 : ℝ) ≤ (b : ℝ) ^ d - 1 := by
        have : (1:ℝ) ≤ (b : ℝ) ^ d := one_le_pow₀ hb1; linarith
      simp only [c]
      push_cast [Nat.cast_sub (Nat.one_le_pow _ _ (by omega : 0 < b))]
      rw [abs_mul, abs_mul, abs_of_pos (by positivity : (0:ℝ) < (b : ℝ) ^ m),
        abs_of_nonneg hd2, Nat.cast_natAbs, Int.cast_abs]
  have hsumd : ∑ d ∈ Finset.Ico 1 N, ∑ m ∈ Finset.range N, G d m ≤
      N * ((N / 3 ^ (W - e - t) : ℕ) : ℝ) + N * (2 * N * T * P) := by
    refine (Finset.sum_le_sum hshift).trans ?_
    rw [Finset.sum_add_distrib, ← Finset.sum_filter, Finset.sum_const, Finset.sum_const,
      nsmul_eq_mul, nsmul_eq_mul, Nat.card_Ico]
    have hbc := bad_count_b hb h3 e W N
    have : (((Finset.Ico 1 N).filter (fun m => W ≤ e + padicValNat 3 (b ^ m - 1))).card : ℝ) ≤
        ((N / 3 ^ (W - e - t) : ℕ) : ℝ) := by exact_mod_cast hbc
    have hN1 : ((N - 1 : ℕ) : ℝ) ≤ N := by exact_mod_cast Nat.sub_le N 1
    have : (0 : ℝ) ≤ 2 * N * T * P := by positivity
    nlinarith
  have hdiv : ((N / 3 ^ (W - e - t) : ℕ) : ℝ) ≤ N * 3 ^ (e + t) * P := by
    have h1 : (N / 3 ^ (W - e - t)) * 3 ^ W ≤ N * 3 ^ (e + t) := by
      calc (N / 3 ^ (W - e - t)) * 3 ^ W ≤ (N / 3 ^ (W - e - t)) * (3 ^ (W - e - t) * 3 ^ (e + t)) := by
            gcongr; rw [← pow_add]; exact Nat.pow_le_pow_right (by norm_num) (by omega)
        _ = (N / 3 ^ (W - e - t)) * 3 ^ (W - e - t) * 3 ^ (e + t) := by ring
        _ ≤ N * 3 ^ (e + t) := by gcongr; exact Nat.div_mul_le_self _ _
    have h2 : ((N / 3 ^ (W - e - t) : ℕ) : ℝ) * 3 ^ W ≤ N * 3 ^ (e + t) := by exact_mod_cast h1
    have h3' : (2 / 3 : ℝ) ^ W * 3 ^ W = 2 ^ W := by rw [← mul_pow]; norm_num
    have h4 : (1 : ℝ) ≤ 2 ^ W := one_le_pow₀ (by norm_num)
    have h5 : (0 : ℝ) < 3 ^ W := by positivity
    rw [← mul_le_mul_iff_of_pos_right h5]
    calc _ ≤ (N : ℝ) * 3 ^ (e + t) := h2
      _ ≤ (N : ℝ) * 3 ^ (e + t) * 2 ^ W := le_mul_of_one_le_right (by positivity) h4
      _ = _ := by rw [mul_assoc _ ((2 / 3 : ℝ) ^ W), h3']
  have hexp := pow_two_sub_le W F rfl
  have hNr : (N : ℝ) ≤ (N : ℝ) ^ 2 * (N : ℝ) ^ (-(1 / 2 : ℝ)) := by
    have hN0 : (1 : ℝ) ≤ N := by exact_mod_cast hN
    have : (N : ℝ) ^ 2 * (N : ℝ) ^ (-(1 / 2 : ℝ)) = N * (N : ℝ) ^ (1 / 2 : ℝ) := by
      rw [show (N : ℝ) ^ 2 = N * N ^ (1 : ℝ) by rw [Real.rpow_one]; ring, mul_assoc,
        ← Real.rpow_add (by positivity)]
      norm_num
    rw [this]
    have : (1 : ℝ) ≤ (N : ℝ) ^ (1 / 2 : ℝ) := Real.one_le_rpow hN0 (by norm_num)
    nlinarith
  have hI := (secondMoment_expand_b free b h M N).trans hpair
  set E := Real.exp (-(Real.log (3 / 2) / 2) * F)
  have hE : 0 ≤ E := (Real.exp_pos _).le
  have hP : 0 ≤ P := by positivity
  have hN0 : (0 : ℝ) ≤ N := by positivity
  have hfin : ∫ ω, ‖∑ k ∈ Finset.range N, ee (h * (b : ℝ) ^ k * pt free ω)‖ ^ 2 ∂coinMeasure ≤
      N + 2 * ((N : ℝ) ^ 2 * (3 ^ (e + t) + 2 * T) * P) := by
    have := mul_le_mul_of_nonneg_left hdiv hN0
    nlinarith
  have hK : (0 : ℝ) ≤ 3 ^ (e + t) + 2 * T := by positivity
  calc _ ≤ N + 2 * ((N : ℝ) ^ 2 * (3 ^ (e + t) + 2 * T) * P) := hfin
    _ ≤ (N : ℝ) ^ 2 * (N : ℝ) ^ (-(1 / 2 : ℝ)) + 2 * ((N : ℝ) ^ 2 * (3 ^ (e + t) + 2 * T) * (3 / 2 * E)) := by
        gcongr
    _ = _ := by simp only [T, E, F, M]; ring

/-- **Cassels second moment, base `b` coprime to 3.**  Confidence 80%.

English proof.  `secondMoment_le_explicit` verbatim with `2 → b`: `secondMoment_expand` (base-free
up to `2ᵏ → bᵏ`) gives `Σ_{n,m} Bf free M (h(bⁿ − bᵐ))`; the pair `m < n` has frequency
`h(bᵈ − 1)·bᵐ`, `d = n − m`.  Good `d` (`e + v₃(bᵈ−1) + 1 ≤ F/2`, `e = v₃ h`): `good_shift` with
`sum_Hf_le_b` in place of `sum_Hf_le`, an extra `(3/2)ᵗ`.  Bad `d`: by
`padicValNat_pow_sub_one_le` they have `v₃(d) ≥ W − e − t`, so there are
`≤ N / 3^{W−e−t−1}` of them (`bad_count` with `3^{t}` more).  The explicit constant becomes
`(1 + 3(3^{e+t+1} + 2))(3/2)ᵗ ≤ 16·|h|·(9/2)ᵗ ≤ 16·|h|·b⁶` (`3ᵉ ≤ |h|`, `three_pow_tb_lt`). -/
theorem secondMoment_le_b (free : ℕ → Bool) {b : ℕ} (hb : 2 ≤ b) (h3 : ¬ 3 ∣ b) (h : ℤ)
    (hh : h ≠ 0) (N : ℕ) (hN : 1 ≤ N) :
    ∫ ω, ‖∑ k ∈ Finset.range N, ee (h * (b : ℝ) ^ k * pt free ω)‖ ^ 2 ∂coinMeasure ≤
      16 * (b : ℝ) ^ 6 * |(h : ℝ)| * (N : ℝ) ^ 2 *
        (Real.exp (-(Real.log (3 / 2) / 2) * freeCount free (Nat.log 3 N / 2)) +
          (N : ℝ) ^ (-(1 / 2 : ℝ))) := by
  refine (secondMoment_le_explicit_b free hb h3 h hh N hN).trans ?_
  set e := padicValNat 3 h.natAbs
  set t := tb b
  set E := Real.exp (-(Real.log (3 / 2) / 2) * freeCount free (Nat.log 3 N / 2))
  set R := (N : ℝ) ^ (-(1 / 2 : ℝ))
  have hE : 0 ≤ E := (Real.exp_pos _).le
  have hR : 0 ≤ R := by positivity
  have hN2 : (0 : ℝ) ≤ (N : ℝ) ^ 2 := by positivity
  have he : (3 : ℝ) ^ e ≤ |(h : ℝ)| := by
    have : 3 ^ e ≤ h.natAbs := Nat.le_of_dvd (Int.natAbs_pos.2 hh) pow_padicValNat_dvd
    rw [← Int.cast_abs, ← Int.natCast_natAbs]; exact_mod_cast this
  have ht : (3 : ℝ) ^ t ≤ (b : ℝ) ^ 2 := by exact_mod_cast (three_pow_tb_lt hb).le
  have hT : (3 / 2 : ℝ) ^ t ≤ 3 ^ t := pow_le_pow_left₀ (by norm_num) (by norm_num) t
  have hb1 : (1 : ℝ) ≤ b := by exact_mod_cast (by omega : 1 ≤ b)
  have hh1 : (1 : ℝ) ≤ |(h : ℝ)| := le_trans (one_le_pow₀ (by norm_num)) he
  have hb2 : (b : ℝ) ^ 2 ≤ (b : ℝ) ^ 6 := pow_le_pow_right₀ hb1 (by norm_num)
  have hb6 : (1 : ℝ) ≤ (b : ℝ) ^ 6 := one_le_pow₀ hb1
  have h3t : (0 : ℝ) ≤ 3 ^ t := by positivity
  have hK : 3 * ((3 : ℝ) ^ (e + t) + 2 * (3 / 2 : ℝ) ^ t) ≤ 16 * (b : ℝ) ^ 6 * |(h : ℝ)| := by
    rw [pow_add]
    have : (3 : ℝ) ^ e * 3 ^ t ≤ |(h : ℝ)| * 3 ^ t := by gcongr
    have : |(h : ℝ)| * 3 ^ t ≤ |(h : ℝ)| * (b : ℝ) ^ 6 := by gcongr; linarith
    have : (1 : ℝ) * 3 ^ t ≤ |(h : ℝ)| * 3 ^ t := by gcongr
    nlinarith
  have h16 : (1 : ℝ) ≤ 16 * (b : ℝ) ^ 6 * |(h : ℝ)| := by nlinarith
  have := mul_le_mul_of_nonneg_right hK (mul_nonneg hN2 hE)
  have := mul_le_mul_of_nonneg_right h16 (mul_nonneg hN2 hR)
  nlinarith


/-! ## Davenport–Erdős–LeVeque, base `b` (copy of `ae_isNormal_two_of_secondMoment`) -/

/-- **DEL along a schedule with ratio → 1, base `b`.**  Proved: the base-2 proof with
`2 → b` and `LevinSparse.fourierMean_orbit`. -/
theorem ae_isNormal_of_secondMoment {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] {b : ℕ} (hb : 2 ≤ b) (G : Ω → ℝ) (hG : Measurable G) (n : ℕ → ℕ)
    (hn : StrictMono n) (hratio : Tendsto (fun j => (n (j + 1) : ℝ) / n j) atTop (𝓝 1))
    (hsum : ∀ h : ℤ, h ≠ 0 → Summable fun j =>
      (∫ ω, ‖∑ k ∈ Finset.range (n j), ee (h * (b : ℝ) ^ k * G ω)‖ ^ 2 ∂μ) / ((n j : ℝ) ^ 2)) :
    ∀ᵐ ω ∂μ, IsNormal b (G ω) := by
  have hone : ∀ h : ℤ, h ≠ 0 → ∀ᵐ ω ∂μ, Tendsto
      (fun N : ℕ => (∑ k ∈ Finset.range N, ee (h * (b : ℝ) ^ k * G ω)) / (N : ℂ)) atTop (𝓝 0) := by
    intro h hh
    set S : ℕ → Ω → ℂ := fun N ω => ∑ k ∈ Finset.range N, ee (h * (b : ℝ) ^ k * G ω) with hSdef
    have hSm : ∀ N, Measurable (S N) := fun N =>
      Finset.measurable_sum _ fun k _ => measurable_ee.comp (hG.const_mul _)
    have hSb : ∀ N ω, ‖S N ω‖ ≤ N := fun N ω =>
      (norm_sum_le _ _).trans (by simp [norm_ee])
    set f : ℕ → Ω → ℝ := fun j ω => ‖S (n j) ω‖ ^ 2 / ((n j : ℝ)) ^ 2 with hfdef
    have hf0 : ∀ j ω, 0 ≤ f j ω := fun j ω => by positivity
    have hfm : ∀ j, Measurable (f j) := fun j => (((hSm _).norm.pow_const 2).div_const _)
    have hfi : ∀ j, Integrable (f j) μ := fun j =>
      Integrable.of_bound (hfm j).aestronglyMeasurable 1 (Eventually.of_forall fun ω => by
        rw [Real.norm_of_nonneg (hf0 j ω)]
        rcases Nat.eq_zero_or_pos (n j) with h0 | hpos
        · simp [f, h0]
        · have hpos' : (0 : ℝ) < n j := by exact_mod_cast hpos
          rw [div_le_one (by positivity)]
          exact pow_le_pow_left₀ (norm_nonneg _) (hSb _ ω) 2)
    have hfI : ∀ j, ∫ ω, f j ω ∂μ =
        (∫ ω, ‖∑ k ∈ Finset.range (n j), ee (h * (b : ℝ) ^ k * G ω)‖ ^ 2 ∂μ) / ((n j : ℝ) ^ 2) := by
      intro j; simp only [f, S]; rw [integral_div]
    have hlin : ∫⁻ ω, ∑' j, ENNReal.ofReal (f j ω) ∂μ ≠ ⊤ := by
      rw [lintegral_tsum fun j => (hfm j).ennreal_ofReal.aemeasurable]
      refine ne_top_of_le_ne_top (ENNReal.ofReal_ne_top
        (r := ∑' j : ℕ, ∫ ω, f j ω ∂μ)) ?_
      have hs : Summable fun j => ∫ ω, f j ω ∂μ := by simp_rw [hfI]; exact hsum h hh
      rw [ENNReal.ofReal_tsum_of_nonneg (fun j => integral_nonneg (hf0 j)) hs]
      refine ENNReal.tsum_le_tsum fun j => ?_
      rw [← ofReal_integral_eq_lintegral_ofReal (hfi j) (Eventually.of_forall (hf0 j))]
    have hae := ae_lt_top' (AEMeasurable.tsum fun j =>
      (hfm j).ennreal_ofReal.aemeasurable) hlin
    filter_upwards [hae] with ω hω
    have h1 : Tendsto (fun j => ENNReal.ofReal (f j ω)) atTop (𝓝 0) :=
      ENNReal.tendsto_atTop_zero_of_tsum_ne_top hω.ne
    have h2 : Tendsto (fun j => f j ω) atTop (𝓝 0) := by
      have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h1
      simpa [Function.comp_def, ENNReal.toReal_ofReal (hf0 _ ω)] using this
    have h3 : Tendsto (fun j : ℕ => ‖S (n j) ω‖ / (n j : ℝ)) atTop (𝓝 0) := by
      have := h2.sqrt
      rw [Real.sqrt_zero] at this
      refine this.congr fun j => ?_
      simp only [hfdef]
      rw [Real.sqrt_div' _ (by positivity), Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (by positivity)]
    exact tendsto_of_tendsto_sched (fun k => ee (h * (b : ℝ) ^ k * G ω)) (fun k => (norm_ee _).le) n hn
      hratio h3
  have hall : ∀ᵐ ω ∂μ, ∀ h : ℤ, h ≠ 0 → Tendsto
      (fun N : ℕ => (∑ k ∈ Finset.range N, ee (h * (b : ℝ) ^ k * G ω)) / (N : ℂ)) atTop (𝓝 0) := by
    rw [ae_all_iff]
    intro h
    by_cases hh : h = 0
    · exact Eventually.of_forall fun ω hne => absurd hh hne
    · filter_upwards [hone h hh] with ω hω _ using hω
  filter_upwards [hall] with ω hω
  rw [isNormal_iff_equidistributed_orbit b hb]
  refine equidistributed_of_weyl _ (fun k => ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩) ?_
  intro h hh
  have := hω h hh
  refine this.congr fun N => ?_
  rw [LevinSparse.fourierMean_orbit]


/-! ## Almost every coin sequence -/

/-- **Base `b` coprime to 3, a.e.**  Wiring (proved from `secondMoment_le_b`). -/
theorem ae_isNormal_of_coprime_three {b : ℕ} (hb : 2 ≤ b) (h3 : ¬ 3 ∣ b) :
    ∀ᵐ ω ∂coinMeasure, IsNormal b (cantorLiouvilleReal ω) := by
  refine ae_isNormal_of_secondMoment coinMeasure hb _ (measurable_pt isFree) sched
    sched_strictMono sched_ratio ?_
  intro h hh
  have hC : (0 : ℝ) < 16 * (b : ℝ) ^ 6 * |(h : ℝ)| := by
    have : (h : ℝ) ≠ 0 := by exact_mod_cast hh
    positivity
  have hl : 0 < Real.log (3 / 2) / 2 := by have := Real.log_pos (by norm_num : (1:ℝ) < 3 / 2); linarith
  refine (summable_sched_bound _ _ hC hl).of_nonneg_of_le
    (fun j => div_nonneg (integral_nonneg fun ω => by positivity) (by positivity))
    (fun j => ?_)
  have hN : (0 : ℝ) < sched j := by exact_mod_cast one_le_sched j
  rw [div_le_iff₀ (by positivity)]
  calc _ ≤ _ := secondMoment_le_b isFree hb h3 h hh (sched j) (one_le_sched j)
    _ = _ := by ring

/-! ## Bases divisible by 3 fail for every coin sequence -/

/-- Split of the point at a run: integer part over `3^A` plus a tail `< 3^{-T}`. -/
theorem run_split (ω : ℕ → Bool) (n : ℕ) : ∃ a : ℤ, ∃ t : ℝ, 0 ≤ t ∧
    t < 1 / 3 ^ ((n + 2) * runStart n) ∧
    cantorLiouvilleReal ω = a / 3 ^ runStart n + t := by
  set A := runStart n
  set T := (n + 2) * A
  set d := ptDigit isFree ω
  set f : ℕ → ℝ := fun i => (d i : ℝ) / 3 ^ (i + 1)
  have hf : Summable f := summable_ptDigit isFree ω
  have hd2 : ∀ i, (d i : ℝ) ≤ 2 := fun i => by
    have : d i ≤ 2 := by simp only [d, ptDigit]; split_ifs <;> norm_num
    exact_mod_cast this
  have hf0 : ∀ i, 0 ≤ f i := fun i => by positivity
  have hrun : ∀ i, A ≤ i → i < T → d i = 0 := by
    intro i h1 h2
    have := isForced_of_mem_run (k := n) h1 h2
    simp [d, ptDigit, isFree, this]
  set a : ℤ := ∑ i ∈ Finset.range A, ((d i * 3 ^ (A - 1 - i) : ℕ) : ℤ)
  have hx : cantorLiouvilleReal ω = ∑ i ∈ Finset.range T, f i + ∑' i, f (i + T) := by
    unfold cantorLiouvilleReal pt realOfDigits
    simp only [Nat.cast_ofNat]
    exact (hf.sum_add_tsum_nat_add T).symm
  have hpart : ∑ i ∈ Finset.range T, f i = a / 3 ^ A := by
    have hT : T = A + (T - A) := by have : A ≤ T := by simp only [T]; nlinarith
                                    omega
    rw [hT, Finset.sum_range_add]
    have hz : ∑ x ∈ Finset.range (T - A), f (A + x) = 0 :=
      Finset.sum_eq_zero fun x hx => by
        simp only [Finset.mem_range] at hx
        simp [f, hrun (A + x) (by omega) (by omega)]
    rw [hz, add_zero]
    simp only [a]; push_cast
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun i hi => ?_
    simp only [Finset.mem_range] at hi
    simp only [f]
    have : (3 : ℝ) ^ A = 3 ^ (A - 1 - i) * 3 ^ (i + 1) := by rw [← pow_add]; congr 1; omega
    rw [this]; field_simp
  set t := ∑' i, f (i + T)
  have hg : Summable fun i : ℕ => (2 : ℝ) / 3 ^ (i + T + 1) := by
    have := (summable_geometric_of_lt_one (r := (1 / 3 : ℝ)) (by norm_num) (by norm_num)).mul_left
      (2 / 3 ^ (T + 1))
    refine this.congr fun i => ?_
    rw [one_div_pow]; field_simp; ring
  have hgsum : ∑' i : ℕ, (2 : ℝ) / 3 ^ (i + T + 1) = 1 / 3 ^ T := by
    have : (fun i : ℕ => (2 : ℝ) / 3 ^ (i + T + 1)) = fun i => 2 / 3 ^ (T + 1) * (1 / 3) ^ i := by
      funext i; rw [one_div_pow, show i + T + 1 = i + (T + 1) by ring, pow_add, pow_succ]; field_simp
    rw [this, tsum_mul_left, tsum_geometric_of_lt_one (by norm_num) (by norm_num), pow_succ]
    field_simp; norm_num
  have hnext : T ≤ runStart (n + 1) := by
    simp only [T, A, runStart_succ_eq]; nlinarith
  have hzero : d (runStart (n + 1)) = 0 := by
    simp [d, ptDigit, isFree_runStart]
  have htlt : t < 1 / 3 ^ T := by
    rw [← hgsum]
    refine Summable.tsum_lt_tsum_of_nonneg (i := runStart (n + 1) - T) (fun i => hf0 _)
      (fun i => ?_) ?_ hg
    · simp only [f]; gcongr; exact hd2 _
    · simp only [f, Nat.sub_add_cancel hnext, hzero, Nat.cast_zero, zero_div]; positivity
  exact ⟨a, t, tsum_nonneg fun i => hf0 _, htlt, by rw [hx, hpart]⟩

/-- **Near-integers on a run.**  Confidence 90%.

English proof.  Split `x = cantorLiouvilleReal ω = P + θ` at place `a = runStart k`:
`P = Σ_{i<a} dᵢ 3^{−(i+1)} ∈ 3^{−a}ℤ` and, the digits on `[a, (k+2)a)` being forced `0`,
`θ = Σ_{i ≥ (k+2)a} dᵢ 3^{−(i+1)}`, with `0 ≤ θ < 3^{−(k+2)a}` strictly (digits `≤ 2`, and the
next run forces a `0`, so the geometric bound is not attained).  Since `3 ∣ b` and `j ≥ a`,
`3^a ∣ bʲ`, so `bʲP ∈ ℤ`; and `bʲθ < bʲ 3^{−(k+2)a} ≤ b⁻¹` by `hj2`.  Hence
`fract(bʲx) = bʲθ < 1/b`. -/
theorem fract_lt_of_mem_run (ω : ℕ → Bool) {b : ℕ} (hb : 2 ≤ b) (h3 : 3 ∣ b) {k j : ℕ}
    (hj1 : runStart k ≤ j) (hj2 : b ^ (j + 1) ≤ 3 ^ ((k + 2) * runStart k)) :
    Int.fract (cantorLiouvilleReal ω * (b : ℝ) ^ j) < 1 / b := by
  obtain ⟨a, t, ht0, ht1, hx⟩ := run_split ω k
  set A := runStart k
  set T := (k + 2) * A
  obtain ⟨q, hq⟩ : 3 ^ A ∣ b ^ j := (pow_dvd_pow 3 hj1).trans (pow_dvd_pow_of_dvd h3 j)
  have hbR : (0 : ℝ) < b := by exact_mod_cast (by omega : 0 < b)
  have hbj : (b : ℝ) ^ j = 3 ^ A * q := by exact_mod_cast hq
  have heq : cantorLiouvilleReal ω * (b : ℝ) ^ j = ((a * q : ℤ) : ℝ) + t * (b : ℝ) ^ j := by
    rw [hx, add_mul, hbj]; push_cast; field_simp
  have hT : (b : ℝ) ^ (j + 1) ≤ 3 ^ T := by exact_mod_cast hj2
  have hlt : t * (b : ℝ) ^ j < 1 / b := by
    have h3T : (0 : ℝ) < 3 ^ T := by positivity
    calc t * (b : ℝ) ^ j ≤ t * (3 ^ T / b) := by
          gcongr; rw [le_div_iff₀ hbR, ← pow_succ]; exact hT
      _ < 1 / 3 ^ T * (3 ^ T / b) := by gcongr
      _ = 1 / b := by field_simp
  have h0 : 0 ≤ t * (b : ℝ) ^ j := by positivity
  rw [heq, Int.fract_intCast_add, Int.fract_eq_self.2 ⟨h0, hlt.trans_le ?_⟩]
  · exact hlt
  · rw [div_le_one hbR]; exact_mod_cast (by omega : 1 ≤ b)

/-- **Every base divisible by 3 fails, for every `ω`.**  Confidence 85%.

English proof.  Suppose `IsNormal b x`; by Wall (`isNormal_iff_equidistributed_orbit`) the
visit frequency of `orbit b x` to `[0, 1/b)` tends to `1/b ≤ 1/3`.  Let `a = runStart k`,
`E = (k+2)a` and `N_k = ⌊E / log₃ b⌋` (so `b^{N_k} ≤ 3^E`).  By `fract_lt_of_mem_run`, every
`j ∈ [a, N_k − 1)` visits `[0, 1/b)`, so `visitCount ≥ N_k − 1 − a`.  Since
`b ≤ 3^{log₃ b}` and `log₃ b ≤ b`, `N_k ≥ E / b − 1 = (k+2)a/b − 1`, and
`(N_k − 1 − a)/N_k ≥ 1 − (2 + a)/N_k → 1 − b/(k+2) → 1` (`a → ∞`, `runStart` grows).  So the
frequency along `N_k` tends to `1 ≠ 1/b`. -/
theorem not_isNormal_of_three_dvd (ω : ℕ → Bool) {b : ℕ} (hb : 2 ≤ b) (h3 : 3 ∣ b) :
    ¬ IsNormal b (cantorLiouvilleReal ω) := by
  intro hn
  rw [isNormal_iff_equidistributed_orbit b hb] at hn
  have hbR : (2 : ℝ) ≤ b := by exact_mod_cast hb
  have ht := hn 0 (1 / b) le_rfl (by positivity) (by rw [div_le_one (by linarith)]; linarith)
  rw [sub_zero] at ht
  have hlt : (1 : ℝ) / b < 3 / 4 := by rw [div_lt_iff₀ (by linarith)]; linarith
  obtain ⟨N0, hN0⟩ := eventually_atTop.1 (ht.eventually (gt_mem_nhds hlt))
  set k := N0 + 8 * b
  set A := runStart k
  set T := (k + 2) * A
  set n := Nat.log b (3 ^ T)
  have hkA := lt_runStart k
  have hlog : 3 ^ T < b ^ (n + 1) := Nat.lt_pow_succ_log_self (by omega) _
  have hb3 : b ^ (n + 1) < 3 ^ (b * (n + 1)) := by
    rw [pow_mul]; exact Nat.pow_lt_pow_left (Nat.lt_pow_self (by norm_num)) (by omega)
  have hT : T < b * (n + 1) := (Nat.pow_lt_pow_iff_right (by norm_num)).1 (hlog.trans hb3)
  have hTA : 8 * b * A ≤ T := Nat.mul_le_mul_right A (by omega)
  have hn8 : 8 * A ≤ n := by
    by_contra hc
    have : b * (n + 1) ≤ b * (8 * A) := Nat.mul_le_mul_left _ (by omega)
    nlinarith
  have hpow : b ^ n ≤ 3 ^ T := Nat.pow_log_le_self b (by positivity)
  have hvis : n - A ≤ visitCount (orbit b (cantorLiouvilleReal ω)) 0 (1 / b) n := by
    unfold visitCount
    have : Finset.Ico A n ⊆ (Finset.range n).filter
        (fun j => orbit b (cantorLiouvilleReal ω) j ∈ Set.Ico 0 (1 / (b : ℝ))) := by
      intro j hj
      simp only [Finset.mem_Ico] at hj
      simp only [Finset.mem_filter, Finset.mem_range, Set.mem_Ico, orbit]
      refine ⟨hj.2, Int.fract_nonneg _, fract_lt_of_mem_run ω hb h3 hj.1 ?_⟩
      exact (Nat.pow_le_pow_right (by omega) (by omega)).trans hpow
    simpa using Finset.card_le_card this
  have hnpos : (0 : ℝ) < n := by have : 0 < n := by omega
                                 exact_mod_cast this
  have := hN0 n (by omega)
  rw [div_lt_iff₀ hnpos] at this
  have h1 : ((n - A : ℕ) : ℝ) ≤ visitCount (orbit b (cantorLiouvilleReal ω)) 0 (1 / b) n := by
    exact_mod_cast hvis
  have h2 : ((n - A : ℕ) : ℝ) = n - A := by push_cast [show A ≤ n by omega]; ring
  have h3' : (8 * A : ℝ) ≤ n := by exact_mod_cast hn8
  linarith

/-- **The separating base.**  Cassels (`Literature.Cassels1959`) makes `μ_K`-a.e. point normal
to base 6; no Cantor–Liouville point is. -/
theorem not_isNormal_six (ω : ℕ → Bool) : ¬ IsNormal 6 (cantorLiouvilleReal ω) :=
  not_isNormal_of_three_dvd ω (by norm_num) (by norm_num)

/-- **Normality profile, a.e. form.**  Wiring (proved). -/
theorem ae_normalProfile :
    ∀ᵐ ω ∂coinMeasure, ∀ b : ℕ, 2 ≤ b → (IsNormal b (cantorLiouvilleReal ω) ↔ ¬ 3 ∣ b) := by
  have hall : ∀ᵐ ω ∂coinMeasure, ∀ b : ℕ, 2 ≤ b → ¬ 3 ∣ b → IsNormal b (cantorLiouvilleReal ω) := by
    rw [ae_all_iff]
    intro b
    by_cases hb : 2 ≤ b
    · by_cases h3 : 3 ∣ b
      · exact Eventually.of_forall fun ω _ h => absurd h3 h
      · filter_upwards [ae_isNormal_of_coprime_three hb h3] with ω hω _ _ using hω
    · exact Eventually.of_forall fun ω h => absurd h hb
  filter_upwards [hall] with ω hω b hb
  exact ⟨fun hn h3 => not_isNormal_of_three_dvd ω hb h3 hn, hω b hb⟩

/-- **Normality profile, existence.**  Wiring (proved). -/
theorem exists_liouville_mem_cantorSet_normalProfile :
    ∃ x : ℝ, x ∈ cantorSet ∧ Liouville x ∧ ∀ b : ℕ, 2 ≤ b → (IsNormal b x ↔ ¬ 3 ∣ b) := by
  obtain ⟨ω, hn, hf⟩ := (ae_normalProfile.and ae_frequently_free).exists
  exact ⟨_, pt_mem_cantorSet _ _, liouville_cantorLiouvilleReal ω hf, hn⟩

/-! ## Computable form -/

section Computable

open Derandomize SchedDerandomize

/-- **Family version of `SchedDerandomize.exists_computable_normal_sched`.**  Confidence 70%.

English proof.  The tests of `exists_computable_normal_sched` are already base-generic
(`fails Ψ b …`, `sprimrec_fails`, `level_bound_w` take `b`); only the assembly fixes `b = 2`.
Run the base-`b` level tests (for each `b` with `S b`) from stage `j ≥ g b` on, with
`g b = j₀ + ⌈4 B_b⌉ + 2 + b`, `B_b = 74016 √(κ b) Zc + 1` replaced by the primrec upper bound
`74016 (κ b + 1) (Zc + 1)` (`Zc` is a fixed real; any fixed rational bound for it works).  The
base-`b` test at stage `j` has mass `≤ B_b/(j+1)²` (`level_bound_w` and `hev`, as in the
base-2 assembly), so the total mass over `b` and `j ≥ g b` is `≤ Σ_b B_b/g b ≤ Σ_b 2^{-b}·…`
after choosing `g b ≥ 4^{b+2} B_b`; together with `bad'` it is `< 1`, so `exists_primrec_avoid`
gives a computable avoider.  Avoiding base `b` from stage `g b` on gives `IsNormal b` exactly as
in the base-2 proof (`good_of_pass`, schedule ratio `→ 1`). -/
theorem exists_computable_normal_sched_family (Ψ : ℕ → ℕ → List Bool → ℕ)
    (hΨp : Primrec fun x : ℕ × ℕ × List Bool => Ψ x.1 x.2.1 x.2.2) (A : List Bool → ℝ)
    (hΨ : ∀ b m p, Ψ b m p = ⌊A p * (b : ℝ) ^ m⌋₊) (hA0 : ∀ p, 0 ≤ A p)
    (G : (ℕ → Bool) → ℝ) (hGm : Measurable G)
    (hAG : ∀ ω D, A (pre ω D) ≤ G ω ∧ G ω ≤ A (pre ω D) + (1 / 2 : ℝ) ^ D)
    (S : ℕ → Prop) [DecidablePred S] (hS : PrimrecPred S) (κ : ℕ → ℕ) (hκ : Primrec κ)
    (W : ℕ → ℝ) (hW0 : ∀ N, 0 ≤ W N) (hWa : Antitone W)
    (hsm : ∀ b, 2 ≤ b → S b → ∀ h : ℤ, h ≠ 0 → ∀ N : ℕ, 1 ≤ N →
      ∫ ω, ‖∑ k ∈ Finset.range N, ee (h * (b : ℝ) ^ k * G ω)‖ ^ 2 ∂coins ≤
        κ b * |(h : ℝ)| * N ^ 2 * W N)
    (Ns nr : ℕ → ℕ) (hNs : Primrec Ns) (hnr : Primrec nr) (hNtop : Tendsto Ns atTop atTop)
    (hrat : ∀ a : ℝ, 1 < a → ∀ᶠ j in atTop, (Ns (j + 1) : ℝ) ≤ a * Ns j)
    (hnrtop : Tendsto nr atTop atTop)
    (hev : ∀ᶠ j in atTop, 8 ≤ nr j ∧ nr j ≤ Ns j ∧
      (nr j : ℝ) ^ 6 * W (Ns j) ≤ 1 / ((j : ℝ) + 1) ^ 4)
    (bad' : ℕ → List Bool → Bool) (hbad' : Primrec₂ bad') (d' : ℕ → ℕ) (hd' : Primrec d')
    (hmass : ∀ j, coins.real {ω | bad' j (pre ω (d' j)) = true} ≤ 1 / ((j : ℝ) + 1) ^ 2) :
    ∃ e : ℕ → Bool, Computable e ∧ (∀ b, 2 ≤ b → S b → IsNormal b (G e)) ∧
      ∃ j₁, ∀ j, j₁ ≤ j → bad' j (pre e (d' j)) = false :=
  SchedFamily.exists_computable_normal_sched_family' Ψ hΨp A hΨ hA0 G hGm hAG S hS κ hκ W hW0 hWa
    hsm Ns nr hNs hnr hNtop hrat hnrtop hev bad' hbad' d' hd' hmass

/-- The base-`b` second moment in `clW` form (wiring from `secondMoment_le_b`). -/
theorem cl_secondMoment_b {b : ℕ} (hb : 2 ≤ b) (h3 : ¬ 3 ∣ b) (h : ℤ) (hh : h ≠ 0) (N : ℕ)
    (hN : 1 ≤ N) :
    ∫ ω, ‖∑ k ∈ Finset.range N, ee (h * (b : ℝ) ^ k * cantorLiouvilleReal ω)‖ ^ 2 ∂coins ≤
      ((16 * b ^ 6 : ℕ) : ℝ) * |(h : ℝ)| * N ^ 2 * clW N := by
  have hW : clW N = Real.exp (-(Real.log (3 / 2) / 2) * freeCount isFree (Nat.log 3 N / 2)) +
      (N : ℝ) ^ (-(1 / 2 : ℝ)) := by
    rw [clW, max_eq_left hN]
  rw [hW]
  refine (secondMoment_le_b isFree hb h3 h hh N hN).trans (le_of_eq ?_)
  push_cast; ring

theorem primrec_notThreeDvd : PrimrecPred fun b : ℕ => ¬ 3 ∣ b := by
  refine PrimrecPred.not ?_
  have : PrimrecPred fun b : ℕ => b % 3 = 0 :=
    Primrec.eq.comp (Primrec.nat_mod.comp Primrec.id (Primrec.const 3)) (Primrec.const 0)
  exact this.of_eq fun b => (Nat.dvd_iff_mod_eq_zero).symm

theorem primrec_kappa : Primrec fun b : ℕ => 16 * b ^ 6 :=
  Primrec.nat_mul.comp (Primrec.const 16)
    (ComputableNormal.primrec_pow.comp Primrec.id (Primrec.const 6))

end Computable

/-- **The normality profile, computable.**  Wiring (proved from the leaves): a computable
`e` such that `x = cantorLiouvilleReal e` lies in the middle-third Cantor set, is Liouville, and
is normal to exactly the bases not divisible by 3. -/
theorem exists_computable_liouville_mem_cantorSet_normalProfile :
    ∃ e : ℕ → Bool, Computable e ∧ cantorLiouvilleReal e ∈ cantorSet ∧
      Liouville (cantorLiouvilleReal e) ∧
      ∀ b : ℕ, 2 ≤ b → (IsNormal b (cantorLiouvilleReal e) ↔ ¬ 3 ∣ b) := by
  obtain ⟨e, hce, hn, j₁, hj⟩ := exists_computable_normal_sched_family clΨ primrec_clΨ clA
    clΨ_eq clA_nonneg cantorLiouvilleReal measurable_cantorLiouvilleReal clA_bounds
    (fun b => ¬ 3 ∣ b) primrec_notThreeDvd (fun b => 16 * b ^ 6) primrec_kappa
    clW clW_nonneg clW_antitone (fun b hb h3 h hh N hN => cl_secondMoment_b hb h3 h hh N hN)
    clNs clNr primrec_clNs primrec_clNr tendsto_clNs clNs_ratio tendsto_clNr cl_ev clBad
    primrec_clBad clD primrec_clD clBad_mass
  refine ⟨e, hce, pt_mem_cantorSet _ _,
    liouville_cantorLiouvilleReal e (frequently_free_of_clBad e j₁ hj), fun b hb => ?_⟩
  exact ⟨fun hn' h3 => not_isNormal_of_three_dvd e hb h3 hn', hn b hb⟩

end NormalNumbers.CantorLiouvilleAll
