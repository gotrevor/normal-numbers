/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.PadicTwoLogs
import NormalNumbers.SparseIdentity
import NormalNumbers.CantorRepetition

/-!
# Assembly: `SparseIdentity.Literature.PadicTwoLogs` from Laurent's zero lemma

`padicTwoLogs_of_zeroLemma : LaurentZeroLemma → SparseIdentity.Literature.PadicTwoLogs`.
After this, the cited Bugeaud–Laurent bound is no longer an input: the 3-adic chain rests on the
(rational, two-variable) zero lemma `PadicTwoLogs.Literature.LaurentZeroLemma` only.
-/

namespace PadicTwoLogs

theorem le_log_of_three_pow_dvd {g : ℕ} {x : ℤ} (hx : x ≠ 0) (h : (3 : ℤ) ^ g ∣ x) :
    g ≤ Nat.log 2 x.natAbs := by
  refine Nat.le_log_of_pow_le (by norm_num) ?_
  have h1 : 3 ^ g ∣ x.natAbs := by
    have := Int.natAbs_dvd_natAbs.2 h; rwa [Int.natAbs_pow] at this
  exact (Nat.pow_le_pow_left (by norm_num) g).trans (Nat.le_of_dvd (by omega) h1)

theorem natLog_le_real (n : ℕ) : ((Nat.log 2 n : ℕ) : ℝ) ≤ 2 * Real.log n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn; · simp
  have h1 : (2 : ℝ) ^ (Nat.log 2 n) ≤ n := by exact_mod_cast Nat.pow_log_le_self 2 (by omega)
  have h2 : ((Nat.log 2 n : ℕ) : ℝ) * Real.log 2 ≤ Real.log n := by
    rw [← Real.log_pow]; exact Real.log_le_log (by positivity) h1
  have h3 : (1 / 2 : ℝ) < Real.log 2 := by have := Real.log_two_gt_d9; linarith
  have h4 : (0 : ℝ) ≤ (Nat.log 2 n : ℕ) := by positivity
  nlinarith

/-- The explicit reduced bound (independent + dependent cases). -/
def coreF (T M q : ℕ) : ℕ :=
  2 ^ 24 * (Nat.log 2 T + 1) * (Nat.log 2 M + 1) * (Nat.log 2 q + 1 + (Nat.log 2 T + 1) + 20) ^ 2 +
    (Nat.log 3 T + Nat.log 3 (2 * (Nat.log 2 T + 1) * q + 4 * (Nat.log 2 M + 1)))

theorem natAbs_le_of_abs_le {a : ℤ} {M : ℕ} (h : |a| ≤ M) : a.natAbs ≤ M := by
  rw [Int.abs_eq_natAbs] at h; exact_mod_cast h

/-- Both cases of the reduced bound, unified. -/
theorem core_bound (hZ : Literature.LaurentZeroLemma) (T : ℕ) (hT : 2 ≤ T)
    (hT1 : (3 : ℤ) ∣ (T : ℤ) - 1) (a b : ℤ) (ha0 : a ≠ 0) (ha3 : ¬ (3 : ℤ) ∣ a) (hb0 : b ≠ 0)
    (q g M : ℕ) (hM1 : 1 ≤ M) (haM : |a| ≤ M) (hbM : |b| ≤ M)
    (hne : (T : ℤ) ^ q * a ≠ b) (hab : (3 : ℤ) ^ g ∣ (T : ℤ) ^ q * a - b) :
    g ≤ coreF T M q := by
  unfold coreF
  by_cases hind : ∀ u v : ℤ, ((T : ℤ) : ℚ) ^ u * ((b : ℚ) / a) ^ v = 1 → u = 0 ∧ v = 0
  · have := g_le_indep hZ T a b q g hT1 hT ha3 ha0 hb0 M hM1 haM hbM hind hne hab
    omega
  · push Not at hind
    obtain ⟨u, v, hrel, huv⟩ := hind
    have hrel' : (T : ℚ) ^ u * ((b : ℚ) / a) ^ v = 1 := by simpa using hrel
    obtain ⟨e, f, he1, heT, hf, hrel2⟩ :=
      small_relation T hT a b ha0 hb0 u v (fun h => huv h.1 h.2) hrel'
    have h := g_le_dep T hT hT1 a b ha0 ha3 q g e f he1 hrel2 hne hab
    have h1 : Nat.log 2 a.natAbs ≤ Nat.log 2 M := Nat.log_mono_right (natAbs_le_of_abs_le haM)
    have h2 : Nat.log 2 b.natAbs ≤ Nat.log 2 M := Nat.log_mono_right (natAbs_le_of_abs_le hbM)
    have h3 : 2 * e * q + 2 * f.natAbs ≤ 2 * (Nat.log 2 T + 1) * q + 4 * (Nat.log 2 M + 1) := by
      have : e * q ≤ (Nat.log 2 T + 1) * q := Nat.mul_le_mul_right _ (by omega)
      have : f.natAbs ≤ Nat.log 2 a.natAbs + Nat.log 2 b.natAbs := by
        rw [Int.abs_eq_natAbs] at hf; exact_mod_cast hf
      nlinarith
    have := Nat.log_mono_right (b := 3) h3
    omega

theorem strip_three (a : ℤ) (ha : a ≠ 0) :
    ∃ k : ℕ, ∃ a₀ : ℤ, a = 3 ^ k * a₀ ∧ ¬ (3 : ℤ) ∣ a₀ ∧ k ≤ Nat.log 2 a.natAbs := by
  obtain ⟨k, m, hm, hk⟩ := Nat.exists_eq_pow_mul_and_not_dvd (Int.natAbs_ne_zero.2 ha) 3 (by norm_num)
  have hd : (3 : ℤ) ^ k ∣ a := by
    rw [← Int.natAbs_dvd_natAbs, hk, Int.natAbs_pow]; exact Dvd.intro _ rfl
  obtain ⟨a₀, rfl⟩ := hd
  refine ⟨k, a₀, rfl, ?_, ?_⟩
  · intro h
    have h1 : (a₀.natAbs) = m := by
      rw [Int.natAbs_mul, Int.natAbs_pow] at hk
      exact Nat.eq_of_mul_eq_mul_left (by positivity) hk
    apply hm; rw [← h1]; exact Int.natAbs_dvd_natAbs.2 h
  · refine Nat.le_log_of_pow_le (by norm_num) ?_
    rw [hk]
    have : 1 ≤ m := Nat.one_le_iff_ne_zero.2 (by rintro rfl; simp at hm)
    calc 2 ^ k ≤ 3 ^ k := Nat.pow_le_pow_left (by norm_num) _
      _ ≤ 3 ^ k * m := Nat.le_mul_of_pos_right _ this

theorem mid_bound (hZ : Literature.LaurentZeroLemma) (t : ℕ) (ht : 2 ≤ t) (ht3 : ¬ (3 : ℤ) ∣ t)
    (δ g : ℕ) (a b : ℤ) (ha0 : a ≠ 0) (hb0 : b ≠ 0)
    (hne : (t : ℤ) ^ δ * a ≠ b) (hab : (3 : ℤ) ^ g ∣ (t : ℤ) ^ δ * a - b) :
    g ≤ Nat.log 2 (max |a| |b|).natAbs + coreF (t ^ 2) (t * (max |a| |b|).natAbs) (δ / 2) := by
  set N := (max |a| |b|).natAbs with hN
  have haN : |a| ≤ N := by rw [hN, Int.natCast_natAbs, abs_of_nonneg (le_max_of_le_left (abs_nonneg a))]; exact le_max_left _ _
  have hbN : |b| ≤ N := by rw [hN, Int.natCast_natAbs, abs_of_nonneg (le_max_of_le_left (abs_nonneg a))]; exact le_max_right _ _
  obtain ⟨k, a₀, rfl, ha₀3, hk⟩ := strip_three a ha0
  have hkN : k ≤ Nat.log 2 N := hk.trans (Nat.log_mono_right (by
    rw [Int.abs_eq_natAbs] at haN; exact_mod_cast haN))
  by_cases hgk : g ≤ k
  · omega
  push Not at hgk
  have hkb : (3 : ℤ) ^ k ∣ b := by
    have h1 : (3 : ℤ) ^ k ∣ (t : ℤ) ^ δ * (3 ^ k * a₀) - b :=
      (pow_dvd_pow 3 hgk.le).trans hab
    exact (dvd_sub_right ((dvd_mul_right _ _).mul_left _)).1 h1
  obtain ⟨b₀, rfl⟩ := hkb
  have h3k : (3 : ℤ) ^ k ≠ 0 := by positivity
  have hδ : δ = 2 * (δ / 2) + δ % 2 := (Nat.div_add_mod δ 2).symm
  have hid : (t : ℤ) ^ δ * (3 ^ k * a₀) - 3 ^ k * b₀ =
      3 ^ k * ((((t ^ 2 : ℕ) : ℤ)) ^ (δ / 2) * ((t : ℤ) ^ (δ % 2) * a₀) - b₀) := by
    conv_lhs => rw [hδ]
    push_cast; rw [pow_add, pow_mul]; ring
  have hab' : (3 : ℤ) ^ (g - k) ∣ (((t ^ 2 : ℕ) : ℤ)) ^ (δ / 2) * ((t : ℤ) ^ (δ % 2) * a₀) - b₀ := by
    rw [hid, show g = k + (g - k) by omega, pow_add] at hab
    exact (mul_dvd_mul_iff_left h3k).1 hab
  have hne' : (((t ^ 2 : ℕ) : ℤ)) ^ (δ / 2) * ((t : ℤ) ^ (δ % 2) * a₀) ≠ b₀ := by
    intro h; apply hne
    have := congrArg (fun x => 3 ^ k * x) (sub_eq_zero.2 h)
    simp only [mul_zero] at this
    rw [← hid] at this; exact sub_eq_zero.1 this
  have ht0 : ¬ (3 : ℤ) ∣ (t : ℤ) ^ (δ % 2) * a₀ := by
    intro h
    rcases Int.prime_three.dvd_or_dvd h with h | h
    · exact ht3 (Int.prime_three.dvd_of_dvd_pow h)
    · exact ha₀3 h
  have hT1 : (3 : ℤ) ∣ (((t ^ 2 : ℕ) : ℤ)) - 1 := by
    have : (((t ^ 2 : ℕ) : ℤ)) - 1 = ((t : ℤ) - 1) * ((t : ℤ) + 1) := by push_cast; ring
    rw [this]
    have : (3 : ℤ) ∣ (t : ℤ) - 1 ∨ (3 : ℤ) ∣ (t : ℤ) + 1 := by omega
    rcases this with h | h
    · exact h.mul_right _
    · exact h.mul_left _
  have ha₀ : a₀ ≠ 0 := by rintro rfl; simp at ha0
  have hb₀ : b₀ ≠ 0 := by rintro rfl; simp at hb0
  have hN1 : 1 ≤ N := by
    have : (1 : ℤ) ≤ |3 ^ k * a₀| := Int.one_le_abs (by positivity)
    have : (1 : ℤ) ≤ N := this.trans haN
    exact_mod_cast this
  have hta : |(t : ℤ) ^ (δ % 2) * a₀| ≤ ((t * N : ℕ) : ℤ) := by
    have h1 : |a₀| ≤ |3 ^ k * a₀| := by
      rw [abs_mul]; exact le_mul_of_one_le_left (abs_nonneg _) (by
        rw [abs_of_pos (by positivity)]; exact one_le_pow₀ (by norm_num))
    have h2 : |(t : ℤ) ^ (δ % 2)| ≤ t := by
      rw [abs_of_nonneg (by positivity)]
      rcases Nat.mod_two_eq_zero_or_one δ with h | h <;> rw [h] <;> (simp; try omega)
    rw [abs_mul]; push_cast
    exact mul_le_mul h2 (h1.trans haN) (abs_nonneg _) (by positivity)
  have htb : |b₀| ≤ ((t * N : ℕ) : ℤ) := by
    have h1 : |b₀| ≤ |3 ^ k * b₀| := by
      rw [abs_mul]; exact le_mul_of_one_le_left (abs_nonneg _) (by
        rw [abs_of_pos (by positivity)]; exact one_le_pow₀ (by norm_num))
    have : (N : ℤ) ≤ ((t * N : ℕ) : ℤ) := by push_cast; nlinarith
    exact (h1.trans hbN).trans this
  have hc := core_bound hZ (t ^ 2) (by nlinarith) hT1 _ _ (mul_ne_zero (by positivity) ha₀) ht0 hb₀
    (δ / 2) (g - k) (t * N) (by nlinarith) hta htb hne' hab'
  omega

theorem log2_mul_le (x y : ℕ) : Nat.log 2 (x * y) ≤ Nat.log 2 x + Nat.log 2 y + 1 := by
  rcases Nat.eq_zero_or_pos x with rfl | hx; · simp
  rcases Nat.eq_zero_or_pos y with rfl | hy; · simp
  have h1 := Nat.lt_pow_succ_log_self (b := 2) (by norm_num) x
  have h2 := Nat.lt_pow_succ_log_self (b := 2) (by norm_num) y
  have : x * y < 2 ^ (Nat.log 2 x + Nat.log 2 y + 2) := by
    calc x * y < 2 ^ (Nat.log 2 x).succ * 2 ^ (Nat.log 2 y).succ := Nat.mul_lt_mul'' h1 h2
      _ = _ := by rw [← pow_add]; congr 1; simp only [Nat.succ_eq_add_one]; ring
  have := Nat.log_lt_of_lt_pow (by positivity) this
  omega

theorem coreF_le (t : ℕ) : ∃ K : ℕ, ∀ N δ : ℕ, 1 ≤ N →
    Nat.log 2 N + coreF (t ^ 2) (t * N) (δ / 2) ≤
      K * (Nat.log 2 (δ + 1) + 1) ^ 2 * (Nat.log 2 N + 1) := by
  set τ := Nat.log 2 (t ^ 2) + 1
  set c := Nat.log 2 t + 1
  set Kb := 2 ^ 24 * τ * (c + 1) * (τ + 21) ^ 2
  set Kc := Nat.log 3 (t ^ 2) + Nat.log 2 (2 * τ + 4) + 1 + c
  refine ⟨3 + Kb + Kc, fun N δ hN => ?_⟩
  set L := Nat.log 2 (δ + 1) + 1
  set H := Nat.log 2 N + 1
  set q := δ / 2
  set A := Nat.log 2 (t * N) + 1
  set P := L ^ 2 * H
  have hL : 1 ≤ L := by omega
  have hH : 1 ≤ H := by omega
  have hHP : H ≤ P := Nat.le_mul_of_pos_left _ (by positivity)
  have hLP : L ≤ P := by
    calc L ≤ L ^ 2 := by nlinarith
      _ ≤ P := Nat.le_mul_of_pos_right _ hH
  have hcA : A ≤ c + H := by have := log2_mul_le t N; omega
  have hA1 : A ≤ (c + 1) * H := by nlinarith
  have hq : Nat.log 2 q + 1 ≤ L := by
    have := Nat.log_mono_right (b := 2) (show q ≤ δ + 1 by omega); omega
  have hbig : 2 ^ 24 * τ * A * (Nat.log 2 q + 1 + τ + 20) ^ 2 ≤ Kb * P := by
    have h1 : Nat.log 2 q + 1 + τ + 20 ≤ (τ + 21) * L := by nlinarith
    calc 2 ^ 24 * τ * A * (Nat.log 2 q + 1 + τ + 20) ^ 2
        ≤ 2 ^ 24 * τ * ((c + 1) * H) * ((τ + 21) * L) ^ 2 := by gcongr
      _ = Kb * P := by ring
  have hX : Nat.log 3 (2 * τ * q + 4 * A) ≤ Nat.log 2 (2 * τ + 4) + 1 + L + c + H := by
    have h0 : Nat.log 3 (2 * τ * q + 4 * A) ≤ Nat.log 2 (2 * τ * q + 4 * A) :=
      Nat.log_anti_left (by norm_num) (by norm_num)
    have hA0 : 1 ≤ A := by omega
    have h1 : 2 * τ * q + 4 * A ≤ (2 * τ + 4) * ((q + 1) * A) := by
      have : 2 * τ * q ≤ 2 * τ * q * A := Nat.le_mul_of_pos_right _ hA0
      nlinarith
    have h2 := Nat.log_mono_right (b := 2) h1
    have h3 := log2_mul_le (2 * τ + 4) ((q + 1) * A)
    have h4 := log2_mul_le (q + 1) A
    have h5 : Nat.log 2 A ≤ A := (Nat.log_le_self 2 A)
    have h6 := Nat.log_mono_right (b := 2) (show q + 1 ≤ δ + 1 by omega)
    omega
  have hKc : Kc ≤ Kc * P := Nat.le_mul_of_pos_right _ (by positivity)
  have hunf : coreF (t ^ 2) (t * N) q = 2 ^ 24 * τ * A * (Nat.log 2 q + 1 + τ + 20) ^ 2 +
      (Nat.log 3 (t ^ 2) + Nat.log 3 (2 * τ * q + 4 * A)) := by
    rfl
  calc Nat.log 2 N + coreF (t ^ 2) (t * N) q ≤ P + Kb * P + Kc * P + P + P := by omega
    _ = (3 + Kb + Kc) * L ^ 2 * H := by ring

/-- **`Literature.PadicTwoLogs` from Laurent's zero lemma (proved modulo `LaurentZeroLemma`).**
`t ↦ t²` (so `3 ∣ t² − 1`), fold `t^{δ mod 2}` into `a`, strip the 3-part of `a` (`strip_three`),
then the independent (`g_le_indep`) / dependent (`g_le_dep`) cases via `core_bound`, `mid_bound`,
`coreF_le`; binary lengths become real logarithms by `natLog_le_real`. -/
theorem padicTwoLogs_of_zeroLemma (hZ : Literature.LaurentZeroLemma) :
    NormalNumbers.SparseIdentity.Literature.PadicTwoLogs := by
  intro t ht ht3
  have ht3' : ¬ (3 : ℤ) ∣ (t : ℤ) := by exact_mod_cast ht3
  obtain ⟨K, hK⟩ := coreF_le t
  refine ⟨8 * (K + 1), by positivity, fun δ g a b hne hab => ?_⟩
  set N := (max |a| |b|).natAbs with hN
  have haN : a.natAbs ≤ N := by
    have : |a| ≤ N := by
      rw [hN, Int.natCast_natAbs, abs_of_nonneg (le_max_of_le_left (abs_nonneg a))]
      exact le_max_left _ _
    rw [Int.abs_eq_natAbs] at this; exact_mod_cast this
  have hbN : b.natAbs ≤ N := by
    have : |b| ≤ N := by
      rw [hN, Int.natCast_natAbs, abs_of_nonneg (le_max_of_le_left (abs_nonneg a))]
      exact le_max_right _ _
    rw [Int.abs_eq_natAbs] at this; exact_mod_cast this
  set L := Nat.log 2 (δ + 1) + 1
  set H := Nat.log 2 N + 1
  have hP : 1 ≤ L ^ 2 * H := Nat.one_le_iff_ne_zero.2 (by positivity)
  have hHP : H ≤ L ^ 2 * H := Nat.le_mul_of_pos_left _ (by positivity)
  -- the natural-number bound
  have hnat : g ≤ (K + 1) * L ^ 2 * H := by
    have hsmall : ∀ x : ℤ, x ≠ 0 → x.natAbs ≤ N → (3 : ℤ) ^ g ∣ x → g ≤ (K + 1) * L ^ 2 * H := by
      intro x hx hxN h
      have h1 := le_log_of_three_pow_dvd hx h
      have h2 := Nat.log_mono_right (b := 2) hxN
      calc g ≤ H := by omega
        _ ≤ L ^ 2 * H := hHP
        _ ≤ (K + 1) * (L ^ 2 * H) := Nat.le_mul_of_pos_left _ (by omega)
        _ = _ := by ring
    by_cases ha0 : a = 0
    · subst ha0
      have hb0 : b ≠ 0 := by intro h; apply hne; simp [h]
      exact hsmall b hb0 hbN (by simpa using hab)
    by_cases hb0 : b = 0
    · subst hb0
      have h1 : (3 : ℤ) ^ g ∣ a := by
        rw [sub_zero] at hab
        exact (three_coprime_pow ht3' δ).dvd_of_dvd_mul_left hab
      exact hsmall a ha0 haN h1
    have hN1 : 1 ≤ N := le_trans (Nat.one_le_iff_ne_zero.2 (Int.natAbs_ne_zero.2 ha0)) haN
    have h1 := mid_bound hZ t ht ht3' δ g a b ha0 hb0 hne hab
    have h2 := hK N δ hN1
    calc g ≤ K * L ^ 2 * H := h1.trans h2
      _ ≤ (K + 1) * L ^ 2 * H := by gcongr; omega
  -- to real logarithms
  have hL : (L : ℝ) ≤ 2 * (1 + Real.log (δ + 1)) := by
    have := natLog_le_real (δ + 1)
    have h0 : 0 ≤ Real.log ((δ : ℝ) + 1) := Real.log_nonneg (by linarith [(Nat.cast_nonneg δ : (0:ℝ) ≤ δ)])
    simp only [L]; push_cast at this ⊢; linarith
  have hNcast : ((N : ℕ) : ℝ) = (((max |a| |b| : ℤ)) : ℝ) := by
    have hz : ((N : ℕ) : ℤ) = max |a| |b| := by
      rw [hN, Int.natCast_natAbs, abs_of_nonneg (le_max_of_le_left (abs_nonneg a))]
    rw [← hz, Int.cast_natCast]
  have hH : (H : ℝ) ≤ 2 * (1 + Real.log ((max |a| |b| : ℤ) : ℝ)) := by
    have := natLog_le_real N
    have h0 : 0 ≤ Real.log ((N : ℕ) : ℝ) := Real.log_natCast_nonneg _
    rw [hNcast] at this h0
    simp only [H]; rw [Nat.cast_add, Nat.cast_one]; linarith
  have hL0 : (0 : ℝ) ≤ L := by positivity
  have hH0 : (0 : ℝ) ≤ H := by positivity
  calc (g : ℝ) ≤ ((K + 1) * L ^ 2 * H : ℕ) := by exact_mod_cast hnat
    _ = (K + 1 : ℝ) * (L : ℝ) ^ 2 * H := by push_cast; ring
    _ ≤ (K + 1 : ℝ) * (2 * (1 + Real.log (δ + 1))) ^ 2 * (2 * (1 + Real.log ((max |a| |b| : ℤ) : ℝ))) := by
      gcongr
    _ = 8 * ((K : ℝ) + 1) * (1 + Real.log (δ + 1)) ^ 2 * (1 + Real.log ((max |a| |b| : ℤ) : ℝ)) := by ring
    _ = _ := by push_cast; ring

/-- **Conditional headline with the 3-adic input reduced to the zero lemma (proved).** -/
theorem liouvilleCantorFullProfile_of_baker_zeroLemma
    (hB : NormalNumbers.CantorExactExponentProfile.Literature.BakerLogDiscrepancy)
    (hZ : Literature.LaurentZeroLemma) : NormalNumbers.CantorRepetition.LiouvilleCantorFullProfile :=
  NormalNumbers.CantorRepetition.liouvilleCantorFullProfile_of_baker_padic hB
    (padicTwoLogs_of_zeroLemma hZ)

end PadicTwoLogs
