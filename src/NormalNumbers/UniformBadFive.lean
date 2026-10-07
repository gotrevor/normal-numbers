/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Architect
import NormalNumbers.UniformBadCount
import NormalNumbers.UniformBadRoute

/-!
# `c⋆ ≤ 5` by two-rate counting

The counting engine of `UniformBadCount` (`Count.growth`, with a level-dependent growth rate) at
exponent `5`:

* **base `2` exact** (`runBad5`): the last five binary digits of an alive cell are not all equal.
  From level `6` on, such a kill has multiplicity `1` over its ancestor at level `k − 4`
  (`card_runKill5_le_one`): the parent is alive, so the run digit is the complement of the
  ancestor's last digit.
* **kill level** `L5 b n` with `3 b^{n+5} ≤ 4 · 2^L` and `2 · 2^L < 3 b^{n+5}` (`L5_spec`): there a
  base-`b` window of order `n` spans fewer than `3` cells and meets at most `4`
  (`card_meets5_le`); it is charged to the ancestor at lag `lag5 b = ⌊log₂(3(b⁵ − 2)/4)⌋`, which
  meets at most one window of that order (`meets5_unique`).  The perfect powers `4, 8, 9` are not
  counted (`Base5`); `admissible_iff_nonPerfectPow` recovers them.
* **two growth rates** (`g5`): `33/20` below a base-`3` kill level, `181/100` otherwise.  Base-`3`
  kill levels satisfy `L5 3 (n+2) ≥ L5 3 n + 3` (`L5_three`), so no three consecutive levels all
  carry one (`no_three`), and the growth over `l` levels is at least
  `F5 l = (181/100 · (33/20)²)^{⌊l/3⌋} (33/20)^{l mod 3}` (`prod_g5_ge`).

The balance (`card_kill5_le`): at a level of either type the kills are at most
`(1/F5 4 + [base-3 level] 4/F5 6 + Σ_{b ≥ 4} w5 b) cnt k`, i.e. `0.1230 + 0.0494 ≤ 0.19` and
`0.1230 + 0.1647 + 0.0494 ≤ 0.35`.  The base series `Σ w5 b ≤ 0.0494` (`sum_w5_le`) is exact
rational arithmetic for `b ≤ 29` (`sum_w5_small`) plus a telescoping tail.  Probe:
`scripts/cstar_models/pess.js` and the lap-10 recomputation (slack `0.013` at the base-3 levels).
-/

namespace NormalNumbers.UniformBadThreshold

open NormalNumbers.UniformBad (dnear)

namespace Count

/-! ## The exponent-`5` forbidden cells -/

section Five

/-- Base `2`: the last five binary digits of a level-`k` cell agree (`k ≥ 5`). -/
def runBad5 (k a : ℕ) : Prop := 5 ≤ k ∧ (a % 32 = 0 ∨ a % 32 = 31)

/-- The kill level of the base-`b` windows of order `n`: `3 b^{n+5} ≤ 4 · 2^L` and
`2 · 2^L < 3 b^{n+5}`, so a window spans fewer than `3` cells there. -/
def L5 (b n : ℕ) : ℕ := Nat.clog 2 (3 * b ^ (n + 5)) - 2

/-- The closed cell `[a/2ᵏ, (a+1)/2ᵏ]` meets the open window of radius `b^{−n−5}` around `A/bⁿ`. -/
def meets5 (k a b n A : ℕ) : Prop :=
  a * b ^ (n + 5) < 2 ^ k * (A * b ^ 5 + 1) ∧ 2 ^ k * (A * b ^ 5) < (a + 1) * b ^ (n + 5) + 2 ^ k

/-- The counted bases: `b ≥ 3` except the perfect powers `4, 8, 9` (handled by `goodBase_pow`). -/
def Base5 (b : ℕ) : Prop := 3 ≤ b ∧ b ≠ 4 ∧ b ≠ 8 ∧ b ≠ 9

/-- The forbidden cells for exponent `5`. -/
def bad5 (k a : ℕ) : Prop := runBad5 k a ∨ ∃ b n A, Base5 b ∧ L5 b n = k ∧ meets5 k a b n A

/-- The lag at which base-`b` kills are charged: `4 · 2^{lag} ≤ 3 (b⁵ − 2)`. -/
def lag5 (b : ℕ) : ℕ := Nat.log 2 (3 * (b ^ 5 - 2) / 4)

theorem L5_spec {b n : ℕ} (hb : 2 ≤ b) :
    3 * b ^ (n + 5) ≤ 4 * 2 ^ L5 b n ∧ 2 * 2 ^ L5 b n < 3 * b ^ (n + 5) := by
  have hP : 32 ≤ b ^ (n + 5) := by
    calc 32 = 2 ^ 5 := by norm_num
      _ ≤ b ^ 5 := Nat.pow_le_pow_left hb 5
      _ ≤ b ^ (n + 5) := Nat.pow_le_pow_right (by omega) (by omega)
  set c := Nat.clog 2 (3 * b ^ (n + 5)) with hc
  have h1 : 3 * b ^ (n + 5) ≤ 2 ^ c := Nat.le_pow_clog (by norm_num) _
  have h2 : 2 ^ c.pred < 3 * b ^ (n + 5) := Nat.pow_pred_clog_lt_self (by norm_num) (by omega)
  have hc2 : 2 ≤ c := by
    by_contra h
    have : 2 ^ c ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  obtain ⟨m, hm⟩ : ∃ m, c = m + 2 := ⟨c - 2, by omega⟩
  have hL : L5 b n = m := by show c - 2 = m; omega
  rw [hL]
  rw [hm, show 2 ^ (m + 2) = 4 * 2 ^ m by ring] at h1
  rw [hm, show (m + 2).pred = m + 1 from rfl, show 2 ^ (m + 1) = 2 * 2 ^ m by ring] at h2
  constructor <;> omega

theorem two_pow_lag5 {b : ℕ} (hb : 3 ≤ b) : 4 * 2 ^ lag5 b ≤ 3 * (b ^ 5 - 2) := by
  have h5 : 243 ≤ b ^ 5 := by
    calc 243 = 3 ^ 5 := by norm_num
      _ ≤ b ^ 5 := Nat.pow_le_pow_left hb 5
  have h1 := Nat.pow_log_le_self 2 (show 3 * (b ^ 5 - 2) / 4 ≠ 0 by omega)
  have h2 := Nat.div_mul_le_self (3 * (b ^ 5 - 2)) 4
  unfold lag5; omega

theorem seven_le_lag5 {b : ℕ} (hb : 3 ≤ b) : 7 ≤ lag5 b := by
  have h5 : 243 ≤ b ^ 5 := by
    calc 243 = 3 ^ 5 := by norm_num
      _ ≤ b ^ 5 := Nat.pow_le_pow_left hb 5
  exact Nat.le_log_of_pow_le (by norm_num) (by omega)

theorem lag5_lt_L5 {b : ℕ} (hb : 3 ≤ b) (n : ℕ) : lag5 b < L5 b n := by
  have h1 := two_pow_lag5 hb
  have h2 : b ^ 5 ≤ b ^ (n + 5) := Nat.pow_le_pow_right (by omega) (by omega)
  have h3 := (L5_spec (n := n) (by omega : 2 ≤ b)).1
  have h4 : 3 ^ 5 ≤ b ^ 5 := Nat.pow_le_pow_left hb 5
  exact (pow_lt_pow_iff_right₀ (by norm_num : 1 < 2)).1 (by omega)

theorem eight_le_L5 {b : ℕ} (hb : 3 ≤ b) (n : ℕ) : 8 ≤ L5 b n := by
  have h1 := (L5_spec (n := n) (by omega : 2 ≤ b)).1
  have h2 : 3 ^ (n + 5) ≤ b ^ (n + 5) := Nat.pow_le_pow_left hb _
  have h3 : 3 ^ 5 ≤ 3 ^ (n + 5) := Nat.pow_le_pow_right (by omega) (by omega)
  have : 2 ^ 7 < 2 ^ L5 b n := by norm_num at h3 ⊢; omega
  have := (pow_lt_pow_iff_right₀ (by norm_num : 1 < 2)).1 this
  omega

theorem L5_lt_succ {b : ℕ} (hb : 2 ≤ b) (n : ℕ) : L5 b n < L5 b (n + 1) := by
  have h1 := (L5_spec (n := n) hb).2
  have h2 := (L5_spec (n := n + 1) hb).1
  have e : b ^ (n + 1 + 5) = b * b ^ (n + 5) := by ring
  rw [e] at h2
  have h3 : 2 * b ^ (n + 5) ≤ b * b ^ (n + 5) := Nat.mul_le_mul_right _ hb
  exact (pow_lt_pow_iff_right₀ (by norm_num : 1 < 2)).1 (by omega)

theorem L5_strictMono {b : ℕ} (hb : 2 ≤ b) : StrictMono (L5 b) :=
  strictMono_nat_of_lt_succ (L5_lt_succ hb)

/-- Base-`3` kill levels: no two consecutive gaps of one. -/
theorem L5_three (n : ℕ) : L5 3 n + 3 ≤ L5 3 (n + 2) := by
  have h1 := (L5_spec (b := 3) (n := n) (by norm_num)).2
  have h2 := (L5_spec (b := 3) (n := n + 2) (by norm_num)).1
  have e : (3 : ℕ) ^ (n + 2 + 5) = 9 * 3 ^ (n + 5) := by ring
  rw [e] at h2
  have : 2 ^ (L5 3 n + 2) < 2 ^ L5 3 (n + 2) := by rw [pow_add]; omega
  have := (pow_lt_pow_iff_right₀ (by norm_num : 1 < 2)).1 this
  omega

/-- A window met by a cell is met by each of its ancestors. -/
theorem meets5_anc {j D a b n A : ℕ} (h : meets5 (j + D) a b n A) :
    meets5 j (a / 2 ^ D) b n A := by
  obtain ⟨h1, h2⟩ := h
  rw [pow_add 2 j D] at h1 h2
  set q := a / 2 ^ D with hq
  set t := 2 ^ D with ht
  set P := b ^ (n + 5) with hP
  have htpos : 0 < t := by positivity
  have hq1 : q * t ≤ a := Nat.div_mul_le_self a t
  have hq2 : a + 1 ≤ (q + 1) * t := by
    have := Nat.div_add_mod a t
    have := Nat.mod_lt a htpos
    nlinarith
  constructor
  · have h3 : q * t * P ≤ a * P := Nat.mul_le_mul_right _ hq1
    have : q * P * t < 2 ^ j * (A * b ^ 5 + 1) * t := by nlinarith
    exact Nat.lt_of_mul_lt_mul_right this
  · have h3 : (a + 1) * P ≤ (q + 1) * t * P := Nat.mul_le_mul_right _ hq2
    have : 2 ^ j * (A * b ^ 5) * t < ((q + 1) * P + 2 ^ j) * t := by nlinarith
    exact Nat.lt_of_mul_lt_mul_right this

/-- A cell of level `j` with `b^{n+5} ≤ 2^j (b⁵ − 2)` meets at most one window of order `n`. -/
theorem meets5_unique {j b n A A' q : ℕ} (hb : 2 ≤ b) (hPj : b ^ (n + 5) ≤ 2 ^ j * (b ^ 5 - 2))
    (h : meets5 j q b n A) (h' : meets5 j q b n A') : A = A' := by
  have key : ∀ {A A'}, meets5 j q b n A → meets5 j q b n A' → A < A' → False := by
    intro A A' h h' hlt
    obtain ⟨h1, -⟩ := h
    obtain ⟨-, h2⟩ := h'
    set R := 2 ^ j
    set P := b ^ (n + 5)
    set B := b ^ 5
    have hB : 2 ≤ B := by
      have : 2 ^ 5 ≤ b ^ 5 := Nat.pow_le_pow_left hb 5
      omega
    have h3 : R * ((A + 1) * B) ≤ R * (A' * B) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hlt)
    have h4 : R * (B - 2) + R * 2 = R * B := by rw [← mul_add, Nat.sub_add_cancel hB]
    nlinarith
  rcases Nat.lt_trichotomy A A' with hlt | heq | hlt
  · exact (key h h' hlt).elim
  · exact heq
  · exact (key h' h hlt).elim

open Classical in
/-- A window spanning fewer than `3` cells meets at most `4` of them. -/
theorem card_meets5_le (k b n A : ℕ) (hk : 2 * 2 ^ k < 3 * b ^ (n + 5)) :
    ((Finset.range (2 ^ k)).filter (fun a => meets5 k a b n A)).card ≤ 4 := by
  set S := (Finset.range (2 ^ k)).filter (fun a => meets5 k a b n A)
  rcases S.eq_empty_or_nonempty with h | h
  · rw [h]; simp
  set m := S.min' h
  have hm : m ∈ S := S.min'_mem h
  have hmS := (Finset.mem_filter.1 hm).2
  have hsub : S ⊆ Finset.Icc m (m + 3) := by
    intro a ha
    have haS := (Finset.mem_filter.1 ha).2
    refine Finset.mem_Icc.2 ⟨S.min'_le a ha, ?_⟩
    obtain ⟨h1, -⟩ := haS
    obtain ⟨-, h2⟩ := hmS
    have : a * b ^ (n + 5) < (m + 4) * b ^ (n + 5) := by nlinarith
    have := Nat.lt_of_mul_lt_mul_right this
    omega
  calc S.card ≤ (Finset.Icc m (m + 3)).card := Finset.card_le_card hsub
    _ = 4 := by rw [Nat.card_Icc]; omega

/-! ### Charging -/

open Classical in
/-- Base-`2` kills at level `k + 1`, charged to the ancestor at level `k − 4` (multiplicity `2`). -/
theorem card_runKill5_le_two (k : ℕ) (h4 : 4 ≤ k) :
    ((Finset.range (2 ^ (k + 1))).filter
      (fun a => Alive bad5 k (a / 2) ∧ runBad5 (k + 1) a)).card ≤ 2 * cnt bad5 (k - 4) := by
  refine card_le_of_charge bad5 _ (fun a => a / 32) (k - 4) 2 (fun a ha => ?_) fun q => ?_
  · have ha := (Finset.mem_filter.1 ha).2.1
    have e : k = (k - 4) + 4 := by omega
    rw [e] at ha
    have := alive_anc bad5 4 ha
    rwa [Nat.div_div_eq_div_mul] at this
  · calc _ ≤ ({32 * q, 32 * q + 31} : Finset ℕ).card := by
          refine Finset.card_le_card fun a ha => ?_
          obtain ⟨ha', hq⟩ := Finset.mem_filter.1 ha
          obtain ⟨-, -, -, h⟩ := Finset.mem_filter.1 ha'
          simp only [Finset.mem_insert, Finset.mem_singleton]
          omega
      _ ≤ 2 := Finset.card_le_two

open Classical in
/-- From level `6` on, the base-`2` charge is exact: the parent is alive, so its own last five
digits do not agree, and the ancestor at level `k − 4` determines the run digit. -/
theorem card_runKill5_le_one (k : ℕ) (h5 : 5 ≤ k) :
    ((Finset.range (2 ^ (k + 1))).filter
      (fun a => Alive bad5 k (a / 2) ∧ runBad5 (k + 1) a)).card ≤ 1 * cnt bad5 (k - 4) := by
  refine card_le_of_charge bad5 _ (fun a => a / 32) (k - 4) 1 (fun a ha => ?_) fun q => ?_
  · have ha := (Finset.mem_filter.1 ha).2.1
    have e : k = (k - 4) + 4 := by omega
    rw [e] at ha
    have := alive_anc bad5 4 ha
    rwa [Nat.div_div_eq_div_mul] at this
  · have hnr : ∀ a, Alive bad5 k (a / 2) → ¬ runBad5 k (a / 2) := by
      intro a h hr
      obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
      exact h.2 (Or.inl hr)
    refine Finset.card_le_one.2 fun a ha a' ha' => ?_
    obtain ⟨ha1, hq⟩ := Finset.mem_filter.1 ha
    obtain ⟨-, hal, hr⟩ := Finset.mem_filter.1 ha1
    obtain ⟨ha1', hq'⟩ := Finset.mem_filter.1 ha'
    obtain ⟨-, hal', hr'⟩ := Finset.mem_filter.1 ha1'
    have n1 := hnr a hal
    have n2 := hnr a' hal'
    simp only [runBad5] at n1 n2 hr hr'
    omega

open Classical in
/-- Base-`b` kills at level `k + 1`, charged to the ancestor at lag `lag5 b` (multiplicity `4`). -/
theorem card_winKill5_le (k b : ℕ) (hb : 3 ≤ b) :
    ((Finset.range (2 ^ (k + 1))).filter
      (fun a => Alive bad5 k (a / 2) ∧ ∃ n A, L5 b n = k + 1 ∧ meets5 (k + 1) a b n A)).card ≤
      4 * cnt bad5 (k + 1 - lag5 b) := by
  set S := (Finset.range (2 ^ (k + 1))).filter
      (fun a => Alive bad5 k (a / 2) ∧ ∃ n A, L5 b n = k + 1 ∧ meets5 (k + 1) a b n A)
  rcases S.eq_empty_or_nonempty with hS | ⟨a₀, ha₀⟩
  · rw [hS]; simp
  obtain ⟨-, -, n₀, A₀, hn₀, hA₀⟩ := Finset.mem_filter.1 ha₀
  have hb2 : 2 ≤ b := by omega
  have hlag := lag5_lt_L5 hb n₀
  have hlag1 := seven_le_lag5 hb
  rw [hn₀] at hlag
  set j := k + 1 - lag5 b with hj
  have ejk : k + 1 = j + lag5 b := by omega
  refine card_le_of_charge bad5 S (fun a => a / 2 ^ lag5 b) j 4 (fun a ha => ?_) fun q => ?_
  · have ha := (Finset.mem_filter.1 ha).2.1
    have e : k = j + (lag5 b - 1) := by omega
    rw [e] at ha
    have := alive_anc bad5 (lag5 b - 1) ha
    rwa [Nat.div_div_eq_div_mul, ← pow_succ', show lag5 b - 1 + 1 = lag5 b by omega] at this
  · rcases (S.filter fun a => a / 2 ^ lag5 b = q).eq_empty_or_nonempty with hF | ⟨a₁, ha₁⟩
    · rw [hF]; simp
    obtain ⟨ha₁S, hq₁⟩ := Finset.mem_filter.1 ha₁
    obtain ⟨-, -, n₁, A₁, hn₁, hA₁⟩ := Finset.mem_filter.1 ha₁S
    have hPj : b ^ (n₁ + 5) ≤ 2 ^ j * (b ^ 5 - 2) := by
      have h1 := (L5_spec (n := n₁) hb2).1
      rw [hn₁, ejk, pow_add 2 j] at h1
      have h2 : 4 * 2 ^ lag5 b * 2 ^ j ≤ 3 * (b ^ 5 - 2) * 2 ^ j :=
        Nat.mul_le_mul_right _ (two_pow_lag5 hb)
      have : 3 * b ^ (n₁ + 5) ≤ 3 * (2 ^ j * (b ^ 5 - 2)) := by
        calc 3 * b ^ (n₁ + 5) ≤ 4 * (2 ^ j * 2 ^ lag5 b) := h1
          _ = 4 * 2 ^ lag5 b * 2 ^ j := by ring
          _ ≤ 3 * (b ^ 5 - 2) * 2 ^ j := h2
          _ = 3 * (2 ^ j * (b ^ 5 - 2)) := by ring
      omega
    have hsub : S.filter (fun a => a / 2 ^ lag5 b = q) ⊆
        (Finset.range (2 ^ (k + 1))).filter (fun a => meets5 (k + 1) a b n₁ A₁) := by
      intro a ha
      obtain ⟨haS, hq⟩ := Finset.mem_filter.1 ha
      obtain ⟨hr, -, n, A, hn, hA⟩ := Finset.mem_filter.1 haS
      have hnn : n = n₁ := (L5_strictMono hb2).injective (hn.trans hn₁.symm)
      subst hnn
      have m1 : meets5 j q b n A := by
        rw [ejk] at hA; have := meets5_anc hA; rwa [hq] at this
      have m2 : meets5 j q b n A₁ := by
        rw [ejk] at hA₁; have := meets5_anc hA₁; rwa [hq₁] at this
      have hAA := meets5_unique hb2 hPj m1 m2
      subst hAA
      exact Finset.mem_filter.2 ⟨hr, hA⟩
    exact (Finset.card_le_card hsub).trans
      (card_meets5_le (k + 1) b n₁ A₁ (hn₁ ▸ (L5_spec hb2).2))

open Classical in
theorem killSet5_subset (k : ℕ) :
    killSet bad5 k ⊆ ((Finset.range (2 ^ (k + 1))).filter
        (fun a => Alive bad5 k (a / 2) ∧ runBad5 (k + 1) a)) ∪
      (Finset.Ioc 2 (2 ^ (k + 3))).biUnion (fun b => (Finset.range (2 ^ (k + 1))).filter
        (fun a => Alive bad5 k (a / 2) ∧ Base5 b ∧
          ∃ n A, L5 b n = k + 1 ∧ meets5 (k + 1) a b n A)) := by
  intro a ha
  have hr : a ∈ Finset.range (2 ^ (k + 1)) := (Finset.mem_filter.1 ha).1
  obtain ⟨hal, hbad⟩ := (mem_killSet bad5).1 ha
  rcases hbad with hrun | ⟨b, n, A, hb, hn, hm⟩
  · exact Finset.mem_union_left _ (Finset.mem_filter.2 ⟨hr, hal, hrun⟩)
  · refine Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨b, Finset.mem_Ioc.2 ⟨hb.1, ?_⟩,
      Finset.mem_filter.2 ⟨hr, hal, hb, n, A, hn, hm⟩⟩)
    have h1 := (L5_spec (n := n) (by have := hb.1; omega : 2 ≤ b)).1
    rw [hn] at h1
    have e : 2 ^ (k + 3) = 4 * 2 ^ (k + 1) := by rw [pow_add 2 (k + 1) 2]; ring_nf
    calc b ≤ b ^ (n + 5) := Nat.le_self_pow (by omega) b
      _ ≤ 2 ^ (k + 3) := by omega

/-! ### Two growth rates -/

/-- Level `m` carries a base-`3` kill. -/
def K3 (m : ℕ) : Prop := ∃ n, L5 3 n = m

theorem no_three (m : ℕ) : K3 m → K3 (m + 1) → K3 (m + 2) → False := by
  rintro ⟨n1, h1⟩ ⟨n2, h2⟩ ⟨n3, h3⟩
  have hs := L5_strictMono (b := 3) (by norm_num)
  have a12 : n1 < n2 := hs.lt_iff_lt.1 (by omega)
  have a23 : n2 < n3 := hs.lt_iff_lt.1 (by omega)
  have := L5_three n1
  have := hs.monotone (show n1 + 2 ≤ n3 by omega)
  omega

open Classical in
/-- The growth rate below level `k + 1`: `33/20` before a base-`3` kill level, else `181/100`. -/
noncomputable def g5 (k : ℕ) : ℝ := if K3 (k + 1) then 33 / 20 else 181 / 100

theorem g5_ge (k : ℕ) : (33 / 20 : ℝ) ≤ g5 k := by
  unfold g5; split_ifs <;> norm_num

theorem g5_le (k : ℕ) : g5 k ≤ 181 / 100 := by
  unfold g5; split_ifs <;> norm_num

theorem triple_ge (j : ℕ) : (181 / 100 * (33 / 20) ^ 2 : ℝ) ≤ g5 j * g5 (j + 1) * g5 (j + 2) := by
  unfold g5
  split_ifs with h1 h2 h3 <;> try norm_num
  exact no_three _ h1 h2 h3

/-- The guaranteed growth over `l` levels: `(181/100 · (33/20)²)^{⌊l/3⌋} (33/20)^{l mod 3}`. -/
def F5 (l : ℕ) : ℚ := (181 / 100 * (33 / 20) ^ 2) ^ (l / 3) * (33 / 20) ^ (l % 3)

theorem F5_cast (l : ℕ) : ((F5 l : ℚ) : ℝ) =
    (181 / 100 * (33 / 20) ^ 2 : ℝ) ^ (l / 3) * (33 / 20) ^ (l % 3) := by
  simp [F5]

theorem F5_pos (l : ℕ) : 0 < F5 l := by unfold F5; positivity

theorem prod_g5_ge : ∀ d j : ℕ, ((F5 d : ℚ) : ℝ) ≤ ∏ i ∈ Finset.Ico j (j + d), g5 i := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    intro j
    rw [F5_cast]
    rcases Nat.lt_or_ge d 3 with hd | hd
    · rw [Nat.div_eq_of_lt hd, Nat.mod_eq_of_lt hd, pow_zero, one_mul]
      calc (33 / 20 : ℝ) ^ d = ∏ _i ∈ Finset.Ico j (j + d), (33 / 20 : ℝ) := by
            rw [Finset.prod_const, Nat.card_Ico]; congr 1; omega
        _ ≤ _ := Finset.prod_le_prod (fun _ _ => by norm_num) fun i _ => g5_ge i
    · have h := ih (d - 3) (by omega) (j + 3)
      rw [F5_cast, show j + 3 + (d - 3) = j + d by omega] at h
      rw [← Finset.prod_Ico_consecutive _ (show j ≤ j + 3 by omega) (show j + 3 ≤ j + d by omega)]
      have e3 : ∏ i ∈ Finset.Ico j (j + 3), g5 i = g5 j * g5 (j + 1) * g5 (j + 2) := by
        rw [Finset.prod_Ico_eq_prod_range, show j + 3 - j = 3 by omega]
        simp [Finset.prod_range_succ]
      rw [e3]
      have hdiv : d / 3 = (d - 3) / 3 + 1 := by omega
      have hmod : d % 3 = (d - 3) % 3 := by omega
      rw [hdiv, hmod, pow_succ]
      have h0 : (0 : ℝ) ≤ (181 / 100 * (33 / 20) ^ 2 : ℝ) ^ ((d - 3) / 3) * (33 / 20) ^ ((d - 3) % 3) :=
        by positivity
      calc (181 / 100 * (33 / 20) ^ 2 : ℝ) ^ ((d - 3) / 3) * (181 / 100 * (33 / 20) ^ 2) *
            (33 / 20) ^ ((d - 3) % 3)
          = (181 / 100 * (33 / 20) ^ 2) * ((181 / 100 * (33 / 20) ^ 2 : ℝ) ^ ((d - 3) / 3) *
            (33 / 20) ^ ((d - 3) % 3)) := by ring
        _ ≤ (g5 j * g5 (j + 1) * g5 (j + 2)) * ∏ i ∈ Finset.Ico (j + 3) (j + d), g5 i :=
            mul_le_mul (triple_ge j) h h0 (by
              have := g5_ge j; have := g5_ge (j + 1); have := g5_ge (j + 2); positivity)

/-! ### The base series -/

/-- The charge weight of a base `b ≥ 4`. -/
def w5 (b : ℕ) : ℚ := if b = 4 ∨ b = 8 ∨ b = 9 then 0 else 4 / F5 (lag5 b - 1)

/-- The explicit bases `4 ≤ b ≤ 29`. -/
theorem sum_w5_small : ∑ b ∈ Finset.Ioc 3 29, w5 b ≤ 457 / 10000 := by
  native_decide

theorem F5_ge (l : ℕ) : (1089 / 1156 : ℚ) * (17 / 10) ^ l ≤ F5 l := by
  unfold F5
  have e : (17 / 10 : ℚ) ^ l = ((17 / 10) ^ 3) ^ (l / 3) * (17 / 10) ^ (l % 3) := by
    rw [← pow_mul, ← pow_add]; congr 1; omega
  rw [e]
  have h1 : ((17 / 10 : ℚ) ^ 3) ^ (l / 3) ≤ (181 / 100 * (33 / 20) ^ 2) ^ (l / 3) :=
    pow_le_pow_left₀ (by norm_num) (by norm_num) _
  have h2 : (1089 / 1156 : ℚ) * (17 / 10) ^ (l % 3) ≤ (33 / 20) ^ (l % 3) := by
    have : l % 3 < 3 := Nat.mod_lt _ (by norm_num)
    interval_cases (l % 3) <;> norm_num
  calc (1089 / 1156 : ℚ) * (((17 / 10) ^ 3) ^ (l / 3) * (17 / 10) ^ (l % 3))
      = ((17 / 10) ^ 3) ^ (l / 3) * ((1089 / 1156) * (17 / 10) ^ (l % 3)) := by ring
    _ ≤ (181 / 100 * (33 / 20) ^ 2) ^ (l / 3) * (33 / 20) ^ (l % 3) :=
        mul_le_mul h1 h2 (by positivity) (by positivity)

/-- For `b ≥ 30`, `w5 b ≤ 4 · (1156/1089) · (1/40) / (b (b − 1))`. -/
theorem w5_tail {b : ℕ} (hb : 30 ≤ b) :
    ((w5 b : ℚ) : ℝ) ≤ 4 * (1156 / 1089) * (1 / 40) * (1 / ((b : ℝ) * ((b : ℝ) - 1))) := by
  have hb3 : 3 ≤ b := by omega
  have hl7 := seven_le_lag5 hb3
  set l := lag5 b - 1 with hl
  -- `b⁵ < 2^{lag + 3}`
  have hb5 : b ^ 5 < 2 ^ (l + 4) := by
    have h5 : 243 ≤ b ^ 5 := by
      calc 243 = 3 ^ 5 := by norm_num
        _ ≤ b ^ 5 := Nat.pow_le_pow_left hb3 5
    have h1 := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) (3 * (b ^ 5 - 2) / 4)
    have h2 : 3 * (b ^ 5 - 2) < 4 * 2 ^ (Nat.log 2 (3 * (b ^ 5 - 2) / 4)).succ := by
      have := (Nat.div_lt_iff_lt_mul (by norm_num : 0 < 4)).1 h1; omega
    have e : l + 4 = (Nat.log 2 (3 * (b ^ 5 - 2) / 4)).succ + 2 := by
      simp only [hl, lag5] at hl7 ⊢; omega
    rw [e, pow_add]; omega
  have hbR : (30 : ℝ) ≤ b := by exact_mod_cast hb
  have hb5R : (b : ℝ) ^ 5 < 2 ^ (l + 4) := by exact_mod_cast hb5
  -- the weight
  have hw : ((w5 b : ℚ) : ℝ) ≤ 4 * (1156 / 1089) * ((10 : ℝ) / 17) ^ l := by
    have hF := F5_ge l
    have hFR : (1089 / 1156 : ℝ) * (17 / 10) ^ l ≤ ((F5 l : ℚ) : ℝ) := by
      have := (Rat.cast_le (K := ℝ)).2 hF; push_cast at this; exact this
    have hpos : (0 : ℝ) < (1089 / 1156 : ℝ) * (17 / 10) ^ l := by positivity
    have hw' : ((w5 b : ℚ) : ℝ) ≤ 4 / ((F5 l : ℚ) : ℝ) := by
      unfold w5
      split_ifs
      · simp only [Rat.cast_zero]; have := F5_pos l; positivity
      · push_cast [hl]; exact le_rfl
    calc ((w5 b : ℚ) : ℝ) ≤ 4 / ((F5 l : ℚ) : ℝ) := hw'
      _ ≤ 4 / ((1089 / 1156 : ℝ) * (17 / 10) ^ l) := by gcongr
      _ = 4 * (1156 / 1089) * ((10 : ℝ) / 17) ^ l := by
          rw [show ((10 : ℝ) / 17) = (17 / 10)⁻¹ by norm_num, inv_pow]; field_simp
  -- `b (b − 1) (10/17)^l ≤ 1/40`
  have hbb : 0 < (b : ℝ) * ((b : ℝ) - 1) := by nlinarith
  set x := (b : ℝ) * ((b : ℝ) - 1) * ((10 : ℝ) / 17) ^ l with hx
  have hx0 : 0 ≤ x := by positivity
  have hy : ((10 : ℝ) / 17) ^ (4 * l) ≤ ((1 : ℝ) / 8) ^ l := by
    rw [pow_mul]; exact pow_le_pow_left₀ (by norm_num) (by norm_num) _
  have h8 : ((1 : ℝ) / 8) ^ l * (b : ℝ) ^ 15 ≤ 4096 := by
    have : (b : ℝ) ^ 15 ≤ (8 : ℝ) ^ l * 4096 := by
      have h1 : (b : ℝ) ^ 15 = ((b : ℝ) ^ 5) ^ 3 := by ring
      have h2 : ((2 : ℝ) ^ (l + 4)) ^ 3 = (8 : ℝ) ^ l * 4096 := by
        rw [← pow_mul, show (l + 4) * 3 = 3 * l + 12 by ring, pow_add, pow_mul]; norm_num
      rw [h1, ← h2]; gcongr
    calc ((1 : ℝ) / 8) ^ l * (b : ℝ) ^ 15 ≤ ((1 : ℝ) / 8) ^ l * ((8 : ℝ) ^ l * 4096) := by gcongr
      _ = 4096 := by rw [← mul_assoc, ← mul_pow]; norm_num
  have hx4 : x ^ 4 ≤ (1 / 40 : ℝ) ^ 4 := by
    have h1 : ((b : ℝ) * ((b : ℝ) - 1)) ^ 4 ≤ (b : ℝ) ^ 8 := by
      have : (b : ℝ) * ((b : ℝ) - 1) ≤ (b : ℝ) ^ 2 := by nlinarith
      calc ((b : ℝ) * ((b : ℝ) - 1)) ^ 4 ≤ ((b : ℝ) ^ 2) ^ 4 := by gcongr
        _ = (b : ℝ) ^ 8 := by ring
    have h7 : (30 : ℝ) ^ 7 ≤ (b : ℝ) ^ 7 := by gcongr
    have hb7 : (0 : ℝ) < (b : ℝ) ^ 7 := by positivity
    have : x ^ 4 * (b : ℝ) ^ 7 ≤ 4096 := by
      calc x ^ 4 * (b : ℝ) ^ 7
          = ((b : ℝ) * ((b : ℝ) - 1)) ^ 4 * ((10 : ℝ) / 17) ^ (4 * l) * (b : ℝ) ^ 7 := by
            rw [hx, mul_pow, ← pow_mul, mul_comm l 4]
        _ ≤ (b : ℝ) ^ 8 * ((1 : ℝ) / 8) ^ l * (b : ℝ) ^ 7 := by gcongr
        _ = ((1 : ℝ) / 8) ^ l * (b : ℝ) ^ 15 := by ring
        _ ≤ 4096 := h8
    have h30 : x ^ 4 * (30 : ℝ) ^ 7 ≤ 4096 :=
      le_trans (mul_le_mul_of_nonneg_left h7 (by positivity)) this
    nlinarith
  have hx1 : x ≤ 1 / 40 := le_of_pow_le_pow_left₀ (by norm_num) (by norm_num) hx4
  calc ((w5 b : ℚ) : ℝ) ≤ 4 * (1156 / 1089) * ((10 : ℝ) / 17) ^ l := hw
    _ = 4 * (1156 / 1089) * x * (1 / ((b : ℝ) * ((b : ℝ) - 1))) := by
        have hb1 : (b : ℝ) - 1 ≠ 0 := by linarith
        have hb0 : (b : ℝ) ≠ 0 := by linarith
        rw [hx]; field_simp
    _ ≤ 4 * (1156 / 1089) * (1 / 40) * (1 / ((b : ℝ) * ((b : ℝ) - 1))) := by gcongr

theorem telescope5 (M : ℕ) (hM : 1 ≤ M) : ∀ N : ℕ, M ≤ N →
    ∑ b ∈ Finset.Ioc M N, 1 / ((b : ℝ) * ((b : ℝ) - 1)) = 1 / (M : ℝ) - 1 / (N : ℝ) := by
  intro N hN
  induction N, hN using Nat.le_induction with
  | base => simp
  | succ N hN ih =>
    rw [Finset.sum_Ioc_succ_top hN, ih]
    have h0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
    push_cast
    rw [show (N : ℝ) + 1 - 1 = N by ring]
    field_simp
    ring

/-- **The base series.**  `Σ_{4 ≤ b ≤ M} w5 b ≤ 494/10000`. -/
theorem sum_w5_le (M : ℕ) : ∑ b ∈ Finset.Ioc 3 M, ((w5 b : ℚ) : ℝ) ≤ 494 / 10000 := by
  set f : ℕ → ℝ := fun b => ((w5 b : ℚ) : ℝ) with hf
  have hf0 : ∀ b, 0 ≤ f b := fun b => by
    simp only [hf]; unfold w5; split_ifs
    · simp
    · have := F5_pos (lag5 b - 1); push_cast; positivity
  have hsmall : ∑ b ∈ Finset.Ioc 3 29, f b ≤ 457 / 10000 := by
    have := sum_w5_small
    have h : ((∑ b ∈ Finset.Ioc 3 29, w5 b : ℚ) : ℝ) ≤ ((457 / 10000 : ℚ) : ℝ) := by
      exact_mod_cast this
    push_cast at h; simpa [hf] using h
  have htail : ∀ N, 29 ≤ N → ∑ b ∈ Finset.Ioc 29 N, f b ≤ 4 * (1156 / 1089) * (1 / 40) * (1 / 29) := by
    intro N hN
    calc ∑ b ∈ Finset.Ioc 29 N, f b
        ≤ ∑ b ∈ Finset.Ioc 29 N, 4 * (1156 / 1089) * (1 / 40) * (1 / ((b : ℝ) * ((b : ℝ) - 1))) :=
          Finset.sum_le_sum fun b hb => w5_tail (by have := (Finset.mem_Ioc.1 hb).1; omega)
      _ = 4 * (1156 / 1089) * (1 / 40) * (1 / 29 - 1 / N) := by
          rw [← Finset.mul_sum, telescope5 29 (by norm_num) N hN]; norm_num
      _ ≤ 4 * (1156 / 1089) * (1 / 40) * (1 / 29) := by
          have : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
          gcongr; linarith [one_div_pos.2 this]
  calc ∑ b ∈ Finset.Ioc 3 M, f b ≤ ∑ b ∈ Finset.Ioc 3 (M + 29), f b :=
        Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.Ioc_subset_Ioc_right (by omega)) fun b _ _ => hf0 b
    _ = ∑ b ∈ Finset.Ioc 3 29, f b + ∑ b ∈ Finset.Ioc 29 (M + 29), f b :=
        (Finset.sum_Ioc_consecutive f (by norm_num) (by omega)).symm
    _ ≤ _ := add_le_add hsmall (htail _ (by omega))
    _ ≤ 494 / 10000 := by norm_num

theorem lag5_three : lag5 3 = 7 := by native_decide

theorem not_K3_lt {m : ℕ} (h : m < 8) : ¬ K3 m := by
  rintro ⟨n, hn⟩; have := eight_le_L5 (b := 3) le_rfl n; omega

/-! ### The per-level balance -/

open Classical in
/-- **Per-level kill bound** for exponent `5`. -/
theorem card_kill5_le (k : ℕ)
    (hch : ∀ j ≤ k, (cnt bad5 j : ℝ) * ∏ i ∈ Finset.Ico j k, g5 i ≤ cnt bad5 k) :
    ((killSet bad5 k).card : ℝ) ≤ (2 - g5 k) * cnt bad5 k := by
  have hF : ∀ j ≤ k, (cnt bad5 j : ℝ) * ((F5 (k - j) : ℚ) : ℝ) ≤ cnt bad5 k := by
    intro j hj
    have h := prod_g5_ge (k - j) j
    rw [show j + (k - j) = k by omega] at h
    exact le_trans (mul_le_mul_of_nonneg_left h (by positivity)) (hch j hj)
  have hck : (0 : ℝ) ≤ cnt bad5 k := by positivity
  have hcard := (Finset.card_le_card (killSet5_subset k)).trans (Finset.card_union_le _ _)
  have hcard' := hcard.trans (Nat.add_le_add_left Finset.card_biUnion_le _)
  have hK : ((killSet bad5 k).card : ℝ) ≤
      (((Finset.range (2 ^ (k + 1))).filter
        (fun a => Alive bad5 k (a / 2) ∧ runBad5 (k + 1) a)).card : ℝ) +
      ∑ b ∈ Finset.Ioc 2 (2 ^ (k + 3)), (((Finset.range (2 ^ (k + 1))).filter
        (fun a => Alive bad5 k (a / 2) ∧ Base5 b ∧
          ∃ n A, L5 b n = k + 1 ∧ meets5 (k + 1) a b n A)).card : ℝ) := by
    exact_mod_cast hcard'
  -- no window kills below level `8`
  have hW0 : k + 1 < 8 → ∀ b, ((Finset.range (2 ^ (k + 1))).filter
        (fun a => Alive bad5 k (a / 2) ∧ Base5 b ∧
          ∃ n A, L5 b n = k + 1 ∧ meets5 (k + 1) a b n A)) = ∅ := by
    intro hk b
    refine Finset.filter_eq_empty_iff.2 fun a _ h => ?_
    obtain ⟨-, hb, n, A, hn, -⟩ := h
    have := eight_le_L5 hb.1 n
    omega
  rcases Nat.lt_or_ge k 5 with hk5 | hk5
  · -- levels `≤ 5`: only the base-`2` kills at level `5`
    simp only [hW0 (by omega), Finset.card_empty, Nat.cast_zero, Finset.sum_const_zero,
      add_zero] at hK
    have hg : g5 k = 181 / 100 := by
      unfold g5; rw [if_neg (not_K3_lt (by omega))]
    rw [hg]
    rcases Nat.lt_or_ge k 4 with hk4 | hk4
    · have : (Finset.range (2 ^ (k + 1))).filter
          (fun a => Alive bad5 k (a / 2) ∧ runBad5 (k + 1) a) = ∅ :=
        Finset.filter_eq_empty_iff.2 fun a _ h => by have := h.2.1; omega
      rw [this] at hK
      simp only [Finset.card_empty, Nat.cast_zero] at hK
      nlinarith
    · obtain rfl : k = 4 := by omega
      have h1 := (Nat.cast_le (α := ℝ)).2 (card_runKill5_le_two 4 le_rfl)
      push_cast at h1
      have h2 := hch 0 (by norm_num)
      have hp : ∏ i ∈ Finset.Ico 0 4, g5 i = (181 / 100 : ℝ) ^ 4 := by
        have : ∀ i ∈ Finset.Ico 0 4, g5 i = 181 / 100 := fun i hi => by
          have := (Finset.mem_Ico.1 hi).2
          unfold g5; rw [if_neg (not_K3_lt (by omega))]
        rw [Finset.prod_congr rfl this, Finset.prod_const]; simp
      rw [hp] at h2
      norm_num at h1 h2 ⊢
      linarith
  · -- runs
    have hrun : (((Finset.range (2 ^ (k + 1))).filter
        (fun a => Alive bad5 k (a / 2) ∧ runBad5 (k + 1) a)).card : ℝ) ≤ cnt bad5 (k - 4) := by
      have h1 := (Nat.cast_le (α := ℝ)).2 (card_runKill5_le_one k hk5)
      push_cast at h1; linarith
    have hr4 := hF (k - 4) (by omega)
    rw [show k - (k - 4) = 4 by omega] at hr4
    have e4 : ((F5 4 : ℚ) : ℝ) = 181 / 100 * (33 / 20) ^ 3 := by norm_num [F5]
    rw [e4] at hr4
    -- windows
    set v : ℕ → ℝ := fun b => if b = 3 then (if K3 (k + 1) then 4 / ((F5 6 : ℚ) : ℝ) else 0)
      else ((w5 b : ℚ) : ℝ) with hv
    have hwin : ∀ b ∈ Finset.Ioc 2 (2 ^ (k + 3)), (((Finset.range (2 ^ (k + 1))).filter
        (fun a => Alive bad5 k (a / 2) ∧ Base5 b ∧
          ∃ n A, L5 b n = k + 1 ∧ meets5 (k + 1) a b n A)).card : ℝ) ≤ v b * cnt bad5 k := by
      intro b _
      set S := (Finset.range (2 ^ (k + 1))).filter
        (fun a => Alive bad5 k (a / 2) ∧ Base5 b ∧ ∃ n A, L5 b n = k + 1 ∧ meets5 (k + 1) a b n A)
      rcases S.eq_empty_or_nonempty with hS | ⟨a₀, ha₀⟩
      · rw [hS, Finset.card_empty, Nat.cast_zero]
        have : 0 ≤ v b := by
          simp only [hv]; split_ifs
          · have := F5_pos 6; positivity
          · exact le_rfl
          · unfold w5; split_ifs
            · simp
            · have := F5_pos (lag5 b - 1); push_cast; positivity
        positivity
      obtain ⟨-, -, hB, n₀, A₀, hn₀, -⟩ := Finset.mem_filter.1 ha₀
      have hlag := lag5_lt_L5 hB.1 n₀
      have hlag7 := seven_le_lag5 hB.1
      rw [hn₀] at hlag
      have hsub : S ⊆ (Finset.range (2 ^ (k + 1))).filter
          (fun a => Alive bad5 k (a / 2) ∧ ∃ n A, L5 b n = k + 1 ∧ meets5 (k + 1) a b n A) := by
        intro a ha
        obtain ⟨hr, hal, -, h⟩ := Finset.mem_filter.1 ha
        exact Finset.mem_filter.2 ⟨hr, hal, h⟩
      have h1 := (Nat.cast_le (α := ℝ)).2 ((Finset.card_le_card hsub).trans (card_winKill5_le k b hB.1))
      push_cast at h1
      have h2 := hF (k + 1 - lag5 b) (by omega)
      rw [show k - (k + 1 - lag5 b) = lag5 b - 1 by omega] at h2
      have hFp : (0 : ℝ) < ((F5 (lag5 b - 1) : ℚ) : ℝ) := by exact_mod_cast F5_pos _
      have h3 : 4 * (cnt bad5 (k + 1 - lag5 b) : ℝ) ≤
          4 / ((F5 (lag5 b - 1) : ℚ) : ℝ) * cnt bad5 k := by
        rw [div_mul_eq_mul_div, le_div_iff₀ hFp]; linarith
      have hvb : v b = 4 / ((F5 (lag5 b - 1) : ℚ) : ℝ) := by
        simp only [hv]
        by_cases h3b : b = 3
        · subst h3b
          rw [if_pos rfl, if_pos ⟨n₀, hn₀⟩, lag5_three]
        · rw [if_neg h3b]
          unfold w5
          rw [if_neg (by have := hB.2; omega)]
          push_cast; rfl
      rw [hvb]; linarith
    have hsum := Finset.sum_le_sum hwin
    have hsplit : ∑ b ∈ Finset.Ioc 2 (2 ^ (k + 3)), v b * cnt bad5 k =
        (v 3 + ∑ b ∈ Finset.Ioc 3 (2 ^ (k + 3)), ((w5 b : ℚ) : ℝ)) * cnt bad5 k := by
      have h8 : 3 ≤ 2 ^ (k + 3) := by
        calc 3 ≤ 2 ^ 3 := by norm_num
          _ ≤ 2 ^ (k + 3) := Nat.pow_le_pow_right (by norm_num) (by omega)
      rw [← Finset.sum_mul, ← Finset.sum_Ioc_consecutive _ (show 2 ≤ 3 by norm_num) h8,
        show Finset.Ioc 2 3 = {3} by decide, Finset.sum_singleton]
      congr 2
      refine Finset.sum_congr rfl fun b hb => ?_
      have := (Finset.mem_Ioc.1 hb).1
      simp only [hv, if_neg (show b ≠ 3 by omega)]
    have hT := sum_w5_le (2 ^ (k + 3))
    have hT' := mul_le_mul_of_nonneg_right hT hck
    rw [hsplit, add_mul] at hsum
    have hc4 : (0 : ℝ) ≤ cnt bad5 (k - 4) := by positivity
    have hrr : (cnt bad5 (k - 4) : ℝ) ≤ 12299 / 100000 * cnt bad5 k := by
      norm_num at hr4; linarith
    have e6 : 4 / ((F5 6 : ℚ) : ℝ) ≤ 16473 / 100000 := by norm_num [F5]
    unfold g5
    by_cases hk3 : K3 (k + 1)
    · have hv3 : v 3 = 4 / ((F5 6 : ℚ) : ℝ) := by simp [hv, hk3]
      rw [if_pos hk3]
      have h6 : v 3 * cnt bad5 k ≤ 16473 / 100000 * cnt bad5 k := by
        rw [hv3]; exact mul_le_mul_of_nonneg_right e6 hck
      linarith
    · have hv3 : v 3 = 0 := by simp [hv, hk3]
      rw [if_neg hk3]
      have h6 : v 3 * cnt bad5 k = 0 := by rw [hv3, zero_mul]
      linarith

/-- The exponent-`5` tree grows by `g5 k` at level `k`. -/
theorem growth_five : ∀ k, g5 k * cnt bad5 k ≤ cnt bad5 (k + 1) :=
  growth bad5 (fun k => le_trans (by norm_num) (g5_ge k)) fun k hch => card_kill5_le k hch

/-! ### From cells to the Diophantine condition -/

theorem dnear_two_ge5 {ξ : ℝ} {n a : ℕ} (hξ : ξ ∈ cell (n + 5) a) (h : ¬ runBad5 (n + 5) a) :
    ((2 : ℝ) ^ 5)⁻¹ ≤ dnear ((2 : ℝ) ^ n * ξ) := by
  have hs : a % 32 ≠ 0 ∧ a % 32 ≠ 31 := by
    simp only [runBad5, not_and, not_or] at h; exact h (by omega)
  obtain ⟨h1, h2⟩ := hξ
  set x := (2 : ℝ) ^ n * ξ with hx
  have e : (2 : ℝ) ^ (n + 5) = 2 ^ n * 32 := by rw [pow_add]; norm_num
  have hpos : (0 : ℝ) < 2 ^ n := by positivity
  have hx1 : (a : ℝ) / 32 ≤ x := by
    rw [e] at h1
    calc (a : ℝ) / 32 = 2 ^ n * ((a : ℝ) / (2 ^ n * 32)) := by field_simp
      _ ≤ x := by rw [hx]; gcongr
  have hx2 : x ≤ ((a : ℝ) + 1) / 32 := by
    rw [e] at h2
    calc x ≤ 2 ^ n * (((a : ℝ) + 1) / (2 ^ n * 32)) := by rw [hx]; gcongr
      _ = ((a : ℝ) + 1) / 32 := by field_simp
  have ha : (a : ℝ) = 32 * ((a / 32 : ℕ) : ℝ) + ((a % 32 : ℕ) : ℝ) := by
    exact_mod_cast (Nat.div_add_mod a 32).symm
  have hs1 : (1 : ℝ) ≤ ((a % 32 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ a % 32)
  have hs2 : ((a % 32 : ℕ) : ℝ) ≤ 30 := by
    exact_mod_cast (by have := Nat.mod_lt a (by norm_num : 32 > 0); omega : a % 32 ≤ 30)
  unfold dnear
  rcases le_or_gt (round x) ((a / 32 : ℕ) : ℤ) with hm | hm
  · have hm' : ((round x : ℤ) : ℝ) ≤ ((a / 32 : ℕ) : ℝ) := by
      have := (Int.cast_le (R := ℝ)).2 hm
      rwa [Int.cast_natCast] at this
    rw [abs_of_nonneg (by linarith)]
    norm_num
    linarith
  · have hm' : ((a / 32 : ℕ) : ℝ) + 1 ≤ ((round x : ℤ) : ℝ) := by
      have hm2 : ((a / 32 : ℕ) : ℤ) + 1 ≤ round x := hm
      have := (Int.cast_le (R := ℝ)).2 hm2
      rwa [Int.cast_add, Int.cast_natCast, Int.cast_one] at this
    rw [abs_of_nonpos (by linarith)]
    norm_num
    linarith

theorem dnear_ge_of_cell5 {ξ : ℝ} {b n k a : ℕ} (hb : 2 ≤ b) (hξ : ξ ∈ cell k a)
    (h : ∀ A, ¬ meets5 k a b n A) : ((b : ℝ) ^ 5)⁻¹ ≤ dnear ((b : ℝ) ^ n * ξ) := by
  by_contra hlt
  replace hlt := not_le.1 hlt
  obtain ⟨h1, h2⟩ := hξ
  set x := (b : ℝ) ^ n * ξ with hx
  have hQ : (0 : ℝ) < 2 ^ k := by positivity
  have hb0 : (0 : ℝ) < b := by exact_mod_cast (by omega : 0 < b)
  have hB : (0 : ℝ) < (b : ℝ) ^ 5 := by positivity
  have hBn : (0 : ℝ) < (b : ℝ) ^ n := by positivity
  have hξ0 : 0 ≤ ξ := le_trans (by positivity) h1
  have hx0 : 0 ≤ x := by positivity
  have hd : |x - round x| < ((b : ℝ) ^ 5)⁻¹ := hlt
  have hB1 : ((b : ℝ) ^ 5)⁻¹ ≤ 1 :=
    inv_le_one_of_one_le₀ (one_le_pow₀ (by exact_mod_cast (by omega : 1 ≤ b)))
  have hr0 : 0 ≤ round x := by
    by_contra hneg
    replace hneg := not_le.1 hneg
    have : ((round x : ℤ) : ℝ) ≤ -1 := by exact_mod_cast (by omega : round x ≤ -1)
    have := (abs_lt.1 hd).2
    linarith
  set A := (round x).toNat with hA
  have hAx : ((A : ℕ) : ℝ) = ((round x : ℤ) : ℝ) := by
    rw [hA]; exact_mod_cast Int.toNat_of_nonneg hr0
  obtain ⟨hd1, hd2⟩ := abs_lt.1 hd
  rw [← hAx] at hd1 hd2
  have hBx1 : (b : ℝ) ^ 5 * x < (b : ℝ) ^ 5 * A + 1 := by
    have := mul_lt_mul_of_pos_left hd2 hB
    rw [mul_sub, mul_inv_cancel₀ hB.ne'] at this; linarith
  have hBx2 : (b : ℝ) ^ 5 * A < (b : ℝ) ^ 5 * x + 1 := by
    have := mul_lt_mul_of_pos_left hd1 hB
    rw [mul_sub, mul_neg, mul_inv_cancel₀ hB.ne'] at this; linarith
  have ha1 : (a : ℝ) ≤ 2 ^ k * ξ := by rwa [div_le_iff₀ hQ, mul_comm] at h1
  have ha2 : 2 ^ k * ξ ≤ (a : ℝ) + 1 := by rwa [le_div_iff₀ hQ, mul_comm] at h2
  refine h A ⟨?_, ?_⟩
  · have key : (a : ℝ) * (b : ℝ) ^ (n + 5) < 2 ^ k * (A * (b : ℝ) ^ 5 + 1) := by
      have e1 : (b : ℝ) ^ (n + 5) = (b : ℝ) ^ n * (b : ℝ) ^ 5 := pow_add _ _ _
      have hP : (0 : ℝ) < (b : ℝ) ^ (n + 5) := by positivity
      calc (a : ℝ) * (b : ℝ) ^ (n + 5) ≤ 2 ^ k * ξ * (b : ℝ) ^ (n + 5) :=
            mul_le_mul_of_nonneg_right ha1 hP.le
        _ = 2 ^ k * ((b : ℝ) ^ 5 * x) := by rw [e1, hx]; ring
        _ < 2 ^ k * ((b : ℝ) ^ 5 * A + 1) := mul_lt_mul_of_pos_left hBx1 hQ
        _ = 2 ^ k * (A * (b : ℝ) ^ 5 + 1) := by ring
    exact_mod_cast key
  · have key : (2 : ℝ) ^ k * (A * (b : ℝ) ^ 5) < (a + 1) * (b : ℝ) ^ (n + 5) + 2 ^ k := by
      have e1 : (b : ℝ) ^ (n + 5) = (b : ℝ) ^ n * (b : ℝ) ^ 5 := pow_add _ _ _
      have hP : (0 : ℝ) < (b : ℝ) ^ (n + 5) := by positivity
      calc (2 : ℝ) ^ k * (A * (b : ℝ) ^ 5) = 2 ^ k * ((b : ℝ) ^ 5 * A) := by ring
        _ < 2 ^ k * ((b : ℝ) ^ 5 * x + 1) := mul_lt_mul_of_pos_left hBx2 hQ
        _ = 2 ^ k * ξ * (b : ℝ) ^ (n + 5) + 2 ^ k := by rw [e1, hx]; ring
        _ ≤ (a + 1) * (b : ℝ) ^ (n + 5) + 2 ^ k := by gcongr
    exact_mod_cast key

theorem base5_of_not_perfPow {b : ℕ} (hb : 3 ≤ b) (hp : ¬ IsPerfPow b) : Base5 b := by
  refine ⟨hb, ?_, ?_, ?_⟩ <;> rintro rfl <;> apply hp
  · exact ⟨2, 2, le_rfl, by norm_num⟩
  · exact ⟨2, 3, by norm_num, by norm_num⟩
  · exact ⟨3, 2, le_rfl, by norm_num⟩

/-- **Exponent `5` is attained (non-strictly) in every base that is not a perfect power.** -/
@[blueprint (title := "A real number with ‖bⁿξ‖ ≥ b^(-5) in every non-perfect-power base")]
theorem exists_good_five :
    ∃ ξ : ℝ, ∀ b : ℕ, 2 ≤ b → ¬ IsPerfPow b → ∀ n : ℕ,
      ((b : ℝ) ^ 5)⁻¹ ≤ dnear ((b : ℝ) ^ n * ξ) := by
  have hpos := cnt_pos bad5 (g := g5) (fun k => lt_of_lt_of_le (by norm_num) (g5_ge k))
    growth_five
  obtain ⟨ξ, hξ⟩ := exists_mem_cells bad5 hpos
  refine ⟨ξ, fun b hb hp n => ?_⟩
  rcases Nat.lt_or_ge b 3 with hb3 | hb3
  · obtain rfl : b = 2 := by omega
    obtain ⟨a, ha, hx⟩ := hξ (n + 5)
    have hnot : ¬ runBad5 (n + 5) a := fun h => ha.2 (Or.inl h)
    simpa using dnear_two_ge5 hx hnot
  · obtain ⟨a, ha, hx⟩ := hξ (L5 b n)
    refine dnear_ge_of_cell5 hb hx fun A hA => ?_
    have hlv := eight_le_L5 hb3 n
    obtain ⟨m, hm⟩ : ∃ m, L5 b n = m + 1 := ⟨L5 b n - 1, by omega⟩
    rw [hm] at ha hA
    exact ha.2 (Or.inr ⟨b, n, A, base5_of_not_perfPow hb3 hp, hm, hA⟩)

end Five

end Count


/-- Every exponent `c > 5` is admissible (`Count.exists_good_five`, `admissible_iff_nonPerfectPow`). -/
theorem admissible_of_five_lt {c : ℝ} (hc : 5 < c) : Admissible c := by
  obtain ⟨ξ, hξ⟩ := Count.exists_good_five
  refine (admissible_iff_nonPerfectPow (by linarith)).2 ⟨ξ, fun b hb hp n => ?_⟩
  refine lt_of_lt_of_le ?_ (hξ b hb hp n)
  have hb1 : (1 : ℝ) < b := by exact_mod_cast (by omega : 1 < b)
  have h1 : (b : ℝ) ^ ((5 : ℕ) : ℝ) < (b : ℝ) ^ c :=
    Real.rpow_lt_rpow_of_exponent_lt hb1 (by exact_mod_cast hc)
  rw [Real.rpow_natCast] at h1
  rw [Real.rpow_neg (by positivity)]
  exact (inv_lt_inv₀ (by positivity) (by positivity)).2 h1

/-- **`c⋆ ≤ 5`** (frozen 2026-10-07, proved 2026-10-07 by `Count.exists_good_five`).  Banked bound
between `cStar_le_six` and the headline `cStar_le_four`.  The proof as formalized differs from the
plan below in the details recorded in the module doc (kill level `L5` for every base with `4`
cells, only `4, 8, 9` excluded, rates `181/100` and `33/20`).

English proof.  Run `Count.growth` with the pruning described in the module doc.  At a level whose
successor carries no base-3 kill, the kills are at most `cnt (k−4) + Σ_{b ≥ 5} 4 cnt (k+1−lag b)`;
bounding each `cnt j` by `cnt k` over the product of the growth rates on `[j, k)`, and each product
from below by the worst count of base-3 kill levels in the window, the kills are at most
`(0.124 + 0.037) cnt k ≤ (2 − 181/100) cnt k`.  At a base-3 kill level the extra term
`4 cnt (k − 6)` adds `0.167 cnt k`, and `0.328 ≤ 2 − 329/200`.  So every level has an alive cell,
the limit point avoids every base-2 run and every window of a base that is not a perfect power,
and `‖bⁿξ‖ ≥ b^{−5}` for all `b ≥ 2` follows from `goodBase_pow`. -/
@[blueprint (title := "Bugeaud 10.36 optimal exponent: c⋆ ≤ 5 by two-rate counting")]
theorem cStar_le_five : cStar ≤ 5 :=
  le_of_forall_gt_imp_ge_of_dense fun _ hc =>
    csInf_le bddBelow_admissible (admissible_of_five_lt hc)

end NormalNumbers.UniformBadThreshold
