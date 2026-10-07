/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Architect
import NormalNumbers.UniformBadCount
import NormalNumbers.UniformBadRoute

/-!
# `c⋆ ≤ 5` by level-dependent counting

The counting engine of `UniformBadCount` (`Count.growth`, which already allows a growth rate `g k`
that depends on the level) at exponent `5`, with three changes against `cStar_le_six`:

* **base `2` exact.**  A cell at level `k + 1 ≥ 6` whose last five binary digits agree has a
  unique charge: its ancestor at level `k − 4` (the other run digit would already have been killed
  one level earlier).  Multiplicity `1`, so the base-2 balance is the run-free recurrence itself.
* **per-window resolution.**  The window of order `n` of base `b` has length `r` cells at its
  resolution level `lv = ⌈log₂ b^{n+5}⌉`, with `r = 2^{lv+1}/b^{n+5} ∈ [2, 4)`.  It is killed at `lv`
  when `r < 3` (at most `4` cells) and one level earlier when `r ≥ 3` (at most `3` cells), and
  charged at lag `⌊log₂(¾ (b⁵ − 2))⌋`.  Perfect powers are dropped (`admissible_iff_nonPerfectPow`).
* **two growth rates.**  `g k = 329/200` when level `k + 1` carries a base-3 kill and `181/100`
  otherwise.  For base `3` the kill levels satisfy `L(n+2) ≥ L(n) + 3` (no two consecutive gaps of
  one), so any `ℓ` consecutive levels hold at most `⌊(2ℓ + 2)/3⌋` of them, and every product of
  growth rates over a charging window is bounded below.

Probe (`scripts/cstar_models/lvl5c.js`, `pess.js`, 2026-10-07): the worst per-level slack of this
scheme is `0.038` along the true kill pattern (`0.028` with every base `b ≥ 5` killing at every
level), and `0.019` with every charging window given its worst count of base-3 kill levels.  With
a single growth rate the scheme fails (best slack `−0.023`), as does charging `5` cells per window
(`−0.011`).  Control: the same pessimistic check at `c = 6` has slack `0.21`, consistent with
`cStar_le_six`.
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

end Five

end Count


/-- **`c⋆ ≤ 5`** (frozen 2026-10-07, believed 90%).  Banked bound between the proved `c⋆ ≤ 6` and
the headline `cStar_le_four`.

English proof.  Run `Count.growth` with the pruning described in the module doc.  At a level whose
successor carries no base-3 kill, the kills are at most `cnt (k−4) + Σ_{b ≥ 5} 4 cnt (k+1−lag b)`;
bounding each `cnt j` by `cnt k` over the product of the growth rates on `[j, k)`, and each product
from below by the worst count of base-3 kill levels in the window, the kills are at most
`(0.124 + 0.037) cnt k ≤ (2 − 181/100) cnt k`.  At a base-3 kill level the extra term
`4 cnt (k − 6)` adds `0.167 cnt k`, and `0.328 ≤ 2 − 329/200`.  So every level has an alive cell,
the limit point avoids every base-2 run and every window of a base that is not a perfect power,
and `‖bⁿξ‖ ≥ b^{−5}` for all `b ≥ 2` follows from `goodBase_pow`. -/
theorem cStar_le_five : cStar ≤ 5 := by
  sorry

end NormalNumbers.UniformBadThreshold
