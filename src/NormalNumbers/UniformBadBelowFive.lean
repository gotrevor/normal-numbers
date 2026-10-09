/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Architect
import NormalNumbers.UniformBadFive

/-!
# `c⋆ ≤ 124/25` by two-rate counting

The `cStar_le_five` engine pushed below exponent `5`, as far as it goes without a new ingredient.
Two changes:

* **base `2` exact at threshold `33/1024`**: besides the runs of five (`runBad5`), the ten-digit
  patterns `0000100000` and `1111011111` are forbidden (`pat10`).  An alive cell then has
  `‖2ⁿξ‖ ≥ 33/1024 > 2^{−124/25}` (`dnear_two_ge4`).  From level `11` on a pattern kill has
  multiplicity `1` over its ancestor at level `k − 9` (`card_patKill4_le_one`): the run digit
  is forced by the parity of that ancestor, since its other value makes a run of five.
* **windows of radius `1/(bⁿ K_b)`** with `K_b^{25} ≤ b^{124}` (`KB`): `K_b = ⌊b^{124/25}⌋` for
  `b < 100` (a bisection, checked by `native_decide`), `K_b = b⁴` for `b ≥ 100`.  Kill level
  `L4 b n` with `3 bⁿ K_b ≤ 4 · 2^L < 6 bⁿ K_b`, at most `4` cells, lag
  `lag4 b = ⌊log₂(3(K_b − 2)/4)⌋` (`lag4 3 = 7`).

The rates are those of `cStar_le_five` (`181/100`, and `33/20` below a base-`3` kill level, with
no three consecutive base-`3` kill levels), so `F5` is reused.  Balance (`card_kill4_le`):
`0.12299 + 0.0116 + 0.04876 ≤ 0.19` and `+ 0.16473 ≤ 0.35`.

Probe: `scripts/cstar_models/gen2.js` (engine slack at real base-`3` positions) and the
exact Lean-pessimistic balance `scripts/cstar_models/bal124.py 33/20`: slack `0.010 / 0.005`.
At `c = 9/2` the same engine fails by about `0.08` (see `UniformBadNineHalves`).
-/

namespace NormalNumbers.UniformBadThreshold

open NormalNumbers.UniformBad (dnear)

namespace Count

section BelowFive

/-- Bisection: starting from `P lo`, the largest `K < hi` with `P K` (for monotone `P`). -/
def bisect (P : ℕ → Bool) : ℕ → ℕ → ℕ → ℕ
  | 0, lo, _ => lo
  | f + 1, lo, hi =>
    if hi ≤ lo + 1 then lo
    else if P ((lo + hi) / 2) then bisect P f ((lo + hi) / 2) hi else bisect P f lo ((lo + hi) / 2)

/-- The window constant `K_b ≤ b^{124/25}`: `⌊b^{124/25}⌋` for `b < 100`, `b⁴` beyond. -/
def KB (b : ℕ) : ℕ :=
  if b < 100 then bisect (fun K => decide (K ^ 25 ≤ b ^ 124)) 64 1 (b ^ 5) else b ^ 4

theorem KB_small : ∀ b ∈ Finset.Ico 3 100, KB b ^ 25 ≤ b ^ 124 ∧ 173 ≤ KB b := by
  native_decide

theorem KB_big {b : ℕ} (hb : 100 ≤ b) : KB b = b ^ 4 := by
  unfold KB; rw [if_neg (by omega)]

theorem KB_pow_le {b : ℕ} (hb : 3 ≤ b) : KB b ^ 25 ≤ b ^ 124 := by
  rcases Nat.lt_or_ge b 100 with h | h
  · exact (KB_small b (Finset.mem_Ico.2 ⟨hb, h⟩)).1
  · rw [KB_big h, ← pow_mul]
    exact Nat.pow_le_pow_right (by omega) (by norm_num)

theorem KB_ge {b : ℕ} (hb : 3 ≤ b) : 173 ≤ KB b := by
  rcases Nat.lt_or_ge b 100 with h | h
  · exact (KB_small b (Finset.mem_Ico.2 ⟨hb, h⟩)).2
  · rw [KB_big h]
    calc 173 ≤ 100 ^ 4 := by norm_num
      _ ≤ b ^ 4 := Nat.pow_le_pow_left h 4

theorem le_KB {b : ℕ} (hb : 3 ≤ b) : b ≤ KB b := by
  rcases Nat.lt_or_ge b 100 with h | h
  · have := KB_ge hb; omega
  · rw [KB_big h]; exact Nat.le_self_pow (by norm_num) b

/-- Base `2`, second pattern: the last ten binary digits are `0000100000` or `1111011111`. -/
def pat10 (k a : ℕ) : Prop := 10 ≤ k ∧ (a % 1024 = 32 ∨ a % 1024 = 991)

/-- The kill level of the base-`b` windows of order `n`. -/
def L4 (b n : ℕ) : ℕ := Nat.clog 2 (3 * (b ^ n * KB b)) - 2

/-- The closed cell `[a/2ᵏ, (a+1)/2ᵏ]` meets the open window of radius `1/(bⁿ K_b)` around
`A/bⁿ`. -/
def meets4 (k a b n A : ℕ) : Prop :=
  a * (b ^ n * KB b) < 2 ^ k * (A * KB b + 1) ∧
    2 ^ k * (A * KB b) < (a + 1) * (b ^ n * KB b) + 2 ^ k

/-- The forbidden cells below exponent `5`. -/
def bad4 (k a : ℕ) : Prop :=
  runBad5 k a ∨ pat10 k a ∨ ∃ b n A, Base5 b ∧ L4 b n = k ∧ meets4 k a b n A

/-- The lag at which base-`b` kills are charged: `4 · 2^{lag} ≤ 3 (K_b − 2)`. -/
def lag4 (b : ℕ) : ℕ := Nat.log 2 (3 * (KB b - 2) / 4)

theorem L4_spec {b n : ℕ} (hb : 3 ≤ b) :
    3 * (b ^ n * KB b) ≤ 4 * 2 ^ L4 b n ∧ 2 * 2 ^ L4 b n < 3 * (b ^ n * KB b) := by
  have hK := KB_ge hb
  have hbn : 1 ≤ b ^ n := Nat.one_le_pow _ _ (by omega)
  set P := b ^ n * KB b with hPdef
  have hP : 32 ≤ P := by
    calc 32 ≤ 1 * KB b := by omega
      _ ≤ P := Nat.mul_le_mul_right _ hbn
  set c := Nat.clog 2 (3 * P) with hc
  have h1 : 3 * P ≤ 2 ^ c := Nat.le_pow_clog (by norm_num) _
  have h2 : 2 ^ c.pred < 3 * P := Nat.pow_pred_clog_lt_self (by norm_num) (by omega)
  have hc2 : 2 ≤ c := by
    by_contra h
    have : 2 ^ c ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  obtain ⟨m, hm⟩ : ∃ m, c = m + 2 := ⟨c - 2, by omega⟩
  have hL : L4 b n = m := by show c - 2 = m; omega
  rw [hL]
  rw [hm, show 2 ^ (m + 2) = 4 * 2 ^ m by ring] at h1
  rw [hm, show (m + 2).pred = m + 1 from rfl, show 2 ^ (m + 1) = 2 * 2 ^ m by ring] at h2
  constructor <;> omega

theorem two_pow_lag4 {b : ℕ} (hb : 3 ≤ b) : 4 * 2 ^ lag4 b ≤ 3 * (KB b - 2) := by
  have hK := KB_ge hb
  have h1 := Nat.pow_log_le_self 2 (show 3 * (KB b - 2) / 4 ≠ 0 by omega)
  have h2 := Nat.div_mul_le_self (3 * (KB b - 2)) 4
  unfold lag4; omega

theorem seven_le_lag4 {b : ℕ} (hb : 3 ≤ b) : 7 ≤ lag4 b := by
  have hK := KB_ge hb
  exact Nat.le_log_of_pow_le (by norm_num) (by omega)

theorem lag4_lt_L4 {b : ℕ} (hb : 3 ≤ b) (n : ℕ) : lag4 b < L4 b n := by
  have h1 := two_pow_lag4 hb
  have hK := KB_ge hb
  have hbn : 1 ≤ b ^ n := Nat.one_le_pow _ _ (by omega)
  have h2 : 1 * KB b ≤ b ^ n * KB b := Nat.mul_le_mul_right _ hbn
  have h3 := (L4_spec (n := n) hb).1
  set P := b ^ n * KB b
  exact (pow_lt_pow_iff_right₀ (by norm_num : 1 < 2)).1 (by omega)

theorem eight_le_L4 {b : ℕ} (hb : 3 ≤ b) (n : ℕ) : 8 ≤ L4 b n := by
  have hK := KB_ge hb
  have hbn : 1 ≤ b ^ n := Nat.one_le_pow _ _ (by omega)
  have h2 : 1 * KB b ≤ b ^ n * KB b := Nat.mul_le_mul_right _ hbn
  have h1 := (L4_spec (n := n) hb).1
  set P := b ^ n * KB b
  have : 2 ^ 7 < 2 ^ L4 b n := by norm_num; omega
  have := (pow_lt_pow_iff_right₀ (by norm_num : 1 < 2)).1 this
  omega

theorem L4_lt_succ {b : ℕ} (hb : 3 ≤ b) (n : ℕ) : L4 b n < L4 b (n + 1) := by
  have h1 := (L4_spec (n := n) hb).2
  have h2 := (L4_spec (n := n + 1) hb).1
  have e : b ^ (n + 1) * KB b = b * (b ^ n * KB b) := by ring
  rw [e] at h2
  have h3 : 2 * (b ^ n * KB b) ≤ b * (b ^ n * KB b) := Nat.mul_le_mul_right _ (by omega)
  set P := b ^ n * KB b
  set Q := b * P
  exact (pow_lt_pow_iff_right₀ (by norm_num : 1 < 2)).1 (by omega)

theorem L4_strictMono {b : ℕ} (hb : 3 ≤ b) : StrictMono (L4 b) :=
  strictMono_nat_of_lt_succ (L4_lt_succ hb)

/-- Base-`3` kill levels: no two consecutive gaps of one. -/
theorem L4_three (n : ℕ) : L4 3 n + 3 ≤ L4 3 (n + 2) := by
  have h1 := (L4_spec (b := 3) (n := n) le_rfl).2
  have h2 := (L4_spec (b := 3) (n := n + 2) le_rfl).1
  have e : (3 : ℕ) ^ (n + 2) * KB 3 = 9 * (3 ^ n * KB 3) := by ring
  rw [e] at h2
  set P := 3 ^ n * KB 3
  have : 2 ^ (L4 3 n + 2) < 2 ^ L4 3 (n + 2) := by rw [pow_add]; omega
  have := (pow_lt_pow_iff_right₀ (by norm_num : 1 < 2)).1 this
  omega

/-- A window met by a cell is met by each of its ancestors. -/
theorem meets4_anc {j D a b n A : ℕ} (h : meets4 (j + D) a b n A) :
    meets4 j (a / 2 ^ D) b n A := by
  obtain ⟨h1, h2⟩ := h
  rw [pow_add 2 j D] at h1 h2
  set q := a / 2 ^ D with hq
  set t := 2 ^ D with ht
  set P := b ^ n * KB b with hP
  have htpos : 0 < t := by positivity
  have hq1 : q * t ≤ a := Nat.div_mul_le_self a t
  have hq2 : a + 1 ≤ (q + 1) * t := by
    have := Nat.div_add_mod a t
    have := Nat.mod_lt a htpos
    nlinarith
  constructor
  · have h3 : q * t * P ≤ a * P := Nat.mul_le_mul_right _ hq1
    have : q * P * t < 2 ^ j * (A * KB b + 1) * t := by nlinarith
    exact Nat.lt_of_mul_lt_mul_right this
  · have h3 : (a + 1) * P ≤ (q + 1) * t * P := Nat.mul_le_mul_right _ hq2
    have : 2 ^ j * (A * KB b) * t < ((q + 1) * P + 2 ^ j) * t := by nlinarith
    exact Nat.lt_of_mul_lt_mul_right this

/-- A cell of level `j` with `bⁿ K_b ≤ 2^j (K_b − 2)` meets at most one window of order `n`. -/
theorem meets4_unique {j b n A A' q : ℕ} (hb : 3 ≤ b) (hPj : b ^ n * KB b ≤ 2 ^ j * (KB b - 2))
    (h : meets4 j q b n A) (h' : meets4 j q b n A') : A = A' := by
  have key : ∀ {A A'}, meets4 j q b n A → meets4 j q b n A' → A < A' → False := by
    intro A A' h h' hlt
    obtain ⟨h1, -⟩ := h
    obtain ⟨-, h2⟩ := h'
    set R := 2 ^ j
    set P := b ^ n * KB b
    set B := KB b
    have hB : 2 ≤ B := by have := KB_ge hb; omega
    have h3 : R * ((A + 1) * B) ≤ R * (A' * B) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hlt)
    have h4 : R * (B - 2) + R * 2 = R * B := by rw [← mul_add, Nat.sub_add_cancel hB]
    nlinarith
  rcases Nat.lt_trichotomy A A' with hlt | heq | hlt
  · exact (key h h' hlt).elim
  · exact heq
  · exact (key h' h hlt).elim

open Classical in
/-- A window spanning fewer than `3` cells meets at most `4` of them. -/
theorem card_meets4_le (k b n A : ℕ) (hk : 2 * 2 ^ k < 3 * (b ^ n * KB b)) :
    ((Finset.range (2 ^ k)).filter (fun a => meets4 k a b n A)).card ≤ 4 := by
  set S := (Finset.range (2 ^ k)).filter (fun a => meets4 k a b n A)
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
    set P := b ^ n * KB b
    have : a * P < (m + 4) * P := by nlinarith
    have := Nat.lt_of_mul_lt_mul_right this
    omega
  calc S.card ≤ (Finset.Icc m (m + 3)).card := Finset.card_le_card hsub
    _ = 4 := by rw [Nat.card_Icc]; omega

/-! ### Charging -/

/-- An alive cell at level `m + 1` is not killed there. -/
theorem not_bad4_of_alive {m x : ℕ} (h : Alive bad4 (m + 1) x) : ¬ bad4 (m + 1) x := h.2

open Classical in
/-- Base-`2` run kills at level `k + 1`, charged to the ancestor at level `k − 4`. -/
theorem card_runKill4_le_two (k : ℕ) (h4 : 4 ≤ k) :
    ((Finset.range (2 ^ (k + 1))).filter
      (fun a => Alive bad4 k (a / 2) ∧ runBad5 (k + 1) a)).card ≤ 2 * cnt bad4 (k - 4) := by
  refine card_le_of_charge bad4 _ (fun a => a / 32) (k - 4) 2 (fun a ha => ?_) fun q => ?_
  · have ha := (Finset.mem_filter.1 ha).2.1
    have e : k = (k - 4) + 4 := by omega
    rw [e] at ha
    have := alive_anc bad4 4 ha
    rwa [Nat.div_div_eq_div_mul] at this
  · calc _ ≤ ({32 * q, 32 * q + 31} : Finset ℕ).card := by
          refine Finset.card_le_card fun a ha => ?_
          obtain ⟨ha', hq⟩ := Finset.mem_filter.1 ha
          obtain ⟨-, -, -, h⟩ := Finset.mem_filter.1 ha'
          simp only [Finset.mem_insert, Finset.mem_singleton]
          omega
      _ ≤ 2 := Finset.card_le_two

open Classical in
/-- From level `6` on the run charge is exact. -/
theorem card_runKill4_le_one (k : ℕ) (h5 : 5 ≤ k) :
    ((Finset.range (2 ^ (k + 1))).filter
      (fun a => Alive bad4 k (a / 2) ∧ runBad5 (k + 1) a)).card ≤ 1 * cnt bad4 (k - 4) := by
  refine card_le_of_charge bad4 _ (fun a => a / 32) (k - 4) 1 (fun a ha => ?_) fun q => ?_
  · have ha := (Finset.mem_filter.1 ha).2.1
    have e : k = (k - 4) + 4 := by omega
    rw [e] at ha
    have := alive_anc bad4 4 ha
    rwa [Nat.div_div_eq_div_mul] at this
  · have hnr : ∀ a, Alive bad4 k (a / 2) → ¬ runBad5 k (a / 2) := by
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
/-- Pattern kills at level `k + 1`, charged to the ancestor at level `k − 9` (multiplicity `2`). -/
theorem card_patKill4_le_two (k : ℕ) (h9 : 9 ≤ k) :
    ((Finset.range (2 ^ (k + 1))).filter
      (fun a => Alive bad4 k (a / 2) ∧ pat10 (k + 1) a)).card ≤ 2 * cnt bad4 (k - 9) := by
  refine card_le_of_charge bad4 _ (fun a => a / 1024) (k - 9) 2 (fun a ha => ?_) fun q => ?_
  · have ha := (Finset.mem_filter.1 ha).2.1
    have e : k = (k - 9) + 9 := by omega
    rw [e] at ha
    have := alive_anc bad4 9 ha
    rwa [Nat.div_div_eq_div_mul] at this
  · calc _ ≤ ({1024 * q + 32, 1024 * q + 991} : Finset ℕ).card := by
          refine Finset.card_le_card fun a ha => ?_
          obtain ⟨ha', hq⟩ := Finset.mem_filter.1 ha
          obtain ⟨-, -, -, h⟩ := Finset.mem_filter.1 ha'
          simp only [Finset.mem_insert, Finset.mem_singleton]
          omega
      _ ≤ 2 := Finset.card_le_two

open Classical in
/-- From level `11` on the pattern charge is exact: the ancestor at level `k − 5` is alive, so
it is not a run of five, and that fixes which of the two patterns can occur. -/
theorem card_patKill4_le_one (k : ℕ) (h10 : 10 ≤ k) :
    ((Finset.range (2 ^ (k + 1))).filter
      (fun a => Alive bad4 k (a / 2) ∧ pat10 (k + 1) a)).card ≤ 1 * cnt bad4 (k - 9) := by
  refine card_le_of_charge bad4 _ (fun a => a / 1024) (k - 9) 1 (fun a ha => ?_) fun q => ?_
  · have ha := (Finset.mem_filter.1 ha).2.1
    have e : k = (k - 9) + 9 := by omega
    rw [e] at ha
    have := alive_anc bad4 9 ha
    rwa [Nat.div_div_eq_div_mul] at this
  · have hnr : ∀ a, Alive bad4 k (a / 2) → ¬ runBad5 (k - 5) (a / 64) := by
      intro a h hr
      have e : k = (k - 5) + 5 := by omega
      rw [e] at h
      have h' := alive_anc bad4 5 h
      rw [Nat.div_div_eq_div_mul] at h'
      obtain ⟨m, hm⟩ : ∃ m, k - 5 = m + 1 := ⟨k - 6, by omega⟩
      rw [hm] at h' hr
      exact h'.2 (Or.inl hr)
    refine Finset.card_le_one.2 fun a ha a' ha' => ?_
    obtain ⟨ha1, hq⟩ := Finset.mem_filter.1 ha
    obtain ⟨-, hal, hr⟩ := Finset.mem_filter.1 ha1
    obtain ⟨ha1', hq'⟩ := Finset.mem_filter.1 ha'
    obtain ⟨-, hal', hr'⟩ := Finset.mem_filter.1 ha1'
    have n1 := hnr a hal
    have n2 := hnr a' hal'
    simp only [runBad5, pat10] at n1 n2 hr hr'
    omega

open Classical in
/-- Base-`b` kills at level `k + 1`, charged to the ancestor at lag `lag4 b` (multiplicity `4`). -/
theorem card_winKill4_le (k b : ℕ) (hb : 3 ≤ b) :
    ((Finset.range (2 ^ (k + 1))).filter
      (fun a => Alive bad4 k (a / 2) ∧ ∃ n A, L4 b n = k + 1 ∧ meets4 (k + 1) a b n A)).card ≤
      4 * cnt bad4 (k + 1 - lag4 b) := by
  set S := (Finset.range (2 ^ (k + 1))).filter
      (fun a => Alive bad4 k (a / 2) ∧ ∃ n A, L4 b n = k + 1 ∧ meets4 (k + 1) a b n A)
  rcases S.eq_empty_or_nonempty with hS | ⟨a₀, ha₀⟩
  · rw [hS]; simp
  obtain ⟨-, -, n₀, A₀, hn₀, hA₀⟩ := Finset.mem_filter.1 ha₀
  have hlag := lag4_lt_L4 hb n₀
  have hlag1 := seven_le_lag4 hb
  rw [hn₀] at hlag
  set j := k + 1 - lag4 b with hj
  have ejk : k + 1 = j + lag4 b := by omega
  refine card_le_of_charge bad4 S (fun a => a / 2 ^ lag4 b) j 4 (fun a ha => ?_) fun q => ?_
  · have ha := (Finset.mem_filter.1 ha).2.1
    have e : k = j + (lag4 b - 1) := by omega
    rw [e] at ha
    have := alive_anc bad4 (lag4 b - 1) ha
    rwa [Nat.div_div_eq_div_mul, ← pow_succ', show lag4 b - 1 + 1 = lag4 b by omega] at this
  · rcases (S.filter fun a => a / 2 ^ lag4 b = q).eq_empty_or_nonempty with hF | ⟨a₁, ha₁⟩
    · rw [hF]; simp
    obtain ⟨ha₁S, hq₁⟩ := Finset.mem_filter.1 ha₁
    obtain ⟨-, -, n₁, A₁, hn₁, hA₁⟩ := Finset.mem_filter.1 ha₁S
    have hPj : b ^ n₁ * KB b ≤ 2 ^ j * (KB b - 2) := by
      have h1 := (L4_spec (n := n₁) hb).1
      rw [hn₁, ejk, pow_add 2 j] at h1
      have h2 : 4 * 2 ^ lag4 b * 2 ^ j ≤ 3 * (KB b - 2) * 2 ^ j :=
        Nat.mul_le_mul_right _ (two_pow_lag4 hb)
      have : 3 * (b ^ n₁ * KB b) ≤ 3 * (2 ^ j * (KB b - 2)) := by
        calc 3 * (b ^ n₁ * KB b) ≤ 4 * (2 ^ j * 2 ^ lag4 b) := h1
          _ = 4 * 2 ^ lag4 b * 2 ^ j := by ring
          _ ≤ 3 * (KB b - 2) * 2 ^ j := h2
          _ = 3 * (2 ^ j * (KB b - 2)) := by ring
      omega
    have hsub : S.filter (fun a => a / 2 ^ lag4 b = q) ⊆
        (Finset.range (2 ^ (k + 1))).filter (fun a => meets4 (k + 1) a b n₁ A₁) := by
      intro a ha
      obtain ⟨haS, hq⟩ := Finset.mem_filter.1 ha
      obtain ⟨hr, -, n, A, hn, hA⟩ := Finset.mem_filter.1 haS
      have hnn : n = n₁ := (L4_strictMono hb).injective (hn.trans hn₁.symm)
      subst hnn
      have m1 : meets4 j q b n A := by
        rw [ejk] at hA; have := meets4_anc hA; rwa [hq] at this
      have m2 : meets4 j q b n A₁ := by
        rw [ejk] at hA₁; have := meets4_anc hA₁; rwa [hq₁] at this
      have hAA := meets4_unique hb hPj m1 m2
      subst hAA
      exact Finset.mem_filter.2 ⟨hr, hA⟩
    exact (Finset.card_le_card hsub).trans
      (card_meets4_le (k + 1) b n₁ A₁ (hn₁ ▸ (L4_spec hb).2))

open Classical in
theorem killSet4_subset (k : ℕ) :
    killSet bad4 k ⊆ (((Finset.range (2 ^ (k + 1))).filter
        (fun a => Alive bad4 k (a / 2) ∧ runBad5 (k + 1) a)) ∪
      ((Finset.range (2 ^ (k + 1))).filter
        (fun a => Alive bad4 k (a / 2) ∧ pat10 (k + 1) a))) ∪
      (Finset.Ioc 2 (2 ^ (k + 3))).biUnion (fun b => (Finset.range (2 ^ (k + 1))).filter
        (fun a => Alive bad4 k (a / 2) ∧ Base5 b ∧
          ∃ n A, L4 b n = k + 1 ∧ meets4 (k + 1) a b n A)) := by
  intro a ha
  have hr : a ∈ Finset.range (2 ^ (k + 1)) := (Finset.mem_filter.1 ha).1
  obtain ⟨hal, hbad⟩ := (mem_killSet bad4).1 ha
  rcases hbad with hrun | hpat | ⟨b, n, A, hb, hn, hm⟩
  · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_filter.2 ⟨hr, hal, hrun⟩))
  · exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_filter.2 ⟨hr, hal, hpat⟩))
  · refine Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨b, Finset.mem_Ioc.2 ⟨hb.1, ?_⟩,
      Finset.mem_filter.2 ⟨hr, hal, hb, n, A, hn, hm⟩⟩)
    have h1 := (L4_spec (n := n) hb.1).1
    rw [hn] at h1
    have hbn : 1 ≤ b ^ n := Nat.one_le_pow _ _ (by have := hb.1; omega)
    have h2 : 1 * KB b ≤ b ^ n * KB b := Nat.mul_le_mul_right _ hbn
    have h3 := le_KB hb.1
    have e : 2 ^ (k + 3) = 4 * 2 ^ (k + 1) := by rw [pow_add 2 (k + 1) 2]; ring_nf
    set P := b ^ n * KB b
    omega

/-! ### Two growth rates -/

/-- Level `m` carries a base-`3` kill. -/
def K3' (m : ℕ) : Prop := ∃ n, L4 3 n = m

theorem no_three4 (m : ℕ) : K3' m → K3' (m + 1) → K3' (m + 2) → False := by
  rintro ⟨n1, h1⟩ ⟨n2, h2⟩ ⟨n3, h3⟩
  have hs := L4_strictMono (b := 3) le_rfl
  have a12 : n1 < n2 := hs.lt_iff_lt.1 (by omega)
  have a23 : n2 < n3 := hs.lt_iff_lt.1 (by omega)
  have := L4_three n1
  have := hs.monotone (show n1 + 2 ≤ n3 by omega)
  omega

open Classical in
/-- The growth rate below level `k + 1`: `33/20` before a base-`3` kill level, else `181/100`. -/
noncomputable def g4 (k : ℕ) : ℝ := if K3' (k + 1) then 33 / 20 else 181 / 100

theorem g4_ge (k : ℕ) : (33 / 20 : ℝ) ≤ g4 k := by
  unfold g4; split_ifs <;> norm_num

theorem triple4_ge (j : ℕ) :
    (181 / 100 * (33 / 20) ^ 2 : ℝ) ≤ g4 j * g4 (j + 1) * g4 (j + 2) := by
  unfold g4
  split_ifs with h1 h2 h3 <;> try norm_num
  exact no_three4 _ h1 h2 h3

theorem prod_g4_ge : ∀ d j : ℕ, ((F5 d : ℚ) : ℝ) ≤ ∏ i ∈ Finset.Ico j (j + d), g4 i := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    intro j
    rw [F5_cast]
    rcases Nat.lt_or_ge d 3 with hd | hd
    · rw [Nat.div_eq_of_lt hd, Nat.mod_eq_of_lt hd, pow_zero, one_mul]
      calc (33 / 20 : ℝ) ^ d = ∏ _i ∈ Finset.Ico j (j + d), (33 / 20 : ℝ) := by
            rw [Finset.prod_const, Nat.card_Ico]; congr 1; omega
        _ ≤ _ := Finset.prod_le_prod (fun _ _ => by norm_num) fun i _ => g4_ge i
    · have h := ih (d - 3) (by omega) (j + 3)
      rw [F5_cast, show j + 3 + (d - 3) = j + d by omega] at h
      rw [← Finset.prod_Ico_consecutive _ (show j ≤ j + 3 by omega) (show j + 3 ≤ j + d by omega)]
      have e3 : ∏ i ∈ Finset.Ico j (j + 3), g4 i = g4 j * g4 (j + 1) * g4 (j + 2) := by
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
        _ ≤ (g4 j * g4 (j + 1) * g4 (j + 2)) * ∏ i ∈ Finset.Ico (j + 3) (j + d), g4 i :=
            mul_le_mul (triple4_ge j) h h0 (by
              have := g4_ge j; have := g4_ge (j + 1); have := g4_ge (j + 2); positivity)

/-! ### The base series -/

/-- The charge weight of a base `b ≥ 4`. -/
def w4 (b : ℕ) : ℚ := if b = 4 ∨ b = 8 ∨ b = 9 then 0 else 4 / F5 (lag4 b - 1)

/-- The explicit bases `4 ≤ b ≤ 99`. -/
theorem sum_w4_small : ∑ b ∈ Finset.Ioc 3 99, w4 b ≤ 4661 / 100000 := by
  native_decide

theorem w4_nonneg (b : ℕ) : (0 : ℝ) ≤ ((w4 b : ℚ) : ℝ) := by
  unfold w4; split_ifs
  · simp
  · have := F5_pos (lag4 b - 1); push_cast; positivity

/-- For `b ≥ 100`, `w4 b ≤ 4 · (1156/1089) · (1/20) / (b (b − 1))`. -/
theorem w4_tail {b : ℕ} (hb : 100 ≤ b) :
    ((w4 b : ℚ) : ℝ) ≤ 4 * (1156 / 1089) * (1 / 20) * (1 / ((b : ℝ) * ((b : ℝ) - 1))) := by
  have hb3 : 3 ≤ b := by omega
  have hl7 := seven_le_lag4 hb3
  set l := lag4 b - 1 with hl
  -- `b⁴ < 2^{l + 3}`
  have hb4 : b ^ 4 < 2 ^ (l + 3) := by
    have hK := KB_big hb
    have hK2 := KB_ge hb3
    have h4 : 100 ^ 4 ≤ b ^ 4 := Nat.pow_le_pow_left hb 4
    set s := Nat.log 2 (3 * (KB b - 2) / 4) with hs
    have h1 := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) (3 * (KB b - 2) / 4)
    rw [← hs] at h1
    have h2 : 3 * (KB b - 2) < 4 * 2 ^ s.succ := by
      have := (Nat.div_lt_iff_lt_mul (by norm_num : 0 < 4)).1 h1; omega
    have e : l + 3 = s.succ + 1 := by
      simp only [hl, lag4] at hl7 ⊢; omega
    have hp : 2 ≤ 2 ^ s.succ := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ _ := Nat.pow_le_pow_right (by norm_num) (by omega)
    have hKs : KB b - 2 + 2 = KB b := Nat.sub_add_cancel (by omega)
    rw [e, pow_succ (2 : ℕ)]
    set T := 2 ^ s.succ
    set B4 := b ^ 4
    omega
  have hbR : (100 : ℝ) ≤ b := by exact_mod_cast hb
  have hb4R : (b : ℝ) ^ 4 < 2 ^ (l + 3) := by exact_mod_cast hb4
  -- the weight
  have hw : ((w4 b : ℚ) : ℝ) ≤ 4 * (1156 / 1089) * ((10 : ℝ) / 17) ^ l := by
    have hF := F5_ge l
    have hFR : (1089 / 1156 : ℝ) * (17 / 10) ^ l ≤ ((F5 l : ℚ) : ℝ) := by
      have := (Rat.cast_le (K := ℝ)).2 hF; push_cast at this; exact this
    have hpos : (0 : ℝ) < (1089 / 1156 : ℝ) * (17 / 10) ^ l := by positivity
    have hw' : ((w4 b : ℚ) : ℝ) ≤ 4 / ((F5 l : ℚ) : ℝ) := by
      unfold w4
      split_ifs
      · simp only [Rat.cast_zero]; have := F5_pos l; positivity
      · push_cast [hl]; exact le_rfl
    calc ((w4 b : ℚ) : ℝ) ≤ 4 / ((F5 l : ℚ) : ℝ) := hw'
      _ ≤ 4 / ((1089 / 1156 : ℝ) * (17 / 10) ^ l) := by gcongr
      _ = 4 * (1156 / 1089) * ((10 : ℝ) / 17) ^ l := by
          rw [show ((10 : ℝ) / 17) = (17 / 10)⁻¹ by norm_num, inv_pow]; field_simp
  -- `b (b − 1) (10/17)^l ≤ 1/20`
  have hbb : 0 < (b : ℝ) * ((b : ℝ) - 1) := by nlinarith
  set x := (b : ℝ) * ((b : ℝ) - 1) * ((10 : ℝ) / 17) ^ l with hx
  have hx0 : 0 ≤ x := by positivity
  have hy : ((10 : ℝ) / 17) ^ (4 * l) ≤ ((1 : ℝ) / 8) ^ l := by
    rw [pow_mul]; exact pow_le_pow_left₀ (by norm_num) (by norm_num) _
  have h8 : ((1 : ℝ) / 8) ^ l * (b : ℝ) ^ 12 ≤ 512 := by
    have : (b : ℝ) ^ 12 ≤ (8 : ℝ) ^ l * 512 := by
      have h1 : (b : ℝ) ^ 12 = ((b : ℝ) ^ 4) ^ 3 := by ring
      have h2 : ((2 : ℝ) ^ (l + 3)) ^ 3 = (8 : ℝ) ^ l * 512 := by
        rw [← pow_mul, show (l + 3) * 3 = 3 * l + 9 by ring, pow_add, pow_mul]; norm_num
      rw [h1, ← h2]; gcongr
    calc ((1 : ℝ) / 8) ^ l * (b : ℝ) ^ 12 ≤ ((1 : ℝ) / 8) ^ l * ((8 : ℝ) ^ l * 512) := by gcongr
      _ = 512 := by rw [← mul_assoc, ← mul_pow]; norm_num
  have hx4 : x ^ 4 ≤ (1 / 20 : ℝ) ^ 4 := by
    have h1 : ((b : ℝ) * ((b : ℝ) - 1)) ^ 4 ≤ (b : ℝ) ^ 8 := by
      have : (b : ℝ) * ((b : ℝ) - 1) ≤ (b : ℝ) ^ 2 := by nlinarith
      calc ((b : ℝ) * ((b : ℝ) - 1)) ^ 4 ≤ ((b : ℝ) ^ 2) ^ 4 := by gcongr
        _ = (b : ℝ) ^ 8 := by ring
    have h7 : (100 : ℝ) ^ 4 ≤ (b : ℝ) ^ 4 := by gcongr
    have : x ^ 4 * (b : ℝ) ^ 4 ≤ 512 := by
      calc x ^ 4 * (b : ℝ) ^ 4
          = ((b : ℝ) * ((b : ℝ) - 1)) ^ 4 * ((10 : ℝ) / 17) ^ (4 * l) * (b : ℝ) ^ 4 := by
            rw [hx, mul_pow, ← pow_mul, mul_comm l 4]
        _ ≤ (b : ℝ) ^ 8 * ((1 : ℝ) / 8) ^ l * (b : ℝ) ^ 4 := by gcongr
        _ = ((1 : ℝ) / 8) ^ l * (b : ℝ) ^ 12 := by ring
        _ ≤ 512 := h8
    have h30 : x ^ 4 * (100 : ℝ) ^ 4 ≤ 512 :=
      le_trans (mul_le_mul_of_nonneg_left h7 (by positivity)) this
    nlinarith
  have hx1 : x ≤ 1 / 20 := le_of_pow_le_pow_left₀ (by norm_num) (by norm_num) hx4
  calc ((w4 b : ℚ) : ℝ) ≤ 4 * (1156 / 1089) * ((10 : ℝ) / 17) ^ l := hw
    _ = 4 * (1156 / 1089) * x * (1 / ((b : ℝ) * ((b : ℝ) - 1))) := by
        have hb1 : (b : ℝ) - 1 ≠ 0 := by linarith
        have hb0 : (b : ℝ) ≠ 0 := by linarith
        rw [hx]; field_simp
    _ ≤ 4 * (1156 / 1089) * (1 / 20) * (1 / ((b : ℝ) * ((b : ℝ) - 1))) := by gcongr

/-- **The base series.**  `Σ_{4 ≤ b ≤ M} w4 b ≤ 4876/100000`. -/
theorem sum_w4_le (M : ℕ) : ∑ b ∈ Finset.Ioc 3 M, ((w4 b : ℚ) : ℝ) ≤ 4876 / 100000 := by
  set f : ℕ → ℝ := fun b => ((w4 b : ℚ) : ℝ) with hf
  have hf0 : ∀ b, 0 ≤ f b := fun b => w4_nonneg b
  have hsmall : ∑ b ∈ Finset.Ioc 3 99, f b ≤ 4661 / 100000 := by
    have := sum_w4_small
    have h : ((∑ b ∈ Finset.Ioc 3 99, w4 b : ℚ) : ℝ) ≤ ((4661 / 100000 : ℚ) : ℝ) := by
      exact_mod_cast this
    push_cast at h; simpa [hf] using h
  have htail : ∀ N, 99 ≤ N →
      ∑ b ∈ Finset.Ioc 99 N, f b ≤ 4 * (1156 / 1089) * (1 / 20) * (1 / 99) := by
    intro N hN
    calc ∑ b ∈ Finset.Ioc 99 N, f b
        ≤ ∑ b ∈ Finset.Ioc 99 N, 4 * (1156 / 1089) * (1 / 20) * (1 / ((b : ℝ) * ((b : ℝ) - 1))) :=
          Finset.sum_le_sum fun b hb => w4_tail (by have := (Finset.mem_Ioc.1 hb).1; omega)
      _ = 4 * (1156 / 1089) * (1 / 20) * (1 / 99 - 1 / N) := by
          rw [← Finset.mul_sum, telescope5 99 (by norm_num) N hN]; norm_num
      _ ≤ 4 * (1156 / 1089) * (1 / 20) * (1 / 99) := by
          have : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
          gcongr; linarith [one_div_pos.2 this]
  calc ∑ b ∈ Finset.Ioc 3 M, f b ≤ ∑ b ∈ Finset.Ioc 3 (M + 99), f b :=
        Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.Ioc_subset_Ioc_right (by omega)) fun b _ _ => hf0 b
    _ = ∑ b ∈ Finset.Ioc 3 99, f b + ∑ b ∈ Finset.Ioc 99 (M + 99), f b :=
        (Finset.sum_Ioc_consecutive f (by norm_num) (by omega)).symm
    _ ≤ _ := add_le_add hsmall (htail _ (by omega))
    _ ≤ 4876 / 100000 := by norm_num

theorem lag4_three : lag4 3 = 7 := by native_decide

theorem not_K3'_lt {m : ℕ} (h : m < 8) : ¬ K3' m := by
  rintro ⟨n, hn⟩; have := eight_le_L4 (b := 3) le_rfl n; omega

/-! ### The per-level balance -/

open Classical in
/-- **Per-level kill bound** below exponent `5`. -/
theorem card_kill4_le (k : ℕ)
    (hch : ∀ j ≤ k, (cnt bad4 j : ℝ) * ∏ i ∈ Finset.Ico j k, g4 i ≤ cnt bad4 k) :
    ((killSet bad4 k).card : ℝ) ≤ (2 - g4 k) * cnt bad4 k := by
  have hF : ∀ j ≤ k, (cnt bad4 j : ℝ) * ((F5 (k - j) : ℚ) : ℝ) ≤ cnt bad4 k := by
    intro j hj
    have h := prod_g4_ge (k - j) j
    rw [show j + (k - j) = k by omega] at h
    exact le_trans (mul_le_mul_of_nonneg_left h (by positivity)) (hch j hj)
  have hck : (0 : ℝ) ≤ cnt bad4 k := by positivity
  have hcard := (Finset.card_le_card (killSet4_subset k)).trans (Finset.card_union_le _ _)
  have hcard' := hcard.trans (Nat.add_le_add (Finset.card_union_le _ _) Finset.card_biUnion_le)
  have hK : ((killSet bad4 k).card : ℝ) ≤
      (((Finset.range (2 ^ (k + 1))).filter
        (fun a => Alive bad4 k (a / 2) ∧ runBad5 (k + 1) a)).card : ℝ) +
      (((Finset.range (2 ^ (k + 1))).filter
        (fun a => Alive bad4 k (a / 2) ∧ pat10 (k + 1) a)).card : ℝ) +
      ∑ b ∈ Finset.Ioc 2 (2 ^ (k + 3)), (((Finset.range (2 ^ (k + 1))).filter
        (fun a => Alive bad4 k (a / 2) ∧ Base5 b ∧
          ∃ n A, L4 b n = k + 1 ∧ meets4 (k + 1) a b n A)).card : ℝ) := by
    exact_mod_cast hcard'
  -- no window kills below level `8`
  have hW0 : k + 1 < 8 → ∀ b, ((Finset.range (2 ^ (k + 1))).filter
        (fun a => Alive bad4 k (a / 2) ∧ Base5 b ∧
          ∃ n A, L4 b n = k + 1 ∧ meets4 (k + 1) a b n A)) = ∅ := by
    intro hk b
    refine Finset.filter_eq_empty_iff.2 fun a _ h => ?_
    obtain ⟨-, hb, n, A, hn, -⟩ := h
    have := eight_le_L4 hb.1 n
    omega
  -- no pattern kills below level `10`
  have hP0 : k + 1 < 10 → (Finset.range (2 ^ (k + 1))).filter
        (fun a => Alive bad4 k (a / 2) ∧ pat10 (k + 1) a) = ∅ := by
    intro hk
    exact Finset.filter_eq_empty_iff.2 fun a _ h => by have := h.2.1; omega
  rcases Nat.lt_or_ge k 5 with hk5 | hk5
  · -- levels `≤ 5`: only the base-`2` kills at level `5`
    simp only [hW0 (by omega), hP0 (by omega), Finset.card_empty, Nat.cast_zero,
      Finset.sum_const_zero, add_zero] at hK
    have hg : g4 k = 181 / 100 := by
      unfold g4; rw [if_neg (not_K3'_lt (by omega))]
    rw [hg]
    rcases Nat.lt_or_ge k 4 with hk4 | hk4
    · have : (Finset.range (2 ^ (k + 1))).filter
          (fun a => Alive bad4 k (a / 2) ∧ runBad5 (k + 1) a) = ∅ :=
        Finset.filter_eq_empty_iff.2 fun a _ h => by have := h.2.1; omega
      rw [this] at hK
      simp only [Finset.card_empty, Nat.cast_zero] at hK
      nlinarith
    · obtain rfl : k = 4 := by omega
      have h1 := (Nat.cast_le (α := ℝ)).2 (card_runKill4_le_two 4 le_rfl)
      push_cast at h1
      have h2 := hch 0 (by norm_num)
      have hp : ∏ i ∈ Finset.Ico 0 4, g4 i = (181 / 100 : ℝ) ^ 4 := by
        have : ∀ i ∈ Finset.Ico 0 4, g4 i = 181 / 100 := fun i hi => by
          have := (Finset.mem_Ico.1 hi).2
          unfold g4; rw [if_neg (not_K3'_lt (by omega))]
        rw [Finset.prod_congr rfl this, Finset.prod_const]; simp
      rw [hp] at h2
      norm_num at h1 h2 ⊢
      linarith
  · -- runs
    have hrun : (((Finset.range (2 ^ (k + 1))).filter
        (fun a => Alive bad4 k (a / 2) ∧ runBad5 (k + 1) a)).card : ℝ) ≤ cnt bad4 (k - 4) := by
      have h1 := (Nat.cast_le (α := ℝ)).2 (card_runKill4_le_one k hk5)
      push_cast at h1; linarith
    have hr4 := hF (k - 4) (by omega)
    rw [show k - (k - 4) = 4 by omega] at hr4
    have e4 : ((F5 4 : ℚ) : ℝ) = 181 / 100 * (33 / 20) ^ 3 := by norm_num [F5]
    rw [e4] at hr4
    -- patterns
    have hpat : (((Finset.range (2 ^ (k + 1))).filter
        (fun a => Alive bad4 k (a / 2) ∧ pat10 (k + 1) a)).card : ℝ) ≤
        116 / 10000 * cnt bad4 k := by
      rcases Nat.lt_or_ge k 9 with hk9 | hk9
      · rw [hP0 (by omega), Finset.card_empty, Nat.cast_zero]; positivity
      rcases Nat.lt_or_ge k 10 with hk10 | hk10
      · obtain rfl : k = 9 := by omega
        have h1 := card_patKill4_le_two 9 le_rfl
        rw [show 9 - 9 = 0 from rfl, cnt_zero] at h1
        have h1r : (((Finset.range (2 ^ (9 + 1))).filter
            (fun a => Alive bad4 9 (a / 2) ∧ pat10 (9 + 1) a)).card : ℝ) ≤ 2 := by
          exact_mod_cast h1
        have h2 := hch 0 (by norm_num)
        rw [cnt_zero] at h2
        have hp : (181 / 100 : ℝ) ^ 7 * (33 / 20) ^ 2 ≤ ∏ i ∈ Finset.Ico 0 9, g4 i := by
          rw [← Finset.prod_Ico_consecutive _ (show 0 ≤ 7 by norm_num) (show 7 ≤ 9 by norm_num)]
          have ha : ∏ i ∈ Finset.Ico 0 7, g4 i = (181 / 100 : ℝ) ^ 7 := by
            have : ∀ i ∈ Finset.Ico 0 7, g4 i = 181 / 100 := fun i hi => by
              have := (Finset.mem_Ico.1 hi).2
              unfold g4; rw [if_neg (not_K3'_lt (by omega))]
            rw [Finset.prod_congr rfl this, Finset.prod_const]; simp
          have hb : (33 / 20 : ℝ) ^ 2 ≤ ∏ i ∈ Finset.Ico 7 9, g4 i := by
            rw [show Finset.Ico 7 9 = {7, 8} by decide, Finset.prod_pair (by norm_num), sq]
            exact mul_le_mul (g4_ge 7) (g4_ge 8) (by norm_num) (by linarith [g4_ge 7])
          rw [ha]; exact mul_le_mul_of_nonneg_left hb (by positivity)
        have h3 : (181 / 100 : ℝ) ^ 7 * (33 / 20) ^ 2 ≤ cnt bad4 9 := by
          simp only [Nat.cast_one, one_mul] at h2; linarith
        have h4 : (2 : ℝ) ≤ 116 / 10000 * ((181 / 100 : ℝ) ^ 7 * (33 / 20) ^ 2) := by norm_num
        linarith
      · have h1 := (Nat.cast_le (α := ℝ)).2 (card_patKill4_le_one k hk10)
        push_cast at h1
        have h2 := hF (k - 9) (by omega)
        rw [show k - (k - 9) = 9 by omega] at h2
        have e9 : ((F5 9 : ℚ) : ℝ) = (181 / 100 * (33 / 20) ^ 2) ^ 3 := by norm_num [F5]
        rw [e9] at h2
        have hc9 : (0 : ℝ) ≤ cnt bad4 (k - 9) := by positivity
        norm_num at h2
        nlinarith
    -- windows
    set v : ℕ → ℝ := fun b => if b = 3 then (if K3' (k + 1) then 4 / ((F5 6 : ℚ) : ℝ) else 0)
      else ((w4 b : ℚ) : ℝ) with hv
    have hwin : ∀ b ∈ Finset.Ioc 2 (2 ^ (k + 3)), (((Finset.range (2 ^ (k + 1))).filter
        (fun a => Alive bad4 k (a / 2) ∧ Base5 b ∧
          ∃ n A, L4 b n = k + 1 ∧ meets4 (k + 1) a b n A)).card : ℝ) ≤ v b * cnt bad4 k := by
      intro b _
      set S := (Finset.range (2 ^ (k + 1))).filter
        (fun a => Alive bad4 k (a / 2) ∧ Base5 b ∧ ∃ n A, L4 b n = k + 1 ∧ meets4 (k + 1) a b n A)
      rcases S.eq_empty_or_nonempty with hS | ⟨a₀, ha₀⟩
      · rw [hS, Finset.card_empty, Nat.cast_zero]
        have : 0 ≤ v b := by
          simp only [hv]; split_ifs
          · have := F5_pos 6; positivity
          · exact le_rfl
          · exact w4_nonneg b
        positivity
      obtain ⟨-, -, hB, n₀, A₀, hn₀, -⟩ := Finset.mem_filter.1 ha₀
      have hlag := lag4_lt_L4 hB.1 n₀
      have hlag7 := seven_le_lag4 hB.1
      rw [hn₀] at hlag
      have hsub : S ⊆ (Finset.range (2 ^ (k + 1))).filter
          (fun a => Alive bad4 k (a / 2) ∧ ∃ n A, L4 b n = k + 1 ∧ meets4 (k + 1) a b n A) := by
        intro a ha
        obtain ⟨hr, hal, -, h⟩ := Finset.mem_filter.1 ha
        exact Finset.mem_filter.2 ⟨hr, hal, h⟩
      have h1 := (Nat.cast_le (α := ℝ)).2
        ((Finset.card_le_card hsub).trans (card_winKill4_le k b hB.1))
      push_cast at h1
      have h2 := hF (k + 1 - lag4 b) (by omega)
      rw [show k - (k + 1 - lag4 b) = lag4 b - 1 by omega] at h2
      have hFp : (0 : ℝ) < ((F5 (lag4 b - 1) : ℚ) : ℝ) := by exact_mod_cast F5_pos _
      have h3 : 4 * (cnt bad4 (k + 1 - lag4 b) : ℝ) ≤
          4 / ((F5 (lag4 b - 1) : ℚ) : ℝ) * cnt bad4 k := by
        rw [div_mul_eq_mul_div, le_div_iff₀ hFp]; linarith
      have hvb : v b = 4 / ((F5 (lag4 b - 1) : ℚ) : ℝ) := by
        simp only [hv]
        by_cases h3b : b = 3
        · subst h3b
          rw [if_pos rfl, if_pos ⟨n₀, hn₀⟩, lag4_three]
        · rw [if_neg h3b]
          unfold w4
          rw [if_neg (by have := hB.2; omega)]
          push_cast; rfl
      rw [hvb]; linarith
    have hsum := Finset.sum_le_sum hwin
    have hsplit : ∑ b ∈ Finset.Ioc 2 (2 ^ (k + 3)), v b * cnt bad4 k =
        (v 3 + ∑ b ∈ Finset.Ioc 3 (2 ^ (k + 3)), ((w4 b : ℚ) : ℝ)) * cnt bad4 k := by
      have h8 : 3 ≤ 2 ^ (k + 3) := by
        calc 3 ≤ 2 ^ 3 := by norm_num
          _ ≤ 2 ^ (k + 3) := Nat.pow_le_pow_right (by norm_num) (by omega)
      rw [← Finset.sum_mul, ← Finset.sum_Ioc_consecutive _ (show 2 ≤ 3 by norm_num) h8,
        show Finset.Ioc 2 3 = {3} by decide, Finset.sum_singleton]
      congr 2
      refine Finset.sum_congr rfl fun b hb => ?_
      have := (Finset.mem_Ioc.1 hb).1
      simp only [hv, if_neg (show b ≠ 3 by omega)]
    have hT := sum_w4_le (2 ^ (k + 3))
    have hT' := mul_le_mul_of_nonneg_right hT hck
    rw [hsplit, add_mul] at hsum
    have hc4 : (0 : ℝ) ≤ cnt bad4 (k - 4) := by positivity
    have hrr : (cnt bad4 (k - 4) : ℝ) ≤ 12299 / 100000 * cnt bad4 k := by
      norm_num at hr4; linarith
    have e6 : 4 / ((F5 6 : ℚ) : ℝ) ≤ 16473 / 100000 := by norm_num [F5]
    unfold g4
    by_cases hk3 : K3' (k + 1)
    · have hv3 : v 3 = 4 / ((F5 6 : ℚ) : ℝ) := by simp [hv, hk3]
      rw [if_pos hk3]
      have h6 : v 3 * cnt bad4 k ≤ 16473 / 100000 * cnt bad4 k := by
        rw [hv3]; exact mul_le_mul_of_nonneg_right e6 hck
      linarith
    · have hv3 : v 3 = 0 := by simp [hv, hk3]
      rw [if_neg hk3]
      have h6 : v 3 * cnt bad4 k = 0 := by rw [hv3, zero_mul]
      linarith

/-- The tree below exponent `5` grows by `g4 k` at level `k`. -/
theorem growth_four : ∀ k, g4 k * cnt bad4 k ≤ cnt bad4 (k + 1) :=
  growth bad4 (fun k => le_trans (by norm_num) (g4_ge k)) fun k hch => card_kill4_le k hch

/-! ### From cells to the Diophantine condition -/

theorem dnear_two_ge4 {ξ : ℝ} {n a : ℕ} (hξ : ξ ∈ cell (n + 10) a) (hs1 : 33 ≤ a % 1024)
    (hs2 : a % 1024 ≤ 990) : (33 / 1024 : ℝ) ≤ dnear ((2 : ℝ) ^ n * ξ) := by
  obtain ⟨h1, h2⟩ := hξ
  set x := (2 : ℝ) ^ n * ξ with hx
  have e : (2 : ℝ) ^ (n + 10) = 2 ^ n * 1024 := by rw [pow_add]; norm_num
  have hpos : (0 : ℝ) < 2 ^ n := by positivity
  have hx1 : (a : ℝ) / 1024 ≤ x := by
    rw [e] at h1
    calc (a : ℝ) / 1024 = 2 ^ n * ((a : ℝ) / (2 ^ n * 1024)) := by field_simp
      _ ≤ x := by rw [hx]; gcongr
  have hx2 : x ≤ ((a : ℝ) + 1) / 1024 := by
    rw [e] at h2
    calc x ≤ 2 ^ n * (((a : ℝ) + 1) / (2 ^ n * 1024)) := by rw [hx]; gcongr
      _ = ((a : ℝ) + 1) / 1024 := by field_simp
  have ha : (a : ℝ) = 1024 * ((a / 1024 : ℕ) : ℝ) + ((a % 1024 : ℕ) : ℝ) := by
    exact_mod_cast (Nat.div_add_mod a 1024).symm
  have hs1' : (33 : ℝ) ≤ ((a % 1024 : ℕ) : ℝ) := by exact_mod_cast hs1
  have hs2' : ((a % 1024 : ℕ) : ℝ) ≤ 990 := by exact_mod_cast hs2
  unfold dnear
  rcases le_or_gt (round x) ((a / 1024 : ℕ) : ℤ) with hm | hm
  · have hm' : ((round x : ℤ) : ℝ) ≤ ((a / 1024 : ℕ) : ℝ) := by
      have := (Int.cast_le (R := ℝ)).2 hm
      rwa [Int.cast_natCast] at this
    rw [abs_of_nonneg (by linarith)]
    linarith
  · have hm' : ((a / 1024 : ℕ) : ℝ) + 1 ≤ ((round x : ℤ) : ℝ) := by
      have hm2 : ((a / 1024 : ℕ) : ℤ) + 1 ≤ round x := hm
      have := (Int.cast_le (R := ℝ)).2 hm2
      rwa [Int.cast_add, Int.cast_natCast, Int.cast_one] at this
    rw [abs_of_nonpos (by linarith)]
    linarith

theorem dnear_ge_of_cell4 {ξ : ℝ} {b n k a : ℕ} (hb : 3 ≤ b) (hξ : ξ ∈ cell k a)
    (h : ∀ A, ¬ meets4 k a b n A) : ((KB b : ℝ))⁻¹ ≤ dnear ((b : ℝ) ^ n * ξ) := by
  by_contra hlt
  replace hlt := not_le.1 hlt
  obtain ⟨h1, h2⟩ := hξ
  set x := (b : ℝ) ^ n * ξ with hx
  have hQ : (0 : ℝ) < 2 ^ k := by positivity
  have hb0 : (0 : ℝ) < b := by exact_mod_cast (by omega : 0 < b)
  have hB : (0 : ℝ) < (KB b : ℝ) := by exact_mod_cast (by have := KB_ge hb; omega : 0 < KB b)
  have hBn : (0 : ℝ) < (b : ℝ) ^ n := by positivity
  have hξ0 : 0 ≤ ξ := le_trans (by positivity) h1
  have hx0 : 0 ≤ x := by positivity
  have hd : |x - round x| < ((KB b : ℝ))⁻¹ := hlt
  have hB1 : ((KB b : ℝ))⁻¹ ≤ 1 :=
    inv_le_one_of_one_le₀ (by exact_mod_cast (by have := KB_ge hb; omega : 1 ≤ KB b))
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
  have hBx1 : (KB b : ℝ) * x < (KB b : ℝ) * A + 1 := by
    have := mul_lt_mul_of_pos_left hd2 hB
    rw [mul_sub, mul_inv_cancel₀ hB.ne'] at this; linarith
  have hBx2 : (KB b : ℝ) * A < (KB b : ℝ) * x + 1 := by
    have := mul_lt_mul_of_pos_left hd1 hB
    rw [mul_sub, mul_neg, mul_inv_cancel₀ hB.ne'] at this; linarith
  have ha1 : (a : ℝ) ≤ 2 ^ k * ξ := by rwa [div_le_iff₀ hQ, mul_comm] at h1
  have ha2 : 2 ^ k * ξ ≤ (a : ℝ) + 1 := by rwa [le_div_iff₀ hQ, mul_comm] at h2
  have hP : (0 : ℝ) < (b : ℝ) ^ n * (KB b : ℝ) := by positivity
  refine h A ⟨?_, ?_⟩
  · have key : (a : ℝ) * ((b : ℝ) ^ n * (KB b : ℝ)) < 2 ^ k * (A * (KB b : ℝ) + 1) := by
      calc (a : ℝ) * ((b : ℝ) ^ n * (KB b : ℝ)) ≤ 2 ^ k * ξ * ((b : ℝ) ^ n * (KB b : ℝ)) :=
            mul_le_mul_of_nonneg_right ha1 hP.le
        _ = 2 ^ k * ((KB b : ℝ) * x) := by rw [hx]; ring
        _ < 2 ^ k * ((KB b : ℝ) * A + 1) := mul_lt_mul_of_pos_left hBx1 hQ
        _ = 2 ^ k * (A * (KB b : ℝ) + 1) := by ring
    exact_mod_cast key
  · have key : (2 : ℝ) ^ k * (A * (KB b : ℝ)) <
        (a + 1) * ((b : ℝ) ^ n * (KB b : ℝ)) + 2 ^ k := by
      calc (2 : ℝ) ^ k * (A * (KB b : ℝ)) = 2 ^ k * ((KB b : ℝ) * A) := by ring
        _ < 2 ^ k * ((KB b : ℝ) * x + 1) := mul_lt_mul_of_pos_left hBx2 hQ
        _ = 2 ^ k * ξ * ((b : ℝ) ^ n * (KB b : ℝ)) + 2 ^ k := by rw [hx]; ring
        _ ≤ (a + 1) * ((b : ℝ) ^ n * (KB b : ℝ)) + 2 ^ k := by gcongr
    exact_mod_cast key

/-- **Below exponent `5`**: a real number with `‖2ⁿξ‖ ≥ 33/1024` and `‖bⁿξ‖ ≥ 1/K_b` in every
base `b ≥ 3` that is not a perfect power. -/
theorem exists_good_four :
    ∃ ξ : ℝ, (∀ n : ℕ, (33 / 1024 : ℝ) ≤ dnear ((2 : ℝ) ^ n * ξ)) ∧
      ∀ b : ℕ, 3 ≤ b → ¬ IsPerfPow b → ∀ n : ℕ, ((KB b : ℝ))⁻¹ ≤ dnear ((b : ℝ) ^ n * ξ) := by
  have hpos := cnt_pos bad4 (g := g4) (fun k => lt_of_lt_of_le (by norm_num) (g4_ge k))
    growth_four
  obtain ⟨ξ, hξ⟩ := exists_mem_cells bad4 hpos
  refine ⟨ξ, fun n => ?_, fun b hb3 hp n => ?_⟩
  · obtain ⟨a, ha, hx⟩ := hξ (n + 10)
    have hpat : ¬ pat10 (n + 9 + 1) a := fun h => ha.2 (Or.inr (Or.inl h))
    have ha5 := alive_anc bad4 5 (show Alive bad4 (n + 5 + 5) a from ha)
    have hrun : ¬ runBad5 (n + 4 + 1) (a / 2 ^ 5) := fun h => ha5.2 (Or.inl h)
    simp only [pat10, runBad5] at hpat hrun
    norm_num at hrun
    exact dnear_two_ge4 hx (by omega) (by omega)
  · obtain ⟨a, ha, hx⟩ := hξ (L4 b n)
    refine dnear_ge_of_cell4 hb3 hx fun A hA => ?_
    have hlv := eight_le_L4 hb3 n
    obtain ⟨m, hm⟩ : ∃ m, L4 b n = m + 1 := ⟨L4 b n - 1, by omega⟩
    rw [hm] at ha hA
    exact ha.2 (Or.inr (Or.inr ⟨b, n, A, base5_of_not_perfPow hb3 hp, hm, hA⟩))

end BelowFive

end Count

/-- `33/1024 > 2^{−c}` for `c > 124/25`, and `1/K_b > b^{−c}` for `b ≥ 3`. -/
theorem admissible_of_lt_124_25 {c : ℝ} (hc : 124 / 25 < c) : Admissible c := by
  obtain ⟨ξ, h2, hb⟩ := Count.exists_good_four
  refine (admissible_iff_nonPerfectPow (by linarith)).2 ⟨ξ, fun b hb2 hp n => ?_⟩
  have hb1 : (1 : ℝ) < b := by exact_mod_cast (by omega : 1 < b)
  have hbc : (b : ℝ) ^ ((124 : ℝ) / 25) < (b : ℝ) ^ c := Real.rpow_lt_rpow_of_exponent_lt hb1 hc
  have hy : ((b : ℝ) ^ ((124 : ℝ) / 25)) ^ (25 : ℕ) = (b : ℝ) ^ (124 : ℕ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]; norm_num
  have hpos : (0 : ℝ) < (b : ℝ) ^ ((124 : ℝ) / 25) := by positivity
  rw [Real.rpow_neg (by positivity)]
  rcases Nat.lt_or_ge b 3 with hb3 | hb3
  · obtain rfl : b = 2 := by omega
    refine lt_of_lt_of_le ?_ (by simpa using h2 n)
    have h1 : (1024 / 33 : ℝ) ≤ (2 : ℝ) ^ ((124 : ℝ) / 25) := by
      refine (pow_le_pow_iff_left₀ (by norm_num) hpos.le (by norm_num : (25 : ℕ) ≠ 0)).1 ?_
      push_cast at hy ⊢
      rw [hy]; norm_num
    push_cast at hbc
    rw [show (33 / 1024 : ℝ) = (1024 / 33)⁻¹ by norm_num]
    exact (inv_lt_inv₀ (by positivity) (by norm_num)).2 (lt_of_le_of_lt h1 hbc)
  · refine lt_of_lt_of_le ?_ (hb b hb3 hp n)
    have hK : ((Count.KB b : ℕ) : ℝ) ≤ (b : ℝ) ^ ((124 : ℝ) / 25) := by
      refine (pow_le_pow_iff_left₀ (by positivity) hpos.le (by norm_num : (25 : ℕ) ≠ 0)).1 ?_
      rw [hy]; exact_mod_cast Count.KB_pow_le hb3
    have hK0 : (0 : ℝ) < ((Count.KB b : ℕ) : ℝ) := by
      exact_mod_cast (by have := Count.KB_ge hb3; omega : 0 < Count.KB b)
    exact (inv_lt_inv₀ (by positivity) hK0).2 (lt_of_le_of_lt hK hbc)

/-- **`c⋆ ≤ 124/25`** (banked 2026-10-07, c⋆ lap 11): the lowest exponent the two-rate counting
engine of `cStar_le_five` certifies.  Proof: `Count.exists_good_four` (base `2` exact at threshold
`33/1024` via runs of five and the ten-digit patterns, windows `1/(bⁿ K_b)` with
`K_b ≤ b^{124/25}`, rates `181/100` and `33/20`), then `admissible_iff_nonPerfectPow`.

The engine has no room left: at `c = 9/2` the same balance fails by about `0.08`, because
pessimistic counting pays `4/g⁶ ≈ 0.12` per base-`3` kill level where the exact joint `{2,3}`
tree loses only about `2.4%`.  See `UniformBadNineHalves`. -/
@[blueprint (title := "Bugeaud 10.36 optimal exponent: c⋆ ≤ 124/25 by two-rate counting")]
theorem cStar_le_124_25 : cStar ≤ 124 / 25 :=
  le_of_forall_gt_imp_ge_of_dense fun _ hc =>
    csInf_le bddBelow_admissible (admissible_of_lt_124_25 hc)

end NormalNumbers.UniformBadThreshold
