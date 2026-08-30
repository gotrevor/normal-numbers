/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.AdderShadow
import NormalNumbers.AdderDescent
import NormalNumbers.AdderCertToy
import NormalNumbers.LnTwoIrrational

/-!
# Endgame: from the certificate to the disjunction (module 5)

Brief: `BRIEF-adder-disjunction-formalization.md` §"Endgame".

* `eq_of_digitOf_eq`: two reals of `[0,1)` with identical binary digit
  streams are equal (nested dyadic cylinders via `digits_prefix_iff`).
* `not_irrational_of_periodic_digits`: eventually periodic binary digits
  force rationality (two orbit points share their digit streams, so
  `fract(2^N·L) = fract(2^{N+p}·L)`, so `2^N(2^p−1)·fract L ∈ ℤ`).
* `no_occurrence_contradiction`: the generic engine — if every channel word
  of a certified family eventually stops occurring, shadowing + descent make
  the digits of `X` eventually periodic, contradicting `Irrational X`.
* `toy_disjunction`: the vacuous 3-channel dry run, end-to-end through every
  module — "`01` occurs infinitely often in ln 2, or `01` in ln 3, or `10`
  in ln 6", kernel-tier.
-/

namespace NormalNumbers.Adder

open NormalNumbers

/-- The repo digit map in `toNat` form. -/
theorem digitOf_two_fract (w : ℝ) (i : ℕ) :
    digitOf 2 (Int.fract w) i = (rdigit w i).toNat := by
  have := rdigit_eq_digitOf w i
  omega

/-- Two reals of `[0,1)` with identical binary digit streams are equal. -/
theorem eq_of_digitOf_eq {u v : ℝ} (hu : u ∈ Set.Ico (0:ℝ) 1)
    (hv : v ∈ Set.Ico (0:ℝ) 1) (h : ∀ j, digitOf 2 u j = digitOf 2 v j) :
    u = v := by
  by_contra hne
  have habs : 0 < |u - v| := abs_pos.2 (sub_ne_zero.2 hne)
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one habs (by norm_num : (1:ℝ)/2 < 1)
  set w : List ℕ := (List.range k).map (digitOf 2 u) with hw
  have hwlt : ∀ d ∈ w, d < 2 := by
    intro d hd
    simp only [hw, List.mem_map, List.mem_range] at hd
    obtain ⟨j, _, rfl⟩ := hd
    exact digitOf_lt 2 le_rfl u j
  have hlen : w.length = k := by simp [hw]
  have hupre : ∀ j (hj : j < w.length), digitOf 2 u j = w[j] := by
    intro j hj
    simp [hw]
  have hvpre : ∀ j (hj : j < w.length), digitOf 2 v j = w[j] := by
    intro j hj
    rw [← h j]
    simp [hw]
  have hu' := (digits_prefix_iff 2 le_rfl u hu w hwlt).1 hupre
  have hv' := (digits_prefix_iff 2 le_rfl v hv w hwlt).1 hvpre
  rw [hlen] at hu' hv'
  have hpow : (0:ℝ) < ((2:ℕ):ℝ) ^ k := by positivity
  have h₁ : u - v < 1 / ((2:ℕ):ℝ) ^ k := by
    have e : ((blockNatVal 2 w : ℝ) + 1) / ((2:ℕ):ℝ) ^ k
        - (blockNatVal 2 w : ℝ) / ((2:ℕ):ℝ) ^ k = 1 / ((2:ℕ):ℝ) ^ k := by
      ring
    have := hu'.2
    have := hv'.1
    linarith
  have h₂ : v - u < 1 / ((2:ℕ):ℝ) ^ k := by
    have e : ((blockNatVal 2 w : ℝ) + 1) / ((2:ℕ):ℝ) ^ k
        - (blockNatVal 2 w : ℝ) / ((2:ℕ):ℝ) ^ k = 1 / ((2:ℕ):ℝ) ^ k := by
      ring
    have := hv'.2
    have := hu'.1
    linarith
  have h₃ : |u - v| < 1 / ((2:ℕ):ℝ) ^ k := abs_sub_lt_iff.2 ⟨h₁, h₂⟩
  have h₄ : ((1:ℝ)/2) ^ k = 1 / ((2:ℕ):ℝ) ^ k := by
    rw [div_pow, one_pow]
    norm_num
  rw [h₄] at hk
  linarith

/-- Eventually periodic binary digits force rationality. -/
theorem not_irrational_of_periodic_digits (L : ℝ) (N p : ℕ) (hp : 0 < p)
    (h : ∀ m, N ≤ m → digitOf 2 (Int.fract L) (m + p) = digitOf 2 (Int.fract L) m) :
    ¬ Irrational L := by
  intro hirr
  set x : ℝ := Int.fract L with hxdef
  have hx : x ∈ Set.Ico (0:ℝ) 1 := ⟨Int.fract_nonneg L, Int.fract_lt_one L⟩
  have heq : orbit 2 x N = orbit 2 x (N + p) := by
    apply eq_of_digitOf_eq (orbit_mem_Ico 2 x N) (orbit_mem_Ico 2 x (N + p))
    intro j
    rw [digitOf_orbit 2 le_rfl x hx.1 N j, digitOf_orbit 2 le_rfl x hx.1 (N + p) j]
    have := h (N + j) (by omega)
    rw [show N + p + j = N + j + p from by omega]
    exact this.symm
  unfold orbit at heq
  rw [Int.fract_eq_fract] at heq
  obtain ⟨z, hz⟩ := heq
  -- x·(2^N − 2^{N+p}) = z, with nonzero coefficient
  have h2 : x * (((2:ℕ):ℝ) ^ N - ((2:ℕ):ℝ) ^ (N + p)) = (z : ℝ) := by
    rw [← hz]; ring
  have hlt : ((2:ℕ):ℝ) ^ N < ((2:ℕ):ℝ) ^ (N + p) := by
    have : ((2:ℕ):ℝ) = 2 := by norm_num
    rw [this]
    exact pow_lt_pow_right₀ (by norm_num) (by omega)
  have hden : (((2:ℕ):ℝ) ^ N - ((2:ℕ):ℝ) ^ (N + p)) ≠ 0 := by linarith
  have hxrat : ¬ Irrational x := by
    intro hxi
    refine hxi ⟨(z : ℚ) / ((2:ℚ) ^ N - (2:ℚ) ^ (N + p)), ?_⟩
    have hq : ((2:ℚ):ℝ) = ((2:ℕ):ℝ) := by norm_num
    push_cast
    rw [eq_comm, eq_div_iff (by push_cast at hden ⊢; convert hden using 2)]
    push_cast at h2 ⊢
    linarith [h2]
  apply hxrat
  have hfr : x = L - (⌊L⌋ : ℝ) := (Int.self_sub_floor L).symm
  rw [hfr]
  exact Irrational.sub_intCast hirr ⌊L⌋

/-- Uniformize per-channel "eventually never occurs" bounds over the list. -/
theorem exists_uniform_no_occurrence (chs : List Channel) (X Y : ℝ)
    (h : ∀ ch ∈ chs, ∃ N, ∀ n, N ≤ n → ¬ OccursAt 2 (ch.a * X + ch.b * Y) ch.word n) :
    ∃ N₀, ∀ ch ∈ chs, ∀ n, N₀ ≤ n → ¬ OccursAt 2 (ch.a * X + ch.b * Y) ch.word n := by
  induction chs with
  | nil => exact ⟨0, by simp⟩
  | cons ch rest ih =>
    obtain ⟨N₁, h₁⟩ := h ch (by simp)
    obtain ⟨N₂, h₂⟩ := ih (fun c hc => h c (by simp [hc]))
    refine ⟨max N₁ N₂, ?_⟩
    intro c hc n hn
    rcases List.mem_cons.1 hc with rfl | hc'
    · exact h₁ n (le_trans (le_max_left _ _) hn)
    · exact h₂ c hc' n (le_trans (le_max_right _ _) hn)

/-- **The generic engine, universal form**: a certified family whose channel
words all eventually stop occurring makes BOTH digit streams eventually
periodic (the joint input digit is `σ = dX + 2·dY`, so periodicity of `σ`
splits into periodicity of each coordinate), hence both `X` and `Y`
rational — contradicting "at least one irrational". -/
theorem no_occurrence_contradiction_universal (chs : List Channel) {S : ℕ}
    {live : ℕ → Bool} {rho omega : ℕ → ℕ} {forced : ℕ → Option (ℕ × ℕ)}
    (hS : S = famSize chs)
    (hcert : checkCert chs S live rho omega forced = true)
    (X Y : ℝ) (hXY : Irrational X ∨ Irrational Y)
    (hab : ∀ ch ∈ chs, 1 ≤ ch.a + ch.b) (hell : ∀ ch ∈ chs, 1 ≤ ch.ell)
    (hword : ∀ ch ∈ chs, ∀ d ∈ ch.word, d ≤ 1)
    (h : ∀ ch ∈ chs, ∃ N, ∀ n, N ≤ n → ¬ OccursAt 2 (ch.a * X + ch.b * Y) ch.word n) :
    False := by
  obtain ⟨N₀, hN₀⟩ := exists_uniform_no_occurrence chs X Y h
  have hσ : ∀ m, (rdigit X (N₀ + m)).toNat + 2 * (rdigit Y (N₀ + m)).toNat < 4 := by
    intro m
    have h₁ := rdigit_toNat_le_one X (N₀ + m)
    have h₂ := rdigit_toNat_le_one Y (N₀ + m)
    omega
  have hst : ∀ m, famState chs X Y (N₀ + m) < S :=
    fun m => hS ▸ famState_lt chs X Y (N₀ + m) hab
  have hstep : ∀ m, HStep chs (famState chs X Y (N₀ + m))
      ((rdigit X (N₀ + m)).toNat + 2 * (rdigit Y (N₀ + m)).toNat)
      (famState chs X Y (N₀ + (m + 1))) := by
    intro m
    exact hstep_famState chs X Y (N₀ + m) hab hell hword
      (fun ch hch => hN₀ ch hch (N₀ + m) (by omega))
  obtain ⟨N, p, hp, hper⟩ := input_eventually_periodic
    (st := fun k => famState chs X Y (N₀ + k))
    (σi := fun k => (rdigit X (N₀ + k)).toNat + 2 * (rdigit Y (N₀ + k)).toNat)
    hcert hσ hst hstep
  have hsplit : ∀ m, N₀ + N ≤ m →
      (rdigit X (m + p)).toNat = (rdigit X m).toNat ∧
      (rdigit Y (m + p)).toNat = (rdigit Y m).toNat := by
    intro m hm
    have hk := hper (m - N₀) (by omega)
    rw [show N₀ + (m - N₀ + p) = m + p from by omega,
      show N₀ + (m - N₀) = m from by omega] at hk
    have b₁ := rdigit_toNat_le_one X (m + p)
    have b₂ := rdigit_toNat_le_one Y (m + p)
    have b₃ := rdigit_toNat_le_one X m
    have b₄ := rdigit_toNat_le_one Y m
    omega
  rcases hXY with hX | hY
  · refine not_irrational_of_periodic_digits X (N₀ + N) p hp ?_ hX
    intro m hm
    rw [digitOf_two_fract, digitOf_two_fract]
    exact (hsplit m hm).1
  · refine not_irrational_of_periodic_digits Y (N₀ + N) p hp ?_ hY
    intro m hm
    rw [digitOf_two_fract, digitOf_two_fract]
    exact (hsplit m hm).2

/-- The one-sided engine (irrational `X`), as an instance of the universal
form. -/
theorem no_occurrence_contradiction (chs : List Channel) {S : ℕ}
    {live : ℕ → Bool} {rho omega : ℕ → ℕ} {forced : ℕ → Option (ℕ × ℕ)}
    (hS : S = famSize chs)
    (hcert : checkCert chs S live rho omega forced = true)
    (X Y : ℝ) (hX : Irrational X)
    (hab : ∀ ch ∈ chs, 1 ≤ ch.a + ch.b) (hell : ∀ ch ∈ chs, 1 ≤ ch.ell)
    (hword : ∀ ch ∈ chs, ∀ d ∈ ch.word, d ≤ 1)
    (h : ∀ ch ∈ chs, ∃ N, ∀ n, N ≤ n → ¬ OccursAt 2 (ch.a * X + ch.b * Y) ch.word n) :
    False :=
  no_occurrence_contradiction_universal chs hS hcert X Y (Or.inl hX) hab hell hword h

/-- **The toy disjunction, end-to-end** (vacuous 3-channel dry run of the
whole pipeline): `01` occurs infinitely often in the binary expansion of
ln 2, or `01` in ln 3, or `10` in ln 6. -/
theorem toy_disjunction :
    (∀ N, ∃ n, N ≤ n ∧ OccursAt 2 (Real.log 2) [0, 1] n) ∨
    (∀ N, ∃ n, N ≤ n ∧ OccursAt 2 (Real.log 3) [0, 1] n) ∨
    (∀ N, ∃ n, N ≤ n ∧ OccursAt 2 (Real.log 6) [1, 0] n) := by
  by_contra hcon
  push Not at hcon
  obtain ⟨h₁, h₂, h₃⟩ := hcon
  obtain ⟨N₁, hN₁⟩ := h₁
  obtain ⟨N₂, hN₂⟩ := h₂
  obtain ⟨N₃, hN₃⟩ := h₃
  refine no_occurrence_contradiction toyFamily (by decide) toy_cert_ok
    (Real.log 2) (Real.log 3) irrational_log_two
    (by decide) (by decide) (by decide) ?_
  intro ch hch
  have h6 : Real.log 6 = Real.log 2 + Real.log 3 := by
    rw [show (6:ℝ) = 2 * 3 from by norm_num]
    exact Real.log_mul (by norm_num) (by norm_num)
  fin_cases hch
  · refine ⟨N₁, fun n hn => ?_⟩
    show ¬ OccursAt 2 (((1:ℕ):ℝ) * Real.log 2 + ((0:ℕ):ℝ) * Real.log 3) [0, 1] n
    rw [show ((1:ℕ):ℝ) * Real.log 2 + ((0:ℕ):ℝ) * Real.log 3 = Real.log 2 from by
      push_cast; ring]
    exact fun hocc => hN₁ n hn hocc
  · refine ⟨N₂, fun n hn => ?_⟩
    show ¬ OccursAt 2 (((0:ℕ):ℝ) * Real.log 2 + ((1:ℕ):ℝ) * Real.log 3) [0, 1] n
    rw [show ((0:ℕ):ℝ) * Real.log 2 + ((1:ℕ):ℝ) * Real.log 3 = Real.log 3 from by
      push_cast; ring]
    exact fun hocc => hN₂ n hn hocc
  · refine ⟨N₃, fun n hn => ?_⟩
    show ¬ OccursAt 2 (((1:ℕ):ℝ) * Real.log 2 + ((1:ℕ):ℝ) * Real.log 3) [1, 0] n
    rw [show ((1:ℕ):ℝ) * Real.log 2 + ((1:ℕ):ℝ) * Real.log 3 = Real.log 6 from by
      push_cast; rw [h6]; ring]
    exact fun hocc => hN₃ n hn hocc

end NormalNumbers.Adder
