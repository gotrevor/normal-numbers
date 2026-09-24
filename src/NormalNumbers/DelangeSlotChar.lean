import NormalNumbers.DelangeSlotAnalytic

/-!
# Rung 2, layer 1: the chain for `g = χ · z^{ω_{>P}}`

For the twisted slot we must run the rung-1 chain not on `h = z^{ω_{>P}}` but on
`g = χ · z^{ω_{>P}}` for `χ` a Dirichlet character mod `Q` (here abstracted as any completely
multiplicative `χ : ℕ → ℂ` of modulus `≤ 1`).

The structural point that makes rung 2 *cheaper* than rung 1 for **non-principal** `χ`:
`ψ(x, χ) = ∑_{d ≤ x} Λ d χ d` has **no main term**, so the chain

  `S_g N · log N = z · ∑_{k ≤ N} g k · ψ(N/k, χ) + O_P(N)`

already gives `S_g N = o(N)` as soon as `ψ(x,χ) = o(x)` — no recursion, no `mSum`, no L6/L7,
and crucially **no quantitative zero-free region**: the qualitative `o(x)`, which is what
Wiener–Ikehara plus mathlib's `LFunction_ne_zero_of_one_le_re` delivers, suffices.  (The
splitting `∑_{k≤N} ε(N/k)·(N/k) ≤ N log N · ε(A) + C N log A` is `sum_littleO_div_le` below.)

For the **principal** character the main term is back and one reruns rung 1 verbatim; see
`DESIGN-2026-09-24-delange-route.md`.

Status of this file: the algebraic chain (L1–L3, L5) is proved for general `χ`; the analytic
input `ψ(x,χ) = o(x)` is the named open obligation `psiChar_isLittleO`.
-/

open Finset ArithmeticFunction Filter Topology

namespace NormalNumbers.DelangeSlot

variable (χ : ℕ → ℂ) (z : ℂ) (P : ℕ)

/-- `g n = χ n · z ^ ω_{>P}(n)`. -/
noncomputable def gfun (χ : ℕ → ℂ) (z : ℂ) (P n : ℕ) : ℂ := χ n * hfun z P n

/-- `S_g N = ∑_{1 ≤ n ≤ N} g n`. -/
noncomputable def Sgsum (χ : ℕ → ℂ) (z : ℂ) (P N : ℕ) : ℂ := ∑ n ∈ Ioc 0 N, gfun χ z P n

/-- The tail over multiples of `p`. -/
noncomputable def Tgsum (χ : ℕ → ℂ) (z : ℂ) (P p X : ℕ) : ℂ :=
  ∑ m ∈ (Ioc 0 X).filter (fun m => p ∣ m), gfun χ z P m

/-- `ψ(x, χ) = ∑_{d ≤ x} Λ d · χ d`. -/
noncomputable def psiChar (χ : ℕ → ℂ) (X : ℕ) : ℂ := ∑ d ∈ Ioc 0 X, (Λ d : ℂ) * χ d

section Norms

variable {χ z P} (hχ : ∀ n, ‖χ n‖ ≤ 1) (hz : ‖z‖ = 1)

include hχ hz in
lemma norm_gfun_le (n : ℕ) : ‖gfun χ z P n‖ ≤ 1 := by
  rw [gfun, norm_mul, norm_hfun_le hz, mul_one]; exact hχ n

include hχ hz in
lemma norm_Sgsum_le (N : ℕ) : ‖Sgsum χ z P N‖ ≤ N := by
  refine (norm_sum_le _ _).trans ?_
  calc ∑ n ∈ Ioc 0 N, ‖gfun χ z P n‖ ≤ ∑ _n ∈ Ioc 0 N, (1:ℝ) :=
        Finset.sum_le_sum fun n _ ↦ norm_gfun_le hχ hz n
    _ = N := by simp

include hχ hz in
lemma norm_Tgsum_le (p X : ℕ) : ‖Tgsum χ z P p X‖ ≤ ((X / p : ℕ) : ℝ) := by
  classical
  refine (norm_sum_le _ _).trans ?_
  calc ∑ m ∈ (Ioc 0 X).filter (fun m => p ∣ m), ‖gfun χ z P m‖
      ≤ ∑ _m ∈ (Ioc 0 X).filter (fun m => p ∣ m), (1:ℝ) :=
        Finset.sum_le_sum fun m _ ↦ norm_gfun_le hχ hz m
    _ = ((Ioc 0 X).filter (fun m => p ∣ m)).card := by simp
    _ = ((X / p : ℕ) : ℝ) := by rw [Nat.Ioc_filter_dvd_card_eq_div X p]

end Norms

/-- **L1 for `g`.**  The von-Mangoldt identity; purely formal. -/
theorem sum_gfun_mul_log (N : ℕ) :
    ∑ n ∈ Ioc 0 N, gfun χ z P n * (Real.log n : ℂ)
      = ∑ d ∈ Ioc 0 N, (Λ d : ℂ) * ∑ m ∈ Ioc 0 (N / d), gfun χ z P (d * m) := by
  classical
  have key : ∀ n ∈ Ioc 0 N, gfun χ z P n * (Real.log n : ℂ)
      = ∑ x ∈ n.divisorsAntidiagonal, (Λ x.1 : ℂ) * gfun χ z P (x.1 * x.2) := by
    intro n hn
    rw [Nat.sum_divisorsAntidiagonal (f := fun d m => (Λ d : ℂ) * gfun χ z P (d * m))]
    have : ∀ d ∈ n.divisors, (Λ d : ℂ) * gfun χ z P (d * (n / d)) = (Λ d : ℂ) * gfun χ z P n := by
      intro d hd
      rw [Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors hd)]
    rw [sum_congr rfl this, ← sum_mul, ← Complex.ofReal_sum, vonMangoldt_sum]
    ring
  rw [sum_congr rfl key, sum_divisorAntidiagonal_swap
      (F := fun d m => (Λ d : ℂ) * gfun χ z P (d * m)) N]
  exact sum_congr rfl fun d _ ↦ (mul_sum _ _ _).symm

section Shift

variable {χ z P} (hmul : ∀ a b : ℕ, χ (a * b) = χ a * χ b)

include hmul in
/-- **Shift at a large prime** for `g`: the factor `χ (p^j)` comes out. -/
lemma sum_gfun_shift_large {p : ℕ} (hp : p.Prime) {j : ℕ} (hj : j ≠ 0) (hP : P < p) (X : ℕ) :
    ∑ m ∈ Ioc 0 X, gfun χ z P (p ^ j * m)
      = χ (p ^ j) * (z * Sgsum χ z P X - (z - 1) * Tgsum χ z P p X) := by
  classical
  have hterm : ∀ m ∈ Ioc 0 X, gfun χ z P (p ^ j * m)
      = χ (p ^ j) * (z * gfun χ z P m - (if p ∣ m then (z - 1) * gfun χ z P m else 0)) := by
    intro m hm
    have hm0 : m ≠ 0 := by have := (mem_Ioc.1 hm).1; lia
    rw [gfun, gfun, hmul, hfun, hfun, omegaLarge_prime_pow_mul hp hj hm0 P]
    by_cases hpm : p ∣ m
    · simp [hpm]; ring
    · simp [hpm, hP, pow_succ]; ring
  rw [sum_congr rfl hterm, ← Finset.mul_sum, Finset.sum_sub_distrib, ← Finset.mul_sum, Sgsum,
    Tgsum, ← Finset.sum_filter, ← Finset.mul_sum]

include hmul in
/-- **Shift at a small prime** for `g`. -/
lemma sum_gfun_shift_small {p : ℕ} (hp : p.Prime) {j : ℕ} (hj : j ≠ 0) (hP : ¬ P < p) (X : ℕ) :
    ∑ m ∈ Ioc 0 X, gfun χ z P (p ^ j * m) = χ (p ^ j) * Sgsum χ z P X := by
  classical
  rw [Sgsum, Finset.mul_sum]
  refine sum_congr rfl fun m hm ↦ ?_
  have hm0 : m ≠ 0 := by have := (mem_Ioc.1 hm).1; lia
  rw [gfun, gfun, hmul, hfun, hfun, omegaLarge_prime_pow_mul hp hj hm0 P]
  simp [hP, mul_assoc]

end Shift


section Chain

variable {χ z P} (hmul : ∀ a b : ℕ, χ (a * b) = χ a * χ b) (hχ : ∀ n, ‖χ n‖ ≤ 1) (hz : ‖z‖ = 1)

include hmul hχ hz in
/-- **L2 for `g`.**  Replacing the inner sum by `z · χ d · S_g (N/d)`; constant depends on `P`. -/
theorem exists_L2g :
    ∃ C : ℝ, ∀ N : ℕ,
      ‖(∑ n ∈ Ioc 0 N, gfun χ z P n * (Real.log n : ℂ))
        - z * ∑ d ∈ Ioc 0 N, (Λ d : ℂ) * χ d * Sgsum χ z P (N / d)‖ ≤ C * N := by
  classical
  have hz1 : ‖z - 1‖ ≤ 2 := by
    calc ‖z - 1‖ ≤ ‖z‖ + ‖(1:ℂ)‖ := norm_sub_le _ _
      _ = 2 := by rw [hz]; norm_num
  refine ⟨16 + 4 * ∑ n ∈ Icc 2 P, Real.log n / (n : ℝ), fun N ↦ ?_⟩
  have hrw : (∑ n ∈ Ioc 0 N, gfun χ z P n * (Real.log n : ℂ))
        - z * ∑ d ∈ Ioc 0 N, (Λ d : ℂ) * χ d * Sgsum χ z P (N / d)
      = ∑ d ∈ Ioc 0 N, (Λ d : ℂ) *
          ((∑ m ∈ Ioc 0 (N / d), gfun χ z P (d * m)) - z * χ d * Sgsum χ z P (N / d)) := by
    rw [sum_gfun_mul_log, Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun d _ ↦ by ring
  rw [hrw]
  refine (norm_sum_le _ _).trans ?_
  have hterm : ∀ d ∈ Ioc 0 N,
      ‖(Λ d : ℂ) * ((∑ m ∈ Ioc 0 (N / d), gfun χ z P (d * m)) - z * χ d * Sgsum χ z P (N / d))‖
        ≤ 2 * (Λ d * ((N / (d * d.minFac) : ℕ) : ℝ))
          + 2 * (if d.minFac ≤ P then Λ d * ((N / d : ℕ) : ℝ) else 0) := by
    intro d _
    by_cases hdp : IsPrimePow d
    · obtain ⟨k, hk0, _, hdk, _⟩ := primePow_spec hdp
      have hp : d.minFac.Prime := Nat.minFac_prime hdp.ne_one
      have hΛ0 : (0:ℝ) ≤ Λ d := vonMangoldt_nonneg
      have hnormΛ : ‖(Λ d : ℂ)‖ = Λ d := by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hΛ0]
      rw [norm_mul, hnormΛ]
      by_cases hP : P < d.minFac
      · have hshift : ∑ m ∈ Ioc 0 (N / d), gfun χ z P (d * m)
            = χ d * (z * Sgsum χ z P (N / d) - (z - 1) * Tgsum χ z P d.minFac (N / d)) := by
          have h := sum_gfun_shift_large (χ := χ) (z := z) (P := P) hmul hp (j := k) (by lia) hP
            (N / d)
          rwa [hdk.symm] at h
        have hTle : ‖Tgsum χ z P d.minFac (N / d)‖ ≤ ((N / (d * d.minFac) : ℕ) : ℝ) := by
          have h := norm_Tgsum_le (χ := χ) (z := z) (P := P) hχ hz d.minFac (N / d)
          rwa [Nat.div_div_eq_div_mul] at h
        have hbody : ‖(∑ m ∈ Ioc 0 (N / d), gfun χ z P (d * m)) - z * χ d * Sgsum χ z P (N / d)‖
            ≤ 2 * ((N / (d * d.minFac) : ℕ) : ℝ) := by
          rw [hshift]
          have he : χ d * (z * Sgsum χ z P (N / d) - (z - 1) * Tgsum χ z P d.minFac (N / d))
              - z * χ d * Sgsum χ z P (N / d)
              = -(χ d * ((z - 1) * Tgsum χ z P d.minFac (N / d))) := by ring
          rw [he, norm_neg, norm_mul, norm_mul]
          have h1 : ‖χ d‖ * (‖z - 1‖ * ‖Tgsum χ z P d.minFac (N / d)‖)
              ≤ 1 * (2 * ((N / (d * d.minFac) : ℕ) : ℝ)) :=
            mul_le_mul (hχ d) (mul_le_mul hz1 hTle (norm_nonneg _) (by norm_num))
              (by positivity) (by norm_num)
          simpa using h1
        have hextra : (0:ℝ) ≤ 2 * (if d.minFac ≤ P then Λ d * ((N / d : ℕ) : ℝ) else 0) := by
          by_cases h : d.minFac ≤ P
          · simp only [h, if_pos]; positivity
          · simp [h]
        nlinarith [mul_le_mul_of_nonneg_left hbody hΛ0, hextra]
      · push_neg at hP
        have hshift : ∑ m ∈ Ioc 0 (N / d), gfun χ z P (d * m) = χ d * Sgsum χ z P (N / d) := by
          have h := sum_gfun_shift_small (χ := χ) (z := z) (P := P) hmul hp (j := k) (by lia)
            (by lia) (N / d)
          rwa [hdk.symm] at h
        have hbody : ‖(∑ m ∈ Ioc 0 (N / d), gfun χ z P (d * m)) - z * χ d * Sgsum χ z P (N / d)‖
            ≤ 2 * ((N / d : ℕ) : ℝ) := by
          rw [hshift]
          have he : χ d * Sgsum χ z P (N / d) - z * χ d * Sgsum χ z P (N / d)
              = -(χ d * ((z - 1) * Sgsum χ z P (N / d))) := by ring
          rw [he, norm_neg, norm_mul, norm_mul]
          have h1 : ‖χ d‖ * (‖z - 1‖ * ‖Sgsum χ z P (N / d)‖)
              ≤ 1 * (2 * ((N / d : ℕ) : ℝ)) :=
            mul_le_mul (hχ d)
              (mul_le_mul hz1 (norm_Sgsum_le hχ hz (N / d)) (norm_nonneg _) (by norm_num))
              (by positivity) (by norm_num)
          simpa using h1
        have hfirst : (0:ℝ) ≤ 2 * (Λ d * ((N / (d * d.minFac) : ℕ) : ℝ)) := by positivity
        simp only [hP, if_pos]
        nlinarith [mul_le_mul_of_nonneg_left hbody hΛ0, hfirst]
    · rw [vonMangoldt_eq_zero_iff.2 hdp]
      by_cases h : d.minFac ≤ P <;> simp [h]
  calc ∑ d ∈ Ioc 0 N,
        ‖(Λ d : ℂ) * ((∑ m ∈ Ioc 0 (N / d), gfun χ z P (d * m)) - z * χ d * Sgsum χ z P (N / d))‖
      ≤ ∑ d ∈ Ioc 0 N, (2 * (Λ d * ((N / (d * d.minFac) : ℕ) : ℝ))
          + 2 * (if d.minFac ≤ P then Λ d * ((N / d : ℕ) : ℝ) else 0)) :=
        Finset.sum_le_sum hterm
    _ = 2 * (∑ d ∈ Ioc 0 N, Λ d * ((N / (d * d.minFac) : ℕ) : ℝ))
          + 2 * (∑ d ∈ Ioc 0 N, (if d.minFac ≤ P then Λ d * ((N / d : ℕ) : ℝ) else 0)) := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    _ ≤ 2 * (8 * (N : ℝ)) + 2 * (2 * (N : ℝ) * ∑ n ∈ Icc 2 P, Real.log n / (n : ℝ)) := by
        have h1 := sum_vonMangoldt_mul_div_minFac_le N
        have h2 := sum_vonMangoldt_smooth_le N P
        linarith
    _ = (16 + 4 * ∑ n ∈ Icc 2 P, Real.log n / (n : ℝ)) * N := by ring

end Chain

/-- **L3 for `g`.**  Transposing the hyperbola onto the `ψ(·,χ)`-side. -/
theorem sum_Lambda_mul_Sgsum (N : ℕ) :
    ∑ d ∈ Ioc 0 N, (Λ d : ℂ) * χ d * Sgsum χ z P (N / d)
      = ∑ k ∈ Ioc 0 N, gfun χ z P k * psiChar χ (N / k) := by
  classical
  have l : ∀ d ∈ Ioc 0 N, (Λ d : ℂ) * χ d * Sgsum χ z P (N / d)
      = ∑ m ∈ Ioc 0 (N / d), ((Λ d : ℂ) * χ d) * gfun χ z P m := by
    intro d _; rw [Sgsum, Finset.mul_sum]
  have r : ∀ k ∈ Ioc 0 N, gfun χ z P k * psiChar χ (N / k)
      = ∑ d ∈ Ioc 0 (N / k), ((Λ d : ℂ) * χ d) * gfun χ z P k := by
    intro k _
    rw [psiChar, Finset.mul_sum]
    exact Finset.sum_congr rfl fun d _ ↦ mul_comm _ _
  rw [sum_congr rfl l, sum_congr rfl r]
  exact sum_div_comm (fun d m => ((Λ d : ℂ) * χ d) * gfun χ z P m) N

/-- **L5 for `g`.**  The `log n` weight versus the flat weight. -/
theorem norm_sum_gfun_mul_log_sub {χ : ℕ → ℂ} {z : ℂ} {P : ℕ} (hχ : ∀ n, ‖χ n‖ ≤ 1)
    (hz : ‖z‖ = 1) (N : ℕ) :
    ‖(∑ n ∈ Ioc 0 N, gfun χ z P n * (Real.log n : ℂ))
      - Sgsum χ z P N * (Real.log N : ℂ)‖ ≤ N := by
  have hrw : (∑ n ∈ Ioc 0 N, gfun χ z P n * (Real.log n : ℂ))
      - Sgsum χ z P N * (Real.log N : ℂ)
      = ∑ n ∈ Ioc 0 N, gfun χ z P n * ((Real.log n : ℂ) - (Real.log N : ℂ)) := by
    rw [Sgsum, Finset.sum_mul, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun n _ ↦ by ring
  rw [hrw]
  refine (norm_sum_le _ _).trans ?_
  refine le_trans (Finset.sum_le_sum (fun n hn ↦ ?_)) (sum_log_div_le N)
  have hn0 : (0:ℝ) < n := by exact_mod_cast (mem_Ioc.1 hn).1
  have hnN : (n:ℝ) ≤ N := by exact_mod_cast (mem_Ioc.1 hn).2
  have hN0 : (0:ℝ) < N := lt_of_lt_of_le hn0 hnN
  have hlog : Real.log n ≤ Real.log N := Real.log_le_log hn0 hnN
  rw [norm_mul, ← Complex.ofReal_sub, Complex.norm_real,
    Real.log_div hN0.ne' hn0.ne', Real.norm_eq_abs, abs_sub_comm]
  have habs : |Real.log N - Real.log n| = Real.log N - Real.log n :=
    abs_of_nonneg (by linarith)
  rw [habs]
  exact mul_le_of_le_one_left (by linarith) (norm_gfun_le hχ hz n)


/-! ### The `o(x) ⟹ mean → 0` bridge -/

/-- `∑_{1 ≤ k ≤ N} 1/k ≤ 1 + log N`. -/
lemma sum_inv_le_one_add_log (N : ℕ) : ∑ k ∈ Ioc 0 N, (1:ℝ) / k ≤ 1 + Real.log N := by
  induction N with
  | zero => simp
  | succ N ih =>
    rcases Nat.eq_zero_or_pos N with rfl | hN
    · norm_num
    have hN0 : (0:ℝ) < N := by exact_mod_cast hN
    have hstep : (1:ℝ) / (N + 1) ≤ Real.log ((N:ℝ) + 1) - Real.log N := by
      have hx : (0:ℝ) < (N:ℝ) / ((N:ℝ) + 1) := by positivity
      have h := Real.log_le_sub_one_of_pos hx
      rw [Real.log_div hN0.ne' (by positivity)] at h
      have : (N:ℝ) / ((N:ℝ) + 1) - 1 = -(1 / ((N:ℝ) + 1)) := by field_simp; ring
      rw [this] at h
      linarith
    rw [Finset.sum_Ioc_succ_top (Nat.zero_le _)]
    push_cast
    linarith

/-- `‖ψ(X, χ)‖ ≤ ψ(X)`. -/
lemma norm_psiChar_le {χ : ℕ → ℂ} (hχ : ∀ n, ‖χ n‖ ≤ 1) (X : ℕ) :
    ‖psiChar χ X‖ ≤ psiN X := by
  refine (norm_sum_le _ _).trans ?_
  rw [psiN]
  refine Finset.sum_le_sum fun d _ ↦ ?_
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg vonMangoldt_nonneg]
  exact mul_le_of_le_one_right vonMangoldt_nonneg (hχ d)

/-- **The hyperbola-sum bridge.**  If `ψ(x,χ) = o(x)` then `∑_{k ≤ N} ‖ψ(N/k, χ)‖ = o(N log N)`.
This is the step that makes the *qualitative* `o(x)` enough: the `k > N/A` range contributes
only `O_A(N)`, and the `k ≤ N/A` range inherits the `ε` through the harmonic sum. -/
theorem sum_psiChar_div_le {χ : ℕ → ℂ} (hχ : ∀ n, ‖χ n‖ ≤ 1)
    (hpsi : ∀ ε : ℝ, 0 < ε → ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X → ‖psiChar χ X‖ ≤ ε * X)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∑ k ∈ Ioc 0 N, ‖psiChar χ (N / k)‖ ≤ ε * N * Real.log N := by
  obtain ⟨A, hA⟩ := hpsi (ε / 4) (by linarith)
  set B : ℝ := psiN A with hB
  have hB0 : 0 ≤ B := psiN_nonneg A
  -- the termwise bound, valid for every `k`
  have hterm : ∀ N k : ℕ, 0 < k → ‖psiChar χ (N / k)‖ ≤ (ε / 4) * ((N:ℝ) / k) + B := by
    intro N k hk
    rcases le_or_gt A (N / k) with h | h
    · have h1 : ‖psiChar χ (N / k)‖ ≤ (ε / 4) * ((N / k : ℕ) : ℝ) := hA _ h
      have h2 : ((N / k : ℕ) : ℝ) ≤ (N:ℝ) / k := Nat.cast_div_le
      nlinarith
    · have : ‖psiChar χ (N / k)‖ ≤ B :=
        (norm_psiChar_le hχ _).trans (psiN_mono h.le)
      have : (0:ℝ) ≤ (ε / 4) * ((N:ℝ) / k) := by positivity
      linarith [(norm_psiChar_le hχ (N / k)).trans (psiN_mono h.le)]
  -- choose the threshold
  obtain ⟨N₀, hN₀⟩ : ∃ N₀ : ℕ, 1 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N → 1 ≤ Real.log N ∧ 4 * B / ε ≤ Real.log N := by
    have hlog : Tendsto (fun n : ℕ => Real.log n) atTop atTop :=
      Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
    obtain ⟨M, hM⟩ := (hlog.eventually_ge_atTop (max 1 (4 * B / ε))).exists_forall_of_atTop
    exact ⟨max 1 M, le_max_left _ _, fun N hN ↦
      ⟨le_trans (le_max_left _ _) (hM N (le_trans (le_max_right _ _) hN)),
       le_trans (le_max_right _ _) (hM N (le_trans (le_max_right _ _) hN))⟩⟩
  refine ⟨N₀, fun N hN ↦ ?_⟩
  obtain ⟨hlog1, hlogB⟩ := hN₀.2 N hN
  have hN1 : 1 ≤ N := le_trans hN₀.1 hN
  have hNR : (1:ℝ) ≤ N := by exact_mod_cast hN1
  have hcoef : (0:ℝ) ≤ ε / 4 * (N:ℝ) := by positivity
  have hharm := sum_inv_le_one_add_log N
  have hstep2 : (1:ℝ) + Real.log N ≤ 2 * Real.log N := by linarith
  have hBlog : B ≤ ε / 4 * Real.log N := by
    rcases eq_or_lt_of_le hB0 with h | h
    · nlinarith [Real.log_nonneg hNR]
    · rw [div_le_iff₀ hε] at hlogB; nlinarith
  calc ∑ k ∈ Ioc 0 N, ‖psiChar χ (N / k)‖
      ≤ ∑ k ∈ Ioc 0 N, (ε / 4 * ((N:ℝ) / k) + B) :=
        Finset.sum_le_sum fun k hk ↦ hterm N k (mem_Ioc.1 hk).1
    _ = (ε / 4 * (N:ℝ)) * (∑ k ∈ Ioc 0 N, (1:ℝ) / k) + (N:ℝ) * B := by
        rw [Finset.sum_add_distrib, Finset.sum_const, Nat.card_Ioc, Nat.sub_zero, nsmul_eq_mul,
          Finset.mul_sum]
        congr 1
        exact Finset.sum_congr rfl fun k _ ↦ by ring
    _ ≤ (ε / 4 * (N:ℝ)) * (1 + Real.log N) + (N:ℝ) * B := by
        have := mul_le_mul_of_nonneg_left hharm hcoef
        linarith
    _ ≤ (ε / 4 * (N:ℝ)) * (2 * Real.log N) + (N:ℝ) * (ε / 4 * Real.log N) := by
        have h1 := mul_le_mul_of_nonneg_left hstep2 hcoef
        have h2 : (N:ℝ) * B ≤ (N:ℝ) * (ε / 4 * Real.log N) := by
          have hN0 : (0:ℝ) ≤ N := by linarith
          exact mul_le_mul_of_nonneg_left hBlog hN0
        linarith
    _ ≤ ε * N * Real.log N := by
        have hlog0 : (0:ℝ) ≤ Real.log N := by linarith
        nlinarith [hlog0, hNR, hε.le]


/-- **Rung 2, layer 1 (the payoff).**  For `χ` completely multiplicative of modulus `≤ 1`,
if `ψ(x,χ) = o(x)` then the mean of `g = χ · z^{ω_{>P}}` tends to `0` — with **no** hypothesis
on `z` beyond `‖z‖ = 1`, and with no recursion.  Applied to a non-principal Dirichlet character
this is the non-principal half of the twisted slot. -/
theorem Sgsum_tendsto_zero_of_psi_littleO {χ : ℕ → ℂ} {z : ℂ} {P : ℕ}
    (hmul : ∀ a b : ℕ, χ (a * b) = χ a * χ b) (hχ : ∀ n, ‖χ n‖ ≤ 1) (hz : ‖z‖ = 1)
    (hpsi : ∀ ε : ℝ, 0 < ε → ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X → ‖psiChar χ X‖ ≤ ε * X) :
    Tendsto (fun N : ℕ => Sgsum χ z P N / (N : ℂ)) atTop (𝓝 0) := by
  obtain ⟨C, hC⟩ := exists_L2g (χ := χ) (z := z) (P := P) hmul hχ hz
  have hC0 : 0 ≤ C := by have := (norm_nonneg _).trans (hC 1); simpa using this
  -- the master inequality
  have master : ∀ N : ℕ, ‖Sgsum χ z P N‖ * Real.log N
      ≤ (1 + C) * N + ∑ k ∈ Ioc 0 N, ‖psiChar χ (N / k)‖ := by
    intro N
    rcases Nat.eq_zero_or_pos N with rfl | hN
    · simp
    have hlog : 0 ≤ Real.log N := Real.log_natCast_nonneg N
    set A : ℂ := ∑ n ∈ Ioc 0 N, gfun χ z P n * (Real.log n : ℂ) with hA
    have hsplit : Sgsum χ z P N * (Real.log N : ℂ)
        = -(A - Sgsum χ z P N * (Real.log N : ℂ))
          + (A - z * ∑ d ∈ Ioc 0 N, (Λ d : ℂ) * χ d * Sgsum χ z P (N / d))
          + z * ∑ k ∈ Ioc 0 N, gfun χ z P k * psiChar χ (N / k) := by
      rw [← sum_Lambda_mul_Sgsum]; ring
    have hpsiSum : ‖∑ k ∈ Ioc 0 N, gfun χ z P k * psiChar χ (N / k)‖
        ≤ ∑ k ∈ Ioc 0 N, ‖psiChar χ (N / k)‖ := by
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ ↦ ?_)
      rw [norm_mul]
      exact mul_le_of_le_one_left (norm_nonneg _) (norm_gfun_le hχ hz k)
    have hnormLHS : ‖Sgsum χ z P N * (Real.log N : ℂ)‖ = ‖Sgsum χ z P N‖ * Real.log N := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hlog]
    rw [← hnormLHS, hsplit]
    calc ‖-(A - Sgsum χ z P N * (Real.log N : ℂ))
            + (A - z * ∑ d ∈ Ioc 0 N, (Λ d : ℂ) * χ d * Sgsum χ z P (N / d))
          + z * ∑ k ∈ Ioc 0 N, gfun χ z P k * psiChar χ (N / k)‖
        ≤ ‖-(A - Sgsum χ z P N * (Real.log N : ℂ))
            + (A - z * ∑ d ∈ Ioc 0 N, (Λ d : ℂ) * χ d * Sgsum χ z P (N / d))‖
          + ‖z * ∑ k ∈ Ioc 0 N, gfun χ z P k * psiChar χ (N / k)‖ := norm_add_le _ _
      _ ≤ (‖-(A - Sgsum χ z P N * (Real.log N : ℂ))‖
            + ‖A - z * ∑ d ∈ Ioc 0 N, (Λ d : ℂ) * χ d * Sgsum χ z P (N / d)‖)
          + ‖z * ∑ k ∈ Ioc 0 N, gfun χ z P k * psiChar χ (N / k)‖ := by
            gcongr; exact norm_add_le _ _
      _ ≤ ((N:ℝ) + C * N) + ∑ k ∈ Ioc 0 N, ‖psiChar χ (N / k)‖ := by
            rw [norm_neg, norm_mul, hz, one_mul]
            gcongr
            · exact norm_sum_gfun_mul_log_sub hχ hz N
            · exact hC N
      _ = (1 + C) * N + ∑ k ∈ Ioc 0 N, ‖psiChar χ (N / k)‖ := by ring
  -- conclude
  have key : ∀ δ : ℝ, 0 < δ → ∃ M : ℕ, ∀ N : ℕ, M ≤ N → ‖Sgsum χ z P N‖ ≤ δ * N := by
    intro δ hδ
    obtain ⟨N₁, hN₁⟩ := sum_psiChar_div_le hχ hpsi (δ / 2) (by linarith)
    have hlogtop : Tendsto (fun n : ℕ => Real.log n) atTop atTop :=
      Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
    obtain ⟨N₂, hN₂⟩ :=
      (hlogtop.eventually_ge_atTop (max 1 (2 * (1 + C) / δ))).exists_forall_of_atTop
    refine ⟨max (max N₁ N₂) 1, fun N hN ↦ ?_⟩
    have hN1 : 1 ≤ N := le_trans (le_max_right _ _) hN
    have hNR : (1:ℝ) ≤ N := by exact_mod_cast hN1
    have hlogge := hN₂ N (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN)
    have hlog1 : (1:ℝ) ≤ Real.log N := le_trans (le_max_left _ _) hlogge
    have hlogC : 2 * (1 + C) / δ ≤ Real.log N := le_trans (le_max_right _ _) hlogge
    have hsum := hN₁ N (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN)
    have hm := master N
    have h2 : (1 + C) * (N:ℝ) ≤ (δ / 2) * N * Real.log N := by
      have hlin : 2 * (1 + C) ≤ δ * Real.log N := by
        rw [div_le_iff₀ hδ] at hlogC; linarith
      nlinarith
    have h3 : ‖Sgsum χ z P N‖ * Real.log N ≤ δ * N * Real.log N := by linarith
    nlinarith [norm_nonneg (Sgsum χ z P N)]
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨M, hM⟩ := key (ε / 2) (by linarith)
  refine ⟨max M 1, fun N hN ↦ ?_⟩
  have hN1 : 1 ≤ N := le_trans (le_max_right _ _) hN
  have hNR : (1:ℝ) ≤ N := by exact_mod_cast hN1
  have hNpos : (0:ℝ) < N := by linarith
  have h4 := hM N (le_trans (le_max_left _ _) hN)
  rw [Complex.dist_eq, sub_zero, norm_div, Complex.norm_natCast, div_lt_iff₀ hNpos]
  nlinarith

end NormalNumbers.DelangeSlot
