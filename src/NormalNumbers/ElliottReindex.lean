import NormalNumbers.ElliottProgression

/-!
# The progression reindexing

Leaf 2, Case B: the *analytic* half of the progression substitution that
`NormalNumbers.ElliottProgression` left open.

Fix a modulus `q ≥ 1` and a residue `n₀ < q`.  Summing a bounded function against the harmonic
weight over `{n ∈ (X/W, X] : n ≡ n₀ (mod q)}` is, after the substitution `n = qk + n₀`, the same
as `(1/q)` times a **genuine** `elliottLogWindow` sum in `k` at the reduced scale
`X' = ⌊(X − n₀)/q⌋` and the ratio `W' = min W X'` — up to an **absolute** error `≤ 4`.

Three things are compared, and each costs an absolute constant:

* the residue term `n = n₀` itself (`k = 0`), of weight `1/n₀ ≤ 1`;
* the weight, `1/(qk+n₀)` versus `1/(qk)`: the difference telescopes, because `n₀ < q` gives
  `1/(qk) − 1/(qk+n₀) ≤ 1/(qk) − 1/(q(k+1))`, so the total is at most `1/q ≤ 1`;
* the window, `Ioc m X'` versus `Ioc (X'/W') X'`: the two lower endpoints differ by at most `2`
  (`progLow_le_div` and `div_le_progLow_add_two`), and each stray term has weight `≤ 1`.

Since an absolute error is absorbed by taking the threshold `A₀` large (the target being
`ε log W`), this is exactly what Case B needs.
-/

open scoped BigOperators
open Finset

namespace NormalNumbers.ElliottReindex

open Erdos67b

noncomputable section

/-- The reduced scale `X' = ⌊(X − n₀)/q⌋`: the largest `k` with `qk + n₀ ≤ X`. -/
def progScale (X n₀ q : ℕ) : ℕ := (X - n₀) / q

/-- The lower endpoint in `k`: the largest `k` with `W(qk+n₀) ≤ X`. -/
def progLow (X W n₀ q : ℕ) : ℕ := (X - W * n₀) / (W * q)

/-! ## The substitution is a bijection of index sets -/

theorem progression_image {q n₀ X W : ℕ} (hq : 0 < q) (hn₀ : n₀ < q) (hW : 0 < W) :
    ((elliottLogWindow X W).filter fun n => n % q = n₀ ∧ q ≤ n)
      = (Finset.Ioc (progLow X W n₀ q) (progScale X n₀ q)).image fun k => q * k + n₀ := by
  classical
  have hWq : 0 < W * q := Nat.mul_pos hW hq
  ext n
  simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_Ioc, mem_elliottLogWindow]
  constructor
  · rintro ⟨⟨hnpos, hnX, hnW⟩, hmod, hqn⟩
    have hsplit : q * (n / q) + n₀ = n := by
      conv_rhs => rw [← Nat.div_add_mod n q, hmod]
    set k := n / q with hkdef
    have hk1 : 1 ≤ k := (Nat.one_le_div_iff hq).mpr hqn
    refine ⟨k, ⟨?_, ?_⟩, hsplit⟩
    · rw [progLow, Nat.div_lt_iff_lt_mul hWq]
      have hWn : W * n = k * (W * q) + W * n₀ := by rw [← hsplit]; ring
      rcases le_or_gt (W * n₀) X with h | h
      · rw [Nat.sub_lt_iff_lt_add h, ← hWn]
        exact hnW
      · rw [Nat.sub_eq_zero_of_le h.le]
        exact Nat.mul_pos hk1 hWq
    · rw [progScale, Nat.le_div_iff_mul_le hq]
      refine Nat.le_sub_of_add_le ?_
      rw [mul_comm k q, hsplit]
      exact hnX
  · rintro ⟨k, ⟨hk1, hk2⟩, rfl⟩
    have hk1' : 1 ≤ k := by
      by_contra hc
      have : k = 0 := by omega
      omega
    have hqk : q ≤ q * k := Nat.le_mul_of_pos_right q hk1'
    have hupper : q * k ≤ X - n₀ := by
      have h := (Nat.le_div_iff_mul_le hq).mp hk2
      rw [mul_comm] at h
      exact h
    have hXn₀ : n₀ ≤ X := by
      have h := (Nat.le_div_iff_mul_le hq).mp (le_trans hk1' hk2)
      omega
    have hnX : q * k + n₀ ≤ X := Nat.add_le_of_le_sub hXn₀ hupper
    have hlow : X - W * n₀ < k * (W * q) := by
      have := hk1
      rw [progLow] at this
      exact (Nat.div_lt_iff_lt_mul hWq).mp this
    refine ⟨⟨by omega, hnX, ?_⟩, ?_, by omega⟩
    · have hWn : W * (q * k + n₀) = k * (W * q) + W * n₀ := by ring
      rcases le_or_gt (W * n₀) X with h | h
      · rw [hWn]
        exact (Nat.sub_lt_iff_lt_add h).mp hlow
      · refine lt_of_lt_of_le h ?_
        exact Nat.mul_le_mul_left W (by omega)
    · rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hn₀]

/-- The weighted sum over the progression, reindexed. -/
theorem sum_progression_eq {q n₀ X W : ℕ} (hq : 0 < q) (hn₀ : n₀ < q) (hW : 0 < W)
    (F : ℕ → ℂ) :
    ∑ n ∈ (elliottLogWindow X W).filter (fun n => n % q = n₀ ∧ q ≤ n), F n
      = ∑ k ∈ Finset.Ioc (progLow X W n₀ q) (progScale X n₀ q), F (q * k + n₀) := by
  classical
  rw [progression_image hq hn₀ hW, Finset.sum_image]
  intro x _ y _ hxy
  simp only at hxy
  exact Nat.eq_of_mul_eq_mul_left hq (Nat.add_right_cancel hxy)

/-! ## The window comparison -/

/-- The progression's lower endpoint is at most the window's. -/
theorem progLow_le_div {q n₀ X W : ℕ} (hq : 0 < q) (hW : 0 < W) :
    progLow X W n₀ q ≤ progScale X n₀ q / min W (progScale X n₀ q) := by
  have hkey : progLow X W n₀ q ≤ progScale X n₀ q / W := by
    rw [progLow, progScale, Nat.div_div_eq_div_mul]
    have h1 : X - W * n₀ ≤ X - n₀ := by
      have : n₀ ≤ W * n₀ := Nat.le_mul_of_pos_left n₀ hW
      omega
    calc (X - W * n₀) / (W * q) ≤ (X - n₀) / (W * q) := Nat.div_le_div_right h1
      _ = (X - n₀) / (q * W) := by rw [Nat.mul_comm]
  refine le_trans hkey ?_
  rcases Nat.eq_zero_or_pos (min W (progScale X n₀ q)) with h | h
  · have hX0 : progScale X n₀ q = 0 := by omega
    rw [hX0] at hkey ⊢
    simpa using hkey
  · exact Nat.div_le_div_left (min_le_left _ _) h

/-- …and by at most `2` less. -/
theorem div_le_progLow_add_two {q n₀ X W : ℕ} (hq : 0 < q) (hn₀ : n₀ < q) (hW : 0 < W) :
    progScale X n₀ q / min W (progScale X n₀ q) ≤ progLow X W n₀ q + 2 := by
  rcases le_or_gt (progScale X n₀ q) W with h | h
  · rw [min_eq_right h]
    rcases Nat.eq_zero_or_pos (progScale X n₀ q) with h0 | h0
    · rw [h0]; simp
    · rw [Nat.div_self h0]; omega
  · rw [min_eq_left h.le]
    have hWq : 0 < W * q := Nat.mul_pos hW hq
    have hkey : X - n₀ ≤ (X - W * n₀) + W * q := by
      have h2 : W * n₀ ≤ W * q := Nat.mul_le_mul_left W (by omega)
      rcases le_or_gt (W * n₀) X with hc | hc
      · have h1 : n₀ ≤ W * n₀ := Nat.le_mul_of_pos_left n₀ hW
        omega
      · omega
    have : progScale X n₀ q / W = (X - n₀) / (W * q) := by
      rw [progScale, Nat.div_div_eq_div_mul, Nat.mul_comm]
    rw [this, progLow]
    calc (X - n₀) / (W * q) ≤ ((X - W * n₀) + W * q) / (W * q) := Nat.div_le_div_right hkey
      _ = (X - W * n₀) / (W * q) + 1 := Nat.add_div_right _ hWq
      _ ≤ (X - W * n₀) / (W * q) + 2 := by omega

/-! ## The telescoping weight comparison -/

theorem sum_Icc_telescope (f : ℕ → ℝ) (N : ℕ) :
    ∑ k ∈ Finset.Icc 1 N, (f k - f (k + 1)) = f 1 - f (N + 1) := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [Finset.sum_Icc_succ_top (by omega), ih]
      ring

/-! ## The main estimate -/

/-- **The progression reindexing, with an absolute error.**  The harmonically weighted sum of a
`1`-bounded `G` over the residue class `n ≡ n₀ (mod q)` inside the window `(X/W, X]` equals
`1/q` times a genuine `elliottLogWindow` sum at the reduced scale, up to an error at most `4` —
independent of `q`, `n₀`, `X`, `W` and `G`. -/
theorem norm_sum_sub_reindexed_le {q n₀ X W : ℕ} (hq : 0 < q) (hn₀ : n₀ < q) (hW : 0 < W)
    (G : ℕ → ℂ) (hG : ∀ k, ‖G k‖ ≤ 1) :
    ‖(∑ n ∈ (elliottLogWindow X W).filter (fun n => n % q = n₀),
        ((n : ℝ)⁻¹ : ℂ) * G ((n - n₀) / q))
      - ((q : ℝ)⁻¹ : ℂ) * ∑ k ∈ elliottLogWindow (progScale X n₀ q) (min W (progScale X n₀ q)),
          ((k : ℝ)⁻¹ : ℂ) * G k‖ ≤ 4 := by
  classical
  set N : ℕ := progScale X n₀ q with hN
  set M : ℕ := progLow X W n₀ q with hM
  set W' : ℕ := min W N with hW'
  set V : Finset ℕ := elliottLogWindow N W' with hV
  set F : ℕ → ℂ := fun n => ((n : ℝ)⁻¹ : ℂ) * G ((n - n₀) / q) with hF
  -- the residue term `k = 0`
  have hsplit : ∑ n ∈ (elliottLogWindow X W).filter (fun n => n % q = n₀), F n
      = (∑ n ∈ (elliottLogWindow X W).filter (fun n => n % q = n₀ ∧ q ≤ n), F n)
        + ∑ n ∈ (elliottLogWindow X W).filter (fun n => n % q = n₀ ∧ ¬ q ≤ n), F n := by
    rw [← Finset.filter_filter, ← Finset.filter_filter]
    exact (Finset.sum_filter_add_sum_filter_not _ _ _).symm
  have hsmall : ‖∑ n ∈ (elliottLogWindow X W).filter (fun n => n % q = n₀ ∧ ¬ q ≤ n), F n‖
      ≤ 1 := by
    have hsub : ((elliottLogWindow X W).filter fun n => n % q = n₀ ∧ ¬ q ≤ n) ⊆ {n₀} := by
      intro n hn
      obtain ⟨-, hmod, hlt⟩ := Finset.mem_filter.mp hn
      have : n < q := by omega
      rw [Nat.mod_eq_of_lt this] at hmod
      simp [hmod]
    have hterm : ∀ n ∈ (elliottLogWindow X W).filter (fun n => n % q = n₀ ∧ ¬ q ≤ n),
        ‖F n‖ ≤ 1 := by
      intro n hn
      have hnpos : 0 < n := (mem_elliottLogWindow.mp (Finset.mem_filter.mp hn).1).1
      have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hnpos
      rw [hF]
      simp only [norm_mul, Complex.norm_real, norm_inv, Real.norm_natCast]
      have h1 : ((n : ℝ))⁻¹ ≤ 1 := by
        rw [inv_le_one_iff₀]; right; exact hn1
      calc (n : ℝ)⁻¹ * ‖G ((n - n₀) / q)‖ ≤ 1 * 1 :=
            mul_le_mul h1 (hG _) (norm_nonneg _) (by norm_num)
        _ = 1 := by ring
    calc ‖_‖ ≤ ∑ n ∈ _, ‖F n‖ := norm_sum_le _ _
      _ ≤ ∑ _n ∈ (elliottLogWindow X W).filter (fun n => n % q = n₀ ∧ ¬ q ≤ n), (1 : ℝ) :=
          Finset.sum_le_sum hterm
      _ = (((elliottLogWindow X W).filter fun n => n % q = n₀ ∧ ¬ q ≤ n).card : ℝ) := by simp
      _ ≤ 1 := by
          have := Finset.card_le_card hsub
          simp only [Finset.card_singleton] at this
          exact_mod_cast this
  -- the reindexed main sum
  have hmain : ∑ n ∈ (elliottLogWindow X W).filter (fun n => n % q = n₀ ∧ q ≤ n), F n
      = ∑ k ∈ Finset.Ioc M N, ((((q * k + n₀ : ℕ) : ℝ))⁻¹ : ℂ) * G k := by
    rw [sum_progression_eq hq hn₀ hW F]
    refine Finset.sum_congr rfl fun k _ => ?_
    have hkk : (q * k + n₀ - n₀) / q = k := by
      rw [Nat.add_sub_cancel, Nat.mul_div_cancel_left k hq]
    simp only [hF, hkk]
  rcases Nat.eq_zero_or_pos N with hN0 | hNpos
  · -- degenerate: the reduced scale is `0`, both the `Ioc` and the window are empty
    have hIoc : Finset.Ioc M N = ∅ := by
      rw [hN0]; simp
    have hVempty : V = ∅ := by
      have hW'0 : W' = 0 := by rw [hW', hN0]; simp
      rw [hV, hW'0, hN0]
      ext n
      simp [mem_elliottLogWindow]
    rw [hsplit, hmain, hIoc, hVempty]
    simp only [Finset.sum_empty, zero_add, mul_zero, sub_zero]
    linarith [hsmall]
  · have hW'pos : 0 < W' := by
      rw [hW']
      omega
    have hVeq : V = Finset.Ioc (N / W') N := by
      rw [hV, elliottLogWindow_eq_Ioc hW'pos]
    have hMle : M ≤ N / W' := by
      rw [hM, hN, hW']
      exact progLow_le_div hq hW
    have hMle2 : N / W' ≤ M + 2 := by
      rw [hM, hN, hW']
      exact div_le_progLow_add_two hq hn₀ hW
    have hsub : V ⊆ Finset.Ioc M N := by
      rw [hVeq]
      exact Finset.Ioc_subset_Ioc_left hMle
    -- decompose
    set a : ℕ → ℂ := fun k => ((((q * k + n₀ : ℕ) : ℝ))⁻¹ : ℂ) * G k with ha
    set b : ℕ → ℂ := fun k => ((((q * k : ℕ) : ℝ))⁻¹ : ℂ) * G k with hb
    have hbV : ((q : ℝ)⁻¹ : ℂ) * ∑ k ∈ V, ((k : ℝ)⁻¹ : ℂ) * G k = ∑ k ∈ V, b k := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun k hk => ?_
      have hkpos : 0 < k := (mem_elliottLogWindow.mp hk).1
      simp only [hb]
      push_cast
      rw [mul_inv]
      ring
    have hdecomp : (∑ k ∈ Finset.Ioc M N, a k) - ∑ k ∈ V, b k
        = (∑ k ∈ Finset.Ioc M N, (a k - b k)) + ∑ k ∈ Finset.Ioc M N \ V, b k := by
      have hb2 : ∑ k ∈ Finset.Ioc M N, b k
          = ∑ k ∈ Finset.Ioc M N \ V, b k + ∑ k ∈ V, b k := (Finset.sum_sdiff hsub).symm
      rw [Finset.sum_sub_distrib, hb2]
      ring
    -- bound the weight difference
    have hdiff : ∑ k ∈ Finset.Ioc M N, ‖a k - b k‖ ≤ 1 := by
      have hterm : ∀ k ∈ Finset.Ioc M N,
          ‖a k - b k‖ ≤ ((q * k : ℕ) : ℝ)⁻¹ - ((q * (k + 1) : ℕ) : ℝ)⁻¹ := by
        intro k hk
        have hkpos : 0 < k := by
          have := (Finset.mem_Ioc.mp hk).1
          omega
        have hqk : (0 : ℝ) < ((q * k : ℕ) : ℝ) := by
          have : 0 < q * k := Nat.mul_pos hq hkpos
          exact_mod_cast this
        have hqk2 : ((q * k : ℕ) : ℝ) ≤ ((q * k + n₀ : ℕ) : ℝ) := by
          have : q * k ≤ q * k + n₀ := by omega
          exact_mod_cast this
        have hqk3 : ((q * k + n₀ : ℕ) : ℝ) ≤ ((q * (k + 1) : ℕ) : ℝ) := by
          have : q * k + n₀ ≤ q * (k + 1) := by
            have : q * (k + 1) = q * k + q := by ring
            omega
          exact_mod_cast this
        have hineq : ((q * (k + 1) : ℕ) : ℝ)⁻¹ ≤ ((q * k + n₀ : ℕ) : ℝ)⁻¹ :=
          by gcongr
        have hineq2 : ((q * k + n₀ : ℕ) : ℝ)⁻¹ ≤ ((q * k : ℕ) : ℝ)⁻¹ := by gcongr
        have hrw : a k - b k =
            (((((q * k + n₀ : ℕ) : ℝ))⁻¹ - (((q * k : ℕ) : ℝ))⁻¹ : ℝ) : ℂ) * G k := by
          rw [ha, hb]
          push_cast
          ring
        rw [hrw, norm_mul, Complex.norm_real, Real.norm_eq_abs]
        have hGk := hG k
        have habs : |(((q * k + n₀ : ℕ) : ℝ))⁻¹ - (((q * k : ℕ) : ℝ))⁻¹|
            = ((q * k : ℕ) : ℝ)⁻¹ - ((q * k + n₀ : ℕ) : ℝ)⁻¹ := by
          rw [abs_sub_comm, abs_of_nonneg (by linarith)]
        rw [habs]
        have hnn : (0 : ℝ) ≤ ((q * k : ℕ) : ℝ)⁻¹ - ((q * k + n₀ : ℕ) : ℝ)⁻¹ := by linarith
        calc (((q * k : ℕ) : ℝ)⁻¹ - ((q * k + n₀ : ℕ) : ℝ)⁻¹) * ‖G k‖
            ≤ (((q * k : ℕ) : ℝ)⁻¹ - ((q * k + n₀ : ℕ) : ℝ)⁻¹) * 1 :=
              mul_le_mul_of_nonneg_left hGk hnn
          _ ≤ ((q * k : ℕ) : ℝ)⁻¹ - ((q * (k + 1) : ℕ) : ℝ)⁻¹ := by
              rw [mul_one]; linarith
      refine le_trans (Finset.sum_le_sum hterm) ?_
      have hsub2 : Finset.Ioc M N ⊆ Finset.Icc 1 N := by
        intro k hk
        obtain ⟨h1, h2⟩ := Finset.mem_Ioc.mp hk
        exact Finset.mem_Icc.mpr ⟨by omega, h2⟩
      have hnn : ∀ k ∈ Finset.Icc 1 N,
          (0 : ℝ) ≤ ((q * k : ℕ) : ℝ)⁻¹ - ((q * (k + 1) : ℕ) : ℝ)⁻¹ := by
        intro k hk
        have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hk).1
        have h1 : ((q * k : ℕ) : ℝ) ≤ ((q * (k + 1) : ℕ) : ℝ) := by
          have : q * k ≤ q * (k + 1) := Nat.mul_le_mul_left q (by omega)
          exact_mod_cast this
        have h2 : (0 : ℝ) < ((q * k : ℕ) : ℝ) := by
          have : 0 < q * k := Nat.mul_pos hq (by omega)
          exact_mod_cast this
        have : ((q * (k + 1) : ℕ) : ℝ)⁻¹ ≤ ((q * k : ℕ) : ℝ)⁻¹ := by gcongr
        linarith
      refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub2 fun i hi _ => hnn i hi) ?_
      have hT := sum_Icc_telescope (fun k => ((q * k : ℕ) : ℝ)⁻¹) N
      rw [hT]
      have h1 : ((q * 1 : ℕ) : ℝ)⁻¹ ≤ 1 := by
        have : (1 : ℝ) ≤ ((q * 1 : ℕ) : ℝ) := by
          have : 1 ≤ q * 1 := by omega
          exact_mod_cast this
        rw [inv_le_one_iff₀]; right; exact this
      have h2 : (0 : ℝ) ≤ ((q * (N + 1) : ℕ) : ℝ)⁻¹ := by positivity
      linarith
    -- bound the window discrepancy
    have hstray : ∑ k ∈ Finset.Ioc M N \ V, ‖b k‖ ≤ 2 := by
      have hcard : (Finset.Ioc M N \ V).card ≤ 2 := by
        have hsub3 : Finset.Ioc M N \ V ⊆ Finset.Ioc M (N / W') := by
          intro k hk
          obtain ⟨hk1, hk2⟩ := Finset.mem_sdiff.mp hk
          obtain ⟨h1, h2⟩ := Finset.mem_Ioc.mp hk1
          rw [hVeq, Finset.mem_Ioc] at hk2
          refine Finset.mem_Ioc.mpr ⟨h1, ?_⟩
          by_contra hc
          exact hk2 ⟨by omega, h2⟩
        have := Finset.card_le_card hsub3
        simp only [Nat.card_Ioc] at this
        omega
      have hterm : ∀ k ∈ Finset.Ioc M N \ V, ‖b k‖ ≤ 1 := by
        intro k hk
        have hkpos : 0 < k := by
          have := (Finset.mem_Ioc.mp (Finset.mem_sdiff.mp hk).1).1
          omega
        simp only [hb]
        rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs]
        have h1 : |(((q * k : ℕ) : ℝ))|⁻¹ ≤ 1 := by
          have hpos : (1 : ℝ) ≤ ((q * k : ℕ) : ℝ) := by
            have : 1 ≤ q * k := Nat.one_le_iff_ne_zero.mpr (by positivity)
            exact_mod_cast this
          rw [abs_of_nonneg (by positivity), inv_le_one_iff₀]
          right; exact hpos
        calc |(((q * k : ℕ) : ℝ))|⁻¹ * ‖G k‖ ≤ 1 * 1 :=
              mul_le_mul h1 (hG k) (norm_nonneg _) (by norm_num)
          _ = 1 := by ring
      calc ∑ k ∈ Finset.Ioc M N \ V, ‖b k‖
          ≤ ∑ _k ∈ Finset.Ioc M N \ V, (1 : ℝ) := Finset.sum_le_sum hterm
        _ = ((Finset.Ioc M N \ V).card : ℝ) := by simp
        _ ≤ 2 := by exact_mod_cast hcard
    -- assemble
    rw [hsplit, hmain, hbV]
    have hfinal : (∑ k ∈ Finset.Ioc M N, a k) + (∑ n ∈ (elliottLogWindow X W).filter
        (fun n => n % q = n₀ ∧ ¬ q ≤ n), F n) - ∑ k ∈ V, b k
        = ((∑ k ∈ Finset.Ioc M N, (a k - b k)) + ∑ k ∈ Finset.Ioc M N \ V, b k)
          + ∑ n ∈ (elliottLogWindow X W).filter (fun n => n % q = n₀ ∧ ¬ q ≤ n), F n := by
      rw [← hdecomp]; ring
    rw [hfinal]
    have h1 : ‖∑ k ∈ Finset.Ioc M N, (a k - b k)‖ ≤ 1 :=
      le_trans (norm_sum_le _ _) hdiff
    have h2 : ‖∑ k ∈ Finset.Ioc M N \ V, b k‖ ≤ 2 :=
      le_trans (norm_sum_le _ _) hstray
    calc ‖_‖ ≤ ‖(∑ k ∈ Finset.Ioc M N, (a k - b k)) + ∑ k ∈ Finset.Ioc M N \ V, b k‖
          + ‖∑ n ∈ (elliottLogWindow X W).filter (fun n => n % q = n₀ ∧ ¬ q ≤ n), F n‖ :=
        norm_add_le _ _
      _ ≤ (1 + 2) + 1 := by
          have := norm_add_le (∑ k ∈ Finset.Ioc M N, (a k - b k))
            (∑ k ∈ Finset.Ioc M N \ V, b k)
          linarith
      _ = 4 := by norm_num

end

end NormalNumbers.ElliottReindex
