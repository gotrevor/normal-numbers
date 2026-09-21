import NormalNumbers.G4WiringSummatory

/-!
# Splitting the summatory node: shifts off the singleton clause

`RoughSummatory h` (the sole analytic input of the G₄ window law off the Chowla sector, frozen in
`G4WiringSummatory.lean`) bundles two clauses of very different depth:

* the **prefix** clause, about `∑_{m<M} ∏_{j=1}^{k} z_j^{ω_{>2}(m+j)}` — a genuine
  *multi-shift* Selberg–Delange statement (a correlation of `k` multiplicative functions at `k`
  distinct shifts);
* the **singleton** clause, about `∑_{m<M} z_k^{ω_{>2}(m+k)}` — ONE multiplicative function at ONE
  shift.

This file removes the shift from the singleton clause.  The shift-free object
`classOmegaSum z b M = ∑_{n < M, n ≡ b (2)} z^{ω_{>2}(n)}` is a textbook Landau–Selberg–Delange
summatory function (Tenenbaum II.5.3 with the Euler factor at `2` split off), so the node
`SDShiftFree h` below is *classical*, not open.  The theorem `roughSummatory_of_split` shows

  `RoughSummatoryPrefix h → SDShiftFree h → RoughSummatory h`,

isolating the multi-shift prefix clause as the only genuinely open piece.

The shift is removed by reindexing `n = m + k` and paying the two boundary blocks
`[0,k)` and `[M, M+k)`, of total size `2k`.  This is affordable **because the node's own error
budget is `C·4^{-k}·M/log M` and `k ≤ windowJ M = ⌊log₂ log₂ M⌋ + 1`**, so `4^k ≤ 4(log₂ M)²` and
`2k` is smaller than the budget by a power of `log M`.  (`shift_cost_small`.)
-/

open Filter Topology Finset
open scoped BigOperators

namespace NormalNumbers.G4

open NormalNumbers.PrimeLambert

/-! ### The shift-free summatory function -/

/-- The site phase base: `z_k = e(h/4^k)`. -/
noncomputable def sdBase (h : ℤ) (k : ℕ) : ℂ := ePhase ((h : ℝ) / (4 : ℝ) ^ k)

lemma norm_sdBase (h : ℤ) (k : ℕ) : ‖sdBase h k‖ = 1 := norm_ePhase _

lemma sdExponent_singleton_eq (h : ℤ) (k : ℕ) : sdExponent h {k} = sdBase h k - 1 := by
  rw [sdExponent, Finset.sum_singleton, sdBase]

/-- `e(n·x) = e(x)^n`. -/
lemma ePhase_nat_mul (x : ℝ) (n : ℕ) : ePhase ((n : ℝ) * x) = ePhase x ^ n := by
  induction n with
  | zero => simp [ePhase, Complex.exp_zero]
  | succ n ih =>
      have : ((n : ℝ) + 1) * x = (n : ℝ) * x + x := by ring
      push_cast
      rw [this, ePhase_add, ih, pow_succ]

/-- The rough phase at one site is a power of the base. -/
lemma roughPhase_eq_pow (h : ℤ) (k m : ℕ) :
    roughPhase h k m = sdBase h k ^ omegaAbove 2 (m + k) := by
  rw [roughPhase, sdBase, ← ePhase_nat_mul]
  congr 1
  ring

/-- **The shift-free summatory function.**  `∑_{n<M, n ≡ b (2)} z^{ω_{>2}(n)}`. -/
noncomputable def classOmegaSum (z : ℂ) (b M : ℕ) : ℂ :=
  ∑ n ∈ (Finset.range M).filter (fun n => n % 2 = b), z ^ omegaAbove 2 n

/-- The summand as a total function, so that index-set surgery is available. -/
private noncomputable def cls (z : ℂ) (b n : ℕ) : ℂ :=
  if n % 2 = b then z ^ omegaAbove 2 n else 0

private lemma norm_cls_le {z : ℂ} (hz : ‖z‖ = 1) (b n : ℕ) : ‖cls z b n‖ ≤ 1 := by
  rw [cls]
  split
  · rw [norm_pow, hz, one_pow]
  · simp

private lemma sum_cls_Ico (z : ℂ) (b a c : ℕ) :
    ∑ n ∈ (Finset.Ico a c).filter (fun n => n % 2 = b), z ^ omegaAbove 2 n
      = ∑ n ∈ Finset.Ico a c, cls z b n := by
  rw [Finset.sum_filter]
  exact Finset.sum_congr rfl (fun n _ => rfl)

private lemma classOmegaSum_eq_sum_cls (z : ℂ) (b M : ℕ) :
    classOmegaSum z b M = ∑ n ∈ Finset.Ico 0 M, cls z b n := by
  rw [classOmegaSum, ← sum_cls_Ico]
  congr 1
  rw [Finset.range_eq_Ico]

/-- Reindexing `n = m + k`: the shifted class sum is a class sum over a shifted interval. -/
private lemma roughClassSum_singleton_eq (h : ℤ) (k a M : ℕ) (ha : a < 2) :
    roughClassSum h {k} a M
      = ∑ n ∈ Finset.Ico k (M + k), cls (sdBase h k) ((a + k) % 2) n := by
  have hstep : ∀ m : ℕ,
      cls (sdBase h k) ((a + k) % 2) (m + k)
        = if m % 2 = a then sdBase h k ^ omegaAbove 2 (m + k) else 0 := by
    intro m
    rw [cls]
    by_cases hm : m % 2 = a
    · rw [if_pos hm, if_pos]
      omega
    · rw [if_neg hm, if_neg]
      omega
  have hre := Finset.sum_Ico_add' (fun n => cls (sdBase h k) ((a + k) % 2) n) 0 M k
  rw [Nat.zero_add] at hre
  rw [← hre, roughClassSum, Finset.sum_filter, Finset.range_eq_Ico]
  exact Finset.sum_congr rfl (fun m _ => by
    rw [hstep m, roughProd_singleton, roughPhase_eq_pow])

/-- The two boundary blocks cost at most `2k`. -/
private lemma norm_shift_block {z : ℂ} (hz : ‖z‖ = 1) (b k M : ℕ) :
    ‖(∑ n ∈ Finset.Ico k (M + k), cls z b n) - ∑ n ∈ Finset.Ico 0 M, cls z b n‖ ≤ 2 * k := by
  have hsplit1 : ∑ n ∈ Finset.Ico 0 (M + k), cls z b n
      = ∑ n ∈ Finset.Ico 0 k, cls z b n + ∑ n ∈ Finset.Ico k (M + k), cls z b n :=
    (Finset.sum_Ico_consecutive _ (Nat.zero_le k) (Nat.le_add_left k M)).symm
  have hsplit2 : ∑ n ∈ Finset.Ico 0 (M + k), cls z b n
      = ∑ n ∈ Finset.Ico 0 M, cls z b n + ∑ n ∈ Finset.Ico M (M + k), cls z b n :=
    (Finset.sum_Ico_consecutive _ (Nat.zero_le M) (Nat.le_add_right M k)).symm
  have hdiff : (∑ n ∈ Finset.Ico k (M + k), cls z b n) - ∑ n ∈ Finset.Ico 0 M, cls z b n
      = ∑ n ∈ Finset.Ico M (M + k), cls z b n - ∑ n ∈ Finset.Ico 0 k, cls z b n := by
    have := hsplit1.symm.trans hsplit2
    linear_combination this
  have hbound : ∀ p q : ℕ, ‖∑ n ∈ Finset.Ico p q, cls z b n‖ ≤ (q - p : ℕ) := by
    intro p q
    calc ‖∑ n ∈ Finset.Ico p q, cls z b n‖
        ≤ ∑ n ∈ Finset.Ico p q, ‖cls z b n‖ := norm_sum_le _ _
      _ ≤ ∑ _n ∈ Finset.Ico p q, (1 : ℝ) :=
          Finset.sum_le_sum (fun n _ => norm_cls_le hz b n)
      _ = ((q - p : ℕ) : ℝ) := by simp
  have h1 := hbound M (M + k)
  have h2 := hbound 0 k
  rw [Nat.add_sub_cancel_left] at h1
  rw [Nat.sub_zero] at h2
  rw [hdiff]
  calc ‖∑ n ∈ Finset.Ico M (M + k), cls z b n - ∑ n ∈ Finset.Ico 0 k, cls z b n‖
      ≤ ‖∑ n ∈ Finset.Ico M (M + k), cls z b n‖ + ‖∑ n ∈ Finset.Ico 0 k, cls z b n‖ :=
        norm_sub_le _ _
    _ ≤ (k : ℝ) + k := add_le_add h1 h2
    _ = 2 * k := by ring

/-- **Shift removal.**  The singleton class sum differs from the shift-free class sum by at most
the two boundary blocks `[0,k)` and `[M, M+k)`. -/
lemma norm_roughClassSum_sub_classOmegaSum (h : ℤ) (k a M : ℕ) (ha : a < 2) :
    ‖roughClassSum h {k} a M - classOmegaSum (sdBase h k) ((a + k) % 2) M‖ ≤ 2 * k := by
  rw [roughClassSum_singleton_eq h k a M ha, classOmegaSum_eq_sum_cls]
  exact norm_shift_block (norm_sdBase h k) _ _ _

/-! ### The shift cost is negligible against the node's error budget -/

lemma natLog_two_le_two_log {M : ℕ} (hM : 1 ≤ M) :
    (Nat.log 2 M : ℝ) ≤ 2 * Real.log M := by
  have h1 : (2:ℕ) ^ (Nat.log 2 M) ≤ M := Nat.pow_log_le_self 2 (by omega)
  have h1' : ((2:ℝ)) ^ (Nat.log 2 M) ≤ (M : ℝ) := by exact_mod_cast h1
  have h2 : Real.log ((2:ℝ) ^ (Nat.log 2 M)) ≤ Real.log M :=
    Real.log_le_log (by positivity) h1'
  rw [Real.log_pow] at h2
  have hl2 : (1:ℝ)/2 ≤ Real.log 2 := by
    have := Real.log_two_gt_d9; linarith
  have hcast : (0:ℝ) ≤ (Nat.log 2 M : ℝ) := Nat.cast_nonneg _
  nlinarith

/-- `2k·4^k` is only polylogarithmic on the window range `k ≤ windowJ M`. -/
lemma two_mul_pow_four_le {M k : ℕ} (hM : 2 ≤ M) (hk : k ≤ windowJ M) :
    2 * (k:ℝ) * 4 ^ k ≤ 64 * Real.log M ^ 3 := by
  set Λ : ℕ := Nat.log 2 M with hΛ
  have hΛ1 : 1 ≤ Λ := by
    rw [hΛ]; exact Nat.log_pos (by norm_num) hM
  have hΛM : ((2:ℝ)) ^ Λ ≤ (M:ℝ) := by
    have := Nat.pow_log_le_self 2 (show M ≠ 0 by omega)
    rw [← hΛ] at this
    exact_mod_cast this
  have hW : windowJ M = Nat.log 2 Λ + 1 := by rw [windowJ, hΛ]
  have hlogΛ : ((2:ℝ)) ^ (Nat.log 2 Λ) ≤ (Λ:ℝ) := by
    have := Nat.pow_log_le_self 2 (show Λ ≠ 0 by omega)
    exact_mod_cast this
  have hkW : k ≤ Nat.log 2 Λ + 1 := by omega
  have hkΛ : k ≤ Λ := by
    have : Nat.log 2 Λ < Λ := Nat.log_lt_self 2 (by omega)
    omega
  have hsq : ((2:ℝ) ^ (Nat.log 2 Λ)) ^ 2 = (4:ℝ) ^ (Nat.log 2 Λ) := by
    rw [← pow_mul, mul_comm, pow_mul]
    norm_num
  have hpow : (4:ℝ) ^ k ≤ 4 * (Λ:ℝ) ^ 2 := by
    have hle : (4:ℝ) ^ k ≤ (4:ℝ) ^ (Nat.log 2 Λ + 1) := pow_le_pow_right₀ (by norm_num) hkW
    have h2 : (4:ℝ) ^ (Nat.log 2 Λ + 1) = 4 * ((2:ℝ) ^ (Nat.log 2 Λ)) ^ 2 := by
      rw [hsq, pow_succ]; ring
    have hnn : (0:ℝ) ≤ (2:ℝ) ^ (Nat.log 2 Λ) := by positivity
    have : ((2:ℝ) ^ (Nat.log 2 Λ)) ^ 2 ≤ (Λ:ℝ) ^ 2 := by
      apply pow_le_pow_left₀ hnn hlogΛ
    linarith [hle, h2.le, h2.ge]
  have hLΛ : (Λ:ℝ) ≤ 2 * Real.log M := natLog_two_le_two_log (by omega)
  have hLpos : 0 ≤ Real.log M := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ M))
  have hkR : (k:ℝ) ≤ (Λ:ℝ) := by exact_mod_cast hkΛ
  have hΛpos : (0:ℝ) ≤ (Λ:ℝ) := Nat.cast_nonneg _
  calc 2 * (k:ℝ) * 4 ^ k ≤ 2 * (Λ:ℝ) * 4 ^ k := by
        nlinarith [pow_pos (show (0:ℝ) < 4 by norm_num) k, hkR]
    _ ≤ 2 * (Λ:ℝ) * (4 * (Λ:ℝ)^2) := by nlinarith [hΛpos, hpow]
    _ = 8 * (Λ:ℝ)^3 := by ring
    _ ≤ 8 * (2 * Real.log M)^3 := by
        have := pow_le_pow_left₀ hΛpos hLΛ 3
        linarith
    _ = 64 * Real.log M ^ 3 := by ring

/-- `log M ≥ 1` past `M = 8`. -/
lemma one_le_log_of_eight {M : ℕ} (hM : 8 ≤ M) : 1 ≤ Real.log M := by
  have h1 : Real.log 8 ≤ Real.log M :=
    Real.log_le_log (by norm_num) (by exact_mod_cast hM)
  have h8 : Real.log 8 = 3 * Real.log 2 := by
    rw [show (8:ℝ) = 2^3 by norm_num, Real.log_pow]; push_cast; ring
  have := Real.log_two_gt_d9
  linarith

/-- **The shift cost is negligible.**  Eventually, on the whole window range, the boundary cost
`2k` of shift removal is below the node's own error budget `C·4^{-k}·M·(log M)^{κ_k−1}/log M`. -/
lemma shift_cost_small (h : ℤ) {C : ℝ} (hC : 0 < C) :
    ∀ᶠ M : ℕ in atTop, ∀ k, 1 ≤ k → k ≤ windowJ M →
      2 * (k:ℝ)
        ≤ C * ((1:ℝ)/4)^k / Real.log M * ((M:ℝ) * Real.log M ^ (sdExponent h {k}).re) := by
  set m : ℕ := ⌈4 * Real.pi * |(h:ℝ)|⌉₊ with hmdef
  have hmb : ∀ k : ℕ, -(m:ℝ) ≤ (sdExponent h {k}).re := by
    intro k
    apply neg_bound_le_re
    refine le_trans (norm_sdExponent_singleton h k) (le_trans ?_ (Nat.le_ceil _))
    have h4 : ((1:ℝ)/4)^k ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    have hnn : (0:ℝ) ≤ 4 * Real.pi * |(h:ℝ)| := by positivity
    exact mul_le_of_le_one_right hnn h4
  filter_upwards [eventually_ge_atTop 8,
    eventually_rpow_log_le (m+3) (C/64) (by positivity)] with M hM8 hMr
  intro k hk1 hkW
  set L : ℝ := Real.log M with hLdef
  have hL1 : 1 ≤ L := one_le_log_of_eight hM8
  have hLpos : 0 < L := lt_of_lt_of_le one_pos hL1
  have hMpos : (0:ℝ) ≤ (M:ℝ) := Nat.cast_nonneg _
  have hre : L ^ (-(m:ℝ)) ≤ L ^ (sdExponent h {k}).re :=
    Real.rpow_le_rpow_of_exponent_le hL1 (hmb k)
  have hcoef : 0 < C * ((1:ℝ)/4)^k / L := by positivity
  -- reduce to the `L^{-m}` bound
  have hmono : C * ((1:ℝ)/4)^k / L * ((M:ℝ) * L ^ (-(m:ℝ)))
      ≤ C * ((1:ℝ)/4)^k / L * ((M:ℝ) * L ^ (sdExponent h {k}).re) := by
    apply mul_le_mul_of_nonneg_left _ hcoef.le
    exact mul_le_mul_of_nonneg_left hre hMpos
  refine le_trans ?_ hmono
  -- the arithmetic core
  have hLm : L * L ^ (m:ℝ) = L ^ ((m:ℝ) + 1) := by
    rw [Real.rpow_add hLpos, Real.rpow_one]; ring
  have hkey : 2 * (k:ℝ) * (4 ^ k * (L * L ^ (m:ℝ))) ≤ C * (M:ℝ) := by
    have h1 : 2 * (k:ℝ) * 4 ^ k ≤ 64 * L ^ 3 :=
      two_mul_pow_four_le (by omega) hkW
    have hpos : (0:ℝ) < L ^ ((m:ℝ) + 1) := Real.rpow_pos_of_pos hLpos _
    have h2 : 2 * (k:ℝ) * (4 ^ k * (L * L ^ (m:ℝ)))
        = (2 * (k:ℝ) * 4 ^ k) * L ^ ((m:ℝ)+1) := by rw [← hLm]; ring
    have h3 : (2 * (k:ℝ) * 4 ^ k) * L ^ ((m:ℝ)+1) ≤ (64 * L ^ 3) * L ^ ((m:ℝ)+1) :=
      mul_le_mul_of_nonneg_right h1 hpos.le
    have h4 : (64 * L ^ 3) * L ^ ((m:ℝ)+1) = 64 * L ^ (((m+3 : ℕ):ℝ) + 1) := by
      have e1 : (L:ℝ) ^ (3:ℕ) = L ^ ((3:ℝ)) := by
        rw [show ((3:ℝ)) = ((3:ℕ):ℝ) from by norm_num, Real.rpow_natCast]
      rw [e1, mul_assoc, ← Real.rpow_add hLpos]
      push_cast
      ring_nf
    have h5 : 64 * L ^ (((m+3 : ℕ):ℝ) + 1) ≤ 64 * (C/64 * (M:ℝ)) := by
      have := mul_le_mul_of_nonneg_left hMr (by norm_num : (0:ℝ) ≤ 64)
      exact this
    have h6 : 64 * (C/64 * (M:ℝ)) = C * (M:ℝ) := by field_simp
    rw [h2]
    linarith [h3, h4.le, h4.ge, h5, h6.le, h6.ge]
  have hfac : 0 < (4:ℝ) ^ k * (L * L ^ (m:ℝ)) := by positivity
  have hX : C * ((1:ℝ)/4)^k / L * ((M:ℝ) * L ^ (-(m:ℝ)))
      = C * (M:ℝ) / ((4:ℝ) ^ k * (L * L ^ (m:ℝ))) := by
    rw [Real.rpow_neg hLpos.le, div_pow, one_pow]
    have h4k : ((4:ℝ) ^ k) ≠ 0 := by positivity
    have hLm0 : (L ^ (m:ℝ)) ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hLpos _)
    field_simp
  rw [hX, le_div_iff₀ hfac]
  linarith [hkey]

/-! ### The two sub-nodes -/

/-- **The multi-shift (prefix) node.**  Selberg–Delange for a *correlation* of `k` multiplicative
functions at the `k` distinct shifts `1,…,k`.  This is the genuinely open piece. -/
def RoughSummatoryPrefix (h : ℤ) : Prop :=
  ∃ (c : ℕ → ℂ) (B C δ : ℝ), 0 ≤ C ∧ 0 < δ ∧
    (∀ k, ‖c k‖ ≤ B) ∧ (∀ k, 1 ≤ k → δ ≤ ‖c k‖) ∧
    ∀ᶠ M : ℕ in atTop, ∀ a, a < 2 → ∀ k, 1 ≤ k → k ≤ windowJ M →
      ‖roughClassSum h (Finset.Icc 1 k) a M - sdMain (c k) (sdExponent h (Finset.Icc 1 k)) M‖
        ≤ C / Real.log M * ((M : ℝ) * Real.log M ^ (sdExponent h (Finset.Icc 1 k)).re)

/-- **The shift-free (singleton) node.**  Landau–Selberg–Delange for the single multiplicative
function `n ↦ z_k^{ω_{>2}(n)}` on each parity class — no shift, no correlation.  This is the
classical statement (Tenenbaum II.5.3 with the Euler factor at `2` split off). -/
def SDShiftFree (h : ℤ) : Prop :=
  ∃ (c : ℕ → ℂ) (B C δ : ℝ), 0 ≤ C ∧ 0 < δ ∧
    (∀ k, ‖c k‖ ≤ B) ∧ (∀ k, 1 ≤ k → δ ≤ ‖c k‖) ∧
    (∀ k, 1 ≤ k → ‖c k - 1‖ ≤ B * ((1:ℝ)/4) ^ k) ∧
    ∀ᶠ M : ℕ in atTop, ∀ b, b < 2 → ∀ k, 1 ≤ k → k ≤ windowJ M →
      ‖classOmegaSum (sdBase h k) b M - sdMain (c k) (sdExponent h {k}) M‖
        ≤ C * ((1:ℝ)/4)^k / Real.log M * ((M : ℝ) * Real.log M ^ (sdExponent h {k}).re)

/-! ### Gluing the two constant families -/

noncomputable def combinedConst (cPre cSing : ℕ → ℂ) (s : Finset ℕ) : ℂ :=
  if s = Finset.Icc 1 (s.sup id) then cPre (s.sup id) else cSing (s.sup id)

private lemma sup_Icc (k : ℕ) (hk : 1 ≤ k) : (Finset.Icc 1 k).sup id = k := by
  refine le_antisymm (Finset.sup_le ?_) ?_
  · intro n hn
    exact (Finset.mem_Icc.mp hn).2
  · exact Finset.le_sup (f := id) (Finset.mem_Icc.mpr ⟨hk, le_rfl⟩)

lemma combinedConst_Icc (cPre cSing : ℕ → ℂ) (k : ℕ) (hk : 1 ≤ k) :
    combinedConst cPre cSing (Finset.Icc 1 k) = cPre k := by
  rw [combinedConst, sup_Icc k hk, if_pos rfl]

lemma combinedConst_singleton (cPre cSing : ℕ → ℂ) (k : ℕ) (hk : 2 ≤ k) :
    combinedConst cPre cSing {k} = cSing k := by
  have hsup : ({k} : Finset ℕ).sup id = k := by simp
  rw [combinedConst, hsup, if_neg]
  intro hcon
  have h1 : (1:ℕ) ∈ Finset.Icc 1 k := Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩
  rw [← hcon] at h1
  simp at h1
  omega

lemma Icc_one_one : Finset.Icc 1 1 = ({1} : Finset ℕ) := by decide +kernel

/-! ### The split -/

private lemma bound_mono {c1 c2 L X : ℝ} (hL : 0 < L) (hX : 0 ≤ X) (hc : c1 ≤ c2) :
    c1 / L * X ≤ c2 / L * X := by
  gcongr

/-- **The split.**  The summatory node follows from the multi-shift prefix node together with the
shift-free (classical Selberg–Delange) singleton node. -/
theorem roughSummatory_of_split (h : ℤ)
    (hpre : RoughSummatoryPrefix h) (hsf : SDShiftFree h) : RoughSummatory h := by
  obtain ⟨cP, BP, CP, δP, hCP, hδP, hBP, hδPk, hPre⟩ := hpre
  obtain ⟨cS, BS, CS, δS, hCS, hδS, hBS, hδSk, hS1, hSing⟩ := hsf
  refine ⟨combinedConst cP cS, max (max BP BS) (4 * ‖cP 1 - 1‖), 4 * CP + CS + 1,
    min δP δS, by linarith, lt_min hδP hδS, ?_, ?_, ?_, ?_⟩
  · intro s
    rw [combinedConst]
    split
    · exact le_trans (hBP _) (le_trans (le_max_left _ _) (le_max_left _ _))
    · exact le_trans (hBS _) (le_trans (le_max_right _ _) (le_max_left _ _))
  · intro k hk1
    refine ⟨?_, ?_⟩
    · rw [combinedConst_Icc _ _ k hk1]
      exact le_trans (min_le_left _ _) (hδPk k hk1)
    · rcases Nat.lt_or_ge k 2 with hk2 | hk2
      · have hk : k = 1 := by omega
        subst hk
        rw [← Icc_one_one, combinedConst_Icc _ _ 1 le_rfl]
        exact le_trans (min_le_left _ _) (hδPk 1 le_rfl)
      · rw [combinedConst_singleton _ _ k hk2]
        exact le_trans (min_le_right _ _) (hδSk k (by omega))
  · intro k hk1
    rcases Nat.lt_or_ge k 2 with hk2 | hk2
    · have hk : k = 1 := by omega
      subst hk
      rw [← Icc_one_one, combinedConst_Icc _ _ 1 le_rfl]
      have h4 : 4 * ‖cP 1 - 1‖ ≤ max (max BP BS) (4 * ‖cP 1 - 1‖) := le_max_right _ _
      have : ((1:ℝ)/4) ^ (1:ℕ) = 1/4 := by norm_num
      rw [this]
      linarith
    · rw [combinedConst_singleton _ _ k hk2]
      refine le_trans (hS1 k (by omega)) ?_
      have hp : (0:ℝ) ≤ ((1:ℝ)/4) ^ k := by positivity
      have : BS ≤ max (max BP BS) (4 * ‖cP 1 - 1‖) :=
        le_trans (le_max_right _ _) (le_max_left _ _)
      exact mul_le_mul_of_nonneg_right this hp
  · filter_upwards [hPre, hSing, shift_cost_small h (show (0:ℝ) < 1 by norm_num),
      eventually_ge_atTop 8] with M hP hS hshift hM8
    intro a ha k hk1 hkW
    have hL1 : 1 ≤ Real.log M := one_le_log_of_eight hM8
    have hLpos : 0 < Real.log M := lt_of_lt_of_le one_pos hL1
    have hXpre : (0:ℝ) ≤ (M:ℝ) * Real.log M ^ (sdExponent h (Finset.Icc 1 k)).re := by positivity
    have hXsing : (0:ℝ) ≤ (M:ℝ) * Real.log M ^ (sdExponent h {k}).re := by positivity
    refine ⟨?_, ?_⟩
    · rw [combinedConst_Icc _ _ k hk1]
      refine le_trans (hP a ha k hk1 hkW) (bound_mono hLpos hXpre (by linarith))
    · rcases Nat.lt_or_ge k 2 with hk2 | hk2
      · have hk : k = 1 := by omega
        subst hk
        rw [← Icc_one_one, combinedConst_Icc _ _ 1 le_rfl]
        refine le_trans (hP a ha 1 le_rfl hkW) ?_
        have hq : ((1:ℝ)/4) ^ (1:ℕ) = 1/4 := by norm_num
        rw [hq]
        refine bound_mono hLpos (by rw [Icc_one_one] at hXpre ⊢; exact hXpre) ?_
        linarith
      · rw [combinedConst_singleton _ _ k hk2]
        have hb : (a + k) % 2 < 2 := Nat.mod_lt _ (by norm_num)
        have hnode := hS ((a + k) % 2) hb k hk1 hkW
        have hshiftk := hshift k hk1 hkW
        have hsplit :
            ‖roughClassSum h {k} a M - sdMain (cS k) (sdExponent h {k}) M‖
              ≤ ‖roughClassSum h {k} a M - classOmegaSum (sdBase h k) ((a + k) % 2) M‖
                + ‖classOmegaSum (sdBase h k) ((a + k) % 2) M
                    - sdMain (cS k) (sdExponent h {k}) M‖ := by
          have : roughClassSum h {k} a M - sdMain (cS k) (sdExponent h {k}) M
              = (roughClassSum h {k} a M - classOmegaSum (sdBase h k) ((a + k) % 2) M)
                + (classOmegaSum (sdBase h k) ((a + k) % 2) M
                    - sdMain (cS k) (sdExponent h {k}) M) := by ring
          rw [this]
          exact norm_add_le _ _
      -- assemble
        have hshift' := norm_roughClassSum_sub_classOmegaSum h k a M ha
        have hsum : ‖roughClassSum h {k} a M - sdMain (cS k) (sdExponent h {k}) M‖
            ≤ 1 * ((1:ℝ)/4)^k / Real.log M * ((M:ℝ) * Real.log M ^ (sdExponent h {k}).re)
              + CS * ((1:ℝ)/4)^k / Real.log M
                  * ((M:ℝ) * Real.log M ^ (sdExponent h {k}).re) := by
          refine le_trans hsplit (add_le_add (le_trans hshift' ?_) hnode)
          simpa using hshiftk
        refine le_trans hsum ?_
        have hfac : (1:ℝ) * ((1:ℝ)/4)^k / Real.log M
              * ((M:ℝ) * Real.log M ^ (sdExponent h {k}).re)
            + CS * ((1:ℝ)/4)^k / Real.log M
                * ((M:ℝ) * Real.log M ^ (sdExponent h {k}).re)
            = (1 + CS) * ((1:ℝ)/4)^k / Real.log M
                * ((M:ℝ) * Real.log M ^ (sdExponent h {k}).re) := by ring
        rw [hfac]
        have hp : (0:ℝ) ≤ ((1:ℝ)/4) ^ k := by positivity
        have hmul : (1 + CS) * ((1:ℝ)/4)^k ≤ (4 * CP + CS + 1) * ((1:ℝ)/4)^k := by
          apply mul_le_mul_of_nonneg_right _ hp
          linarith
        exact bound_mono hLpos hXsing hmul

/-- **Headline, re-based on the split.**  The G₄ window law off the Chowla sector now rests on the
multi-shift prefix node plus the *classical* shift-free singleton node. -/
theorem isNormal_G4_of_shiftSplit
    (hPre : ∀ h : ℤ, h ≠ 0 → ¬ ChowlaSector h → RoughSummatoryPrefix h)
    (hSF : ∀ h : ℤ, h ≠ 0 → ¬ ChowlaSector h → SDShiftFree h)
    (hCh : ∀ h : ℤ, h ≠ 0 → ChowlaSector h → WindowDecay h)
    (hSite : SiteDecayFull) : IsNormal 4 (primeLambertAtBase 4) :=
  isNormal_G4_of_summatory
    (fun h hh hc => roughSummatory_of_split h (hPre h hh hc) (hSF h hh hc)) hCh hSite

/-! ### How small the prefix main term really is

The prefix main term is `c·M·(log M)^{κ_k}` with `κ_k = sdExponent h (Icc 1 k)`, and the node's
error budget is `C·M·(log M)^{Re κ_k − 1}`.  The size of `Re κ_k` therefore controls every attack on
the prefix node.  It is **at most `−1`** as soon as `k` passes the `4`-adic valuation of `h`:
at the first site `j` with `4^j ∤ h` the phase `e(h/4^j)` is a quarter turn or a half turn, so
`Re(e(h/4^j) − 1) ≤ −1`, and every other site contributes `≤ 0`.

Consequence (recorded in `PENDING_WORK.md`): a *pointwise* truncation of the shift product at
`j₀ ≤ windowJ M` costs `≍ M·(log log M)·4^{-j₀} ≥ M (log log M)/(4 (log₂ M)²)`, while the budget is
at most `C·M·(log M)^{-2}`.  The truncation route to the multi-shift node is refuted. -/

lemma re_ePhase (x : ℝ) : (ePhase x).re = Real.cos (2 * Real.pi * x) := by
  have : ePhase x = Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I) := by
    unfold ePhase; congr 1; push_cast; ring
  rw [this, Complex.exp_ofReal_mul_I_re]

/-- A quarter- or half-turn phase has non-positive real part. -/
lemma re_ePhase_quarter_nonpos {r : ℤ} (hr : ¬ (4:ℤ) ∣ r) :
    (ePhase ((r : ℝ) / 4)).re ≤ 0 := by
  have hsplit : (r : ℝ) / 4 = ((r % 4 : ℤ) : ℝ) / 4 + ((r / 4 : ℤ) : ℝ) := by
    have hr' : (r : ℝ) = ((r % 4 : ℤ) : ℝ) + 4 * ((r / 4 : ℤ) : ℝ) := by
      have h2 : r = r % 4 + 4 * (r / 4) := by omega
      exact_mod_cast congrArg (fun z : ℤ => (z : ℝ)) h2
    rw [hr']; ring
  rw [hsplit, ePhase_add_int, re_ePhase]
  have hlt : r % 4 < 4 := Int.emod_lt_of_pos r (by norm_num)
  have hge : 0 ≤ r % 4 := Int.emod_nonneg r (by norm_num)
  have hne : r % 4 ≠ 0 := fun hc => hr (Int.dvd_of_emod_eq_zero hc)
  interval_cases hm : (r % 4)
  · exact absurd rfl hne
  · have : 2 * Real.pi * (((1:ℤ) : ℝ) / 4) = Real.pi / 2 := by push_cast; ring
    rw [this, Real.cos_pi_div_two]
  · have : 2 * Real.pi * (((2:ℤ) : ℝ) / 4) = Real.pi := by push_cast; ring
    rw [this, Real.cos_pi]; norm_num
  · have : 2 * Real.pi * (((3:ℤ) : ℝ) / 4) = Real.pi + Real.pi / 2 := by push_cast; ring
    rw [this, Real.cos_add_pi_div_two, Real.sin_pi]
    norm_num

/-- **The prefix exponent has real part `≤ −1` past the `4`-adic valuation of `h`.** -/
theorem exists_re_sdExponent_le_neg_one (h : ℤ) (hh : h ≠ 0) :
    ∃ t : ℕ, 1 ≤ t ∧ ∀ k : ℕ, t ≤ k → (sdExponent h (Finset.Icc 1 k)).re ≤ -1 := by
  have hex : ∃ j : ℕ, 1 ≤ j ∧ ¬ ((4:ℤ) ^ j ∣ h) := by
    obtain ⟨j, hj⟩ := pow_unbounded_of_one_lt (|(h:ℤ)| : ℤ) (by norm_num : (1:ℤ) < 4)
    refine ⟨j + 1, by omega, ?_⟩
    intro hdvd
    have h1 : (4:ℤ) ^ (j+1) ≤ |h| := Int.le_of_dvd (abs_pos.mpr hh) ((dvd_abs _ _).mpr hdvd)
    have h2 : (4:ℤ) ^ j ≤ (4:ℤ) ^ (j+1) := by
      apply pow_le_pow_right₀ (by norm_num); omega
    omega
  classical
  set P : ℕ → Prop := fun j => 1 ≤ j ∧ ¬ ((4:ℤ) ^ j ∣ h) with hP
  have hdec : DecidablePred P := fun _ => inferInstance
  obtain ⟨t, htP, htmin⟩ := Nat.findX (p := P) hex
  refine ⟨t, htP.1, ?_⟩
  intro k hk
  -- the site `t` contributes `≤ -1`
  have hprev : (4:ℤ) ^ (t - 1) ∣ h := by
    rcases Nat.eq_or_lt_of_le htP.1 with h1 | h1
    · rw [← h1]; simp
    · by_contra hcon
      exact absurd ⟨by omega, hcon⟩ (htmin (t-1) (by omega))
  obtain ⟨r, hr⟩ := hprev
  have hr4 : ¬ ((4:ℤ) ∣ r) := by
    intro ⟨u, hu⟩
    refine htP.2 ⟨u, ?_⟩
    rw [hr, hu, ← mul_assoc, ← pow_succ]
    congr 2
    omega
  have hval : ((h : ℝ)) / (4:ℝ) ^ t = (r : ℝ) / 4 := by
    have hcast : ((h : ℝ)) = ((4:ℝ) ^ (t-1)) * (r : ℝ) := by
      rw [hr]; push_cast; ring
    rw [hcast]
    have : ((4:ℝ) ^ t) = (4:ℝ) ^ (t-1) * 4 := by
      rw [← pow_succ]; congr 1; omega
    rw [this]
    have h4 : ((4:ℝ) ^ (t-1)) ≠ 0 := by positivity
    field_simp
  have hsite : (ePhase ((h:ℝ) / (4:ℝ)^t) - 1).re ≤ -1 := by
    rw [Complex.sub_re, Complex.one_re, hval]
    have := re_ePhase_quarter_nonpos hr4
    linarith
  -- every site contributes `≤ 0`
  have hall : ∀ j : ℕ, (ePhase ((h:ℝ) / (4:ℝ)^j) - 1).re ≤ 0 := by
    intro j
    rw [Complex.sub_re, Complex.one_re, re_ePhase]
    have := Real.cos_le_one (2 * Real.pi * ((h:ℝ)/(4:ℝ)^j))
    linarith
  have hmem : t ∈ Finset.Icc 1 k := Finset.mem_Icc.mpr ⟨htP.1, hk⟩
  rw [sdExponent, Complex.re_sum]
  calc ∑ j ∈ Finset.Icc 1 k, (ePhase ((h:ℝ) / (4:ℝ)^j) - 1).re
      ≤ ∑ j ∈ Finset.Icc 1 k, (if j = t then (-1 : ℝ) else 0) := by
        refine Finset.sum_le_sum (fun j _ => ?_)
        by_cases hj : j = t
        · rw [if_pos hj, hj]; exact hsite
        · rw [if_neg hj]; exact hall j
    _ = -1 := by rw [Finset.sum_ite_eq' (Finset.Icc 1 k) t (fun _ => (-1:ℝ))]; simp [hmem]

/-! ### Reducing the shift-free node to the ODD class alone

`omega_{>2}` is blind to the factor `2`, so halving is an exact bijection between the even residues
below `M` and ALL residues below `⌈M/2⌉`:

  `E(M) = E(⌈M/2⌉) + O(⌈M/2⌉)`  (`classOmegaSum_zero_eq`).

Iterating `V` times expresses the even class as `Σ_{v≤V} O(⌈M/2^v⌉) + E(⌈M/2^V⌉)`; taking
`2^V ≈ √M` makes the remainder `≤ √M + 1`, negligible against the node's budget.  So the whole
shift-free node is carried by the ODD-class summatory function alone — the primitive
Landau–Selberg–Delange object. -/

/-- `⌈M/2⌉`, written so that `2*m < M ↔ m < halfCeil M` for `M ≥ 1`. -/
def halfCeil (M : ℕ) : ℕ := (M - 1) / 2 + 1

lemma lt_halfCeil_iff {M m : ℕ} (hM : 1 ≤ M) : m < halfCeil M ↔ 2 * m < M := by
  rw [halfCeil]; omega

lemma omegaAbove_two_double' (m : ℕ) : omegaAbove 2 (2 * m) = omegaAbove 2 m := by
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm; rfl
  · exact omegaAbove_two_double m (by omega)

/-- **Halving is exact.**  The even class below `M` is everything below `⌈M/2⌉`. -/
lemma classOmegaSum_zero_eq (z : ℂ) {M : ℕ} (hM : 1 ≤ M) :
    classOmegaSum z 0 M = classOmegaSum z 0 (halfCeil M) + classOmegaSum z 1 (halfCeil M) := by
  classical
  have hbij : classOmegaSum z 0 M
      = ∑ m ∈ Finset.range (halfCeil M), z ^ omegaAbove 2 m := by
    rw [classOmegaSum]
    refine Finset.sum_nbij' (fun n => n / 2) (fun m => 2 * m) ?_ ?_ ?_ ?_ ?_
    · intro n hn
      rw [Finset.mem_filter, Finset.mem_range] at hn
      rw [Finset.mem_range, lt_halfCeil_iff hM]
      omega
    · intro m hm
      rw [Finset.mem_range, lt_halfCeil_iff hM] at hm
      rw [Finset.mem_filter, Finset.mem_range]
      omega
    · intro n hn
      rw [Finset.mem_filter, Finset.mem_range] at hn
      omega
    · intro m _
      omega
    · intro n hn
      rw [Finset.mem_filter, Finset.mem_range] at hn
      have h2 : 2 * (n / 2) = n := by omega
      rw [← omegaAbove_two_double' (n / 2), h2]
  rw [hbij, classOmegaSum, classOmegaSum, ← Finset.sum_filter_add_sum_filter_not
    (Finset.range (halfCeil M)) (fun n => n % 2 = 0)]
  congr 1
  refine Finset.sum_congr (Finset.filter_congr (fun n _ => ?_)) (fun _ _ => rfl)
  constructor <;> intro hh <;> omega

/-- The `v`-th iterated halving of `M`. -/
def halfIter (M v : ℕ) : ℕ := halfCeil^[v] M

@[simp] lemma halfIter_zero (M : ℕ) : halfIter M 0 = M := rfl

lemma halfIter_succ (M v : ℕ) : halfIter M (v + 1) = halfCeil (halfIter M v) := by
  rw [halfIter, halfIter, Function.iterate_succ_apply']

lemma one_le_halfCeil (M : ℕ) : 1 ≤ halfCeil M := by rw [halfCeil]; omega

lemma one_le_halfIter {M : ℕ} (hM : 1 ≤ M) (v : ℕ) : 1 ≤ halfIter M v := by
  cases v with
  | zero => simpa using hM
  | succ v => rw [halfIter_succ]; exact one_le_halfCeil _

/-- `2^v · ⌈M/2^v⌉ ≤ M + 2^v − 1`. -/
lemma halfIter_bound {M : ℕ} (hM : 1 ≤ M) (v : ℕ) : 2 ^ v * halfIter M v + 1 ≤ M + 2 ^ v := by
  induction v with
  | zero => simp
  | succ v ih =>
      have hY : 1 ≤ halfIter M v := one_le_halfIter hM v
      have hstep : 2 * halfCeil (halfIter M v) ≤ halfIter M v + 1 := by
        rw [halfCeil]; omega
      have := Nat.mul_le_mul_left (2 ^ v) hstep
      rw [halfIter_succ]
      have hpow : (2:ℕ) ^ (v + 1) = 2 ^ v * 2 := by rw [pow_succ]
      rw [hpow]
      nlinarith [ih, this, Nat.one_le_two_pow (n := v)]

/-- **Unrolling the halving recursion.**  The even class is a finite sum of ODD-class sums at the
halved scales, plus an even-class remainder at scale `⌈M/2^V⌉`. -/
lemma classOmegaSum_zero_unroll (z : ℂ) {M : ℕ} (hM : 1 ≤ M) (V : ℕ) :
    classOmegaSum z 0 M
      = (∑ v ∈ Finset.Icc 1 V, classOmegaSum z 1 (halfIter M v))
        + classOmegaSum z 0 (halfIter M V) := by
  induction V with
  | zero => simp
  | succ V ih =>
      rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ V + 1), ih,
        classOmegaSum_zero_eq z (one_le_halfIter hM V), ← halfIter_succ]
      ring

/-! ### Tools for the 2-adic assembly -/

/-- The downward companion of `norm_ofReal_one_add_cpow_sub_one_le`: a *shrinking* scale factor.
`‖(1−y)^κ − 1‖ ≤ 4‖κ‖y` for `0 ≤ y ≤ 1/2`. -/
theorem norm_ofReal_one_sub_cpow_sub_one_le (y : ℝ) (hy : 0 ≤ y) (hy2 : y ≤ 1/2) (κ : ℂ)
    (hκy : ‖κ‖ * (2 * y) ≤ 1) : ‖(((1 - y : ℝ)) : ℂ) ^ κ - 1‖ ≤ 4 * (‖κ‖ * y) := by
  have h1y : (0:ℝ) < 1 - y := by linarith
  have hne : (((1 - y : ℝ)) : ℂ) ≠ 0 := by
    simpa using (Complex.ofReal_ne_zero.mpr h1y.ne')
  rw [Complex.cpow_def_of_ne_zero hne]
  have hlog : Complex.log (((1 - y : ℝ)) : ℂ) = ((Real.log (1 - y) : ℝ) : ℂ) :=
    (Complex.ofReal_log h1y.le).symm
  rw [hlog]
  -- `|log (1−y)| ≤ 2y` for `y ≤ 1/2`
  have hlognp : Real.log (1 - y) ≤ 0 := Real.log_nonpos (by linarith) (by linarith)
  have hlogge : -(2 * y) ≤ Real.log (1 - y) := by
    have hkey : Real.log (1 - y) = -Real.log (1 / (1 - y)) := by
      rw [one_div, Real.log_inv]; ring
    have hb : Real.log (1 / (1 - y)) ≤ 2 * y := by
      have h1 : (1:ℝ) / (1 - y) ≤ 1 + 2 * y := by
        rw [div_le_iff₀ h1y]
        nlinarith
      have h2 : Real.log (1 / (1 - y)) ≤ Real.log (1 + 2 * y) :=
        Real.log_le_log (by positivity) h1
      have h3 : Real.log (1 + 2 * y) ≤ 2 * y := by
        have := Real.log_le_sub_one_of_pos (show (0:ℝ) < 1 + 2 * y by linarith)
        linarith
      linarith
    rw [hkey]; linarith
  have habs : |Real.log (1 - y)| ≤ 2 * y := abs_le.mpr ⟨hlogge, by linarith⟩
  have hw : ‖((Real.log (1 - y) : ℝ) : ℂ) * κ‖ ≤ ‖κ‖ * (2 * y) := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_comm]
    exact mul_le_mul_of_nonneg_left habs (norm_nonneg _)
  have hw1 : ‖((Real.log (1 - y) : ℝ) : ℂ) * κ‖ ≤ 1 := le_trans hw hκy
  refine (Complex.norm_exp_sub_one_le hw1).trans ?_
  linarith [hw]

/-- `M ≤ 2^v · ⌈M/2^v⌉`. -/
lemma le_halfIter_bound (M v : ℕ) : M ≤ 2 ^ v * halfIter M v := by
  induction v with
  | zero => simp
  | succ v ih =>
      have hstep : halfIter M v ≤ 2 * halfCeil (halfIter M v) := by
        rw [halfCeil]; omega
      have := Nat.mul_le_mul_left (2 ^ v) hstep
      rw [halfIter_succ, pow_succ]
      calc M ≤ 2 ^ v * halfIter M v := ih
        _ ≤ 2 ^ v * (2 * halfCeil (halfIter M v)) := this
        _ = 2 ^ v * 2 * halfCeil (halfIter M v) := by ring

/-- The halved scale loses at most `v·log 2` of the logarithm. -/
lemma log_halfIter_ge {M : ℕ} (hM : 1 ≤ M) (v : ℕ) :
    Real.log M - v * Real.log 2 ≤ Real.log (halfIter M v) := by
  have hpos : 0 < halfIter M v := one_le_halfIter hM v
  have hle : (M : ℝ) ≤ (2:ℝ) ^ v * (halfIter M v : ℝ) := by
    have := le_halfIter_bound M v
    exact_mod_cast (by exact_mod_cast this : (M:ℝ) ≤ ((2 ^ v * halfIter M v : ℕ) : ℝ))
  have h1 : Real.log M ≤ Real.log ((2:ℝ) ^ v * (halfIter M v : ℝ)) :=
    Real.log_le_log (by exact_mod_cast hM) hle
  rw [Real.log_mul (by positivity) (by exact_mod_cast hpos.ne'), Real.log_pow] at h1
  linarith

/-- The halved scale is at least `M/2^v`. -/
lemma halfIter_ge_div {M : ℕ} (v : ℕ) : (M : ℝ) / 2 ^ v ≤ (halfIter M v : ℝ) := by
  have hle : (M : ℝ) ≤ (2:ℝ) ^ v * (halfIter M v : ℝ) := by
    have := le_halfIter_bound M v
    exact_mod_cast (by exact_mod_cast this : (M:ℝ) ≤ ((2 ^ v * halfIter M v : ℕ) : ℝ))
  rw [div_le_iff₀ (by positivity)]
  linarith

/-- The halved scale is at most `M/2^v + 1`. -/
lemma halfIter_le_div {M : ℕ} (hM : 1 ≤ M) (v : ℕ) : (halfIter M v : ℝ) ≤ (M : ℝ) / 2 ^ v + 1 := by
  have hb := halfIter_bound hM v
  have hb' : ((2 ^ v * halfIter M v : ℕ) : ℝ) + 1 ≤ (M : ℝ) + ((2 ^ v : ℕ) : ℝ) := by
    exact_mod_cast hb
  push_cast at hb'
  have hp : (0:ℝ) < (2:ℝ) ^ v := by positivity
  rw [← sub_le_iff_le_add, le_div_iff₀ hp]
  nlinarith [hb']

/-! ### The primitive node: the ODD class alone -/

/-- **The primitive Landau–Selberg–Delange node.**  One multiplicative function `n ↦ z_k^{ω_{>2}(n)}`,
no shift, ODD arguments only.  The `windowJ X + 2` range (rather than `windowJ X`) is what lets the
halving recursion feed the node back at the halved scales `X ≈ M/2^v ≥ √M`. -/
def SDOdd (h : ℤ) : Prop :=
  ∃ (c : ℕ → ℂ) (B C δ : ℝ), 0 ≤ C ∧ 0 < δ ∧
    (∀ k, ‖c k‖ ≤ B) ∧ (∀ k, 1 ≤ k → δ ≤ ‖c k‖) ∧
    (∀ k, 1 ≤ k → ‖c k - 1‖ ≤ B * ((1:ℝ)/4) ^ k) ∧
    ∀ᶠ X : ℕ in atTop, ∀ k, 1 ≤ k → k ≤ windowJ X + 2 →
      ‖classOmegaSum (sdBase h k) 1 X - sdMain (c k) (sdExponent h {k}) X‖
        ≤ C * ((1:ℝ)/4)^k / Real.log X * ((X : ℝ) * Real.log X ^ (sdExponent h {k}).re)

/-- **OPEN SUB-GOAL — the 2-adic assembly.**  Disclosed `sorry`: the even class inherits the odd
class's asymptotic *with the same constant*, by `classOmegaSum_zero_unroll` with `2^V ≈ √M`.

The three pieces, all elementary but each a real estimate:

* **main terms.**  `Σ_{v=1}^{V} (c/2)·M_v·(log M_v)^κ = (c/2)·M·(log M)^κ + O(‖κ‖ M (log M)^{Re κ−1})`,
  using `M_v = M/2^v + O(1)`, `Σ_{v≥1} 2^{-v} = 1` (this is *where the equal-constants-on-both-
  parity-classes clause comes from*, so it is derived, not assumed), and
  `(log M_v)^κ = (log M)^κ (1 + O(‖κ‖ v / log M))`; the sum `Σ v 2^{-v} = 2` converges.
  Since `‖κ‖ = ‖sdExponent h {k}‖ ≤ 4π|h| 4^{-k}`, this error has exactly the node's shape.
* **error terms.**  `Σ_{v=1}^{V} C 4^{-k} M_v (log M_v)^{Re κ−1} ≤ 8C 4^{-k} (M+V) (log M)^{Re κ−1}`,
  using `log M_v ≥ ½ log M` on the retained range `M_v ≥ √M/2` and `Re κ ≥ −2`.
* **remainder.**  `‖E(M_V)‖ ≤ M_V ≤ √M + 1`, negligible since the budget is
  `≥ M (log M)^{−3}/(4 (log₂ M)²)`.

Applicability of the node at the halved scales needs `k ≤ windowJ M_v + 2`, which is why `SDOdd`
carries the `+2`: `M_v ≥ √M/2` gives `windowJ M_v ≥ windowJ M − 2`. -/
theorem exists_classOmegaSum_zero_bound (h : ℤ) (c : ℕ → ℂ) (B C : ℝ)
    (hC : 0 ≤ C) (hB : ∀ k, ‖c k‖ ≤ B)
    (hodd : ∀ᶠ X : ℕ in atTop, ∀ k, 1 ≤ k → k ≤ windowJ X + 2 →
      ‖classOmegaSum (sdBase h k) 1 X - sdMain (c k) (sdExponent h {k}) X‖
        ≤ C * ((1:ℝ)/4)^k / Real.log X * ((X : ℝ) * Real.log X ^ (sdExponent h {k}).re)) :
    ∃ C' : ℝ, 0 ≤ C' ∧ ∀ᶠ M : ℕ in atTop, ∀ k, 1 ≤ k → k ≤ windowJ M →
      ‖classOmegaSum (sdBase h k) 0 M - sdMain (c k) (sdExponent h {k}) M‖
        ≤ C' * ((1:ℝ)/4)^k / Real.log M
            * ((M : ℝ) * Real.log M ^ (sdExponent h {k}).re) := by
  sorry

/-- **The shift-free node is carried by the odd class alone.** -/
theorem sdShiftFree_of_sdOdd (h : ℤ) (hodd : SDOdd h) : SDShiftFree h := by
  obtain ⟨c, B, C, δ, hC, hδ, hB, hδk, hc1, hev⟩ := hodd
  obtain ⟨C', hC', heven⟩ := exists_classOmegaSum_zero_bound h c B C hC hB hev
  refine ⟨c, B, max C C', δ, le_trans hC (le_max_left _ _), hδ, hB, hδk, hc1, ?_⟩
  filter_upwards [hev, heven, eventually_ge_atTop 8] with M hoddM hevenM hM8
  intro b hb k hk1 hkW
  have hL1 : 1 ≤ Real.log M := one_le_log_of_eight hM8
  have hLpos : 0 < Real.log M := lt_of_lt_of_le one_pos hL1
  have hX : (0:ℝ) ≤ (M:ℝ) * Real.log M ^ (sdExponent h {k}).re := by positivity
  have hp : (0:ℝ) ≤ ((1:ℝ)/4) ^ k := by positivity
  interval_cases b
  · refine le_trans (hevenM k hk1 hkW) ?_
    exact bound_mono hLpos hX (mul_le_mul_of_nonneg_right (le_max_right _ _) hp)
  · refine le_trans (hoddM k hk1 (by omega)) ?_
    exact bound_mono hLpos hX (mul_le_mul_of_nonneg_right (le_max_left _ _) hp)

/-- **Headline, re-based on the primitive odd-class node.** -/
theorem isNormal_G4_of_oddNode
    (hPre : ∀ h : ℤ, h ≠ 0 → ¬ ChowlaSector h → RoughSummatoryPrefix h)
    (hOdd : ∀ h : ℤ, h ≠ 0 → ¬ ChowlaSector h → SDOdd h)
    (hCh : ∀ h : ℤ, h ≠ 0 → ChowlaSector h → WindowDecay h)
    (hSite : SiteDecayFull) : IsNormal 4 (primeLambertAtBase 4) :=
  isNormal_G4_of_shiftSplit hPre
    (fun h hh hc => sdShiftFree_of_sdOdd h (hOdd h hh hc)) hCh hSite

end NormalNumbers.G4

#print axioms NormalNumbers.G4.isNormal_G4_of_shiftSplit
#print axioms NormalNumbers.G4.roughSummatory_of_split
#print axioms NormalNumbers.G4.norm_roughClassSum_sub_classOmegaSum
#print axioms NormalNumbers.G4.shift_cost_small
#print axioms NormalNumbers.G4.exists_re_sdExponent_le_neg_one
