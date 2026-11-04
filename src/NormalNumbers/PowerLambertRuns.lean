/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.PowerLambertRich

/-!
# Long constant runs in a perfect-power Lambert constant force large window sums

Write `Y = Σ_{i<L} g i · b^i + κ` with "digits" `g i ∈ ℕ` (possibly `≥ b`) and an incoming carry
`κ`.  If the low `L` base-`b` digits of `Y` are all `b − 1` (`b^L ∣ Y + 1`), the carry chain
gives `(b − 1) L ≤ Σ g + κ`.  If they are all `0` (`b^L ∣ Y`) and the chain is started (`κ ≥ 1`
or some `g i ≥ 1` with `i < P`), then `(b − 1)(L − P) ≤ Σ g + κ`.

For `S = powerLambert b r` the event "`L` constant digits after position `n`" is exactly such a
divisibility, with `g i = c(n + L − i)` (`c = powerDivisorCount r`) and `κ = ⌊T_{n+L}⌋`.
-/

namespace NormalNumbers.ArithmeticDisjunctivity

open Finset

/-- **Carry chain, all digits `b − 1`.**  If `b^L ∣ Σ_{i<L} g i b^i + κ + 1`, then
`(b − 1) L ≤ Σ_{i<L} g i + κ`. -/
theorem carry_le_of_dvd_succ {b : ℕ} (hb : 1 ≤ b) :
    ∀ (L : ℕ) (g : ℕ → ℕ) (κ : ℕ), b ^ L ∣ (∑ i ∈ range L, g i * b ^ i) + κ + 1 →
      (b - 1) * L ≤ (∑ i ∈ range L, g i) + κ := by
  intro L
  induction L with
  | zero => intro g κ _; simp
  | succ L ih =>
    intro g κ h
    rw [Finset.sum_range_succ'] at h ⊢
    have hb1 : b ∣ g 0 + κ + 1 := by
      have h1 : b ∣ (∑ i ∈ range L, g (i + 1) * b ^ (i + 1)) + g 0 * b ^ 0 + κ + 1 :=
        (dvd_pow_self b (by omega)).trans h
      have h2 : b ∣ ∑ i ∈ range L, g (i + 1) * b ^ (i + 1) :=
        Finset.dvd_sum fun i _ => Dvd.dvd.mul_left (dvd_pow_self b (by omega)) _
      rw [pow_zero, mul_one, add_assoc, add_assoc] at h1
      rw [add_assoc]
      exact (Nat.dvd_add_right h2).mp h1
    obtain ⟨q, hq⟩ := hb1
    have hq1 : 1 ≤ q := by
      rcases Nat.eq_zero_or_pos q with h0 | h0
      · rw [h0, mul_zero] at hq; omega
      · exact h0
    have hrest : b ^ L ∣ (∑ i ∈ range L, g (i + 1) * b ^ i) + (q - 1) + 1 := by
      have hsum : (∑ i ∈ range L, g (i + 1) * b ^ (i + 1)) =
          b * ∑ i ∈ range L, g (i + 1) * b ^ i := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => by ring
      have he : (∑ i ∈ range L, g (i + 1) * b ^ (i + 1)) + g 0 * b ^ 0 + κ + 1 =
          b * ((∑ i ∈ range L, g (i + 1) * b ^ i) + (q - 1) + 1) := by
        rw [hsum, pow_zero, mul_one]
        have : (q - 1) + 1 = q := by omega
        rw [add_assoc _ (q - 1) 1, this, mul_add, ← hq]
        ring
      rw [he, pow_succ, mul_comm (b ^ L) b] at h
      exact Nat.dvd_of_mul_dvd_mul_left (by omega) h
    have hih := ih (fun i => g (i + 1)) (q - 1) hrest
    have hbq : (b - 1) + (q - 1) ≤ g 0 + κ := by
      have : b * q ≥ q + (b - 1) := by
        have : b * q = q + (b - 1) * q := by
          rw [Nat.sub_mul, one_mul]; have := Nat.le_mul_of_pos_left q (by omega : 0 < b); omega
        rw [this]
        have : (b - 1) * 1 ≤ (b - 1) * q := Nat.mul_le_mul_left _ hq1
        omega
      omega
    rw [Nat.mul_succ]
    omega

/-- **Carry chain, all digits `0`.**  If `b^L ∣ Σ_{i<L} g i b^i + κ` and the chain is started
(`κ ≥ 1`, or `g i ≥ 1` for some `i < P`), then `(b − 1)(L − P) ≤ Σ_{i<L} g i + κ`. -/
theorem carry_le_of_dvd {b : ℕ} (hb : 1 ≤ b) :
    ∀ (L : ℕ) (g : ℕ → ℕ) (κ P : ℕ), b ^ L ∣ (∑ i ∈ range L, g i * b ^ i) + κ →
      (1 ≤ κ ∨ ∃ i < P, 1 ≤ g i) → (b - 1) * (L - P) ≤ (∑ i ∈ range L, g i) + κ := by
  intro L
  induction L with
  | zero => intro g κ P _ _; simp
  | succ L ih =>
    intro g κ P h hstart
    rw [Finset.sum_range_succ'] at h ⊢
    have hsum : (∑ i ∈ range L, g (i + 1) * b ^ (i + 1)) =
        b * ∑ i ∈ range L, g (i + 1) * b ^ i := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring
    have hb1 : b ∣ g 0 + κ := by
      have h1 : b ∣ (∑ i ∈ range L, g (i + 1) * b ^ (i + 1)) + g 0 * b ^ 0 + κ :=
        (dvd_pow_self b (by omega)).trans h
      rw [pow_zero, mul_one, add_assoc, hsum] at h1
      exact (Nat.dvd_add_right (dvd_mul_right _ _)).mp h1
    obtain ⟨q, hq⟩ := hb1
    have hrest : b ^ L ∣ (∑ i ∈ range L, g (i + 1) * b ^ i) + q := by
      have he : (∑ i ∈ range L, g (i + 1) * b ^ (i + 1)) + g 0 * b ^ 0 + κ =
          b * ((∑ i ∈ range L, g (i + 1) * b ^ i) + q) := by
        rw [hsum, pow_zero, mul_one, add_assoc, hq, mul_add]
      rw [he, pow_succ, mul_comm (b ^ L) b] at h
      exact Nat.dvd_of_mul_dvd_mul_left (by omega) h
    rcases Nat.eq_zero_or_pos (g 0 + κ) with h0 | h0
    · -- the chain has not started at the lowest digit
      have hg0 : g 0 = 0 := by omega
      have hκ : κ = 0 := by omega
      have hq0 : q = 0 := by
        rcases Nat.eq_zero_or_pos q with h | h
        · exact h
        · have : 0 < b * q := Nat.mul_pos (by omega) h
          omega
      obtain ⟨i, hiP, hgi⟩ : ∃ i < P, 1 ≤ g i := by
        rcases hstart with h | h
        · omega
        · exact h
      obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := by
        rcases i with _ | i'
        · omega
        · exact ⟨i', rfl⟩
      have hih := ih (fun i => g (i + 1)) q (P - 1) hrest (Or.inr ⟨i', by omega, hgi⟩)
      rw [hq0] at hih
      have : L + 1 - P = L - (P - 1) := by omega
      rw [this]
      omega
    · -- the chain has started: every later carry is positive
      have hq1 : 1 ≤ q := by
        rcases Nat.eq_zero_or_pos q with h | h
        · rw [h, mul_zero] at hq; omega
        · exact h
      have hih := ih (fun i => g (i + 1)) q 0 hrest (Or.inl hq1)
      have hbq : (b - 1) + q ≤ g 0 + κ := by
        have : b * q = q + (b - 1) * q := by
          rw [Nat.sub_mul, one_mul]; have := Nat.le_mul_of_pos_left q (by omega : 0 < b); omega
        have : (b - 1) * 1 ≤ (b - 1) * q := Nat.mul_le_mul_left _ hq1
        omega
      have hmono : (b - 1) * (L + 1 - P) ≤ (b - 1) * (L + 1) :=
        Nat.mul_le_mul_left _ (by omega)
      rw [Nat.sub_zero] at hih
      rw [Nat.mul_succ] at hmono
      omega

/-! ### The run event as a divisibility -/

/-- The integer head `H_N = Σ_{m ≤ N} c(m) b^{N−m}` of `powerLambert b r · b^N`. -/
def powerHead (b r N : ℕ) : ℕ :=
  ∑ m ∈ range (N + 1), powerDivisorCount r m * b ^ (N - m)

/-- The window `W_L(n) = Σ_{i<L} c(n+L−i) b^i` of the coefficients at positions
`n+1, …, n+L` (lowest significance at position `n + L`). -/
def powerWindow (b r L n : ℕ) : ℕ :=
  ∑ i ∈ range L, powerDivisorCount r (n + L - i) * b ^ i

/-- The tail `T_n = Σ_{j≥0} c(n+1+j) / b^{j+1}`, so that `S b^n = H_n + T_n`. -/
noncomputable def powerTail (b r n : ℕ) : ℝ :=
  ∑' j : ℕ, (powerDivisorCount r (n + 1 + j) : ℝ) / (b : ℝ) ^ (j + 1)

theorem powerTail_nonneg (b r n : ℕ) : 0 ≤ powerTail b r n :=
  tsum_nonneg fun _ => by positivity

theorem summable_powerTail (b r : ℕ) (hb : 2 ≤ b) (n : ℕ) :
    Summable (fun j : ℕ => (powerDivisorCount r (n + 1 + j) : ℝ) / (b : ℝ) ^ (j + 1)) :=
  summable_tail_of_le b hb n _ fun _ => powerDivisorCount_le_self r _

/-- One step of the head recurrence: `H_{N+1} = b H_N + c(N+1)`. -/
theorem powerHead_succ (b r N : ℕ) :
    powerHead b r (N + 1) = b * powerHead b r N + powerDivisorCount r (N + 1) := by
  unfold powerHead
  rw [Finset.sum_range_succ, Nat.sub_self, pow_zero, mul_one, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun m hm => ?_
  have hmN : m ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)
  rw [show N + 1 - m = (N - m) + 1 by omega, pow_succ]
  ring

/-- One step of the window recurrence: `W_{L+1}(n) = b W_L(n) + c(n+L+1)`. -/
theorem powerWindow_succ (b r L n : ℕ) :
    powerWindow b r (L + 1) n = b * powerWindow b r L n + powerDivisorCount r (n + L + 1) := by
  unfold powerWindow
  rw [Finset.sum_range_succ', Finset.mul_sum]
  simp only [Nat.sub_zero, pow_zero, mul_one]
  congr 1
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [show n + (L + 1) - (i + 1) = n + L - i by omega, pow_succ]
  ring

/-- The head after `n + L` positions is the shifted head plus the window. -/
theorem powerHead_add (b r n L : ℕ) :
    powerHead b r (n + L) = b ^ L * powerHead b r n + powerWindow b r L n := by
  induction L with
  | zero => simp [powerWindow]
  | succ L ih =>
    rw [← add_assoc, powerHead_succ, ih, powerWindow_succ, pow_succ]
    ring

/-- `S b^N = H_N + T_N`. -/
theorem powerLambert_mul_pow (b r : ℕ) (hb : 2 ≤ b) (hr : 1 ≤ r) (N : ℕ) :
    powerLambert b r * (b : ℝ) ^ N = (powerHead b r N : ℝ) + powerTail b r N := by
  have hx : powerLambert b r = CastingOut.lambertVal b (powerDivisorCount r) := by
    unfold powerLambert
    rw [powerLambert_eq_coefficientValue hb hr]
    rfl
  rw [hx, JointLambert.lambertVal_mul_pow_eq b hb _ (powerDivisorCount_le_self r) N]
  rfl

/-- If `{y} < 1/M` then `M ∣ ⌊M y⌋`. -/
theorem int_dvd_floor_of_fract_lt {M : ℕ} (hM : 0 < M) {y : ℝ}
    (h : Int.fract y < 1 / (M : ℝ)) : (M : ℤ) ∣ ⌊(M : ℝ) * y⌋ := by
  have hMpos : (0 : ℝ) < M := by exact_mod_cast hM
  have hsplit : (M : ℝ) * y = ((M * ⌊y⌋ : ℤ) : ℝ) + M * Int.fract y := by
    rw [← Int.self_sub_floor]
    push_cast
    ring
  have h0 : ⌊(M : ℝ) * Int.fract y⌋ = 0 := by
    rw [Int.floor_eq_zero_iff]
    refine ⟨by have := Int.fract_nonneg y; positivity, ?_⟩
    calc (M : ℝ) * Int.fract y < M * (1 / M) := mul_lt_mul_of_pos_left h hMpos
      _ = 1 := by field_simp
  rw [hsplit, Int.floor_intCast_add, h0, add_zero]
  exact dvd_mul_right _ _

/-- If `1 − 1/M ≤ {y}` then `M ∣ ⌊M y⌋ + 1`. -/
theorem int_dvd_floor_add_one_of_le_fract {M : ℕ} (hM : 0 < M) {y : ℝ}
    (h : 1 - 1 / (M : ℝ) ≤ Int.fract y) : (M : ℤ) ∣ ⌊(M : ℝ) * y⌋ + 1 := by
  have hMpos : (0 : ℝ) < M := by exact_mod_cast hM
  have hsplit : (M : ℝ) * y = ((M * ⌊y⌋ : ℤ) : ℝ) + M * Int.fract y := by
    rw [← Int.self_sub_floor]
    push_cast
    ring
  have h0 : ⌊(M : ℝ) * Int.fract y⌋ = (M : ℤ) - 1 := by
    rw [Int.floor_eq_iff]
    push_cast
    constructor
    · have := mul_le_mul_of_nonneg_left h hMpos.le
      rw [mul_sub, mul_one, mul_one_div_cancel hMpos.ne'] at this
      linarith
    · have := Int.fract_lt_one y
      nlinarith
  rw [hsplit, Int.floor_intCast_add, h0]
  exact ⟨⌊y⌋ + 1, by ring⟩

/-- **A run of `L` zeros is a divisibility.**  If `{b^n S} < 1/b^L`, then
`b^L ∣ W_L(n) + ⌊T_{n+L}⌋`. -/
theorem dvd_powerWindow_of_orbit_lt (b r : ℕ) (hb : 2 ≤ b) (hr : 1 ≤ r) (n L : ℕ)
    (h : orbit b (powerLambert b r) n < 1 / (b : ℝ) ^ L) :
    b ^ L ∣ powerWindow b r L n + ⌊powerTail b r (n + L)⌋₊ := by
  have hM : 0 < b ^ L := Nat.pow_pos (by omega)
  have h1 := int_dvd_floor_of_fract_lt hM (y := powerLambert b r * (b : ℝ) ^ n)
    (by push_cast; exact h)
  have hy : ((b ^ L : ℕ) : ℝ) * (powerLambert b r * (b : ℝ) ^ n) =
      (powerHead b r (n + L) : ℝ) + powerTail b r (n + L) := by
    rw [← powerLambert_mul_pow b r hb hr]
    push_cast
    rw [pow_add]
    ring
  rw [hy, Int.floor_natCast_add, ← Int.natCast_floor_eq_floor (powerTail_nonneg _ _ _),
    powerHead_add] at h1
  have h2 : b ^ L ∣ b ^ L * powerHead b r n + powerWindow b r L n +
      ⌊powerTail b r (n + L)⌋₊ := by exact_mod_cast h1
  rw [add_assoc] at h2
  exact (Nat.dvd_add_right (dvd_mul_right _ _)).mp h2

/-- **A run of `L` digits `b − 1` is a divisibility.**  If `1 − 1/b^L ≤ {b^n S}`, then
`b^L ∣ W_L(n) + ⌊T_{n+L}⌋ + 1`. -/
theorem dvd_powerWindow_succ_of_le_orbit (b r : ℕ) (hb : 2 ≤ b) (hr : 1 ≤ r) (n L : ℕ)
    (h : 1 - 1 / (b : ℝ) ^ L ≤ orbit b (powerLambert b r) n) :
    b ^ L ∣ powerWindow b r L n + ⌊powerTail b r (n + L)⌋₊ + 1 := by
  have hM : 0 < b ^ L := Nat.pow_pos (by omega)
  have h1 := int_dvd_floor_add_one_of_le_fract hM (y := powerLambert b r * (b : ℝ) ^ n)
    (by push_cast; exact h)
  have hy : ((b ^ L : ℕ) : ℝ) * (powerLambert b r * (b : ℝ) ^ n) =
      (powerHead b r (n + L) : ℝ) + powerTail b r (n + L) := by
    rw [← powerLambert_mul_pow b r hb hr]
    push_cast
    rw [pow_add]
    ring
  rw [hy, Int.floor_natCast_add, ← Int.natCast_floor_eq_floor (powerTail_nonneg _ _ _),
    powerHead_add] at h1
  have h2 : b ^ L ∣ b ^ L * powerHead b r n + powerWindow b r L n +
      ⌊powerTail b r (n + L)⌋₊ + 1 := by exact_mod_cast h1
  rw [add_assoc, add_assoc] at h2
  rw [add_assoc]
  exact (Nat.dvd_add_right (dvd_mul_right _ _)).mp h2

end NormalNumbers.ArithmeticDisjunctivity
