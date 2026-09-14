import NormalNumbers.PrimeLambertTail

/-!
# Large primes: pointwise bounds

Every prime part is bounded by `‖c‖₁ · 2^{−K}` with no hypothesis at all: on each atom at
most the geometric tail `∑_{K<j≤J} 2^{−j} < 2^{−K}` survives (`abs_primePart_le`), and a prime
dividing none of the arguments contributes nothing (`primePart_eq_zero`).  Hence the large
class is bounded by the number of large primes that divide some argument
(`abs_classSum_le_card`), and `LargePrimeNegligible` reduces to the count Prop
`LargePrimeCountSmall`: `#{p large : p ∣ some n + j d_a − s_a} · ‖c‖₁ 2^{−K} ≤ ε_N → 0`
(`largePrimeNegligible_of_count`).  This union-cardinality estimate is true but too coarse for
the intended asymptotics: it loses an extra configuration-and-window factor.  The useful estimate
counts primes separately for each affine argument while retaining its coefficient and geometric
weight.  That weighted bound and its semantic asymptotic hypothesis are recorded below.
-/

open Filter Topology Finset
open scoped BigOperators

namespace NormalNumbers.PrimeLambert

/-- `ℓ¹`-mass of a configuration. -/
noncomputable def l1 (c : TConfig) : ℝ := ∑ a ∈ c.support, |(c a : ℝ)|

lemma l1_nonneg (c : TConfig) : 0 ≤ l1 c := Finset.sum_nonneg (fun _ _ => abs_nonneg _)

/-- `∑_{K ≤ i < J} 2^{−(i+1)} ≤ 2^{−K}`. -/
lemma sum_Ico_geom_le (K J : ℕ) : ∑ i ∈ Ico K J, (1 : ℝ) / 2 ^ (i + 1) ≤ 1 / 2 ^ K := by
  rw [Finset.sum_Ico_eq_sum_range]
  have h : ∀ i ∈ range (J - K), (1 : ℝ) / 2 ^ (K + i + 1) = 1 / 2 ^ (i + K + 1) := by
    intro i _; rw [show K + i + 1 = i + K + 1 by ring]
  rw [Finset.sum_congr rfl h, ← tsum_shift_geom K]
  exact Summable.sum_le_tsum _ (fun i _ => by positivity)
    ((summable_nat_add_iff K).mpr summable_geom_shift |>.congr (fun i => by simp only))

/-- **Pointwise bound**: `|X_p(n)| ≤ ‖c‖₁ 2^{−K}`, unconditionally. -/
theorem abs_primePart_le (c : TConfig) (K J p : ℕ) (n : ℤ) :
    |primePart c K J p n| ≤ l1 c / 2 ^ K := by
  unfold primePart Finsupp.sum l1
  rw [Finset.sum_div]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun a _ => ?_))
  rw [abs_mul, div_eq_mul_one_div]
  gcongr
  refine (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum (fun i _ => ?_)).trans
    (sum_Ico_geom_le K J))
  split_ifs <;> simp

/-- A prime dividing no argument contributes nothing. -/
theorem primePart_eq_zero (c : TConfig) (K J p : ℕ) (n : ℤ)
    (h : ¬ ∃ a ∈ c.support, ∃ i ∈ Ico K J, (p : ℤ) ∣ n + ((i : ℤ) + 1) * a.1 - a.2) :
    primePart c K J p n = 0 := by
  unfold primePart Finsupp.sum
  refine Finset.sum_eq_zero (fun a ha => ?_)
  simp only
  rw [Finset.sum_eq_zero (fun i hi => ?_), mul_zero]
  rw [if_neg (fun hd => h ⟨a, ha, i, hi, hd⟩)]

/-- The primes of a class that actually divide some argument of the finite tail at `n`. -/
def activePrimes (c : TConfig) (K J : ℕ) (S : Finset ℕ) (n : ℤ) : Finset ℕ :=
  S.filter (fun p => ∃ a ∈ c.support, ∃ i ∈ Ico K J, (p : ℤ) ∣ n + ((i : ℤ) + 1) * a.1 - a.2)

/-- **Class bound**: `|∑_{p ∈ S} X_p(n)| ≤ #(active primes) · ‖c‖₁ 2^{−K}`. -/
theorem abs_classSum_le_card (c : TConfig) (K J : ℕ) (S : Finset ℕ) (n : ℤ) :
    |classSum c K J S n| ≤ (activePrimes c K J S n).card * (l1 c / 2 ^ K) := by
  unfold classSum
  rw [← Finset.sum_filter_add_sum_filter_not S
    (fun p => ∃ a ∈ c.support, ∃ i ∈ Ico K J, (p : ℤ) ∣ n + ((i : ℤ) + 1) * a.1 - a.2)]
  rw [Finset.sum_eq_zero (fun p hp => primePart_eq_zero c K J p n (Finset.mem_filter.mp hp).2),
    add_zero]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  refine (Finset.sum_le_sum (fun p _ => abs_primePart_le c K J p n)).trans (le_of_eq ?_)
  rw [Finset.sum_const, nsmul_eq_mul]
  rfl

/-- The primes in `S` dividing one fixed affine argument. -/
def argumentPrimes (S : Finset ℕ) (n : ℤ) (a : ℕ × ℤ) (i : ℕ) : Finset ℕ :=
  S.filter (fun p => (p : ℤ) ∣ n + ((i : ℤ) + 1) * a.1 - a.2)

/-- Weighted per-argument bound, retaining the coefficient and binary-tail weight. -/
theorem abs_classSum_le_argumentPrimes (c : TConfig) (K J : ℕ) (S : Finset ℕ) (n : ℤ) :
    |classSum c K J S n| ≤
      ∑ a ∈ c.support, |(c a : ℝ)| *
        ∑ i ∈ Ico K J, ((argumentPrimes S n a i).card : ℝ) / 2 ^ (i + 1) := by
  unfold classSum primePart Finsupp.sum
  calc
    _ ≤ ∑ p ∈ S, ∑ a ∈ c.support, |(c a : ℝ)| *
        ∑ i ∈ Ico K J,
          if (p : ℤ) ∣ n + ((i : ℤ) + 1) * a.1 - a.2 then 1 / 2 ^ (i + 1) else 0 := by
            refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun p hp => ?_))
            refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun a ha => ?_))
            rw [abs_mul]
            gcongr
            exact (Finset.abs_sum_le_sum_abs _ _).trans_eq (Finset.sum_congr rfl fun i hi => by
              split_ifs <;> simp)
    _ = _ := by
      unfold argumentPrimes
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro a ha
      rw [← Finset.mul_sum, Finset.sum_comm]
      congr 1
      apply Finset.sum_congr rfl
      intro i hi
      rw [← Finset.sum_filter]
      rw [Finset.sum_const, nsmul_eq_mul]
      simp [div_eq_mul_inv]

/-- A uniform per-argument prime-divisor bound, at the weighted scale needed in the proof. -/
def LargePrimeArgumentCountSmall {q : ℤ} (C : Chain q) : Prop :=
  ∃ B ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) ∧
    (∀ N, 0 ≤ B N) ∧
    (∀ N, ∀ n ∈ (C.D N).P, ∀ a ∈ (C.c N).support,
      ∀ i ∈ Ico (C.K N) (C.S N).J,
        ((argumentPrimes (C.S N).large n a i).card : ℝ) ≤ B N) ∧
    ∀ N, B N * (l1 (C.c N) / 2 ^ C.K N) ≤ ε N

/-- Per-argument divisor control implies `LargePrimeNegligible`. -/
theorem largePrimeNegligible_of_argumentCount {q : ℤ} (C : Chain q)
    (h : LargePrimeArgumentCountSmall C) : LargePrimeNegligible C := by
  obtain ⟨B, ε, hε, hB, hcount, hscale⟩ := h
  refine ⟨ε, hε, fun N n hn => (abs_classSum_le_argumentPrimes _ _ _ _ n).trans ?_⟩
  calc
    _ ≤ ∑ a ∈ (C.c N).support, |((C.c N) a : ℝ)| *
        ∑ i ∈ Ico (C.K N) (C.S N).J, B N / 2 ^ (i + 1) := by
          refine Finset.sum_le_sum (fun a ha => mul_le_mul_of_nonneg_left ?_ (abs_nonneg _))
          refine Finset.sum_le_sum (fun i hi => ?_)
          exact div_le_div_of_nonneg_right (hcount N n hn a ha i hi) (by positivity)
    _ ≤ B N * (l1 (C.c N) / 2 ^ C.K N) := by
          unfold l1
          have hfactor :
              (∑ i ∈ Ico (C.K N) (C.S N).J, B N / 2 ^ (i + 1)) =
                B N * ∑ i ∈ Ico (C.K N) (C.S N).J, (1 : ℝ) / 2 ^ (i + 1) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro i hi
            ring
          calc
            _ = B N * (∑ a ∈ (C.c N).support, |((C.c N) a : ℝ)|) *
                (∑ i ∈ Ico (C.K N) (C.S N).J, (1 : ℝ) / 2 ^ (i + 1)) := by
                  rw [hfactor, ← Finset.sum_mul]
                  ring
            _ ≤ B N * (∑ a ∈ (C.c N).support, |((C.c N) a : ℝ)|) *
                (1 / 2 ^ C.K N) := by
                  exact mul_le_mul_of_nonneg_left (sum_Ico_geom_le _ _)
                    (mul_nonneg (hB N) (Finset.sum_nonneg fun _ _ => abs_nonneg _))
            _ = _ := by ring
    _ ≤ ε N := hscale N

/-- Coarse union count: the number of large primes dividing some argument, times
`‖c‖₁ 2^{−K}`, is uniformly `o(1)` on the sample. -/
def LargePrimeCountSmall {q : ℤ} (C : Chain q) : Prop :=
  ∃ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) ∧
    ∀ N, ∀ n ∈ (C.D N).P,
      (activePrimes (C.c N) (C.K N) (C.S N).J (C.S N).large n).card
        * (l1 (C.c N) / 2 ^ C.K N) ≤ ε N

/-- `LargePrimeCountSmall → LargePrimeNegligible`. -/
theorem largePrimeNegligible_of_count {q : ℤ} (C : Chain q) (h : LargePrimeCountSmall C) :
    LargePrimeNegligible C := by
  obtain ⟨ε, hε, hb⟩ := h
  exact ⟨ε, hε, fun N n hn => (abs_classSum_le_card _ _ _ _ n).trans (hb N n hn)⟩

end NormalNumbers.PrimeLambert
