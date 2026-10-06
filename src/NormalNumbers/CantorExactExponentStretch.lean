/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.CantorExactExponent

/-!
# Stretch: exact exponent `μ₀` for every `μ₀ > 2`, in `K`, normal to every base prime to 3

`CantorExactExponent.exists_computable_mem_cantorSet_irrExponent_normal` covers
`μ₀ > 2 + log₂ 3 ≈ 3.585`.  This file freezes the full range `μ₀ > 2` (Bugeaud's Theorem 7.21
range, `μ ≥ 2`, minus the endpoint, which is the literature control below).

## Why the main mechanism stops at `2 + log₂ 3`

The Borel–Cantelli bound counts `O(2^{F(m)})` numerators per denominator `q ≈ 3ᵐ` near the
support.  Where the window `(m, τm]` enters a forced run (`m ≈ a_{k+1}/(τ−1)`), only
`a_{k+1} − m` places are free (`CantorExactExponent.freeCount_window_le_of_run`), and the block
cost `3ᵐ 2^{−(τ−2)m}` does not decay for `τ ≤ 2 + log₂ 3` (kernel control
`CantorExactExponent.bcTerm_red_mu_three`).  The heuristic count (rationals equidistributed
against the coin measure) predicts a cost `q^{2−τ}` per dyadic block, summable for every `τ > 2`.

## Candidate mechanism (none known to the repo)

An effective count of rationals near the truncations `P/3^a` of Cantor points.  Best proved
input found: He–Liao, arXiv 2602.01307, Cor. 6.5 (local equidistribution of `A_Q(η)` against
the Cantor measure on balls of radius `≥ Q^{−β}`, `η ∈ [Q^{−α}, Q^{−1}]`, `α − 1 > 0` small and
not explicit), and He–Liao 2608.15686.  The Broderick–Fishman–Reich count and Bugeaud–Durand
conjecture (18) are open for `K`.

## He–Liao does not transfer (checked 2026-10-05)

`Literature.HeLiao2026Cor65` is the upper half of their Cor. 6.5, for cylinders of the Cantor
measure.  Conditioned on a prefix that ends where a free stretch starts, our coin measure is
exactly such a branch down to the next run start `b`, so the measure-level transfer itself is
fine.  It fails for two independent reasons:

* **Scale.**  The trivial count only fails in run-entering windows, `(τ−1)m ≤ b < τm` with
  `q ≈ 3ᵐ`.  There the point is `P/3^b` up to `3^{−E}`, and every other rational is at least
  `1/(q·3^b)` from `P/3^b` (`endpoint_sep`).  So the event lives below the cylinder scale
  `3^{−b}`, and no measure-level count sees it.  Thickening to `3^{−b}` costs `Q·η = 3^{2m−b}`
  per window, which is `≥ 1` for every `τ ≤ 3` (`thickening_cost_ge_one`).  A
  Bugeaud–Durand-strength *measure* count would therefore reach at best `μ₀ > 3`, not `μ₀ > 2`.
* **Range.**  Cor. 6.5's main term needs `η ≥ Q^{−α}` with `α − 1 > 0` small and not explicit.
  The thickened windows need `η = 3^{m−b} ≤ Q^{2−τ}`, so `α ≥ τ − 2`, which is greater than 1
  for every `τ > 3`.  The two regimes never overlap.

What would reopen it is a count of rationals near the *discrete* endpoints `P/3^b` at the
heuristic density `Q^{2−τ}`, uniformly over cylinders (`EndpointRationalCount`).  That is a
Broderick–Fishman–Reich-type count, open for `K`.  He–Liao 2608.15686 (the Bugeaud–Durand
formula for `τ` near 1) has the same small-`α` regime.

Confidence 10%.
-/

open MeasureTheory Filter Topology

namespace NormalNumbers.CantorExactExponentStretch

open CantorLiouville CantorExactExponent CantorExpGeneric Derandomize

namespace Literature

/-- **Weiss 2001** (B. Weiss, *Almost no points on a Cantor set are very well approximable*,
Proc. R. Soc. Lond. A 457 (2001) 949–952; Bugeaud 2012, Thm 7.16 states `v₁(ξ) = 1` for
`μ_K`-a.e. `ξ`, i.e. exponent `2`): for the Cantor measure (law of `pt (fun _ => true)` under fair
coins), almost every point is `τ`-approximable for no `τ > 2`.  Cited for the `μ₀ = 2` control
only. -/
def Weiss2001 : Prop :=
  ∀ᵐ ω ∂coins, ∀ τ : ℝ, 2 < τ → ¬ LiouvilleWith τ (pt (fun _ => true) ω)

/-- **Bugeaud 2008, Theorem 7.21 of the 2012 book** (Y. Bugeaud, *Diophantine approximation and
Cantor sets*, Math. Ann. 341 (2008) 677–684): "Let μ ≥ 2.  The middle third Cantor set K contains
uncountably many elements whose irrationality exponent is equal to μ."  Weakened to existence.
Cited as the pairwise intersection `K ∩ {μ(x) = μ}`; nothing here uses it. -/
def Bugeaud2008Thm721 : Prop :=
  ∀ μ : ℝ, 2 ≤ μ → ∃ x ∈ cantorSet, HasIrrExponent x μ

/-- **He–Liao 2026, Corollary 6.5, upper half** (Y. He, L. Liao, *Jarník-type theorem for
self-similar sets*, arXiv 2602.01307, built on Bénard–He–Zhang and Khalil–Luethi): for the Cantor
measure there are `α > 1` and `β > 0` such that, for large `Q`, every cylinder `K_w` of length
`≥ Q^{−β}` and every `η ∈ [Q^{−α}, Q^{−1}]`,
`μ(K_w ∩ A_Q(η)) ≪ μ(K_w) · Q η`, where `A_Q(η) = {x : ‖qx‖ < η for some Q ≤ q < 2Q}`.
Their statement is two-sided and for balls; the ball case reduces to cylinders by the open set
condition (their proof of 6.5).  `α` and `β` are not explicit (`κ` of Bénard–He–Zhang).  Cited,
unused: it records why the transfer fails (module doc). -/
def HeLiao2026Cor65 : Prop :=
  ∃ α : ℝ, 1 < α ∧ ∃ β : ℝ, 0 < β ∧ ∃ C : ℝ, 0 < C ∧ ∃ Q₀ : ℕ, ∀ Q : ℕ, Q₀ ≤ Q →
    ∀ (n : ℕ) (w : ℕ → Bool), (Q : ℝ) ^ (-β) ≤ (3 : ℝ)⁻¹ ^ n →
    ∀ η : ℝ, (Q : ℝ) ^ (-α) ≤ η → η ≤ (Q : ℝ)⁻¹ →
      coins.real {ω | (∀ i < n, ω i = w i) ∧ ∃ q : ℕ, Q ≤ q ∧ q < 2 * Q ∧
          ∃ p : ℤ, |(q : ℝ) * pt (fun _ => true) ω - p| < η} ≤
        C * Q * η * coins.real {ω | ∀ i < n, ω i = w i}

end Literature

/-- **Endpoint separation.**  A rational `p/q` other than `P/3^b` is at least `1/(q·3^b)` from
it.  So in a run-entering window (`q^{−τ} < 3^{−b}/q`), only the endpoint's own triadic
rationals are within `q^{−τ}`, and the stretch event is a question about the discrete endpoints
`P/3^b`, below the cylinder scale. -/
theorem endpoint_sep (P b q : ℕ) (p : ℤ) (hq : 0 < q)
    (hne : (p : ℝ) / q ≠ (P : ℝ) / 3 ^ b) :
    1 / ((q : ℝ) * 3 ^ b) ≤ |(P : ℝ) / 3 ^ b - p / q| := by
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  have h3 : (0 : ℝ) < 3 ^ b := by positivity
  have key : (P : ℝ) / 3 ^ b - p / q = (((P : ℤ) * q - p * 3 ^ b : ℤ) : ℝ) / ((q : ℝ) * 3 ^ b) := by
    push_cast
    field_simp
  have hz : (P : ℤ) * q - p * 3 ^ b ≠ 0 := by
    intro h
    apply hne
    have h' : ((P : ℤ) * q : ℝ) = (p * 3 ^ b : ℤ) := by
      exact_mod_cast sub_eq_zero.mp h
    push_cast at h'
    rw [div_eq_div_iff hq'.ne' h3.ne']
    linarith
  rw [key, abs_div, abs_of_pos (by positivity : (0 : ℝ) < q * 3 ^ b)]
  apply div_le_div_of_nonneg_right _ (by positivity)
  have : (1 : ℤ) ≤ |(P : ℤ) * q - p * 3 ^ b| := Int.one_le_abs hz
  rw [← Int.cast_abs]
  exact_mod_cast this

/-- **Thickening cost.**  Pushing the endpoint event up to the cylinder scale `3^{−b}` costs
`Q·η = 3^{2m−b}` in a window with `(τ−1)m ≤ b`; at the window's first denominator scale
(`b ≤ (τ−1)m`) this is `≥ 1` whenever `τ ≤ 3`.  So a measure-level count, even of
Bugeaud–Durand strength, cannot certify `μ₀ ≤ 3`. -/
theorem thickening_cost_ge_one (τ : ℝ) (hτ : τ ≤ 3) (m b : ℕ) (hb : (b : ℝ) ≤ (τ - 1) * m) :
    1 ≤ (3 : ℝ) ^ (2 * m) / 3 ^ b := by
  have hbm : b ≤ 2 * m := by
    have h2 : (τ - 1) * (m : ℝ) ≤ 2 * m :=
      mul_le_mul_of_nonneg_right (by linarith) (Nat.cast_nonneg m)
    exact_mod_cast hb.trans h2
  rw [le_div_iff₀ (by positivity), one_mul]
  exact pow_le_pow_right₀ (by norm_num) hbm

/-- **Reopen condition for the He–Liao wall** (`Maze`: "He–Liao local count on the forced-run
measure").  Rationals `p/q`, `q ∈ [3ᵐ, 2·3ᵐ)`, within `q^{−τ}` of the depth-`b` Cantor endpoint
`P/3^b` (other than `P/3^b` itself) have conditional probability `O(Q^{2−τ})` on every cylinder
of depth `a ≤ 2m`: the heuristic density (per endpoint, `Σ_q 2q^{1−τ}`).  A statement, not a
belief: a Broderick–Fishman–Reich-type count on the discrete endpoints.  That it suffices for
`ae_not_liouvilleWith_all` is believed, not checked (60%). -/
def EndpointRationalCount : Prop :=
  ∀ τ : ℝ, 2 < τ → ∃ C : ℝ, ∀ (a b m : ℕ) (w : ℕ → Bool), a ≤ b → a ≤ 2 * m →
    (b : ℝ) < τ * m →
    coins.real {ω | (∀ i < a, ω i = w i) ∧ ∃ q : ℕ, 3 ^ m ≤ q ∧ q < 2 * 3 ^ m ∧ ∃ p : ℤ,
        (p : ℝ) / q ≠ (hd (fun _ => true) ω b : ℝ) / 3 ^ b ∧
        |(hd (fun _ => true) ω b : ℝ) / 3 ^ b - p / q| < (q : ℝ) ^ (-τ)} ≤
      C * (3 : ℝ) ^ ((2 - τ) * m) * coins.real {ω | ∀ i < a, ω i = w i}

/-- **Control at `μ₀ = 2`: the triple is literature.**  Confidence 90%.

English proof.  Weiss 2001 gives `¬ LiouvilleWith τ` for `τ > 2`, a.e.; Cassels 1959
(`CantorLiouvilleAll.Literature.Cassels1959`) gives normality to base 2 a.e., hence
irrationality, hence `LiouvilleWith 2` by Dirichlet (Mathlib:
`Real.infinite_rat_abs_sub_lt_one_div_den_sq_of_irrational`), and `LiouvilleWith p` for `p < 2`
by `LiouvilleWith.mono`.  Intersect the two full-measure sets. -/
theorem exists_mem_cantorSet_irrExponent_two_of_literature (hW : Literature.Weiss2001)
    (hC : CantorLiouvilleAll.Literature.Cassels1959) :
    ∃ x ∈ cantorSet, HasIrrExponent x 2 ∧ IsNormal 2 x := by
  sorry

/-- **Stretch crux: the exponent upper bound for every `μ₀ > 2`.**  Confidence 15%.

English proof (heuristic only).  As `CantorExactExponent.ae_not_liouvilleWith`, with the trivial
numerator count replaced by an equidistribution count of rationals `p/q`, `q ≈ 3ᵐ`, near the
prefix rationals `P/3^{a_{k+1}}`: expected hits `≈ q^{1−τ}` per `q`, so `3^{m(2−τ)}` per block,
summable for `τ > 2`.  No proved count of this strength is known for `K` (see module doc). -/
theorem ae_not_liouvilleWith_all (μ₀ : ℚ) (hμ : 2 < μ₀) (τ : ℝ) (hτ : (μ₀ : ℝ) < τ) :
    ∀ᵐ ω ∂coins, ¬ LiouvilleWith τ (cantorExpReal μ₀ ω) := by
  sorry

/-- **Stretch headline.**  For every rational `μ₀ > 2` a computable `x ∈ K` with irrationality
exponent exactly `μ₀`, normal to every base `b ≥ 2` with `3 ∤ b`, not normal to base 3.
Confidence 10%. -/
theorem exists_computable_mem_cantorSet_irrExponent_normal_all (μ₀ : ℚ) (hμ : 2 < μ₀) :
    ∃ e : ℕ → Bool, Computable e ∧ cantorExpReal μ₀ e ∈ cantorSet ∧
      HasIrrExponent (cantorExpReal μ₀ e) μ₀ ∧
      (∀ b : ℕ, 2 ≤ b → ¬ 3 ∣ b → IsNormal b (cantorExpReal μ₀ e)) ∧
      ¬ IsNormal 3 (cantorExpReal μ₀ e) := by
  sorry

/-! ## Lap 2026-10-05: the exact residue count

The cylinder count prices a run-entering window at `3ᵐ 2^{m−b}` (`bcTerm_red_mu_three`).  It
over-counts: for `3 ∤ q` the map `P ↦ P q mod 3^b` is injective, and an approximation `p/q` of
`P/3^b` with `|P/3^b − p/q| < q^{−τ}` means `P q ≡ r (mod 3^b)` with `|r| < 3^b q^{1−τ} ≤ 3^k`,
`k = b − ⌊(τ−1)m⌋`.  Splitting `P` at digit `k`, the low digits fix `r` up to sign and the
high digits are then determined (`card_lowResidue_le`): per `q` at most `2·2^k` numerators, a
fraction `2^{1−(τ−1)m}` of the `2^b`.  Summed over `q ≈ 3ᵐ`: `(3·2^{−(τ−1)})ᵐ`, summable iff
`τ > 1 + log₂ 3` (`runEnteringCountAt_of_lt`).  The same exponent as the interior windows' cylinder
count, so the elementary threshold drops from `2 + log₂ 3 ≈ 3.585` to `1 + log₂ 3 ≈ 2.585`
(`ae_not_liouvilleWith_mid`, stated). -/

/-- Integers `P < 3^b` whose `b` ternary digits are all `0` or `2`: the depth-`b` Cantor
numerators, `P/3^b` the left endpoints of the depth-`b` Cantor intervals. -/
def cantorInts (b : ℕ) : Finset ℕ :=
  (Finset.range (3 ^ b)).filter fun P => ∀ i < b, P / 3 ^ i % 3 ≠ 1

/-- Non-vacuity: depth 2 has the four numerators `0, 2, 6, 8`. -/
theorem cantorInts_two : cantorInts 2 = {0, 2, 6, 8} := by decide

/-- The low `k` digits of a Cantor numerator form a Cantor numerator. -/
theorem mod_mem_cantorInts {b k P : ℕ} (hk : k ≤ b) (hP : P ∈ cantorInts b) :
    P % 3 ^ k ∈ cantorInts k := by
  simp only [cantorInts, Finset.mem_filter, Finset.mem_range] at hP ⊢
  refine ⟨Nat.mod_lt _ (by positivity), fun i hi => ?_⟩
  have h := hP.2 i (by omega)
  obtain ⟨j, rfl⟩ : ∃ j, k = i + (j + 1) := ⟨k - i - 1, by omega⟩
  rw [pow_add, Nat.mod_mul_right_div_self,
    Nat.mod_mod_of_dvd _ (dvd_pow_self 3 (Nat.succ_ne_zero j))]
  exact h

/-- Dropping the last digit of a Cantor numerator gives a Cantor numerator. -/
theorem div_three_mem_cantorInts {k P : ℕ} (hP : P ∈ cantorInts (k + 1)) :
    P / 3 ∈ cantorInts k := by
  simp only [cantorInts, Finset.mem_filter, Finset.mem_range] at hP ⊢
  refine ⟨?_, fun i hi => ?_⟩
  · rw [pow_succ] at hP
    exact Nat.div_lt_of_lt_mul (by linarith [hP.1])
  · have h := hP.2 (i + 1) (by omega)
    rwa [Nat.div_div_eq_div_mul, ← pow_succ']

/-- At most `2^k` Cantor numerators of depth `k`. -/
theorem card_cantorInts_le (k : ℕ) : (cantorInts k).card ≤ 2 ^ k := by
  induction k with
  | zero => decide
  | succ k ih =>
    have hmap : Set.MapsTo (fun P => (P / 3, P % 3)) (cantorInts (k + 1) : Set ℕ)
        ((cantorInts k ×ˢ ({0, 2} : Finset ℕ) : Finset (ℕ × ℕ)) : Set (ℕ × ℕ)) := by
      intro P hP
      have hP' := hP
      simp only [Finset.mem_coe, cantorInts, Finset.mem_filter] at hP'
      have h0 := hP'.2 0 (by omega)
      simp only [pow_zero, Nat.div_one] at h0
      simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe]
      refine ⟨div_three_mem_cantorInts hP, ?_⟩
      have : P % 3 < 3 := Nat.mod_lt _ (by norm_num)
      simp only [Finset.mem_insert, Finset.mem_singleton]
      omega
    have hinj : Set.InjOn (fun P => (P / 3, P % 3)) (cantorInts (k + 1) : Set ℕ) := by
      intro P _ P' _ h
      simp only [Prod.mk.injEq] at h
      rw [← Nat.div_add_mod P 3, ← Nat.div_add_mod P' 3, h.1, h.2]
    calc (cantorInts (k + 1)).card
        ≤ (cantorInts k ×ˢ ({0, 2} : Finset ℕ)).card := Finset.card_le_card_of_injOn _ hmap hinj
      _ = (cantorInts k).card * 2 := by rw [Finset.card_product]; rfl
      _ ≤ 2 ^ (k + 1) := by rw [pow_succ]; omega

/-- **Exact residue count.**  For `3 ∤ q` and `k ≤ b`, at most `2 · #cantorInts k ≤ 2^{k+1}`
Cantor numerators `P` of depth `b` have `P q mod 3^b` within `3^k` of `0` (on either side).
The low `k` digits of `P` fix `P q mod 3^k`, hence the residue up to the side, and the
residue fixes `P` (`q` is a unit mod `3^b`). -/
theorem card_lowResidue_le (b k q : ℕ) (hk : k ≤ b) (hq : Nat.Coprime q 3) :
    ((cantorInts b).filter fun P =>
        P * q % 3 ^ b < 3 ^ k ∨ 3 ^ b < P * q % 3 ^ b + 3 ^ k).card
      ≤ 2 * (cantorInts k).card := by
  classical
  have hdvd : 3 ^ k ∣ 3 ^ b := pow_dvd_pow 3 hk
  have hmap : Set.MapsTo (fun P => (P % 3 ^ k, decide (P * q % 3 ^ b < 3 ^ k)))
      (((cantorInts b).filter fun P =>
        P * q % 3 ^ b < 3 ^ k ∨ 3 ^ b < P * q % 3 ^ b + 3 ^ k : Finset ℕ) : Set ℕ)
      ((cantorInts k ×ˢ (Finset.univ : Finset Bool) : Finset (ℕ × Bool)) : Set (ℕ × Bool)) := by
    intro P hP
    simp only [Finset.coe_filter, Set.mem_ofPred_eq] at hP
    simp only [Finset.coe_product, Finset.coe_univ, Set.prod_univ, Set.mem_preimage,
      Finset.mem_coe]
    exact mod_mem_cantorInts hk hP.1
  have hinj : Set.InjOn (fun P => (P % 3 ^ k, decide (P * q % 3 ^ b < 3 ^ k)))
      (((cantorInts b).filter fun P =>
        P * q % 3 ^ b < 3 ^ k ∨ 3 ^ b < P * q % 3 ^ b + 3 ^ k : Finset ℕ) : Set ℕ) := by
    intro P hP P' hP' h
    simp only [Finset.coe_filter, Set.mem_ofPred_eq] at hP hP'
    simp only [Prod.mk.injEq, decide_eq_decide] at h
    have hPb : P < 3 ^ b := by
      have := hP.1; simp only [cantorInts, Finset.mem_filter, Finset.mem_range] at this
      exact this.1
    have hPb' : P' < 3 ^ b := by
      have := hP'.1; simp only [cantorInts, Finset.mem_filter, Finset.mem_range] at this
      exact this.1
    have hcm : P * q % 3 ^ b ≡ P' * q % 3 ^ b [MOD 3 ^ k] := by
      unfold Nat.ModEq
      rw [Nat.mod_mod_of_dvd _ hdvd, Nat.mod_mod_of_dvd _ hdvd, Nat.mul_mod, h.1, ← Nat.mul_mod]
    have hc : P * q % 3 ^ b = P' * q % 3 ^ b := by
      have h1 : P * q % 3 ^ b < 3 ^ b := Nat.mod_lt _ (by positivity)
      have h2 : P' * q % 3 ^ b < 3 ^ b := Nat.mod_lt _ (by positivity)
      by_cases hlt : P * q % 3 ^ b < 3 ^ k
      · exact hcm.eq_of_lt_of_lt hlt (h.2.mp hlt)
      · have hlt' : ¬ P' * q % 3 ^ b < 3 ^ k := fun h' => hlt (h.2.mpr h')
        have ha := hP.2.resolve_left hlt
        have hb := hP'.2.resolve_left hlt'
        apply hcm.eq_of_abs_lt
        generalize P * q % 3 ^ b = c at *
        generalize P' * q % 3 ^ b = c' at *
        generalize (3 : ℕ) ^ b = X at *
        generalize (3 : ℕ) ^ k = Y at *
        rw [abs_sub_lt_iff]
        constructor <;> omega
    have hcop : Nat.gcd (3 ^ b) q = 1 := Nat.Coprime.pow_left b hq.symm
    have := Nat.ModEq.cancel_right_of_coprime hcop (show P * q ≡ P' * q [MOD 3 ^ b] from hc)
    unfold Nat.ModEq at this
    rwa [Nat.mod_eq_of_lt hPb, Nat.mod_eq_of_lt hPb'] at this
  calc _ ≤ (cantorInts k ×ˢ (Finset.univ : Finset Bool)).card :=
        Finset.card_le_card_of_injOn _ hmap hinj
    _ = 2 * (cantorInts k).card := by rw [Finset.card_product, Finset.card_univ, Fintype.card_bool, mul_comm]

/-- **H0, the schedule-free barrier for the trivial (spacing) count** (kickoff seed, verified).
Write `x = 1/(τ−1)` and `L = log₃ 2`.  Avoiding every rational with `q ≤ 3^{xb}` near a
cylinder of depth `a = λb` by choosing the `(1−λ)b` free digits deterministically, with the
spacing count `Q² 3^{−a} + Q` (each rational kills at most one numerator), needs
`2x < λ + (1−λ)L` and `x < (1−λ)L`.  Then `x < L/(1+L)`, i.e. `τ > 2 + log₂ 3`, for every
`λ`: no schedule rescues the trivial count.  (Sharp at `λ = L/(1+L)`.) -/
theorem trivial_count_barrier {L x lam : ℝ} (hL : 0 < L) (hL1 : L ≤ 1)
    (hA : 2 * x < lam + (1 - lam) * L) (hB : x < (1 - lam) * L) :
    x < L / (1 + L) := by
  rw [lt_div_iff₀ (by linarith)]
  nlinarith [mul_lt_mul_of_pos_left hA hL, mul_le_mul_of_nonneg_left hB.le (by linarith : 0 ≤ 1 - L)]

/-- **H2, residue form of an approximation** (kickoff seed, verified).
`|P/3^b − p/q| < η` iff `r = P q − p 3^b` has `|r| < η q 3^b`.  Exact; the counts above work
with `r`. -/
theorem abs_sub_lt_iff_residue (P b q : ℕ) (p : ℤ) (hq : 0 < q) (η : ℝ) :
    |(P : ℝ) / 3 ^ b - p / q| < η ↔
      |(((P : ℤ) * q - p * 3 ^ b : ℤ) : ℝ)| < η * (q * 3 ^ b) := by
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  have h3 : (0 : ℝ) < 3 ^ b := by positivity
  have key : (P : ℝ) / 3 ^ b - p / q =
      (((P : ℤ) * q - p * 3 ^ b : ℤ) : ℝ) / ((q : ℝ) * 3 ^ b) := by
    push_cast
    field_simp
  rw [key, abs_div, abs_of_pos (by positivity : (0 : ℝ) < q * 3 ^ b),
    div_lt_iff₀ (by positivity)]

/-- **H3, 3-adic linearization of the inverse** (kickoff seed, verified; not used: the
congruence `P q ≡ r` is already linear in `P`, so the counts never invert `P`).  If
`P₀ u ≡ 1 (mod 3^b)` and `b ≤ 2k`, then `(P₀ + 3^k t)(u − 3^k t u²) ≡ 1 (mod 3^b)`. -/
theorem inv_linearize (P₀ u t : ℤ) (b k : ℕ) (hb : b ≤ 2 * k) (hu : P₀ * u ≡ 1 [ZMOD 3 ^ b]) :
    (P₀ + 3 ^ k * t) * (u - 3 ^ k * t * u ^ 2) ≡ 1 [ZMOD 3 ^ b] := by
  obtain ⟨c, hc⟩ := (Int.modEq_iff_dvd.mp hu.symm)
  have h2k : (3 : ℤ) ^ b ∣ 3 ^ (2 * k) := pow_dvd_pow 3 hb
  obtain ⟨d, hd⟩ := h2k
  apply Int.modEq_iff_dvd.mpr
  refine ⟨-(c - 3 ^ k * t * u * c - d * t ^ 2 * u ^ 2), ?_⟩
  have e : (3 : ℤ) ^ k * 3 ^ k = 3 ^ b * d := by rw [← pow_add, ← two_mul, hd]
  have hc' : P₀ * u = 1 + 3 ^ b * c := by linarith
  linear_combination (-1 + 3 ^ k * t * u) * hc' + t ^ 2 * u ^ 2 * e

/-- The elementary per-window ratio: `3 · 2^{−(τ−1)} < 1` iff `τ > 1 + log₂ 3`. -/
theorem exactCount_rho_lt_one (τ : ℝ) (hτ : 1 + Real.logb 2 3 < τ) :
    3 * (2 : ℝ) ^ (-(τ - 1)) < 1 := by
  have := rho_lt_one (τ + 1) (by unfold threshold; linarith)
  convert this using 3
  ring

open Classical in
/-- Run-entering count at exponent `τ`: among Cantor numerators `P` of depth `b'` placed under
an arbitrary fixed prefix `A` (the numerator is `A·3^{b'} + P` at depth `b ≥ b'`), those with
a rational `p/q ≠ (A·3^{b'}+P)/3^b`, `q ∈ [3ᵐ, 3^{m+1})`, within `q^{−τ}` number
`O(2^{b'} 3^{b−b'} 3^{−δm})`.  Only windows `(τ−1)m ≤ b` matter (`endpoint_sep`). -/
def RunEnteringCountAt (τ : ℝ) : Prop :=
  ∃ δ : ℝ, 0 < δ ∧ ∃ C : ℝ, ∀ (A b b' m : ℕ), b' ≤ b → ((τ - 1) * m : ℝ) ≤ b →
    (((cantorInts b').filter fun P => ∃ q : ℕ, 3 ^ m ≤ q ∧ q < 3 ^ (m + 1) ∧ ∃ r : ℤ, r ≠ 0 ∧
        |(r : ℝ)| < 3 ^ b * (q : ℝ) ^ (1 - τ) ∧
        ((A * 3 ^ b' + P : ℕ) * q : ℤ) ≡ r [ZMOD 3 ^ b]).card : ℝ)
      ≤ C * 2 ^ b' * 3 ^ (b - b') * (3 : ℝ) ^ (-(δ * m))

/-- **The crux for `2 < μ₀ ≤ 1 + log₂ 3`** (open conjecture node).  The run-entering count at
every `τ > 2`: the Cantor numerators meet the modular hyperbola `{r q̄ mod 3^b : q ≈ 3ᵐ,
|r| < 3^b q^{1−τ}}` (density `3^{(2−τ)m}`) at its expected rate up to `3^{−δm}`.  Proved for
`τ > 1 + log₂ 3` (`runEnteringCountAt_of_lt`).  Below, `#{(q, r)} > 2^b` at the window's
bottom `m ≈ b/τ`, so no count that loses the sign of the Riesz product can work: the uniform
`L¹` bound `Σ_s |Ĉ(s)| ≤ 4^b` (`Λ ≤ 4/3`, numerically `Λ = 1.29663`) reaches only
`m < b·log₃(2/Λ) ≈ 0.394 b`.  A sum–product / Kloosterman-with-restricted-digits estimate in
`ℤ/3^b`.  Evidence: heuristic density; `experiments/stretch_exact_count.py`. -/
def RunEnteringCount : Prop := ∀ τ : ℝ, 2 < τ → RunEnteringCountAt τ

/-- **The exact residue count proves the run-entering count above `1 + log₂ 3`.**
Confidence 90% (English proof: `card_lowResidue_le` per `q` with `k = b − ⌊(τ−1)m⌋`, the
prefix shifts `P ↦ A·3^{b'} + P` without changing low digits when `k ≤ b'`, and the trivial
bound `2^{b'}` covers `k > b'`; sum over `2·3ᵐ` denominators, `δ = −log₃(3·2^{−(τ−1)})`;
`q` divisible by `3` reduces to modulus `3^{b−v₃(q)}`). -/
theorem runEnteringCountAt_of_lt (τ : ℝ) (hτ : 1 + Real.logb 2 3 < τ) :
    RunEnteringCountAt τ := by
  sorry

/-- **Mid range: the exponent upper bound for `1 + log₂ 3 < μ₀`.**  Confidence 65%.

English proof.  Borel–Cantelli over windows `q ∈ [3ᵐ, 3^{m+1})`, with `b = a_{k+1}` the run
start following the window (units of `b`, `u = m/b`; earlier runs are `O(b/k)` digits):
* interior windows (`τu ≤ 1` or past the run end): cylinder count `3ᵐ 2^{−(τ−1)m(1−o(1))}`;
* run-entering, `1/τ ≤ u ≤ 1/(τ−1)`: `runEnteringCountAt_of_lt`, the same rate;
* `1/(τ−1) < u < μ₀ − 1`: empty, by `endpoint_sep` and `|x − P/3^b| ≤ 3^{−μ₀ b}`, except the
  reduced `P/3^b` itself, whose exponent exceeds `τ` with probability `2^{−Ω(b)}` (3-adic
  valuation of `P` plus zeros after the run);
* post-run, `μ₀ − 1 ≤ u < μ₀`: `q ≥ 3^b` runs over complete residue systems, so
  `#{(P, q, r) : P q ≡ r}` is exact, and the tail `y` past the run must hit a ball of radius
  `3^{(μ₀−τu)b}`: cost exponent `2u − μ₀ − log₃2·(τu − μ₀)`, negative on the range when
  `τ > 1 + log₂ 3`.
The last two cases are by hand only. -/
theorem ae_not_liouvilleWith_mid (μ₀ : ℚ) (hμ : 1 + Real.logb 2 3 < μ₀) (τ : ℝ)
    (hτ : (μ₀ : ℝ) < τ) :
    ∀ᵐ ω ∂coins, ¬ LiouvilleWith τ (cantorExpReal μ₀ ω) := by
  sorry


end NormalNumbers.CantorExactExponentStretch
