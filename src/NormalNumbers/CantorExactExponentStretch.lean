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

**Confidence (restated 2026-10-06, end of lap 2):** node `ae_not_liouvilleWith_all` 80% (was
10%).  What moved: `RunEnteringCount` is not a Kloosterman wall.  Fractions `r/q` of small height
are separated 3-adically (`padic_sep`): two run-entering hits whose numerators agree mod `3^j`,
`3^j > |r q' − r' q|`, have the same fraction, so the hitting numerators are fixed by
`≈ log₃(|r| q)` low digits plus `v₃(q)` top digits, a count `≲ (|r| q)^{log₃ 2}`, a power saving
for every `τ > 2` (`hit_mass_padic`).  Windows that do not enter a run use the real Farey
separation (`hit_mass_farey`, mass `2^{−F[2m+3, L−2)}`).  The node and the stretch headline are
wired from the one leaf `ev_expTest_mass_all`; the remaining 20% is formalization risk in the six
elementary leaves (the case split needs `E_k = o(m)` and `L + 1 ≤ E_{k+1}`).  BFR bet: 5% (the
3-adic count is the elementary analogue of the trivial `Q^{2 dim K}` bound, not a new count of
rationals near `K`).

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
formula for `τ` near 1) has the same small-`α` regime.  (Superseded 2026-10-06: the endpoint
count is elementary 3-adically, `hit_mass_padic`; confidence restated above.)
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

/-- Dropping the last `n` digits of a Cantor numerator gives a Cantor numerator. -/
theorem div_pow_mem_cantorInts {b n P : ℕ} (hP : P ∈ cantorInts b) :
    P / 3 ^ n ∈ cantorInts (b - n) := by
  simp only [cantorInts, Finset.mem_filter, Finset.mem_range] at hP ⊢
  refine ⟨?_, fun i hi => ?_⟩
  · apply Nat.div_lt_of_lt_mul
    calc P < 3 ^ b := hP.1
      _ ≤ 3 ^ (b - n + n) := Nat.pow_le_pow_right (by norm_num) (by omega)
      _ = 3 ^ n * 3 ^ (b - n) := by rw [pow_add, mul_comm]
  · have h := hP.2 (n + i) (by omega)
    rwa [Nat.div_div_eq_div_mul, ← pow_add]

/-- From a small nonzero residue to the side condition mod `3^{b−v}` used by
`card_residue_le_gen`. -/
theorem residue_cond_of_exists (A b b' k v q' P : ℕ) (hk : k ≤ b) (hv : v ≤ k)
    (h : ∃ r : ℤ, r ≠ 0 ∧ |r| < 3 ^ k ∧
        (((A * 3 ^ b' + P : ℕ) : ℤ) * ((3 ^ v * q' : ℕ) : ℤ)) ≡ r [ZMOD 3 ^ b]) :
    (A * 3 ^ b' + P) * q' % 3 ^ (b - v) < 3 ^ (k - v) ∨
      3 ^ (b - v) < (A * 3 ^ b' + P) * q' % 3 ^ (b - v) + 3 ^ (k - v) := by
  obtain ⟨r, -, hrk, hr⟩ := h
  have hb : (3 : ℤ) ^ b = 3 ^ v * 3 ^ (b - v) := by rw [← pow_add]; congr 1; omega
  have hkk : (3 : ℤ) ^ k = 3 ^ v * 3 ^ (k - v) := by rw [← pow_add]; congr 1; omega
  have hd : (3 : ℤ) ^ b ∣ r - ((A * 3 ^ b' + P : ℕ) : ℤ) * ((3 ^ v * q' : ℕ) : ℤ) :=
    Int.modEq_iff_dvd.mp hr
  have hdv : (3 : ℤ) ^ v ∣ r := by
    have h1 : (3 : ℤ) ^ v ∣ r - ((A * 3 ^ b' + P : ℕ) : ℤ) * ((3 ^ v * q' : ℕ) : ℤ) :=
      (Dvd.intro _ hb.symm).trans hd
    have h2 : (3 : ℤ) ^ v ∣ ((A * 3 ^ b' + P : ℕ) : ℤ) * ((3 ^ v * q' : ℕ) : ℤ) := by
      push_cast; exact Dvd.dvd.mul_left (Dvd.intro _ rfl) _
    have := dvd_add h1 h2
    rwa [sub_add_cancel] at this
  obtain ⟨s, rfl⟩ := hdv
  have h3v : (0 : ℤ) < 3 ^ v := by positivity
  have hs : |s| < 3 ^ (k - v) := by
    rw [abs_mul, abs_of_pos h3v, hkk] at hrk
    exact lt_of_mul_lt_mul_left hrk h3v.le
  have hmod : (((A * 3 ^ b' + P) * q' : ℕ) : ℤ) ≡ s [ZMOD 3 ^ (b - v)] := by
    apply Int.modEq_iff_dvd.mpr
    rw [hb] at hd
    have : (3 : ℤ) ^ v * 3 ^ (b - v) ∣ 3 ^ v * (s - (((A * 3 ^ b' + P) * q' : ℕ) : ℤ)) := by
      convert hd using 1; push_cast; ring
    exact (mul_dvd_mul_iff_left h3v.ne').mp this
  have hc : ((((A * 3 ^ b' + P) * q' % 3 ^ (b - v) : ℕ)) : ℤ) = s % 3 ^ (b - v) := by
    rw [Int.natCast_mod]; push_cast at hmod ⊢; exact hmod
  have hjn : (3 : ℤ) ^ (k - v) ≤ 3 ^ (b - v) := pow_le_pow_right₀ (by norm_num) (by omega)
  rw [abs_lt] at hs
  have key : ((((A * 3 ^ b' + P) * q' % 3 ^ (b - v) : ℕ)) : ℤ) = s ∨
      ((((A * 3 ^ b' + P) * q' % 3 ^ (b - v) : ℕ)) : ℤ) = s + 3 ^ (b - v) := by
    rw [hc]
    rcases le_or_gt 0 s with h0 | h0
    · left; exact Int.emod_eq_of_lt h0 (by linarith)
    · right
      rw [← Int.add_emod_right]
      exact Int.emod_eq_of_lt (by linarith) (by linarith)
  clear hrk hr hd hmod hc hb hkk
  generalize (A * 3 ^ b' + P) * q' % 3 ^ (b - v) = c at key ⊢
  have e1 : ((3 ^ (k - v) : ℕ) : ℤ) = (3 : ℤ) ^ (k - v) := by push_cast; ring
  have e2 : ((3 ^ (b - v) : ℕ) : ℤ) = (3 : ℤ) ^ (b - v) := by push_cast; ring
  rw [← e1] at hs; rw [← e2] at key hjn; rw [← e1] at hjn
  generalize 3 ^ (k - v) = Y at *
  generalize 3 ^ (b - v) = Z at *
  omega

open Classical in
/-- **Exact residue count, general denominator and prefix.**  For `q = 3^v q'` with `3 ∤ q'`,
a fixed prefix `A` above digit `b'`, and `k ≤ b`: at most `2^{k+1}` Cantor numerators
`P` of depth `b'` make `(A·3^{b'} + P) q ≡ r (mod 3^b)` for some `0 < |r| < 3^k`.  Low
`k − v` digits and a side bit fix the residue mod `3^{b−v}`; the top digits above `b − v` are
Cantor too, so they cost `2^{v}` at most, not `3^v`. -/
theorem card_residue_le_gen (A b b' k v q' : ℕ) (hb' : b' ≤ b) (hk : k ≤ b)
    (hq' : Nat.Coprime q' 3) :
    ((cantorInts b').filter fun P => ∃ r : ℤ, r ≠ 0 ∧ |r| < 3 ^ k ∧
        (((A * 3 ^ b' + P : ℕ) : ℤ) * ((3 ^ v * q' : ℕ) : ℤ)) ≡ r [ZMOD 3 ^ b]).card
      ≤ 2 ^ (k + 1) := by
  by_cases hv : k < v
  · refine le_trans (le_of_eq ?_) (Nat.zero_le _)
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    rintro P - ⟨r, hr0, hrk, hr⟩
    apply hr0
    have hd : (3 : ℤ) ^ b ∣ r - ((A * 3 ^ b' + P : ℕ) : ℤ) * ((3 ^ v * q' : ℕ) : ℤ) :=
      Int.modEq_iff_dvd.mp hr
    have hw : (3 : ℤ) ^ (min v b) ∣ r := by
      have h1 := (pow_dvd_pow (3 : ℤ) (min_le_right v b)).trans hd
      have h2 : (3 : ℤ) ^ (min v b) ∣ ((A * 3 ^ b' + P : ℕ) : ℤ) * ((3 ^ v * q' : ℕ) : ℤ) := by
        push_cast
        exact Dvd.dvd.mul_left (Dvd.dvd.mul_right (pow_dvd_pow 3 (min_le_left _ _)) _) _
      have := dvd_add h1 h2
      rwa [sub_add_cancel] at this
    exact Int.eq_zero_of_abs_lt_dvd hw
      (lt_of_lt_of_le hrk (pow_le_pow_right₀ (by norm_num) (by omega)))
  push Not at hv
  by_cases hj : b' < k - v
  · calc _ ≤ (cantorInts b').card := Finset.card_filter_le _ _
      _ ≤ 2 ^ b' := card_cantorInts_le _
      _ ≤ 2 ^ (k + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  push Not at hj
  set j := k - v with hjdef
  set n := b - v with hndef
  have hjn : j ≤ n := by omega
  have hdj : 3 ^ j ∣ 3 ^ n := pow_dvd_pow 3 hjn
  have hdj' : 3 ^ j ∣ A * 3 ^ b' := Dvd.dvd.mul_left (pow_dvd_pow 3 hj) _
  have hmap : Set.MapsTo (fun P => ((P % 3 ^ j, decide ((A * 3 ^ b' + P) * q' % 3 ^ n < 3 ^ j)),
        P / 3 ^ n))
      (((cantorInts b').filter fun P => ∃ r : ℤ, r ≠ 0 ∧ |r| < 3 ^ k ∧
        (((A * 3 ^ b' + P : ℕ) : ℤ) * ((3 ^ v * q' : ℕ) : ℤ)) ≡ r [ZMOD 3 ^ b] : Finset ℕ) : Set ℕ)
      (((cantorInts j ×ˢ (Finset.univ : Finset Bool)) ×ˢ cantorInts (b' - n) :
        Finset ((ℕ × Bool) × ℕ)) : Set ((ℕ × Bool) × ℕ)) := by
    intro P hP
    simp only [Finset.coe_filter, Set.mem_ofPred_eq] at hP
    simp only [Finset.coe_product, Finset.coe_univ, Set.prod_univ, Set.mem_prod, Set.mem_preimage,
      Finset.mem_coe]
    exact ⟨mod_mem_cantorInts hj hP.1, div_pow_mem_cantorInts hP.1⟩
  have hinj : Set.InjOn (fun P => ((P % 3 ^ j, decide ((A * 3 ^ b' + P) * q' % 3 ^ n < 3 ^ j)),
        P / 3 ^ n))
      (((cantorInts b').filter fun P => ∃ r : ℤ, r ≠ 0 ∧ |r| < 3 ^ k ∧
        (((A * 3 ^ b' + P : ℕ) : ℤ) * ((3 ^ v * q' : ℕ) : ℤ)) ≡ r [ZMOD 3 ^ b] : Finset ℕ) :
          Set ℕ) := by
    intro P hP P' hP' h
    simp only [Finset.coe_filter, Set.mem_ofPred_eq] at hP hP'
    simp only [Prod.mk.injEq, decide_eq_decide] at h
    obtain ⟨⟨hlow, hflag⟩, htop⟩ := h
    have cP := residue_cond_of_exists A b b' k v q' P hk hv hP.2
    have cP' := residue_cond_of_exists A b b' k v q' P' hk hv hP'.2
    have hcm : (A * 3 ^ b' + P) * q' % 3 ^ n ≡ (A * 3 ^ b' + P') * q' % 3 ^ n [MOD 3 ^ j] := by
      unfold Nat.ModEq
      rw [Nat.mod_mod_of_dvd _ hdj, Nat.mod_mod_of_dvd _ hdj, Nat.mul_mod, Nat.add_mod, hlow,
        ← Nat.add_mod, ← Nat.mul_mod]
    have hc : (A * 3 ^ b' + P) * q' % 3 ^ n = (A * 3 ^ b' + P') * q' % 3 ^ n := by
      by_cases hlt : (A * 3 ^ b' + P) * q' % 3 ^ n < 3 ^ j
      · exact hcm.eq_of_lt_of_lt hlt (hflag.mp hlt)
      · have hlt' : ¬ (A * 3 ^ b' + P') * q' % 3 ^ n < 3 ^ j := fun h' => hlt (hflag.mpr h')
        have ha := cP.resolve_left hlt
        have hb := cP'.resolve_left hlt'
        have h1 : (A * 3 ^ b' + P) * q' % 3 ^ n < 3 ^ n := Nat.mod_lt _ (by positivity)
        have h2 : (A * 3 ^ b' + P') * q' % 3 ^ n < 3 ^ n := Nat.mod_lt _ (by positivity)
        apply hcm.eq_of_abs_lt
        generalize (A * 3 ^ b' + P) * q' % 3 ^ n = c at *
        generalize (A * 3 ^ b' + P') * q' % 3 ^ n = c' at *
        generalize (3 : ℕ) ^ n = X at *
        generalize (3 : ℕ) ^ j = Y at *
        rw [abs_sub_lt_iff]
        constructor <;> omega
    have hcop : Nat.gcd (3 ^ n) q' = 1 := Nat.Coprime.pow_left n hq'.symm
    have hX := Nat.ModEq.cancel_right_of_coprime hcop
      (show (A * 3 ^ b' + P) * q' ≡ (A * 3 ^ b' + P') * q' [MOD 3 ^ n] from hc)
    have hPP : P % 3 ^ n = P' % 3 ^ n := Nat.ModEq.add_left_cancel' _ hX
    rw [← Nat.div_add_mod P (3 ^ n), ← Nat.div_add_mod P' (3 ^ n), htop, hPP]
  calc _ ≤ ((cantorInts j ×ˢ (Finset.univ : Finset Bool)) ×ˢ cantorInts (b' - n)).card :=
        Finset.card_le_card_of_injOn _ hmap hinj
    _ = (cantorInts j).card * 2 * (cantorInts (b' - n)).card := by
        rw [Finset.card_product, Finset.card_product, Finset.card_univ, Fintype.card_bool]
    _ ≤ 2 ^ j * 2 * 2 ^ (b' - n) := by
        gcongr
        · exact card_cantorInts_le _
        · exact card_cantorInts_le _
    _ ≤ 2 ^ (k + 1) := by
        rw [← pow_succ, ← pow_add]
        exact Nat.pow_le_pow_right (by norm_num) (by omega)

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

/-- **The per-`q` method stops at `1 + log₂ 3`.**  For `τ ≤ 1 + log₂ 3` the per-window cost
`3ᵐ · 2^{−(τ−1)m}` of any bound that is uniform in `q` at the `card_lowResidue_le` rate does
not decay. -/
theorem exactCount_rho_ge_one (τ : ℝ) (hτ : τ ≤ 1 + Real.logb 2 3) :
    1 ≤ 3 * (2 : ℝ) ^ (-(τ - 1)) := by
  have h1 : (3 : ℝ) = 2 ^ Real.logb 2 3 :=
    (Real.rpow_logb (by norm_num) (by norm_num) (by norm_num)).symm
  rw [h1, ← Real.rpow_add (by norm_num)]
  exact Real.one_le_rpow (by norm_num) (by linarith)

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

/-- Real bookkeeping for `runEnteringCountAt_of_lt`: `2·3ᵐ·2^{b−⌊(τ−1)m⌋+1} ≤ 8·2^{b'}3^{b−b'}ρᵐ`. -/
theorem runEntering_real_bound (τ : ℝ) (b b' m : ℕ) (hb' : b' ≤ b) (hK : ⌊(τ - 1) * m⌋₊ ≤ b) :
    2 * (3 : ℝ) ^ m * 2 ^ (b - ⌊(τ - 1) * m⌋₊ + 1) ≤
      8 * 2 ^ b' * 3 ^ (b - b') * (3 * (2 : ℝ) ^ (-(τ - 1))) ^ m := by
  set K := ⌊(τ - 1) * m⌋₊
  have hKlt : (τ - 1) * m < K + 1 := Nat.lt_floor_add_one _
  have h2b : (2 : ℝ) ^ b ≤ 2 ^ b' * 3 ^ (b - b') := by
    calc (2 : ℝ) ^ b = 2 ^ b' * 2 ^ (b - b') := by rw [← pow_add]; congr 1; omega
      _ ≤ 2 ^ b' * 3 ^ (b - b') := by gcongr; norm_num
  have hsplit : (2 : ℝ) ^ (b - K + 1) * 2 ^ K = 2 * 2 ^ b := by
    rw [← pow_add, ← pow_succ']; congr 1; omega
  have hK2 : (2 : ℝ) ^ (-(τ - 1) * m) * 2 ≥ 1 / 2 ^ K := by
    rw [ge_iff_le, div_le_iff₀ (by positivity), ← Real.rpow_natCast, ← Real.rpow_add_one (by norm_num),
      ← Real.rpow_add (by norm_num)]
    apply Real.one_le_rpow (by norm_num); linarith
  have hρm : (3 * (2 : ℝ) ^ (-(τ - 1))) ^ m = 3 ^ m * 2 ^ (-(τ - 1) * m) := by
    rw [mul_pow, ← Real.rpow_mul_natCast (by norm_num)]
  rw [hρm]
  have h2K : (0 : ℝ) < 2 ^ K := by positivity
  have e : (2 : ℝ) ^ (b - K + 1) = 2 * 2 ^ b * (1 / 2 ^ K) := by
    field_simp; linarith [hsplit]
  rw [e]
  have h3 : (0 : ℝ) ≤ 3 ^ m := by positivity
  have hb0 : (0 : ℝ) ≤ 2 ^ b := by positivity
  calc 2 * (3 : ℝ) ^ m * (2 * 2 ^ b * (1 / 2 ^ K))
      ≤ 2 * 3 ^ m * (2 * 2 ^ b * (2 ^ (-(τ - 1) * m) * 2)) := by gcongr
    _ = 8 * 2 ^ b * (3 ^ m * 2 ^ (-(τ - 1) * m)) := by ring
    _ ≤ 8 * (2 ^ b' * 3 ^ (b - b')) * (3 ^ m * 2 ^ (-(τ - 1) * m)) := by gcongr
    _ = _ := by ring

/-- **The exact residue count proves the run-entering count above `1 + log₂ 3`.**
Confidence 90% (English proof: `card_lowResidue_le` per `q` with `k = b − ⌊(τ−1)m⌋`, the
prefix shifts `P ↦ A·3^{b'} + P` without changing low digits when `k ≤ b'`, and the trivial
bound `2^{b'}` covers `k > b'`; sum over `2·3ᵐ` denominators, `δ = −log₃(3·2^{−(τ−1)})`;
`q` divisible by `3` reduces to modulus `3^{b−v₃(q)}`). -/
theorem runEnteringCountAt_of_lt (τ : ℝ) (hτ : 1 + Real.logb 2 3 < τ) :
    RunEnteringCountAt τ := by
  classical
  have hlog : 0 < Real.logb 2 3 := Real.logb_pos (by norm_num) (by norm_num)
  have hτ1 : 1 < τ := by linarith
  set ρ := 3 * (2 : ℝ) ^ (-(τ - 1)) with hρdef
  have hρ1 : ρ < 1 := exactCount_rho_lt_one τ hτ
  have hρ0 : 0 < ρ := by positivity
  refine ⟨-Real.logb 3 ρ, by linarith [Real.logb_neg (by norm_num : (1 : ℝ) < 3) hρ0 hρ1], 8, ?_⟩
  intro A b b' m hb' hwin
  have h3δ : (3 : ℝ) ^ (-(-Real.logb 3 ρ * m)) = ρ ^ m := by
    rw [neg_mul, neg_neg, Real.rpow_mul_natCast (by norm_num),
      Real.rpow_logb (by norm_num) (by norm_num) hρ0]
  rw [h3δ]
  have hτm : (0 : ℝ) ≤ (τ - 1) * m := by positivity
  set K := ⌊(τ - 1) * m⌋₊ with hKdef
  have hKle : (K : ℝ) ≤ (τ - 1) * m := Nat.floor_le hτm
  have hKb : K ≤ b := by exact_mod_cast hKle.trans hwin
  set k := b - K with hkdef
  have hkb : k ≤ b := Nat.sub_le _ _
  have hsub : ((cantorInts b').filter fun P => ∃ q : ℕ, 3 ^ m ≤ q ∧ q < 3 ^ (m + 1) ∧
      ∃ r : ℤ, r ≠ 0 ∧ |(r : ℝ)| < 3 ^ b * (q : ℝ) ^ (1 - τ) ∧
        ((A * 3 ^ b' + P : ℕ) * q : ℤ) ≡ r [ZMOD 3 ^ b]) ⊆
      (Finset.Ico (3 ^ m : ℕ) (3 ^ (m + 1))).biUnion (fun q : ℕ => (cantorInts b').filter fun P =>
        ∃ r : ℤ, r ≠ 0 ∧ |r| < 3 ^ k ∧ (((A * 3 ^ b' + P : ℕ) : ℤ) * (q : ℤ)) ≡ r [ZMOD 3 ^ b]) := by
    intro P hP
    simp only [Finset.mem_filter] at hP
    obtain ⟨hPC, q, hq1, hq2, r, hr0, hrq, hr⟩ := hP
    simp only [Finset.mem_biUnion, Finset.mem_Ico, Finset.mem_filter]
    refine ⟨q, ⟨hq1, hq2⟩, hPC, r, hr0, ?_, hr⟩
    have hq0 : (0 : ℝ) < (3 : ℝ) ^ m := by positivity
    have hqm : (3 : ℝ) ^ m ≤ q := by exact_mod_cast hq1
    have h1 : (q : ℝ) ^ (1 - τ) ≤ ((3 : ℝ) ^ m) ^ (1 - τ) :=
      Real.rpow_le_rpow_of_nonpos hq0 hqm (by linarith)
    have h2 : (3 : ℝ) ^ b * ((3 : ℝ) ^ m) ^ (1 - τ) ≤ (3 : ℝ) ^ k := by
      rw [← Real.rpow_natCast (3 : ℝ) m, ← Real.rpow_mul (by norm_num), ← Real.rpow_natCast (3 : ℝ) b,
        ← Real.rpow_add (by norm_num), ← Real.rpow_natCast (3 : ℝ) k]
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      rw [hkdef, Nat.cast_sub hKb]
      nlinarith
    have h3 : |(r : ℝ)| < (3 : ℝ) ^ k :=
      lt_of_lt_of_le hrq ((mul_le_mul_of_nonneg_left h1 (by positivity)).trans h2)
    exact_mod_cast h3
  have hper : ∀ q ∈ Finset.Ico (3 ^ m : ℕ) (3 ^ (m + 1)), ((cantorInts b').filter fun P =>
        ∃ r : ℤ, r ≠ 0 ∧ |r| < 3 ^ k ∧
          (((A * 3 ^ b' + P : ℕ) : ℤ) * (q : ℤ)) ≡ r [ZMOD 3 ^ b]).card ≤ 2 ^ (k + 1) := by
    intro q hq
    have hq0 : q ≠ 0 := by
      simp only [Finset.mem_Ico] at hq; have := Nat.one_le_pow m 3 (by norm_num); omega
    obtain ⟨v, q', hndvd, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hq0 3 (by norm_num)
    have hcop : Nat.Coprime q' 3 :=
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hndvd).symm
    exact card_residue_le_gen A b b' k v q' hb' hkb hcop
  have hcard : (((cantorInts b').filter fun P => ∃ q : ℕ, 3 ^ m ≤ q ∧ q < 3 ^ (m + 1) ∧
      ∃ r : ℤ, r ≠ 0 ∧ |(r : ℝ)| < 3 ^ b * (q : ℝ) ^ (1 - τ) ∧
        ((A * 3 ^ b' + P : ℕ) * q : ℤ) ≡ r [ZMOD 3 ^ b]).card) ≤ 2 * 3 ^ m * 2 ^ (k + 1) := by
    calc _ ≤ _ := Finset.card_le_card hsub
      _ ≤ ∑ q ∈ Finset.Ico (3 ^ m : ℕ) (3 ^ (m + 1)), ((cantorInts b').filter fun P =>
        ∃ r : ℤ, r ≠ 0 ∧ |r| < 3 ^ k ∧
          (((A * 3 ^ b' + P : ℕ) : ℤ) * (q : ℤ)) ≡ r [ZMOD 3 ^ b]).card := Finset.card_biUnion_le
      _ ≤ (Finset.Ico (3 ^ m : ℕ) (3 ^ (m + 1))).card * 2 ^ (k + 1) := Finset.sum_le_card_nsmul _ _ _ hper
      _ = 2 * 3 ^ m * 2 ^ (k + 1) := by
        rw [Nat.card_Ico, pow_succ]; congr 1; omega
  calc _ ≤ ((2 * 3 ^ m * 2 ^ (k + 1) : ℕ) : ℝ) := by exact_mod_cast hcard
    _ = 2 * (3 : ℝ) ^ m * 2 ^ (b - K + 1) := by push_cast; rfl
    _ ≤ _ := runEntering_real_bound τ b b' m hb' hKb

/-- Equal depth-`n` numerators force equal free coins below `n`. -/
theorem agree_of_hd_eq (free : ℕ → Bool) (ω ω' : ℕ → Bool) (n : ℕ)
    (h : hd free ω n = hd free ω' n) : ∀ i < n, free i = true → ω i = ω' i := by
  induction n with
  | zero => intro i hi; omega
  | succ n ih =>
    rw [hd_succ, hd_succ] at h
    have hd2 := ptDigit_le_two free ω n
    have hd2' := ptDigit_le_two free ω' n
    have h1 : hd free ω n = hd free ω' n := by omega
    have h2 : ptDigit free ω n = ptDigit free ω' n := by omega
    intro i hi hf
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · exact ih h1 i hi hf
    · unfold ptDigit at h2
      cases hw : ω i <;> cases hw' : ω' i <;> simp_all

/-- **Union bound over numerators**: the coin mass of `hd ∈ S` is at most `|S| · 2^{−F(n)}`. -/
theorem coins_hd_mem_le (free : ℕ → Bool) (n : ℕ) (S : Finset ℕ) :
    coins.real {ω | hd free ω n ∈ S} ≤ S.card * (1 / 2 : ℝ) ^ freeCount free n := by
  classical
  have hsub : {ω | hd free ω n ∈ S} ⊆ ⋃ t ∈ S, {ω | hd free ω n = t} := by
    intro ω hω; simp only [Set.mem_iUnion, Set.mem_ofPred_eq] at hω ⊢; exact ⟨_, hω, rfl⟩
  refine (measureReal_mono hsub (measure_ne_top _ _)).trans ((measureReal_biUnion_finset_le _ _).trans ?_)
  rw [← nsmul_eq_mul]
  refine Finset.sum_le_card_nsmul _ _ _ fun t _ => ?_
  by_cases hE : ∃ ω₀, hd free ω₀ n = t
  · obtain ⟨ω₀, rfl⟩ := hE
    have hs : {ω | hd free ω n = hd free ω₀ n} ⊆
        {ω | ∀ i ∈ (Finset.range n).filter fun i => free i = true, ω i = ω₀ i} := by
      intro ω hω i hi
      simp only [Finset.mem_filter, Finset.mem_range] at hi
      exact agree_of_hd_eq free ω ω₀ n hω i hi.1 hi.2
    refine (measureReal_mono hs).trans (le_of_eq ?_)
    rw [coins_real_cyl]; rfl
  · push Not at hE
    have : {ω | hd free ω n = t} = ∅ := by ext ω; simpa using hE ω
    rw [this, measureReal_empty]; positivity
/-- Dropping the last `j` digits of a depth-`(a+j)` numerator. -/
theorem hd_add_div (free : ℕ → Bool) (ω : ℕ → Bool) (a j : ℕ) :
    hd free ω (a + j) / 3 ^ j = hd free ω a := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [← add_assoc, hd_succ, pow_succ', ← Nat.div_div_eq_div_mul]
    have := ptDigit_le_two free ω (a + j)
    rw [show (3 * hd free ω (a + j) + ptDigit free ω (a + j)) / 3 = hd free ω (a + j) by omega, ih]

/-- Every coin numerator has Cantor digits. -/
theorem hd_mem_cantorInts (free : ℕ → Bool) (ω : ℕ → Bool) (n : ℕ) :
    hd free ω n ∈ cantorInts n := by
  simp only [cantorInts, Finset.mem_filter, Finset.mem_range]
  refine ⟨hd_lt free ω n, fun i hi => ?_⟩
  obtain ⟨c, rfl⟩ : ∃ c, n = (c + 1) + i := ⟨n - i - 1, by omega⟩
  rw [hd_add_div, hd_succ]
  have := ptDigit_eq_zero_or free ω c
  omega

open Classical in
/-- **Run-entering mass by the exact residue count.**  Digits `[a, b)` free, `[b, L]` forced
(the window enters a run at `b`).  A hit is `P q ≡ r (mod 3^b)` for the depth-`b` numerator `P`
with `|r| < 3^{m+2+b−(L+1)}`: if `r ≠ 0`, `card_residue_le_gen` per prefix and per `q`, and
`coins_hd_mem_le`; if `r = 0`, the digits `[m, b)` vanish. -/
theorem hit_mass_runEntering (free : ℕ → Bool) (m L a b : ℕ) (ham : a ≤ m) (hmb : m ≤ b)
    (hbn : b ≤ L + 1) (hm2 : m + 2 ≤ L + 1) (hk : L + 1 - b ≤ m + 2)
    (hfree : ∀ i, a ≤ i → i < b → free i = true)
    (hforced : ∀ i, b ≤ i → i < L + 1 → free i = false) :
    coins.real {ω | CantorExpGeneric.hitB free m L (pre ω (L + 1)) = true} ≤
      2 * 3 ^ m * 2 ^ (m + 3 + b - (L + 1)) * (1 / 2 : ℝ) ^ (b - a) + (1 / 2 : ℝ) ^ (b - m) := by
  set n := L + 1 with hn
  set k := m + 2 + b - n with hkdef
  have hkb : k ≤ b := by omega
  set S : Finset ℕ := (HS free a).biUnion fun A => (Finset.Ico (3 ^ m : ℕ) (3 ^ (m + 1))).biUnion
    fun q : ℕ => ((cantorInts (b - a)).filter fun P => ∃ r : ℤ, r ≠ 0 ∧ |r| < 3 ^ k ∧
      (((A * 3 ^ (b - a) + P : ℕ) : ℤ) * (q : ℤ)) ≡ r [ZMOD 3 ^ b]).image (A * 3 ^ (b - a) + ·)
    with hS
  have hsub : {ω | CantorExpGeneric.hitB free m L (pre ω n) = true} ⊆
      {ω | hd free ω b ∈ S} ∪ {ω | ∀ i, m ≤ i → i < b → free i = true → ω i = false} := by
    intro ω hω
    simp only [Set.mem_ofPred_eq] at hω
    obtain ⟨q, pp, hq2, hpp, hq1, hc⟩ := (hitB_iff free m L _).1 hω
    rw [tNum_pre] at hc
    have hq0 : 0 < q := lt_of_lt_of_le (by positivity) hq1
    have hT : hd free ω n = 3 ^ (n - b) * hd free ω b :=
      hd_zero_ext free ω b n hbn (fun i h1 h2 => by simp [ptDigit, hforced i h1 h2])
    set P' := hd free ω b with hP'
    rw [hT] at hc
    obtain ⟨hc1, hc2⟩ := hc
    -- residue
    set r : ℤ := (P' : ℤ) * q - pp * 3 ^ b with hr
    have h3nb : (3 : ℤ) ^ n = 3 ^ (n - b) * 3 ^ b := by rw [← pow_add]; congr 1; omega
    have habs : (3 : ℤ) ^ (n - b) * |r| ≤ 3 * q := by
      have e : (3 : ℤ) ^ (n - b) * r = ((3 ^ (n - b) * P' : ℕ) : ℤ) * q - pp * 3 ^ n := by
        rw [h3nb, hr]; push_cast; ring
      rw [← abs_of_pos (by positivity : (0:ℤ) < 3 ^ (n - b)), ← abs_mul, e, abs_le]
      constructor
      · have : ((pp * 3 ^ n : ℕ) : ℤ) ≤ ((3 ^ (n - b) * P' * q + 3 * q : ℕ) : ℤ) := by exact_mod_cast hc2
        push_cast at this ⊢; linarith
      · have : ((3 ^ (n - b) * P' * q : ℕ) : ℤ) ≤ ((pp * 3 ^ n + 3 * q : ℕ) : ℤ) := by exact_mod_cast hc1
        push_cast at this ⊢; linarith
    have hrk : |r| < 3 ^ k := by
      have hq3 : (3 : ℤ) * q < 3 ^ (n - b) * 3 ^ k := by
        rw [← pow_add, show n - b + k = m + 2 by omega, pow_succ', pow_succ']
        have : (q : ℤ) < 3 ^ (m + 1) := by exact_mod_cast hq2
        rw [pow_succ'] at this; linarith
      exact lt_of_mul_lt_mul_left (habs.trans_lt hq3) (by positivity)
    by_cases hr0 : r = 0
    · right
      have heq : pp * 3 ^ b = P' * q := by
        have : (pp : ℤ) * 3 ^ b = (P' : ℤ) * q := by linarith
        exact_mod_cast this
      have hdvd := pow_dvd_of_eq hq0.ne' hq2 heq
      have hz := digits_zero_of_dvd free ω (b - m) b (by omega) hdvd
      intro i h1 h2 hf
      have := hz i (by omega) h2
      simp only [ptDigit, hf, Bool.true_and] at this
      cases hw : ω i <;> simp_all
    · left
      simp only [Set.mem_ofPred_eq, hS, Finset.mem_biUnion, Finset.mem_image, Finset.mem_Ico,
        Finset.mem_filter]
      have hsplit : P' = hd free ω a * 3 ^ (b - a) + P' % 3 ^ (b - a) := by
        have := hd_add_div free ω a (b - a)
        rw [show a + (b - a) = b by omega] at this
        rw [← this, mul_comm]; exact (Nat.div_add_mod _ _).symm
      refine ⟨hd free ω a, hd_mem_HS free ω a, q, ⟨hq1, hq2⟩, P' % 3 ^ (b - a),
        ⟨mod_mem_cantorInts (by omega) (hd_mem_cantorInts free ω b), r, hr0, hrk, ?_⟩,
        hsplit.symm⟩
      rw [← hsplit]
      apply Int.modEq_iff_dvd.mpr
      exact ⟨-pp, by rw [hr]; ring⟩
  have hcardS : S.card ≤ 2 ^ freeCount free a * (2 * 3 ^ m * 2 ^ (k + 1)) := by
    calc S.card ≤ ∑ A ∈ HS free a, _ := Finset.card_biUnion_le
      _ ≤ (HS free a).card * (2 * 3 ^ m * 2 ^ (k + 1)) := by
        apply Finset.sum_le_card_nsmul
        intro A _
        calc _ ≤ ∑ q ∈ Finset.Ico (3 ^ m : ℕ) (3 ^ (m + 1)), _ := Finset.card_biUnion_le
          _ ≤ (Finset.Ico (3 ^ m : ℕ) (3 ^ (m + 1))).card * 2 ^ (k + 1) := by
            apply Finset.sum_le_card_nsmul
            intro q hq
            refine Finset.card_image_le.trans ?_
            have hq0 : q ≠ 0 := by
              simp only [Finset.mem_Ico] at hq; have := Nat.one_le_pow m 3 (by norm_num); omega
            obtain ⟨v, q', hndvd, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hq0 3 (by norm_num)
            have hcop : Nat.Coprime q' 3 :=
              ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hndvd).symm
            have := card_residue_le_gen A b (b - a) k v q' (by omega) hkb hcop
            convert this using 4
          _ = 2 * 3 ^ m * 2 ^ (k + 1) := by rw [Nat.card_Ico, pow_succ]; congr 1; omega
      _ ≤ _ := Nat.mul_le_mul_right _ (card_HS free a)
  have hFb : freeCount free b = freeCount free a + (b - a) := by
    rw [freeCount_sub free (by omega : a ≤ b), fc_of_free free hfree]
  have hz : coins.real {ω | ∀ i, m ≤ i → i < b → free i = true → ω i = false} = (1 / 2 : ℝ) ^ (b - m) := by
    rw [coins_zero_window, fc_of_free free (fun i h1 h2 => hfree i (by omega) h2)]
  refine (measureReal_mono hsub (measure_ne_top _ _)).trans ((measureReal_union_le _ _).trans ?_)
  rw [hz]
  gcongr
  refine (coins_hd_mem_le free b S).trans ?_
  rw [hFb, pow_add]
  have hc : (S.card : ℝ) ≤ 2 ^ freeCount free a * (2 * 3 ^ m * 2 ^ (k + 1)) := by exact_mod_cast hcardS
  have e : (2 : ℝ) ^ freeCount free a * (1 / 2) ^ freeCount free a = 1 := by
    rw [← mul_pow]; norm_num
  calc (S.card : ℝ) * ((1 / 2) ^ freeCount free a * (1 / 2) ^ (b - a))
      ≤ 2 ^ freeCount free a * (2 * 3 ^ m * 2 ^ (k + 1)) * ((1 / 2) ^ freeCount free a * (1 / 2) ^ (b - a)) := by
        gcongr
    _ = (2 ^ freeCount free a * (1 / 2) ^ freeCount free a) * (2 * 3 ^ m * 2 ^ (k + 1)) * (1 / 2) ^ (b - a) := by ring
    _ = _ := by rw [e, one_mul, show k + 1 = m + 3 + b - n by omega]

/-! ## Lap 2026-10-06: Farey separation, real and 3-adic

Two hitting points that share enough digits must approximate the *same* fraction, because
fractions of bounded height are separated.

* Real side (`farey_sep`): fractions with denominators below `3^{m+1}` are more than
  `3^{−(2m+2)}` apart, so the hitting set meets each depth-`(2m+3)` cylinder inside one
  depth-`(L−2)` cylinder (`hit_mass_farey`, mass `2^{−F[2m+3, L−2)}`).
* 3-adic side (`padic_sep`): in a run-entering window a hit is `P q ≡ r (mod 3^b)` with
  `3^{L+1−b} |r| ≤ 3q`, and fractions `r/q` whose cross products `r q' − r' q` are below `3^j`
  and agree mod `3^j` are equal.  So the hitting numerators are determined by their low
  `j ≈ log₃(|r| q)` digits and their top `v₃(q)` digits (`hit_mass_padic`, mass
  `Σ_v 2^{−F[v, L−2m−3+2v)}`).

In both cases the mass is `2^{−(μ₀−2)m + o(m)}`, so every window decays for every `μ₀ > 2`.  The
per-`q` count (`card_lowResidue_le`) used the low digits for one `q` at a time and stopped at
`1 + log₂ 3`; the 3-adic separation uses them for all `(q, r)` at once. -/

/-- **Farey separation.**  Distinct fractions with denominators in `(0, 3^{m+1})` are more than
`3^{−(2m+2)}` apart. -/
theorem farey_sep (m q q' pp pp' : ℕ) (hq : 0 < q) (hq' : 0 < q') (hq3 : q < 3 ^ (m + 1))
    (hq3' : q' < 3 ^ (m + 1)) (hne : (pp : ℝ) / q ≠ pp' / q') :
    1 / (3 : ℝ) ^ (2 * m + 2) < |(pp : ℝ) / q - pp' / q'| := by
  have hqr : (0 : ℝ) < q := by exact_mod_cast hq
  have hqr' : (0 : ℝ) < q' := by exact_mod_cast hq'
  have hcross : ((pp : ℤ) * q' - pp' * q) ≠ 0 := by
    intro h; apply hne; rw [div_eq_div_iff hqr.ne' hqr'.ne']
    have : ((pp : ℤ) * q' : ℤ) = pp' * q := by linarith
    exact_mod_cast this
  have h1 : (1 : ℝ) ≤ |(pp : ℝ) * q' - pp' * q| := by
    have := Int.one_le_abs hcross; exact_mod_cast this
  have heq : (pp : ℝ) / q - pp' / q' = ((pp : ℝ) * q' - pp' * q) / (q * q') := by
    field_simp
  have hqq : (q : ℝ) * q' < (3 : ℝ) ^ (2 * m + 2) := by
    have a : (q : ℝ) < 3 ^ (m + 1) := by exact_mod_cast hq3
    have b : (q' : ℝ) < 3 ^ (m + 1) := by exact_mod_cast hq3'
    calc (q : ℝ) * q' < 3 ^ (m + 1) * 3 ^ (m + 1) := mul_lt_mul'' a b hqr.le hqr'.le
      _ = _ := by rw [← pow_add]; ring_nf
  rw [heq, abs_div, abs_of_pos (mul_pos hqr hqr')]
  calc 1 / (3 : ℝ) ^ (2 * m + 2) < 1 / (q * q') := one_div_lt_one_div_of_lt (by positivity) hqq
    _ ≤ _ := div_le_div_of_nonneg_right h1 (by positivity)

/-- **Farey mass of the scale-`m` test.**  Two hitting points with the same free coins below
`2m+3` lie within `3^{−(2m+3)}` of each other, so their fractions are within
`3^{−(2m+3)} + 4·3^{−L} < 3^{−(2m+2)}` and coincide (`farey_sep`); then the points are within
`4·3^{−L} < 3^{−(L−2)}` and share the free coins below `L − 2` (`agree_of_close`). -/
theorem hit_mass_farey (free : ℕ → Bool) (m L : ℕ) (hL : 2 * m + 5 ≤ L) :
    coins.real {ω | hitB free m L (pre ω (L + 1)) = true} ≤
      (1 / 2 : ℝ) ^ fc free (2 * m + 3) (L - 2) := by
  sorry

/-- **3-adic Farey separation.**  With `r₀ = P q₀ − pp·3^c` and `r₀' = P' q₀' − pp'·3^c`
(`q₀, q₀'` prime to 3): if `P ≡ P' (mod 3^j)`, `j ≤ c`, and `|r₀ q₀' − r₀' q₀| < 3^j`, then
`P ≡ P' (mod 3^c)`.  The cross product is `≡ (P − P') q₀ q₀' ≡ 0 (mod 3^j)`, hence `0`, hence
`3^c ∣ (P − P') q₀ q₀'`. -/
theorem padic_sep (c j P P' q₀ q₀' pp pp' : ℕ) (hj : j ≤ c) (hq : Nat.Coprime q₀ 3)
    (hq' : Nat.Coprime q₀' 3) (hPP : P % 3 ^ j = P' % 3 ^ j)
    (hb : |((P : ℤ) * q₀ - pp * 3 ^ c) * q₀' - ((P' : ℤ) * q₀' - pp' * 3 ^ c) * q₀| < 3 ^ j) :
    P % 3 ^ c = P' % 3 ^ c := by
  have hdj : ((3 ^ j : ℕ) : ℤ) ∣ (P' : ℤ) - P := (Nat.modEq_iff_dvd.mp hPP)
  have h3c : ((3 : ℤ) ^ j) ∣ (3 : ℤ) ^ c := pow_dvd_pow 3 hj
  set X : ℤ := ((P : ℤ) * q₀ - pp * 3 ^ c) * q₀' - ((P' : ℤ) * q₀' - pp' * 3 ^ c) * q₀ with hX
  have hXe : X = ((P : ℤ) - P') * q₀ * q₀' - 3 ^ c * (pp * q₀' - pp' * q₀) := by rw [hX]; ring
  have hXd : (3 : ℤ) ^ j ∣ X := by
    rw [hXe]; push_cast at hdj
    refine dvd_sub (Dvd.dvd.mul_right (Dvd.dvd.mul_right ?_ _) _) (Dvd.dvd.mul_right h3c _)
    rw [← dvd_neg, neg_sub]; exact hdj
  have hX0 : X = 0 := by
    obtain ⟨k, hk⟩ := hXd
    have hpos : (0 : ℤ) < 3 ^ j := by positivity
    rw [hk, abs_mul, abs_of_pos hpos] at hb
    have : |k| < 1 := by nlinarith [abs_nonneg k]
    have : k = 0 := by rw [abs_lt] at this; omega
    rw [hk, this, mul_zero]
  have hdiv : (3 : ℤ) ^ c ∣ ((P' : ℤ) - P) * (q₀ * q₀') := by
    refine ⟨-(pp * q₀' - pp' * q₀), ?_⟩
    have := hXe; rw [hX0] at this; linarith
  have hcop : IsCoprime ((3 : ℤ) ^ c) ((q₀ : ℤ) * q₀') := by
    apply IsCoprime.pow_left
    rw [Int.isCoprime_iff_gcd_eq_one]
    have := Nat.Coprime.mul_left hq hq'
    rw [Int.gcd_comm]; exact_mod_cast this
  have := hcop.dvd_of_dvd_mul_right hdiv
  exact Nat.modEq_iff_dvd.mpr (by push_cast; exact this)

theorem mod3_aux (h d M : ℕ) (hd : d < 3) (hM : 0 < M) : (3 * h + d) % (3 * M) = 3 * (h % M) + d := by
  conv_lhs => rw [← Nat.div_add_mod h M]
  rw [show 3 * (M * (h / M) + h % M) + d = (3 * (h % M) + d) + (3 * M) * (h / M) by ring,
    Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt]
  have := Nat.mod_lt h hM; omega

theorem fc_succ_self (free : ℕ → Bool) (n : ℕ) : fc free n (n + 1) = if free n then 1 else 0 := by
  unfold fc; rw [Nat.Ico_succ_singleton, Finset.filter_singleton]; split_ifs <;> simp_all

/-- Low digits of reachable numerators: at most `2^{F[n−j, n)}` residues mod `3^j`. -/
theorem card_image_mod_HS_le (free : ℕ → Bool) (j n : ℕ) (hj : j ≤ n) :
    ((HS free n).image (· % 3 ^ j)).card ≤ 2 ^ fc free (n - j) n := by
  classical
  induction n generalizing j with
  | zero =>
    obtain rfl : j = 0 := by omega
    calc _ ≤ ({0} : Finset ℕ).card := Finset.card_le_card (by
            intro x hx; simp only [Finset.mem_image] at hx; obtain ⟨y, -, rfl⟩ := hx; simp [Nat.mod_one])
      _ ≤ _ := by simp; exact Nat.one_le_two_pow
  | succ n ih =>
    rcases j with _ | j
    · calc _ ≤ ({0} : Finset ℕ).card := Finset.card_le_card (by
            intro x hx; simp only [Finset.mem_image] at hx; obtain ⟨y, -, rfl⟩ := hx; simp [Nat.mod_one])
        _ ≤ _ := by simp; exact Nat.one_le_two_pow
    have ih' := ih j (by omega)
    set I := (HS free n).image (· % 3 ^ j)
    have hfc : fc free (n + 1 - (j + 1)) (n + 1) = fc free (n - j) n + if free n then 1 else 0 := by
      rw [show n + 1 - (j + 1) = n - j by omega,
        fc_add free (show n - j ≤ n by omega) (show n ≤ n + 1 by omega), fc_succ_self]
    have key : ∀ h d, d < 3 → (3 * h + d) % 3 ^ (j + 1) = 3 * (h % 3 ^ j) + d := fun h d hd => by
      rw [pow_succ, mul_comm _ 3]; exact mod3_aux h d _ hd (by positivity)
    rw [hfc]
    simp only [HS]
    split_ifs with hf
    · calc _ ≤ (I.image (3 * ·) ∪ I.image (3 * · + 2)).card := by
            apply Finset.card_le_card
            intro x hx
            simp only [Finset.mem_image, Finset.mem_union, I] at hx ⊢
            rcases hx with ⟨y, (⟨h, hh, rfl⟩ | ⟨h, hh, rfl⟩), rfl⟩
            · left; exact ⟨_, ⟨h, hh, rfl⟩, by simpa using (key h 0 (by norm_num)).symm⟩
            · right; exact ⟨_, ⟨h, hh, rfl⟩, (key h 2 (by norm_num)).symm⟩
        _ ≤ I.card + I.card := (Finset.card_union_le _ _).trans
            (add_le_add Finset.card_image_le Finset.card_image_le)
        _ ≤ _ := by rw [pow_succ]; omega
    · calc _ ≤ (I.image (3 * ·)).card := by
            apply Finset.card_le_card
            intro x hx
            simp only [Finset.mem_image, I] at hx ⊢
            obtain ⟨y, ⟨h, hh, rfl⟩, rfl⟩ := hx
            exact ⟨_, ⟨h, hh, rfl⟩, by simpa using (key h 0 (by norm_num)).symm⟩
        _ ≤ _ := Finset.card_image_le.trans (by simpa using ih')

/-- Group-`v` hit predicate on a depth-`b` numerator. -/
def grp (m L b v P : ℕ) : Prop := ∃ q₀ pp : ℕ, Nat.Coprime q₀ 3 ∧ q₀ < 3 ^ (m + 1 - v) ∧
  (3 : ℤ) ^ (L + 1 - b) * |(P : ℤ) * q₀ - pp * 3 ^ (b - v)| ≤ 3 * q₀

theorem hit_classify (free : ℕ → Bool) (m L b : ℕ) (hmb : m ≤ b) (hbn : b ≤ L + 1)
    (hforced : ∀ i, b ≤ i → i < L + 1 → free i = false) (ω : ℕ → Bool)
    (hω : hitB free m L (pre ω (L + 1)) = true) :
    (∀ i, m ≤ i → i < b → free i = true → ω i = false) ∨
      ∃ v < m + 2 + b - (L + 1), grp m L b v (hd free ω b) := by
  set n := L + 1 with hn
  obtain ⟨q, pp, hq2, hpp, hq1, hc⟩ := (hitB_iff free m L _).1 hω
  rw [tNum_pre] at hc
  have hq0 : 0 < q := lt_of_lt_of_le (by positivity) hq1
  have hT : hd free ω n = 3 ^ (n - b) * hd free ω b :=
    hd_zero_ext free ω b n hbn (fun i h1 h2 => by simp [ptDigit, hforced i h1 h2])
  set P' := hd free ω b with hP'
  rw [hT] at hc
  obtain ⟨hc1, hc2⟩ := hc
  set r : ℤ := (P' : ℤ) * q - pp * 3 ^ b with hr
  have h3nb : (3 : ℤ) ^ n = 3 ^ (n - b) * 3 ^ b := by rw [← pow_add]; congr 1; omega
  have habs : (3 : ℤ) ^ (n - b) * |r| ≤ 3 * q := by
    have e : (3 : ℤ) ^ (n - b) * r = ((3 ^ (n - b) * P' : ℕ) : ℤ) * q - pp * 3 ^ n := by
      rw [h3nb, hr]; push_cast; ring
    rw [← abs_of_pos (by positivity : (0:ℤ) < 3 ^ (n - b)), ← abs_mul, e, abs_le]
    constructor
    · have : ((pp * 3 ^ n : ℕ) : ℤ) ≤ ((3 ^ (n - b) * P' * q + 3 * q : ℕ) : ℤ) := by exact_mod_cast hc2
      push_cast at this ⊢; linarith
    · have : ((3 ^ (n - b) * P' * q : ℕ) : ℤ) ≤ ((pp * 3 ^ n + 3 * q : ℕ) : ℤ) := by exact_mod_cast hc1
      push_cast at this ⊢; linarith
  by_cases hr0 : r = 0
  · left
    have heq : pp * 3 ^ b = P' * q := by
      have : (pp : ℤ) * 3 ^ b = (P' : ℤ) * q := by linarith
      exact_mod_cast this
    have hdvd := pow_dvd_of_eq hq0.ne' hq2 heq
    have hz := digits_zero_of_dvd free ω (b - m) b (by omega) hdvd
    intro i h1 h2 hf
    have := hz i (by omega) h2
    simp only [ptDigit, hf, Bool.true_and] at this
    cases hw : ω i <;> simp_all
  · right
    obtain ⟨v, q₀, hndvd, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hq0.ne' 3 (by norm_num)
    have hcop : Nat.Coprime q₀ 3 :=
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hndvd).symm
    have hq₀ : 0 < q₀ := Nat.pos_of_ne_zero (by rintro rfl; simp at hq0)
    have hvm : v ≤ m := by
      by_contra hc
      have : 3 ^ (m + 1) ≤ 3 ^ v * q₀ :=
        (Nat.pow_le_pow_right (by norm_num) (by omega)).trans (Nat.le_mul_of_pos_right _ hq₀)
      omega
    have hq₀M : q₀ < 3 ^ (m + 1 - v) := by
      have : 3 ^ v * q₀ < 3 ^ v * 3 ^ (m + 1 - v) := by
        rw [← pow_add, show v + (m + 1 - v) = m + 1 by omega]; exact hq2
      exact lt_of_mul_lt_mul_left this (Nat.zero_le _)
    set r₀ : ℤ := (P' : ℤ) * q₀ - pp * 3 ^ (b - v) with hr₀
    have hrr : r = 3 ^ v * r₀ := by
      rw [hr, hr₀, mul_sub, show (3 : ℤ) ^ b = 3 ^ v * 3 ^ (b - v) by rw [← pow_add]; congr 1; omega]
      push_cast; ring
    have hpv : (0 : ℤ) < 3 ^ v := by positivity
    have hb0 : (3 : ℤ) ^ (n - b) * |r₀| ≤ 3 * q₀ := by
      rw [hrr, abs_mul, abs_of_pos hpv] at habs
      push_cast at habs
      have : (3 : ℤ) ^ v * ((3 : ℤ) ^ (n - b) * |r₀|) ≤ 3 ^ v * (3 * q₀) := by linarith
      exact le_of_mul_le_mul_left this hpv
    refine ⟨v, ?_, q₀, pp, hcop, hq₀M, hb0⟩
    have hr₀0 : r₀ ≠ 0 := by rintro h; apply hr0; rw [hrr, h, mul_zero]
    have h1 : (1 : ℤ) ≤ |r₀| := Int.one_le_abs hr₀0
    have h2 : (3 : ℤ) ^ (n - b) < 3 ^ (m + 2 - v) := by
      have : (3 * q₀ : ℤ) < 3 * 3 ^ (m + 1 - v) := by
        have : (q₀ : ℤ) < 3 ^ (m + 1 - v) := by exact_mod_cast hq₀M
        linarith
      rw [show m + 2 - v = (m + 1 - v) + 1 by omega, pow_succ]
      nlinarith [show (0 : ℤ) < 3 ^ (n - b) by positivity]
    have := (pow_lt_pow_iff_right₀ (by norm_num : (1 : ℤ) < 3)).1 h2
    omega

theorem group_sep (c j e P P' q₀ q₀' pp pp' M : ℕ) (hj : j ≤ c) (hq : Nat.Coprime q₀ 3)
    (hq' : Nat.Coprime q₀' 3) (hqM : q₀ < M) (hqM' : q₀' < M) (hej : 3 ^ (e + j) = 9 * M ^ 2)
    (hr : (3 : ℤ) ^ e * |(P : ℤ) * q₀ - pp * 3 ^ c| ≤ 3 * q₀)
    (hr' : (3 : ℤ) ^ e * |(P' : ℤ) * q₀' - pp' * 3 ^ c| ≤ 3 * q₀')
    (hlow : P % 3 ^ j = P' % 3 ^ j) : P % 3 ^ c = P' % 3 ^ c := by
  apply padic_sep c j P P' q₀ q₀' pp pp' hj hq hq' hlow
  set r := (P : ℤ) * q₀ - pp * 3 ^ c
  set r' := (P' : ℤ) * q₀' - pp' * 3 ^ c
  have h0 : (0 : ℤ) ≤ q₀ := by positivity
  have h0' : (0 : ℤ) ≤ q₀' := by positivity
  have hX : (3 : ℤ) ^ e * |r * q₀' - r' * q₀| ≤ 6 * q₀ * q₀' := by
    calc (3 : ℤ) ^ e * |r * q₀' - r' * q₀| ≤ 3 ^ e * (|r| * q₀' + |r'| * q₀) := by
          gcongr
          refine (abs_sub _ _).trans ?_
          rw [abs_mul, abs_mul, abs_of_nonneg h0, abs_of_nonneg h0']
      _ = (3 ^ e * |r|) * q₀' + (3 ^ e * |r'|) * q₀ := by ring
      _ ≤ (3 * q₀) * q₀' + (3 * q₀') * q₀ := by gcongr
      _ = _ := by ring
  have hM : (6 : ℤ) * q₀ * q₀' < 3 ^ e * 3 ^ j := by
    rw [← pow_add]
    have : ((3 ^ (e + j) : ℕ) : ℤ) = ((9 * M ^ 2 : ℕ) : ℤ) := by rw [hej]
    push_cast at this; rw [this]
    have a : (q₀ : ℤ) < M := by exact_mod_cast hqM
    have b : (q₀' : ℤ) < M := by exact_mod_cast hqM'
    nlinarith
  exact lt_of_mul_lt_mul_left (hX.trans_lt hM) (by positivity)

/-- **3-adic Farey mass of a run-entering scale-`m` test.**  Digits `[b, L]` forced, so the
truncated numerator is `3^{L+1−b} P` with `P = hd b`.  An exact hit (`pp/q = P/3^b`) forces zero
digits on `[m, b)`.  Otherwise group by `v = v₃(q)`, `q = 3^v q₀`: two hits in group `v` with the
same top `v` digits and the same low `j_v = 2m+3+b−L−2v` digits have equal numerators
(`padic_sep` with `c = b − v`), so group `v` has mass `2^{−F[v, b−j_v)}`. -/
theorem hit_mass_padic (free : ℕ → Bool) (m L b : ℕ) (hmb : m ≤ b) (hbn : b ≤ L + 1)
    (hL : 2 * m + 3 ≤ L) (hforced : ∀ i, b ≤ i → i < L + 1 → free i = false) :
    coins.real {ω | hitB free m L (pre ω (L + 1)) = true} ≤
      ∑ v ∈ Finset.range (m + 2 + b - (L + 1)), (1 / 2 : ℝ) ^ fc free v (L - 2 * m - 3 + 2 * v) +
        (1 / 2 : ℝ) ^ fc free m b := by
  classical
  set K := m + 2 + b - (L + 1) with hK
  let j : ℕ → ℕ := fun v => 2 * m + 3 + b - L - 2 * v
  let T : ℕ → Finset ℕ := fun v =>
    (HS free b).filter fun P => grp m L b v P ∧ ∃ ω, hd free ω b = P
  have hsub : {ω | hitB free m L (pre ω (L + 1)) = true} ⊆
      (⋃ v ∈ Finset.range K, {ω | hd free ω b ∈ T v}) ∪
        {ω | ∀ i, m ≤ i → i < b → free i = true → ω i = false} := by
    intro ω hω
    rcases hit_classify free m L b hmb hbn hforced ω hω with h | ⟨v, hv, hg⟩
    · exact Or.inr h
    · left
      simp only [Set.mem_iUnion, Set.mem_ofPred_eq, Finset.mem_range]
      exact ⟨v, hv, Finset.mem_filter.2 ⟨hd_mem_HS free ω b, hg, ω, rfl⟩⟩
  have hmass : ∀ v ∈ Finset.range K, coins.real {ω | hd free ω b ∈ T v} ≤
      (1 / 2 : ℝ) ^ fc free v (L - 2 * m - 3 + 2 * v) := by
    intro v hv
    rw [Finset.mem_range] at hv
    have hjb : b - j v = L - 2 * m - 3 + 2 * v := by simp only [j]; omega
    have hvj : v ≤ b - j v := by omega
    have hjb' : j v ≤ b := by simp only [j]; omega
    have hcard : (T v).card ≤ 2 ^ freeCount free v * 2 ^ fc free (b - j v) b := by
      calc (T v).card ≤ (HS free v ×ˢ (HS free b).image (· % 3 ^ j v)).card := by
            refine Finset.card_le_card_of_injOn (fun P => (P / 3 ^ (b - v), P % 3 ^ j v)) ?_ ?_
            · intro P hP
              simp only [T, Finset.coe_filter, Set.mem_ofPred_eq] at hP
              obtain ⟨hPH, -, ω, rfl⟩ := hP
              simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, Finset.mem_image]
              refine ⟨?_, _, hPH, rfl⟩
              have := hd_add_div free ω v (b - v)
              rw [show v + (b - v) = b by omega] at this
              rw [this]; exact hd_mem_HS free ω v
            · intro P hP P' hP' he
              simp only [T, Finset.coe_filter, Set.mem_ofPred_eq] at hP hP'
              simp only [Prod.mk.injEq] at he
              obtain ⟨-, ⟨q₀, pp, hc, hqM, hr⟩, -⟩ := hP
              obtain ⟨-, ⟨q₀', pp', hc', hqM', hr'⟩, -⟩ := hP'
              have hlow := group_sep (b - v) (j v) (L + 1 - b) P P' q₀ q₀' pp pp' (3 ^ (m + 1 - v))
                (by simp only [j]; omega) hc hc' hqM hqM'
                (by rw [← pow_mul, show (9 : ℕ) = 3 ^ 2 by rfl, ← pow_add]; congr 1; simp only [j]; omega)
                hr hr' he.2
              rw [← Nat.div_add_mod P (3 ^ (b - v)), ← Nat.div_add_mod P' (3 ^ (b - v)), he.1, hlow]
        _ ≤ _ := by
            rw [Finset.card_product]
            exact Nat.mul_le_mul (card_HS free v) (card_image_mod_HS_le free (j v) b hjb')
    have hF : freeCount free b = freeCount free v + fc free v (b - j v) + fc free (b - j v) b := by
      rw [freeCount_sub free (show v ≤ b by omega), fc_add free hvj (by omega), add_assoc]
    refine (coins_hd_mem_le free b (T v)).trans ?_
    rw [hF, ← hjb, pow_add, pow_add]
    have hc : ((T v).card : ℝ) ≤ 2 ^ freeCount free v * 2 ^ fc free (b - j v) b := by exact_mod_cast hcard
    have e1 : (2 : ℝ) ^ freeCount free v * (1 / 2) ^ freeCount free v = 1 := by rw [← mul_pow]; norm_num
    have e2 : (2 : ℝ) ^ fc free (b - j v) b * (1 / 2) ^ fc free (b - j v) b = 1 := by rw [← mul_pow]; norm_num
    calc ((T v).card : ℝ) * ((1 / 2) ^ freeCount free v * (1 / 2) ^ fc free v (b - j v) *
          (1 / 2) ^ fc free (b - j v) b)
        ≤ (2 ^ freeCount free v * 2 ^ fc free (b - j v) b) * ((1 / 2) ^ freeCount free v *
          (1 / 2) ^ fc free v (b - j v) * (1 / 2) ^ fc free (b - j v) b) := by gcongr
      _ = (2 ^ freeCount free v * (1 / 2) ^ freeCount free v) *
          (2 ^ fc free (b - j v) b * (1 / 2) ^ fc free (b - j v) b) * (1 / 2) ^ fc free v (b - j v) := by ring
      _ = _ := by rw [e1, e2, one_mul, one_mul]
  refine (measureReal_mono hsub (measure_ne_top _ _)).trans ((measureReal_union_le _ _).trans ?_)
  rw [coins_zero_window]
  gcongr
  exact (measureReal_biUnion_finset_le _ _).trans (Finset.sum_le_sum hmass)

/-- **Scale-test masses for every `μ₀ > 2`.**  As `CantorExactExponent.ev_expTest_mass`, with the
Borel–Cantelli case split by whether the window enters the next run: if not, `hit_mass_farey`
(the free count of `[2m+3, L−2)` is `≥ (μ₀−2)m + √m − 9`); if it does (`a_{k+1} ≤ L − 3`),
`hit_mass_padic` with `b = a_{k+1}` (free counts `≥ L − 2m − 3 + v − E_k`, and
`E_k = a_{k+1}/(k+2) = o(m)`).  The triangle case is unchanged. -/
theorem ev_expTest_mass_all (μ₀ : ℚ) (hμ : 2 < μ₀) :
    ∀ᶠ m : ℕ in atTop, coins.real {ω | expTest μ₀ m (pre ω (expL μ₀ m + 1)) = true} ≤
      1 / ((m : ℝ) + 1) ^ 2 := by
  sorry

/-- **Mid-range scale-test masses** (leaf of `ae_not_liouvilleWith_mid`).  Confidence 65%.
As `CantorExactExponent.ev_expTest_mass`, for `μ₀ > 1 + log₂ 3`.  English proof: in
`expTest_mass_le` replace the run-entering BC case (`hit_mass_bc`, cost `3ᵐ 2^{−(μ₀−2)m}`) by the
exact residue count: the truncated numerator is `P·3^{L+1−b}` (run zeros at the bottom), so a hit
gives `P q ≡ r (mod 3^b)` with `|r| ≤ 3^{m+2−(L+1−b)}`, and `card_residue_le_gen` prices it at
`3ᵐ 2^{m−L+E_k}`, with `E_k = o(m)`; `r = 0` needs `≈ b − m` trailing zero digits of `P`.
The interior and triangle cases are unchanged, the post-run case is `hit_mass_tri`. -/
theorem ev_expTest_mass_mid (μ₀ : ℚ) (hμ : 1 + Real.logb 2 3 < μ₀) :
    ∀ᶠ m : ℕ in atTop, coins.real {ω | expTest μ₀ m (pre ω (expL μ₀ m + 1)) = true} ≤
      1 / ((m : ℝ) + 1) ^ 2 := by
  refine ev_expTest_mass_all μ₀ ?_
  have h1 : (1 : ℝ) < Real.logb 2 3 := by
    rw [Real.lt_logb_iff_rpow_lt (by norm_num) (by norm_num)]; norm_num
  have : (2 : ℝ) < μ₀ := by linarith
  exact_mod_cast this

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
Wiring proved from `ev_expTest_mass_mid` (the one open leaf). -/
theorem ae_not_liouvilleWith_mid (μ₀ : ℚ) (hμ : 1 + Real.logb 2 3 < μ₀) (τ : ℝ)
    (hτ : (μ₀ : ℝ) < τ) :
    ∀ᵐ ω ∂coins, ¬ LiouvilleWith τ (cantorExpReal μ₀ ω) := by
  have h2 : (2 : ℚ) < μ₀ := by
    have : (2 : ℝ) < μ₀ := by
      have := Real.logb_pos (b := 2) (x := 3) (by norm_num) (by norm_num)
      have h1 : (1 : ℝ) < Real.logb 2 3 := by
        rw [Real.lt_logb_iff_rpow_lt (by norm_num) (by norm_num)]; norm_num
      linarith
    exact_mod_cast this
  obtain ⟨J₀, hJ₀⟩ := eventually_atTop.1 (ev_expTest_mass_mid μ₀ hμ)
  have hfin : ∑' m : ℕ, coins {ω | J₀ ≤ m ∧ expTest μ₀ m (pre ω (expL μ₀ m + 1)) = true} ≠ ⊤ := by
    have hs : Summable fun m : ℕ => 1 / ((m : ℝ) + 1) ^ 2 := by
      have := (summable_nat_add_iff 1).2 (Real.summable_one_div_nat_pow.2 (by norm_num : 1 < 2))
      simpa using this
    refine ne_top_of_le_ne_top (ENNReal.ofReal_tsum_of_nonneg (fun _ => by positivity) hs ▸
      ENNReal.ofReal_ne_top) (ENNReal.tsum_le_tsum fun m => ?_)
    by_cases hm : J₀ ≤ m
    · simp only [hm, true_and]
      rw [← ofReal_measureReal]
      exact ENNReal.ofReal_le_ofReal (hJ₀ m hm)
    · simp [hm]
  have h0 := measure_setOfPred_frequently_eq_zero hfin
  have hae : ∀ᵐ ω ∂coins, ¬ ∃ᶠ m in atTop, J₀ ≤ m ∧ expTest μ₀ m (pre ω (expL μ₀ m + 1)) = true :=
    measure_eq_zero_iff_ae_notMem.1 h0
  filter_upwards [hae] with ω hω
  rw [not_frequently] at hω
  obtain ⟨m₁, hm₁⟩ := eventually_atTop.1 hω
  have hex := hasIrrExponent_of_avoid_two μ₀ h2 ω ⟨max m₁ J₀, fun m hm => by
    have := hm₁ m (le_of_max_le_left hm)
    simpa [le_of_max_le_right hm] using this⟩
  exact hex.2 τ hτ


/-- **Stretch crux: the exponent upper bound for every `μ₀ > 2`.**  Confidence 80%.

Wiring proved from `ev_expTest_mass_all` (Borel–Cantelli and `hasIrrExponent_of_avoid_two`), whose
run-entering case is the 3-adic Farey count `hit_mass_padic`. -/
theorem ae_not_liouvilleWith_all (μ₀ : ℚ) (hμ : 2 < μ₀) (τ : ℝ) (hτ : (μ₀ : ℝ) < τ) :
    ∀ᵐ ω ∂coins, ¬ LiouvilleWith τ (cantorExpReal μ₀ ω) := by
  obtain ⟨J₀, hJ₀⟩ := eventually_atTop.1 (ev_expTest_mass_all μ₀ hμ)
  have hfin : ∑' m : ℕ, coins {ω | J₀ ≤ m ∧ expTest μ₀ m (pre ω (expL μ₀ m + 1)) = true} ≠ ⊤ := by
    have hs : Summable fun m : ℕ => 1 / ((m : ℝ) + 1) ^ 2 := by
      have := (summable_nat_add_iff 1).2 (Real.summable_one_div_nat_pow.2 (by norm_num : 1 < 2))
      simpa using this
    refine ne_top_of_le_ne_top (ENNReal.ofReal_tsum_of_nonneg (fun _ => by positivity) hs ▸
      ENNReal.ofReal_ne_top) (ENNReal.tsum_le_tsum fun m => ?_)
    by_cases hm : J₀ ≤ m
    · simp only [hm, true_and]
      rw [← ofReal_measureReal]
      exact ENNReal.ofReal_le_ofReal (hJ₀ m hm)
    · simp [hm]
  have h0 := measure_setOfPred_frequently_eq_zero hfin
  have hae : ∀ᵐ ω ∂coins, ¬ ∃ᶠ m in atTop, J₀ ≤ m ∧ expTest μ₀ m (pre ω (expL μ₀ m + 1)) = true :=
    measure_eq_zero_iff_ae_notMem.1 h0
  filter_upwards [hae] with ω hω
  rw [not_frequently] at hω
  obtain ⟨m₁, hm₁⟩ := eventually_atTop.1 hω
  have hex := hasIrrExponent_of_avoid_two μ₀ hμ ω ⟨max m₁ J₀, fun m hm => by
    have := hm₁ m (le_of_max_le_left hm)
    simpa [le_of_max_le_right hm] using this⟩
  exact hex.2 τ hτ

/-- **Stretch headline.**  For every rational `μ₀ > 2` a computable `x ∈ K` with irrationality
exponent exactly `μ₀`, normal to every base `b ≥ 2` with `3 ∤ b`, not normal to base 3.
Confidence 80%: wiring proved from `ev_expTest_mass_all` and the main file's
`exists_computable_normal_avoid`. -/
theorem exists_computable_mem_cantorSet_irrExponent_normal_all (μ₀ : ℚ) (hμ : 2 < μ₀) :
    ∃ e : ℕ → Bool, Computable e ∧ cantorExpReal μ₀ e ∈ cantorSet ∧
      HasIrrExponent (cantorExpReal μ₀ e) μ₀ ∧
      (∀ b : ℕ, 2 ≤ b → ¬ 3 ∣ b → IsNormal b (cantorExpReal μ₀ e)) ∧
      ¬ IsNormal 3 (cantorExpReal μ₀ e) := by
  have h1 : (1 : ℚ) < μ₀ := by linarith
  obtain ⟨J₀, hJ₀⟩ := eventually_atTop.1 (ev_expTest_mass_all μ₀ hμ)
  have hmass : ∀ j, coins.real {ω | (fun j p => decide (J₀ ≤ j) && expTest μ₀ j p) j
      (pre ω ((fun j => expL μ₀ j + 1) j)) = true} ≤ 1 / ((j : ℝ) + 1) ^ 2 := by
    intro j
    by_cases hj : J₀ ≤ j
    · simpa [hj] using hJ₀ j hj
    · simp only [hj, decide_false, Bool.false_and, Bool.false_eq_true, Set.ofPred_false,
        measureReal_empty]
      positivity
  have hbad : Primrec₂ fun j p => decide (J₀ ≤ j) && expTest μ₀ j p :=
    Primrec.and.comp (Primrec.nat_le.comp (Primrec.const J₀) Primrec.fst).decide
      (primrec_expTest μ₀)
  obtain ⟨e, hce, hn, j₁, hj⟩ := exists_computable_normal_avoid μ₀ h1 _ hbad
    (fun j => expL μ₀ j + 1) (Primrec.succ.comp (primrec_expL μ₀)) hmass
  refine ⟨e, hce, mem_cantorSet μ₀ e, hasIrrExponent_of_avoid_two μ₀ hμ e ⟨max j₁ J₀, fun m hm => ?_⟩,
    hn, not_isNormal_three_cantorExpReal μ₀ h1 e⟩
  have := hj m (le_of_max_le_left hm)
  simpa [le_of_max_le_right hm] using this

end NormalNumbers.CantorExactExponentStretch
