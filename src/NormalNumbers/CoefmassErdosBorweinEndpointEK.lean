/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib
import Architect
import NormalNumbers.RealDefs
import NormalNumbers.CoefmassErdosBorweinEndpoint

/-!
# The Erdős–Borwein endpoint `a = ln 2`, Step 2 and assembly (FDEK-conditional)

Statements copied verbatim from the KB packet `NNErdosBorweinRandom.lean`.  The growing-moment
criterion `ebRandom_ae_normal_of_divisorVariance_diverges` is proved in
`CoefmassErdosBorweinEndpoint.lean`.  This file owes Step 2, divergence of the variance divisor
mass at the endpoint given finite-dimensional Erdős–Kac (a named literature hypothesis, not an
axiom), and the assembly.  Paper: `nn-erdos-borwein-random-2026-10-12.md`, "Step 2".
-/

namespace NormalNumbers.ErdosBorweinEndpointEK

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology
open NormalNumbers.ErdosBorweinPositive NormalNumbers.ErdosBorweinEndpoint

/-- The power family `δ_m = min(1/2, (log m)^{-a})` (and `1/2` for `m < 3`). -/
noncomputable def powerDelta (a : ℝ) (m : ℕ) : ℝ :=
  if m < 3 then 1 / 2 else min (1 / 2) (Real.rpow (Real.log m) (-a))

/-- **Candidate positive answer on the unresolved range** (renamed from `EBPowerThresholdOpen` on
2026-10-12, before any use; the statement is unchanged).  For the power family:
* `a > ln 2`: a.s. non-normal (`ebRandom_ae_not_normal`).
* `0 ≤ a < ln 2`: a.s. normal (`ebRandom_ae_normal_below_ln2`, with `c = (log 2)^a/4`).
So the only unresolved case of this Prop is the endpoint `a = ln 2`, where it is the PROPOSED positive
answer.  It is a candidate, not a claim, and its literature status is unverified. -/
def EBPowerCandidateNormal : Prop :=
  ∀ a : ℝ, 0 < a → a ≤ Real.log 2 →
    ∀ {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
      (X : ℕ → Ω → Bool), BernoulliLawNat μ (powerDelta a) X →
      ∀ᵐ w ∂μ, ∀ b : ℕ, 2 ≤ b → NormalNumbers.IsNormal b (ebLambert b X w)

/-- `ω` restricted to primes `p ≤ y`. -/
noncomputable def omegaUpTo (y : ℝ) (n : ℕ) : ℕ :=
  (n.primeFactors.filter (fun p : ℕ => (p : ℝ) ≤ y)).card

/-- Finite-dimensional law of Brownian motion at times `t 1 < … < t R` (with `t 0 = 0`), as the
image of independent Gaussian increments under partial summation. -/
noncomputable def brownianFDD (R : ℕ) (t : Fin (R + 1) → ℝ) : Measure (Fin R → ℝ) :=
  (Measure.pi (fun j : Fin R =>
      gaussianReal 0 (Real.toNNReal (t j.succ - t j.castSucc)))).map
    (fun y j => ∑ i ∈ Finset.univ.filter (fun i : Fin R => i ≤ j), y i)

open Classical in
/-- Literature input: finite-dimensional Erdős–Kac, in portmanteau (closed-set upper bound) form.
For `n` uniform in `[1, N]`, `((ω(n; ≤ exp((log N)^{t_j})) - t_j log log N)/√(log log N))_j`
converges in law to `(B_{t_j})_j`.  Standard via the Kubilius model or the moment method plus
Cramér–Wold.  It is a special case of Billingsley's functional limit theorem (Ann. Probab. 2 (1974)
749–791; theorem number unverified).  A named hypothesis, not an axiom. -/
def ErdosKacFiniteDim : Prop :=
  ∀ R : ℕ, ∀ t : Fin (R + 1) → ℝ, StrictMono t → t 0 = 0 → t (Fin.last R) ≤ 1 →
    ∀ F : Set (Fin R → ℝ), IsClosed F → ∀ ε : ℝ, 0 < ε →
      ∀ᶠ N : ℕ in atTop,
        (((Finset.Icc 1 N).filter (fun n =>
          (fun j : Fin R =>
            ((omegaUpTo (Real.exp (Real.log N ^ t j.succ)) n : ℝ) -
                t j.succ * Real.log (Real.log N)) /
              Real.sqrt (Real.log (Real.log N))) ∈ F)).card : ℝ) / N ≤
          (brownianFDD R t F).toReal + ε

/-! ### Deterministic divisor-chain supply -/

/-- The prime factors of `n` no larger than `p`. -/
def primeFactorsUpTo (p n : ℕ) : Finset ℕ :=
  n.primeFactors.filter (fun q ↦ q ≤ p)

/-- Squarefree divisors in the chain ending at `p`: multiply `p` by an arbitrary subset of the
other prime factors of `n` no larger than `p`. -/
def primeChainDivisors (p n : ℕ) : Finset ℕ :=
  ((primeFactorsUpTo p n).erase p).powerset.image (fun s ↦ p * ∏ q ∈ s, q)

/-- Products of subsets of a finite set of primes are injective. -/
theorem primeProducts_injOn {A : Finset ℕ} (hA : ∀ q ∈ A, q.Prime) :
    Set.InjOn (fun s : Finset ℕ ↦ ∏ q ∈ s, q) A.powerset := by
  intro s hs t ht hst
  have hsA : s ⊆ A := Finset.mem_powerset.mp hs
  have htA : t ⊆ A := Finset.mem_powerset.mp ht
  have hsprime : ∀ q ∈ s, q.Prime := fun q hq ↦ hA q (hsA hq)
  have htprime : ∀ q ∈ t, q.Prime := fun q hq ↦ hA q (htA hq)
  calc
    s = (∏ q ∈ s, q).primeFactors := (Nat.primeFactors_prod hsprime).symm
    _ = (∏ q ∈ t, q).primeFactors := congrArg Nat.primeFactors hst
    _ = t := Nat.primeFactors_prod htprime

/-- The chain ending at `p` contains exactly `2^(t-1)` distinct divisors, where `t` is the
number of prime factors of `n` no larger than `p`. -/
theorem card_primeChainDivisors {p n : ℕ} (hp : p.Prime) (hpn : p ∣ n) (hn : n ≠ 0) :
    (primeChainDivisors p n).card = 2 ^ ((primeFactorsUpTo p n).card - 1) := by
  have hpA : p ∈ primeFactorsUpTo p n := by
    simp only [primeFactorsUpTo, Finset.mem_filter, Nat.mem_primeFactors]
    exact ⟨⟨hp, hpn, hn⟩, le_rfl⟩
  have hAprime : ∀ q ∈ (primeFactorsUpTo p n).erase p, q.Prime := by
    intro q hq
    have hqA := (Finset.mem_erase.mp hq).2
    exact (Nat.mem_primeFactors.mp (Finset.mem_filter.mp hqA).1).1
  rw [primeChainDivisors, Finset.card_image_of_injOn]
  · rw [Finset.card_powerset, Finset.card_erase_of_mem hpA]
  · intro s hs t ht hst
    have hp0 : 0 < p := hp.pos
    apply primeProducts_injOn hAprime hs ht
    exact Nat.eq_of_mul_eq_mul_left hp0 (by simpa only using hst)

/-- Every member of the prime chain is a divisor of `n`, is at least its terminal prime `p`, and
is at most `p^t`, where `t` counts the prime factors of `n` no larger than `p`. -/
theorem mem_primeChainDivisors_bounds {p n d : ℕ} (hp : p.Prime) (hpn : p ∣ n) (hn : n ≠ 0)
    (hd : d ∈ primeChainDivisors p n) :
    p ≤ d ∧ d ∣ n ∧ d ≤ p ^ (primeFactorsUpTo p n).card := by
  classical
  rcases Finset.mem_image.mp hd with ⟨s, hs, rfl⟩
  have hsA : s ⊆ (primeFactorsUpTo p n).erase p := Finset.mem_powerset.mp hs
  have hsp : p ∉ s := fun hps ↦ (Finset.mem_erase.mp (hsA hps)).1 rfl
  have hsprime : ∀ q ∈ s, q.Prime := by
    intro q hq
    have hqA := (Finset.mem_erase.mp (hsA hq)).2
    exact (Nat.mem_primeFactors.mp (Finset.mem_filter.mp hqA).1).1
  have hspos : 0 < ∏ q ∈ s, q := Finset.prod_pos fun q hq ↦ (hsprime q hq).pos
  have hlower : p ≤ p * ∏ q ∈ s, q := Nat.le_mul_of_pos_right p hspos
  have hdvd : p * ∏ q ∈ s, q ∣ n := by
    have hprod : ∏ q ∈ insert p s, q ∣ n := by
      apply Finset.prod_primes_dvd n
      · intro q hq
        rcases Finset.mem_insert.mp hq with rfl | hqs
        · exact hp.prime
        · exact (hsprime q hqs).prime
      · intro q hq
        rcases Finset.mem_insert.mp hq with rfl | hqs
        · exact hpn
        · have hqA := (Finset.mem_erase.mp (hsA hqs)).2
          exact (Nat.mem_primeFactors.mp (Finset.mem_filter.mp hqA).1).2.1
    simpa only [Finset.prod_insert hsp] using hprod
  have hqle : ∀ q ∈ s, q ≤ p := by
    intro q hq
    exact (Finset.mem_filter.mp (Finset.mem_erase.mp (hsA hq)).2).2
  have hprodle : ∏ q ∈ s, q ≤ p ^ s.card := Finset.prod_le_pow_card s id p hqle
  have hscard : s.card + 1 ≤ (primeFactorsUpTo p n).card := by
    have hins : insert p s ⊆ primeFactorsUpTo p n := by
      intro q hq
      rcases Finset.mem_insert.mp hq with rfl | hqs
      · simp only [primeFactorsUpTo, Finset.mem_filter, Nat.mem_primeFactors]
        exact ⟨⟨hp, hpn, hn⟩, le_rfl⟩
      · exact (Finset.mem_erase.mp (hsA hqs)).2
    have := Finset.card_le_card hins
    simpa only [Finset.card_insert_of_notMem hsp] using this
  refine ⟨hlower, hdvd, ?_⟩
  calc
    p * ∏ q ∈ s, q ≤ p * p ^ s.card := Nat.mul_le_mul_left p hprodle
    _ = p ^ (s.card + 1) := by rw [pow_succ, mul_comm]
    _ ≤ p ^ (primeFactorsUpTo p n).card := Nat.pow_le_pow_right hp.one_le hscard

/-- `primeFactorsUpTo` is the finitary set counted by `omegaUpTo` at a prime cutoff. -/
theorem card_primeFactorsUpTo_eq_omegaUpTo (p n : ℕ) :
    (primeFactorsUpTo p n).card = omegaUpTo (p : ℝ) n := by
  unfold primeFactorsUpTo omegaUpTo
  congr 2 with q
  exact_mod_cast (show q ≤ p ↔ q ≤ p from Iff.rfl)

/-- Quantitative chain bound before simplifying `log (p^t)`: every chain divisor contributes at
least the endpoint weight evaluated at the common upper bound `p^t`. -/
theorem divisorVarianceMass_ge_primeChain (v : ℕ → ℝ) (c : ℝ) (hc : 0 ≤ c)
    (hv0 : ∀ m, 0 ≤ v m)
    (hv : ∀ m : ℕ, 2 ≤ m → c * Real.rpow (Real.log m) (-Real.log 2) ≤ v m)
    {P p n : ℕ} (hp : p.Prime) (hpn : p ∣ n) (hn : n ≠ 0) (hPp : P < p) :
    ((primeChainDivisors p n).card : ℝ) *
        (c * Real.rpow (Real.log (p ^ (primeFactorsUpTo p n).card)) (-Real.log 2)) ≤
      divisorVarianceMass v P n := by
  classical
  let A := primeChainDivisors p n
  let w := c * Real.rpow (Real.log (p ^ (primeFactorsUpTo p n).card)) (-Real.log 2)
  have hterm : ∀ d ∈ A, w ≤ v d := by
    intro d hd
    have hb := mem_primeChainDivisors_bounds hp hpn hn (by simpa only [A] using hd)
    have hd2 : 2 ≤ d := hp.two_le.trans hb.1
    have hdpos : (0 : ℝ) < d := by exact_mod_cast (lt_of_lt_of_le hp.pos hb.1)
    have hlogd : 0 < Real.log d := Real.log_pos (by exact_mod_cast (lt_of_lt_of_le hp.one_lt hb.1))
    have hlogle : Real.log d ≤ Real.log (p ^ (primeFactorsUpTo p n).card) :=
      Real.log_le_log hdpos (by exact_mod_cast hb.2.2)
    have hrpow :
        Real.rpow (Real.log (p ^ (primeFactorsUpTo p n).card)) (-Real.log 2) ≤
          Real.rpow (Real.log d) (-Real.log 2) :=
      Real.rpow_le_rpow_of_nonpos hlogd hlogle (by
        have := Real.log_pos (by norm_num : (1 : ℝ) < 2)
        linarith)
    exact (mul_le_mul_of_nonneg_left hrpow hc).trans (hv d hd2)
  have hsub : A ⊆ n.divisors.filter (fun m ↦ P < m) := by
    intro d hd
    have hb := mem_primeChainDivisors_bounds hp hpn hn (by simpa only [A] using hd)
    rw [Finset.mem_filter, Nat.mem_divisors]
    exact ⟨⟨hb.2.1, hn⟩, hPp.trans_le hb.1⟩
  calc
    ((primeChainDivisors p n).card : ℝ) *
          (c * Real.rpow (Real.log (p ^ (primeFactorsUpTo p n).card)) (-Real.log 2)) =
        ∑ d ∈ A, w := by simp only [A, w, Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ d ∈ A, v d := Finset.sum_le_sum fun d hd ↦ hterm d hd
    _ ≤ ∑ d ∈ n.divisors.filter (fun m ↦ P < m), v d :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun d _ _ ↦ hv0 d)
    _ = divisorVarianceMass v P n := by rfl

/-- The chain bound in the walk argument's exact form.  If `t = ω(n; ≤ p)`, the
`2^(t-1)` chain divisors all have endpoint weight at least `(t log p)^(-log 2)`. -/
theorem divisorVarianceMass_ge_primeChain_endpoint (v : ℕ → ℝ) (c : ℝ) (hc : 0 ≤ c)
    (hv0 : ∀ m, 0 ≤ v m)
    (hv : ∀ m : ℕ, 2 ≤ m → c * Real.rpow (Real.log m) (-Real.log 2) ≤ v m)
    {P p n : ℕ} (hp : p.Prime) (hpn : p ∣ n) (hn : n ≠ 0) (hPp : P < p) :
    ((2 ^ (omegaUpTo (p : ℝ) n - 1) : ℕ) : ℝ) *
        (c * Real.rpow ((omegaUpTo (p : ℝ) n : ℝ) * Real.log p) (-Real.log 2)) ≤
      divisorVarianceMass v P n := by
  have h := divisorVarianceMass_ge_primeChain v c hc hv0 hv hp hpn hn hPp
  rw [card_primeChainDivisors hp hpn hn, card_primeFactorsUpTo_eq_omegaUpTo] at h
  simpa only [Nat.cast_pow, Nat.cast_ofNat, Real.log_pow, Nat.cast_mul] using h

/-- Taking logarithms in the endpoint chain inequality.  This is the scalar core of the walk
cap: exponential growth in the number of prime factors beats the endpoint's logarithmic loss. -/
theorem walk_cap_analytic {k : ℕ} {c T x : ℝ} (hk : 1 ≤ k) (hc : 0 < c) (hx : 0 < x)
    (hchain : ((2 ^ (k - 1) : ℕ) : ℝ) *
      (c * Real.rpow ((k : ℝ) * x) (-Real.log 2)) ≤ T) :
    (k : ℝ) - Real.log x ≤
      1 + Real.log (k : ℝ) + Real.log (T / c) / Real.log 2 := by
  have hk0 : 0 < k := by omega
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk0
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hy : 0 < (k : ℝ) * x := mul_pos hkR hx
  have hrpow : 0 < Real.rpow ((k : ℝ) * x) (-Real.log 2) :=
    Real.rpow_pos_of_pos hy _
  have hpow : (0 : ℝ) < ((2 ^ (k - 1) : ℕ) : ℝ) := by positivity
  have hleft : 0 < ((2 ^ (k - 1) : ℕ) : ℝ) *
      (c * Real.rpow ((k : ℝ) * x) (-Real.log 2)) :=
    mul_pos hpow (mul_pos hc hrpow)
  have hT : 0 < T := hleft.trans_le hchain
  have hlogchain := Real.log_le_log hleft hchain
  rw [Real.log_mul hpow.ne' (mul_pos hc hrpow).ne', Real.log_mul hc.ne' hrpow.ne',
    Nat.cast_pow, Real.log_pow] at hlogchain
  have hrpow_eq : Real.rpow ((k : ℝ) * x) (-Real.log 2) =
      ((k : ℝ) * x) ^ (-Real.log 2) := rfl
  rw [hrpow_eq, Real.log_rpow hy, Real.log_mul hkR.ne' hx.ne', Nat.cast_pred hk0] at hlogchain
  norm_num at hlogchain
  rw [Real.log_div hT.ne' hc.ne']
  have hdiv : (k : ℝ) - Real.log x - (1 + Real.log (k : ℝ)) ≤
      (Real.log T - Real.log c) / Real.log 2 := by
    apply (le_div_iff₀ hlog2).2
    nlinarith [hlogchain]
  linarith

/-- Pointwise walk cap at a prime jump.  On a bounded-divisor-mass event, the excess of the
restricted prime-factor count over `log log p` is at most logarithmic in that count. -/
theorem omegaUpTo_sub_log_log_le_of_divisorVarianceMass_le
    (v : ℕ → ℝ) (c : ℝ) (hc : 0 < c)
    (hv0 : ∀ m, 0 ≤ v m)
    (hv : ∀ m : ℕ, 2 ≤ m → c * Real.rpow (Real.log m) (-Real.log 2) ≤ v m)
    {P p n : ℕ} {T : ℝ} (hp : p.Prime) (hpn : p ∣ n) (hn : n ≠ 0) (hPp : P < p)
    (hmass : divisorVarianceMass v P n ≤ T) :
    (omegaUpTo (p : ℝ) n : ℝ) - Real.log (Real.log p) ≤
      1 + Real.log (omegaUpTo (p : ℝ) n : ℝ) + Real.log (T / c) / Real.log 2 := by
  have hpA : p ∈ primeFactorsUpTo p n := by
    simp only [primeFactorsUpTo, Finset.mem_filter, Nat.mem_primeFactors]
    exact ⟨⟨hp, hpn, hn⟩, le_rfl⟩
  have homega : 1 ≤ omegaUpTo (p : ℝ) n := by
    rw [← card_primeFactorsUpTo_eq_omegaUpTo]
    exact Finset.one_le_card.mpr ⟨p, hpA⟩
  have hlogp : 0 < Real.log p := Real.log_pos (by exact_mod_cast hp.one_lt)
  apply walk_cap_analytic homega hc hlogp
  exact (divisorVarianceMass_ge_primeChain_endpoint v c hc.le hv0 hv hp hpn hn hPp).trans hmass

/-- The walk cap in the form used on the finite-dimensional Erdős--Kac good set: an a priori
bound `ω(n; ≤ p) ≤ 2L` makes the right side uniform in the prime jump. -/
theorem omegaUpTo_sub_log_log_le_of_divisorVarianceMass_le_of_le
    (v : ℕ → ℝ) (c : ℝ) (hc : 0 < c)
    (hv0 : ∀ m, 0 ≤ v m)
    (hv : ∀ m : ℕ, 2 ≤ m → c * Real.rpow (Real.log m) (-Real.log 2) ≤ v m)
    {P p n : ℕ} {T L : ℝ} (hp : p.Prime) (hpn : p ∣ n) (hn : n ≠ 0) (hPp : P < p)
    (hmass : divisorVarianceMass v P n ≤ T) (hL : 0 < L)
    (homega : (omegaUpTo (p : ℝ) n : ℝ) ≤ 2 * L) :
    (omegaUpTo (p : ℝ) n : ℝ) - Real.log (Real.log p) ≤
      1 + Real.log (2 * L) + Real.log (T / c) / Real.log 2 := by
  have hcap := omegaUpTo_sub_log_log_le_of_divisorVarianceMass_le
    v c hc hv0 hv hp hpn hn hPp hmass
  have hpA : p ∈ primeFactorsUpTo p n := by
    simp only [primeFactorsUpTo, Finset.mem_filter, Nat.mem_primeFactors]
    exact ⟨⟨hp, hpn, hn⟩, le_rfl⟩
  have homega_pos : (0 : ℝ) < omegaUpTo (p : ℝ) n := by
    exact_mod_cast (show 0 < omegaUpTo (p : ℝ) n by
      rw [← card_primeFactorsUpTo_eq_omegaUpTo]
      exact Finset.card_pos.mpr ⟨p, hpA⟩)
  have hlogle : Real.log (omegaUpTo (p : ℝ) n : ℝ) ≤ Real.log (2 * L) :=
    Real.log_le_log homega_pos homega
  linarith

/-- **The divisor variance mass diverges at the endpoint.**  Chain bound: for a prime `p ∣ n+a₀`
with `P₀ < p`, the `2^{t-1}` divisors `p·d'` (with `t = ω(n+a₀; ≤ p)`) give
`W ≥ (c/2) exp(ln 2 (t - log log p) - ln 2 · ln t)`.  So `W ≤ T` caps the walk
`ω(n+a₀; ≤ e^{e^u}) - u` by `O(log log log N) = o(√(log log N))` at every jump.  FDEK on refining
grids and `P(sup_{(0,1-η]} B ≤ 0) = 0` finish. -/
theorem divisorVariance_diverges_at_ln2 (hEK : ErdosKacFiniteDim)
    (v : ℕ → ℝ) (c : ℝ) (hc : 0 < c) (hv0 : ∀ m, 0 ≤ v m)
    (hv : ∀ m : ℕ, 2 ≤ m → c * Real.rpow (Real.log m) (-Real.log 2) ≤ v m)
    (a₀ : ℕ) (T : ℝ) :
    Tendsto (fun N : ℕ =>
      (((Finset.Icc 1 N).filter (fun n =>
        divisorVarianceMass v (collisionCutoff N) (n + a₀) ≤ T)).card : ℝ) / N)
      atTop (𝓝 0) := by
  sorry

/-- **Normal at and below `ln 2`.**  `δ_m(1-δ_m) ≥ c (log m)^{-ln 2}` gives a.s., for each `b`, base-`b` normality of `E_b` (one number per base, not absolute normality).
Below `ln 2` is a literal corollary (for `m ≥ 3`, `(log m)^{-a} ≥ (log m)^{-ln 2}`), so this
supersedes the Hardy–Ramanujan route of `ebRandom_ae_normal_below_ln2`, given FDEK. -/
@[blueprint (title := "Random Erdős–Borwein subseries are normal at exponent ln 2")]
theorem ebRandom_ae_normal_le_ln2_of_EK (hEK : ErdosKacFiniteDim)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (delta : ℕ → ℝ) (X : ℕ → Ω → Bool) (hX : BernoulliLawNat μ delta X)
    (c : ℝ) (hc : 0 < c)
    (hvar : ∀ m : ℕ, 2 ≤ m →
      c * Real.rpow (Real.log m) (-Real.log 2) ≤ delta m * (1 - delta m)) :
    ∀ᵐ w ∂μ, ∀ b : ℕ, 2 ≤ b → NormalNumbers.IsNormal b (ebLambert b X w) := by
  apply ebRandom_ae_normal_of_divisorVariance_diverges μ delta X hX
  intro a₀ T
  exact divisorVariance_diverges_at_ln2 hEK (fun m ↦ delta m * (1 - delta m)) c hc
    (fun m ↦ mul_nonneg (hX.1 m).1 (sub_nonneg.mpr (hX.1 m).2)) hvar a₀ T

/-- The power-family Bernoulli variance has the endpoint lower bound uniformly in `m ≥ 2`.
The constant also absorbs the exceptional value `m = 2`, where `powerDelta` is defined to be
`1/2`. -/
theorem exists_powerDelta_variance_lower {a : ℝ} (ha0 : 0 < a) (ha : a ≤ Real.log 2) :
    ∃ c : ℝ, 0 < c ∧ ∀ m : ℕ, 2 ≤ m →
      c * Real.rpow (Real.log m) (-Real.log 2) ≤
        powerDelta a m * (1 - powerDelta a m) := by
  let q₂ := Real.rpow (Real.log 2) (-Real.log 2)
  let c : ℝ := min (1 / 4) ((1 / 4) / q₂)
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hq₂ : 0 < q₂ := Real.rpow_pos_of_pos hlog2 _
  have hc : 0 < c := lt_min (by norm_num) (div_pos (by norm_num) hq₂)
  refine ⟨c, hc, ?_⟩
  intro m hm
  by_cases hm3 : m < 3
  · have hm2 : m = 2 := by omega
    subst m
    have hcq : c * q₂ ≤ 1 / 4 :=
      (le_div_iff₀ hq₂).mp (min_le_right (1 / 4 : ℝ) ((1 / 4) / q₂))
    rw [powerDelta, if_pos (by omega)]
    convert hcq using 1 <;> norm_num [q₂]
  · have hm3' : 3 ≤ m := by omega
    have hlog1 : (1 : ℝ) ≤ Real.log m := by
      calc
        (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
        _ ≤ Real.log 3 := Real.log_le_log (Real.exp_pos 1) Real.exp_one_lt_three.le
        _ ≤ Real.log m := Real.log_le_log (by norm_num) (by exact_mod_cast hm3')
    let q := Real.rpow (Real.log m) (-a)
    let qₑ := Real.rpow (Real.log m) (-Real.log 2)
    have hq0 : 0 ≤ q := Real.rpow_nonneg (by linarith) _
    have hq1 : q ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hlog1 (by linarith)
    have hqₑ0 : 0 ≤ qₑ := Real.rpow_nonneg (by linarith) _
    have hqₑq : qₑ ≤ q := by
      exact Real.rpow_le_rpow_of_exponent_le hlog1 (by linarith)
    have hhalf : qₑ / 2 ≤ min (1 / 2) q := by
      rw [le_min_iff]
      constructor <;> linarith
    have hdelta0 : 0 ≤ min (1 / 2) q := by positivity
    have hdelta1 : min (1 / 2) q ≤ 1 / 2 := min_le_left _ _
    have hprod : (1 / 4 : ℝ) * qₑ ≤
        min (1 / 2) q * (1 - min (1 / 2) q) := by
      calc
        (1 / 4 : ℝ) * qₑ = (qₑ / 2) * (1 / 2) := by ring
        _ ≤ min (1 / 2) q * (1 - min (1 / 2) q) :=
          mul_le_mul hhalf (by linarith) (by norm_num) hdelta0
    have hcle : c ≤ (1 / 4 : ℝ) := min_le_left _ _
    have hcprod : c * qₑ ≤ (1 / 4 : ℝ) * qₑ :=
      mul_le_mul_of_nonneg_right hcle hqₑ0
    simpa only [powerDelta, if_neg hm3, q, qₑ] using hcprod.trans hprod

/-- The candidate positive answer holds, given FDEK.  For `0 < a ≤ ln 2` and `m ≥ 3`,
`powerDelta a m (1 - powerDelta a m) ≥ (1/4)(log m)^{-ln 2}`.  At `m = 2` the variance is `1/4`, so
`c = 1/8` works throughout. -/
theorem ebPowerCandidateNormal_of_EK (hEK : ErdosKacFiniteDim) : EBPowerCandidateNormal := by
  intro a ha0 ha Ω _ μ _ X hX
  obtain ⟨c, hc, hvar⟩ := exists_powerDelta_variance_lower ha0 ha
  exact ebRandom_ae_normal_le_ln2_of_EK hEK μ (powerDelta a) X hX c hc hvar



end NormalNumbers.ErdosBorweinEndpointEK
