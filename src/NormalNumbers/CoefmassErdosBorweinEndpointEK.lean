/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib
import Architect
import NormalNumbers.RealDefs
import NormalNumbers.CoefmassErdosBorweinEndpoint
import NormalNumbers.CoefmassErdosBorweinEndpointEKAux

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
open NormalNumbers.ErdosBorweinEndpointEKAux

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

/-! ### From prime jumps to finite cutoffs -/

/-- If `p` is the largest prime factor of `n` below a real cutoff `y`, then cutting the
prime-factor count at `y` is the same as cutting it at `p`. -/
theorem omegaUpTo_eq_of_greatest_primeFactor {p n : ℕ} {y : ℝ}
    (hpy : (p : ℝ) ≤ y)
    (hmax : ∀ q ∈ n.primeFactors, (q : ℝ) ≤ y → q ≤ p) :
    omegaUpTo y n = omegaUpTo (p : ℝ) n := by
  unfold omegaUpTo
  apply congrArg Finset.card
  ext q
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨hq, hqy⟩
    exact ⟨hq, by exact_mod_cast hmax q hq hqy⟩
  · rintro ⟨hq, hqp⟩
    exact ⟨hq, hqp.trans hpy⟩

/-- Finite-cutoff bridge.  Given an early cutoff `x` with `P ≤ x ≤ y`, either there is a
largest prime jump above `P` at which the count at `y` is attained, or no such jump occurred and
the count at `y` already equals the count at `x`. -/
theorem omegaUpTo_primeJump_or_eq_early {P n : ℕ} {x y : ℝ}
    (hPx : (P : ℝ) ≤ x) (hxy : x ≤ y) :
    (∃ p : ℕ, p.Prime ∧ p ∣ n ∧ P < p ∧ (p : ℝ) ≤ y ∧
      omegaUpTo y n = omegaUpTo (p : ℝ) n) ∨
      omegaUpTo y n = omegaUpTo x n := by
  classical
  let B := n.primeFactors.filter (fun p ↦ P < p ∧ (p : ℝ) ≤ y)
  by_cases hB : B.Nonempty
  · left
    obtain ⟨p, hpB, hpmax⟩ := Finset.exists_max_image B id hB
    have hpdata := Finset.mem_filter.mp hpB
    rcases Nat.mem_primeFactors.mp hpdata.1 with ⟨hp, hpn, _⟩
    refine ⟨p, hp, hpn, hpdata.2.1, hpdata.2.2, ?_⟩
    apply omegaUpTo_eq_of_greatest_primeFactor hpdata.2.2
    intro q hqn hqy
    by_cases hPq : P < q
    · exact hpmax q (Finset.mem_filter.mpr ⟨hqn, hPq, hqy⟩)
    · exact (Nat.le_of_not_gt hPq).trans hpdata.2.1.le
  · right
    unfold omegaUpTo
    apply congrArg Finset.card
    ext q
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hqn, hqy⟩
      refine ⟨hqn, ?_⟩
      by_contra hqx
      have hxq : x < (q : ℝ) := lt_of_not_ge hqx
      have hPq : P < q := by exact_mod_cast hPx.trans_lt hxq
      exact hB ⟨q, Finset.mem_filter.mpr ⟨hqn, hPq, hqy⟩⟩
    · rintro ⟨hqn, hqx⟩
      exact ⟨hqn, hqx.trans hxy⟩

/-- On a bounded divisor-mass event, the finite-cutoff count either has not moved since an early
cutoff, or obeys the uniform walk cap inherited from its last prime jump. -/
theorem omegaUpTo_cutoff_eq_early_or_sub_log_log_le
    (v : ℕ → ℝ) (c : ℝ) (hc : 0 < c)
    (hv0 : ∀ m, 0 ≤ v m)
    (hv : ∀ m : ℕ, 2 ≤ m → c * Real.rpow (Real.log m) (-Real.log 2) ≤ v m)
    {P n : ℕ} {x y T L : ℝ} (hn : n ≠ 0) (hPx : (P : ℝ) ≤ x) (hxy : x ≤ y)
    (hmass : divisorVarianceMass v P n ≤ T) (hL : 0 < L)
    (homega : (omegaUpTo y n : ℝ) ≤ 2 * L) :
    omegaUpTo y n = omegaUpTo x n ∨
      (omegaUpTo y n : ℝ) - Real.log (Real.log y) ≤
        1 + Real.log (2 * L) + Real.log (T / c) / Real.log 2 := by
  rcases omegaUpTo_primeJump_or_eq_early hPx hxy with hjump | hearly
  · right
    obtain ⟨p, hp, hpn, hPp, hpy, hpcount⟩ := hjump
    have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
    have hlogp : 0 < Real.log (p : ℝ) := Real.log_pos (by exact_mod_cast hp.one_lt)
    have hlogle : Real.log (p : ℝ) ≤ Real.log y := Real.log_le_log hpR hpy
    have hloglogle : Real.log (Real.log (p : ℝ)) ≤ Real.log (Real.log y) :=
      Real.log_le_log hlogp hlogle
    have hcap := omegaUpTo_sub_log_log_le_of_divisorVarianceMass_le_of_le
      v c hc hv0 hv hp hpn hn hPp hmass hL (hpcount ▸ homega)
    rw [hpcount]
    linarith
  · exact Or.inl hearly

/-! ### The finite-dimensional upper rectangle -/

/-- The coordinatewise upper rectangle used in the portmanteau application. -/
def upperRectangle {R : ℕ} (u : Fin R → ℝ) : Set (Fin R → ℝ) :=
  {z | ∀ j, z j ≤ u j}

/-- A finite coordinatewise upper rectangle is closed. -/
theorem isClosed_upperRectangle {R : ℕ} (u : Fin R → ℝ) :
    IsClosed (upperRectangle u) := by
  rw [show upperRectangle u = ⋂ j, {z | z j ≤ u j} by
    ext z
    simp only [upperRectangle, Set.mem_ofPred_eq, Set.mem_iInter]]
  exact isClosed_iInter fun j ↦ isClosed_le (continuous_apply j) continuous_const

/-- The equally spaced FDEK grid on `[0,1]`. -/
noncomputable def equalTimeGrid (R : ℕ) : Fin (R + 1) → ℝ :=
  fun j ↦ (j : ℕ) / (R : ℝ)

/-- Equal grid times are strictly increasing when the grid is nonempty. -/
theorem strictMono_equalTimeGrid {R : ℕ} (hR : 0 < R) :
    StrictMono (equalTimeGrid R) := by
  intro i j hij
  apply div_lt_div_of_pos_right _ (by exact_mod_cast hR)
  exact_mod_cast hij

@[simp]
theorem equalTimeGrid_zero (R : ℕ) : equalTimeGrid R 0 = 0 := by
  simp [equalTimeGrid]

/-- The final equal-grid time is one. -/
theorem equalTimeGrid_last {R : ℕ} (hR : 0 < R) :
    equalTimeGrid R (Fin.last R) = 1 := by
  simp [equalTimeGrid, hR.ne']

/-- Every equal-grid increment has variance `1/R`. -/
theorem equalTimeGrid_increment {R : ℕ} (hR : 0 < R) (j : Fin R) :
    equalTimeGrid R j.succ - equalTimeGrid R j.castSucc = (R : ℝ)⁻¹ := by
  simp only [equalTimeGrid, Fin.val_succ, Fin.val_castSucc, Nat.cast_add, Nat.cast_one]
  field_simp
  ring

/-- The increment-space event that every partial sum stays below a constant barrier. -/
def gaussianPartialSumUpperSet (R : ℕ) (δ : ℝ) : Set (Fin R → ℝ) :=
  {y | ∀ j, ∑ i ∈ Finset.univ.filter (fun i : Fin R ↦ i ≤ j), y i ≤ δ}

/-- The prefix-sum event used by the Brownian adapter is exactly survival of the recursively
defined Gaussian walk below the same constant barrier. -/
theorem gaussianPartialSumUpperSet_eq_survivalSet (R : ℕ) (δ : ℝ) :
    gaussianPartialSumUpperSet R δ = gaussianWalkSurvivalSet R δ := by
  ext y
  simp only [gaussianPartialSumUpperSet, gaussianWalkSurvivalSet, Set.mem_ofPred_eq]
  exact (gaussianWalkSurvives_iff_prefix_sums R δ y).symm

/-- On an equal grid, a `brownianFDD` constant upper rectangle is exactly the iid Gaussian
partial-sum barrier event.  This is the adapter from the portmanteau law to a finite Gaussian
ballot estimate. -/
theorem brownianFDD_upperRectangle_equalTimeGrid {R : ℕ} (hR : 0 < R) (δ : ℝ) :
    brownianFDD R (equalTimeGrid R) (upperRectangle (fun _ ↦ δ)) =
      Measure.pi (fun _ : Fin R ↦ gaussianReal 0 (Real.toNNReal (R : ℝ)⁻¹))
        (gaussianPartialSumUpperSet R δ) := by
  have hsum : Measurable
      (fun y : Fin R → ℝ ↦ fun j : Fin R ↦
        ∑ i ∈ Finset.univ.filter (fun i : Fin R ↦ i ≤ j), y i) := by
    fun_prop
  rw [brownianFDD, Measure.map_apply hsum
    (isClosed_upperRectangle (fun _ : Fin R ↦ δ)).measurableSet]
  rw [show Measure.pi (fun j : Fin R ↦ gaussianReal 0
      (Real.toNNReal (equalTimeGrid R j.succ - equalTimeGrid R j.castSucc))) =
      Measure.pi (fun _ : Fin R ↦ gaussianReal 0 (Real.toNNReal (R : ℝ)⁻¹)) by
    congr 1
    funext j
    rw [equalTimeGrid_increment hR j]]
  congr 1

/-- Soft Gaussian ballot bound for the constant Brownian upper rectangle on the equal grid. -/
theorem brownianFDD_upperRectangle_equalTimeGrid_le
    {R : ℕ} (hR : 0 < R) {δ : ℝ} (hδ : 0 ≤ δ) :
    (brownianFDD R (equalTimeGrid R) (upperRectangle (fun _ ↦ δ))).toReal ≤
      2 * Real.sqrt (δ / Real.sqrt (R : ℝ)⁻¹ + 2) /
        Real.sqrt (Real.sqrt (R : ℝ)) := by
  rw [brownianFDD_upperRectangle_equalTimeGrid hR δ,
    gaussianPartialSumUpperSet_eq_survivalSet]
  have hRreal : (0 : ℝ) < R := by exact_mod_cast hR
  have hv : Real.toNNReal (R : ℝ)⁻¹ ≠ 0 := by
    exact ne_of_gt (Real.toNNReal_pos.mpr (inv_pos.mpr hRreal))
  convert gaussianWalk_fixedVariance_survival_probability_le_fourthRoot R hR hδ hv using 1 <;>
    simp only [Measure.real, Real.coe_toNNReal, inv_nonneg, hRreal.le]

/-- The centering in FDEK is exactly `t log log N` at its exponential cutoff. -/
theorem log_log_exp_log_rpow {N : ℕ} {t : ℝ} (hN : 1 < N) :
    Real.log (Real.log (Real.exp (Real.log N ^ t))) = t * Real.log (Real.log N) := by
  rw [Real.log_exp]
  exact Real.log_rpow (Real.log_pos (by exact_mod_cast hN)) t

/-- The FDEK exponential cutoffs are monotone in their time parameter once `N ≥ 3`. -/
theorem exp_log_rpow_mono {N : ℕ} {s t : ℝ} (hN : 3 ≤ N) (hst : s ≤ t) :
    Real.exp (Real.log N ^ s) ≤ Real.exp (Real.log N ^ t) := by
  apply Real.exp_le_exp.mpr
  have hlog1 : (1 : ℝ) ≤ Real.log N := by
    calc
      (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
      _ ≤ Real.log 3 := Real.log_le_log (Real.exp_pos 1) Real.exp_one_lt_three.le
      _ ≤ Real.log N := Real.log_le_log (by norm_num) (by exact_mod_cast hN)
  exact Real.rpow_le_rpow_of_exponent_le hlog1 hst

/-- The terminal FDEK cutoff is the sample size itself. -/
theorem exp_log_rpow_one {N : ℕ} (hN : 0 < N) :
    Real.exp (Real.log N ^ (1 : ℝ)) = N := by
  rw [Real.rpow_one, Real.exp_log]
  exact_mod_cast hN

/-- The collision cutoff lies below every fixed positive FDEK time, even after a fixed shift of
the sample endpoint. -/
theorem eventually_collisionCutoff_le_exp_log_rpow_add (a : ℕ) {s : ℝ} (hs : 0 < s) :
    ∀ᶠ N : ℕ in atTop,
      (collisionCutoff N : ℝ) ≤ Real.exp (Real.log (N + a) ^ s) := by
  have hsmallReal := (isLittleO_log_rpow_rpow_atTop 2 hs).bound one_pos
  have hlogTop : Tendsto (fun N : ℕ ↦ Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hsmall := hlogTop.eventually hsmallReal
  filter_upwards [hsmall, eventually_ge_atTop 3] with N hsmallN hN
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (lt_of_lt_of_le (by norm_num) hN)
  have hlogN1 : (1 : ℝ) ≤ Real.log N := by
    calc
      (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
      _ ≤ Real.log 3 := Real.log_le_log (Real.exp_pos 1) Real.exp_one_lt_three.le
      _ ≤ Real.log N := Real.log_le_log (by norm_num) (by exact_mod_cast hN)
  have hloglog0 : 0 ≤ Real.log (Real.log N) := Real.log_nonneg hlogN1
  have hrpow0 : 0 ≤ Real.log N ^ s :=
    Real.rpow_nonneg (le_trans zero_le_one hlogN1) _
  have hlogSq : Real.log (Real.log N) ^ 2 ≤ Real.log N ^ s := by
    have hsmallN' : |Real.log (Real.log N) ^ (2 : ℝ)| ≤ Real.log N ^ s := by
      simpa only [Real.norm_eq_abs, abs_of_nonneg hrpow0, one_mul] using hsmallN
    rw [abs_of_nonneg (Real.rpow_nonneg hloglog0 _)] at hsmallN'
    rw [Real.rpow_two] at hsmallN'
    exact hsmallN'
  have hlogMono : Real.log N ≤ Real.log (N + a) := by
    apply Real.log_le_log hNpos
    exact_mod_cast Nat.le_add_right N a
  have hrpowMono : Real.log N ^ s ≤ Real.log (N + a) ^ s :=
    Real.rpow_le_rpow (le_trans zero_le_one hlogN1) hlogMono hs.le
  calc
    (collisionCutoff N : ℝ) ≤ Real.exp (Real.log (Real.log N) ^ 2) := by
      exact Nat.floor_le (Real.exp_pos _).le
    _ ≤ Real.exp (Real.log (N + a) ^ s) :=
      Real.exp_le_exp.mpr (hlogSq.trans hrpowMono)

/-- Shifting the sampled integers by a fixed nonnegative amount only embeds the filtered interval
into the correspondingly enlarged unshifted interval. -/
theorem card_filter_Icc_add_le (Q : ℕ → Prop) [DecidablePred Q] (N a : ℕ) :
    ((Finset.Icc 1 N).filter (fun n ↦ Q (n + a))).card ≤
      ((Finset.Icc 1 (N + a)).filter Q).card := by
  let e : ℕ ↪ ℕ := addRightEmbedding a
  have hsub : ((Finset.Icc 1 N).filter (fun n ↦ Q (n + a))).map e ⊆
      (Finset.Icc 1 (N + a)).filter Q := by
    intro m hm
    rcases Finset.mem_map.mp hm with ⟨n, hn, rfl⟩
    rw [Finset.mem_filter] at hn ⊢
    simp only [Finset.mem_Icc] at hn ⊢
    simp only [e, addRightEmbedding_apply]
    exact ⟨⟨by omega, by omega⟩, hn.2⟩
  simpa only [Finset.card_map] using Finset.card_le_card hsub

/-- The logarithmic chain cap is negligible on the FDEK `√L` scale. -/
theorem eventually_walk_cap_le_sqrt (c T δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ L : ℝ in atTop,
      1 + Real.log (2 * L) + Real.log (T / c) / Real.log 2 ≤ δ * Real.sqrt L := by
  let D : ℝ := 1 + Real.log 2 + Real.log (T / c) / Real.log 2
  have hhalf : (0 : ℝ) < 1 / 2 := by norm_num
  have hsmall := (isLittleO_log_rpow_atTop hhalf).bound (half_pos hδ)
  have hlarge := (tendsto_rpow_atTop hhalf).eventually_ge_atTop (2 * D / δ)
  filter_upwards [hsmall, hlarge, eventually_ge_atTop (1 : ℝ)] with L hlog hpow hL
  have hLpos : 0 < L := zero_lt_one.trans_le hL
  have hlog0 : 0 ≤ Real.log L := Real.log_nonneg hL
  have hrpow0 : 0 ≤ L ^ (1 / 2 : ℝ) := Real.rpow_nonneg hLpos.le _
  have hlog' : Real.log L ≤ (δ / 2) * L ^ (1 / 2 : ℝ) := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg hlog0, abs_of_nonneg hrpow0] using hlog
  have hD : D ≤ (δ / 2) * L ^ (1 / 2 : ℝ) := by
    calc
      D = (δ / 2) * (2 * D / δ) := by field_simp
      _ ≤ (δ / 2) * L ^ (1 / 2 : ℝ) :=
        mul_le_mul_of_nonneg_left hpow (half_pos hδ).le
  rw [Real.sqrt_eq_rpow, Real.log_mul (by norm_num) hLpos.ne']
  dsimp only [D] at hD
  linarith

/-- A fixed positive gap between the early cutoff and a grid time dominates every fixed early
coordinate bound on the `√L` scale. -/
theorem eventually_early_gap_le {s t : ℝ} (hst : s < t) (A δ : ℝ) :
    ∀ᶠ L : ℝ in atTop, A - (t - s) * Real.sqrt L ≤ δ := by
  have hd : 0 < t - s := sub_pos.2 hst
  have hlarge := (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).eventually_ge_atTop
    ((A - δ) / (t - s))
  filter_upwards [hlarge] with L hL
  rw [Real.sqrt_eq_rpow]
  have hmul := mul_le_mul_of_nonneg_left hL hd.le
  rw [mul_div_cancel₀ (A - δ) hd.ne'] at hmul
  linarith

/-- The terminal FDEK coordinate controls the total restricted prime-factor count.  This is the
deterministic conversion used to supply the `ω ≤ 2L` hypothesis in the walk cap. -/
theorem omegaUpTo_le_two_mul_of_normalized_terminal_le_one {y : ℝ} {n : ℕ} {L : ℝ}
    (hL : 1 ≤ L)
    (hterminal : ((omegaUpTo y n : ℝ) - L) / Real.sqrt L ≤ 1) :
    (omegaUpTo y n : ℝ) ≤ 2 * L := by
  have hsqrt_pos : 0 < Real.sqrt L := Real.sqrt_pos.2 (lt_of_lt_of_le zero_lt_one hL)
  have hsqrt_sq : Real.sqrt L * Real.sqrt L = L := by
    nlinarith [Real.sq_sqrt (le_trans (by norm_num) hL)]
  have hsqrt_le : Real.sqrt L ≤ L := by
    nlinarith [Real.sqrt_nonneg L]
  have h := (div_le_iff₀ hsqrt_pos).1 hterminal
  linarith

/-- A freely chosen fixed terminal rectangle threshold supplies the same `ω ≤ 2L` cap once
`√L` dominates that threshold.  Unlike a hard-coded threshold of one, this form lets the
complementary Gaussian terminal tail be made arbitrarily small. -/
theorem omegaUpTo_le_two_mul_of_normalized_terminal_le {y : ℝ} {n : ℕ} {L A : ℝ}
    (hL : 0 < L) (hA : A ≤ Real.sqrt L)
    (hterminal : ((omegaUpTo y n : ℝ) - L) / Real.sqrt L ≤ A) :
    (omegaUpTo y n : ℝ) ≤ 2 * L := by
  have hsqrt_pos : 0 < Real.sqrt L := Real.sqrt_pos.2 hL
  have hsqrt_sq : Real.sqrt L * Real.sqrt L = L := by
    nlinarith [Real.sq_sqrt hL.le]
  have h := (div_le_iff₀ hsqrt_pos).1 hterminal
  have hmul := mul_le_mul_of_nonneg_right hA hsqrt_pos.le
  nlinarith

/-- Every fixed terminal rectangle threshold is eventually at most the FDEK scale `√L`. -/
theorem eventually_const_le_sqrt (A : ℝ) :
    ∀ᶠ L : ℝ in atTop, A ≤ Real.sqrt L := by
  simpa only [Real.sqrt_eq_rpow] using
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).eventually_ge_atTop A

/-- Pointwise deterministic rectangle implication at one grid coordinate.  The early-cutoff
alternative loses `(t-s)√L`, while the prime-jump alternative is bounded by the chain cap.  The
analytic hypotheses at the end are exactly the two scalar comparisons that later hold eventually
for a fixed FDEK grid. -/
theorem normalized_omegaUpTo_cutoff_le
    (v : ℕ → ℝ) (c : ℝ) (hc : 0 < c)
    (hv0 : ∀ m, 0 ≤ v m)
    (hv : ∀ m : ℕ, 2 ≤ m → c * Real.rpow (Real.log m) (-Real.log 2) ≤ v m)
    {P n : ℕ} {x y T L s t A δ : ℝ}
    (hn : n ≠ 0) (hPx : (P : ℝ) ≤ x) (hxy : x ≤ y)
    (hmass : divisorVarianceMass v P n ≤ T) (hL : 0 < L)
    (homega : (omegaUpTo y n : ℝ) ≤ 2 * L)
    (hloglog : Real.log (Real.log y) = t * L)
    (hearly : (omegaUpTo x n : ℝ) - s * L ≤ A * Real.sqrt L)
    (hgap : A - (t - s) * Real.sqrt L ≤ δ)
    (hcap : 1 + Real.log (2 * L) + Real.log (T / c) / Real.log 2 ≤
      δ * Real.sqrt L) :
    ((omegaUpTo y n : ℝ) - t * L) / Real.sqrt L ≤ δ := by
  have hsqrt_pos : 0 < Real.sqrt L := Real.sqrt_pos.2 hL
  rcases omegaUpTo_cutoff_eq_early_or_sub_log_log_le
      v c hc hv0 hv hn hPx hxy hmass hL homega with heq | hjump
  · apply (div_le_iff₀ hsqrt_pos).2
    have hsqrt_sq : Real.sqrt L * Real.sqrt L = L := by
      nlinarith [Real.sq_sqrt hL.le]
    have hmul : (t - s) * L = ((t - s) * Real.sqrt L) * Real.sqrt L := by
      calc
        (t - s) * L = (t - s) * (Real.sqrt L * Real.sqrt L) :=
          congrArg ((t - s) * ·) hsqrt_sq.symm
        _ = ((t - s) * Real.sqrt L) * Real.sqrt L := by ring
    rw [heq]
    calc
      (omegaUpTo x n : ℝ) - t * L =
          ((omegaUpTo x n : ℝ) - s * L) - (t - s) * L := by ring
      _ ≤ A * Real.sqrt L - (t - s) * L := by linarith
      _ = (A - (t - s) * Real.sqrt L) * Real.sqrt L := by
        rw [hmul]
        ring
      _ ≤ δ * Real.sqrt L := mul_le_mul_of_nonneg_right hgap hsqrt_pos.le
  · apply (div_le_iff₀ hsqrt_pos).2
    rw [← hloglog]
    exact hjump.trans hcap

/-! ### Gaussian control-coordinate tails and parameter choice -/

/-- Chebyshev's inequality for a centered real Gaussian. -/
theorem gaussianReal_abs_tail_le {v : NNReal} {r : ℝ} (hr : 0 < r) :
    (gaussianReal 0 v).real {x : ℝ | r ≤ |x|} ≤ (v : ℝ) / r ^ 2 := by
  have hcheb := meas_ge_le_variance_div_sq
    (memLp_id_gaussianReal' (μ := 0) (v := v) 2 (by simp)) hr
  simp only [integral_id_gaussianReal, sub_zero, id_eq, variance_id_gaussianReal] at hcheb
  calc
    (gaussianReal 0 v).real {x | r ≤ |x|} ≤
        (ENNReal.ofReal ((v : ℝ) / r ^ 2)).toReal := by
      exact ENNReal.toReal_mono ENNReal.ofReal_ne_top hcheb
    _ = (v : ℝ) / r ^ 2 := ENNReal.toReal_ofReal (by positivity)

/-- Chebyshev's inequality for the sum of independent centered Gaussian coordinates. -/
theorem gaussianProduct_sum_abs_tail_le (R : ℕ) (v : NNReal)
    {r : ℝ} (hr : 0 < r) :
    (Measure.pi (fun _ : Fin R ↦ gaussianReal 0 v)).real
        {y | r ≤ |∑ i, y i|} ≤ R * (v : ℝ) / r ^ 2 := by
  let μ : Fin R → Measure ℝ := fun _ ↦ gaussianReal 0 v
  let P : Measure (Fin R → ℝ) := Measure.pi μ
  let X : (Fin R → ℝ) → ℝ := fun y ↦ ∑ i, y i
  have hcoord : ∀ i : Fin R, MemLp (fun y : Fin R → ℝ ↦ y i) 2 P := by
    intro i
    exact (memLp_id_gaussianReal' (μ := 0) (v := v) 2 (by simp)).comp_measurePreserving
      (measurePreserving_eval μ i)
  have hX : MemLp X 2 P := by
    exact memLp_finsetSum Finset.univ (fun i _ ↦ hcoord i)
  have hmean_coord : ∀ i : Fin R, ∫ y, y i ∂P = 0 := by
    intro i
    have hid : AEStronglyMeasurable id (P.map (fun y ↦ y i)) := by
      rw [(measurePreserving_eval μ i).map_eq]
      exact (memLp_id_gaussianReal' (μ := 0) (v := v) 2 (by simp)).1
    calc
      ∫ y, y i ∂P = ∫ x, id x ∂(P.map (fun y ↦ y i)) := by
        exact (integral_map (f := id) (μ := P) (φ := fun y ↦ y i)
          (measurable_pi_apply i).aemeasurable hid).symm
      _ = ∫ x, id x ∂gaussianReal 0 v := by
        rw [(measurePreserving_eval μ i).map_eq]
      _ = 0 := integral_id_gaussianReal
  have hmean : ∫ y, X y ∂P = 0 := by
    change ∫ y, ∑ i : Fin R, y i ∂P = 0
    rw [integral_finsetSum Finset.univ
      (fun i _ ↦ (hcoord i).integrable (by norm_num))]
    simp only [hmean_coord, Finset.sum_const_zero]
  have hvariance : Var[X; P] = R * (v : ℝ) := by
    rw [show X = ∑ i : Fin R, fun y ↦ id (y i) by
      funext y
      simp only [X, id_eq, Finset.sum_apply]]
    rw [variance_sum_pi (fun _ ↦ memLp_id_gaussianReal' (μ := 0) (v := v) 2 (by simp))]
    simp only [variance_id_gaussianReal, Finset.sum_const, nsmul_eq_mul,
      Finset.card_univ, Fintype.card_fin]
  have hcheb := meas_ge_le_variance_div_sq hX hr
  rw [hmean, hvariance] at hcheb
  simp only [sub_zero] at hcheb
  calc
    (Measure.pi (fun _ : Fin R ↦ gaussianReal 0 v)).real {y | r ≤ |∑ i, y i|} =
        P.real {y | r ≤ |X y|} := by rfl
    _ ≤ (ENNReal.ofReal (R * (v : ℝ) / r ^ 2)).toReal := by
      exact ENNReal.toReal_mono ENNReal.ofReal_ne_top hcheb
    _ = R * (v : ℝ) / r ^ 2 := ENNReal.toReal_ofReal (by positivity)

/-- The first coordinate of the equal-grid Brownian law has variance `1/R`. -/
theorem brownianFDD_first_ge_le {R : ℕ} (hR : 0 < R) {r : ℝ} (hr : 0 < r) :
    (brownianFDD R (equalTimeGrid R) {z | r ≤ z ⟨0, hR⟩}).toReal ≤
      (R : ℝ)⁻¹ / r ^ 2 := by
  let j₀ : Fin R := ⟨0, hR⟩
  let μ : Fin R → Measure ℝ :=
    fun _ ↦ gaussianReal 0 (Real.toNNReal (R : ℝ)⁻¹)
  have hsum : Measurable
      (fun y : Fin R → ℝ ↦ fun j : Fin R ↦
        ∑ i ∈ Finset.univ.filter (fun i : Fin R ↦ i ≤ j), y i) := by
    fun_prop
  have hclosed : IsClosed {z : Fin R → ℝ | r ≤ z j₀} :=
    isClosed_le continuous_const (continuous_apply j₀)
  rw [brownianFDD, Measure.map_apply hsum hclosed.measurableSet]
  rw [show Measure.pi (fun j : Fin R ↦ gaussianReal 0
      (Real.toNNReal (equalTimeGrid R j.succ - equalTimeGrid R j.castSucc))) =
      Measure.pi μ by
    congr 1
    funext j
    simp only [μ, equalTimeGrid_increment hR j]]
  have hsubset :
      {y : Fin R → ℝ | r ≤ ∑ i ∈ Finset.univ.filter (fun i : Fin R ↦ i ≤ j₀), y i} ⊆
        {y : Fin R → ℝ | r ≤ |y j₀|} := by
    intro y hy
    have hfilter : Finset.univ.filter (fun i : Fin R ↦ i ≤ j₀) = {j₀} := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      constructor
      · intro hi
        apply Fin.ext
        change i.val = 0
        apply Nat.eq_zero_of_le_zero
        change i.val ≤ 0
        change i.val ≤ j₀.val at hi
        exact hi
      · rintro rfl
        exact le_rfl
    rw [hfilter] at hy
    simp only [Finset.sum_singleton] at hy
    change r ≤ |y j₀|
    exact hy.trans (le_abs_self _)
  calc
    (Measure.pi μ).real
        {y | r ≤ ∑ i ∈ Finset.univ.filter (fun i : Fin R ↦ i ≤ j₀), y i} ≤
        (Measure.pi μ).real {y | r ≤ |y j₀|} :=
      measureReal_mono hsubset (measure_ne_top _ _)
    _ = (gaussianReal 0 (Real.toNNReal (R : ℝ)⁻¹)).real {x | r ≤ |x|} := by
      simp only [measureReal_def]
      change ((Measure.pi μ) ((fun y ↦ y j₀) ⁻¹' {x : ℝ | r ≤ |x|})).toReal = _
      rw [← Measure.map_apply (measurable_pi_apply j₀)
          (measurableSet_le measurable_const measurable_id'.abs),
        (measurePreserving_eval μ j₀).map_eq]
    _ ≤ (Real.toNNReal (R : ℝ)⁻¹ : ℝ) / r ^ 2 := gaussianReal_abs_tail_le hr
    _ = (R : ℝ)⁻¹ / r ^ 2 := by
      congr 1
      exact Real.coe_toNNReal ((R : ℝ)⁻¹) (inv_nonneg.mpr (Nat.cast_nonneg R))

/-- The terminal coordinate of the equal-grid Brownian law has variance one. -/
theorem brownianFDD_last_ge_le {R : ℕ} (hR : 0 < R) {r : ℝ} (hr : 0 < r) :
    (brownianFDD R (equalTimeGrid R) {z | r ≤ z ⟨R - 1, by omega⟩}).toReal ≤
      1 / r ^ 2 := by
  let jlast : Fin R := ⟨R - 1, by omega⟩
  let μ : Fin R → Measure ℝ :=
    fun _ ↦ gaussianReal 0 (Real.toNNReal (R : ℝ)⁻¹)
  have hsum : Measurable
      (fun y : Fin R → ℝ ↦ fun j : Fin R ↦
        ∑ i ∈ Finset.univ.filter (fun i : Fin R ↦ i ≤ j), y i) := by
    fun_prop
  have hclosed : IsClosed {z : Fin R → ℝ | r ≤ z jlast} :=
    isClosed_le continuous_const (continuous_apply jlast)
  rw [brownianFDD, Measure.map_apply hsum hclosed.measurableSet]
  rw [show Measure.pi (fun j : Fin R ↦ gaussianReal 0
      (Real.toNNReal (equalTimeGrid R j.succ - equalTimeGrid R j.castSucc))) =
      Measure.pi μ by
    congr 1
    funext j
    simp only [μ, equalTimeGrid_increment hR j]]
  have hfilter :
      Finset.univ.filter (fun i : Fin R ↦ i ≤ jlast) = Finset.univ := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
    change i.val ≤ R - 1
    omega
  change (Measure.pi μ).real
    {y | r ≤ ∑ i ∈ Finset.univ.filter (fun i : Fin R ↦ i ≤ jlast), y i} ≤ _
  rw [hfilter]
  calc
    (Measure.pi μ).real {y | r ≤ ∑ i, y i} ≤
        (Measure.pi μ).real {y | r ≤ |∑ i, y i|} := by
      apply measureReal_mono _ (measure_ne_top _ _)
      intro y hy
      change r ≤ |∑ i, y i|
      exact hy.trans (le_abs_self _)
    _ ≤ R * (Real.toNNReal (R : ℝ)⁻¹ : ℝ) / r ^ 2 :=
      gaussianProduct_sum_abs_tail_le R _ hr
    _ = 1 / r ^ 2 := by
      rw [Real.coe_toNNReal ((R : ℝ)⁻¹) (inv_nonneg.mpr (Nat.cast_nonneg R))]
      have hRreal : (R : ℝ) ≠ 0 := by exact_mod_cast hR.ne'
      rw [mul_inv_cancel₀ hRreal]

/-- On the grid `R = q^8` with barrier `q⁻²`, both the ballot probability and the first
coordinate control probability are `O(1/q)`. -/
theorem equalTimeGrid_control_bounds (q : ℕ) (hq : 0 < q) :
    let R := q ^ 8
    let δ := ((q : ℝ) ^ 2)⁻¹
    2 * Real.sqrt (δ / Real.sqrt (R : ℝ)⁻¹ + 2) /
        Real.sqrt (Real.sqrt (R : ℝ)) ≤ 4 / q ∧
      (R : ℝ)⁻¹ / δ ^ 2 ≤ 1 / q := by
  dsimp only
  let x : ℝ := q
  have hx : 1 ≤ x := by
    dsimp only [x]
    exact_mod_cast (show 1 ≤ q by omega)
  have hx0 : 0 < x := zero_lt_one.trans_le hx
  have hcast : ((q ^ 8 : ℕ) : ℝ) = x ^ 8 := by
    simp only [Nat.cast_pow, x]
  have hsqrt8 : Real.sqrt (x ^ 8) = x ^ 4 := by
    rw [show x ^ 8 = (x ^ 4) ^ 2 by ring, Real.sqrt_sq (by positivity)]
  have hsqrt4 : Real.sqrt (x ^ 4) = x ^ 2 := by
    rw [show x ^ 4 = (x ^ 2) ^ 2 by ring, Real.sqrt_sq (by positivity)]
  have hsqrtInv : Real.sqrt (x ^ 8)⁻¹ = (x ^ 4)⁻¹ := by
    rw [Real.sqrt_inv, hsqrt8]
  rw [hcast, hsqrtInv, hsqrt8, hsqrt4]
  have hquot : (x ^ 2)⁻¹ / (x ^ 4)⁻¹ = x ^ 2 := by
    field_simp
  rw [hquot]
  constructor
  · have hsqrt_le : Real.sqrt (x ^ 2 + 2) ≤ 2 * x := by
      rw [← Real.sqrt_sq (by positivity : (0 : ℝ) ≤ 2 * x)]
      apply Real.sqrt_le_sqrt
      nlinarith [sq_nonneg x]
    calc
      2 * Real.sqrt (x ^ 2 + 2) / x ^ 2 ≤ 2 * (2 * x) / x ^ 2 := by
        gcongr
      _ = 4 / x := by field_simp <;> norm_num
  · have hinvpow : (x ^ 8)⁻¹ / ((x ^ 2)⁻¹) ^ 2 = (x ^ 4)⁻¹ := by
      field_simp
    rw [hinvpow]
    have hxpow : x ≤ x ^ 4 := by
      calc
        x = x ^ 1 := (pow_one x).symm
        _ ≤ x ^ 4 := pow_le_pow_right₀ hx (by norm_num)
    simpa only [one_div, x] using one_div_le_one_div_of_le hx0 hxpow

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
  classical
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨nq, hnq⟩ := exists_nat_one_div_lt (show 0 < ε / 100 by positivity)
  let q : ℕ := nq + 1
  let R : ℕ := q ^ 8
  let δ : ℝ := ((q : ℝ) ^ 2)⁻¹
  let A : ℝ := q
  let η : ℝ := ε / 100
  let j₀ : Fin R := ⟨0, by simp only [R, q]; positivity⟩
  let jlast : Fin R := ⟨R - 1, by
    simp only [R, q]
    have : 0 < (nq + 1) ^ 8 := by positivity
    omega⟩
  let Fmain : Set (Fin R → ℝ) := upperRectangle (fun _ ↦ δ)
  let Ffirst : Set (Fin R → ℝ) := {z | δ ≤ z j₀}
  let Flast : Set (Fin R → ℝ) := {z | A ≤ z jlast}
  have hq : 0 < q := by simp only [q]; omega
  have hR : 0 < R := by simp only [R]; positivity
  have hqsmall : 1 / (q : ℝ) < η := by
    simpa only [q, η, Nat.cast_add, Nat.cast_one] using hnq
  have hη : 0 < η := by simp only [η]; positivity
  have hgrid := equalTimeGrid_control_bounds q hq
  have hFmain : IsClosed Fmain := isClosed_upperRectangle _
  have hFfirst : IsClosed Ffirst :=
    isClosed_le continuous_const (continuous_apply j₀)
  have hFlast : IsClosed Flast :=
    isClosed_le continuous_const (continuous_apply jlast)
  have htimeLast : equalTimeGrid R jlast.succ = 1 := by
    have hj : jlast.succ = Fin.last R := by
      apply Fin.ext
      simp only [jlast, Fin.val_succ, Fin.val_last]
      omega
    rw [hj, equalTimeGrid_last hR]
  have htimeFirst : equalTimeGrid R j₀.succ = (R : ℝ)⁻¹ := by
    simp only [equalTimeGrid, j₀, Fin.val_succ, Nat.cast_one, zero_add]
    rw [one_div]
  have hmainMeasure : (brownianFDD R (equalTimeGrid R) Fmain).toReal ≤ 4 / q := by
    exact (brownianFDD_upperRectangle_equalTimeGrid_le hR
      (show 0 ≤ δ by simp only [δ]; positivity)).trans hgrid.1
  have hfirstMeasure : (brownianFDD R (equalTimeGrid R) Ffirst).toReal ≤ 1 / q := by
    exact (brownianFDD_first_ge_le hR
      (show 0 < δ by simp only [δ]; positivity)).trans hgrid.2
  have hlastMeasure : (brownianFDD R (equalTimeGrid R) Flast).toReal ≤ 1 / q := by
    have htail := brownianFDD_last_ge_le hR
      (show 0 < A by simp only [A]; exact_mod_cast hq)
    have hqR : (1 : ℝ) ≤ q := by exact_mod_cast (show 1 ≤ q by omega)
    exact htail.trans (by
      have hqpos : (0 : ℝ) < q := zero_lt_one.trans_le hqR
      rw [div_le_div_iff₀ (sq_pos_of_pos hqpos) hqpos]
      nlinarith [sq_nonneg ((q : ℝ) - 1)])
  have hmainEK := hEK R (equalTimeGrid R) (strictMono_equalTimeGrid hR)
    (equalTimeGrid_zero R) (equalTimeGrid_last hR).le Fmain hFmain η hη
  have hfirstEK := hEK R (equalTimeGrid R) (strictMono_equalTimeGrid hR)
    (equalTimeGrid_zero R) (equalTimeGrid_last hR).le Ffirst hFfirst η hη
  have hlastEK := hEK R (equalTimeGrid R) (strictMono_equalTimeGrid hR)
    (equalTimeGrid_zero R) (equalTimeGrid_last hR).le Flast hFlast η hη
  have hmainEKN := (tendsto_add_atTop_nat a₀).eventually hmainEK
  have hfirstEKN := (tendsto_add_atTop_nat a₀).eventually hfirstEK
  have hlastEKN := (tendsto_add_atTop_nat a₀).eventually hlastEK
  have hLtop : Tendsto (fun N : ℕ ↦ Real.log (Real.log ((N + a₀ : ℕ) : ℝ))) atTop atTop :=
    Real.tendsto_log_atTop.comp
      (Real.tendsto_log_atTop.comp
        (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat a₀)))
  have hcapN := hLtop.eventually (eventually_walk_cap_le_sqrt c T δ
    (show 0 < δ by simp only [δ]; positivity))
  have hAsqrtN := hLtop.eventually (eventually_const_le_sqrt A)
  have hcutN := eventually_collisionCutoff_le_exp_log_rpow_add a₀
    (show 0 < (R : ℝ)⁻¹ by positivity)
  apply eventually_atTop.1
  filter_upwards [hmainEKN, hfirstEKN, hlastEKN, hcapN, hAsqrtN, hcutN,
      eventually_ge_atTop (max 3 a₀)] with N hmainN hfirstN hlastN hcap hAsqrt hcut hN
  let M : ℕ := N + a₀
  let L : ℝ := Real.log (Real.log M)
  let Z : ℕ → (Fin R → ℝ) := fun m j ↦
    ((omegaUpTo (Real.exp (Real.log M ^ equalTimeGrid R j.succ)) m : ℝ) -
        equalTimeGrid R j.succ * L) / Real.sqrt L
  let Q : ℕ → Prop := fun m ↦
    divisorVarianceMass v (collisionCutoff N) m ≤ T
  let S := (Finset.Icc 1 M).filter Q
  let Smain := (Finset.Icc 1 M).filter (fun m ↦ Z m ∈ Fmain)
  let Sfirst := (Finset.Icc 1 M).filter (fun m ↦ Z m ∈ Ffirst)
  let Slast := (Finset.Icc 1 M).filter (fun m ↦ Z m ∈ Flast)
  have hM3 : 3 ≤ M := by simp only [M]; omega
  have hMpos : 0 < M := by omega
  have hLpos : 0 < L := by
    simp only [L]
    exact Real.log_pos (by
      calc
        (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
        _ < Real.log 3 := Real.strictMonoOn_log (Real.exp_pos 1) (by norm_num)
          Real.exp_one_lt_three
        _ ≤ Real.log M := Real.log_le_log (by norm_num) (by exact_mod_cast hM3))
  have hsub : S ⊆ Smain ∪ (Sfirst ∪ Slast) := by
    intro m hm
    have hmIcc := (Finset.mem_filter.mp hm).1
    have hmass := (Finset.mem_filter.mp hm).2
    rw [Finset.mem_union, Finset.mem_union]
    by_cases hfirstbad : δ ≤ Z m j₀
    · exact Or.inr (Or.inl (Finset.mem_filter.mpr ⟨hmIcc, hfirstbad⟩))
    by_cases hlastbad : A ≤ Z m jlast
    · exact Or.inr (Or.inr (Finset.mem_filter.mpr ⟨hmIcc, hlastbad⟩))
    apply Or.inl
    rw [Finset.mem_filter]
    refine ⟨hmIcc, ?_⟩
    intro j
    by_cases hj : j = j₀
    · subst j
      exact le_of_not_ge hfirstbad
    have hjlt : j₀.succ < j.succ := by
      apply Fin.mk_lt_mk.mpr
      have hjpos : 0 < j.val := by
        by_contra hjzero
        have : j.val = 0 := by omega
        apply hj
        apply Fin.ext
        simpa only [j₀] using this
      change j₀.val + 1 < j.val + 1
      dsimp only [j₀]
      omega
    have hst : equalTimeGrid R j₀.succ < equalTimeGrid R j.succ :=
      strictMono_equalTimeGrid hR hjlt
    have hxy : Real.exp (Real.log M ^ equalTimeGrid R j₀.succ) ≤
        Real.exp (Real.log M ^ equalTimeGrid R j.succ) :=
      exp_log_rpow_mono hM3 hst.le
    have hm0 : m ≠ 0 := by
      have hm1 : 1 ≤ m := (Finset.mem_Icc.mp hmIcc).1
      omega
    have htermNorm :
        ((omegaUpTo (M : ℝ) m : ℝ) - L) / Real.sqrt L ≤ A := by
      have ht := le_of_not_ge hlastbad
      simp only [Z, htimeLast, one_mul] at ht
      rw [exp_log_rpow_one hMpos] at ht
      exact ht
    have homega : (omegaUpTo (M : ℝ) m : ℝ) ≤ 2 * L :=
      omegaUpTo_le_two_mul_of_normalized_terminal_le hLpos hAsqrt htermNorm
    have hearlyNorm :
        ((omegaUpTo (Real.exp (Real.log M ^ equalTimeGrid R j₀.succ)) m : ℝ) -
          equalTimeGrid R j₀.succ * L) / Real.sqrt L ≤ δ :=
      le_of_not_ge hfirstbad
    have hearly :
        (omegaUpTo (Real.exp (Real.log M ^ equalTimeGrid R j₀.succ)) m : ℝ) -
          equalTimeGrid R j₀.succ * L ≤ δ * Real.sqrt L :=
      (div_le_iff₀ (Real.sqrt_pos.2 hLpos)).mp hearlyNorm
    have hgap : δ - (equalTimeGrid R j.succ - equalTimeGrid R j₀.succ) *
        Real.sqrt L ≤ δ := by
      have : 0 ≤ (equalTimeGrid R j.succ - equalTimeGrid R j₀.succ) * Real.sqrt L :=
        mul_nonneg (sub_nonneg.mpr hst.le) (Real.sqrt_nonneg L)
      linarith
    have hloglog := log_log_exp_log_rpow (N := M) (t := equalTimeGrid R j.succ)
      (show 1 < M by omega)
    have hPfirst : (collisionCutoff N : ℝ) ≤
        Real.exp (Real.log M ^ equalTimeGrid R j₀.succ) := by
      simpa only [M, htimeFirst, Nat.cast_add] using hcut
    have htjle : equalTimeGrid R j.succ ≤ 1 := by
      rw [← equalTimeGrid_last hR]
      exact (strictMono_equalTimeGrid hR).monotone (Fin.le_last _)
    have hyM : Real.exp (Real.log M ^ equalTimeGrid R j.succ) ≤ (M : ℝ) := by
      calc
        Real.exp (Real.log M ^ equalTimeGrid R j.succ) ≤
            Real.exp (Real.log M ^ (1 : ℝ)) := exp_log_rpow_mono hM3 htjle
        _ = M := exp_log_rpow_one hMpos
    have homegaYNat :
        omegaUpTo (Real.exp (Real.log M ^ equalTimeGrid R j.succ)) m ≤
          omegaUpTo (M : ℝ) m := by
      unfold omegaUpTo
      apply Finset.card_le_card
      intro p hp
      simp only [Finset.mem_filter] at hp ⊢
      exact ⟨hp.1, hp.2.trans hyM⟩
    have homegaY :
        (omegaUpTo (Real.exp (Real.log M ^ equalTimeGrid R j.succ)) m : ℝ) ≤ 2 * L := by
      have hcast :
          (omegaUpTo (Real.exp (Real.log M ^ equalTimeGrid R j.succ)) m : ℝ) ≤
            (omegaUpTo (M : ℝ) m : ℝ) := by
        exact_mod_cast homegaYNat
      exact hcast.trans homega
    have hresult := normalized_omegaUpTo_cutoff_le v c hc hv0 hv hm0 hPfirst hxy
      hmass hLpos homegaY hloglog hearly hgap hcap
    exact hresult
  have hcard : S.card ≤ Smain.card + Sfirst.card + Slast.card := by
    have h₁ := Finset.card_le_card hsub
    have h₂ := Finset.card_union_le Smain (Sfirst ∪ Slast)
    have h₃ := Finset.card_union_le Sfirst Slast
    omega
  have hmainDensity : (Smain.card : ℝ) / M ≤ 4 / q + η := by
    calc
      (Smain.card : ℝ) / M ≤ (brownianFDD R (equalTimeGrid R) Fmain).toReal + η := hmainN
      _ ≤ 4 / q + η := by gcongr
  have hfirstDensity : (Sfirst.card : ℝ) / M ≤ 1 / q + η := by
    calc
      (Sfirst.card : ℝ) / M ≤ (brownianFDD R (equalTimeGrid R) Ffirst).toReal + η := hfirstN
      _ ≤ 1 / q + η := by gcongr
  have hlastDensity : (Slast.card : ℝ) / M ≤ 1 / q + η := by
    calc
      (Slast.card : ℝ) / M ≤ (brownianFDD R (equalTimeGrid R) Flast).toReal + η := hlastN
      _ ≤ 1 / q + η := by gcongr
  have hshiftCard :
      ((Finset.Icc 1 N).filter (fun m ↦
        divisorVarianceMass v (collisionCutoff N) (m + a₀) ≤ T)).card ≤ S.card := by
    simpa only [Q, S, M] using card_filter_Icc_add_le Q N a₀
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hMreal : (0 : ℝ) < M := by exact_mod_cast hMpos
  have hMN : (M : ℝ) / N ≤ 2 := by
    apply (div_le_iff₀ hNpos).2
    simp only [M, Nat.cast_add]
    have haN : a₀ ≤ N := le_trans (le_max_right 3 a₀) hN
    exact_mod_cast (show N + a₀ ≤ 2 * N by omega)
  have hsumDensity :
      ((Smain.card + Sfirst.card + Slast.card : ℕ) : ℝ) / M ≤
        6 / q + 3 * η := by
    push_cast
    calc
      ((Smain.card : ℝ) + Sfirst.card + Slast.card) / M =
          (Smain.card : ℝ) / M + Sfirst.card / M + Slast.card / M := by ring
      _ ≤ (4 / q + η) + (1 / q + η) + (1 / q + η) := by gcongr
      _ = 6 / q + 3 * η := by ring
  have hbound :
      (((Finset.Icc 1 N).filter (fun m ↦
        divisorVarianceMass v (collisionCutoff N) (m + a₀) ≤ T)).card : ℝ) / N < ε := by
    calc
      (((Finset.Icc 1 N).filter (fun m ↦
          divisorVarianceMass v (collisionCutoff N) (m + a₀) ≤ T)).card : ℝ) / N
          ≤ (S.card : ℝ) / N := by gcongr
      _ ≤ ((Smain.card + Sfirst.card + Slast.card : ℕ) : ℝ) / N := by gcongr
      _ = (((Smain.card + Sfirst.card + Slast.card : ℕ) : ℝ) / M) *
          ((M : ℝ) / N) := by field_simp
      _ ≤ (6 / q + 3 * η) * 2 :=
        mul_le_mul hsumDensity hMN (by positivity) (by positivity)
      _ < ε := by
        have hsix : 6 / (q : ℝ) < 6 * η := by
          calc
            6 / (q : ℝ) = 6 * (1 / (q : ℝ)) := by ring
            _ < 6 * η := mul_lt_mul_of_pos_left hqsmall (by norm_num)
        calc
          (6 / (q : ℝ) + 3 * η) * 2 < (6 * η + 3 * η) * 2 := by
            gcongr
          _ < ε := by simp only [η]; linarith
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (div_nonneg (by positivity) (by positivity))]
  exact hbound

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
