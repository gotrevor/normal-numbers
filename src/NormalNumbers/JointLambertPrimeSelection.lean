/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import NormalNumbers.JointLambertArithmetic

set_option maxHeartbeats 1000000

/-!
# Prime selection for the joint Lambert progression (paper §3 + §4 head)

Paper: `papers/2026-09-26-joint-lambert-disjunctivity.md`, §3 (the inherited analytic
input) and the prime-selection opening of §4.

`NormalNumbers.JointLambert.exists_joint_progression` (in `JointLambertArithmetic.lean`)
is a *finite CRT theorem*: it takes the primes `q` and `p j t` as **data**.  This file
supplies that data.  It is the first place an analytic input is unavoidable, and both
inputs are carried as **explicit named `Prop`s passed as hypotheses** — `AGP` and
`PrimeIntervalSupply` — never as global axioms, and never as the old vacuous
`PrimeDensityAP`.

## The two inputs

* `AGP` — the Alford–Granville–Pomerance consequence used by Vandehey, Prop. 2.1:
  there are `X0, D0` such that for every `X ≥ X0` an exceptional set `𝒟(X)` of at most
  `D0` integers, each exceeding `log X`, exists **before** any modulus is chosen, and
  for every `B ≥ 1` with `B ≤ X^(1/4)`, every `u` coprime to `B`, and no exceptional `D`
  dividing `B`, the count of primes `≤ X` in the class `u mod B` is at least
  `X / (2 φ(B) log X)`.
* `PrimeIntervalSupply` — the standard PNT consequence that `(L, 2L)` contains at least
  `L / (3 log L)` primes for `L` large.

Neither is strengthened here.  The exceptional set is quantified so that it is fixed
before `B`, `u` and the prime allocation, exactly as the paper demands.

## Structure

1. `killOffset` / `killPoolSize` flatten the doubly-indexed killed-slot family
   `(j, t) ↦ p j t` into one initial segment of length `∑_{j<k, j≠r} (j+1)`.
2. `exists_prime_allocation` — the **finite avoidance and allocation** theorem: a pool
   of `1 + killPoolSize k r + #𝒟` primes suffices to pick `q` and every `p j t`
   distinctly while no exceptional modulus divides `jointB`.  One prime is deleted per
   exceptional modulus; `D = 0` and moduli with no pool prime divisor are handled.
3. `pow_four_le_two_pow` / `exists_selection_scale` — the asymptotic availability of the
   parameters, *proved*, not assumed.
4. `exists_joint_prime_candidates` — the target: from `AGP` and `PrimeIntervalSupply`,
   parameters `k ≥ K` with the dyadic schedule `L = 2^k`, `U = 2^(k^4)`, `X = U^4`,
   primes in `(L, 2L)`, the full `exists_joint_progression` conclusion, the size bounds
   `Q ≤ (2L)^(a-1)`, `B ≤ (2L)^(1 + c · killPoolSize)`, `B ≤ U`, `Q ≤ U`, `R > L`, and a
   real lower bound `M / (16 k^4)` on the number of prime candidate indices.

The dyadic schedule (`L = 2^k` rather than the paper's `L = ⌊(log₂ X)²⌋`) is authorized
for the *qualitative* theorem; it is what the scalar formalization uses and it avoids
logarithmic floors.  The quantitative all-`N` bound of the paper is a separate target.
-/

namespace NormalNumbers.JointLambert

open Finset

/-- **The AGP input** (Alford–Granville–Pomerance 1994, in the form of Vandehey,
Prop. 2.1).  Source-faithful: the exceptional set `Dset` depends only on `X`, and is
therefore fixed *before* the modulus `B`, the residue `u`, and the prime allocation. -/
def AGP : Prop :=
  ∃ X0 D0 : ℕ, ∀ X : ℕ, X0 ≤ X →
    ∃ Dset : Finset ℕ, Dset.card ≤ D0 ∧ (∀ D ∈ Dset, Real.log X < D) ∧
      ∀ B u : ℕ, 1 ≤ B → (B : ℝ) ≤ (X : ℝ) ^ ((1 : ℝ) / 4) →
        Nat.Coprime u B → (∀ D ∈ Dset, ¬ D ∣ B) →
        (X : ℝ) / (2 * B.totient * Real.log X) ≤
          (((range (X + 1)).filter (fun z => z.Prime ∧ z % B = u % B)).card : ℝ)

/-- **The prime-interval supply input**: a standard PNT consequence, that the *open*
interval `(L, 2L)` contains at least `L / (3 log L)` primes once `L` is large. -/
def PrimeIntervalSupply : Prop :=
  ∃ L0 : ℕ, ∀ L : ℕ, L0 ≤ L → 2 ≤ L →
    (L : ℝ) / (3 * Real.log L) ≤ (((Ioo L (2 * L)).filter Nat.Prime).card : ℝ)

/-- Total number of killed-slot primes needed: `∑_{j < k, j ≠ r} (j + 1)`. -/
def killPoolSize (k r : ℕ) : ℕ := ∑ j ∈ killedIdx k r, (j + 1)

/-- Offset of killed slot `j` in the flat enumeration of the killed-slot primes. -/
def killOffset (k r j : ℕ) : ℕ :=
  ∑ i ∈ (killedIdx k r).filter (fun i => i < j), (i + 1)

/-! ### Flattening the killed-slot index set -/

private lemma sum_insert_filter_self (k r j : ℕ) :
    ∑ i ∈ insert j ((killedIdx k r).filter (fun i => i < j)), (i + 1)
      = (j + 1) + killOffset k r j := by
  rw [Finset.sum_insert (by simp)]
  rfl

/-- Slot offsets are spread out: consecutive killed slots leave room for all `j+1` primes
of slot `j`. -/
lemma killOffset_add_le {k r j j' : ℕ} (hj : j ∈ killedIdx k r) (hjj : j < j') :
    killOffset k r j + (j + 1) ≤ killOffset k r j' := by
  have hsub : insert j ((killedIdx k r).filter (fun i => i < j)) ⊆
      (killedIdx k r).filter (fun i => i < j') := by
    intro i hi
    simp only [Finset.mem_insert, Finset.mem_filter] at hi ⊢
    rcases hi with rfl | ⟨h1, h2⟩
    · exact ⟨hj, hjj⟩
    · exact ⟨h1, by omega⟩
  have h := Finset.sum_le_sum_of_subset (f := fun i => i + 1) hsub
  rw [sum_insert_filter_self] at h
  simp only [killOffset] at h ⊢
  omega

/-- Every flat index `killOffset k r j + t` used by the allocation lies below
`killPoolSize k r`. -/
lemma killOffset_add_lt {k r j t : ℕ} (hj : j ∈ killedIdx k r) (ht : t < j + 1) :
    killOffset k r j + t < killPoolSize k r := by
  have hsub : insert j ((killedIdx k r).filter (fun i => i < j)) ⊆ killedIdx k r := by
    intro i hi
    simp only [Finset.mem_insert, Finset.mem_filter] at hi
    rcases hi with rfl | ⟨h1, _⟩
    · exact hj
    · exact h1
  have h := Finset.sum_le_sum_of_subset (f := fun i => i + 1) hsub
  rw [sum_insert_filter_self] at h
  simp only [killPoolSize, killOffset] at h ⊢
  omega

/-- The flattening `(j, t) ↦ killOffset k r j + t` is injective on the killed-slot index
set. -/
lemma killOffset_inj {k r j t j' t' : ℕ} (hj : j ∈ killedIdx k r) (hj' : j' ∈ killedIdx k r)
    (ht : t < j + 1) (ht' : t' < j' + 1)
    (h : killOffset k r j + t = killOffset k r j' + t') : j = j' ∧ t = t' := by
  rcases lt_trichotomy j j' with hlt | heq | hgt
  · have := killOffset_add_le hj hlt; omega
  · subst heq; exact ⟨rfl, by omega⟩
  · have := killOffset_add_le hj' hgt; omega

private lemma sum_range_succ_le_sq (k : ℕ) : ∑ j ∈ range k, (j + 1) ≤ k ^ 2 := by
  induction k with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ]
    have h2 : n ^ 2 + (n + 1) ≤ (n + 1) ^ 2 := by nlinarith
    omega

/-- `killPoolSize k r = ∑_{j<k, j≠r} (j+1) ≤ k²`. -/
lemma killPoolSize_le_sq (k r : ℕ) : killPoolSize k r ≤ k ^ 2 := by
  refine le_trans (Finset.sum_le_sum_of_subset (f := fun i => i + 1) ?_) (sum_range_succ_le_sq k)
  intro i hi
  exact Finset.mem_range.mpr (mem_killedIdx.mp hi).2

/-! ### Which primes can divide `jointB` -/

/-- `jointB` is positive as soon as `q` and the killed-slot primes are. -/
lemma jointB_pos {c k r q : ℕ} {p : ℕ → ℕ → ℕ} (hq : 0 < q)
    (hp : ∀ j t, j ∈ killedIdx k r → t < j + 1 → 0 < p j t) : 0 < jointB c k r q p := by
  simp only [jointB, killCore]
  refine Nat.mul_pos hq (Finset.prod_pos fun j hj => pow_pos ?_ c)
  simp only [slotProd]
  exact Finset.prod_pos fun t ht => hp j t hj (Finset.mem_range.mp ht)

/-- Every prime dividing `jointB` is one of the selected primes.  This is what makes the
"remove one prime per exceptional modulus" strategy work: `jointB` is a product of powers
of the chosen primes and nothing else. -/
lemma prime_dvd_jointB {c k r q : ℕ} {p : ℕ → ℕ → ℕ} {π : ℕ} (hπ : π.Prime)
    (hqp : q.Prime) (hp : ∀ j t, j ∈ killedIdx k r → t < j + 1 → (p j t).Prime)
    (h : π ∣ jointB c k r q p) :
    π = q ∨ ∃ j ∈ killedIdx k r, ∃ t, t < j + 1 ∧ π = p j t := by
  simp only [jointB, killCore] at h
  rcases (Nat.Prime.dvd_mul hπ).mp h with h1 | h1
  · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hπ hqp).mp h1)
  · obtain ⟨j, hj, hdvd⟩ := (Prime.dvd_finsetProd_iff hπ.prime _).mp h1
    have hd2 : π ∣ slotProd p j := hπ.dvd_of_dvd_pow hdvd
    simp only [slotProd] at hd2
    obtain ⟨t, ht, hdt⟩ := (Prime.dvd_finsetProd_iff hπ.prime _).mp hd2
    exact Or.inr ⟨j, hj, t, Finset.mem_range.mp ht,
      (Nat.prime_dvd_prime_iff_eq hπ (hp j t hj (Finset.mem_range.mp ht))).mp hdt⟩

/-! ### Finite avoidance and allocation -/

/-- **Finite avoidance and allocation.**

A pool `S` of primes with at least `1 + killPoolSize k r + #Dset` members permits choosing
`q` and the entire killed-slot family `p j t` (`j < k`, `j ≠ r`, `t < j+1`) pairwise
distinctly inside `S`, in such a way that **no** exceptional modulus `D ∈ Dset` with
`D ≠ 1` divides `jointB c k r q p` — hence none divides any product of powers of the
selected primes.

The removal is one prime per exceptional modulus: for each `D ∈ Dset` having a prime
divisor in `S`, the least such divisor is deleted from the pool before allocation, so at
most `#Dset` primes are lost.  The two degenerate cases are handled:

* an exceptional `D` with **no** prime divisor in `S` costs nothing, since then no selected
  prime divides `D`, and if `D ∣ jointB` its least prime factor would have to be a selected
  prime (by `prime_dvd_jointB`), which lies in `S` — a contradiction;
* `D = 0` cannot divide `jointB` because `jointB > 0`.

`D = 1` is genuinely excluded, not glossed: `1` divides everything.  In the application
`Dset` consists of integers exceeding `log X ≥ 2`, so `D ≠ 1` is automatic. -/
theorem exists_prime_allocation (c k r : ℕ) (S Dset : Finset ℕ)
    (hS : ∀ π ∈ S, π.Prime)
    (hcard : 1 + killPoolSize k r + Dset.card ≤ S.card) :
    ∃ (q : ℕ) (p : ℕ → ℕ → ℕ),
      q ∈ S ∧ (∀ j t, j ∈ killedIdx k r → t < j + 1 → p j t ∈ S) ∧
      (∀ j t, j ∈ killedIdx k r → t < j + 1 → p j t ≠ q) ∧
      (∀ j t j' t', j ∈ killedIdx k r → t < j + 1 → j' ∈ killedIdx k r → t' < j' + 1 →
        p j t = p j' t' → j = j' ∧ t = t') ∧
      (∀ D ∈ Dset, D ≠ 1 → ¬ D ∣ jointB c k r q p) := by
  classical
  -- the prime removed on account of the exceptional modulus `D`, if any
  set f : ℕ → ℕ := fun D =>
    if h : (D.primeFactors ∩ S).Nonempty then (D.primeFactors ∩ S).min' h else 0 with hf
  set Removed : Finset ℕ := Dset.image f with hRem
  set n : ℕ := 1 + killPoolSize k r with hn
  have hRemcard : Removed.card ≤ Dset.card := Finset.card_image_le
  have hS'card : n ≤ (S \ Removed).card := by
    have := Finset.card_le_card_sdiff_add_card (s := S) (t := Removed)
    omega
  obtain ⟨T, hTS', hT⟩ := Finset.exists_subset_card_eq hS'card
  have hTS : T ⊆ S := hTS'.trans (Finset.sdiff_subset)
  have hTR : ∀ x ∈ T, x ∉ Removed := fun x hx => (Finset.mem_sdiff.mp (hTS' hx)).2
  -- the flat allocation
  set g : ℕ → ℕ := fun i => if h : i < n then T.orderEmbOfFin hT ⟨i, h⟩ else 0 with hg
  have hgT : ∀ i, (h : i < n) → g i ∈ T := by
    intro i h
    simp only [hg, dif_pos h]
    exact T.orderEmbOfFin_mem hT _
  have hginj : ∀ i i', i < n → i' < n → g i = g i' → i = i' := by
    intro i i' hi hi' h
    simp only [hg, dif_pos hi, dif_pos hi'] at h
    have := (T.orderEmbOfFin hT).injective h
    simpa using congrArg Fin.val this
  have hn0 : 0 < n := by omega
  have hidx : ∀ j t, j ∈ killedIdx k r → t < j + 1 → 1 + (killOffset k r j + t) < n := by
    intro j t hj ht
    have := killOffset_add_lt hj ht
    omega
  refine ⟨g 0, fun j t => g (1 + (killOffset k r j + t)), hTS (hgT 0 hn0), ?_, ?_, ?_, ?_⟩
  · intro j t hj ht; exact hTS (hgT _ (hidx j t hj ht))
  · intro j t hj ht h
    have := hginj _ _ (hidx j t hj ht) hn0 h
    omega
  · intro j t j' t' hj ht hj' ht' h
    have := hginj _ _ (hidx j t hj ht) (hidx j' t' hj' ht') h
    exact killOffset_inj hj hj' ht ht' (by omega)
  -- avoidance
  · have hqprime : (g 0).Prime := hS _ (hTS (hgT 0 hn0))
    have hpprime : ∀ j t, j ∈ killedIdx k r → t < j + 1 →
        (g (1 + (killOffset k r j + t))).Prime := fun j t hj ht =>
      hS _ (hTS (hgT _ (hidx j t hj ht)))
    have hpos : 0 < jointB c k r (g 0) (fun j t => g (1 + (killOffset k r j + t))) :=
      jointB_pos hqprime.pos fun j t hj ht => (hpprime j t hj ht).pos
    -- any prime dividing `jointB` lies in `T`, hence outside `Removed`
    have hchosen : ∀ π : ℕ, π.Prime →
        π ∣ jointB c k r (g 0) (fun j t => g (1 + (killOffset k r j + t))) → π ∈ T := by
      intro π hπ hdvd
      rcases prime_dvd_jointB hπ hqprime (fun j t hj ht => hpprime j t hj ht) hdvd with
        h1 | ⟨j, hj, t, ht, h1⟩
      · exact h1 ▸ hgT 0 hn0
      · exact h1 ▸ hgT _ (hidx j t hj ht)
    intro D hD hD1 hdvd
    rcases Nat.eq_zero_or_pos D with rfl | hDpos
    · exact absurd (Nat.eq_zero_of_zero_dvd hdvd) (by omega)
    have hD2 : 2 ≤ D := by rcases Nat.lt_or_ge D 2 with h | h; · interval_cases D <;> omega
                           · exact h
    -- the least prime factor of `D` divides `jointB`, so it is a selected prime, so it is
    -- in `S`; therefore `f D` is defined and is a prime factor of `D` inside `S`
    have hmf : (D.minFac).Prime := Nat.minFac_prime (by omega)
    have hmfS : D.minFac ∈ S := hTS (hchosen _ hmf ((Nat.minFac_dvd D).trans hdvd))
    have hne : (D.primeFactors ∩ S).Nonempty :=
      ⟨D.minFac, Finset.mem_inter.mpr ⟨Nat.mem_primeFactors.mpr ⟨hmf, Nat.minFac_dvd D, by omega⟩,
        hmfS⟩⟩
    have hfmem : f D ∈ D.primeFactors ∩ S := by
      simp only [hf, dif_pos hne]
      exact Finset.min'_mem _ hne
    obtain ⟨hfpf, -⟩ := Finset.mem_inter.mp hfmem
    obtain ⟨hfp, hfd, -⟩ := Nat.mem_primeFactors.mp hfpf
    exact hTR _ (hchosen _ hfp (hfd.trans hdvd)) (Finset.mem_image_of_mem f hD)

/-- **Finite-avoidance control.**  The hypothesis bundle of `exists_prime_allocation` is
satisfiable and its avoidance conclusion has content: with `k = 2`, `r = 1`, `c = 2` (one
killed slot, `j = 0`, needing one prime), pool `{3,5,7,11}` and exceptional set `{6}`, the
required count is `1 + 1 + 1 = 3 ≤ 4`, and the allocation really does dodge `6 ∣ B`.  (Note
`6` has the pool prime divisor `3`, so this exercises the removal branch, not the
vacuous "no pool prime divides `D`" branch.) -/
theorem exists_prime_allocation_nonvacuous :
    ∃ (q : ℕ) (p : ℕ → ℕ → ℕ),
      q ∈ ({3, 5, 7, 11} : Finset ℕ) ∧
      (∀ j t, j ∈ killedIdx 2 1 → t < j + 1 → p j t ∈ ({3, 5, 7, 11} : Finset ℕ)) ∧
      (∀ j t, j ∈ killedIdx 2 1 → t < j + 1 → p j t ≠ q) ∧
      ¬ (6 ∣ jointB 2 2 1 q p) := by
  have hcard : 1 + killPoolSize 2 1 + ({6} : Finset ℕ).card ≤ ({3, 5, 7, 11} : Finset ℕ).card := by
    simp only [killPoolSize, killedIdx]
    decide
  obtain ⟨q, p, h1, h2, h3, -, h5⟩ :=
    exists_prime_allocation 2 2 1 ({3, 5, 7, 11} : Finset ℕ) ({6} : Finset ℕ)
      (by intro π hπ; fin_cases hπ <;> norm_num) hcard
  exact ⟨q, p, h1, h2, h3, h5 6 (by simp) (by norm_num)⟩

/-! ### Asymptotic availability of the parameters (proved, not assumed)

All of these are polynomial-versus-exponential facts in `ℕ`.  They are proved by supplying
the monomial comparisons explicitly and closing with `omega` over the monomials as atoms,
which is far more reliable in `ℕ` than `nlinarith`.
-/

/-- Monomial ladder for `k ≥ 16`, with literal exponents so that `omega` sees the same
atoms as the goals. -/
private lemma monomial_ladder {k : ℕ} (h : 16 ≤ k) :
    16 * k ^ 3 ≤ k ^ 4 ∧ 16 * k ^ 2 ≤ k ^ 3 ∧ 16 * k ≤ k ^ 2 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [show k ^ 4 = k * k ^ 3 by ring]; exact Nat.mul_le_mul h le_rfl
  · rw [show k ^ 3 = k * k ^ 2 by ring]; exact Nat.mul_le_mul h le_rfl
  · rw [show k ^ 2 = k * k by ring]; exact Nat.mul_le_mul h le_rfl

/-- `k⁴ ≤ 2^k` for `k ≥ 16` (equality at `k = 16`).  This single growth fact drives every
parameter inequality of the dyadic schedule. -/
lemma pow_four_le_two_pow : ∀ k : ℕ, 16 ≤ k → k ^ 4 ≤ 2 ^ k := by
  intro k hk
  induction k with
  | zero => omega
  | succ n ih =>
    rcases Nat.lt_or_ge n 16 with h | h
    · have hn : n = 15 := by omega
      subst hn; norm_num
    · have hih := ih h
      obtain ⟨h1, h2, h3⟩ := monomial_ladder h
      have h5 : (n + 1) ^ 4 = n ^ 4 + 4 * n ^ 3 + 6 * n ^ 2 + 4 * n + 1 := by ring
      have h6 : 2 ^ (n + 1) = 2 * 2 ^ n := by rw [pow_succ]; ring
      omega

/-- The three schedule inequalities, from `k ≥ 16`, `4c ≤ k`, `a ≤ k`, `D₀ ≤ k`. -/
private lemma scale_facts {k c a D0 : ℕ} (hk : 16 ≤ k) (hkc : 4 * c ≤ k) (hka : a ≤ k)
    (hkD : D0 ≤ k) :
    3 * k * (1 + k ^ 2 + D0) ≤ 2 ^ k ∧
    (k + 1) * (1 + c * k ^ 2) ≤ k ^ 4 ∧ (k + 1) * (a - 1) ≤ k ^ 4 := by
  have hp := pow_four_le_two_pow k hk
  obtain ⟨m3, m2, m1⟩ := monomial_ladder hk
  -- `c·k^n` ladders, from `4c ≤ k`
  have c3 : 4 * (c * k ^ 3) ≤ k ^ 4 := by
    have : k ^ 4 = k * k ^ 3 := by ring
    rw [this, show 4 * (c * k ^ 3) = 4 * c * k ^ 3 by ring]
    exact Nat.mul_le_mul hkc le_rfl
  have c2 : 4 * (c * k ^ 2) ≤ k ^ 3 := by
    have : k ^ 3 = k * k ^ 2 := by ring
    rw [this, show 4 * (c * k ^ 2) = 4 * c * k ^ 2 by ring]
    exact Nat.mul_le_mul hkc le_rfl
  refine ⟨?_, ?_, ?_⟩
  · have hstep : 3 * k * (1 + k ^ 2 + D0) ≤ k ^ 4 := by
      have hD : 3 * k * (1 + k ^ 2 + D0) ≤ 3 * k * (1 + k ^ 2 + k) :=
        Nat.mul_le_mul le_rfl (by omega)
      have hexp : 3 * k * (1 + k ^ 2 + k) = 3 * k + 3 * k ^ 3 + 3 * k ^ 2 := by ring
      omega
    omega
  · have hexp : (k + 1) * (1 + c * k ^ 2) = 1 + c * k ^ 2 + k + c * k ^ 3 := by ring
    omega
  · obtain ⟨b, hb⟩ : ∃ b, a = b + 1 ∨ a = 0 := ⟨a - 1, by omega⟩
    have hbk : (k + 1) * (a - 1) ≤ (k + 1) * k := Nat.mul_le_mul le_rfl (by omega)
    have hexp : (k + 1) * k = k ^ 2 + k := by ring
    omega

/-- **Asymptotic parameter availability.**  For any cutoffs there is a `k` satisfying every
inequality the dyadic schedule `L = 2^k`, `U = 2^(k⁴)`, `X = U⁴` needs: `k ≥ K`, `k > r`,
`L ≥ L₀`, `X ≥ X₀`, enough primes in `(L, 2L)` for the pool (`3k(1 + k² + D₀) ≤ 2^k`),
`B ≤ U` (`(k+1)(1 + c·k²) ≤ k⁴`) and `Q ≤ U` (`(k+1)(a-1) ≤ k⁴`).  Nothing here is
assumed; this is the "prove the parameter availability" clause of the contract. -/
lemma exists_selection_scale (K r c a D0 X0 L0 : ℕ) :
    ∃ k : ℕ, K ≤ k ∧ r < k ∧ 16 ≤ k ∧ L0 ≤ 2 ^ k ∧ X0 ≤ 2 ^ (4 * k ^ 4) ∧
      3 * k * (1 + k ^ 2 + D0) ≤ 2 ^ k ∧
      (k + 1) * (1 + c * k ^ 2) ≤ k ^ 4 ∧ (k + 1) * (a - 1) ≤ k ^ 4 := by
  set k : ℕ := K + r + 16 + X0 + L0 + 4 * c + a + D0 with hkdef
  have hk16 : 16 ≤ k := by omega
  obtain ⟨f1, f2, f3⟩ := scale_facts hk16 (c := c) (a := a) (D0 := D0)
    (by omega) (by omega) (by omega)
  have hlt : k < 2 ^ k := Nat.lt_two_pow_self
  have hmono : (2 : ℕ) ^ k ≤ 2 ^ (4 * k ^ 4) := by
    refine Nat.pow_le_pow_right (by norm_num) ?_
    have : k ≤ k ^ 4 := Nat.le_self_pow (by norm_num) k
    omega
  exact ⟨k, by omega, by omega, hk16, by omega, by omega, f1, f2, f3⟩

/-! ### Size bookkeeping and the candidate injection -/

/-- `Q = q^(a-1) ≤ (2L)^(a-1)`. -/
lemma jointQ_le {a q L : ℕ} (hq : q < 2 * L) : jointQ a q ≤ (2 * L) ^ (a - 1) :=
  Nat.pow_le_pow_left (by omega) _

/-- `B = q ∏ P_j^c ≤ (2L)^(1 + c · ∑_{j<k, j≠r}(j+1))`, the explicit size bound of §4. -/
lemma jointB_le {c k r q L : ℕ} {p : ℕ → ℕ → ℕ} (hq : q < 2 * L)
    (hp : ∀ j t, j ∈ killedIdx k r → t < j + 1 → p j t < 2 * L) :
    jointB c k r q p ≤ (2 * L) ^ (1 + c * killPoolSize k r) := by
  have hslot : ∀ j ∈ killedIdx k r, slotProd p j ≤ (2 * L) ^ (j + 1) := by
    intro j hj
    simp only [slotProd]
    calc ∏ t ∈ range (j + 1), p j t ≤ ∏ _t ∈ range (j + 1), (2 * L) := by
          refine Finset.prod_le_prod' ?_
          intro t ht
          exact le_of_lt (hp j t hj (Finset.mem_range.mp ht))
      _ = (2 * L) ^ (j + 1) := by rw [Finset.prod_const, Finset.card_range]
  have hcore : killCore c k r p ≤ (2 * L) ^ (c * killPoolSize k r) := by
    simp only [killCore]
    calc ∏ j ∈ killedIdx k r, slotProd p j ^ c
        ≤ ∏ j ∈ killedIdx k r, ((2 * L) ^ (j + 1)) ^ c := by
          refine Finset.prod_le_prod' ?_
          intro j hj
          exact Nat.pow_le_pow_left (hslot j hj) c
      _ = ∏ j ∈ killedIdx k r, (2 * L) ^ (c * (j + 1)) := by
          refine Finset.prod_congr rfl fun j _ => ?_
          rw [← pow_mul, Nat.mul_comm (j + 1) c]
      _ = (2 * L) ^ (∑ j ∈ killedIdx k r, c * (j + 1)) := by
          rw [Finset.prod_pow_eq_pow_sum]
      _ = (2 * L) ^ (c * killPoolSize k r) := by
          rw [killPoolSize, Finset.mul_sum]
  calc jointB c k r q p = q * killCore c k r p := rfl
    _ ≤ (2 * L) * (2 * L) ^ (c * killPoolSize k r) := Nat.mul_le_mul (by omega) hcore
    _ = (2 * L) ^ (1 + c * killPoolSize k r) := by rw [pow_add, pow_one]

/-- `R > L`: the CRT residue at the (always killed, because `r ≥ 1`) slot `j = 0` forces
`R % P₀^c = P₀^(c-1) ≥ P₀ > L`. -/
lemma lt_crt_solution {c k r L R : ℕ} {p : ℕ → ℕ → ℕ} (hc : 2 ≤ c) (hr : 1 ≤ r) (hrk : r < k)
    (hp0 : 2 ≤ p 0 0) (hpL : L < p 0 0)
    (hres : ∀ j, j < k → j ≠ r → R + j ≡ slotProd p j ^ (c - 1) [MOD slotProd p j ^ c]) :
    L < R := by
  have h0 : slotProd p 0 = p 0 0 := by simp [slotProd]
  have h := hres 0 (by omega) (by omega)
  rw [Nat.add_zero, h0] at h
  have hlt : p 0 0 ^ (c - 1) < p 0 0 ^ c := Nat.pow_lt_pow_right (by omega) (by omega)
  have hmod : R % (p 0 0 ^ c) = p 0 0 ^ (c - 1) := by
    rw [Nat.ModEq] at h
    rw [h, Nat.mod_eq_of_lt hlt]
  have hle : p 0 0 ^ (c - 1) ≤ R := by
    rw [← hmod]; exact Nat.mod_le _ _
  have hge : p 0 0 ≤ p 0 0 ^ (c - 1) := by
    calc p 0 0 = p 0 0 ^ 1 := (pow_one _).symm
      _ ≤ p 0 0 ^ (c - 1) := Nat.pow_le_pow_right (by omega) (by omega)
  omega

/-- The **candidate injection**: every prime `z ≤ X` in the class `u mod B` is `u + mB` for
the single index `m = z / B < X/B + 1`.  Hence the AGP count is a lower bound for the number
of candidate indices. -/
lemma card_agp_le_card_candidates {B u X : ℕ} (hB : 1 ≤ B) (huB : u < B) :
    ((range (X + 1)).filter (fun z => z.Prime ∧ z % B = u % B)).card ≤
      ((range (X / B + 1)).filter
        (fun m => (u + m * B).Prime ∧ u + m * B ≤ X)).card := by
  classical
  have key : ∀ z ∈ (range (X + 1)).filter (fun z => z.Prime ∧ z % B = u % B),
      u + (z / B) * B = z := by
    intro z hz
    obtain ⟨-, -, hmod⟩ := by
      simpa only [Finset.mem_filter, Finset.mem_range, and_assoc] using hz
    have : z % B = u := by rw [hmod, Nat.mod_eq_of_lt huB]
    have hd : B * (z / B) + z % B = z := Nat.div_add_mod z B
    have hcm : (z / B) * B = B * (z / B) := Nat.mul_comm _ _
    omega
  refine Finset.card_le_card_of_injOn (fun z => z / B) ?_ ?_
  · intro z hz
    have hzX : z ≤ X := by
      have := (Finset.mem_filter.mp hz).1
      simpa using Nat.lt_succ_iff.mp (Finset.mem_range.mp this)
    obtain ⟨hp, -⟩ := (Finset.mem_filter.mp hz).2
    refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ?_, ?_, ?_⟩
    · show z / B < X / B + 1
      have : z / B ≤ X / B := Nat.div_le_div_right hzX
      omega
    · rw [key z hz]; exact hp
    · rw [key z hz]; exact hzX
  · intro z hz z' hz' heq
    have h1 := key z (by simpa using hz)
    have h2 := key z' (by simpa using hz')
    simp only at heq
    rw [← h1, ← h2, heq]

/-! ### The two real-analytic reductions -/

/-- Core real inequality behind the candidate count: with `l = log 2 ≤ 1` and `t = X/B ≥ 1`,
`(t+1)/(16 K) ≤ t/(8 K l)`.  Only `l ≤ 1` is used, so no numeric bound on `log 2` is
needed. -/
private lemma count_real_core {t l K : ℝ} (ht : 1 ≤ t) (hl0 : 0 < l) (hl : l ≤ 1)
    (hK : 0 < K) : (t + 1) / (16 * K) ≤ t / (8 * K * l) := by
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have hcore : l * (t + 1) ≤ 2 * t := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_left hcore (by positivity : (0:ℝ) ≤ 8 * K)]

/-- **The pool supply reduction.**  From `PrimeIntervalSupply` at `L = 2^k` and the schedule
inequality `3k(1 + k² + D₀) ≤ 2^k`, the open interval `(2^k, 2^(k+1))` contains at least
`1 + killPoolSize k r + D₀` primes — enough to lose one prime per exceptional modulus and
still allocate `q` and the whole killed-slot family. -/
lemma pool_card_ge {k r D0 N : ℕ} (hk : 1 ≤ k)
    (hpool : 3 * k * (1 + k ^ 2 + D0) ≤ 2 ^ k)
    (hcard : ((2 ^ k : ℕ) : ℝ) / (3 * Real.log ((2 ^ k : ℕ) : ℝ)) ≤ (N : ℝ)) :
    1 + killPoolSize k r + D0 ≤ N := by
  have hl0 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hl1 : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (x := (2 : ℝ)) (by norm_num)
    linarith
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hlog : Real.log ((2 : ℝ) ^ k) = (k : ℝ) * Real.log 2 := by rw [Real.log_pow]
  push_cast at hcard
  rw [hlog] at hcard
  have hden : (0 : ℝ) < 3 * ((k : ℝ) * Real.log 2) := by positivity
  -- `3 log L ≤ 3k`, so `L/(3k) ≤ L/(3 log L) ≤ N`
  have h1 : ((2 : ℝ) ^ k) / (3 * (k : ℝ)) ≤ (N : ℝ) := by
    refine le_trans (div_le_div_of_nonneg_left (by positivity) hden ?_) hcard
    nlinarith
  -- the schedule inequality gives `1 + k² + D₀ ≤ L/(3k)`
  have h2 : ((1 + k ^ 2 + D0 : ℕ) : ℝ) ≤ ((2 : ℝ) ^ k) / (3 * (k : ℝ)) := by
    rw [le_div_iff₀ (by positivity)]
    have hcast : ((3 * k * (1 + k ^ 2 + D0) : ℕ) : ℝ) ≤ (((2 : ℕ) ^ k : ℕ) : ℝ) := by
      exact_mod_cast hpool
    push_cast at hcast ⊢
    nlinarith
  have h4 : 1 + k ^ 2 + D0 ≤ N := by exact_mod_cast le_trans h2 h1
  have := killPoolSize_le_sq k r
  omega

/-- **The candidate-count reduction.**  From the AGP lower bound on the number of primes
`≤ X` in the class `u mod B`, with `X = 2^(4k⁴)`, `1 ≤ B ≤ X`, the count is at least
`M / (16 k⁴)` where `M = X/B + 1`.  The slack is genuine: `log X = 4k⁴ log 2` and
`2/log 2 > 2`, which absorbs the `+1` in `M`. -/
lemma count_lower_bound {B X k N : ℕ} (hk : 1 ≤ k) (hB : 1 ≤ B) (hBX : B ≤ X)
    (hX : X = 2 ^ (4 * k ^ 4))
    (hN : (X : ℝ) / (2 * B.totient * Real.log X) ≤ (N : ℝ)) :
    ((X / B + 1 : ℕ) : ℝ) / (16 * (k : ℝ) ^ 4) ≤ (N : ℝ) := by
  have hl0 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hl1 : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (x := (2 : ℝ)) (by norm_num)
    linarith
  have hkR : (0 : ℝ) < (k : ℝ) ^ 4 := by
    have : (0 : ℝ) < k := by exact_mod_cast hk
    positivity
  have hBR : (0 : ℝ) < B := by exact_mod_cast hB
  have hXR : (0 : ℝ) < X := by
    have : 0 < X := by omega
    exact_mod_cast this
  have hlogX : Real.log X = 4 * (k : ℝ) ^ 4 * Real.log 2 := by
    subst hX
    push_cast
    rw [Real.log_pow]
    push_cast
    ring
  have hlogXpos : 0 < Real.log X := by rw [hlogX]; positivity
  have hphi0 : (0 : ℝ) < B.totient := by
    have : 0 < B.totient := Nat.totient_pos.mpr (by omega)
    exact_mod_cast this
  have hphiB : ((B.totient : ℕ) : ℝ) ≤ (B : ℝ) := by exact_mod_cast Nat.totient_le B
  -- drop `φ(B)` to `B`
  have step1 : (X : ℝ) / (2 * (B : ℝ) * Real.log X) ≤ (N : ℝ) := by
    refine le_trans ?_ hN
    gcongr
  have ht : 1 ≤ (X : ℝ) / (B : ℝ) := (one_le_div hBR).mpr (by exact_mod_cast hBX)
  have heq : (X : ℝ) / (2 * (B : ℝ) * Real.log X)
      = ((X : ℝ) / (B : ℝ)) / (8 * (k : ℝ) ^ 4 * Real.log 2) := by
    rw [hlogX]
    field_simp
    ring
  have hmain : (((X : ℝ) / (B : ℝ)) + 1) / (16 * (k : ℝ) ^ 4)
      ≤ (X : ℝ) / (2 * (B : ℝ) * Real.log X) := by
    rw [heq]
    exact count_real_core ht hl0 hl1 hkR
  have hle : ((X / B + 1 : ℕ) : ℝ) ≤ ((X : ℝ) / (B : ℝ)) + 1 := by
    have := Nat.cast_div_le (α := ℝ) (m := X) (n := B)
    push_cast
    linarith
  calc ((X / B + 1 : ℕ) : ℝ) / (16 * (k : ℝ) ^ 4)
      ≤ (((X : ℝ) / (B : ℝ)) + 1) / (16 * (k : ℝ) ^ 4) := by gcongr
    _ ≤ (X : ℝ) / (2 * (B : ℝ) * Real.log X) := hmain
    _ ≤ (N : ℝ) := step1

/-! ### The dyadic schedule: `L = 2^k`, `U = 2^(k⁴)`, `X = U⁴` -/

/-- `log X = 4k⁴ log 2` for `X = 2^(4k⁴)`. -/
private lemma log_X_eq (k : ℕ) :
    Real.log ((2 ^ (4 * k ^ 4) : ℕ) : ℝ) = 4 * (k : ℝ) ^ 4 * Real.log 2 := by
  push_cast
  rw [Real.log_pow]
  push_cast
  ring

/-- `log X ≥ 2`, so every exceptional modulus (which exceeds `log X`) is `≥ 2`, in particular
`≠ 1` and `≠ 0`. -/
private lemma two_le_log_X {k : ℕ} (hk : 1 ≤ k) :
    2 ≤ Real.log ((2 ^ (4 * k ^ 4) : ℕ) : ℝ) := by
  rw [log_X_eq]
  have hl := Real.log_two_gt_d9
  have h1 : (1 : ℝ) ≤ (k : ℝ) ^ 4 := by
    have h : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    exact one_le_pow₀ h
  nlinarith

/-- `X^(1/4) = U` exactly, for `X = U⁴ = 2^(4k⁴)` and `U = 2^(k⁴)`.  This is why the schedule
uses `X = U⁴`: the AGP hypothesis `B ≤ X^(1/4)` becomes the clean `B ≤ U`. -/
private lemma rpow_quarter_X (k : ℕ) :
    ((2 ^ (4 * k ^ 4) : ℕ) : ℝ) ^ ((1 : ℝ) / 4) = ((2 ^ (k ^ 4) : ℕ) : ℝ) := by
  have hy : (0 : ℝ) ≤ (2 : ℝ) ^ (k ^ 4) := by positivity
  have h1 : ((2 ^ (4 * k ^ 4) : ℕ) : ℝ) = ((2 : ℝ) ^ (k ^ 4)) ^ (4 : ℕ) := by
    push_cast
    rw [← pow_mul]
    ring_nf
  rw [h1, ← Real.rpow_natCast ((2 : ℝ) ^ (k ^ 4)) 4, ← Real.rpow_mul hy]
  push_cast
  norm_num

/-- **The target.**  Prime selection feeding `exists_joint_progression`, with a quantitative
prime-candidate count.  Both analytic inputs are hypotheses.

For any fixed `c ≥ 2`, `a ≥ 2`, `r ≥ 1` and any requested cutoff `K`, there are `k ≥ K` with
`r < k` and, with the dyadic schedule `L = 2^k`, `U = 2^(k⁴)`, `X = U⁴ = 2^(4k⁴)`:

* primes `q` and `p j t` (`j < k`, `j ≠ r`, `t < j+1`) all lying in the open interval
  `(L, 2L)`, pairwise distinct, and avoiding every AGP exceptional modulus in `B`;
* the **complete** `exists_joint_progression` conclusion for them — `0 < R < A`,
  `1 ≤ u < B`, `R + r = Qu`, `A = QB`, `u ≡ 1 [MOD q]`, `(u,B) = 1`, the exact CRT residues,
  `c^(j+1) ∣ τ(R + mA + j)` at every killed slot for every `m`, the survivor value
  `τ(R + mA + r) = 2a` whenever `u + mB` is prime, and `(R + j, A) = 1` on the free tail;
* the size bookkeeping `Q ≤ (2L)^(a-1)`, `B ≤ (2L)^(1 + c·killPoolSize k r)`, `B ≤ U`,
  `Q ≤ U`, and `R > L`;
* at least `M / (16 k⁴)` candidate indices `m < M`, where `M = X/B + 1`, with `u + mB`
  prime and `u + mB ≤ X` — a genuine real inequality.

`K` is arbitrary, so later tail and digit margins may demand `k` as large as they like. -/
theorem exists_joint_prime_candidates (hagp : AGP) (hpis : PrimeIntervalSupply)
    {c a r : ℕ} (hc : 2 ≤ c) (ha : 2 ≤ a) (hr : 1 ≤ r) (K : ℕ) :
    ∃ (k q : ℕ) (p : ℕ → ℕ → ℕ) (R u : ℕ),
      K ≤ k ∧ r < k ∧
      2 ^ k < q ∧ q < 2 * 2 ^ k ∧ q.Prime ∧
      (∀ j t, j < k → j ≠ r → t < j + 1 →
        (p j t).Prime ∧ 2 ^ k < p j t ∧ p j t < 2 * 2 ^ k) ∧
      -- the complete `exists_joint_progression` contract
      0 < R ∧ R < jointA c a k r q p ∧ 1 ≤ u ∧ u < jointB c k r q p ∧
      R + r = jointQ a q * u ∧
      jointA c a k r q p = jointQ a q * jointB c k r q p ∧
      u ≡ 1 [MOD q] ∧ Nat.Coprime u (jointB c k r q p) ∧
      R + r ≡ jointQ a q [MOD q ^ a] ∧
      (∀ j, j < k → j ≠ r → R + j ≡ slotProd p j ^ (c - 1) [MOD slotProd p j ^ c]) ∧
      (∀ m j, j < k → j ≠ r →
        c ^ (j + 1) ∣ NormalNumbers.SwingC2.tau (R + m * jointA c a k r q p + j)) ∧
      (∀ m, (u + m * jointB c k r q p).Prime →
        NormalNumbers.SwingC2.tau (R + m * jointA c a k r q p + r) = 2 * a) ∧
      (∀ j, k ≤ j → j < 2 ^ k → Nat.Coprime (R + j) (jointA c a k r q p)) ∧
      -- explicit size bookkeeping
      jointQ a q ≤ (2 * 2 ^ k) ^ (a - 1) ∧
      jointB c k r q p ≤ (2 * 2 ^ k) ^ (1 + c * killPoolSize k r) ∧
      jointB c k r q p ≤ 2 ^ (k ^ 4) ∧ jointQ a q ≤ 2 ^ (k ^ 4) ∧ 2 ^ k < R ∧
      -- the quantitative prime-candidate count
      ((2 ^ (4 * k ^ 4) / jointB c k r q p + 1 : ℕ) : ℝ) / (16 * k ^ 4) ≤
        (((range (2 ^ (4 * k ^ 4) / jointB c k r q p + 1)).filter
          (fun m => (u + m * jointB c k r q p).Prime ∧
            u + m * jointB c k r q p ≤ 2 ^ (4 * k ^ 4))).card : ℝ) := by
  classical
  obtain ⟨X0, D0, hAGP⟩ := hagp
  obtain ⟨L0, hPIS⟩ := hpis
  obtain ⟨k, hkK, hkr, hk16, hL0, hX0, hpool, hschedB, hschedQ⟩ :=
    exists_selection_scale K r c a D0 X0 L0
  have hk1 : 1 ≤ k := by omega
  have hL2 : 2 ≤ 2 ^ k := by
    calc (2 : ℕ) = 2 ^ 1 := rfl
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk1
  have hkL : k ≤ 2 ^ k := Nat.lt_two_pow_self.le
  -- ### the exceptional set, fixed before any modulus
  obtain ⟨Dset, hDcard, hDlog, hAGPcount⟩ := hAGP _ hX0
  have hD2 : ∀ D ∈ Dset, 2 ≤ D := by
    intro D hD
    have h1 := hDlog D hD
    have h2 := two_le_log_X (k := k) hk1
    have : (2 : ℝ) < (D : ℝ) := lt_of_le_of_lt h2 h1
    have : (2 : ℕ) < D := by exact_mod_cast this
    omega
  -- ### the prime pool in the open dyadic interval
  have hpisL := hPIS (2 ^ k) hL0 hL2
  have hScard : 1 + killPoolSize k r + Dset.card ≤
      (((Ioo (2 ^ k) (2 * 2 ^ k)).filter Nat.Prime).card) := by
    have := pool_card_ge (r := r) (D0 := D0) hk1 hpool hpisL
    omega
  obtain ⟨q, p, hqS, hpS, hpqne, hpinj, havoid⟩ :=
    exists_prime_allocation c k r ((Ioo (2 ^ k) (2 * 2 ^ k)).filter Nat.Prime) Dset
      (fun π hπ => (Finset.mem_filter.mp hπ).2) hScard
  have hqdata : q.Prime ∧ 2 ^ k < q ∧ q < 2 * 2 ^ k := by
    obtain ⟨hmem, hpr⟩ := Finset.mem_filter.mp hqS
    obtain ⟨h1, h2⟩ := Finset.mem_Ioo.mp hmem
    exact ⟨hpr, h1, h2⟩
  have hpdata : ∀ j t, j ∈ killedIdx k r → t < j + 1 →
      (p j t).Prime ∧ 2 ^ k < p j t ∧ p j t < 2 * 2 ^ k := by
    intro j t hj ht
    obtain ⟨hmem, hpr⟩ := Finset.mem_filter.mp (hpS j t hj ht)
    obtain ⟨h1, h2⟩ := Finset.mem_Ioo.mp hmem
    exact ⟨hpr, h1, h2⟩
  -- ### instantiate the §4 arithmetic theorem
  have hqr : r < jointQ a q := by
    have h1 : q ^ 1 ≤ q ^ (a - 1) := Nat.pow_le_pow_right hqdata.1.pos (by omega)
    rw [pow_one] at h1
    simp only [jointQ]
    omega
  obtain ⟨R, u, hR0, hRA, hu1, huB, hRr, hAQB, humod, hcopuB, hres_r, hres_j, hkill,
      hsurv, htail⟩ :=
    exists_joint_progression (L := 2 ^ k) (p := p) hc ha hr hkr hkL hqdata.1 hqdata.2.1 hqr
      (fun j t hjk hjr ht => (hpdata j t (mem_killedIdx.mpr ⟨hjr, hjk⟩) ht).1)
      (fun j t hjk hjr ht => (hpdata j t (mem_killedIdx.mpr ⟨hjr, hjk⟩) ht).2.1)
      (fun j t hjk hjr ht => hpqne j t (mem_killedIdx.mpr ⟨hjr, hjk⟩) ht)
      (fun j t j' t' hjk hjr ht hj'k hj'r ht' he =>
        hpinj j t j' t' (mem_killedIdx.mpr ⟨hjr, hjk⟩) ht (mem_killedIdx.mpr ⟨hj'r, hj'k⟩) ht' he)
  -- ### size bookkeeping
  have htwo : 2 * 2 ^ k = 2 ^ (k + 1) := by rw [pow_succ]; ring
  have hQle : jointQ a q ≤ (2 * 2 ^ k) ^ (a - 1) := jointQ_le hqdata.2.2
  have hBle : jointB c k r q p ≤ (2 * 2 ^ k) ^ (1 + c * killPoolSize k r) :=
    jointB_le hqdata.2.2 fun j t hj ht => (hpdata j t hj ht).2.2
  have hQU : jointQ a q ≤ 2 ^ (k ^ 4) := by
    refine hQle.trans ?_
    rw [htwo, ← pow_mul]
    exact Nat.pow_le_pow_right (by norm_num) hschedQ
  have hBU : jointB c k r q p ≤ 2 ^ (k ^ 4) := by
    refine hBle.trans ?_
    rw [htwo, ← pow_mul]
    refine Nat.pow_le_pow_right (by norm_num) (le_trans ?_ hschedB)
    exact Nat.mul_le_mul le_rfl
      (Nat.add_le_add_left (Nat.mul_le_mul le_rfl (killPoolSize_le_sq k r)) 1)
  have hRL : 2 ^ k < R := by
    have h0 : (0 : ℕ) ∈ killedIdx k r := mem_killedIdx.mpr ⟨by omega, by omega⟩
    have hd := hpdata 0 0 h0 (by omega)
    exact lt_crt_solution hc hr hkr hd.1.two_le hd.2.1 hres_j
  -- ### the AGP count
  have hB1 : 1 ≤ jointB c k r q p := by omega
  have hBX : jointB c k r q p ≤ 2 ^ (4 * k ^ 4) := by
    refine hBU.trans (Nat.pow_le_pow_right (by norm_num) ?_)
    nlinarith [Nat.one_le_iff_ne_zero.mpr (show k ^ 4 ≠ 0 by positivity)]
  have hBrpow : (jointB c k r q p : ℝ) ≤ ((2 ^ (4 * k ^ 4) : ℕ) : ℝ) ^ ((1 : ℝ) / 4) := by
    rw [rpow_quarter_X]
    exact_mod_cast hBU
  have hnoD : ∀ D ∈ Dset, ¬ D ∣ jointB c k r q p := fun D hD =>
    havoid D hD (by have := hD2 D hD; omega)
  have hcount := hAGPcount (jointB c k r q p) u hB1 hBrpow hcopuB hnoD
  have hinj := card_agp_le_card_candidates (B := jointB c k r q p) (u := u)
    (X := 2 ^ (4 * k ^ 4)) hB1 huB
  have hfinal := count_lower_bound (B := jointB c k r q p) (X := 2 ^ (4 * k ^ 4)) (k := k)
    (N := ((range (2 ^ (4 * k ^ 4) + 1)).filter
      (fun z => z.Prime ∧ z % jointB c k r q p = u % jointB c k r q p)).card)
    hk1 hB1 hBX rfl hcount
  refine ⟨k, q, p, R, u, hkK, hkr, hqdata.2.1, hqdata.2.2, hqdata.1, ?_, hR0, hRA, hu1, huB,
    hRr, hAQB, humod, hcopuB, hres_r, hres_j, hkill, hsurv, htail, hQle, hBle, hBU, hQU, hRL,
    le_trans hfinal (by exact_mod_cast hinj)⟩
  intro j t hjk hjr ht
  exact hpdata j t (mem_killedIdx.mpr ⟨hjr, hjk⟩) ht

end NormalNumbers.JointLambert
