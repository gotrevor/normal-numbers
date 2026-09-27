/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import NormalNumbers.JointLambertArithmetic

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

/-- The target of this file, with its analytic inputs as hypotheses.  See the module
docstring.  TEMPORARY `sorry`: the statement is fixed first so that partial scaffolding
cannot be mistaken for success. -/
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
  sorry

end NormalNumbers.JointLambert
