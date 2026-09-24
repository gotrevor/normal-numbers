/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.SwingC3Mean

/-!
# Total variation replaces the period

The master inequality of `SwingC3Mean` prices the truncated tail by its **period**
`∏_{P<p≤K} p ≈ e^K`, which forces `K ≲ log N`.  That factor comes from the trivial stub bound
`‖∑_{n<N} g‖ ≤ L` for an `L`-periodic unimodular `g` with vanishing complete sum, and lap 15
named "a sub-trivial bound on that incomplete sum" as the only structurally untried handle.

This file supplies one.  The point is that the truncated summand is not an arbitrary periodic
function: it is a **product of one-prime factors, each of which is close to `1` on most residues**.
Writing `g_p = 1 + (g_p − 1)` and expanding, the whole sum is controlled by the *total variations*

    V_p = ∑_{r<p} ‖g_p(r) − 1‖,

and each prime costs a factor `(1 + V_p)` instead of a factor `p`:

    ‖∑_{n<N} e(jn/Q) ∏_{p∈F} g_p(n)‖ ≤ Q · ∏_{p∈F} (1 + V_p),     uniformly in `N`.

For the crux's summand `g_p(n) = e(h · tailPrimeTerm b p n)` the variation is bounded by the
**exact** complete-period mass of `SwingC3Mean.sum_range_tailPrimeTerm_period`:

    V_p ≤ 16|h| · ∑_{r<p} tailPrimeTerm b p r = 16|h|/(b−1),      a constant, uniform in `p`.

So the period `∏_{P<p≤K} p` in the master inequality may be replaced by
`(1 + 16|h|/(b−1))^{π(K)−π(P)}` — exponential in `π(K) ≈ K/log K` rather than in `K`.  That is a
strict improvement for every prime `p > 16|h|/(b−1)`, and it widens the usable truncation window
from `K ≲ log N` to `K ≲ log N · loglog N`.

It does **not** close the crux: the discarded mass still needs `K ≳ N` (see
`SwingC3Mean.sum_range_tailTrunc_sub_le`), and `loglog N − loglog(log N loglog N) ≍ loglog N`
is unchanged.  The value of the bound is that it is the first improvement of the period term,
and that it isolates the real obstruction: the method is limited by the *total variation*
`V_p ≍ 1`, whereas the *mean* `V_p/p ≍ 1/(b−1)p` is what would make `∏(1+V_p/p) ≍ (log K)^c`
harmless.  The gap between those two is exactly "no cancellation inside an incomplete period".

## The proof

Induction on `F`, peeling one prime `q` at a time, and carrying an arbitrary congruence condition
`n ≡ a [MOD m]` with `m` coprime to `Q` and to the remaining primes:

* base (`F = ∅`): `‖∑_{n<N, n≡a [m]} e(jn/Q)‖ ≤ Q` — the indicator of an AP is `m`-periodic, so the
  complete sum over `m·Q` vanishes by `sum_addChar_mul_periodic_eq_zero`, and the stub carries
  exactly `Q` nonzero terms (`Nat.count_modEq_card`);
* step: `g_q = 1 + (g_q − 1)`; the `1` reproduces the statement for `F \ {q}`, and the second part
  is split by `n % q = r`, which by CRT (`Nat.chineseRemainder`) refines the congruence to
  modulus `m·q` — so the induction hypothesis applies to each fibre and the total cost is
  `∑_{r<q} ‖g_q(r) − 1‖ = V_q`.
-/

open Finset

namespace NormalNumbers

/-! ### A stub bound that sees the summand's size -/

/-- **A sharper stub bound.**  For an `L`-periodic summand with vanishing complete sum, the
incomplete sum is bounded by the `ℓ¹` norm over one period — not by `L · sup‖g‖`. -/
theorem norm_sum_range_le_sum_norm_period {L : ℕ} (hL : 0 < L) (g : ℕ → ℂ)
    (hg : ∀ n, g (n + L) = g n) (hzero : ∑ m ∈ range L, g m = 0) (N : ℕ) :
    ‖∑ n ∈ range N, g n‖ ≤ ∑ m ∈ range L, ‖g m‖ := by
  rw [sum_range_eq_sum_mod hL g hg hzero N]
  refine (norm_sum_le _ _).trans ?_
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun i _ _ => norm_nonneg _)
  intro x hx
  exact mem_range.2 (lt_of_lt_of_le (mem_range.1 hx) (Nat.mod_lt N hL).le)

/-- A periodic function only sees the residue. -/
theorem periodic_eq_mod {α : Type*} {p : ℕ} (f : ℕ → α)
    (hf : ∀ n, f (n + p) = f n) (n : ℕ) : f n = f (n % p) := by
  have key : ∀ k r : ℕ, f (r + p * k) = f r := by
    intro k
    induction k with
    | zero => intro r; simp
    | succ k ih =>
        intro r
        have h : r + p * (k + 1) = (r + p * k) + p := by ring
        rw [h, hf, ih]
  have h := key (n / p) (n % p)
  rwa [Nat.mod_add_div] at h

/-! ### The base case: a nontrivial character over an arithmetic progression -/

/-- **The character sum over an AP is bounded by `Q`, uniformly in the modulus.**  This is the
engine: however fine the progression `n ≡ a [MOD m]`, the twisting character mod `Q` still
cancels, and the leftover is at most `Q` terms. -/
theorem norm_sum_addChar_ap_le {Q j : ℕ} (hQ : 0 < Q) (hj0 : 0 < j) (hjQ : j < Q)
    {m : ℕ} (hm : 0 < m) (hcop : Nat.Coprime m Q) (a N : ℕ) :
    ‖∑ n ∈ (range N).filter (fun n => n ≡ a [MOD m]),
        ee (((j : ℝ) * n / Q : ℝ) : ℂ)‖ ≤ (Q : ℝ) := by
  classical
  set f : ℕ → ℂ := fun n => if n ≡ a [MOD m] then 1 else 0 with hf
  set g : ℕ → ℂ := fun n => ee (((j : ℝ) * n / Q : ℝ) : ℂ) * f n with hgdef
  have hfper : ∀ n, f (n + m) = f n := by
    intro n
    have : (n + m ≡ a [MOD m]) ↔ (n ≡ a [MOD m]) := by
      constructor
      · intro h; exact (Nat.add_modEq_right).symm.trans h
      · intro h; exact (Nat.add_modEq_right).trans h
    simp only [hf]
    by_cases hc : n ≡ a [MOD m]
    · rw [if_pos (this.2 hc), if_pos hc]
    · rw [if_neg (fun hcc => hc (this.1 hcc)), if_neg hc]
  have hsum : ∑ n ∈ (range N).filter (fun n => n ≡ a [MOD m]),
      ee (((j : ℝ) * n / Q : ℝ) : ℂ) = ∑ n ∈ range N, g n := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun n _ => ?_
    simp only [hgdef, hf]
    by_cases hc : n ≡ a [MOD m] <;> simp [hc]
  rw [hsum]
  -- periodicity of `g` with period `m * Q`
  have hgper : ∀ n, g (n + m * Q) = g n := by
    intro n
    have h1 : f (n + m * Q) = f n := by
      have : ∀ t : ℕ, f (n + m * t) = f n := by
        intro t
        induction t with
        | zero => simp
        | succ t ih =>
            have h : n + m * (t + 1) = (n + m * t) + m := by ring
            rw [h, hfper, ih]
      exact this Q
    have h2 : ee (((j : ℝ) * ((n + m * Q : ℕ) : ℝ) / Q : ℝ) : ℂ)
        = ee (((j : ℝ) * n / Q : ℝ) : ℂ) := by
      have hQR : (Q : ℝ) ≠ 0 := by positivity
      have hreal : ((j : ℝ) * ((n + m * Q : ℕ) : ℝ) / Q : ℝ)
          = ((j : ℝ) * n / Q : ℝ) + ((((j * m : ℕ) : ℤ) : ℝ)) := by
        push_cast
        field_simp
      rw [hreal, Complex.ofReal_add, Complex.ofReal_intCast, ee_add, ee_int, mul_one]
    simp only [hgdef]
    rw [h1, h2]
  have hzero : ∑ n ∈ range (m * Q), g n = 0 :=
    sum_addChar_mul_periodic_eq_zero hm hQ hcop hj0 hjQ f hfper
  have hmain := norm_sum_range_le_sum_norm_period (Nat.mul_pos hm hQ) g hgper hzero N
  refine hmain.trans (le_of_eq ?_)
  have hnorm : ∀ n, ‖g n‖ = if n ≡ a [MOD m] then (1 : ℝ) else 0 := by
    intro n
    simp only [hgdef, hf, norm_mul, norm_ee_real, one_mul]
    by_cases hc : n ≡ a [MOD m] <;> simp [hc]
  rw [Finset.sum_congr rfl (fun n _ => hnorm n), Finset.sum_boole]
  have hcard : ((range (m * Q)).filter (fun n => n ≡ a [MOD m])).card = Q := by
    have := Nat.count_modEq_card (b := m * Q) (r := m) hm a
    rw [Nat.count_eq_card_filter_range] at this
    simp only [Nat.mul_mod_right, Nat.not_lt_zero, if_false, Nat.mul_div_cancel_left _ hm] at this
    simpa using this
  rw [hcard]

/-! ### The variation bound -/

/-- **Total variation replaces the period.**  Let `g_p` be `p`-periodic for each `p` in a finite
set `F` of pairwise coprime moduli, each coprime to `Q`, and let `V_p` bound the total variation
`∑_{r<p} ‖g_p(r) − 1‖`.  Then, for every `N` and every ambient progression `n ≡ a [MOD m]` with
`m` coprime to `Q` and to every `p ∈ F`,

    ‖∑_{n<N, n≡a [m]} e(jn/Q) ∏_{p∈F} g_p(n)‖ ≤ Q · ∏_{p∈F} (1 + V_p).

The bound does not involve `N`, and — crucially — it does not involve the period `∏_{p∈F} p`. -/
theorem norm_sum_addChar_prod_le {Q j : ℕ} (hQ : 0 < Q) (hj0 : 0 < j) (hjQ : j < Q)
    (g : ℕ → ℕ → ℂ) (V : ℕ → ℝ) :
    ∀ F : Finset ℕ, (∀ p ∈ F, 0 < p) → (∀ p ∈ F, ∀ n, g p (n + p) = g p n) →
      (∀ p ∈ F, ∑ r ∈ range p, ‖g p r - 1‖ ≤ V p) →
      (∀ p ∈ F, Nat.Coprime p Q) → ((F : Set ℕ).Pairwise Nat.Coprime) →
      ∀ m a N : ℕ, 0 < m → Nat.Coprime m Q → (∀ p ∈ F, Nat.Coprime p m) →
      ‖∑ n ∈ (range N).filter (fun n => n ≡ a [MOD m]),
          ee (((j : ℝ) * n / Q : ℝ) : ℂ) * ∏ p ∈ F, g p n‖ ≤ (Q : ℝ) * ∏ p ∈ F, (1 + V p) := by
  classical
  intro F
  induction F using Finset.induction_on with
  | empty =>
      intro _ _ _ _ _ m a N hm hmQ _
      simpa using norm_sum_addChar_ap_le hQ hj0 hjQ hm hmQ a N
  | @insert q s hq ih =>
      intro hpos hper hV hcopQ hpair m a N hm hmQ hcopm
      have hqmem : q ∈ insert q s := Finset.mem_insert_self q s
      have hsmem : ∀ p, p ∈ s → p ∈ insert q s := fun p hp => Finset.mem_insert_of_mem hp
      have hqpos : 0 < q := hpos q hqmem
      have hVnn : ∀ p, p ∈ insert q s → 0 ≤ V p := fun p hp =>
        le_trans (Finset.sum_nonneg fun r _ => norm_nonneg _) (hV p hp)
      have hprodnn : (0 : ℝ) ≤ ∏ p ∈ s, (1 + V p) :=
        Finset.prod_nonneg fun p hp => by linarith [hVnn p (hsmem p hp)]
      -- the induction hypothesis, over an arbitrary progression
      have ihs : ∀ m' a' : ℕ, 0 < m' → Nat.Coprime m' Q → (∀ p ∈ s, Nat.Coprime p m') →
          ‖∑ n ∈ (range N).filter (fun n => n ≡ a' [MOD m']),
              ee (((j : ℝ) * n / Q : ℝ) : ℂ) * ∏ p ∈ s, g p n‖
            ≤ (Q : ℝ) * ∏ p ∈ s, (1 + V p) := by
        intro m' a' hm' hm'Q hcop'
        exact ih (fun p hp => hpos p (hsmem p hp)) (fun p hp => hper p (hsmem p hp))
          (fun p hp => hV p (hsmem p hp)) (fun p hp => hcopQ p (hsmem p hp))
          (hpair.mono (by intro x hx; exact hsmem x hx)) m' a' N hm' hm'Q hcop'
      -- split `g q = 1 + (g q - 1)`
      have hsplit : ∀ n : ℕ, ee (((j : ℝ) * n / Q : ℝ) : ℂ) * ∏ p ∈ insert q s, g p n
          = ee (((j : ℝ) * n / Q : ℝ) : ℂ) * ∏ p ∈ s, g p n
            + (g q n - 1) * (ee (((j : ℝ) * n / Q : ℝ) : ℂ) * ∏ p ∈ s, g p n) := by
        intro n
        rw [Finset.prod_insert hq]
        ring
      rw [Finset.sum_congr rfl (fun n _ => hsplit n), Finset.sum_add_distrib]
      refine (norm_add_le _ _).trans ?_
      have hfirst := ihs m a hm hmQ (fun p hp => hcopm p (hsmem p hp))
      -- the second piece: split by the residue mod `q`
      have hsecond : ‖∑ n ∈ (range N).filter (fun n => n ≡ a [MOD m]),
          (g q n - 1) * (ee (((j : ℝ) * n / Q : ℝ) : ℂ) * ∏ p ∈ s, g p n)‖
          ≤ V q * ((Q : ℝ) * ∏ p ∈ s, (1 + V p)) := by
        have hmq : Nat.Coprime m q := (hcopm q hqmem).symm
        have hfib := Finset.sum_fiberwise_of_maps_to
          (s := (range N).filter (fun n => n ≡ a [MOD m])) (t := range q)
          (g := fun n => n % q)
          (f := fun n => (g q n - 1) * (ee (((j : ℝ) * n / Q : ℝ) : ℂ) * ∏ p ∈ s, g p n))
          (fun x _ => Finset.mem_range.2 (Nat.mod_lt x hqpos))
        rw [← hfib]
        refine (norm_sum_le _ _).trans ?_
        have hterm : ∀ r ∈ range q,
            ‖∑ n ∈ ((range N).filter (fun n => n ≡ a [MOD m])).filter (fun n => n % q = r),
              (g q n - 1) * (ee (((j : ℝ) * n / Q : ℝ) : ℂ) * ∏ p ∈ s, g p n)‖
              ≤ ‖g q r - 1‖ * ((Q : ℝ) * ∏ p ∈ s, (1 + V p)) := by
          intro r hr
          have hrq : r < q := Finset.mem_range.1 hr
          obtain ⟨c, hca, hcr⟩ : ∃ c : ℕ, c ≡ a [MOD m] ∧ c ≡ r [MOD q] :=
            ⟨(Nat.chineseRemainder hmq a r : ℕ), (Nat.chineseRemainder hmq a r).2.1,
              (Nat.chineseRemainder hmq a r).2.2⟩
          have hset : ((range N).filter (fun n => n ≡ a [MOD m])).filter (fun n => n % q = r)
              = (range N).filter (fun n => n ≡ c [MOD m * q]) := by
            rw [Finset.filter_filter]
            refine Finset.filter_congr ?_
            intro n _
            constructor
            · rintro ⟨h1, h2⟩
              refine (Nat.modEq_and_modEq_iff_modEq_mul hmq).1 ⟨h1.trans hca.symm, ?_⟩
              have hnr : n ≡ r [MOD q] := by
                show n % q = r % q
                rw [h2, Nat.mod_eq_of_lt hrq]
              exact hnr.trans hcr.symm
            · intro h
              obtain ⟨h1, h2⟩ := (Nat.modEq_and_modEq_iff_modEq_mul hmq).2 h
              refine ⟨h1.trans hca, ?_⟩
              have hnr : n ≡ r [MOD q] := h2.trans hcr
              have : n % q = r % q := hnr
              rwa [Nat.mod_eq_of_lt hrq] at this
          have hcongr : ∀ n ∈ ((range N).filter (fun n => n ≡ a [MOD m])).filter
                (fun n => n % q = r),
              (g q n - 1) * (ee (((j : ℝ) * n / Q : ℝ) : ℂ) * ∏ p ∈ s, g p n)
                = (g q r - 1) * (ee (((j : ℝ) * n / Q : ℝ) : ℂ) * ∏ p ∈ s, g p n) := by
            intro n hn
            have hnq : n % q = r := (Finset.mem_filter.1 hn).2
            have hgn : g q n = g q r := by
              rw [periodic_eq_mod (g q) (hper q hqmem) n, hnq]
            rw [hgn]
          rw [Finset.sum_congr rfl hcongr, ← Finset.mul_sum, norm_mul, hset]
          have hcop' : ∀ p ∈ s, Nat.Coprime p (m * q) := by
            intro p hp
            refine Nat.Coprime.mul_right (hcopm p (hsmem p hp)) ?_
            have hne : p ≠ q := fun hpq => hq (hpq ▸ hp)
            exact hpair (hsmem p hp) hqmem hne
          have := ihs (m * q) c (Nat.mul_pos hm hqpos)
            (Nat.Coprime.mul hmQ (hcopQ q hqmem)) hcop'
          exact mul_le_mul_of_nonneg_left this (norm_nonneg _)
        refine (Finset.sum_le_sum hterm).trans ?_
        rw [← Finset.sum_mul]
        refine mul_le_mul_of_nonneg_right (hV q hqmem) ?_
        positivity
      rw [Finset.prod_insert hq]
      have hRHS : (Q : ℝ) * ((1 + V q) * ∏ p ∈ s, (1 + V p))
          = (Q : ℝ) * ∏ p ∈ s, (1 + V p) + V q * ((Q : ℝ) * ∏ p ∈ s, (1 + V p)) := by ring
      rw [hRHS]
      exact add_le_add hfirst hsecond

/-! ### The crux's summand: the variation is an absolute constant -/

lemma ee_zero : ee 0 = 1 := by simp [ee]

lemma ee_sum {ι : Type*} (s : Finset ι) (f : ι → ℂ) :
    ee (∑ i ∈ s, f i) = ∏ i ∈ s, ee (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [ee_zero]
  | @insert i t hi ih => rw [Finset.sum_insert hi, ee_add, ih, Finset.prod_insert hi]

/-- **The variation of one prime factor is `16|h|/(b−1)` — independent of `p`.**  This is the
exact complete-period mass of `sum_range_tailPrimeTerm_period`, converted by `‖e(x)−1‖ ≤ 16|x|`. -/
theorem sum_range_norm_ee_tailPrimeTerm_sub_one_le {b : ℕ} (hb : 2 ≤ b) {p : ℕ} (hp : 0 < p)
    (h : ℤ) :
    ∑ r ∈ range p, ‖ee (((h : ℝ) * tailPrimeTerm b p r : ℝ) : ℂ) - 1‖
      ≤ 16 * |(h : ℝ)| / ((b : ℝ) - 1) := by
  have hbR : (2 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
  have hnn : ∀ r : ℕ, 0 ≤ tailPrimeTerm b p r := by
    intro r
    have hbp : (1 : ℝ) < (b : ℝ) ^ p := one_lt_pow₀ (by linarith) (by omega)
    rw [tailPrimeTerm]; positivity
  have hstep : ∀ r ∈ range p, ‖ee (((h : ℝ) * tailPrimeTerm b p r : ℝ) : ℂ) - 1‖
      ≤ 16 * |(h : ℝ)| * tailPrimeTerm b p r := by
    intro r _
    have h0 : ee (((0 : ℝ)) : ℂ) = 1 := by rw [Complex.ofReal_zero, ee_zero]
    have := norm_ee_sub_ee_le ((h : ℝ) * tailPrimeTerm b p r) 0
    rw [h0, sub_zero] at this
    refine this.trans (le_of_eq ?_)
    rw [abs_mul, abs_of_nonneg (hnn r)]
    ring
  refine (Finset.sum_le_sum hstep).trans (le_of_eq ?_)
  rw [← Finset.mul_sum, sum_range_tailPrimeTerm_period hb hp]
  ring

/-- **The sharpened master bound.**  The twisted sum of the truncated tail is bounded by
`Q · (1 + 16|h|/(b−1))^{#primes in (P,K]}` — exponential in `π(K) ≈ K/log K`, not in `K`.
This replaces the period `∏_{P<p≤K} p` of `norm_sum_addChar_tailTrunc_le`, and is strictly
smaller as soon as the primes exceed `16|h|/(b−1)`. -/
theorem norm_sum_addChar_tailTrunc_le_var {b P K Q j : ℕ} (hb : 2 ≤ b) (hQ : 0 < Q)
    (hQP : ∀ p : ℕ, p.Prime → p ∣ Q → p ≤ P) (hj0 : 0 < j) (hjQ : j < Q) (h : ℤ) (N : ℕ) :
    ‖∑ n ∈ range N, ee (((j : ℝ) * n / Q : ℝ) : ℂ)
        * ee (((h : ℝ) * tailTrunc b P K n : ℝ) : ℂ)‖
      ≤ (Q : ℝ)
        * (1 + 16 * |(h : ℝ)| / ((b : ℝ) - 1)) ^ (((Finset.Ioc P K).filter Nat.Prime).card) := by
  classical
  set F : Finset ℕ := (Finset.Ioc P K).filter Nat.Prime with hF
  set g : ℕ → ℕ → ℂ := fun p n => ee (((h : ℝ) * tailPrimeTerm b p n : ℝ) : ℂ) with hg
  have hmemF : ∀ p ∈ F, p.Prime ∧ P < p ∧ p ≤ K := by
    intro p hp
    simp only [hF, Finset.mem_filter, Finset.mem_Ioc] at hp
    exact ⟨hp.2, hp.1.1, hp.1.2⟩
  -- the summand is the product of the one-prime factors
  have hprod : ∀ n : ℕ, ee (((h : ℝ) * tailTrunc b P K n : ℝ) : ℂ) = ∏ p ∈ F, g p n := by
    intro n
    have hsum : (((h : ℝ) * tailTrunc b P K n : ℝ) : ℂ)
        = ∑ p ∈ F, (((h : ℝ) * tailPrimeTerm b p n : ℝ) : ℂ) := by
      rw [tailTrunc, Finset.mul_sum]
      push_cast
      rfl
    rw [hsum, ee_sum]
  have hpos : ∀ p ∈ F, 0 < p := fun p hp => (hmemF p hp).1.pos
  have hper : ∀ p ∈ F, ∀ n, g p (n + p) = g p n := by
    intro p _ n
    simp only [hg]
    rw [tailPrimeTerm_congr (Nat.add_modEq_right)]
  have hV : ∀ p ∈ F, ∑ r ∈ range p, ‖g p r - 1‖ ≤ 16 * |(h : ℝ)| / ((b : ℝ) - 1) := by
    intro p hp
    exact sum_range_norm_ee_tailPrimeTerm_sub_one_le hb (hmemF p hp).1.pos h
  have hcopQ : ∀ p ∈ F, Nat.Coprime p Q := by
    intro p hp
    obtain ⟨hpp, hPp, _⟩ := hmemF p hp
    rw [Nat.Prime.coprime_iff_not_dvd hpp]
    intro hd
    exact absurd (hQP p hpp hd) (by omega)
  have hpair : ((F : Set ℕ)).Pairwise Nat.Coprime := by
    intro x hx y hy hxy
    exact (Nat.coprime_primes (hmemF x (by simpa using hx)).1 (hmemF y (by simpa using hy)).1).2 hxy
  have key := norm_sum_addChar_prod_le hQ hj0 hjQ g (fun _ => 16 * |(h : ℝ)| / ((b : ℝ) - 1))
    F hpos hper hV hcopQ hpair 1 0 N Nat.one_pos (Nat.coprime_one_left Q)
    (fun p _ => Nat.coprime_one_right p)
  rw [Finset.filter_true_of_mem (fun x _ => Nat.modEq_one), Finset.prod_const] at key
  calc ‖∑ n ∈ range N, ee (((j : ℝ) * n / Q : ℝ) : ℂ)
          * ee (((h : ℝ) * tailTrunc b P K n : ℝ) : ℂ)‖
      = ‖∑ n ∈ range N, ee (((j : ℝ) * n / Q : ℝ) : ℂ) * ∏ p ∈ F, g p n‖ := by
        refine congrArg _ (Finset.sum_congr rfl fun n _ => ?_)
        rw [hprod n]
    _ ≤ _ := key

/-! ### The sharpened master inequality, and the comparison -/

/-- **The new period term is never worse than the old one** once `P ≥ 16|h|/(b−1)`: each prime
`p > P` pays a factor `1 + 16|h|/(b−1) ≤ p` instead of a factor `p`. -/
theorem var_pow_le_primePeriod {b P K : ℕ} (h : ℤ) (hb : 2 ≤ b)
    (hP : 1 + 16 * |(h : ℝ)| / ((b : ℝ) - 1) ≤ (P : ℝ) + 1) :
    (1 + 16 * |(h : ℝ)| / ((b : ℝ) - 1)) ^ (((Finset.Ioc P K).filter Nat.Prime).card)
      ≤ (primePeriod P K : ℝ) := by
  classical
  have hbR : (2 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
  have hc : (0 : ℝ) ≤ 16 * |(h : ℝ)| / ((b : ℝ) - 1) :=
    div_nonneg (by positivity) (by linarith)
  have hcast : ((primePeriod P K : ℕ) : ℝ) = ∏ p ∈ (Finset.Ioc P K).filter Nat.Prime, (p : ℝ) := by
    rw [primePeriod, Nat.cast_prod]
  rw [hcast, ← Finset.prod_const]
  refine Finset.prod_le_prod (fun p _ => by linarith) (fun p hp => ?_)
  have hPp : P < p := (Finset.mem_Ioc.1 (Finset.mem_filter.1 hp).1).1
  have : (P : ℝ) + 1 ≤ (p : ℝ) := by exact_mod_cast hPp
  linarith

/-- **THE SHARPENED MASTER INEQUALITY.**  The period `∏_{P<p≤K} p · Q` of
`SwingC3Mean.norm_sum_addChar_tailLarge_le` is replaced by `Q · (1 + 16|h|/(b−1))^{π(K)−π(P)}`.
The discarded-mass term is untouched — and that is the point: the improvement moves the first
term's constraint from `K ≲ log N` to `K ≲ log N · loglog N`, while the second still demands
`K ≳ N`, so the window survives.  The bound is the first sub-trivial estimate for the incomplete
sum, and it identifies the exact quantity the period method is limited by: the *total variation*
`∑_{r<p}‖g_p(r)−1‖ ≍ 1` per prime, rather than its *mean* `≍ 1/p`. -/
theorem norm_sum_addChar_tailLarge_le_var {b P K Q j : ℕ} (hb : 2 ≤ b) (hQ : 0 < Q)
    (hQP : ∀ p : ℕ, p.Prime → p ∣ Q → p ≤ P) (hj0 : 0 < j) (hjQ : j < Q) (h : ℤ) (N : ℕ) :
    ‖∑ n ∈ range N, ee (((j : ℝ) * n / Q : ℝ) : ℂ)
        * ee (((h : ℝ) * tailLarge P b n : ℝ) : ℂ)‖
      ≤ (Q : ℝ) * (1 + 16 * |(h : ℝ)| / ((b : ℝ) - 1))
            ^ (((Finset.Ioc P K).filter Nat.Prime).card)
        + 16 * |(h : ℝ)| * ∑ n ∈ range N, (tailLarge P b n - tailTrunc b P K n) := by
  classical
  set A : ℂ := ∑ n ∈ range N, ee (((j : ℝ) * n / Q : ℝ) : ℂ)
    * ee (((h : ℝ) * tailTrunc b P K n : ℝ) : ℂ) with hA
  have hsplit : ∑ n ∈ range N, ee (((j : ℝ) * n / Q : ℝ) : ℂ)
      * ee (((h : ℝ) * tailLarge P b n : ℝ) : ℂ)
      = A + ∑ n ∈ range N, ee (((j : ℝ) * n / Q : ℝ) : ℂ)
        * (ee (((h : ℝ) * tailLarge P b n : ℝ) : ℂ)
          - ee (((h : ℝ) * tailTrunc b P K n : ℝ) : ℂ)) := by
    rw [hA, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun n _ => by ring
  have hAbd := norm_sum_addChar_tailTrunc_le_var (b := b) (K := K) hb hQ hQP hj0 hjQ h N
  have hDbd : ‖∑ n ∈ range N, ee (((j : ℝ) * n / Q : ℝ) : ℂ)
      * (ee (((h : ℝ) * tailLarge P b n : ℝ) : ℂ)
        - ee (((h : ℝ) * tailTrunc b P K n : ℝ) : ℂ))‖
      ≤ 16 * |(h : ℝ)| * ∑ n ∈ range N, (tailLarge P b n - tailTrunc b P K n) := by
    calc ‖∑ n ∈ range N, ee (((j : ℝ) * n / Q : ℝ) : ℂ)
        * (ee (((h : ℝ) * tailLarge P b n : ℝ) : ℂ)
          - ee (((h : ℝ) * tailTrunc b P K n : ℝ) : ℂ))‖
        ≤ ∑ n ∈ range N, ‖ee (((j : ℝ) * n / Q : ℝ) : ℂ)
            * (ee (((h : ℝ) * tailLarge P b n : ℝ) : ℂ)
              - ee (((h : ℝ) * tailTrunc b P K n : ℝ) : ℂ))‖ := norm_sum_le _ _
      _ ≤ ∑ n ∈ range N, 16 * |(h : ℝ)| * (tailLarge P b n - tailTrunc b P K n) := by
          refine Finset.sum_le_sum fun n _ => ?_
          rw [norm_mul, norm_ee_real, one_mul]
          refine le_trans (norm_ee_sub_ee_le _ _) ?_
          have hnn := tailLarge_sub_tailTrunc_nonneg hb P K n
          have habs : |(h : ℝ) * tailLarge P b n - (h : ℝ) * tailTrunc b P K n|
              = |(h : ℝ)| * (tailLarge P b n - tailTrunc b P K n) := by
            rw [← mul_sub, abs_mul, abs_of_nonneg hnn]
          rw [habs]
          ring_nf
          exact le_rfl
      _ = 16 * |(h : ℝ)| * ∑ n ∈ range N, (tailLarge P b n - tailTrunc b P K n) := by
          rw [← Finset.mul_sum]
  rw [hsplit]
  exact le_trans (norm_add_le _ _) (by linarith)

end NormalNumbers



