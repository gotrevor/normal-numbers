/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.LnTwo
import NormalNumbers.PiBBP
import NormalNumbers.LnTwoIrrational
import NormalNumbers.KickedOrbit

/-!
# Normality's master conjectures as hypothesis `Prop`s (campaign launched 2026-10-02)

The Schanuel pattern from lean-formalizations, for normality: state the big believed conjectures
once, as named `Prop`s, and derive what follows from each.  Proposal:
`docs/proposal-normality-master-conjectures-2026-09-29.md`; kickoff:
`KICKOFF-2026-10-02-master-conjectures.md`.

* `BorelConjecture` (Borel 1950): every irrational algebraic real is normal in every base.
* `BaileyCrandallHypA` (Bailey–Crandall, *On the random character of fundamental constant
  expansions*, Experimental Math. 10 (2001), Hypothesis A, with Definitions 2.3 and 2.5).  Tier P
  for the wording, read from the paper on 2026-10-02.  Faithful-or-weaker: the attractor uses
  distance on the circle (the paper's `‖·‖`), which only makes the attractor alternative easier,
  and equidistribution is the repo's `Equidistributed` (all `[a, c) ⊆ [0, 1]`), which is the
  paper's Definition 2.3.

## Frozen statements (do not edit; prove them)

* `hypA_lnTwo`: Hypothesis A ⇒ `ln 2` normal in base 2 (Bailey–Crandall Thm 1.1, via the repo's
  reduction `LnTwo.lean`).
* `hypA_pi_base16`: Hypothesis A + the BBP formula ⇒ `π` normal in base 16.
* `borel_sqrt_two`: Borel ⇒ `√2` normal in base 2.

## Guard rule

**Content locator.**  `r_n = 1/n`, `b = 2` is `lnTwoOrbit`; there Hypothesis A's content is
exactly `Equidistributed lnTwoOrbit` (Maze "Hypothesis A as weaker": a restatement for `ln 2`).
The new content is the general form: one `Prop` with many consequences.

**Degenerate cases.**  `p = 0` would give `x ≡ 0`, a finite attractor; Bailey–Crandall exclude it
by `0 ≤ deg p`, here `p ≠ 0`.  `deg p ≥ deg q` is excluded (the perturbation must tend to `0`).
A rational `α = Σ r_n/bⁿ` is the finite-attractor branch (their Thm 2.10), so the disjunction is
load-bearing.  For Borel: rationals are excluded by `Irrational`, and `√2` is the first instance.
-/

namespace NormalNumbers.MasterConjectures

open Polynomial Filter

/-- Distance on the circle `ℝ/ℤ`: `‖x − w‖ = |(x − w) − round(x − w)|`. -/
noncomputable def circDist (x w : ℝ) : ℝ := |(x - w) - round (x - w)|

/-- The Bailey–Crandall orbit: `x₀ = 0`, `xₙ = (b·xₙ₋₁ + p(n)/q(n)) mod 1`. -/
noncomputable def bcOrbit (p q : ℤ[X]) (b : ℕ) : ℕ → ℝ
  | 0 => 0
  | n + 1 => Int.fract (b * bcOrbit p q b n
      + ((p.eval ((n + 1 : ℕ) : ℤ) : ℤ) : ℝ) / ((q.eval ((n + 1 : ℕ) : ℤ) : ℤ) : ℝ))

/-- Bailey–Crandall Definition 2.5: `x` has a finite attractor `W` if for every `ε > 0` there is
`K` such that every `x_{K+k}` is within `ε` (on the circle) of some element of `W`. -/
def HasFiniteAttractor (x : ℕ → ℝ) : Prop :=
  ∃ W : Finset ℝ, W.Nonempty ∧ ∀ ε > 0, ∃ K : ℕ, ∀ k : ℕ, ∃ w ∈ W, circDist (x (K + k)) w < ε

/-- **Bailey–Crandall Hypothesis A.**  For `p, q ∈ ℤ[X]` with `p ≠ 0`, `deg p < deg q` and
`q(n) ≠ 0` for every positive integer `n`, and every base `b ≥ 2`, the orbit `bcOrbit p q b`
either has a finite attractor or is equidistributed.  Open (believed). -/
def BaileyCrandallHypA : Prop :=
  ∀ (p q : ℤ[X]) (b : ℕ), p ≠ 0 → p.natDegree < q.natDegree →
    (∀ n : ℕ, 1 ≤ n → q.eval (n : ℤ) ≠ 0) → 2 ≤ b →
      HasFiniteAttractor (bcOrbit p q b) ∨ Equidistributed (bcOrbit p q b)

/-- **Borel's conjecture (1950).**  Every irrational algebraic real is normal in every base.
Open (believed). -/
def BorelConjecture : Prop :=
  ∀ x : ℝ, Irrational x → IsAlgebraic ℚ x → ∀ b : ℕ, 2 ≤ b → IsNormal b x

/-! ## Circle-distance toolkit and the finite-attractor exclusion (proved 2026-10-02) -/

theorem circDist_nonneg (x w : ℝ) : 0 ≤ circDist x w := abs_nonneg _

theorem circDist_le_int (x w : ℝ) (k : ℤ) : circDist x w ≤ |x - w - k| := round_le _ _

theorem circDist_add_int (x w : ℝ) (k : ℤ) : circDist (x + k) w = circDist x w := by
  unfold circDist
  have : x + k - w = (x - w) + k := by ring
  rw [this, round_add_intCast]; push_cast; ring_nf

theorem circDist_fract (y w : ℝ) : circDist (Int.fract y) w = circDist y w := by
  have : Int.fract y = y + ((-⌊y⌋ : ℤ) : ℝ) := by rw [Int.fract]; push_cast; ring
  rw [this, circDist_add_int]

theorem circDist_triangle (a b c : ℝ) : circDist a c ≤ circDist a b + circDist b c := by
  calc circDist a c ≤ |a - c - ((round (a - b) + round (b - c) : ℤ) : ℝ)| := circDist_le_int _ _ _
    _ = |((a - b) - round (a - b)) + ((b - c) - round (b - c))| := by push_cast; ring_nf
    _ ≤ _ := abs_add_le _ _

theorem circDist_perturb (y δ w : ℝ) : circDist (y + δ) w ≤ circDist y w + |δ| := by
  calc circDist (y + δ) w ≤ |y + δ - w - round (y - w)| := circDist_le_int _ _ _
    _ = |((y - w) - round (y - w)) + δ| := by ring_nf
    _ ≤ _ := abs_add_le _ _

theorem circDist_two_mul (a b : ℝ) : circDist (2 * b) (2 * a) ≤ 2 * circDist a b := by
  calc circDist (2 * b) (2 * a) ≤ |2 * b - 2 * a - ((-(2 * round (a - b)) : ℤ) : ℝ)| :=
        circDist_le_int _ _ _
    _ = |(-2) * ((a - b) - round (a - b))| := by push_cast; ring_nf
    _ = _ := by rw [abs_mul]; norm_num; rfl

/-- A finite attractor survives a vanishing perturbation. -/
theorem hasFiniteAttractor_perturb (u δ : ℕ → ℝ) (hu : HasFiniteAttractor u)
    (hδ : Tendsto δ atTop (nhds 0)) :
    HasFiniteAttractor (fun n => Int.fract (u n + δ n)) := by
  obtain ⟨W, hW, h⟩ := hu
  refine ⟨W, hW, fun ε hε => ?_⟩
  obtain ⟨K1, hK1⟩ := h (ε / 2) (by positivity)
  obtain ⟨K2, hK2⟩ := (Metric.tendsto_atTop.1 hδ) (ε / 2) (by positivity)
  refine ⟨max K1 K2, fun k => ?_⟩
  obtain ⟨w, hw, hd⟩ := hK1 (max K1 K2 - K1 + k)
  have hidx : K1 + (max K1 K2 - K1 + k) = max K1 K2 + k := by omega
  rw [hidx] at hd
  have h2 := hK2 (max K1 K2 + k) (by omega)
  rw [Real.dist_eq, sub_zero] at h2
  refine ⟨w, hw, ?_⟩
  rw [circDist_fract]
  linarith [circDist_perturb (u (max K1 K2 + k)) (δ (max K1 K2 + k)) w]

theorem fract_two_mul_fract (t : ℝ) : Int.fract (2 * Int.fract t) = Int.fract (2 * t) := by
  have : 2 * Int.fract t = 2 * t - ((2 * ⌊t⌋ : ℤ) : ℝ) := by rw [Int.fract]; push_cast; ring
  rw [this, Int.fract_sub_intCast]

theorem circDist_mul_nat (a b' : ℝ) (b : ℕ) : circDist (b * b') (b * a) ≤ b * circDist a b' := by
  calc circDist (b * b') (b * a) ≤ |b * b' - b * a - ((-(b * round (a - b')) : ℤ) : ℝ)| :=
        circDist_le_int _ _ _
    _ = |(-(b : ℝ)) * ((a - b') - round (a - b'))| := by push_cast; ring_nf
    _ = _ := by rw [abs_mul, abs_neg, Nat.abs_cast]; rfl

theorem fract_nat_mul_fract (b : ℕ) (t : ℝ) :
    Int.fract (b * Int.fract t) = Int.fract (b * t) := by
  have : (b : ℝ) * Int.fract t = b * t - ((b * ⌊t⌋ : ℤ) : ℝ) := by rw [Int.fract]; push_cast; ring
  rw [this, Int.fract_sub_intCast]

/-- Bailey–Crandall Thm 2.10 for `x ↦ b·x mod 1`: a finite attractor forces rationality. -/
theorem not_irrational_of_hasFiniteAttractor_base (b : ℕ) (hb : 2 ≤ b) (x : ℝ)
    (hx : HasFiniteAttractor (orbit b x)) : ¬ Irrational x := by
  intro hirr
  obtain ⟨W, hW, h⟩ := hx
  have hbR : (2 : ℝ) ≤ b := by exact_mod_cast hb
  set S := ((W ×ˢ W).image (fun pr : ℝ × ℝ => circDist (b * pr.1) pr.2)).filter (0 < ·)
  have hne : (insert (1 : ℝ) S).Nonempty := Finset.insert_nonempty _ _
  set η := (insert (1 : ℝ) S).min' hne
  have hη : 0 < η := by
    show 0 < (insert (1 : ℝ) S).min' hne
    obtain hm := Finset.min'_mem _ hne
    rcases Finset.mem_insert.1 hm with h1 | h1
    · rw [h1]; norm_num
    · exact (Finset.mem_filter.1 h1).2
  have hsep : ∀ w ∈ W, ∀ w' ∈ W, circDist (b * w) w' < η → circDist (b * w) w' = 0 := by
    intro w hw w' hw' hlt
    by_contra hne0
    have hpos : 0 < circDist (b * w) w' := lt_of_le_of_ne (circDist_nonneg _ _) (Ne.symm hne0)
    have hmem : circDist (b * w) w' ∈ insert (1 : ℝ) S :=
      Finset.mem_insert_of_mem (Finset.mem_filter.2
        ⟨Finset.mem_image.2 ⟨(w, w'), Finset.mem_product.2 ⟨hw, hw'⟩, rfl⟩, hpos⟩)
    exact absurd (Finset.min'_le _ _ hmem) (not_le.2 hlt)
  set ε := min (η / (2 * (b + 1))) (1 / (2 * (b + 1))) with hεdef
  have hε : 0 < ε := by positivity
  have hεη : ε * (b + 1) < η := by
    have : ε ≤ η / (2 * (b + 1)) := min_le_left _ _
    rw [le_div_iff₀ (by positivity)] at this; nlinarith
  have hε1 : ε * (b + 1) < 1 := by
    have : ε ≤ 1 / (2 * (b + 1)) := min_le_right _ _
    rw [le_div_iff₀ (by positivity)] at this; nlinarith
  obtain ⟨K, hK⟩ := h ε hε
  choose w hwW hwd using hK
  set y : ℕ → ℝ := fun k => orbit b x (K + k) with hydef
  have hy_succ : ∀ k, y (k + 1) = Int.fract (b * y k) := by
    intro k
    simp only [hydef, orbit, fract_nat_mul_fract]
    congr 1; rw [show K + (k + 1) = (K + k) + 1 by omega, pow_succ]; ring
  have hA : ∀ k, circDist (b * w k) (w (k + 1)) = 0 := by
    intro k
    apply hsep _ (hwW k) _ (hwW (k + 1))
    have h1 := circDist_mul_nat (y k) (w k) b
    have h2 : circDist (b * y k) (w (k + 1)) < ε := by
      rw [← circDist_fract, ← hy_succ]; exact hwd (k + 1)
    have h3 := circDist_triangle (b * w k) (b * y k) (w (k + 1))
    have h4 : circDist (y k) (w k) < ε := hwd k
    have : (b : ℝ) * circDist (y k) (w k) ≤ b * ε := by
      apply mul_le_mul_of_nonneg_left h4.le; positivity
    nlinarith
  set e : ℕ → ℝ := fun k => y k - w k - round (y k - w k) with hedef
  have he_lt : ∀ k, |e k| < ε := fun k => hwd k
  have he_succ : ∀ k, e (k + 1) = b * e k := by
    intro k
    have hz : ∃ m : ℤ, b * w k - w (k + 1) = m := by
      have h0 := hA k
      unfold circDist at h0
      exact ⟨round (b * w k - w (k + 1)), by linarith [abs_eq_zero.1 h0]⟩
    obtain ⟨m, hm⟩ := hz
    set j : ℤ := b * round (y k - w k) - ⌊(b : ℝ) * y k⌋ + m - round (y (k + 1) - w (k + 1))
    have hj : e (k + 1) - b * e k = j := by
      simp only [hedef, j]; rw [hy_succ k, Int.fract]; push_cast; linarith
    have hjabs : |(j : ℝ)| < 1 := by
      rw [← hj]
      calc |e (k + 1) - b * e k| ≤ |e (k + 1)| + |b * e k| := abs_sub _ _
        _ = |e (k + 1)| + b * |e k| := by rw [abs_mul, Nat.abs_cast]
        _ ≤ ε + b * ε := by
          have := he_lt k
          gcongr
          · exact (he_lt (k + 1)).le
        _ < 1 := by linarith
    have : j = 0 := by
      rw [← Int.cast_abs] at hjabs
      have : |j| < 1 := by exact_mod_cast hjabs
      exact Int.abs_lt_one_iff.1 this
    rw [this] at hj; push_cast at hj; linarith
  have he_pow : ∀ k, e k = (b : ℝ) ^ k * e 0 := by
    intro k; induction k with
    | zero => simp
    | succ k ih => rw [he_succ, ih, pow_succ]; ring
  have he0 : e 0 = 0 := by
    by_contra hne0
    have hpos : 0 < |e 0| := abs_pos.2 hne0
    obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (ε / |e 0|) (by linarith : (1 : ℝ) < b)
    have := he_lt k
    rw [he_pow, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < (b : ℝ) ^ k)] at this
    rw [div_lt_iff₀ hpos] at hk
    linarith
  have hyw : ∀ k, y k = Int.fract (w k) := by
    intro k
    have hek : e k = 0 := by rw [he_pow, he0, mul_zero]
    have : w k = y k + ((-round (y k - w k) : ℤ) : ℝ) := by
      simp only [hedef] at hek; push_cast; linarith
    rw [this, Int.fract_add_intCast]
    simp only [hydef, orbit, Int.fract_fract]
  have hmaps : ∀ k ∈ Finset.range (W.card + 1), y k ∈ W.image Int.fract := by
    intro k _; rw [hyw]; exact Finset.mem_image_of_mem _ (hwW k)
  have hcard : (W.image Int.fract).card < (Finset.range (W.card + 1)).card := by
    rw [Finset.card_range]; exact Nat.lt_succ_of_le Finset.card_image_le
  obtain ⟨i, -, j, -, hij, hyij⟩ := Finset.exists_ne_map_eq_of_card_lt_of_maps_to hcard hmaps
  simp only [hydef, orbit] at hyij
  obtain ⟨z, hz⟩ := Int.fract_eq_fract.1 hyij
  have hq : ((b : ℚ) ^ (K + i) - b ^ (K + j)) ≠ 0 := by
    intro h0
    have : (b : ℚ) ^ (K + i) = b ^ (K + j) := by linarith
    have := Nat.pow_right_injective hb (by exact_mod_cast this : b ^ (K + i) = b ^ (K + j))
    omega
  have := hirr.mul_ratCast hq
  push_cast at this
  rw [show x * ((b : ℝ) ^ (K + i) - b ^ (K + j)) = (z : ℝ) by linarith] at this
  exact Int.not_irrational z this

/-- Bailey–Crandall Thm 2.10 for the doubling map: a finite attractor forces rationality. -/
theorem not_irrational_of_hasFiniteAttractor (x : ℝ) (hx : HasFiniteAttractor (orbit 2 x)) :
    ¬ Irrational x :=
  not_irrational_of_hasFiniteAttractor_base 2 le_rfl x hx

/-- Bailey–Crandall eq. (3), scaled by 16: numerator. -/
noncomputable def piP : ℤ[X] := C 16 * (C 120 * X ^ 2 - C 89 * X + C 16)
/-- Bailey–Crandall eq. (3): denominator. -/
noncomputable def piQ : ℤ[X] :=
  C 512 * X ^ 4 - C 1024 * X ^ 3 + C 712 * X ^ 2 - C 206 * X + C 21

theorem piQ_eval (n : ℕ) : ((piQ.eval ((n + 1 : ℕ) : ℤ) : ℤ) : ℝ)
    = (8 * (n : ℝ) + 1) * (8 * n + 4) * (8 * n + 5) * (8 * n + 6) / 8 := by
  simp [piQ]; ring

theorem pi_kick_eq (n : ℕ) :
    ((piP.eval ((n + 1 : ℕ) : ℤ) : ℤ) : ℝ) / ((piQ.eval ((n + 1 : ℕ) : ℤ) : ℤ) : ℝ)
      = 16 * bbpKick n := by
  rw [piQ_eval]
  simp only [piP, bbpKick, eval_mul, eval_C, eval_add, eval_sub, eval_pow, eval_X]
  have h1 : (8 * (n : ℝ) + 1) ≠ 0 := by positivity
  have h4 : (8 * (n : ℝ) + 4) ≠ 0 := by positivity
  have h5 : (8 * (n : ℝ) + 5) ≠ 0 := by positivity
  have h6 : (8 * (n : ℝ) + 6) ≠ 0 := by positivity
  push_cast
  field_simp
  ring

theorem bcOrbit_pi : bcOrbit piP piQ 16 = piSurrogate := by
  funext n
  induction n with
  | zero => simp [bcOrbit, piSurrogate, piPartial]
  | succ n ih =>
    rw [bcOrbit, ih, pi_kick_eq, piSurrogate, piSurrogate]
    set t := (16 : ℝ) ^ n * piPartial n
    have : ((16 : ℕ) : ℝ) * Int.fract t + 16 * bbpKick n
        = (16 * t + 16 * bbpKick n) + ((-(16 * ⌊t⌋) : ℤ) : ℝ) := by
      rw [Int.fract]; push_cast; ring
    rw [this, Int.fract_add_intCast]
    congr 1
    simp only [t, piPartial, Finset.sum_range_succ, bbpTerm]
    field_simp
    ring

theorem piQ_natDegree : piQ.natDegree = 4 := by unfold piQ; compute_degree!
theorem piP_natDegree : piP.natDegree = 2 := by unfold piP; compute_degree!

theorem piQ_ne (n : ℕ) (hn : 1 ≤ n) : piQ.eval (n : ℤ) ≠ 0 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  intro h
  have := piQ_eval m
  rw [h] at this
  have : (0 : ℝ) < (8 * (m : ℝ) + 1) * (8 * m + 4) * (8 * m + 5) * (8 * m + 6) / 8 := by positivity
  push_cast at *; linarith

theorem piSurrogate_mem_Ico (n : ℕ) : piSurrogate n ∈ Set.Ico (0 : ℝ) 1 :=
  ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩

theorem tendsto_pi_tail (hπ : PiBBP) :
    Tendsto (fun n : ℕ => (16 : ℝ) ^ n * piTail n) atTop (nhds 0) := by
  have hlim : Tendsto (fun n : ℕ => 22 * (1 / ((n : ℝ) + 1))) atTop (nhds 0) := by
    simpa using tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (22 : ℝ)
  refine squeeze_zero (fun n => ?_) (fun n => ?_) hlim
  · exact le_trans (by positivity) (piTail_ge hπ n)
  · refine (piTail_le hπ n).trans ?_
    rw [div_le_iff₀ (by positivity)]
    have : (0 : ℝ) ≤ n := n.cast_nonneg
    field_simp
    nlinarith

theorem orbit_pi_eq (n : ℕ) :
    orbit 16 Real.pi n = Int.fract (piSurrogate n + (16 : ℝ) ^ n * piTail n) := by
  rw [orbit_eq_fract_add_tail 16 Real.pi (piPartial n) n, piSurrogate, piTail]; push_cast; rfl

theorem bcOrbit_lnTwo : bcOrbit (C 1) X 2 = lnTwoOrbit := by
  funext n
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [bcOrbit, lnTwoOrbit, ih]
    simp

/-- `√2` is algebraic over `ℚ` (root of `X² − 2`). -/
theorem isAlgebraic_sqrt_two : IsAlgebraic ℚ (Real.sqrt 2) := by
  refine ⟨X ^ 2 - C 2, X_pow_sub_C_ne_zero (by norm_num) _, ?_⟩
  simp

/-- Hypothesis A gives the normality of `ln 2` in base 2 (Bailey–Crandall Thm 1.1). -/
theorem hypA_lnTwo (hA : BaileyCrandallHypA) : IsNormal 2 (Real.log 2) := by
  rcases hA (C 1) X 2 (by simp) (by simp) (fun n hn => by simp; omega) le_rfl with hfa | heq
  · exfalso
    rw [bcOrbit_lnTwo] at hfa
    have hpert := hasFiniteAttractor_perturb _ _ hfa tendsto_pow_mul_lnTwoTail
    have : orbit 2 (Real.log 2) = fun n => Int.fract (lnTwoOrbit n + 2 ^ n * lnTwoTail n) :=
      funext orbit_log_two_eq
    rw [← this] at hpert
    exact not_irrational_of_hasFiniteAttractor _ hpert irrational_log_two
  · rw [bcOrbit_lnTwo] at heq
    exact isNormal_log_two_of_equidistributed heq

/-- Hypothesis A and the BBP formula give the normality of `π` in base 16. -/
theorem hypA_pi_base16 (hA : BaileyCrandallHypA) (hπ : PiBBP) : IsNormal 16 Real.pi := by
  have hp : piP ≠ 0 := by
    intro h; have := piP_natDegree; rw [h] at this; simp at this
  rcases hA piP piQ 16 hp (by rw [piP_natDegree, piQ_natDegree]; norm_num) piQ_ne (by norm_num)
    with hfa | heq
  · exfalso
    rw [bcOrbit_pi] at hfa
    have hpert := hasFiniteAttractor_perturb _ _ hfa (tendsto_pi_tail hπ)
    rw [← funext orbit_pi_eq] at hpert
    exact not_irrational_of_hasFiniteAttractor_base 16 (by norm_num) _ hpert irrational_pi
  · rw [bcOrbit_pi] at heq
    rw [isNormal_iff_equidistributed_orbit 16 (by norm_num) Real.pi, funext orbit_pi_eq]
    exact equidistributed_of_fract_perturb _ _ heq piSurrogate_mem_Ico
      (fun n => le_trans (by positivity) (piTail_ge hπ n)) (tendsto_pi_tail hπ)

/-- Borel's conjecture gives the normality of `√2` in base 2. -/
theorem borel_sqrt_two (hB : BorelConjecture) : IsNormal 2 (Real.sqrt 2) := by
  exact hB _ irrational_sqrt_two isAlgebraic_sqrt_two 2 le_rfl

end NormalNumbers.MasterConjectures
