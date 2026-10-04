/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.DigitCantor
import NormalNumbers.WallRational
import NormalNumbers.EquidistTransfer

/-!
# Entropy lane (E5): cited inputs, the Cantor profile, and the bi-Lipschitz question

Audit: `docs/ENTROPY-AUDIT-2026-10-04.md`.

**Cited inputs** (named hypothesis `Prop`s, faithful-or-weaker, never axioms):

* `CasselsSchmidtCantor`: Cassels 1959 / Schmidt 1960, the Cantor–Lebesgue measure is
  pointwise `b`-normal for every `b ≁ 3`.
* `HochmanShmerkinCantorDiff1`: Hochman–Shmerkin, *Equidistribution from fractal measures*,
  Invent. Math. 202 (2015) 427–479, Theorem 1.4 (arXiv:1302.5792 numbering), specialised to the
  middle-third IFS: the same holds for `f_*μ`, every `C¹` diffeomorphism `f` of `ℝ`.
* `HochmanShmerkinTimesP`: the same paper, Theorem 1.10 (Host 1995, Théorème 1, when
  `gcd(m, p) = 1`): a `×p`-ergodic measure of positive dimension is pointwise `m`-normal for
  every `m ≁ p`.

**Proved wiring.**  `casselsSchmidt_of_hochmanShmerkin` (take `f = id`); the exact a.e.
profile of Cantor-typical points, `ae_isNormal_iff_not_multDep` (normal in `b` iff `b ≁ 3`,
conditional on Cassels–Schmidt); the known-false sibling `not_isNormal_three_pow_cantorPt`
(every Cantor point fails every base `3ᵏ`, so the `b ≁ 3` hypothesis cannot be dropped).

**Frozen headline** (`sorry`): `exists_strictMono_biLipschitz_cantorSet_not_isNormal_two`,
a negative answer to Hochman–Shmerkin's question "The stability of our results under
bi-Lipschitz transformations remains open" (§1.2.1, after Corollary 1.8).  Its consequences
`not_biLipschitz_stable` and `exists_biLipschitz_ae_not_isNormal_two` are wired from it.
-/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace NormalNumbers.EntropyProfiles

open DigitCantor

/-! ## Vocabulary -/

/-- `a` and `b` are **multiplicatively dependent**, `a ∼ b`: some positive powers agree
(equivalently `log a / log b ∈ ℚ` for `a, b ≥ 2`). -/
def MultDep (a b : ℕ) : Prop := ∃ m n : ℕ, 0 < m ∧ 0 < n ∧ a ^ m = b ^ n

/-- A `C¹` diffeomorphism of `ℝ` (Hochman–Shmerkin's `diff¹(ℝ)`): `C¹`, nowhere-vanishing
derivative, bijective (the inverse is then `C¹` by the inverse function theorem). -/
def IsC1Diffeo (f : ℝ → ℝ) : Prop :=
  ContDiff ℝ 1 f ∧ (∀ x, deriv f x ≠ 0) ∧ Function.Bijective f

/-- A bi-Lipschitz map of `ℝ`, with one constant for both directions. -/
def IsBiLipschitz (g : ℝ → ℝ) : Prop := ∃ K : ℝ≥0, LipschitzWith K g ∧ AntilipschitzWith K g

/-- The `×p` map on `[0,1)`. -/
noncomputable def timesMap (p : ℕ) (x : ℝ) : ℝ := Int.fract ((p : ℝ) * x)

/-- The middle-third Cantor point with ternary digits `2ω_i ∈ {0, 2}`. -/
noncomputable def cantorPt (ω : ℕ → Fin 2) : ℝ :=
  realOfDigits 3 (fun i => 2 * (ω i : ℕ))

/-- The **Cantor–Lebesgue measure**: the law of `cantorPt` under fair i.i.d. digits. -/
noncomputable def cantorLebesgue : Measure ℝ := (digitMeasure 1).map cantorPt

/-! ## Basic facts -/

theorem cantorPt_eq_two_mul (ω : ℕ → Fin 2) : cantorPt ω = 2 * zReal 1 ω := by
  unfold cantorPt zReal realOfDigits digs
  rw [← tsum_mul_left]
  congr 1
  funext i
  push_cast
  ring

theorem cantorPt_eq_ofDigits (ω : ℕ → Fin 2) :
    cantorPt ω = Real.ofDigits (fun i => (⟨2 * (ω i : ℕ), by have := (ω i).isLt; omega⟩ : Fin 3)) := by
  unfold cantorPt realOfDigits Real.ofDigits Real.ofDigitsTerm
  congr 1

theorem cantorPt_mem_cantorSet (ω : ℕ → Fin 2) : cantorPt ω ∈ cantorSet := by
  rw [cantorPt_eq_ofDigits]
  refine ofDigits_zero_two_sequence_mem_cantorSet fun n h => ?_
  have := congrArg Fin.val h
  simp at this

theorem measurable_cantorPt : Measurable cantorPt := by
  have : cantorPt = fun ω => 2 * zReal 1 ω := funext cantorPt_eq_two_mul
  rw [this]
  exact measurable_const.mul measurable_zReal

instance : IsProbabilityMeasure cantorLebesgue := by
  unfold cantorLebesgue
  exact Measure.isProbabilityMeasure_map measurable_cantorPt.aemeasurable

theorem ae_mem_cantorSet : ∀ᵐ x ∂cantorLebesgue, x ∈ cantorSet := by
  unfold cantorLebesgue
  exact (ae_map_iff measurable_cantorPt.aemeasurable (p := fun x => x ∈ cantorSet)
    isClosed_cantorSet.measurableSet).2 (ae_of_all _ cantorPt_mem_cantorSet)

theorem not_multDep_two_three : ¬ MultDep 2 3 := by
  rintro ⟨m, n, hm, hn, h⟩
  have h2 : 2 ∣ 3 ^ n := h ▸ dvd_pow_self 2 hm.ne'
  have : 2 ∣ 3 := (Nat.prime_two.dvd_of_dvd_pow h2)
  omega

theorem multDep_three_pow {k : ℕ} (hk : 0 < k) : MultDep (3 ^ k) 3 :=
  ⟨1, k, one_pos, hk, by ring⟩

/-- A base dependent on `3` is a power of `3`. -/
theorem eq_three_pow_of_multDep {b : ℕ} (hb : 2 ≤ b) (h : MultDep b 3) :
    ∃ k, 0 < k ∧ b = 3 ^ k := by
  obtain ⟨m, n, hm, hn, hbm⟩ := h
  have hb0 : b ≠ 0 := by omega
  have hfac := Nat.eq_prime_pow_of_unique_prime_dvd (p := 3) hb0 fun {d} hd hdb => by
    have : d ∣ 3 ^ n := hbm ▸ dvd_pow hdb hm.ne'
    exact (Nat.prime_dvd_prime_iff_eq hd Nat.prime_three).1 (hd.dvd_of_dvd_pow this)
  refine ⟨b.primeFactorsList.length, ?_, hfac⟩
  rcases Nat.eq_zero_or_pos b.primeFactorsList.length with h0 | h0
  · rw [h0, pow_zero] at hfac; omega
  · exact h0

/-! ## Known-false sibling: dependent bases -/

/-- **Guard.**  Every Cantor point fails every base `3ᵏ` (it misses the ternary digit `1`), so
the hypothesis `b ≁ 3` in the cited inputs cannot be dropped; `9` is the `log 9 / log 3 ∈ ℚ`
case. -/
theorem not_isNormal_three_pow_cantorPt (ω : ℕ → Fin 2) {k : ℕ} (hk : 0 < k) :
    ¬ IsNormal (3 ^ k) (cantorPt ω) := by
  intro h
  have h3 : IsNormal 3 (cantorPt ω) := isNormal_of_isNormal_pow (by norm_num) hk h
  have hz := isNormal_rat_mul_add 3 (by norm_num) _ (1 / 2 : ℚ) 0 (by norm_num) h3
  apply not_isNormal_zReal (m := 1) ω
  convert hz using 1
  rw [cantorPt_eq_two_mul]
  push_cast
  ring

theorem not_ae_isNormal_three_pow {k : ℕ} (hk : 0 < k) :
    ¬ ∀ᵐ x ∂cantorLebesgue, IsNormal (3 ^ k) x := by
  intro h
  have h' : ∀ᵐ ω ∂(digitMeasure 1), IsNormal (3 ^ k) (cantorPt ω) :=
    ae_of_ae_map measurable_cantorPt.aemeasurable h
  have hfalse : ∀ᵐ ω ∂(digitMeasure 1), False :=
    h'.mono fun ω hω => not_isNormal_three_pow_cantorPt ω hk hω
  rw [ae_iff] at hfalse
  simp at hfalse

/-- The base-`9` instance of the guard. -/
theorem not_ae_isNormal_nine : ¬ ∀ᵐ x ∂cantorLebesgue, IsNormal 9 x := by
  simpa using not_ae_isNormal_three_pow (k := 2) (by norm_num)

/-! ## Cited inputs -/

/-- **Cited: Cassels (Colloq. Math. 7 (1959) 95–101) and Schmidt (Pacific J. Math. 10 (1960)
661–672).**  The Cantor–Lebesgue measure on the middle-third Cantor set is pointwise
`b`-normal for every `b ≁ 3`.  Also Hochman–Shmerkin 2015, Theorem 1.4 with `g = id`.
Faithful: our form `∀ᵐ x ∂μ, IsNormal b x` is their "μ-a.e. `x` is `b`-normal". -/
def CasselsSchmidtCantor : Prop :=
  ∀ b : ℕ, 2 ≤ b → ¬ MultDep b 3 → ∀ᵐ x ∂cantorLebesgue, IsNormal b x

/-- **Cited: Hochman–Shmerkin, *Equidistribution from fractal measures*, Invent. Math. 202
(2015) 427–479, Theorem 1.4** (arXiv:1302.5792 numbering, label `thm:dissonant-IFSs`),
specialised to the regular `C^{1+ε}` IFS `{x/3, x/3 + 2/3}` (contraction ratio `1/3`,
`1/3 ≁ b` iff `b ≁ 3`) and its Bernoulli(1/2) measure, a quasi-product measure: "`μ` is pointwise
`β`-normal, and so is `gμ` for all `g ∈ diff¹(ℝ)`", with `β = b` an integer (integers count as
Pisot in their convention).  Faithful-or-weaker: their `g μ`-a.e. statement implies ours via
`ae_of_ae_map`. -/
def HochmanShmerkinCantorDiff1 : Prop :=
  ∀ f : ℝ → ℝ, IsC1Diffeo f → ∀ b : ℕ, 2 ≤ b → ¬ MultDep b 3 →
    ∀ᵐ x ∂cantorLebesgue, IsNormal b (f x)

/-- **Cited: Hochman–Shmerkin 2015, Theorem 1.10** (label `thm:application-HostLindenstrauss`,
`γ = p`, `β = m` an integer), extending Host, *Nombres normaux, entropie, translations*, Israel
J. Math. 91 (1995) 419–428, Théorème 1 (case `gcd(m, p) = 1`) and Lindenstrauss 2001.  A
`T_p`-invariant ergodic measure of positive entropy is pointwise `m`-normal when `m ≁ p`.

Faithful-or-weaker: "positive entropy" is replaced by the stronger hypothesis of a Frostman bound
`μ(B(x, r)) ≤ C r^δ`, `δ > 0`, which gives `dim μ ≥ δ > 0`, and for a `T_p`-ergodic measure
`dim μ = h(μ) / log p`. -/
def HochmanShmerkinTimesP : Prop :=
  ∀ p m : ℕ, 2 ≤ p → 2 ≤ m → ¬ MultDep m p →
    ∀ μ : Measure ℝ, IsProbabilityMeasure μ → μ (Set.Ico 0 1)ᶜ = 0 →
      Ergodic (timesMap p) μ →
      (∃ C δ : ℝ, 0 < δ ∧ ∀ x r : ℝ, 0 < r → μ (Metric.closedBall x r) ≤ ENNReal.ofReal (C * r ^ δ)) →
      ∀ᵐ x ∂μ, IsNormal m x

/-! ## Wiring -/

theorem isC1Diffeo_id : IsC1Diffeo id :=
  ⟨contDiff_id, fun x => by simp, Function.bijective_id⟩

/-- Hochman–Shmerkin's Theorem 1.4 contains Cassels–Schmidt (`g = id`). -/
theorem casselsSchmidt_of_hochmanShmerkin (h : HochmanShmerkinCantorDiff1) :
    CasselsSchmidtCantor := fun b hb hdep => h id isC1Diffeo_id b hb hdep

/-- **The a.e. normality profile of Cantor-typical points** (known: Cassels–Schmidt plus the
missing digit).  `μ`-a.e. normal in base `b` iff `b ≁ 3`.  Recorded so that "a new a.e. profile
theorem for `×p` / self-similar measures" is visibly not a target: the profile is `{b ≁ p}`. -/
theorem ae_isNormal_iff_not_multDep (hCS : CasselsSchmidtCantor) {b : ℕ} (hb : 2 ≤ b) :
    (∀ᵐ x ∂cantorLebesgue, IsNormal b x) ↔ ¬ MultDep b 3 := by
  constructor
  · intro h hdep
    obtain ⟨k, hk, rfl⟩ := eq_three_pow_of_multDep hb hdep
    exact not_ae_isNormal_three_pow hk h
  · exact hCS b hb

/-! ## Frozen headline: the bi-Lipschitz question -/

/-- **Headline (frozen, `sorry`).  Hochman–Shmerkin's bi-Lipschitz question has a negative
answer.**

*Problem* (Hochman–Shmerkin, Invent. Math. 202 (2015), §1.2.1, after Corollary 1.8, arXiv:1302.5792):
"Bugeaud, Fishman, Kleinbock and Weiss have shown that for many fractal sets, including
self-similar sets satisfying the open set condition, there is a full-dimension subset consisting of
numbers which are *not* normal in any integer base. Moreover their result holds for any
bi-Lipschitz image of the set. **The stability of our results under bi-Lipschitz transformations
remains open.**"  Their results include `HochmanShmerkinCantorDiff1`: `g μ` is pointwise
`b`-normal for every `C¹` diffeomorphism `g` and `b ≁ 3`.

*Claim.*  There is a strictly increasing bi-Lipschitz `g : ℝ → ℝ` (hence a bi-Lipschitz
homeomorphism of `ℝ`) with `g(x)` not normal in base `2` for **every** `x` in the middle-third
Cantor set `K`.  So `g μ` is not pointwise `2`-normal although `2 ≁ 3`, and `g(K)` contains no
`2`-normal number at all.

*English proof.*  Let `F = {y ∈ [0,1] : no hexadecimal digit of y equals 15}`; every point of `F`
misses a base-16 digit, so is not 16-normal, hence not 2-normal.  `F` is closed and
`dim F = log 15 / log 16 > log 2 / log 3 = dim K`.  Gap estimate: if `e ∈ F` is a *left-type* point
`0.w000…` (resp. *right-type* `0.wEEE…`), every complementary gap of `F` at distance `D` to its
right (resp. left) has length `≤ 1.15 D`; hence every window `e + [A r, B r]` (resp. `e − [B r, A r]`)
with `B / A ≥ 2.3` meets `F`, in fact contains points of both types.  Fix `L` with
`(3/2)^L > 40` and work with the level-`nL` intervals `I_u` of `K` (length `3^{-nL}`, `2^L` children
each).  Build nested closed intervals `J_u` with endpoints in `F` (left end left-type, right end
right-type), `diam J_u ∈ [A 3^{-nL}, B 3^{-nL}]` with `B = 2.3 A`, by placing the `2^L` children
of `J_u` in order, each child's endpoints chosen in windows of ratio `≥ 2.3` positioned at the
affine image of the child's position in `I_u`; the budget `2^L · B < 3^L · A / 2` leaves gaps
`≍ 3^{-nL}` between consecutive children and the intermediate `K`-levels inside one block are
handled with constants depending only on `L`.  Set `g(x) = ⋂ J_{u(x)}` on `K` and extend affinely
on each gap of `K` (and outside `[0,1]`).  For `x, y ∈ K` splitting at level `n`, `|g x − g y| ≍
3^{-n}`; each gap of `K` of length `ℓ` maps to a gap of length `≍ ℓ`; since `K` and `g(K)` are
Lebesgue-null, `g(t) − g(s) ≍ t − s` for all `s < t`.  Endpoints lie in the closed set `F`, so
`g(K) ⊆ F`.  (Constants by the gap estimate; no cited input.)

*Why this does not contradict Hochman–Shmerkin.*  `g` is not `C¹`: on `K` its local scale ratio
`|J_u| / |I_u|` wanders in `[A, B]` with no limit, which is exactly the freedom a `C¹` map lacks
(their argument transports sceneries of `μ` at `x` to `f μ` at `f x` through `f′(x)`).

*Confidence.*  Mathematics 85%; not already answered in print 65% (searches logged in the audit);
Lean proof in a few laps 55%. -/
theorem exists_strictMono_biLipschitz_cantorSet_not_isNormal_two :
    ∃ g : ℝ → ℝ, StrictMono g ∧ IsBiLipschitz g ∧ ∀ x ∈ cantorSet, ¬ IsNormal 2 (g x) := by
  sorry

/-- The measure form of the headline: `g_*μ` is not pointwise `2`-normal; `μ`-a.e. `g x` fails. -/
theorem exists_biLipschitz_ae_not_isNormal_two :
    ∃ g : ℝ → ℝ, StrictMono g ∧ IsBiLipschitz g ∧ ∀ᵐ x ∂cantorLebesgue, ¬ IsNormal 2 (g x) := by
  obtain ⟨g, hmono, hbl, hK⟩ := exists_strictMono_biLipschitz_cantorSet_not_isNormal_two
  exact ⟨g, hmono, hbl, ae_mem_cantorSet.mono fun x hx => hK x hx⟩

/-- **Hochman–Shmerkin's `diff¹` stability does not extend to bi-Lipschitz maps.**  Contrast with
`HochmanShmerkinCantorDiff1`, which gives the same conclusion for every `C¹` diffeomorphism and
every `b ≁ 3` (here `b = 2`, `not_multDep_two_three`). -/
theorem not_biLipschitz_stable :
    ¬ ∀ g : ℝ → ℝ, IsBiLipschitz g → ∀ᵐ x ∂cantorLebesgue, IsNormal 2 (g x) := by
  intro h
  obtain ⟨g, -, hbl, hae⟩ := exists_biLipschitz_ae_not_isNormal_two
  have hfalse : ∀ᵐ x ∂cantorLebesgue, False :=
    (h g hbl).mp (hae.mono fun x hx hn => hx hn)
  rw [ae_iff] at hfalse
  simp at hfalse

/-- The headline's map is not a `C¹` diffeomorphism (given Hochman–Shmerkin): the cited theorem
and the headline are consistent only because `g` is genuinely non-smooth. -/
theorem headline_map_not_isC1Diffeo (hHS : HochmanShmerkinCantorDiff1) {g : ℝ → ℝ}
    (hae : ∀ᵐ x ∂cantorLebesgue, ¬ IsNormal 2 (g x)) : ¬ IsC1Diffeo g := by
  intro hg
  have hfalse : ∀ᵐ x ∂cantorLebesgue, False :=
    (hHS g hg 2 le_rfl not_multDep_two_three).mp (hae.mono fun x hx hn => hx hn)
  rw [ae_iff] at hfalse
  simp at hfalse

end NormalNumbers.EntropyProfiles
