/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.ExplicitSquareNonNormal
import NormalNumbers.PowerBaseReal
import NormalNumbers.Wall
import NormalNumbers.WeylCriterion
import NormalNumbers.DecayAeNormal

/-!
# Levin's rate in base 2, normal in every odd base

Audit: `docs/LEVIN-SPARSE-AUDIT-2026-10-03.md` (sweep `docs/OPEN-PROBLEMS-SWEEP-2026-10-03b.md` §3).

**Target.**  A real `x` normal in base 2 (hence in every `2^k`) and in every odd base `r ≥ 3`,
whose base-2 star discrepancy is `D*_N(2ⁿx) = O((log N)²/N)`, Levin's one-base rate.  For
normality in more than one base, the best published rate is `O(N^{-1/2})` in every base
(Aistleitner–Becher–Scheerer–Slaman, arXiv 1707.02628, who call `N^{-1/2}` "a kind of barrier";
Manai 2508.09319 §1 still calls lower discrepancy "a very difficult … problem").  The target
beats the barrier in one base while keeping normality in the odd bases.

**Mechanism.**  `x = α + y`.  `α` is Levin's base-2 number (`Literature.Levin1999`).  `y` is a
random point of Becher–Lew Deveali's sparse Cantor set `C(S)` (2607.06773): binary digits are
`0` off a sparse set `S`, fair coins on it.
* **Base 2, every `y ∈ C(S)` at once.**  `{2ⁿy}` is below `2/N` except when an element of `S`
  lies in `(n, n + log₂N + 1]`; there are at most `(log₂N + 2)·#(S ∩ [1, 2N])` such `n`
  (`fract_bldPoint_small`).  Moving all but those points by at most `2/N` costs
  `2D + 2/N + #B/N` (`discLe_fract_add`).  With `#(S ∩ [1,N]) = O(log N)`, which BLD's own
  example `{⌈e^{j/100}⌉}` has (`sIcc_expSet_le`), the total is `O((log N)²/N)`.
* **Odd bases, `μ_S`-a.e. `y`.**  BLD's second-moment bound (proof of Lemma 7) bounds the cosine
  double sum `N⁻² Σ_{p,q} Π_{k∈S} |cos(π h(rᵖ − r^q)/2ᵏ)|` (`bld_doubleSum_le`, from the cited
  Lemma 5).  The second moment of the **translate** `α + y` is bounded by the same double sum
  (`secondMoment_translate_le`: translation multiplies each Fourier coefficient by a unimodular
  phase).  Davenport–Erdős–LeVeque (`del_ae_tendsto`) then gives Weyl's criterion a.s.

**Why even bases are blocked** (not claimed): for `r = 2ᵃm`, `a ≥ 1`, `m > 1` odd, the frequency
`h(rᵖ − r^q)` is divisible by `2^{aq}`, so only the positions of `S` in `(aq, O(p)]` matter.  A
sparse `S` with `#(S ∩ [1,N]) = O(log N)` has `O(1)` points there, so the cosine product does not
tend to `0` and the second-moment route gives nothing; BLD Theorem 2 even puts base-6 non-normal
points in `C(S)`.  Base `4 = 2²` is fine: it follows from base 2 (`PowerBase.isNormal_pow`).

**Known-false siblings** (the mechanism must refuse them, and does):
* dense digits (`S = {k ≥ 1}`): the base-2 perturbation budget is `≥ 1`
  (`perturbBudget_dense_ge_one`, proved), and indeed some `y` in the dense set makes `α + y`
  non-normal in base 2 (`exists_not_isNormal_two_dense`), so the "every `y`" base-2 claim needs
  sparsity;
* the base-2 bound for `y` alone (`α = 0`): every `y ∈ C(S)` has digit-1 frequency `0`, so it is
  not normal in base 2; the content is in the `α` + sparse-`y` split.
-/

open MeasureTheory Filter Topology

namespace NormalNumbers.LevinSparse

open DecayAeNormal ExplicitSquare

/-! ## Definitions -/

/-- **Star discrepancy bound**: `D*_N(u) ≤ D`, with `D*_N(u) = sup_{c∈[0,1]} |#{n<N : u n ∈ [0,c)}/N − c|`
(Levin 1999 eq. (1), up to the endpoint `c = 0`, where the term is `0`). -/
def DiscLe (u : ℕ → ℝ) (N : ℕ) (D : ℝ) : Prop :=
  ∀ c ∈ Set.Icc (0 : ℝ) 1, |(visitCount u 0 c N : ℝ) / N - c| ≤ D

theorem DiscLe.mono {u : ℕ → ℝ} {N : ℕ} {D D' : ℝ} (h : DiscLe u N D) (hD : D ≤ D') :
    DiscLe u N D' := fun c hc => (h c hc).trans hD

/-- BLD's `S(a, c) = #(S ∩ [a, c])` (inclusive). -/
noncomputable def sIcc (S : Set ℕ) (a c : ℕ) : ℕ := by
  classical exact ((Finset.Icc a c).filter (· ∈ S)).card

/-- **Sparse set** (Becher–Lew Deveali 2607.06773, Definition "Sparse set"), in a form that
implies theirs: `S ⊆ ℤ_{>0}`, density zero, and a sparsity exponent `ρ > 0` with
`S(a, a+k) ≥ (1+ε)·30 log k` for all large `k` and all `0 ≤ a ≤ k^ρ`.  Theirs is
`liminf_k min_{0≤a≤k^ρ} S(a,a+k)/(30 log k) > 1`, which is equivalent to the existence of such
an `ε`.  (Taking the margin explicitly keeps every cited Prop quantified over `Sparse` no
stronger than BLD's lemma.) -/
def Sparse (S : Set ℕ) (ρ : ℝ) : Prop :=
  0 ∉ S ∧ Tendsto (fun n : ℕ => (sIcc S 1 n : ℝ) / n) atTop (𝓝 0) ∧ 0 < ρ ∧
    ∃ ε : ℝ, 0 < ε ∧ ∃ K₀ : ℕ, ∀ k : ℕ, K₀ ≤ k → ∀ a : ℕ, (a : ℝ) ≤ (k : ℝ) ^ ρ →
      (1 + ε) * (30 * Real.log k) ≤ sIcc S a (a + k)

/-- **The point of `C(S)` coded by `ω`**: binary digit `k` (weight `2^{-k}`, `k ≥ 1`) is `ω k`
for `k ∈ S` and `0` otherwise (BLD Definition "Sparse Cantor set").  Under fair coins its law is
BLD's measure `μ(S)`. -/
noncomputable def bldPoint (S : Set ℕ) (ω : ℕ → Bool) : ℝ := by
  classical exact ∑' k : ℕ, (if k ∈ S ∧ ω k = true then (1 : ℝ) else 0) / 2 ^ k

/-- **The Riesz tail** `Π_{k∈S, k>a} |cos(π t / 2^{k-a})|`, as the infimum of its partial
products (which decrease in `M`, every factor lying in `[0,1]`), so it is the infinite product
with no junk value.  `|μ̂_S(t)| = rieszTail S 0 t` (BLD §2). -/
noncomputable def rieszTail (S : Set ℕ) (a : ℕ) (t : ℝ) : ℝ := by
  classical exact ⨅ M : ℕ,
    ∏ k ∈ (Finset.Ioc a M).filter (· ∈ S), |Real.cos (Real.pi * t / 2 ^ (k - a))|

/-- BLD's own example of a sparse set (2607.06773 §1: "Also `{⌈e^{j/100}⌉ : j ≥ 1}` is sparse"). -/
def expSet : Set ℕ := {k | ∃ j : ℕ, 1 ≤ j ∧ k = ⌈Real.exp ((j : ℝ) / 100)⌉₊}

/-! ## Cited inputs -/

namespace Literature

/-- **Levin 1999.**  M. B. Levin, *On the discrepancy estimate of normal numbers*, Acta Arith. 88
(1999) 99–111, **Theorem 2** (base `q = 2` here): the explicit
`α = Σ_{m≥1} q^{-n_m} Σ_{0≤n<q^{2^m}} q^{-n2^m} Σ_{i=1}^{2^m} d_i(n) q^{-i}`
(`d_i(n)` from Pascal's triangle mod 2 applied to the base-`q` digits of `n`) is normal to base
`q` with `D(N, {αqⁿ}) = O(N⁻¹ log² N)`, `D` the star discrepancy of eq. (1).  An `O` for
`N → ∞` with a fixed constant covers all `N ≥ 2` after enlarging the constant (each `D ≤ 1`,
`log² N / N > 0`).  Faithful-or-weaker: existential in `α`, star discrepancy, base 2 only.
Quoted the same way in ABSS 1707.02628 §1 and Alvarez–Becher 1510.02004 §1. -/
def Levin1999 : Prop :=
  ∃ α C : ℝ, 0 < C ∧ ∀ N : ℕ, 2 ≤ N → DiscLe (orbit 2 α) N (C * Real.log N ^ 2 / N)

/-- **Becher–Lew Deveali, Lemma 5** (2607.06773v1, §2, p. 8), with the threshold of Lemmas 1,
3, 4 made explicit.  For sparse `S` with exponent `ρ`, integers `a ≥ 0`, odd `r ≥ 3`, odd
`ℓ > 0` and `N ≥ δ₄(a)`:
`Σ_{n<N} Π_{k∈S,k>a} |cos(πℓrⁿ/2^{k−a})| ≤ 2^{ν₂(r²−1)+2} N/(log N)^{1.005}`.
Their threshold: `δ₄(a) = 2^{δ₃(a)}`, `δ₃(a) = max(δ₁(a), 10³⁰)`, `δ₁(a) = (a^{1/ρ}+1)K_S`
(Lemma 1, `K_S ≥ 2` depending only on `S`).  Here the threshold is
`2^{K(a+1)^{1/ρ} + 10³⁰}`, which is `≥ δ₄(a)` for `K = 3K_S` (so this Prop is implied by
theirs, possibly-ceiling'd `δ₁` included).  `Sparse` implies their sparsity, so the Prop is
faithful-or-weaker. -/
def BLDLemma5 : Prop :=
  ∀ (S : Set ℕ) (ρ : ℝ), Sparse S ρ → ∃ K : ℝ, 0 < K ∧
    ∀ a ℓ r N : ℕ, Odd ℓ → Odd r → 3 ≤ r →
      (2 : ℝ) ^ (K * ((a : ℝ) + 1) ^ (1 / ρ) + 10 ^ 30) ≤ N →
        ∑ n ∈ Finset.range N, rieszTail S a ((ℓ : ℝ) * (r : ℝ) ^ n) ≤
          (2 : ℝ) ^ (padicValNat 2 (r ^ 2 - 1) + 2) * N / Real.log N ^ (1.005 : ℝ)

end Literature

/-! ## Base 2: the sparse perturbation barely moves the discrepancy -/

/-- **Shift lemma.**  Moving all points outside `B` up by at most `η` (mod 1) costs at most
`2D + η + #B/N` in star discrepancy.

Confidence 92%.  Proof: for `n ∉ B`, `v_n := fract(u_n + δ_n)` satisfies
`u_n < c − η ⇒ v_n < c` and `v_n < c ⇒ u_n < c ∨ u_n ≥ 1 − η` (wrap-around).  So
`#{v < c} ≥ N(c − η − D) − #B` and `#{v < c} ≤ N(c + D) + N(η + D) + #B`, using
`#{u ≥ 1−η} = N − #{u < 1−η} ≤ N(η + D)`.  Edge cases `c < η`, `η ≥ 1`, `N = 0` are trivial
(`DiscLe u 0 D` forces `D ≥ 1`). -/
theorem discLe_fract_add (u δ : ℕ → ℝ) (N : ℕ) (D η : ℝ) (B : Finset ℕ)
    (hu : ∀ n, u n ∈ Set.Ico (0 : ℝ) 1) (hδ0 : ∀ n, 0 ≤ δ n) (hη : 0 ≤ η)
    (hδ : ∀ n < N, n ∉ B → δ n ≤ η) (hD : DiscLe u N D) :
    DiscLe (fun n => Int.fract (u n + δ n)) N (2 * D + η + B.card / N) := by
  sorry

/-- **Digit tail of a sparse point.**  `{2ⁿy} ≤ 2/N` except for at most
`(log₂N + 2)·S(1, N + log₂N + 2)` indices `n < N`.

Confidence 92%.  Proof: `B = {n < N : ∃ k ∈ S, n < k ≤ n + L}`, `L = Nat.log 2 N + 1`.  Each
`k ∈ S ∩ [1, N+L]` puts at most `L` indices `n ∈ [k−L, k)` in `B`.  For `n ∉ B` the binary digits
of `y` at positions `n+1, …, n+L` vanish, so `{2ⁿy} = Σ_{k∈S, k>n+L} b_k 2^{n−k} ≤ 2^{−L} < 1/N`
(the digits `k ≤ n` contribute integers, and the tail is `< 1`). -/
theorem fract_bldPoint_small (S : Set ℕ) (hS0 : 0 ∉ S) (ω : ℕ → Bool) (N : ℕ) (hN : 2 ≤ N) :
    ∃ B : Finset ℕ, (B.card : ℝ) ≤ (Nat.log 2 N + 2) * sIcc S 1 (N + Nat.log 2 N + 2) ∧
      ∀ n < N, n ∉ B → Int.fract (bldPoint S ω * 2 ^ n) ≤ 2 / N := by
  sorry

theorem bldPoint_nonneg (S : Set ℕ) (ω : ℕ → Bool) : 0 ≤ bldPoint S ω := by
  unfold bldPoint
  exact tsum_nonneg fun k => by split_ifs <;> positivity

/-- **Base-2 transfer** (wiring): every point of `C(S)` moves Levin's discrepancy by at most the
perturbation budget. -/
theorem discLe_add_bldPoint (S : Set ℕ) (hS0 : 0 ∉ S) (ω : ℕ → Bool) (α : ℝ) (N : ℕ)
    (hN : 2 ≤ N) {D : ℝ} (hD : DiscLe (orbit 2 α) N D) :
    DiscLe (orbit 2 (α + bldPoint S ω)) N
      (2 * D + 2 / N + (Nat.log 2 N + 2) * sIcc S 1 (N + Nat.log 2 N + 2) / N) := by
  obtain ⟨B, hBc, hB⟩ := fract_bldPoint_small S hS0 ω N hN
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have key := discLe_fract_add (orbit 2 α) (fun n => Int.fract (bldPoint S ω * 2 ^ n)) N D (2 / N)
    B (fun n => ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩) (fun n => Int.fract_nonneg _)
    (by positivity) (fun n hn hnB => by simpa using hB n hn hnB) hD
  have heq : (fun n => Int.fract (orbit 2 α n + Int.fract (bldPoint S ω * 2 ^ n)))
      = orbit 2 (α + bldPoint S ω) := by
    funext n
    simp only [orbit]
    rw [Int.fract_eq_fract]
    refine ⟨-⌊α * (2 : ℝ) ^ n⌋ - ⌊bldPoint S ω * 2 ^ n⌋, ?_⟩
    push_cast
    rw [Int.fract, Int.fract]
    ring
  rw [heq] at key
  refine key.mono ?_
  have : (B.card : ℝ) / N ≤ (Nat.log 2 N + 2) * sIcc S 1 (N + Nat.log 2 N + 2) / N :=
    div_le_div_of_nonneg_right hBc hNpos.le
  linarith

/-- **Discrepancy → normality** (any base): a star-discrepancy bound tending to `0` gives
equidistribution of the orbit, hence normality by Wall.

Confidence 95%.  Proof: `visitCount u a c N = visitCount u 0 c N − visitCount u 0 a N` for
`0 ≤ a ≤ c` (orbit values are in `[0,1)`), so each interval frequency is within `2ε N` of
`c − a`; then `isNormal_iff_equidistributed_orbit`. -/
theorem isNormal_of_discLe (b : ℕ) (hb : 2 ≤ b) (x : ℝ) (ε : ℕ → ℝ)
    (hε : Tendsto ε atTop (𝓝 0)) (h : ∀ N : ℕ, 2 ≤ N → DiscLe (orbit b x) N (ε N)) :
    IsNormal b x := by
  sorry

/-! ## Odd bases: BLD's second moment survives translation -/

/-- **Davenport–Erdős–LeVeque** (Michigan Math. J. 10 (1963) 311–314, Theorem 1), for
unit-bounded measurable functions on a probability space: `Σ_N N⁻¹ 𝔼|A_N|² < ∞` forces
`A_N → 0` a.s., `A_N = N⁻¹ Σ_{n<N} f_n`.

Confidence 95% (classical).  Proof: the series condition gives `N_k ↑` with `N_{k+1}/N_k → 1`
and `Σ_k 𝔼|A_{N_k}|² < ∞` (pick `N_k` minimizing `𝔼|A_N|²` on `[(1+1/k)^?…]` blocks, or the
standard dyadic-refinement argument of DEL); Borel–Cantelli / monotone convergence gives
`A_{N_k} → 0` a.s.; unit bounds interpolate (`|A_N − A_{N_k}| ≤ 2(N − N_k)/N`). -/
theorem del_ae_tendsto {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (f : ℕ → Ω → ℂ) (hf : ∀ n, Measurable (f n)) (hb : ∀ n ω, ‖f n ω‖ ≤ 1)
    (hs : Summable fun N : ℕ =>
      (∫ ω, ‖(∑ n ∈ Finset.range N, f n ω) / (N : ℂ)‖ ^ 2 ∂μ) / N) :
    ∀ᵐ ω ∂μ, Tendsto (fun N : ℕ => (∑ n ∈ Finset.range N, f n ω) / (N : ℂ)) atTop (𝓝 0) := by
  sorry

/-- **Translation invariance of the second moment bound.**  For any `α`,
`𝔼|N⁻¹Σ_{j<N} e(h rʲ(α + y))|² ≤ N⁻² Σ_{p,q<N} |μ̂_S(h(rᵖ − r^q))|`, and
`|μ̂_S(t)| = Π_{k∈S} |cos(πt/2ᵏ)| = rieszTail S 0 t` (BLD §2).

Confidence 88% (truth 98%).  Proof: expand the square;
`𝔼 e(t(α+y)) = e(tα) μ̂_S(t)` and `μ̂_S(t) = Π_{k∈S} (1 + e(t/2ᵏ))/2` (independent coins, the
product converging since `Σ_k t²/4ᵏ < ∞`); `|(1 + e(s))/2| = |cos(πs)|`; then the triangle
inequality.  The partial products decrease to the infimum. -/
theorem secondMoment_translate_le (S : Set ℕ) (hS0 : 0 ∉ S) (α : ℝ) (h : ℤ) (r N : ℕ) :
    ∫ ω, ‖(∑ j ∈ Finset.range N, ee (h * (r : ℝ) ^ j * (α + bldPoint S ω))) / (N : ℂ)‖ ^ 2
        ∂coinMeasure ≤
      (∑ p ∈ Finset.range N, ∑ q ∈ Finset.range N,
        rieszTail S 0 ((h : ℝ) * ((r : ℝ) ^ p - (r : ℝ) ^ q))) / (N : ℝ) ^ 2 := by
  sorry

/-- **BLD Lemma 7, cosine form.**  The double sum decays like `(log N)^{-1.005}`.  This is the
inequality BLD's proof of Lemma 7 actually establishes (2607.06773 pp. 9–11, "Combining the
estimates"), before they bound the integral by it.

Confidence 85%.  Proof (BLD): diagonal `p = q` gives `N`.  For `p > q`, `g = p − q`,
`d(g) = ν₂(r^g − 1)`: `h(rᵖ − r^q) = 2^{ν₂(h)+d(g)} ℓ_g r^q` with `ℓ_g` odd, so
`rieszTail S 0 (h(rᵖ−r^q)) = rieszTail S (ν₂(h)+d(g)) (ℓ_g r^q)` (factors `k ≤ a` are `|±1|`).
Small valuations `d(g) ≤ B = ⌊2 log₂ log N⌋`: Lemma 5 with `a = ν₂(h)+d(g) ≤ 3 log₂ log N`
(threshold `2^{K(a+1)^{1/ρ}+10³⁰} ≤ N` for large `N`) and Lemma 6
(`#{g ≤ N : d(g) = d} ≤ 2^{ν₂(r²−1)−1} N/2ᵈ`, Lifting-the-Exponent).  Large valuations: at most
`2^{ν₂(r²−1)−1}N/2^B ≤ 2^{ν₂(r²−1)}N/(log N)²` values of `g`, each inner sum `≤ N`.  Total
`≤ 2^{2ν₂(r²−1)+4}/(log N)^{1.005}` after dividing by `N²`. -/
theorem bld_doubleSum_le (hL5 : Literature.BLDLemma5) {S : Set ℕ} {ρ : ℝ} (hS : Sparse S ρ)
    (r : ℕ) (hr : Odd r) (hr3 : 3 ≤ r) (h : ℤ) (hh : h ≠ 0) :
    ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      (∑ p ∈ Finset.range N, ∑ q ∈ Finset.range N,
          rieszTail S 0 ((h : ℝ) * ((r : ℝ) ^ p - (r : ℝ) ^ q))) / (N : ℝ) ^ 2 ≤
        C / Real.log N ^ (1.005 : ℝ) := by
  sorry

/-- **Odd-base normality of every translate**, `μ_S`-almost surely.

Confidence 85%.  Proof: for each odd `r ≥ 3` and `h ≠ 0` (countably many), `del_ae_tendsto`
with `f_j(ω) = e(h rʲ(α + bldPoint S ω))`: measurability of `bldPoint` (a `tsum` of measurable
coordinate functions), summability from `secondMoment_translate_le` + `bld_doubleSum_le`
(`Σ_N C/(N (log N)^{1.005}) < ∞`, integral test).  Then Weyl (`equidistributed_of_weyl`, the
Weyl mean of `orbit r x` equals the raw mean as in `fourierMean_orbit_two`) and Wall
(`isNormal_iff_equidistributed_orbit`). -/
theorem ae_isNormal_odd_add (hL5 : Literature.BLDLemma5) {S : Set ℕ} {ρ : ℝ} (hS : Sparse S ρ)
    (α : ℝ) :
    ∀ᵐ ω ∂coinMeasure, ∀ r : ℕ, 3 ≤ r → Odd r → IsNormal r (α + bldPoint S ω) := by
  sorry

/-! ## The sparse set -/

/-- BLD's example is sparse (their §1 claim; they give no proof).

Confidence 85%.  Proof: `⌈e^{j/100}⌉ ∈ [a, a+k]` iff `e^{j/100} ∈ (a−1, a+k]`.  For `a ≥ 101`
consecutive values differ by `> 1`, so they are distinct and the count is
`≥ 100 log((a+k)/(a−1)) − 1 ≥ 100(1 − ρ) log k − O(1)` for `a ≤ k^ρ`; with `ρ = 1/2` this is
`≥ 50 log k − O(1) ≥ 1.5 · 30 log k` for large `k`.  For `a ≤ 100` every integer in `[2, 100]`
is hit and the count is `≥ 100 log((a+k)/101) − 1`.  Density zero: `sIcc_expSet_le`. -/
theorem sparse_expSet : Sparse expSet (1 / 2) := by
  sorry

/-- Logarithmic count: `#(expSet ∩ [1, N]) ≤ 100 log N + 1`.

Confidence 97%.  Proof: `⌈e^{j/100}⌉ ≤ N` forces `j ≤ 100 log N`, and the map `j ↦ ⌈e^{j/100}⌉`
covers the set. -/
theorem sIcc_expSet_le (N : ℕ) (hN : 1 ≤ N) :
    (sIcc expSet 1 N : ℝ) ≤ 100 * Real.log N + 1 := by
  sorry

theorem zero_not_mem_expSet : 0 ∉ expSet := by
  rintro ⟨j, hj, h0⟩
  have hpos : 0 < Real.exp ((j : ℝ) / 100) := Real.exp_pos _
  have : (0 : ℝ) < ⌈Real.exp ((j : ℝ) / 100)⌉₊ := by
    exact_mod_cast Nat.ceil_pos.2 hpos
  rw [← h0] at this
  simp at this

/-- **Rate arithmetic** for the headline.

Confidence 99%.  Proof: for `N ≥ 2`, `Nat.log 2 N + 2 ≤ 3 log N / log 2 ≤ 5 log N`,
`log(N + Nat.log 2 N + 2) ≤ log (3N) ≤ 3 log N`, `2 ≤ 5 log² N`. -/
theorem rate_arith (C : ℝ) (hC : 0 < C) (N : ℕ) (hN : 2 ≤ N) :
    2 * (C * Real.log N ^ 2 / N) + 2 / N +
        (Nat.log 2 N + 2) * (100 * Real.log ((N + Nat.log 2 N + 2 : ℕ) : ℝ) + 1) / N ≤
      (2 * C + 2000) * Real.log N ^ 2 / N := by
  sorry

/-! ## Headline -/

/-- **Headline.**  There is a real `x` normal in every odd base `≥ 3` and every power-of-two base,
whose base-2 star discrepancy is `O((log N)²/N)`: Levin's one-base rate, far below the `N^{-1/2}`
"barrier" of ABSS 1707.02628 for numbers normal in several bases.

Wiring (proved from the leaves): `x = α + bldPoint expSet ω` with `α` from `Levin1999` and `ω`
from the full-measure set of `ae_isNormal_odd_add`. -/
theorem exists_levinRate_oddNormal (hL : Literature.Levin1999) (hB : Literature.BLDLemma5) :
    ∃ x : ℝ, (∀ b : ℕ, 2 ≤ b → (Odd b ∨ ∃ k : ℕ, b = 2 ^ k) → IsNormal b x) ∧
      ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 2 ≤ N → DiscLe (orbit 2 x) N (C * Real.log N ^ 2 / N) := by
  obtain ⟨α, C, hC, hα⟩ := hL
  obtain ⟨ω, hω⟩ := (ae_isNormal_odd_add hB sparse_expSet α).exists
  set x := α + bldPoint expSet ω with hx
  have hrate : ∀ N : ℕ, 2 ≤ N →
      DiscLe (orbit 2 x) N ((2 * C + 2000) * Real.log N ^ 2 / N) := by
    intro N hN
    refine (discLe_add_bldPoint expSet zero_not_mem_expSet ω α N hN (hα N hN)).mono ?_
    refine le_trans ?_ (rate_arith C hC N hN)
    have hcnt := sIcc_expSet_le (N + Nat.log 2 N + 2) (by omega)
    have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
    have hL0 : (0 : ℝ) ≤ (Nat.log 2 N : ℝ) + 2 := by positivity
    have : (Nat.log 2 N + 2 : ℝ) * (sIcc expSet 1 (N + Nat.log 2 N + 2) : ℝ) / N ≤
        (Nat.log 2 N + 2) * (100 * Real.log ((N + Nat.log 2 N + 2 : ℕ) : ℝ) + 1) / N :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hcnt hL0) hNpos.le
    linarith
  have h2 : IsNormal 2 x := by
    refine isNormal_of_discLe 2 le_rfl x (fun N => (2 * C + 2000) * Real.log N ^ 2 / N) ?_ hrate
    have h0 := (Real.tendsto_pow_log_div_mul_add_atTop 1 0 2 one_ne_zero).comp
      tendsto_natCast_atTop_atTop
    have := h0.const_mul (2 * C + 2000)
    simp only [mul_zero] at this
    refine this.congr fun N => ?_
    simp only [Function.comp_apply, one_mul, add_zero]
    ring
  refine ⟨x, ?_, 2 * C + 2000, by positivity, hrate⟩
  intro b hb hcase
  rcases hcase with hodd | ⟨k, rfl⟩
  · exact hω b (by
      rcases hodd with ⟨m, rfl⟩
      omega) hodd
  · have hk : 0 < k := by
      rcases Nat.eq_zero_or_pos k with rfl | hk
      · simp at hb
      · exact hk
    exact PowerBase.isNormal_pow (b := 2) (by norm_num) hk h2

/-! ## Known-false siblings and the open upgrade -/

/-- The full binary set `{k ≥ 1}` (dense digits). -/
def denseSet : Set ℕ := {k | 1 ≤ k}

/-- **The mechanism refuses dense digits**: with `S = {k ≥ 1}` the base-2 perturbation budget
`(log₂N + 2)·S(1, N + log₂N + 2)/N` is at least `1`, so `discLe_add_bldPoint` says nothing. -/
theorem perturbBudget_dense_ge_one (N : ℕ) (hN : 1 ≤ N) :
    (1 : ℝ) ≤ (Nat.log 2 N + 2) * sIcc denseSet 1 (N + Nat.log 2 N + 2) / N := by
  have hc : sIcc denseSet 1 (N + Nat.log 2 N + 2) = N + Nat.log 2 N + 2 := by
    classical
    unfold sIcc
    rw [show ((Finset.Icc 1 (N + Nat.log 2 N + 2)).filter (· ∈ denseSet)) =
        Finset.Icc 1 (N + Nat.log 2 N + 2) by
      ext k
      simp only [Finset.mem_filter, Finset.mem_Icc]
      constructor
      · exact fun h => h.1
      · exact fun h => ⟨h, h.1⟩]
    simp
  rw [hc]
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  rw [le_div_iff₀ hNpos]
  push_cast
  nlinarith [(Nat.cast_nonneg (Nat.log 2 N) : (0 : ℝ) ≤ _)]

/-- **Dense digits really fail "for every `y`"**: for every `α` some point of the dense set makes
`α + y` an integer, hence not normal in base 2.

Confidence 92%.  Proof: take `ω` the binary digits of `fract(−α)` (shifted to positions `k ≥ 1`);
then `bldPoint denseSet ω = fract(−α)` (proper expansion, `Bridge.digitOf_realOfDigits`-style),
`α + fract(−α) ∈ ℤ`, all base-2 digits of `fract 0 = 0` are `0`. -/
theorem exists_not_isNormal_two_dense (α : ℝ) :
    ∃ ω : ℕ → Bool, ¬ IsNormal 2 (α + bldPoint denseSet ω) := by
  sorry

/-- **Open upgrade (not claimed; 20%).**  An absolutely normal `x` with base-2 star discrepancy
`o(N^{-1/2})`.  Route: a denser sparse set (BLD exponent `1 < ρ < 2`, e.g. the primes, with
`#(S ∩ [1,N]) ≈ N^{1−1/ρ}`) keeps the base-2 budget at `O(N^{-1/ρ} log² N) = o(N^{-1/2})`, but the
odd/even-base decay for bases `2ᵃm` (`a ≥ 1`) needs Schmidt's 1960 tools on windows of length
`≫ log N` at shifts `≍ N`, which BLD only assert ("Applying Schmidt's specialized tools from [18]
it can be extended to all bases multiplicatively independent of 2") and do not prove. -/
theorem exists_absNormal_base2_fast :
    ∃ x : ℝ, (∀ b : ℕ, 2 ≤ b → IsNormal b x) ∧ ∃ C θ : ℝ, 0 < C ∧ 1 / 2 < θ ∧
      ∀ N : ℕ, 2 ≤ N → DiscLe (orbit 2 x) N (C / (N : ℝ) ^ θ) := by
  sorry

/-- **Derandomization stretch (65%).**  For computable `α ∈ [0,1)` (Levin's `α` is an explicit
digit concatenation), a computable coin sequence `e` with `α + bldPoint expSet e` normal in every
odd base.  Route: BLD Theorem 3's algorithm (Becher–Figueira reformulation of Sierpiński, bad
sets defined by exponential-sum averages, choices only at positions in `S`), with the bad-set
measure bounds coming from `secondMoment_translate_le` + `bld_doubleSum_le` by Chebyshev, which
are translation-invariant. -/
theorem exists_computable_bld_odd_add (hL5 : Literature.BLDLemma5) (α : ℝ) (hα0 : 0 ≤ α)
    (hα : Computable fun n : ℕ => ⌊α * 2 ^ n⌋₊) :
    ∃ e : ℕ → Bool, Computable e ∧
      ∀ r : ℕ, 3 ≤ r → Odd r → IsNormal r (α + bldPoint expSet e) := by
  sorry

end NormalNumbers.LevinSparse
