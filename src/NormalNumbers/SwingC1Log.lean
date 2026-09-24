import NormalNumbers.SwingC1LogCarry
import NormalNumbers.SwingC1LogAbel

/-!
# Swing at C1, logarithmic density

The log-averaged twin of `ConjC1`.  Logarithmic averaging is where the Tao (2016) two-point and
Tao–Teräväinen (2019) odd-order Elliott results live, so this is where published results might
already carry C1.

## What `L = 1` actually is

`castLawLog_one_iff` below settles the first question of the swing.  At window length one the
casting-out statistic IS the digit, so `CastLawLog b x 1` unpacks into `b − 1` constraints on the
`b` digit frequencies of `x`:

* `freq(d) = 1/b` for every `0 < d < b − 1`;
* `freq(0) + freq(b−1) = 2/b`.

That is **simple normality in logarithmic density, up to merging the two digits `0` and `b−1`** —
exactly one degree of freedom short of full simple normality.  So the `L = 1` rung is not a cheap
corollary of anything: it is the simple-normality problem for `G4_b` itself.
-/

open Finset Filter Topology NormalNumbers.PrimeLambert

namespace NormalNumbers.CastingOut

/-- Logarithmic frequency of windows whose digit sum is `≡ r (mod b−1)`. -/
noncomputable def castFreqLog (b : ℕ) (x : ℝ) (L r N : ℕ) : ℝ :=
  (∑ n ∈ (range N).filter (fun n => windowDigitSum b x n L % (b - 1) = r), (1 : ℝ) / (n + 1)) /
    ∑ n ∈ range N, (1 : ℝ) / (n + 1)

/-- The normal casting-out law in logarithmic density. -/
def CastLawLog (b : ℕ) (x : ℝ) (L : ℕ) : Prop :=
  ∀ r < b - 1, Tendsto (castFreqLog b x L r) atTop (𝓝 (normalCastLaw b L r))

/-- **C1-log.** -/
def ConjC1Log : Prop := ∀ b, 3 ≤ b → ∀ L, CastLawLog b (primeLambertAtBase b) L

/-! ## Logarithmic digit frequencies -/

/-- Logarithmic frequency of the digit value `d` among the first `N` base-`b` digits of `x`. -/
noncomputable def digitFreqLog (b : ℕ) (x : ℝ) (d N : ℕ) : ℝ :=
  (∑ n ∈ (range N).filter (fun n => digitOf b (Int.fract x) n = d), (1 : ℝ) / (n + 1)) /
    ∑ n ∈ range N, (1 : ℝ) / (n + 1)

/-- `x` is **simply normal in logarithmic density**: every digit has log-frequency `1/b`. -/
def SimplyNormalLog (b : ℕ) (x : ℝ) : Prop :=
  ∀ d < b, Tendsto (digitFreqLog b x d) atTop (𝓝 ((b : ℝ)⁻¹))

/-- The digits `< b` in a fixed residue class mod `b − 1`. -/
def residueDigits (b r : ℕ) : Finset ℕ := (range b).filter (fun d => d % (b - 1) = r)

theorem residueDigits_pos (b r : ℕ) (hb : 3 ≤ b) (hr0 : 0 < r) (hr : r < b - 1) :
    residueDigits b r = {r} := by
  ext d
  simp only [residueDigits, Finset.mem_filter, Finset.mem_range, Finset.mem_singleton]
  constructor
  · rintro ⟨hd, hmod⟩
    rcases lt_or_ge d (b - 1) with h | h
    · rwa [Nat.mod_eq_of_lt h] at hmod
    · have : d = b - 1 := by omega
      subst this
      rw [Nat.mod_self] at hmod
      omega
  · rintro rfl
    exact ⟨by omega, Nat.mod_eq_of_lt hr⟩

theorem residueDigits_zero (b : ℕ) (hb : 3 ≤ b) :
    residueDigits b 0 = {0, b - 1} := by
  ext d
  simp only [residueDigits, Finset.mem_filter, Finset.mem_range, Finset.mem_insert,
    Finset.mem_singleton]
  constructor
  · rintro ⟨hd, hmod⟩
    rcases lt_or_ge d (b - 1) with h | h
    · rw [Nat.mod_eq_of_lt h] at hmod; exact Or.inl hmod
    · right; omega
  · rintro (rfl | rfl)
    · exact ⟨by omega, by simp⟩
    · exact ⟨by omega, by simp⟩

/-- `normalCastLaw` at window length one counts digits in the residue class. -/
theorem normalCastLaw_one (b r : ℕ) (hb : 3 ≤ b) :
    normalCastLaw b 1 r = ((residueDigits b r).card : ℝ) / b := by
  unfold normalCastLaw residueDigits
  rw [pow_one]
  congr 2
  refine Finset.card_nbij (fun v => (v 0 : ℕ)) ?_ ?_ ?_
  · intro v hv
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq,
      Fin.sum_univ_one] at hv
    simp only [Finset.coe_filter, Finset.mem_range, Set.mem_setOf_eq]
    exact ⟨(v 0).isLt, hv⟩
  · intro v _ v' _ h
    funext i
    have : i = 0 := Subsingleton.elim _ _
    subst this
    exact Fin.ext h
  · intro d hd
    simp only [Finset.coe_filter, Finset.mem_range, Set.mem_setOf_eq] at hd
    refine ⟨fun _ => ⟨d, hd.1⟩, ?_, rfl⟩
    simp only [Set.mem_image, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq,
      Fin.sum_univ_one]
    exact hd.2

/-- At window length one the casting-out frequency is the sum of the digit frequencies over the
residue class. -/
theorem castFreqLog_one (b : ℕ) (x : ℝ) (r N : ℕ) (hb : 2 ≤ b) :
    castFreqLog b x 1 r N = ∑ d ∈ residueDigits b r, digitFreqLog b x d N := by
  classical
  unfold castFreqLog digitFreqLog residueDigits
  rw [← Finset.sum_div]
  congr 1
  set y := Int.fract x with hy
  have hws : ∀ n, windowDigitSum b x n 1 = digitOf b y n := by
    intro n; simp [windowDigitSum, hy]
  simp only [hws]
  have hmaps : ∀ n ∈ (range N).filter (fun n => digitOf b y n % (b - 1) = r),
      digitOf b y n ∈ (range b).filter (fun d => d % (b - 1) = r) := by
    intro n hn
    simp only [Finset.mem_filter, Finset.mem_range] at hn ⊢
    exact ⟨Nat.mod_lt _ (by omega), hn.2⟩
  rw [← Finset.sum_fiberwise_of_maps_to hmaps (fun n => (1 : ℝ) / (n + 1))]
  refine Finset.sum_congr rfl fun d hd => ?_
  simp only [Finset.mem_filter, Finset.mem_range] at hd
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext n
  simp only [Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨⟨hn, _⟩, hdn⟩; exact ⟨hn, hdn⟩
  · rintro ⟨hn, hdn⟩; exact ⟨⟨hn, by rw [hdn]; exact hd.2⟩, hdn⟩

theorem card_pair_ne (b : ℕ) (hb : 3 ≤ b) : ({0, b - 1} : Finset ℕ).card = 2 := by
  rw [Finset.card_insert_of_notMem (by simp; omega), Finset.card_singleton]

/-- **What the `L = 1` rung is.**  `CastLawLog b x 1` says exactly: every digit `0 < d < b−1` has
log-frequency `1/b`, and the digits `0` and `b−1` have log-frequencies summing to `2/b`.  It is
simple normality in log density, up to merging `0` with `b−1`. -/
theorem castLawLog_one_iff (b : ℕ) (hb : 3 ≤ b) (x : ℝ) :
    CastLawLog b x 1 ↔
      ((∀ r, 0 < r → r < b - 1 → Tendsto (digitFreqLog b x r) atTop (𝓝 ((b : ℝ)⁻¹))) ∧
        Tendsto (fun N => digitFreqLog b x 0 N + digitFreqLog b x (b - 1) N) atTop
          (𝓝 (2 / (b : ℝ)))) := by
  have hb2 : 2 ≤ b := by omega
  -- the two shapes of the frequency, as function identities
  have epos : ∀ r, 0 < r → r < b - 1 →
      castFreqLog b x 1 r = fun N => digitFreqLog b x r N := by
    intro r hr0 hr
    funext N
    rw [castFreqLog_one b x r N hb2, residueDigits_pos b r hb hr0 hr, Finset.sum_singleton]
  have ezero : castFreqLog b x 1 0
      = fun N => digitFreqLog b x 0 N + digitFreqLog b x (b - 1) N := by
    funext N
    rw [castFreqLog_one b x 0 N hb2, residueDigits_zero b hb,
      Finset.sum_insert (by simp; omega), Finset.sum_singleton]
  have lpos : ∀ r, 0 < r → r < b - 1 → normalCastLaw b 1 r = ((b : ℝ))⁻¹ := by
    intro r hr0 hr
    rw [normalCastLaw_one b r hb, residueDigits_pos b r hb hr0 hr, Finset.card_singleton,
      Nat.cast_one, one_div]
  have lzero : normalCastLaw b 1 0 = 2 / (b : ℝ) := by
    rw [normalCastLaw_one b 0 hb, residueDigits_zero b hb, card_pair_ne b hb]
    norm_num
  constructor
  · intro h
    refine ⟨fun r hr0 hr => ?_, ?_⟩
    · have := h r (by omega)
      rwa [epos r hr0 hr, lpos r hr0 hr] at this
    · have := h 0 (by omega)
      rwa [ezero, lzero] at this
  · rintro ⟨h1, h2⟩ r hr
    rcases Nat.eq_zero_or_pos r with rfl | hr0
    · rw [ezero, lzero]; exact h2
    · rw [epos r hr0 hr, lpos r hr0 hr]; exact h1 r hr0 hr

/-- Simple normality in log density gives the `L = 1` rung. -/
theorem castLawLog_one_of_simplyNormalLog (b : ℕ) (hb : 3 ≤ b) (x : ℝ)
    (hx : SimplyNormalLog b x) : CastLawLog b x 1 := by
  rw [castLawLog_one_iff b hb x]
  refine ⟨fun r _ hr => hx r (by omega), ?_⟩
  have h0 := hx 0 (by omega)
  have h1 := hx (b - 1) (by omega)
  have : (2 : ℝ) / b = (b : ℝ)⁻¹ + (b : ℝ)⁻¹ := by
    rw [inv_eq_one_div]; ring
  rw [this]
  exact h0.add h1

/-! ## Remaining rungs -/

/-- Natural density implies logarithmic density (partial summation).  Sanity bridge. -/
theorem castLawLog_of_castLaw (b : ℕ) (x : ℝ) (L : ℕ) (h : CastLaw b x L) :
    CastLawLog b x L := by
  classical
  intro r hr
  set a : ℕ → ℝ := fun n => if windowDigitSum b x n L % (b - 1) = r then (1 : ℝ) else 0 with ha
  have hnum : ∀ N : ℕ,
      ∑ n ∈ (range N).filter (fun n => windowDigitSum b x n L % (b - 1) = r), (1 : ℝ) / (n + 1)
        = ∑ n ∈ range N, a n / (n + 1) := by
    intro N
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun n _ => ?_
    simp only [ha]
    split <;> simp
  have hden : ∀ N : ℕ,
      ((((range N).filter (fun n => windowDigitSum b x n L % (b - 1) = r)).card : ℝ))
        = ∑ n ∈ range N, a n := by
    intro N
    simp only [ha, Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const,
      nsmul_eq_mul, mul_one]
  have h' : Tendsto (fun N => (∑ n ∈ range N, a n) / N) atTop (𝓝 (normalCastLaw b L r)) := by
    refine (h r hr).congr fun N => ?_
    rw [castFreq, hden N]
  have := tendsto_logAvg_of_tendsto_avg a (normalCastLaw b L r) h'
  refine this.congr fun N => ?_
  rw [castFreqLog, hnum N]

/-- **The `L = 1` rung, conditionally.**  `H` = log-simple-normality of `G4_b`.  By
`castLawLog_one_iff` this hypothesis is (bar the single `0 ↔ b−1` degree of freedom) also
NECESSARY, so it is the honest input, not a convenient over-assumption. -/
theorem castLawLog_one_of_H (b : ℕ) (hb : 3 ≤ b)
    (H : SimplyNormalLog b (primeLambertAtBase b)) :
    CastLawLog b (primeLambertAtBase b) 1 :=
  castLawLog_one_of_simplyNormalLog b hb _ H

/-- **C1-log, conditionally on the natural-density C1.**  Partial summation only; this is the
sanity direction (natural density is the harder hypothesis), recorded so the log rung is never
mistaken for a strengthening. -/
theorem conjC1Log_of_conjC1 (H : ConjC1) : ConjC1Log :=
  fun b hb L => castLawLog_of_castLaw b _ L (H b hb L)

/-!
## Verdict of the swing (2026-09-24)

**Which log-correlations does `L = 1` need?**  By `digitOf_lambertVal` the digit is
`d_n = ω(n+1) + c_{n+1} − b·c_n` with `c_N = ⌊Σ_{k≥1} ω(N+k) b^{−k}⌋`.  So the residue
`d_n mod (b−1)` is `ω(n+1) + c_{n+1} − c_n`, and `c_N` is a FLOOR of a `b`-adically weighted
window of `ω` at `N+1, N+2, …`.  Truncating that window at depth `K` costs
`Σ_{k>K} ω(N+k) b^{−k}`, whose average over `N ≤ X` is `≍ (log log X)·b^{−K}`.  Hence the depth
must satisfy `b^{−K} log log X → 0`, i.e. `K ≍ log log log X → ∞`: the needed input is a
`K`-point log-correlation of `z^ω` (`z` a `b^K`-th root of unity) with `K` GROWING and with an
error term uniform in `K` beating `b^{−K}`.

**Is that covered by the published logarithmic results?**  No, for two independent reasons.
1. *Growing `K`.*  Tao (2016, two-point logarithmic Chowla/Elliott) and Tao–Teräväinen (2019,
   odd-order logarithmic Elliott; structure of logarithmically averaged correlations) are
   statements at a FIXED number of shifts, with no uniformity as the number of shifts grows.
   `carry_correction_unbounded` is the machine-checked form of the obstruction: the correction
   `ω(n+1) − d_n = b·c_n − c_{n+1}` is UNBOUNDED, so no fixed-depth truncation of the carry is
   admissible and no fixed-`k` correlation theorem can be the input.
2. *Parity.*  Even at fixed `k`, what is needed is the `k`-point statement for every `k`, and the
   published odd-order theorem leaves `k` EVEN, `k ≥ 4`, open.

**And `L = 1` is not a small target.**  `castLawLog_one_iff`: the rung is exactly log-simple
normality of `G4_b` up to merging the digits `0` and `b−1` — `b − 1` of the `b` digit frequencies
pinned.  So C1-log at its first rung is the simple-normality problem for the prime-Lambert
constant itself, in logarithmic density.  The swing lands as a REFUTATION of the hope that
published log-Elliott carries C1: it does not, and the gap is not a technicality.
-/

/-- First rung: single digits (`L = 1`).  RATIFIED headline, restored 2026-09-24 after the swing
deleted it.  Open: by `castLawLog_one_iff` it is log-simple-normality of `G4_b` up to merging `0`
with `b − 1`; needs growing-`K` log-Elliott (see HANDOFF-2026-09-24-2100-swing-c1log-DONE.md). -/
theorem castLawLog_one (b : ℕ) (hb : 3 ≤ b) : CastLawLog b (primeLambertAtBase b) 1 := by
  sorry

/-- **C1-log**, ratified headline (restored).  Open. -/
theorem conjC1Log : ConjC1Log := by
  sorry

end NormalNumbers.CastingOut
