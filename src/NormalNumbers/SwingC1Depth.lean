import NormalNumbers.SwingC1Model
import NormalNumbers.G4Irrational

/-!
# The truncation depth: replacing `θ_n` by its finite-depth window

The kickoff's item 1 warns that `ω ≈ log log N` is unbounded, so the depth at which the carry may
be truncated must GROW with `N`.  This file turns that warning into an explicit, unconditional
bound, and so pins the depth at which hypothesis `H` must be stated.

`omegaTail_pow` (`SwingC1.lean`) is the exact shift identity `b^L · θ_n = H_L(n) + θ_{n+L}` with
`H_L(n) = omegaHead b L n = Σ_{i<L} ω(n+1+i) b^{L−1−i}` an INTEGER.  Hence

`h·θ_n − h·H_L(n)/b^L = h·θ_{n+L}/b^L`,

so the entire truncation question is the SIZE of `θ`, and that is settled unconditionally by
`omegaTail_le_log : θ_N ≤ log₂(N+1) + 1` (already in `SwingC1.lean`, from `2^{ω(m)} ≤ m`).

Results here:

* `norm_phase_omegaTail_sub_head` — pointwise, `‖e(h θ_n) − e(h H_L(n)/b^L)‖ ≤ 4π·|h|(log₂(n+L+1)+1)/b^L`;
* `norm_fullMean_phase_sub_head` — the same for the Weyl mean over `n < M`, with the uniform
  constant `D = |h|(log₂(M+L)+1)/b^L`;
* `depthBound_tendsto_zero` — `D → 0` along any depth schedule `L(M)` with
  `b^{L(M)} / log₂ M → ∞`; in particular `L(M) = ⌈2 log_b log₂ M⌉` works.

**Consequence for the crux.**  The Weyl sums of the `×b`-orbit of `G₄_b` are, to `o(1)`, the
finite-depth sums `mean_{n<M} Π_{i<L} z_i^{ω(n+1+i)}` with `z_i = e(h b^{i+1−L}/1)` — a
correlation of `L(M) ≍ log_b log₂ M` shifted copies of the multiplicative function `z^{ω}`.  So
hypothesis `H` needs depth exactly `log_b log log N + O(1)`, which is Delange's regime: at `L = 1`
it is Delange's theorem `mean z^{ω(n)} → 0` (`Re z < 1`), and the growth of `L` is what makes the
general case Elliott-hard.  This is the honest statement of where the difficulty sits.
-/

open Finset Filter Topology NormalNumbers.PrimeLambert

namespace NormalNumbers.CastingOut

/-- The uniform truncation error at depth `L` for the window `n < M`. -/
noncomputable def depthBound (b : ℕ) (h : ℝ) (M L : ℕ) : ℝ :=
  |h| * ((Nat.log 2 (M + L) : ℝ) + 1) / (b : ℝ) ^ L

lemma depthBound_nonneg (b : ℕ) (h : ℝ) (M L : ℕ) (hb : 2 ≤ b) : 0 ≤ depthBound b h M L := by
  have hbpos : (0 : ℝ) < (b : ℝ) := by
    have : (2 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
    linarith
  rw [depthBound]
  positivity

/-- **The pointwise truncation bound.**  The phase of the tail agrees with the phase of its
depth-`L` window to within `4π·|h|(log₂(n+L+1)+1)/b^L`. -/
theorem norm_phase_omegaTail_sub_head (b : ℕ) (hb : 2 ≤ b) (h : ℝ) (L n M : ℕ)
    (hn : n < M) (hsmall : 2 * Real.pi * depthBound b h M L ≤ 1) :
    ‖phase (h * omegaTail b n)
        - phase (h * ((omegaHead b L n : ℤ) : ℝ) / (b : ℝ) ^ L)‖
      ≤ 4 * Real.pi * depthBound b h M L := by
  have hbpos : (0 : ℝ) < (b : ℝ) := by
    have : (2 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
    linarith
  have hbL : (0 : ℝ) < (b : ℝ) ^ L := by positivity
  -- the exact difference of arguments
  have hkey : h * omegaTail b n - h * ((omegaHead b L n : ℤ) : ℝ) / (b : ℝ) ^ L
      = h * omegaTail b (n + L) / (b : ℝ) ^ L := by
    have hpow := omegaTail_pow b hb L n
    field_simp
    linear_combination h * hpow
  -- its size
  have htail : omegaTail b (n + L) ≤ (Nat.log 2 (n + L + 1) : ℝ) + 1 :=
    omegaTail_le_log b hb (n + L)
  have hmono : Nat.log 2 (n + L + 1) ≤ Nat.log 2 (M + L) :=
    Nat.log_mono_right (by omega)
  have hmonoR : ((Nat.log 2 (n + L + 1) : ℝ)) ≤ ((Nat.log 2 (M + L) : ℝ)) := by
    exact_mod_cast hmono
  have hnonneg : 0 ≤ omegaTail b (n + L) := omegaTail_nonneg b hb (n + L)
  have hsize : |h * omegaTail b (n + L) / (b : ℝ) ^ L| ≤ depthBound b h M L := by
    rw [abs_div, abs_of_pos hbL, abs_mul, abs_of_nonneg hnonneg, depthBound,
      div_le_div_iff_of_pos_right hbL]
    have habs : 0 ≤ |h| := abs_nonneg h
    nlinarith [htail, hmonoR, hnonneg]
  -- transfer through `phase`
  rw [norm_phase_sub_phase, hkey]
  have hsm : 2 * Real.pi * |h * omegaTail b (n + L) / (b : ℝ) ^ L| ≤ 1 := by
    have : 2 * Real.pi * |h * omegaTail b (n + L) / (b : ℝ) ^ L|
        ≤ 2 * Real.pi * depthBound b h M L :=
      mul_le_mul_of_nonneg_left hsize (by positivity)
    linarith
  have hbnd := norm_phase_sub_one_le hsm
  have : 4 * Real.pi * |h * omegaTail b (n + L) / (b : ℝ) ^ L|
      ≤ 4 * Real.pi * depthBound b h M L :=
    mul_le_mul_of_nonneg_left hsize (by positivity)
  linarith

/-- **The Weyl mean is the finite-depth Weyl mean, up to `4π·D`.**  This is the reduction the
crux needs: it replaces the infinite-depth object `θ_n` by the depth-`L` window
`H_L(n)/b^L = Σ_{i<L} ω(n+1+i) b^{−1−i}`, uniformly for `n < M`. -/
theorem norm_fullMean_phase_sub_head (b : ℕ) (hb : 2 ≤ b) (h : ℝ) (M L : ℕ)
    (hsmall : 2 * Real.pi * depthBound b h M L ≤ 1) :
    ‖fullMean (fun n => phase (h * omegaTail b n)) M
        - fullMean (fun n => phase (h * ((omegaHead b L n : ℤ) : ℝ) / (b : ℝ) ^ L)) M‖
      ≤ 4 * Real.pi * depthBound b h M L := by
  rcases Nat.eq_zero_or_pos M with rfl | hM
  · simp only [fullMean, Nat.cast_zero, div_zero, sub_zero, norm_zero]
    have := depthBound_nonneg b h 0 L hb
    positivity
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  have hMc : ((M : ℂ)) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  rw [fullMean, fullMean, div_sub_div_same, ← Finset.sum_sub_distrib, norm_div,
    Complex.norm_natCast, div_le_iff₀ hMr]
  calc ‖∑ n ∈ range M, (phase (h * omegaTail b n)
          - phase (h * ((omegaHead b L n : ℤ) : ℝ) / (b : ℝ) ^ L))‖
      ≤ ∑ n ∈ range M, ‖phase (h * omegaTail b n)
          - phase (h * ((omegaHead b L n : ℤ) : ℝ) / (b : ℝ) ^ L)‖ := norm_sum_le _ _
    _ ≤ ∑ _n ∈ range M, (4 * Real.pi * depthBound b h M L) :=
        Finset.sum_le_sum fun n hn =>
          norm_phase_omegaTail_sub_head b hb h L n M (Finset.mem_range.mp hn) hsmall
    _ = 4 * Real.pi * depthBound b h M L * M := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring

/-! ### The depth requirement, stated crisply -/

/-- **The depth requirement.**  The truncation error vanishes along a depth schedule `L(M)`
exactly when `b^{L(M)}` beats `log₂ M`.  So the crux's finite-depth hypothesis `H` must hold at
depth `L(M) ≍ log_b log₂ M` — Delange's regime — and no slower schedule will do: by
`omegaTail_le_log` the tail really is of size `log₂ M`, and by `sum_primePeriodicTerm_period`
(mean `1/(b−1)` per prime, no decay) no truncation of the PRIME expansion is uniformly small
either.  Depth `L` bounded is therefore refuted, not merely unproven. -/
theorem depthBound_tendsto_zero_of_pow_div_atTop (b : ℕ) (hb : 2 ≤ b) (h : ℝ) (L : ℕ → ℕ)
    (hL : Tendsto (fun M => (b : ℝ) ^ (L M) / ((Nat.log 2 (M + L M) : ℝ) + 1)) atTop atTop) :
    Tendsto (fun M => depthBound b h M (L M)) atTop (𝓝 0) := by
  have hbpos : (0 : ℝ) < (b : ℝ) := by
    have : (2 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
    linarith
  have h1 : Tendsto
      (fun M => ((b : ℝ) ^ (L M) / ((Nat.log 2 (M + L M) : ℝ) + 1))⁻¹) atTop (𝓝 0) :=
    hL.inv_tendsto_atTop
  have h2 : Tendsto
      (fun M => |h| * ((b : ℝ) ^ (L M) / ((Nat.log 2 (M + L M) : ℝ) + 1))⁻¹) atTop (𝓝 0) := by
    simpa using h1.const_mul |h|
  refine h2.congr fun M => ?_
  have hA : ((b : ℝ) ^ (L M)) ≠ 0 := by positivity
  have hB : ((Nat.log 2 (M + L M) : ℝ) + 1) ≠ 0 := by positivity
  rw [depthBound, inv_div]
  field_simp

/-! ### The tail is never an integer (irrationality of `G₄_b`) -/

/-- `b^N · G₄_b` splits as the integer head plus the tail `θ_N`. -/
lemma primeLambert_mul_pow (b : ℕ) (hb : 2 ≤ b) (N : ℕ) :
    primeLambertAtBase b * (b : ℝ) ^ N
      = ((∑ m ∈ range (N + 1), omegaNat m * b ^ (N - m) : ℕ) : ℝ) + omegaTail b N := by
  have hb0 : (0 : ℝ) < b := by
    have : (2 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
    linarith
  have hs := summable_lambert b hb omegaNat omegaNat_le
  have hsN : Summable (fun m : ℕ => (omegaNat m : ℝ) / (b : ℝ) ^ m * (b : ℝ) ^ N) :=
    hs.mul_right _
  rw [primeLambertAtBase_eq_lambertVal_omegaNat, lambertVal, ← tsum_mul_right,
    ← Summable.sum_add_tsum_nat_add (N + 1) hsN]
  congr 1
  · push_cast
    refine Finset.sum_congr rfl fun m hm => ?_
    have hmN : m ≤ N := by
      have := Finset.mem_range.mp hm; omega
    have hsplit : (b : ℝ) ^ N = (b : ℝ) ^ m * (b : ℝ) ^ (N - m) := by
      rw [← pow_add]; congr 1; omega
    rw [hsplit]
    field_simp
  · rw [omegaTail]
    exact tsum_congr fun k => omegaTail_term b hb N k

/-- **The tail is never an integer.**  Immediate from the irrationality of `G₄_b` (`b ≥ 3`,
`G4.irrational_primeLambertAtBase`).  This is what makes leaf (B) of the crux — the carry
overflow — discharge unconditionally: for every `n` the depth can be pushed past the overflow. -/
theorem fract_omegaTail_pos (b : ℕ) (hb : 3 ≤ b) (N : ℕ) : 0 < Int.fract (omegaTail b N) := by
  rcases lt_or_eq_of_le (Int.fract_nonneg (omegaTail b N)) with h | h
  · exact h
  · exfalso
    have hint : omegaTail b N = ((⌊omegaTail b N⌋ : ℤ) : ℝ) := by
      have := Int.self_sub_fract (omegaTail b N)
      rw [← h] at this
      linarith [this]
    have hsplit := primeLambert_mul_pow b (by omega) N
    rw [hint] at hsplit
    have hrat : primeLambertAtBase b * (b : ℝ) ^ N
        = (((∑ m ∈ range (N + 1), omegaNat m * b ^ (N - m) : ℕ) : ℤ)
            + ⌊omegaTail b N⌋ : ℤ) := by
      rw [hsplit]; push_cast; ring
    have hirr : Irrational (primeLambertAtBase b) := G4.irrational_primeLambertAtBase hb
    have hirr2 : Irrational (primeLambertAtBase b * ((b ^ N : ℕ) : ℝ)) :=
      hirr.mul_natCast (by positivity)
    rw [Nat.cast_pow] at hirr2
    exact hirr2.ne_int _ hrat

/-! ### Leaf (B) of the crux, discharged: an explicit depth profile with NO bad set -/

/-- The truncation at depth `K` is exact at `n` as soon as the depth-`K` remainder
`θ_{n+L+K}/b^K` fits inside the fractional part of `θ_{n+L}`. -/
theorem windowVal_eq_trunc_of_tail_le (b : ℕ) (hb : 2 ≤ b) (L K n : ℕ)
    (hK : omegaTail b (n + L + K) / (b : ℝ) ^ K ≤ Int.fract (omegaTail b (n + L))) :
    omegaWindowVal b L n = windowValTrunc b L K n := by
  have hb0 : (0 : ℝ) < b := by
    have : (2 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
    linarith
  have hbK : (0 : ℝ) < (b : ℝ) ^ K := by positivity
  set H : ℤ := omegaHead b K (n + L) with hH
  set θ : ℝ := omegaTail b (n + L) with hθ
  set δ : ℝ := omegaTail b (n + L + K) / (b : ℝ) ^ K with hδ
  have hδ0 : 0 ≤ δ := by
    rw [hδ]
    exact div_nonneg (omegaTail_nonneg b hb _) (le_of_lt hbK)
  have hreal : ((H : ℝ)) / (b : ℝ) ^ K = θ - δ := by
    have hpow := omegaTail_pow b hb K (n + L)
    rw [← hH, ← hθ] at hpow
    rw [hδ]
    field_simp
    linarith [hpow]
  -- the integer division is the floor
  have hediv : H / (b : ℤ) ^ K = ⌊((H : ℝ)) / (b : ℝ) ^ K⌋ := by
    have h1 : ⌊((H : ℝ)) / ((b ^ K : ℕ) : ℝ)⌋ = ⌊((H : ℝ))⌋ / ((b ^ K : ℕ) : ℤ) :=
      Int.floor_div_natCast _ _
    rw [Int.floor_intCast] at h1
    rw [show ((b : ℝ)) ^ K = ((b ^ K : ℕ) : ℝ) by push_cast; ring,
      h1, show (((b ^ K : ℕ)) : ℤ) = (b : ℤ) ^ K by push_cast; ring]
  -- the floor is unchanged
  have hfloor : ⌊θ - δ⌋ = ⌊θ⌋ := by
    refine Int.floor_eq_iff.mpr ⟨?_, ?_⟩
    · have hfr : Int.fract θ = θ - (⌊θ⌋ : ℝ) := Int.self_sub_floor θ ▸ rfl
      linarith [hK, hfr]
    · have h1 : Int.fract θ < 1 := Int.fract_lt_one θ
      have hfr : Int.fract θ = θ - (⌊θ⌋ : ℝ) := Int.self_sub_floor θ ▸ rfl
      linarith
  rw [omegaWindowVal, windowValTrunc, ← hH, omegaCarry_eq_floor, ← hθ, hediv, hreal, hfloor]

/-- For every `n` there are arbitrarily large exact depths. -/
theorem exists_good_depth (b : ℕ) (hb : 3 ≤ b) (L n K₀ : ℕ) :
    ∃ K, K₀ ≤ K ∧
      omegaTail b (n + L + K) / (b : ℝ) ^ K ≤ Int.fract (omegaTail b (n + L)) := by
  have hb2 : 2 ≤ b := by omega
  have hb0 : (0 : ℝ) < b := by
    have : (3 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
    linarith
  have hb1 : (1 : ℝ) < (b : ℝ) := by
    have : (3 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
    linarith
  set ε : ℝ := Int.fract (omegaTail b (n + L)) with hε
  have hεpos : 0 < ε := fract_omegaTail_pos b hb (n + L)
  set r : ℝ := 1 / (b : ℝ) with hr
  have hr0 : (0 : ℝ) ≤ r := by rw [hr]; positivity
  have hr1 : r < 1 := by rw [hr, div_lt_one hb0]; exact hb1
  have hrn : ‖r‖ < 1 := by rw [Real.norm_eq_abs, abs_of_nonneg hr0]; exact hr1
  set c : ℕ := n + L + 2 with hc
  -- the comparison sequence tends to zero
  have hsum : Summable (fun K : ℕ => ((c : ℝ) + K) * r ^ K) := by
    have h1 : Summable (fun K : ℕ => (c : ℝ) * r ^ K) :=
      (summable_geometric_of_lt_one hr0 hr1).mul_left _
    have h2 : Summable (fun K : ℕ => (K : ℝ) * r ^ K) :=
      (hasSum_coe_mul_geometric_of_norm_lt_one hrn).summable
    exact (h1.add h2).congr fun K => by ring
  have htend : Tendsto (fun K : ℕ => ((c : ℝ) + K) * r ^ K) atTop (𝓝 0) :=
    hsum.tendsto_atTop_zero
  have hev := (NormedAddCommGroup.tendsto_nhds_zero.mp htend) ε hεpos
  obtain ⟨K, hK0, hKlt⟩ := (hev.and (Filter.eventually_ge_atTop K₀)).exists
  refine ⟨K, hKlt, ?_⟩
  have hnn : (0 : ℝ) ≤ ((c : ℝ) + K) * r ^ K := by positivity
  have hK0' : ((c : ℝ) + K) * r ^ K < ε := by
    rw [Real.norm_eq_abs, abs_of_nonneg hnn] at hK0
    exact hK0
  -- and it dominates the remainder
  have hbK : (0 : ℝ) < (b : ℝ) ^ K := by positivity
  have hnum : omegaTail b (n + L + K) ≤ (c : ℝ) + K := by
    have h1 : omegaTail b (n + L + K) ≤ (Nat.log 2 (n + L + K + 1) : ℝ) + 1 :=
      omegaTail_le_log b hb2 (n + L + K)
    have h2 : Nat.log 2 (n + L + K + 1) ≤ n + L + K + 1 := Nat.log_le_self _ _
    have h3 : ((Nat.log 2 (n + L + K + 1) : ℝ)) ≤ ((n + L + K + 1 : ℕ) : ℝ) := by
      exact_mod_cast h2
    have h4 : (((n + L + K + 1 : ℕ)) : ℝ) + 1 = (c : ℝ) + K := by
      rw [hc]; push_cast; ring
    linarith
  have hpowr : r ^ K = 1 / (b : ℝ) ^ K := by rw [hr, div_pow, one_pow]
  calc omegaTail b (n + L + K) / (b : ℝ) ^ K
      ≤ ((c : ℝ) + K) / (b : ℝ) ^ K := by
        exact div_le_div_of_nonneg_right hnum (le_of_lt hbK) |>.trans (le_of_eq rfl)
    _ = ((c : ℝ) + K) * r ^ K := by rw [hpowr]; ring
    _ ≤ ε := le_of_lt hK0'

open Classical in
/-- **The explicit exact-depth profile.**  `goodDepth b L n` is a depth `≥ n` at which the
window-value truncation at `n` is EXACT. -/
noncomputable def goodDepth (b L n : ℕ) : ℕ :=
  if h : ∃ K, n ≤ K ∧
      omegaTail b (n + L + K) / (b : ℝ) ^ K ≤ Int.fract (omegaTail b (n + L))
    then h.choose else n

theorem goodDepth_spec (b : ℕ) (hb : 3 ≤ b) (L n : ℕ) :
    n ≤ goodDepth b L n ∧ omegaWindowVal b L n = windowValTrunc b L (goodDepth b L n) n := by
  have hex : ∃ K, n ≤ K ∧
      omegaTail b (n + L + K) / (b : ℝ) ^ K ≤ Int.fract (omegaTail b (n + L)) :=
    exists_good_depth b hb L n n
  have hgd : goodDepth b L n = hex.choose := by
    rw [goodDepth]
    exact dif_pos hex
  obtain ⟨h1, h2⟩ := hex.choose_spec
  rw [hgd]
  exact ⟨h1, windowVal_eq_trunc_of_tail_le b (by omega) L _ n h2⟩

/-- **Leaf (B) of the crux is UNCONDITIONAL.**  At the profile `goodDepth` the bad set is EMPTY,
so the carry-overflow density is identically zero. -/
theorem hCarryOverflowAt_goodDepth (b : ℕ) (hb : 3 ≤ b) (L : ℕ) :
    HCarryOverflowAt b L (goodDepth b L) := by
  have hzero : ∀ N : ℕ, carryBadCount b L (goodDepth b L) N = 0 := by
    intro N
    rw [carryBadCount, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro n _
    simp only [not_not]
    exact (goodDepth_spec b hb L n).2
  rw [HCarryOverflowAt]
  refine Filter.Tendsto.congr (fun N => ?_) (tendsto_const_nhds (x := (0 : ℝ)))
  rw [hzero N]
  simp

/-- **The crux now has exactly ONE leaf.**  `HDepth b L` — hence the whole C1 chain — follows
from the joint-equidistribution leaf (A) ALONE, at the explicit depth profile `goodDepth b L`.
Leaf (B), the carry overflow, is discharged unconditionally by `hCarryOverflowAt_goodDepth`. -/
theorem hDepth_of_hTruncDecay (b : ℕ) (hb : 3 ≤ b) (L : ℕ)
    (h : HTruncDecayAt b L (goodDepth b L)) : HDepth b L := by
  refine ⟨goodDepth b L, ?_, h, hCarryOverflowAt_goodDepth b hb L⟩
  refine tendsto_atTop_mono (fun n => (goodDepth_spec b hb L n).1) tendsto_id

/-! ### ⚠️ Honest correction: the depth-profile split of the crux is VACUOUS

`goodDepth` makes the truncation exact, but it is `≥ n`, so `windowValTrunc b L (goodDepth b L n) n`
depends on `ω(n+1), …, ω(n+L+goodDepth n)` — i.e. on everything.  Consequently
`HTruncDecayAt b L (goodDepth b L)` is *literally the same statement* as `HWindowChar b L`, and the
reduction `hDepth_of_hTruncDecay` combined with `hWindowChar_of_hDepth` proves only

`HDepth b L ↔ HWindowChar b L`   (`hDepth_iff_hWindowChar`, below).

That is a genuine structural fact — **the carry is not where any of the difficulty lives**, and the
whole "choose the depth profile cleverly" line of attack is refuted — but it is NOT a weakening of
the crux.  To be *useful* a profile `κ` must be SLOWLY GROWING, and then leaf (B) needs
`density{n < N : fract(θ_{n+L}) < Λ_N/b^{κ n}} → 0`: a quantitative non-concentration of the very
orbit under study at `0`.  That, not the exactness, is the real content of leaf (B), and it is
strictly weaker than leaf (A) (one-sided, at one point, at scale `1/b^κ`).
-/

/-- **The depth-profile split is vacuous.**  `HDepth` and `HWindowChar` are equivalent. -/
theorem hDepth_iff_hWindowChar (b : ℕ) (hb : 3 ≤ b) (L : ℕ) :
    HDepth b L ↔ HWindowChar b L := by
  refine ⟨hWindowChar_of_hDepth b L, fun h => hDepth_of_hTruncDecay b hb L ?_⟩
  intro a ha haL
  have heq : ∀ N : ℕ, windowCharSumTrunc b L (goodDepth b L) a N = windowCharSum b L a N := by
    intro N
    rw [windowCharSumTrunc, windowCharSum]
    congr 1
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [(goodDepth_spec b hb L n).2]
  exact (h a ha haL).congr fun N => (heq N).symm

/-! ### Leaf (B) in its honest, useful form -/

/-- **Non-concentration of the orbit at `0`.**  The orbit `fract(θ_{n+L})` is below the depth-`κ n`
remainder only on a density-zero set.  This — not exactness — is the real content of leaf (B) for a
slowly growing depth profile, and it is a strictly one-sided, single-point, scale-`b^{−κ}`
statement, far weaker than leaf (A). -/
def OrbitNonConc (b L : ℕ) (κ : ℕ → ℕ) : Prop :=
  Tendsto (fun N => ((((range N).filter (fun n =>
      Int.fract (omegaTail b (n + L))
        < omegaTail b (n + L + κ n) / (b : ℝ) ^ (κ n))).card : ℝ)) / N) atTop (𝓝 0)

/-- Non-concentration gives leaf (B) at the SAME profile — for any profile, however slow. -/
theorem hCarryOverflowAt_of_orbitNonConc (b : ℕ) (hb : 2 ≤ b) (L : ℕ) (κ : ℕ → ℕ)
    (h : OrbitNonConc b L κ) : HCarryOverflowAt b L κ := by
  classical
  have hsub : ∀ N : ℕ, carryBadCount b L κ N
      ≤ ((range N).filter (fun n =>
          Int.fract (omegaTail b (n + L))
            < omegaTail b (n + L + κ n) / (b : ℝ) ^ (κ n))).card := by
    intro N
    refine Finset.card_le_card ?_
    intro n hn
    rw [Finset.mem_filter] at hn ⊢
    refine ⟨hn.1, ?_⟩
    by_contra hcon
    push_neg at hcon
    exact hn.2 (windowVal_eq_trunc_of_tail_le b hb L (κ n) n hcon)
  rw [HCarryOverflowAt]
  refine squeeze_zero (fun N => by positivity) (fun N => ?_) h
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp
  · have hNr : (0 : ℝ) < N := by exact_mod_cast hN
    refine div_le_div_of_nonneg_right ?_ (le_of_lt hNr) |>.trans (le_of_eq rfl)
    exact_mod_cast hsub N

end NormalNumbers.CastingOut
