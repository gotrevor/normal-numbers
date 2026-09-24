import NormalNumbers.SwingC1Head
import NormalNumbers.WeylCriterion

/-!
# Wiring the Weyl mean to the headline leaf `hWindowCharAll`

`SwingC1Delange.lean`, `SwingC1Katai.lean` and `SwingC1Head.lean` all work with
`weylMean b h N = mean_{n<N} e(h·θ_n)`, the Weyl sum of the `×b`-orbit of `G₄_b`.  Until this
file nothing connected that object to the open leaves of `SwingC1.lean`, so the whole
Delange/Kátai chain was formally DANGLING.  The bridge:

`weylMean b k → 0` for every nonzero integer `k`
  ⟹ (Weyl's criterion, `equidistributed_of_weyl`) the orbit `fract θ_n` is equidistributed
  ⟹ `HWindowChar b L` for every `L` (`hWindowChar_of_equidistributed`)
  ⟹ `HWindow`, `HState`, `ConjC1`.

The middle step is a finite computation.  By `omegaTail_pow`,
`omegaWindowVal b L n = ⌊b^L·θ_n⌋ ≡ ⌊b^L·fract θ_n⌋ (mod b^L)`, so the window character sum is a
STEP function of the orbit point, equal to `ζ_{b^L}^{a v}` on `[v/b^L, (v+1)/b^L)`; and
`Σ_{v<b^L} ζ_{b^L}^{a v} = 0` whenever `b^L ∤ a`.

⚠️ This route proves normality of `G₄_b` in base `b`, which is STRICTLY STRONGER than `ConjC1`;
`hAutoCorrAll` (fixed modulus `b − 1`) remains the weaker leaf `conjC1` rests on.  The route is
the one `SwingC1.lean` records as `hState_of_blockRoute`.

Sorry-free.
-/

open Finset Filter Topology NormalNumbers.PrimeLambert

namespace NormalNumbers.CastingOut

/-- The orbit point: `fract(b^n·G₄_b) = fract(θ_n)`. -/
noncomputable def orbitFract (b n : ℕ) : ℝ := Int.fract (omegaTail b n)

lemma orbitFract_mem_Ico (b n : ℕ) : orbitFract b n ∈ Set.Ico (0 : ℝ) 1 :=
  ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩

/-- The Weyl mean at an integer frequency IS the Fourier mean of the orbit. -/
lemma weylMean_eq_fourierMean (b : ℕ) (k : ℤ) (N : ℕ) :
    weylMean b (k : ℝ) N = fourierMean (orbitFract b) k N := by
  rw [weylMean, fullMean, fourierMean]
  congr 1
  refine Finset.sum_congr rfl fun n _ => ?_
  have hsplit : (omegaTail b n : ℝ) = orbitFract b n + (⌊omegaTail b n⌋ : ℝ) := by
    rw [orbitFract, Int.fract]; ring
  rw [phase, hsplit]
  have key : (2 * (Real.pi : ℂ) * Complex.I
        * ((((k : ℝ) * (orbitFract b n + ((⌊omegaTail b n⌋ : ℤ) : ℝ))) : ℝ) : ℂ))
      = 2 * (Real.pi : ℂ) * Complex.I * (k : ℂ) * ((orbitFract b n : ℝ) : ℂ)
        + ((k * ⌊omegaTail b n⌋ : ℤ) : ℂ) * (2 * Real.pi * Complex.I) := by
    push_cast; ring
  rw [key, Complex.exp_add, Complex.exp_int_mul, Complex.exp_two_pi_mul_I, one_zpow, mul_one]

/-- **Weyl's criterion, applied to the orbit of `G₄_b`.** -/
theorem equidistributed_of_weylMean (b : ℕ)
    (hw : ∀ k : ℤ, k ≠ 0 → Tendsto (fun N => weylMean b (k : ℝ) N) atTop (𝓝 0)) :
    Equidistributed (orbitFract b) := by
  refine equidistributed_of_weyl (orbitFract b) (orbitFract_mem_Ico b) ?_
  intro k hk
  exact (hw k hk).congr (fun N => weylMean_eq_fourierMean b k N)

/-! ### The window value is the digit block of the orbit point -/

/-- The window value and the digit block of the orbit point differ by a multiple of `b^L`. -/
lemma omegaWindowVal_sub_floor (b : ℕ) (hb : 2 ≤ b) (L n : ℕ) :
    omegaWindowVal b L n - ⌊(b : ℝ) ^ L * orbitFract b n⌋
      = (b : ℤ) ^ L * ⌊omegaTail b n⌋ := by
  have hsplit : (b : ℝ) ^ L * orbitFract b n
      = (b : ℝ) ^ L * omegaTail b n + (((-((b : ℤ) ^ L * ⌊omegaTail b n⌋) : ℤ)) : ℝ) := by
    rw [orbitFract, Int.fract]
    push_cast
    ring
  rw [omegaWindowVal_eq_floor b hb L n, hsplit, Int.floor_add_intCast]
  ring

/-! ### The finite character sum -/

/-- `Σ_{v<M} ζ_M^{a v} = 0` when `M ∤ a`. -/
lemma sum_zetaRoot_pow_eq_zero (M a : ℕ) (hM : 0 < M) (ha : ¬ ((M : ℤ) ∣ (a : ℤ))) :
    ∑ v ∈ range M, zetaRoot M ^ ((a : ℤ) * (v : ℤ)) = 0 := by
  set z : ℂ := zetaRoot M ^ ((a : ℤ)) with hz
  have hzv : ∀ v : ℕ, zetaRoot M ^ ((a : ℤ) * (v : ℤ)) = z ^ v := by
    intro v
    rw [hz, ← zpow_natCast (zetaRoot M ^ ((a : ℤ))) v, ← zpow_mul]
  have hzne : z - 1 ≠ 0 := by
    rw [sub_ne_zero, hz]
    intro hcon
    exact ha ((zetaRoot_zpow_eq_one_iff M hM _).mp hcon)
  have hzM : z ^ M = 1 := by
    rw [hz, ← zpow_natCast (zetaRoot M ^ ((a : ℤ))) M, ← zpow_mul]
    exact (zetaRoot_zpow_eq_one_iff M hM _).mpr ⟨(a : ℤ), by ring⟩
  rw [Finset.sum_congr rfl (fun v _ => hzv v), geom_sum_eq (by
    intro hcon; exact hzne (by rw [hcon]; ring)), hzM, sub_self, zero_div]

lemma mem_Ico_div_iff (M : ℕ) (hM : 0 < M) (x : ℝ) (v : ℕ) :
    x ∈ Set.Ico ((v : ℝ) / M) (((v : ℝ) + 1) / M) ↔ ⌊(M : ℝ) * x⌋ = (v : ℤ) := by
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM
  rw [Set.mem_Ico, div_le_iff₀ hMR, lt_div_iff₀ hMR, Int.floor_eq_iff]
  push_cast
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨by linarith, by linarith⟩
  · rintro ⟨h1, h2⟩; exact ⟨by linarith, by linarith⟩

/-! ### The bridge -/

set_option maxHeartbeats 1000000 in
/-- **The bridge.**  Equidistribution of the orbit gives the Weyl-form window leaf at every
length `L`.  The window character sum is a step function of the orbit point, equal to
`ζ_{b^L}^{a v}` on `[v/b^L, (v+1)/b^L)`, and those `b^L` roots of unity sum to zero. -/
theorem hWindowChar_of_equidistributed (b : ℕ) (hb : 2 ≤ b) (L : ℕ)
    (he : Equidistributed (orbitFract b)) : HWindowChar b L := by
  classical
  intro a ha haL
  set M : ℕ := b ^ L with hMdef
  have hMpos : 0 < M := by rw [hMdef]; positivity
  have hMR : (0 : ℝ) < M := by exact_mod_cast hMpos
  have hMRL : ((M : ℝ)) = (b : ℝ) ^ L := by rw [hMdef]; push_cast; ring
  have hMZL : ((M : ℤ)) = (b : ℤ) ^ L := by rw [hMdef]; push_cast; ring
  -- the floor of `M·orbitFract` lies in `[0, M)` and determines the summand
  have hfl0 : ∀ n : ℕ, 0 ≤ ⌊(M : ℝ) * orbitFract b n⌋ := by
    intro n
    refine Int.floor_nonneg.mpr ?_
    have := (orbitFract_mem_Ico b n).1
    positivity
  have hflM : ∀ n : ℕ, ⌊(M : ℝ) * orbitFract b n⌋ < (M : ℤ) := by
    intro n
    refine Int.floor_lt.mpr ?_
    have h1 := (orbitFract_mem_Ico b n).2
    push_cast
    nlinarith
  have hval : ∀ n : ℕ, zetaRoot M ^ ((a : ℤ) * omegaWindowVal b L n)
      = zetaRoot M ^ ((a : ℤ) * ⌊(M : ℝ) * orbitFract b n⌋) := by
    intro n
    have hd := omegaWindowVal_sub_floor b hb L n
    rw [← hMRL] at hd
    have hsplit : (a : ℤ) * omegaWindowVal b L n
        = (a : ℤ) * ⌊(M : ℝ) * orbitFract b n⌋ + (M : ℤ) * ((a : ℤ) * ⌊omegaTail b n⌋) := by
      rw [hMZL]; linear_combination (a : ℤ) * hd
    rw [hsplit, zpow_add₀ (zetaRoot_ne_zero M),
      (zetaRoot_zpow_eq_one_iff M hMpos _).mpr ⟨(a : ℤ) * ⌊omegaTail b n⌋, rfl⟩, mul_one]
  -- the summand as a step function of the orbit point
  have hstep : ∀ n : ℕ, zetaRoot M ^ ((a : ℤ) * omegaWindowVal b L n)
      = ∑ v ∈ range M,
          (if orbitFract b n ∈ Set.Ico ((v : ℝ) / M) (((v : ℝ) + 1) / M)
            then zetaRoot M ^ ((a : ℤ) * (v : ℤ)) else 0) := by
    intro n
    set u : ℕ := (⌊(M : ℝ) * orbitFract b n⌋).toNat with hu
    have huw : ((u : ℕ) : ℤ) = ⌊(M : ℝ) * orbitFract b n⌋ :=
      Int.toNat_of_nonneg (hfl0 n)
    have humem : u ∈ range M := by
      rw [Finset.mem_range]
      have := hflM n
      omega
    rw [Finset.sum_eq_single u]
    · rw [if_pos ((mem_Ico_div_iff M hMpos (orbitFract b n) u).mpr huw.symm), hval n, huw]
    · intro v _ hvu
      refine if_neg ?_
      intro hcon
      have := (mem_Ico_div_iff M hMpos (orbitFract b n) v).mp hcon
      exact hvu (by omega)
    · intro hcon; exact absurd humem hcon
  -- sum, swap, and recognise the visit counts
  have hsum : ∀ N : ℕ, windowCharSum b L a N
      = ∑ v ∈ range M, zetaRoot M ^ ((a : ℤ) * (v : ℤ))
          * ((((visitCount (orbitFract b) ((v : ℝ) / M) (((v : ℝ) + 1) / M) N : ℕ) : ℝ)
              / (N : ℝ) : ℝ) : ℂ) := by
    intro N
    rw [windowCharSum, Finset.sum_congr rfl (fun n _ => hstep n), Finset.sum_comm,
      Finset.sum_div]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const_zero, add_zero, nsmul_eq_mul,
      visitCount]
    push_cast
    ring
  -- the limit
  have hlim : ∀ v ∈ range M,
      Tendsto (fun N : ℕ => zetaRoot M ^ ((a : ℤ) * (v : ℤ))
          * ((((visitCount (orbitFract b) ((v : ℝ) / M) (((v : ℝ) + 1) / M) N : ℕ) : ℝ)
              / (N : ℝ) : ℝ) : ℂ)) atTop
        (𝓝 (zetaRoot M ^ ((a : ℤ) * (v : ℤ)) * ((1 / (M : ℝ) : ℝ) : ℂ))) := by
    intro v hv
    rw [Finset.mem_range] at hv
    have hvR : ((v : ℝ) + 1) / M ≤ 1 := by
      rw [div_le_one hMR]
      have : (v : ℝ) + 1 ≤ (M : ℝ) := by
        have : ((v : ℕ) : ℝ) + 1 ≤ ((M : ℕ) : ℝ) := by exact_mod_cast hv
        linarith
      linarith
    have hE := he ((v : ℝ) / M) (((v : ℝ) + 1) / M) (by positivity)
      (by rw [div_le_div_iff_of_pos_right hMR]; linarith) hvR
    have hval2 : ((v : ℝ) + 1) / M - (v : ℝ) / M = 1 / (M : ℝ) := by field_simp; ring
    rw [hval2] at hE
    exact (Complex.ofRealCLM.continuous.tendsto _).comp hE |>.const_mul _
  have hfin : Tendsto (windowCharSum b L a) atTop
      (𝓝 (∑ v ∈ range M, zetaRoot M ^ ((a : ℤ) * (v : ℤ)) * ((1 / (M : ℝ) : ℝ) : ℂ))) := by
    refine (tendsto_finsetSum _ hlim).congr fun N => (hsum N).symm
  have hzero : ∑ v ∈ range M, zetaRoot M ^ ((a : ℤ) * (v : ℤ)) * ((1 / (M : ℝ) : ℝ) : ℂ)
      = 0 := by
    rw [← Finset.sum_mul, sum_zetaRoot_pow_eq_zero M a hMpos ?_, zero_mul]
    intro hcon
    have : (M : ℤ) ≤ (a : ℤ) := Int.le_of_dvd (by exact_mod_cast ha) hcon
    have : M ≤ a := by exact_mod_cast this
    omega
  rw [hzero] at hfin
  exact hfin

/-! ### Reducing to frequencies prime to `b` -/

lemma phase_intCast (m : ℤ) : phase ((m : ℤ) : ℝ) = 1 := by
  rw [phase, show (2 * (Real.pi : ℂ) * Complex.I * (((m : ℤ) : ℝ) : ℂ))
      = ((m : ℤ) : ℂ) * (2 * Real.pi * Complex.I) by push_cast; ring,
    Complex.exp_int_mul, Complex.exp_two_pi_mul_I, one_zpow]

/-- Multiplying the frequency by `b` shifts the orbit by one step: the `ω`-digit it peels off is
an integer, so it contributes the phase `1`. -/
lemma weylMean_mul_b (b : ℕ) (hb : 2 ≤ b) (k : ℤ)
    (h : Tendsto (fun N => weylMean b ((k : ℤ) : ℝ) N) atTop (𝓝 0)) :
    Tendsto (fun N => weylMean b (((b : ℤ) * k : ℤ) : ℝ) N) atTop (𝓝 0) := by
  have hpt : ∀ n : ℕ, phase ((((b : ℤ) * k : ℤ) : ℝ) * omegaTail b n)
      = phase (((k : ℤ) : ℝ) * omegaTail b (n + 1)) := by
    intro n
    have hrec := omegaTail_rec b hb n
    have hsplit : (((b : ℤ) * k : ℤ) : ℝ) * omegaTail b n
        = (((k * (omegaNat (n + 1) : ℤ) : ℤ)) : ℝ) + ((k : ℤ) : ℝ) * omegaTail b (n + 1) := by
      push_cast
      push_cast at hrec
      linear_combination (k : ℝ) * hrec
    rw [hsplit, phase_add, phase_intCast, one_mul]
  have hshift : Tendsto
      (fun N => fullMean (fun n => phase (((k : ℤ) : ℝ) * omegaTail b (n + 1))) N)
      atTop (𝓝 0) :=
    tendsto_fullMean_shift (g := fun n => phase (((k : ℤ) : ℝ) * omegaTail b n))
      (fun n => le_of_eq (norm_phase _)) h
  refine hshift.congr fun N => ?_
  rw [weylMean, fullMean, fullMean]
  congr 1
  exact Finset.sum_congr rfl fun n _ => (hpt n).symm

/-- Every nonzero frequency reduces to one prime to `b`. -/
theorem weylMean_tendsto_zero_of_coprime (b : ℕ) (hb : 2 ≤ b)
    (h : ∀ m : ℤ, m ≠ 0 → ¬ ((b : ℤ) ∣ m) →
      Tendsto (fun N => weylMean b ((m : ℤ) : ℝ) N) atTop (𝓝 0)) :
    ∀ k : ℤ, k ≠ 0 → Tendsto (fun N => weylMean b ((k : ℤ) : ℝ) N) atTop (𝓝 0) := by
  have hb0 : (0 : ℤ) < (b : ℤ) := by exact_mod_cast (by omega : 0 < b)
  intro k
  induction hn : k.natAbs using Nat.strong_induction_on generalizing k with
  | _ n ih =>
      intro hk
      by_cases hdvd : ((b : ℤ) ∣ k)
      · obtain ⟨c, hc⟩ := hdvd
        have hcne : c ≠ 0 := by rintro rfl; simp at hc; exact hk hc
        have hlt : c.natAbs < n := by
          subst hn
          rw [hc, Int.natAbs_mul]
          have : 1 < (b : ℤ).natAbs := by
            simp only [Int.natAbs_natCast]
            omega
          have hcpos : 0 < c.natAbs := Int.natAbs_pos.mpr hcne
          calc c.natAbs = 1 * c.natAbs := (one_mul _).symm
            _ < (b : ℤ).natAbs * c.natAbs := by
                exact (Nat.mul_lt_mul_right hcpos).mpr this
        have := ih c.natAbs hlt c rfl hcne
        rw [hc]
        exact weylMean_mul_b b hb c this
      · exact h k hk hdvd

/-! ### The assembled conditional theorems -/

/-- **`ConjC1` from the Weyl means.** -/
theorem conjC1_of_weylMean
    (hw : ∀ b : ℕ, 3 ≤ b → ∀ m : ℤ, m ≠ 0 → ¬ ((b : ℤ) ∣ m) →
      Tendsto (fun N => weylMean b ((m : ℤ) : ℝ) N) atTop (𝓝 0)) :
    ConjC1 :=
  conjC1_of_hState (hState_of_hWindow (fun b hb L =>
    hWindow_of_hWindowChar b (by omega) L
      (hWindowChar_of_equidistributed b (by omega) L
        (equidistributed_of_weylMean b
          (weylMean_tendsto_zero_of_coprime b (by omega) (hw b hb))))))

/-- **THE SWING'S CONDITIONAL THEOREM.**  `ConjC1` follows from
* `KataiOrthogonality` — the Daboussi–Kátai orthogonality criterion, a KNOWN theorem;
* `DelangeMean (m/b)` for `b ∤ m` — Delange's theorem (1969), KNOWN; and
* `PairDecorr b (m/b)` for `b ∤ m` — leaf (D), the one genuinely open statement.

`PairDecorr` is a pure statement about the orbit `θ` of `G₄_b` at multiplicatively shifted
indices; `SwingC1Pair.lean` proves its periodic-model form unconditionally. -/
theorem conjC1_of_delange_katai (hDK : KataiOrthogonality)
    (hD : ∀ b : ℕ, 3 ≤ b → ∀ m : ℤ, m ≠ 0 → ¬ ((b : ℤ) ∣ m) → DelangeMean (((m : ℤ) : ℝ) / b))
    (hP : ∀ b : ℕ, 3 ≤ b → ∀ m : ℤ, m ≠ 0 → ¬ ((b : ℤ) ∣ m) → PairDecorr b (((m : ℤ) : ℝ) / b)) :
    ConjC1 :=
  conjC1_of_weylMean fun b hb m hm hdvd =>
    weylMean_tendsto_zero_of b (by omega) ((m : ℤ) : ℝ) (hD b hb m hm hdvd)
      (shiftIndep_of_pairDecorr b (((m : ℤ) : ℝ) / b) hDK (hD b hb m hm hdvd)
        (hP b hb m hm hdvd))

end NormalNumbers.CastingOut
