import NormalNumbers.ElliottAffineGraph

/-!
# The `a`-dilated bilinear block pairing — the last Fourier obstruction of the crux

`NormalNumbers.ElliottAffineGraph` proved the lower-bound engine of the crux
`NormalNumbers.ElliottLadder.DilatedCMLogElliott` at full affine generality: the graph step
`n ↦ q n` dilates both shifts of `(a n + c₁, a n + c₂)`, so the common dilation `a` never enters
the edge estimate.  In *block* coordinates the resulting edge is

```
b (a*m + q*c₁) * c (a*m + q*c₂)          (the proved case is a = 1, c₁ = 0, c₂ = h)
```

i.e. the block index is **dilated by `a`**.  Re-basing the block at `a*(n+1)` turns this into: sum
over the block positions `m` lying in the residue class `q*c₁ (mod a)`, of `b m * c (m + σ)` with
`σ = q*(c₂-c₁)`.  So the one genuinely new Fourier ingredient is a bilinear pairing carrying a
**residue-class restriction whose class `s = q*c₁` moves with the prime `q`** — exactly the
feature that killed the slice route at the level of the observable.

Inside the Fourier layer it is harmless, and this file proves why.  Write `T = α * D`.  The
restriction `α ∣ m - s` is detected by the `α`-term orthogonality
`∑_{u < α} e_α(u (m-s)) = α · 1_{α ∣ m-s}`, and `e_α(u m) = e_T(u D m)`, so the effect is only to
shift the frequency of the **first** block by `u D`:

```
∑_{t < T} ∑_{u < α} [ b̂(t + uD) · conj ĉ̄(t) ] · e_T(t σ) · e_α(-u s)
    = T · α · ∑_m dilatedPairShiftEdge b c α s σ m.
```

The crucial consequence, and the reason the whole stack survives: with `s = q c₁` and
`σ = q (c₂ - c₁)` the two phases combine into

```
e_T(t σ) · e_α(-u s) = phase T (t*(c₂-c₁) - u*D*c₁) q,
```

a **single** frequency in `q`.  So the prime sum still produces
`NormalNumbers.ElliottTwistedGraph.twistedPrimeGraphMultiplier` evaluated at one frequency, and the
fourth-moment bound `fourth_moment_twistedPrimeGraphMultiplier_le_energy` and everything above it
(Markov, large frequencies, entropy decrement) is untouched.  Only the coefficient changes: the two
blocks are transformed at frequencies differing by `u D`, and there are `α` (a constant) values
of `u`.

Never edit dependency files; everything here is a new statement in `src/`.
-/

open scoped BigOperators ComplexConjugate
open Finset
open Erdos438.Fourier

namespace NormalNumbers.ElliottDilatedPairing

open Erdos67b

noncomputable section

/-! ## Two missing phase identities -/

/-- Additivity of `Erdos438.Fourier.phase` in the frequency. -/
theorem phase_add_left (T : ℕ) (t t' x : ℤ) :
    phase T (t + t') x = phase T t x * phase T t' x := by
  rw [phase, phase, phase, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- A frequency at a coarser modulus is a frequency at the finer one: `e_α(u m) = e_T(u D m)`
when `T = α * D`. -/
theorem phase_dilate {T α D : ℕ} (hTD : T = α * D) (hα : α ≠ 0) (hD : D ≠ 0) (u m : ℤ) :
    phase α u m = phase T ((u : ℤ) * D) m := by
  have hDc : ((D : ℂ)) ≠ 0 := Nat.cast_ne_zero.mpr hD
  have hαc : ((α : ℂ)) ≠ 0 := Nat.cast_ne_zero.mpr hα
  rw [phase, phase, hTD]
  congr 1
  push_cast
  field_simp

/-! ## The dilated edge and its pairing -/

/-- The graph edge of the `a`-dilated block: the block positions in the residue class `s (mod α)`,
paired with their translate by `σ`.  The case `α = 1`, `s = 0` is
`NormalNumbers.ElliottTwistedGraph.pairShiftEdge`. -/
def dilatedPairShiftEdge {H : ℕ} (b c : Fin H → ℂ) (α : ℕ) (s : ℤ) (σ : ℕ) (m : Fin H) : ℂ :=
  if (α : ℤ) ∣ (m.1 : ℤ) - s then
    (if hm : m.1 + σ < H then b m * c ⟨m.1 + σ, hm⟩ else 0)
  else 0

/-- The `a`-dilated bilinear pairing: the two blocks are transformed at frequencies differing by
`u * D`.  At `u = 0` this is `NormalNumbers.ElliottTwistedGraph.pairBlockPairing`. -/
def dilatedBlockPairing {H : ℕ} (T D : ℕ) (b c : Fin H → ℂ) (t u : ℤ) : ℂ :=
  blockFourier T b (t + u * D) * conj (blockFourier T (fun j ↦ conj (c j)) t)

theorem norm_dilatedBlockPairing {H : ℕ} (T D : ℕ) (b c : Fin H → ℂ) (t u : ℤ) :
    ‖dilatedBlockPairing T D b c t u‖ =
      ‖blockFourier T b (t + u * D)‖ * ‖blockFourier T (fun j ↦ conj (c j)) t‖ := by
  rw [dilatedBlockPairing, norm_mul, RCLike.norm_conj]

/-- Pointwise expansion of the dilated pairing against its two phases. -/
theorem dilatedBlockPairing_mul_phase {H T α D : ℕ} (hTD : T = α * D) (hα : α ≠ 0) (hD : D ≠ 0)
    (b c : Fin H → ℂ) (t u : ℤ) (s : ℤ) (σ : ℕ) :
    dilatedBlockPairing T D b c t u * phase T t σ * phase α u (-s) =
      ∑ m : Fin H, ∑ k : Fin H,
        (b m * c k) * (phase T t ((m.1 : ℤ) + σ - k.1) * phase α u ((m.1 : ℤ) - s)) := by
  simp only [dilatedBlockPairing, blockFourier, map_sum, map_mul, Complex.conj_conj,
    Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ ↦ Finset.sum_congr rfl fun k _ ↦ ?_
  rw [conj_phase]
  have hj : phase T (t + u * D) j.1 = phase T t j.1 * phase α u j.1 := by
    rw [phase_add_left, phase_dilate hTD hα hD]
  calc
    (b j * phase T (t + u * D) j.1) * (c k * phase T t (-(k.1 : ℤ))) * phase T t σ *
        phase α u (-s)
        = (b j * c k) * ((phase T t j.1 * phase T t σ * phase T t (-(k.1 : ℤ))) *
            (phase α u j.1 * phase α u (-s))) := by
          rw [hj]; ring
    _ = _ := by
      rw [← phase_add_right, ← phase_add_right, ← phase_add_right]
      congr 3

/-! ## Orthogonality -/

/-- `∑_{u < α} e_α(u x) = α · 1_{α ∣ x}`. -/
theorem sum_phase_dvd {α : ℕ} [NeZero α] (x : ℤ) :
    (∑ u ∈ Finset.range α, phase α (u : ℤ) x) = if (α : ℤ) ∣ x then (α : ℂ) else 0 := by
  rw [phase_orthogonality]
  congr 1
  simp [ZMod.intCast_zmod_eq_zero_iff_dvd]

/-- **The dilated orthogonality identity.**  The residue-class restriction `α ∣ m - s` costs
exactly one extra frequency variable `u`, ranging over `α` values, which shifts the *first*
block's frequency by `u * D`. -/
theorem sum_dilatedBlockPairing_mul_phase {H T α D : ℕ} [NeZero T] [NeZero α]
    (hTD : T = α * D) (b c : Fin H → ℂ) (s : ℤ) (σ : ℕ) (hT : H + σ ≤ T) :
    (∑ t ∈ Finset.range T, ∑ u ∈ Finset.range α,
        dilatedBlockPairing T D b c (t : ℤ) (u : ℤ) * phase T (t : ℤ) σ * phase α (u : ℤ) (-s)) =
      (T : ℂ) * (α : ℂ) * ∑ m : Fin H, dilatedPairShiftEdge b c α s σ m := by
  classical
  have hα : α ≠ 0 := NeZero.ne α
  have hD : D ≠ 0 := by
    rintro rfl
    exact (NeZero.ne T) (by simp [hTD])
  -- expand every summand
  have hexp : ∀ t u : ℤ,
      dilatedBlockPairing T D b c t u * phase T t σ * phase α u (-s) =
        ∑ m : Fin H, ∑ k : Fin H,
          (b m * c k) * (phase T t ((m.1 : ℤ) + σ - k.1) * phase α u ((m.1 : ℤ) - s)) :=
    fun t u ↦ dilatedBlockPairing_mul_phase hTD hα hD b c t u s σ
  simp_rw [hexp]
  -- swap the four sums into ∑_m ∑_k ∑_t ∑_u
  have hswap : (∑ t ∈ Finset.range T, ∑ u ∈ Finset.range α, ∑ m : Fin H, ∑ k : Fin H,
        (b m * c k) * (phase T (t : ℤ) ((m.1 : ℤ) + σ - k.1) *
          phase α (u : ℤ) ((m.1 : ℤ) - s))) =
      ∑ m : Fin H, ∑ k : Fin H, (b m * c k) *
        ((∑ t ∈ Finset.range T, phase T (t : ℤ) ((m.1 : ℤ) + σ - k.1)) *
          (∑ u ∈ Finset.range α, phase α (u : ℤ) ((m.1 : ℤ) - s))) := by
    rw [Finset.sum_comm]
    have step : ∀ u ∈ Finset.range α,
        (∑ t ∈ Finset.range T, ∑ m : Fin H, ∑ k : Fin H,
          (b m * c k) * (phase T (t : ℤ) ((m.1 : ℤ) + σ - k.1) *
            phase α (u : ℤ) ((m.1 : ℤ) - s))) =
        ∑ m : Fin H, ∑ k : Fin H, (b m * c k) *
          ((∑ t ∈ Finset.range T, phase T (t : ℤ) ((m.1 : ℤ) + σ - k.1)) *
            phase α (u : ℤ) ((m.1 : ℤ) - s)) := by
      intro u _
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun m _ ↦ ?_
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun k _ ↦ ?_
      rw [Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_congr rfl step]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun m _ ↦ ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    rw [Finset.mul_sum, Finset.mul_sum]
  rw [hswap]
  -- evaluate both orthogonality sums
  have hortho : ∀ m k : Fin H,
      ((∑ t ∈ Finset.range T, phase T (t : ℤ) ((m.1 : ℤ) + σ - k.1)) *
        (∑ u ∈ Finset.range α, phase α (u : ℤ) ((m.1 : ℤ) - s))) =
      (if m.1 + σ = k.1 then (T : ℂ) else 0) *
        (if (α : ℤ) ∣ (m.1 : ℤ) - s then (α : ℂ) else 0) := by
    intro m k
    rw [sum_phase_block_shift σ hT m k, sum_phase_dvd]
  simp_rw [hortho]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ ↦ ?_
  by_cases hdvd : (α : ℤ) ∣ (m.1 : ℤ) - s
  · by_cases hm : m.1 + σ < H
    · have hmem : (⟨m.1 + σ, hm⟩ : Fin H) ∈ (Finset.univ : Finset (Fin H)) := Finset.mem_univ _
      rw [Finset.sum_eq_single_of_mem _ hmem]
      · have hrfl : m.1 + σ = (⟨m.1 + σ, hm⟩ : Fin H).1 := rfl
        rw [dilatedPairShiftEdge, if_pos hdvd, dif_pos hm, if_pos hrfl, if_pos hdvd]
        ring
      · intro k _ hk
        have hne : ¬ (m.1 + σ = k.1) := fun hEq ↦ hk (Fin.ext hEq.symm)
        simp [hne]
    · have hzero : ∀ k : Fin H, ¬ (m.1 + σ = k.1) := fun k hEq ↦ hm (hEq ▸ k.2)
      rw [dilatedPairShiftEdge, if_pos hdvd, dif_neg hm]
      simp [hzero]
  · rw [dilatedPairShiftEdge, if_neg hdvd]
    simp [hdvd]


/-- The `h`-form of the single-frequency collapse, in the shape the graph mean needs. -/
theorem phase_pair_single_frequency {T α D : ℕ} (hTD : T = α * D) (hα : α ≠ 0) (hD : D ≠ 0)
    (t u h c₁ q : ℤ) :
    phase T t (q * h) * phase α u (-(q * c₁)) = phase T (t * h - u * D * c₁) q := by
  rw [phase_dilate hTD hα hD, phase, phase, phase, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-! ## The dilated prime graph mean and its exact Fourier identity -/

/-- The prime graph mean of the `a`-dilated edge: the prime `p` contributes the edge whose
residue class is `p*c₁ (mod α)` and whose step is `p*h`. -/
def dilatedPairTwistedMean {H : ℕ} (w : ℕ → ℂ) (b c : Fin H → ℂ) (α c₁ h : ℕ)
    (s : Finset ℕ) : ℂ :=
  ∑ p ∈ s, w p * (p : ℂ)⁻¹ * ∑ m : Fin H, dilatedPairShiftEdge b c α ((p * c₁ : ℕ) : ℤ) (p * h) m

/-- The multiplier of the dilated graph: the two frequency variables enter through the *single*
frequency `t*h - u*D*c₁`. -/
def dilatedTwistedMultiplier (T D h c₁ : ℕ) (s : Finset ℕ) (w : ℕ → ℂ) (t u : ℤ) : ℂ :=
  ∑ p ∈ s, w p * (p : ℂ)⁻¹ * phase T (t * h - u * D * c₁) (p : ℤ)

/-- **The dilated multiplier is the *proved* multiplier**, at shift `1` and frequency
`t*h - u*D*c₁`.  Every bound already established for
`NormalNumbers.ElliottTwistedGraph.twistedPrimeGraphMultiplier` — in particular the fourth-moment /
additive-energy bound — therefore applies verbatim. -/
theorem dilatedTwistedMultiplier_eq (T D h c₁ : ℕ) (s : Finset ℕ) (w : ℕ → ℂ) (t u : ℤ) :
    dilatedTwistedMultiplier T D h c₁ s w t u =
      NormalNumbers.ElliottTwistedGraph.twistedPrimeGraphMultiplier T 1 s w
        (t * h - u * D * c₁) := by
  simp [dilatedTwistedMultiplier, NormalNumbers.ElliottTwistedGraph.twistedPrimeGraphMultiplier]

/-- **The exact Fourier identity for the dilated graph mean.**  Compare
`NormalNumbers.ElliottTwistedGraph.pairTwistedPrimeGraphMean_eq_fourier`: the only change is the
extra frequency variable `u`, ranging over the `α` aliases, and the normalisation `(T*α)⁻¹`. -/
theorem dilatedPairTwistedMean_eq_fourier {H T α D : ℕ} [NeZero T] [NeZero α]
    (hTD : T = α * D) (w : ℕ → ℂ) (b c : Fin H → ℂ) (c₁ h : ℕ) (s : Finset ℕ)
    (hT : ∀ p ∈ s, H + p * h ≤ T) :
    dilatedPairTwistedMean w b c α c₁ h s = ((T : ℂ) * α)⁻¹ *
      ∑ t ∈ Finset.range T, ∑ u ∈ Finset.range α,
        dilatedBlockPairing T D b c (t : ℤ) (u : ℤ) *
          dilatedTwistedMultiplier T D h c₁ s w (t : ℤ) (u : ℤ) := by
  classical
  have hα : α ≠ 0 := NeZero.ne α
  have hD : D ≠ 0 := by
    rintro rfl
    exact (NeZero.ne T) (by simp [hTD])
  have hTα : ((T : ℂ) * α) ≠ 0 :=
    mul_ne_zero (Nat.cast_ne_zero.mpr (NeZero.ne T)) (Nat.cast_ne_zero.mpr hα)
  have hswap : (∑ t ∈ Finset.range T, ∑ u ∈ Finset.range α,
        dilatedBlockPairing T D b c (t : ℤ) (u : ℤ) *
          dilatedTwistedMultiplier T D h c₁ s w (t : ℤ) (u : ℤ)) =
      ∑ p ∈ s, ∑ t ∈ Finset.range T, ∑ u ∈ Finset.range α,
        dilatedBlockPairing T D b c (t : ℤ) (u : ℤ) *
          (w p * (p : ℂ)⁻¹ *
            phase T ((t : ℤ) * h - (u : ℤ) * D * c₁) (p : ℤ)) := by
    simp only [dilatedTwistedMultiplier, Finset.mul_sum]
    rw [show (∑ t ∈ Finset.range T, ∑ u ∈ Finset.range α, ∑ p ∈ s,
          dilatedBlockPairing T D b c (t : ℤ) (u : ℤ) *
            (w p * (p : ℂ)⁻¹ * phase T ((t : ℤ) * h - (u : ℤ) * D * c₁) (p : ℤ))) =
        ∑ t ∈ Finset.range T, ∑ p ∈ s, ∑ u ∈ Finset.range α,
          dilatedBlockPairing T D b c (t : ℤ) (u : ℤ) *
            (w p * (p : ℂ)⁻¹ * phase T ((t : ℤ) * h - (u : ℤ) * D * c₁) (p : ℤ)) from
      Finset.sum_congr rfl fun t _ ↦ Finset.sum_comm]
    exact Finset.sum_comm
  have hper : ∀ p ∈ s,
      (∑ t ∈ Finset.range T, ∑ u ∈ Finset.range α,
        dilatedBlockPairing T D b c (t : ℤ) (u : ℤ) *
          (w p * (p : ℂ)⁻¹ *
            phase T ((t : ℤ) * h - (u : ℤ) * D * c₁) (p : ℤ))) =
      ((T : ℂ) * α) * (w p * (p : ℂ)⁻¹ *
        ∑ m : Fin H, dilatedPairShiftEdge b c α ((p * c₁ : ℕ) : ℤ) (p * h) m) := by
    intro p hp
    have hkey := sum_dilatedBlockPairing_mul_phase (H := H) (T := T) (α := α) (D := D)
      hTD b c ((p * c₁ : ℕ) : ℤ) (p * h) (hT p hp)
    calc
      _ = w p * (p : ℂ)⁻¹ * ∑ t ∈ Finset.range T, ∑ u ∈ Finset.range α,
            dilatedBlockPairing T D b c (t : ℤ) (u : ℤ) *
              phase T (t : ℤ) ((p * h : ℕ) : ℤ) * phase α (u : ℤ) (-((p * c₁ : ℕ) : ℤ)) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun t _ ↦ ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun u _ ↦ ?_
        have : phase T (t : ℤ) ((p * h : ℕ) : ℤ) * phase α (u : ℤ) (-((p * c₁ : ℕ) : ℤ)) =
            phase T ((t : ℤ) * h - (u : ℤ) * D * c₁) (p : ℤ) := by
          have := phase_pair_single_frequency (T := T) (α := α) (D := D) hTD hα hD
            (t : ℤ) (u : ℤ) (h : ℤ) (c₁ : ℤ) (p : ℤ)
          push_cast at this ⊢
          rw [← this]
        rw [← this]
        ring
      _ = _ := by rw [hkey]; ring
  rw [hswap, Finset.sum_congr rfl hper, ← Finset.mul_sum, ← mul_assoc,
    inv_mul_cancel₀ hTα, one_mul, dilatedPairTwistedMean]

/-! ## The consequence that keeps the multiplier one-dimensional -/

/-- **The two phases combine into a single frequency in the prime `q`.**  This is why the whole
fourth-moment / large-frequency / entropy stack above the pairing survives the dilation. -/
theorem phase_mul_phase_eq_single_frequency {T α D : ℕ} (hTD : T = α * D) (hα : α ≠ 0)
    (hD : D ≠ 0) (t u : ℤ) (c₁ c₂ : ℤ) (q : ℤ) :
    phase T t (q * (c₂ - c₁)) * phase α u (-(q * c₁)) =
      phase T (t * (c₂ - c₁) - u * D * c₁) q := by
  rw [phase_dilate hTD hα hD, phase, phase, phase, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-! ## Periodicity of the block transform, and the aliased Parseval bound

The `α` aliases `t ↦ t + u*D` permute the frequency range, so Parseval survives the dilation with
the loss exactly `α` (a constant).  Mathlib has no shift lemma for periodic sums over
`Finset.range`, so it is proved here by induction on the shift.
-/

/-- `phase` is periodic in the frequency with period the modulus. -/
theorem phase_add_modulus {T : ℕ} (hT : T ≠ 0) (t x : ℤ) :
    phase T (t + T) x = phase T t x := by
  have hTc : ((T : ℂ)) ≠ 0 := Nat.cast_ne_zero.mpr hT
  rw [phase, phase]
  have hsplit : (2 * (Real.pi : ℂ) * Complex.I * (((t + T : ℤ)) : ℂ) * (x : ℂ) / (T : ℂ)) =
      (2 * (Real.pi : ℂ) * Complex.I * (t : ℂ) * (x : ℂ) / (T : ℂ)) +
        (x : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
    push_cast
    field_simp
  rw [hsplit, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

/-- The block transform is periodic in the frequency with period `T`. -/
theorem blockFourier_add_modulus {H T : ℕ} (hT : T ≠ 0) (b : Fin H → ℂ) (t : ℤ) :
    blockFourier T b (t + T) = blockFourier T b t :=
  Finset.sum_congr rfl fun j _ ↦ by rw [phase_add_modulus hT]

/-- A `T`-periodic function has the same sum over `range T` after any integer shift. -/
theorem sum_range_shift_of_periodic {T : ℕ} (g : ℤ → ℝ) (hg : ∀ t : ℤ, g (t + T) = g t) :
    ∀ k : ℕ, (∑ t ∈ Finset.range T, g ((t : ℤ) + (k : ℤ))) = ∑ t ∈ Finset.range T, g (t : ℤ) := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
      refine Eq.trans ?_ ih
      have e1 := Finset.sum_range_succ' (fun i : ℕ ↦ g ((i : ℤ) + (k : ℤ))) T
      have e2 := Finset.sum_range_succ (fun i : ℕ ↦ g ((i : ℤ) + (k : ℤ))) T
      have e3 : g (((T : ℕ) : ℤ) + (k : ℤ)) = g ((0 : ℤ) + (k : ℤ)) := by
        rw [show (((T : ℕ) : ℤ) + (k : ℤ)) = (k : ℤ) + (T : ℕ) by push_cast; ring, hg]
        simp
      have e5 := e1.symm.trans e2
      rw [e3] at e5
      simp only [Nat.cast_zero, zero_add] at e5
      have e6 := add_right_cancel e5
      rw [← e6]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      congr 1
      push_cast
      ring

/-- Parseval for the aliased first block. -/
theorem sum_norm_sq_blockFourier_shift {H T : ℕ} (hT : T ≠ 0) (b : Fin H → ℂ) (k : ℕ) :
    (∑ t ∈ Finset.range T, ‖blockFourier T b ((t : ℤ) + (k : ℤ))‖ ^ 2) =
      ∑ t ∈ Finset.range T, ‖blockFourier T b (t : ℤ)‖ ^ 2 :=
  sum_range_shift_of_periodic (fun τ ↦ ‖blockFourier T b τ‖ ^ 2)
    (fun τ ↦ by rw [blockFourier_add_modulus hT]) k

/-! ## The large-frequency bound for the dilated mean -/

/-- The pairs of frequencies at which the dilated multiplier is large. -/
def dilatedLargeFrequencies (T D h c₁ α : ℕ) (s : Finset ℕ) (w : ℕ → ℂ) (θ : ℝ) :
    Finset (ℕ × ℕ) :=
  ((Finset.range T) ×ˢ (Finset.range α)).filter fun x ↦
    θ ≤ ‖dilatedTwistedMultiplier T D h c₁ s w (x.1 : ℤ) (x.2 : ℤ)‖

/-- **The large-frequency bound survives the dilation.**  Port of
`NormalNumbers.ElliottTwistedGraph.norm_pairTwistedPrimeGraphMean_le_largeFrequencies`.

Two changes, both harmless: the frequency runs over the `α` aliases as well, and the first block is
transformed at `t + u*D` while the second is at `t`.  The threshold split is unchanged (AM–GM on
the two squares, which are at *different* frequencies), and Parseval survives because each alias
permutes `range T` (`Alias.sum_norm_sq_blockFourier_shift`), costing exactly the factor `α`. -/
theorem norm_dilatedPairTwistedMean_le_largeFrequencies {H T α D : ℕ} [NeZero T] [NeZero α]
    (hTD : T = α * D) (w : ℕ → ℂ) (b c : Fin H → ℂ) (c₁ h : ℕ) (s : Finset ℕ)
    (hHT : H ≤ T) (hT : ∀ p ∈ s, H + p * h ≤ T)
    (hb : ∀ j, ‖b j‖ ≤ 1) (hc : ∀ j, ‖c j‖ ≤ 1)
    {θ M : ℝ} (hθ : 0 ≤ θ)
    (hmult : ∀ x ∈ (Finset.range T) ×ˢ (Finset.range α),
      ‖dilatedTwistedMultiplier T D h c₁ s w (x.1 : ℤ) (x.2 : ℤ)‖ ≤ M) :
    ‖dilatedPairTwistedMean w b c α c₁ h s‖ ≤ θ * H + ((H : ℝ) * M / ((T : ℝ) * α)) *
      ∑ x ∈ dilatedLargeFrequencies T D h c₁ α s w θ,
        ‖blockFourier T b ((x.1 : ℤ) + (x.2 : ℤ) * D)‖ := by
  classical
  have hTne : T ≠ 0 := NeZero.ne T
  have hαne : α ≠ 0 := NeZero.ne α
  have hTr : (0 : ℝ) < T := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hTne)
  have hαr : (0 : ℝ) < α := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hαne)
  set c' : Fin H → ℂ := fun j ↦ conj (c j) with hc'
  have hc'b : ∀ j, ‖c' j‖ ≤ 1 := by
    intro j; rw [hc', RCLike.norm_conj]; exact hc j
  set P : Finset (ℕ × ℕ) := (Finset.range T) ×ˢ (Finset.range α) with hPdef
  -- the pointwise split at the threshold `θ`
  have hpoint : ∀ x ∈ P,
      ‖dilatedBlockPairing T D b c (x.1 : ℤ) (x.2 : ℤ)‖ *
          ‖dilatedTwistedMultiplier T D h c₁ s w (x.1 : ℤ) (x.2 : ℤ)‖ ≤
        θ * ((‖blockFourier T b ((x.1 : ℤ) + (x.2 : ℤ) * D)‖ ^ 2 +
              ‖blockFourier T c' (x.1 : ℤ)‖ ^ 2) / 2) +
          if θ ≤ ‖dilatedTwistedMultiplier T D h c₁ s w (x.1 : ℤ) (x.2 : ℤ)‖ then
            (H : ℝ) * M * ‖blockFourier T b ((x.1 : ℤ) + (x.2 : ℤ) * D)‖ else 0 := by
    intro x hx
    have hcH : ‖blockFourier T c' (x.1 : ℤ)‖ ≤ H := by
      simpa using norm_blockFourier_le T c' (x.1 : ℤ) hc'b
    have hnorm : ‖dilatedBlockPairing T D b c (x.1 : ℤ) (x.2 : ℤ)‖ =
        ‖blockFourier T b ((x.1 : ℤ) + (x.2 : ℤ) * D)‖ * ‖blockFourier T c' (x.1 : ℤ)‖ :=
      norm_dilatedBlockPairing T D b c _ _
    by_cases htlarge : θ ≤ ‖dilatedTwistedMultiplier T D h c₁ s w (x.1 : ℤ) (x.2 : ℤ)‖
    · rw [if_pos htlarge, hnorm]
      have hkey : ‖blockFourier T b ((x.1 : ℤ) + (x.2 : ℤ) * D)‖ *
          ‖blockFourier T c' (x.1 : ℤ)‖ *
          ‖dilatedTwistedMultiplier T D h c₁ s w (x.1 : ℤ) (x.2 : ℤ)‖ ≤
            (H : ℝ) * M * ‖blockFourier T b ((x.1 : ℤ) + (x.2 : ℤ) * D)‖ := by
        have h1 : ‖blockFourier T b ((x.1 : ℤ) + (x.2 : ℤ) * D)‖ *
            ‖blockFourier T c' (x.1 : ℤ)‖ ≤
            ‖blockFourier T b ((x.1 : ℤ) + (x.2 : ℤ) * D)‖ * (H : ℝ) :=
          mul_le_mul_of_nonneg_left hcH (norm_nonneg _)
        calc
          _ ≤ ‖blockFourier T b ((x.1 : ℤ) + (x.2 : ℤ) * D)‖ * (H : ℝ) *
              ‖dilatedTwistedMultiplier T D h c₁ s w (x.1 : ℤ) (x.2 : ℤ)‖ :=
            mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
          _ ≤ ‖blockFourier T b ((x.1 : ℤ) + (x.2 : ℤ) * D)‖ * (H : ℝ) * M :=
            mul_le_mul_of_nonneg_left (hmult x hx) (by positivity)
          _ = _ := by ring
      nlinarith [sq_nonneg ‖blockFourier T b ((x.1 : ℤ) + (x.2 : ℤ) * D)‖,
        sq_nonneg ‖blockFourier T c' (x.1 : ℤ)‖, mul_nonneg hθ
          (add_nonneg (sq_nonneg ‖blockFourier T b ((x.1 : ℤ) + (x.2 : ℤ) * D)‖)
            (sq_nonneg ‖blockFourier T c' (x.1 : ℤ)‖))]
    · rw [if_neg htlarge, add_zero, hnorm]
      have hlt := le_of_not_ge htlarge
      have hamgm : ‖blockFourier T b ((x.1 : ℤ) + (x.2 : ℤ) * D)‖ *
          ‖blockFourier T c' (x.1 : ℤ)‖ ≤
          (‖blockFourier T b ((x.1 : ℤ) + (x.2 : ℤ) * D)‖ ^ 2 +
            ‖blockFourier T c' (x.1 : ℤ)‖ ^ 2) / 2 := by
        nlinarith [sq_nonneg (‖blockFourier T b ((x.1 : ℤ) + (x.2 : ℤ) * D)‖ -
          ‖blockFourier T c' (x.1 : ℤ)‖)]
      have hprodnn : 0 ≤ ‖blockFourier T b ((x.1 : ℤ) + (x.2 : ℤ) * D)‖ *
          ‖blockFourier T c' (x.1 : ℤ)‖ := mul_nonneg (norm_nonneg _) (norm_nonneg _)
      calc
        _ ≤ ‖blockFourier T b ((x.1 : ℤ) + (x.2 : ℤ) * D)‖ *
            ‖blockFourier T c' (x.1 : ℤ)‖ * θ := mul_le_mul_of_nonneg_left hlt hprodnn
        _ = θ * (‖blockFourier T b ((x.1 : ℤ) + (x.2 : ℤ) * D)‖ *
            ‖blockFourier T c' (x.1 : ℤ)‖) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hamgm hθ
  have hsum := Finset.sum_le_sum hpoint
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_filter, ← Finset.mul_sum] at hsum
  -- aliased Parseval on both blocks
  have hpb : (∑ x ∈ P, ‖blockFourier T b ((x.1 : ℤ) + (x.2 : ℤ) * D)‖ ^ 2) ≤ (α : ℝ) * (T * H) := by
    rw [hPdef, Finset.sum_product]
    rw [Finset.sum_comm]
    have hrow : ∀ u ∈ Finset.range α,
        (∑ t ∈ Finset.range T, ‖blockFourier T b ((t : ℤ) + (u : ℤ) * D)‖ ^ 2) ≤ (T : ℝ) * H := by
      intro u _
      have key := sum_norm_sq_blockFourier_shift (T := T) (H := H) hTne b (u * D)
      calc (∑ t ∈ Finset.range T, ‖blockFourier T b ((t : ℤ) + (u : ℤ) * D)‖ ^ 2)
          = ∑ t ∈ Finset.range T, ‖blockFourier T b ((t : ℤ) + ((u * D : ℕ) : ℤ))‖ ^ 2 :=
            Finset.sum_congr rfl fun t _ ↦ by
              norm_cast
        _ = ∑ t ∈ Finset.range T, ‖blockFourier T b (t : ℤ)‖ ^ 2 := key
        _ ≤ (T : ℝ) * H := sum_blockFourier_norm_sq_le b hHT hb
    calc
      _ ≤ ∑ _u ∈ Finset.range α, (T : ℝ) * H := Finset.sum_le_sum hrow
      _ = (α : ℝ) * (T * H) := by simp [mul_comm]
  have hpc : (∑ x ∈ P, ‖blockFourier T c' (x.1 : ℤ)‖ ^ 2) ≤ (α : ℝ) * (T * H) := by
    rw [hPdef, Finset.sum_product]
    have : ∀ t ∈ Finset.range T,
        (∑ _u ∈ Finset.range α, ‖blockFourier T c' (t : ℤ)‖ ^ 2) =
          (α : ℝ) * ‖blockFourier T c' (t : ℤ)‖ ^ 2 := by
      intro t _; simp [mul_comm]
    rw [Finset.sum_congr rfl this, ← Finset.mul_sum]
    have := sum_blockFourier_norm_sq_le c' hHT hc'b
    nlinarith [hαr.le, this]
  have hparseval : (∑ x ∈ P,
      (‖blockFourier T b ((x.1 : ℤ) + (x.2 : ℤ) * D)‖ ^ 2 +
        ‖blockFourier T c' (x.1 : ℤ)‖ ^ 2) / 2) ≤ (T : ℝ) * α * H := by
    rw [← Finset.sum_div, Finset.sum_add_distrib]
    nlinarith [hpb, hpc]
  have htotal := hsum.trans (add_le_add (mul_le_mul_of_nonneg_left hparseval hθ) le_rfl)
  calc
    ‖dilatedPairTwistedMean w b c α c₁ h s‖ ≤ ((T : ℝ) * α)⁻¹ * ∑ x ∈ P,
        ‖dilatedBlockPairing T D b c (x.1 : ℤ) (x.2 : ℤ)‖ *
          ‖dilatedTwistedMultiplier T D h c₁ s w (x.1 : ℤ) (x.2 : ℤ)‖ := by
      rw [dilatedPairTwistedMean_eq_fourier hTD w b c c₁ h s hT, norm_mul, norm_inv, norm_mul,
        Complex.norm_natCast, Complex.norm_natCast]
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      rw [hPdef, Finset.sum_product]
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun t _ ↦ ?_)
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun u _ ↦ ?_)
      rw [norm_mul]
    _ ≤ ((T : ℝ) * α)⁻¹ * (θ * ((T : ℝ) * α * H) + H * M *
        ∑ x ∈ dilatedLargeFrequencies T D h c₁ α s w θ,
          ‖blockFourier T b ((x.1 : ℤ) + (x.2 : ℤ) * D)‖) := by
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      rw [dilatedLargeFrequencies, hPdef]
      exact htotal
    _ = _ := by field_simp


/-! ## Closing the loop: the dilated edge on affine blocks IS the affine observable

`NormalNumbers.ElliottAffineGraph.norm_logProb_affineTwistedObservable_sub_correlation_le` controls
the logarithmic mean of `pairObservable f₁ f₂ a (q c₁) (q c₂)` over the window.  The graph side of
the argument sees, instead, the *block* edge `dilatedPairShiftEdge`.  This section identifies the
two: on the block re-based at `a*(n+1)`, the edge at a position `m` of the residue class
`q*c₁ (mod a)` is literally the affine observable at the point `n + 1 + (m - q c₁)/a`.

That is the whole content of the re-basing: the residue class `q*c₁ (mod a)` in the block index is
what the divisibility `a ∣ ·` of the slice route tried, and failed, to express as an indicator on
the *observable*.  Here it is an index condition, and the previous sections showed the Fourier layer
absorbs it for the price of `α` aliases.
-/

open NormalNumbers.ElliottLadder in
/-- The block of `f` re-based at `a*(n+1)`: the positions the `a`-dilated edge samples. -/
def affineBlock (f : ℕ → ℂ) (a n H : ℕ) : Fin H → ℂ :=
  fun i ↦ positiveIntExtension f (((a * (n + 1) : ℕ) : ℤ) + (i.1 : ℤ))

open NormalNumbers.ElliottLadder in
/-- **The dilated block edge is the affine pair observable.**  At block position
`m = a*k + q*c₁` (the general element of the residue class `q*c₁ (mod a)`), the edge with step
`q*h` equals `pairObservable f₁ f₂ a (q*c₁) (q*c₂) (n+1+k)` with `c₂ = c₁ + h`. -/
theorem dilatedPairShiftEdge_affineBlock {H : ℕ} (f₁ f₂ : ℕ → ℂ) (a n q c₁ h k : ℕ)
    (hm : a * k + q * c₁ < H) (hmσ : a * k + q * c₁ + q * h < H) :
    dilatedPairShiftEdge (affineBlock f₁ a n H) (affineBlock f₂ a n H) a ((q * c₁ : ℕ) : ℤ)
        (q * h) ⟨a * k + q * c₁, hm⟩ =
      pairObservable f₁ f₂ a ((q * c₁ : ℕ) : ℤ) ((q * (c₁ + h) : ℕ) : ℤ) (n + 1 + k) := by
  have hdvd : (a : ℤ) ∣ ((a * k + q * c₁ : ℕ) : ℤ) - ((q * c₁ : ℕ) : ℤ) := by
    refine ⟨(k : ℤ), ?_⟩
    push_cast
    ring
  rw [dilatedPairShiftEdge, if_pos hdvd, dif_pos hmσ, affineBlock, affineBlock, pairObservable]
  congr 1
  · congr 1
    simp only [integerAffine]
    push_cast
    ring
  · congr 1
    simp only [integerAffine]
    push_cast
    ring


/-! ## The edge sum as a sum along the progression -/

/-- A block extended by zero off its index range. -/
def blockExtend {H : ℕ} (b : Fin H → ℂ) : ℕ → ℂ :=
  fun i ↦ if h : i < H then b ⟨i, h⟩ else 0

theorem dilatedPairShiftEdge_eq_extend {H : ℕ} (b c : Fin H → ℂ) (α : ℕ) (s : ℤ) (σ : ℕ)
    (m : Fin H) :
    dilatedPairShiftEdge b c α s σ m =
      if (α : ℤ) ∣ (m.1 : ℤ) - s then blockExtend b m.1 * blockExtend c (m.1 + σ) else 0 := by
  by_cases hdvd : (α : ℤ) ∣ (m.1 : ℤ) - s
  · rw [dilatedPairShiftEdge, if_pos hdvd, if_pos hdvd]
    unfold blockExtend
    rw [dif_pos m.2]
    by_cases hm : m.1 + σ < H
    · rw [dif_pos hm, dif_pos hm]
    · rw [dif_neg hm, dif_neg hm, mul_zero]
  · rw [dilatedPairShiftEdge, if_neg hdvd, if_neg hdvd]

/-- **The dilated edge sum is a sum along the arithmetic progression `r, r+α, r+2α, …`**, where
`r = s mod α`.  This is the reindexing that turns the graph side into a sum of affine pair
observables (`dilatedPairShiftEdge_affineBlock`). -/
theorem sum_dilatedPairShiftEdge_eq_progression {H : ℕ} (b c : Fin H → ℂ) {α : ℕ} (hα : 0 < α)
    (s : ℤ) (σ : ℕ) :
    (∑ m : Fin H, dilatedPairShiftEdge b c α s σ m) =
      ∑ j ∈ (Finset.range H).filter (fun j ↦ α * j + (s % (α : ℤ)).toNat < H),
        blockExtend b (α * j + (s % (α : ℤ)).toNat) *
          blockExtend c (α * j + (s % (α : ℤ)).toNat + σ) := by
  classical
  set r : ℕ := (s % (α : ℤ)).toNat with hrdef
  have hαZ : (0 : ℤ) < (α : ℤ) := by exact_mod_cast hα
  have hmod_nonneg : 0 ≤ s % (α : ℤ) := Int.emod_nonneg s (by exact_mod_cast hα.ne')
  have hrZ : (r : ℤ) = s % (α : ℤ) := by rw [hrdef, Int.toNat_of_nonneg hmod_nonneg]
  have hrlt : r < α := by
    have := Int.emod_lt_of_pos s hαZ
    omega
  -- the divisibility condition is a congruence on the block index
  have hmem : ∀ i : ℕ, ((α : ℤ) ∣ (i : ℤ) - s) ↔ i % α = r := by
    intro i
    have hiff : ((α : ℤ) ∣ (i : ℤ) - s) ↔ s % (α : ℤ) = (i : ℤ) % (α : ℤ) :=
      Iff.symm Int.modEq_iff_dvd
    rw [hiff, ← hrZ, ← Int.natCast_mod]
    constructor <;> intro hh <;> exact_mod_cast hh.symm
  have hkey : ∀ i : ℕ, i % α = r → α * (i / α) + r = i := by
    intro i hi
    have := Nat.div_add_mod i α
    omega
  have hkey2 : ∀ i : ℕ, i % α = r → (i - r) / α = i / α := by
    intro i hi
    have h1 := hkey i hi
    have : i - r = α * (i / α) := by omega
    rw [this, Nat.mul_div_cancel_left _ hα]
  calc
    (∑ m : Fin H, dilatedPairShiftEdge b c α s σ m)
        = ∑ i ∈ Finset.range H,
            (if (α : ℤ) ∣ (i : ℤ) - s then blockExtend b i * blockExtend c (i + σ) else 0) := by
          refine Eq.trans (Finset.sum_congr rfl fun m _ ↦
            dilatedPairShiftEdge_eq_extend b c α s σ m) ?_
          exact Fin.sum_univ_eq_sum_range (fun i ↦ if (α : ℤ) ∣ (i : ℤ) - s then
              blockExtend b i * blockExtend c (i + σ) else 0) H
    _ = ∑ i ∈ (Finset.range H).filter (fun i ↦ i % α = r),
            blockExtend b i * blockExtend c (i + σ) := by
          rw [Finset.sum_filter]
          refine Finset.sum_congr rfl fun i _ ↦ ?_
          by_cases hi : i % α = r
          · rw [if_pos ((hmem i).mpr hi), if_pos hi]
          · rw [if_neg (fun hd ↦ hi ((hmem i).mp hd)), if_neg hi]
    _ = _ := by
          refine Finset.sum_nbij' (i := fun i ↦ (i - r) / α) (j := fun j ↦ α * j + r)
            ?_ ?_ ?_ ?_ ?_
          · intro i hi
            simp only [Finset.mem_filter, Finset.mem_range] at hi ⊢
            obtain ⟨hiH, hir⟩ := hi
            have h1 := hkey i hir
            have h2 := hkey2 i hir
            have h3 : i / α ≤ i := Nat.div_le_self i α
            rw [h2]
            exact ⟨lt_of_le_of_lt h3 hiH, by rw [h1]; exact hiH⟩
          · intro j hj
            simp only [Finset.mem_filter, Finset.mem_range] at hj ⊢
            refine ⟨by omega, ?_⟩
            rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hrlt]
          · intro i hi
            simp only [Finset.mem_filter, Finset.mem_range] at hi
            obtain ⟨hiH, hir⟩ := hi
            have h1 := hkey i hir
            have h2 := hkey2 i hir
            rw [h2]
            exact h1
          · intro j hj
            simp only [Finset.mem_filter, Finset.mem_range] at hj
            simp [Nat.mul_div_cancel_left _ hα]
          · intro i hi
            simp only [Finset.mem_filter, Finset.mem_range] at hi
            obtain ⟨hiH, hir⟩ := hi
            have h1 := hkey i hir
            have h2 := hkey2 i hir
            rw [h2, h1]

end

end NormalNumbers.ElliottDilatedPairing
