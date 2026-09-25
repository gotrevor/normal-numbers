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

end

end NormalNumbers.ElliottDilatedPairing
