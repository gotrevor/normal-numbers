import NormalNumbers.PrimeLambertConfig

/-!
# Exact six-for-three geometry: hexagons, tensoring, and the coprime transform

Signed configurations of tail shifts live in the group ring `ℤ[ℤ × ℤ]`
(`AddMonoidAlgebra ℤ (ℤ × ℤ)`): a point `(u, s)` is a multiplier displacement `u` and a
numerator-shift displacement `s`.  The site-`j` projection is the additive map
`ℓ j (u, s) = j·u − s`, and a configuration *cancels at `j`* when its pushforward along
`ℓ j` vanishes.

* `edge g = 1 − δ_g` cancels at `j` whenever `ℓ j g = 0` (`cancels_edge`).
* Cancellation is an ideal property: `Cancels f j → Cancels (f * g) j` (`Cancels.mul_right`),
  because `ℓ j` induces a ring hom of group rings (`AddMonoidAlgebra.mapDomain_mul`).
* The hexagon of a triple `i < j < k` is `edge g_i * edge g_j * edge g_k` with
  `g_h = (v_h, h·v_h)`, `(v_i, v_j, v_k) = (k−j, i−k, j−i)`; it cancels at `i, j, k`
  (`hexagon_cancels`).  Its expanded six-atom form is `hexagon_eq_six`.
* Scaling by an integer `B` preserves cancellation (`Cancels.scale`); the tensor
  `hexTensor r B` of the `2r` scaled hexagons partitioning sites `1..6r` cancels at every
  site `1 ≤ j ≤ 6r` (`hexTensor_cancels`).
* The coprime transform `(u, s) ↦ (1 + Q(D + u), Q s)` carries any configuration cancelling at
  `j` to a `TConfig` cancelling at `j` (`cancelsAt_toConfig`), since the transformed projection
  is `j + Q(jD + ℓ j (u,s))`, an injective affine image of `ℓ j`.  Multipliers are positive
  (`toConfig_pos`) and pairwise coprime for `Q` divisible by all nonzero `|u − u'|`
  (`transform_coprime`).

Everything here is exact algebra; no estimate is used.
-/

open scoped BigOperators

noncomputable section

namespace NormalNumbers.PrimeLambert

/-- The lattice of signed tail shifts. -/
abbrev Lat := ℤ × ℤ

/-- Signed configurations: the group ring `ℤ[ℤ × ℤ]`. -/
abbrev Cfg := AddMonoidAlgebra ℤ Lat

/-- Site-`j` projection `(u, s) ↦ j·u − s` as an additive hom. -/
def ℓ (j : ℕ) : Lat →+ ℤ where
  toFun x := (j : ℤ) * x.1 - x.2
  map_zero' := by simp
  map_add' x y := by simp only [Prod.fst_add, Prod.snd_add]; ring

@[simp] lemma ℓ_apply (j : ℕ) (x : Lat) : ℓ j x = (j : ℤ) * x.1 - x.2 := rfl

/-- `f` cancels at site `j`: the pushforward of its coefficients along `ℓ j` vanishes. -/
def Cancels (f : Cfg) (j : ℕ) : Prop := Finsupp.mapDomain (ℓ j) f.coeff = 0

/-- Cancellation in group-ring form. -/
lemma cancels_iff (f : Cfg) (j : ℕ) : Cancels f j ↔ AddMonoidAlgebra.mapDomain (ℓ j) f = 0 := by
  unfold Cancels
  rw [← AddMonoidAlgebra.coeff_inj, AddMonoidAlgebra.coeff_mapDomain]
  rfl

theorem Cancels.mul_right {f : Cfg} {j : ℕ} (hf : Cancels f j) (g : Cfg) : Cancels (f * g) j := by
  rw [cancels_iff] at *
  rw [AddMonoidAlgebra.mapDomain_mul (ℓ j), hf, zero_mul]

theorem Cancels.mul_left {f : Cfg} {j : ℕ} (hf : Cancels f j) (g : Cfg) : Cancels (g * f) j := by
  rw [cancels_iff] at *
  rw [AddMonoidAlgebra.mapDomain_mul (ℓ j), hf, mul_zero]

/-- The two-atom switching element `1 − δ_g`. -/
def edge (g : Lat) : Cfg := 1 - AddMonoidAlgebra.single g 1

theorem cancels_edge {g : Lat} {j : ℕ} (h : ℓ j g = 0) : Cancels (edge g) j := by
  unfold Cancels edge
  rw [AddMonoidAlgebra.coeff_sub, AddMonoidAlgebra.one_def, AddMonoidAlgebra.coeff_single,
    AddMonoidAlgebra.coeff_single, Finsupp.mapDomain_sub, Finsupp.mapDomain_single,
    Finsupp.mapDomain_single, h, map_zero, sub_self]

/-- Direction vector of site `h` with multiplier displacement `v`: `(v, h·v)`; it lies in
`ker (ℓ h)`. -/
def dir (h : ℕ) (v : ℤ) : Lat := (v, (h : ℤ) * v)

@[simp] lemma ℓ_dir (h : ℕ) (v : ℤ) : ℓ h (dir h v) = 0 := by simp [dir]

/-- The hexagon of a triple `i < j < k`: `edge g_i * edge g_j * edge g_k` with
`(v_i, v_j, v_k) = (k − j, i − k, j − i)`. -/
def hexagon (i j k : ℕ) : Cfg :=
  edge (dir i ((k : ℤ) - j)) * edge (dir j ((i : ℤ) - k)) * edge (dir k ((j : ℤ) - i))

theorem hexagon_cancels (i j k : ℕ) (h : ℕ) (hh : h = i ∨ h = j ∨ h = k) :
    Cancels (hexagon i j k) h := by
  unfold hexagon
  rcases hh with rfl | rfl | rfl
  · exact ((cancels_edge (ℓ_dir _ _)).mul_right _).mul_right _
  · exact ((cancels_edge (ℓ_dir _ _)).mul_left _).mul_right _
  · exact (cancels_edge (ℓ_dir _ _)).mul_left _

/-- The three hexagon directions sum to zero. -/
lemma dir_sum_zero (i j k : ℕ) :
    dir i ((k : ℤ) - j) + dir j ((i : ℤ) - k) + dir k ((j : ℤ) - i) = 0 := by
  simp only [dir, Prod.mk_add_mk, Prod.mk_eq_zero]
  constructor <;> ring

/-- **Six-for-three**: the eight subset terms collapse to six atoms, `−δ_{g_h} + δ_{−g_h}`. -/
theorem hexagon_eq_six (i j k : ℕ) :
    hexagon i j k =
      (AddMonoidAlgebra.single (-dir i ((k : ℤ) - j)) 1 - AddMonoidAlgebra.single (dir i ((k : ℤ) - j)) 1)
      + (AddMonoidAlgebra.single (-dir j ((i : ℤ) - k)) 1 - AddMonoidAlgebra.single (dir j ((i : ℤ) - k)) 1)
      + (AddMonoidAlgebra.single (-dir k ((j : ℤ) - i)) 1 - AddMonoidAlgebra.single (dir k ((j : ℤ) - i)) 1) := by
  unfold hexagon edge
  set a := dir i ((k : ℤ) - j)
  set b := dir j ((i : ℤ) - k)
  set c := dir k ((j : ℤ) - i)
  have habc : a + b + c = 0 := dir_sum_zero i j k
  have hab : a + b = -c := eq_neg_of_add_eq_zero_left habc
  have hac : a + c = -b := eq_neg_of_add_eq_zero_left (by rw [show a + c + b = a + b + c by abel]; exact habc)
  have hbc : b + c = -a := eq_neg_of_add_eq_zero_left (by rw [show b + c + a = a + b + c by abel]; exact habc)
  simp only [sub_mul, mul_sub, one_mul, mul_one, AddMonoidAlgebra.single_mul_single, hab, hac, hbc,
    neg_add_cancel, ← AddMonoidAlgebra.one_def]
  abel

/-! ### Scaling and tensoring -/

/-- Dilation of the lattice by `B`. -/
def dil (B : ℤ) : Lat →+ Lat where
  toFun x := (B * x.1, B * x.2)
  map_zero' := by simp
  map_add' x y := by ext <;> simp [mul_add]

lemma ℓ_dil (j : ℕ) (B : ℤ) (x : Lat) : ℓ j (dil B x) = B * ℓ j x := by
  simp [dil]; ring

/-- Scale a configuration by `B`. -/
def dilate (B : ℤ) (f : Cfg) : Cfg := AddMonoidAlgebra.mapDomain (dil B) f

theorem Cancels.scale {f : Cfg} {j : ℕ} (hf : Cancels f j) (B : ℤ) : Cancels (dilate B f) j := by
  unfold Cancels at *
  unfold dilate
  have h1 : (⇑(ℓ j) : Lat → ℤ) ∘ ⇑(dil B) = (fun t : ℤ => B * t) ∘ ⇑(ℓ j) := by
    funext x; exact ℓ_dil j B x
  rw [AddMonoidAlgebra.coeff_mapDomain, ← Finsupp.mapDomain_comp, h1, Finsupp.mapDomain_comp, hf,
    Finsupp.mapDomain_zero]

/-- The block-`t` pair of hexagons: `(6t+1, 6t+2, 6t+4)` scaled by `B^(2t)` and
`(6t+3, 6t+5, 6t+6)` scaled by `B^(2t+1)`. -/
def hexBlock (B : ℤ) (t : ℕ) : Cfg :=
  dilate (B ^ (2 * t)) (hexagon (6 * t + 1) (6 * t + 2) (6 * t + 4)) *
    dilate (B ^ (2 * t + 1)) (hexagon (6 * t + 3) (6 * t + 5) (6 * t + 6))

/-- The tensor of the first `r` blocks, cancelling sites `1..6r`. -/
def hexTensor (r : ℕ) (B : ℤ) : Cfg := ∏ t ∈ Finset.range r, hexBlock B t

theorem hexBlock_cancels (B : ℤ) (t j : ℕ) (h1 : 6 * t + 1 ≤ j) (h2 : j ≤ 6 * t + 6) :
    Cancels (hexBlock B t) j := by
  unfold hexBlock
  have : j = 6 * t + 1 ∨ j = 6 * t + 2 ∨ j = 6 * t + 4 ∨ j = 6 * t + 3 ∨ j = 6 * t + 5 ∨ j = 6 * t + 6 := by
    omega
  rcases this with h | h | h | h | h | h
  · exact ((hexagon_cancels _ _ _ j (by omega)).scale _).mul_right _
  · exact ((hexagon_cancels _ _ _ j (by omega)).scale _).mul_right _
  · exact ((hexagon_cancels _ _ _ j (by omega)).scale _).mul_right _
  · exact ((hexagon_cancels _ _ _ j (by omega)).scale _).mul_left _
  · exact ((hexagon_cancels _ _ _ j (by omega)).scale _).mul_left _
  · exact ((hexagon_cancels _ _ _ j (by omega)).scale _).mul_left _

theorem Cancels.prod {ι : Type*} [DecidableEq ι] (s : Finset ι) (g : ι → Cfg) (j : ℕ)
    (hs : ∃ t ∈ s, Cancels (g t) j) : Cancels (∏ t ∈ s, g t) j := by
  obtain ⟨t, ht, hc⟩ := hs
  rw [← Finset.mul_prod_erase s g ht]
  exact hc.mul_right _

/-- **Tensor cancellation**: `hexTensor r B` cancels at every site `1 ≤ j ≤ 6r`, for any `B`. -/
theorem hexTensor_cancels (r : ℕ) (B : ℤ) (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ 6 * r) :
    Cancels (hexTensor r B) j := by
  unfold hexTensor
  refine Cancels.prod _ _ _ ⟨(j - 1) / 6, Finset.mem_range.mpr (by omega), ?_⟩
  exact hexBlock_cancels B _ j (by omega) (by omega)

/-! ### The coprime transform to a `TConfig` -/

/-- `(u, s) ↦ (1 + Q(D + u), Q s)`; the multiplier is read in `ℕ` via `toNat`. -/
def transform (Q D : ℤ) (x : Lat) : ℕ × ℤ := ((1 + Q * (D + x.1)).toNat, Q * x.2)

/-- The transported configuration of `f`. -/
def toConfig (Q D : ℤ) (f : Cfg) : TConfig := Finsupp.mapDomain (transform Q D) f.coeff

/-- The transformed projection is the affine image `j + Q(jD + ℓ j x)` of the old one. -/
lemma proj_transform (Q D : ℤ) (j : ℕ) (x : Lat) (hx : 0 ≤ 1 + Q * (D + x.1)) :
    proj j (transform Q D x) = (j : ℤ) + Q * ((j : ℤ) * D + ℓ j x) := by
  simp only [proj, transform, ℓ_apply]
  rw [Int.toNat_of_nonneg hx]
  ring

/-- **Transport of cancellation.**  If `f` cancels at `j` and `D + u ≥ 0` on the support
(with `Q ≥ 0`), then the transported configuration cancels at `j`. -/
theorem cancelsAt_toConfig (Q D : ℤ) (hQ : 0 ≤ Q) (f : Cfg) (j : ℕ)
    (hD : ∀ x ∈ f.coeff.support, 0 ≤ D + x.1) (hf : Cancels f j) :
    CancelsAt (toConfig Q D f) j := by
  unfold CancelsAt toConfig
  unfold Cancels at hf
  rw [← Finsupp.mapDomain_comp]
  have h : ∀ x ∈ f.coeff.support, (proj j ∘ transform Q D) x
      = ((fun t : ℤ => (j : ℤ) + Q * ((j : ℤ) * D + t)) ∘ ⇑(ℓ j)) x := by
    intro x hx
    simp only [Function.comp]
    exact proj_transform Q D j x (by have := hD x hx; positivity)
  rw [Finsupp.mapDomain_congr h, Finsupp.mapDomain_comp, hf, Finsupp.mapDomain_zero]

/-- Transformed multipliers are positive on the support (for `Q, D + u ≥ 0`). -/
theorem transform_pos (Q D : ℤ) (hQ : 0 ≤ Q) (x : Lat) (hx : 0 ≤ D + x.1) :
    (transform Q D x).1 ≠ 0 := by
  simp only [transform]
  have : 0 < 1 + Q * (D + x.1) := by positivity
  omega

/-- The support of the transported configuration lies in the image of the support. -/
lemma toConfig_support_subset (Q D : ℤ) (f : Cfg) :
    (toConfig Q D f).support ⊆ f.coeff.support.image (transform Q D) :=
  Finsupp.mapDomain_support

/-- Positivity of every multiplier in the transported configuration. -/
theorem toConfig_pos (Q D : ℤ) (hQ : 0 ≤ Q) (f : Cfg)
    (hD : ∀ x ∈ f.coeff.support, 0 ≤ D + x.1) :
    ∀ a ∈ (toConfig Q D f).support, a.1 ≠ 0 := by
  intro a ha
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp (toConfig_support_subset Q D f ha)
  exact transform_pos Q D hQ x (hD x hx)

/-- **Pairwise coprimality** of transformed multipliers: if every prime dividing the nonzero
difference `u − u'` divides `Q`, then `gcd(1 + Q(D+u), 1 + Q(D+u')) = 1`. -/
theorem transform_coprime (Q D u u' : ℤ) (_huu : u ≠ u')
    (hQ : ∀ p : ℕ, p.Prime → (p : ℤ) ∣ u - u' → (p : ℤ) ∣ Q) :
    IsCoprime (1 + Q * (D + u)) (1 + Q * (D + u')) := by
  rw [Int.isCoprime_iff_gcd_eq_one]
  by_contra hne
  obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hne
  have h1 : (p : ℤ) ∣ 1 + Q * (D + u) :=
    (Int.natCast_dvd_natCast.mpr hpd).trans (Int.gcd_dvd_left _ _)
  have h2 : (p : ℤ) ∣ 1 + Q * (D + u') :=
    (Int.natCast_dvd_natCast.mpr hpd).trans (Int.gcd_dvd_right _ _)
  have hdiff : (p : ℤ) ∣ Q * (u - u') := by
    have := dvd_sub h1 h2
    rwa [show 1 + Q * (D + u) - (1 + Q * (D + u')) = Q * (u - u') by ring] at this
  have hpQ : (p : ℤ) ∣ Q := by
    rcases (Int.Prime.dvd_mul' hp hdiff) with h | h
    · exact h
    · exact hQ p hp h
  have : (p : ℤ) ∣ 1 := by
    have := dvd_sub h1 (dvd_mul_of_dvd_left hpQ (D + u))
    simpa using this
  exact hp.one_lt.ne' (by exact_mod_cast Int.eq_one_of_dvd_one (by positivity) this)

/-- A shift `D` dominating every multiplier displacement on the support. -/
def domShift (f : Cfg) : ℤ := (f.coeff.support.sup fun x => x.1.natAbs : ℕ)

lemma domShift_add_nonneg (f : Cfg) (x : Lat) (hx : x ∈ f.coeff.support) : 0 ≤ domShift f + x.1 := by
  have h : x.1.natAbs ≤ f.coeff.support.sup fun y => y.1.natAbs :=
    Finset.le_sup (f := fun y : Lat => y.1.natAbs) hx
  unfold domShift
  have : (x.1.natAbs : ℤ) ≤ (f.coeff.support.sup fun y => y.1.natAbs : ℕ) := by exact_mod_cast h
  omega

/-- **Assembly**: for every `r` and `Q ≥ 0` there is a transported configuration (the hexagon
tensor at any scale `B`) that cancels at every site `1 ≤ j ≤ 6r` and has positive multipliers.
-/
theorem exists_tconfig_cancelling (r : ℕ) (B Q : ℤ) (hQ : 0 ≤ Q) :
    ∃ c : TConfig, (∀ j, 1 ≤ j → j ≤ 6 * r → CancelsAt c j) ∧ ∀ a ∈ c.support, a.1 ≠ 0 := by
  refine ⟨toConfig Q (domShift (hexTensor r B)) (hexTensor r B), fun j h1 h2 => ?_, ?_⟩
  · exact cancelsAt_toConfig Q _ hQ _ j (domShift_add_nonneg _) (hexTensor_cancels r B j h1 h2)
  · exact toConfig_pos Q _ hQ _ (domShift_add_nonneg _)

end NormalNumbers.PrimeLambert

end
