/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.AdderBaseG
import NormalNumbers.HittingSetSparse

/-!
# The carry-consistency reduction 🧵

The ambient state space of a single-track base-`g` family
`(m₁,0,w), …, (mₙ,0,w)` is the **product** `∏ᵢ mᵢ · g^(ℓ−1)`, and that product is
what `checkCertA` sweeps.  For the hitting-set families this explodes: the `(6,1)`
set `{1,8,11,14,16,20,23}` has `9067520` ambient states and the `(2,4)` set
`{1,3,…,17}` has `8^9 · 34459425 ≈ 4.6·10^15`.

**But the carries of the channels are not independent.**  All channels read the
*same* real `X`, and `carryTG g m 0 X 0 n = ⌊m · fract(X·gⁿ)⌋`
(`carryTG_single`), so the joint carry vector at step `n` is
`(⌊m₁ t⌋, …, ⌊mₙ t⌋)` for the single parameter `t = fract(X·gⁿ) ∈ [0,1)`.  The
reachable set is therefore a **one-parameter curve**, of size at most
`Σᵢ (mᵢ − 1) + 1` rather than `∏ᵢ mᵢ`: for `(6,1)`, `76` states instead of nine
million.

With `N = lcm(mᵢ)` the curve is finitely parametrized —
`⌊mᵢ t⌋ = (mᵢ · ⌊N t⌋)/N` (`floor_mul_of_dvd`) — so the whole reachable set is the
image of `k ↦ Σᵢ ((mᵢ·k)/N)·strideᵢ` over `k < N`, a `decide`-sized fact.

`signed_engine_g_single_reduced` is `signed_engine_g_single` run on the relabelled
state space: the certificate is checked on `[0, S')` with `Lget : ℕ → ℕ` the state
list and `idxf` its inverse, and the only extra hypothesis is that `idxf` is a
section over the states the walk actually visits.

Word length `ℓ ≥ 2` needs one more parameter (the window digits of `mᵢ·X` depend
on `⌊X·gⁿ⌋ mod g` as well as on `t`), so this file covers `ℓ = 1` families;
`(3,2)` and `(2,4)` are the open cases.
-/

namespace NormalNumbers.Adder

open NormalNumbers

/-! ## The carry is a function of one real parameter -/

/-- The single-track carry: `carryTG` of a channel `(a, 0)` at step `n` is
`⌊a · fract(X·gⁿ)⌋` — a function of the tail `fract(X·gⁿ)` alone. -/
theorem carryTG_single (g : ℕ) (a : ℤ) (X : ℝ) (n : ℕ) :
    carryTG g a 0 X 0 n = ⌊(a : ℝ) * Int.fract (X * (g : ℝ) ^ n)⌋ := by
  unfold carryTG
  have h : (a : ℝ) * Int.fract (X * (g : ℝ) ^ n)
      = (a : ℝ) * X * (g : ℝ) ^ n - ((a * ⌊X * (g : ℝ) ^ n⌋ : ℤ) : ℝ) := by
    rw [Int.fract]
    push_cast
    ring
  rw [h, Int.floor_sub_intCast]
  have h2 : ((a : ℝ) * X + ((0:ℤ) : ℝ) * (0 : ℝ)) * (g : ℝ) ^ n = (a : ℝ) * X * (g : ℝ) ^ n := by
    push_cast; ring
  rw [h2]
  ring

/-- With `a ∣ N` the value `⌊a·t⌋` is determined by `⌊N·t⌋`. -/
theorem floor_mul_of_dvd {a q : ℕ} (hq : 0 < q) (t : ℝ) :
    ⌊(a : ℝ) * t⌋ = ⌊((a * q : ℕ) : ℝ) * t⌋ / (q : ℤ) := by
  have h : ((a * q : ℕ) : ℝ) * t / (q : ℝ) = (a : ℝ) * t := by
    have hq' : (q : ℝ) ≠ 0 := by positivity
    push_cast
    field_simp
  rw [← h, Int.floor_div_natCast]


/-! ## The relabelled engine -/

/-- **The reduced single-track base-`g` engine.**  Identical to
`signed_engine_g_single` except that the certificate is checked on a relabelled
state space `[0, S')`: `Lget j` is the `j`-th state of the reachable list and
`idxf` is its inverse there.  The extra hypothesis `hsec` says exactly that
`idxf` is a section of `Lget` on the states the shadow walk of `X` visits — for
a word-length-`1` family this is the carry-consistency fact above, a
`decide`-sized statement about `k ↦ Σᵢ ((mᵢ·k)/N)·strideᵢ`. -/
theorem signed_engine_g_single_reduced (g : ℕ) (hg : 2 ≤ g) (chs : List ZChannel) {S' : ℕ}
    (Lget idxf : ℕ → ℕ)
    {live : ℕ → Bool} {rho omega : ℕ → ℕ} {forced : ℕ → Option (ℕ × ℕ)}
    (hcert : checkCertA (fun σ j => (gfamPred g chs (σ % g) (σ / g) (Lget j)).map idxf)
      g S' live rho omega forced = true)
    (X : ℝ) (hX : Irrational X)
    (hpos : ∀ ch ∈ chs, 1 ≤ ch.posSum) (hell : ∀ ch ∈ chs, 1 ≤ ch.ell)
    (hword : ∀ ch ∈ chs, ∀ d ∈ ch.word, d < g)
    (hlt : ∀ m : ℕ, idxf (gfamState g chs X 0 m) < S')
    (hsec : ∀ m : ℕ, Lget (idxf (gfamState g chs X 0 m)) = gfamState g chs X 0 m) :
    ∃ ch ∈ chs, ∀ N, ∃ n, N ≤ n ∧ OccursAt g (ch.a * X) ch.word n := by
  have hg1 : 1 ≤ g := by omega
  by_contra hcon
  push Not at hcon
  have h : ∀ ch ∈ chs, ∃ N, ∀ n, N ≤ n
      → ¬ OccursAt g (ch.a * X + ch.b * (0:ℝ)) ch.word n := by
    intro ch hch
    obtain ⟨N, hN⟩ := hcon ch hch
    refine ⟨N, fun n hn hocc => hN n hn ?_⟩
    rw [show ch.a * X + ch.b * (0:ℝ) = ch.a * X from by ring] at hocc
    exact hocc
  obtain ⟨N₀, hN₀⟩ := gexists_uniform_no_occurrence g chs X 0 h
  have hzero : ∀ m, (gdigit g (0 : ℝ) m).toNat = 0 := fun m => by
    rw [gdigit_zero]; rfl
  have hσ : ∀ m, (gdigit g X (N₀ + m)).toNat < g :=
    fun m => gdigit_toNat_lt g hg1 X (N₀ + m)
  have hstep0 : ∀ m, HStepA (fun σ s' => gfamPred g chs (σ % g) (σ / g) s')
      (gfamState g chs X 0 (N₀ + m)) ((gdigit g X (N₀ + m)).toNat)
      (gfamState g chs X 0 (N₀ + (m + 1))) := by
    intro m
    have h₀ := ghstep_gfamState g hg chs X 0 (N₀ + m) hpos hell hword
      (fun ch hch => hN₀ ch hch (N₀ + m) (by omega))
    rw [hzero (N₀ + m), Nat.mul_zero, Nat.add_zero] at h₀
    exact h₀
  have hstep : ∀ m, HStepA (fun σ j => (gfamPred g chs (σ % g) (σ / g) (Lget j)).map idxf)
      (idxf (gfamState g chs X 0 (N₀ + m))) ((gdigit g X (N₀ + m)).toNat)
      (idxf (gfamState g chs X 0 (N₀ + (m + 1)))) := by
    intro m
    have hs := hstep0 m
    unfold HStepA at hs ⊢
    simp only []
    rw [hsec (N₀ + (m + 1))]
    simp only [hs, Option.map_some]
  obtain ⟨N, p, hp, hper⟩ := inputA_eventually_periodic
    (st := fun k => idxf (gfamState g chs X 0 (N₀ + k)))
    (σi := fun k => (gdigit g X (N₀ + k)).toNat)
    hcert hσ (fun m => hlt (N₀ + m)) hstep
  refine not_irrational_of_periodic_digits_g g hg X (N₀ + N) p hp ?_ hX
  intro m hm
  rw [digitOf_g_fract g hg, digitOf_g_fract g hg]
  have hk := hper (m - N₀) (by omega)
  rw [show N₀ + (m - N₀ + p) = m + p from by omega,
    show N₀ + (m - N₀) = m from by omega] at hk
  exact hk


/-! ## Word-length-`1` channels: the state is `⌊a·t⌋` -/

/-- A single-track channel with a one-digit word has no window, so its whole
state is the carry `⌊a · fract(X·gᵐ)⌋`. -/
theorem gchanCode_single (g a d : ℕ) (X : ℝ) (m : ℕ) :
    gchanCode g ⟨(a : ℤ), 0, [d]⟩ X 0 m
      = (⌊(a : ℝ) * Int.fract (X * (g : ℝ) ^ m)⌋).toNat := by
  unfold gchanCode
  have hoff : (ZChannel.off ⟨(a : ℤ), 0, [d]⟩) = 0 := by
    simp [ZChannel.off]
  have hell : (ZChannel.ell ⟨(a : ℤ), 0, [d]⟩) = 1 := rfl
  have hwin : (ZChannel.gwinSize g ⟨(a : ℤ), 0, [d]⟩) = 1 := by
    simp [ZChannel.gwinSize, hell]
  rw [hoff, hwin, hell]
  simp only [Nat.cast_zero, add_zero, mul_one, Nat.sub_self, winCodeG,
    Finset.range_zero, Finset.sum_empty]
  rw [carryTG_single]
  norm_num

/-- The `⌊a·t⌋` of a channel, read off the single index `k = ⌊N·t⌋` for any
`N = a·q`. -/
theorem carry_of_index (a q : ℕ) (hq : 0 < q) (t : ℝ) (ht : 0 ≤ t) :
    (⌊(a : ℝ) * t⌋).toNat = (a * (⌊((a * q : ℕ) : ℝ) * t⌋).toNat) / (a * q) := by
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · simp
  have hfl : (0 : ℤ) ≤ ⌊((a * q : ℕ) : ℝ) * t⌋ := by
    apply Int.floor_nonneg.2
    positivity
  rw [floor_mul_of_dvd (a := a) hq t]
  obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le hfl
  rw [hn]
  rw [show ((n : ℤ)) / (q : ℤ) = ((n / q : ℕ) : ℤ) from by exact_mod_cast rfl]
  rw [Int.toNat_natCast, Int.toNat_natCast, Nat.mul_div_mul_left _ _ ha]


/-! ## The reachable state as a function of one index -/

/-- The channel list of a single-track, one-digit-word family. -/
def chansOf (ms : List ℕ) (d : ℕ) : List ZChannel :=
  ms.map (fun a : ℕ => ZChannel.mk (Int.ofNat a) 0 [d])

/-- The joint state as a function of the tail parameter `t` (mixed radix,
channel `0` least significant). -/
noncomputable def stateOfT : List ℕ → ℝ → ℕ
  | [], _ => 0
  | a :: rest, t => (⌊(a : ℝ) * t⌋).toNat + a * stateOfT rest t

/-- The same state read off the single integer index `k = ⌊N·t⌋`. -/
def stateOfK : List ℕ → ℕ → ℕ → ℕ
  | [], _, _ => 0
  | a :: rest, N, k => (a * k) / N + a * stateOfK rest N k

/-- **The family state is a function of the one real `fract(X·gᵐ)`.**  All
channels read the same `X`, so the joint carry vector is a one-parameter curve,
not a product. -/
theorem gfamState_ell1 (g d : ℕ) (ms : List ℕ) (hms : ∀ a ∈ ms, 1 ≤ a) (X : ℝ) (m : ℕ) :
    gfamState g (chansOf ms d) X 0 m = stateOfT ms (Int.fract (X * (g : ℝ) ^ m)) := by
  induction ms with
  | nil => simp [chansOf, gfamState, stateOfT]
  | cons a rest ih =>
    have ih := ih (fun b hb => hms b (by simp [hb]))
    have ha : 1 ≤ a := hms a (by simp)
    simp only [chansOf, List.map_cons, gfamState, stateOfT]
    rw [show (Int.ofNat a) = ((a : ℕ) : ℤ) from rfl, gchanCode_single, ← ih]
    simp only [chansOf]
    congr 1
    simp [ZChannel.gsize, ZChannel.gwinSize, ZChannel.carrySize, ZChannel.posSum,
      ZChannel.off, ZChannel.ell, ha]

/-- **…and that curve is finitely indexed.**  If every multiplier divides `N`
then the state is determined by `k = ⌊N·t⌋`. -/
theorem stateOfT_eq_stateOfK (ms : List ℕ) (N : ℕ) (hN : 0 < N)
    (hdvd : ∀ a ∈ ms, a ∣ N) (t : ℝ) (ht : 0 ≤ t) :
    stateOfT ms t = stateOfK ms N (⌊(N : ℝ) * t⌋).toNat := by
  induction ms with
  | nil => simp [stateOfT, stateOfK]
  | cons a rest ih =>
    obtain ⟨q, hq⟩ := hdvd a (by simp)
    have hq0 : 0 < q := by
      rcases Nat.eq_zero_or_pos q with rfl | h
      · omega
      · exact h
    simp only [stateOfT, stateOfK]
    rw [ih (fun b hb => hdvd b (by simp [hb]))]
    congr 1
    rw [carry_of_index a q hq0 t ht, ← hq]


/-! ## Word length `ℓ ≥ 2`: the window digits are also functions of `t`

The window of channel `a` at base point `m` holds the digits
`gdigit g (a·X) (m+j)`, `j < ℓ−1`.  Writing `u = X·gᵐ`, `F = ⌊u⌋`, `t = fract u`:

  `gdigit g (a·X) (m+j) = ⌊a·g^(j+1)·u⌋ − g·⌊a·g^j·u⌋
                        = (a g^{j+1} F + ⌊a g^{j+1} t⌋) − g (a g^j F + ⌊a g^j t⌋)`

and the two `F` terms **cancel**, because `a·g^{j+1} = g·(a·g^j)`.  So the whole
state — carry and window — is a function of `t` alone, exactly as for `ℓ = 1`,
provided `N` is divisible by `a·g^j` for every `j ≤ ℓ−1` (one power of `g` more
than the window depth). -/

/-- `⌊a·u⌋ = a·⌊u⌋ + ⌊a·fract u⌋`. -/
theorem floor_mul_split (a : ℕ) (u : ℝ) :
    ⌊(a : ℝ) * u⌋ = a * ⌊u⌋ + ⌊(a : ℝ) * Int.fract u⌋ := by
  have h : (a : ℝ) * Int.fract u = (a : ℝ) * u - ((a * ⌊u⌋ : ℤ) : ℝ) := by
    rw [Int.fract]; push_cast; ring
  rw [h, Int.floor_sub_intCast]
  ring

/-- The window digits of `a·X` depend only on the tail `t = fract(X·gᵐ)`. -/
theorem gdigit_window (g a : ℕ) (X : ℝ) (m j : ℕ) :
    gdigit g ((a : ℝ) * X) (m + j)
      = ⌊((a * g ^ (j + 1) : ℕ) : ℝ) * Int.fract (X * (g : ℝ) ^ m)⌋
        - g * ⌊((a * g ^ j : ℕ) : ℝ) * Int.fract (X * (g : ℝ) ^ m)⌋ := by
  unfold gdigit
  have e1 : (a : ℝ) * X * (g : ℝ) ^ (m + j + 1)
      = ((a * g ^ (j + 1) : ℕ) : ℝ) * (X * (g : ℝ) ^ m) := by
    push_cast; ring
  have e2 : (a : ℝ) * X * (g : ℝ) ^ (m + j)
      = ((a * g ^ j : ℕ) : ℝ) * (X * (g : ℝ) ^ m) := by
    push_cast; ring
  rw [e1, e2, floor_mul_split (a * g ^ (j + 1)) (X * (g : ℝ) ^ m),
    floor_mul_split (a * g ^ j) (X * (g : ℝ) ^ m)]
  have hc : ((a * g ^ (j + 1) : ℕ) : ℤ) = (g : ℤ) * ((a * g ^ j : ℕ) : ℤ) := by
    push_cast; ring
  rw [hc]
  ring

/-! ## The indexed state for word length `ℓ` -/

/-- The `j`-th window digit, read off the index `k = ⌊N·t⌋`. -/
def digitK (g N a j k : ℕ) : ℕ := (a * g ^ (j + 1) * k) / N - g * ((a * g ^ j * k) / N)

/-- One channel's code (carry in the high part, window below). -/
def chanCodeK (g N a ell k : ℕ) : ℕ :=
  ((a * k) / N) * g ^ (ell - 1)
    + ∑ j ∈ Finset.range (ell - 1), digitK g N a j k * g ^ j

/-- The joint state, read off the single index `k = ⌊N·t⌋`. -/
def stateOfKW (g N ell : ℕ) : List ℕ → ℕ → ℕ
  | [], _ => 0
  | a :: rest, k => chanCodeK g N a ell k + (a * g ^ (ell - 1)) * stateOfKW g N ell rest k

/-- The channel list of a single-track family avoiding the word `w`. -/
def chansOfW (ms : List ℕ) (w : List ℕ) : List ZChannel :=
  ms.map (fun a : ℕ => ZChannel.mk (Int.ofNat a) 0 w)


/-- `⌊b·t⌋` read off the index `k = ⌊N·t⌋`, for any `b ∣ N`. -/
theorem floor_index (b N k : ℕ) (hN : 0 < N) (hb : b ∣ N) (t : ℝ) (ht : 0 ≤ t)
    (hk : k = (⌊(N : ℝ) * t⌋).toNat) : (⌊(b : ℝ) * t⌋).toNat = (b * k) / N := by
  obtain ⟨q, hq⟩ := hb
  have hq0 : 0 < q := by
    rcases Nat.eq_zero_or_pos q with rfl | h
    · omega
    · exact h
  subst hq
  subst hk
  exact carry_of_index b q hq0 t ht

/-- The window digit, read off the index. -/
theorem gdigit_window_index (g a N k j : ℕ) (hg : 1 ≤ g) (hN : 0 < N)
    (h1 : a * g ^ (j + 1) ∣ N) (h2 : a * g ^ j ∣ N) (X : ℝ) (m : ℕ)
    (hk : k = (⌊(N : ℝ) * Int.fract (X * (g : ℝ) ^ m)⌋).toNat) :
    (gdigit g ((a : ℝ) * X) (m + j)).toNat = digitK g N a j k := by
  have ht : 0 ≤ Int.fract (X * (g : ℝ) ^ m) := Int.fract_nonneg _
  have hA := floor_index (a * g ^ (j + 1)) N k hN h1 _ ht hk
  have hB := floor_index (a * g ^ j) N k hN h2 _ ht hk
  have hd := gdigit_window g a X m j
  have hnn : 0 ≤ gdigit g ((a : ℝ) * X) (m + j) := gdigit_nonneg g hg _ _
  have hA0 : 0 ≤ ⌊((a * g ^ (j + 1) : ℕ) : ℝ) * Int.fract (X * (g : ℝ) ^ m)⌋ :=
    Int.floor_nonneg.2 (by positivity)
  have hB0 : 0 ≤ ⌊((a * g ^ j : ℕ) : ℝ) * Int.fract (X * (g : ℝ) ^ m)⌋ :=
    Int.floor_nonneg.2 (by positivity)
  have key : ∀ (x y : ℕ) (z : ℤ), z = (x : ℤ) - (g : ℤ) * (y : ℤ) → 0 ≤ z →
      z.toNat = x - g * y := by
    intro x y z h1 h2
    omega
  unfold digitK
  rw [← hA, ← hB]
  refine key _ _ _ ?_ hnn
  rw [hd, Int.toNat_of_nonneg hA0, Int.toNat_of_nonneg hB0]


/-- One channel's code, read off the index `k = ⌊N·t⌋`. -/
theorem gchanCode_window (g a N k ell : ℕ) (hg : 1 ≤ g) (w : List ℕ) (hw : w.length = ell)
    (hN : 0 < N) (hdvd : ∀ j, j ≤ ell - 1 → a * g ^ j ∣ N)
    (X : ℝ) (m : ℕ) (hk : k = (⌊(N : ℝ) * Int.fract (X * (g : ℝ) ^ m)⌋).toNat) :
    gchanCode g ⟨(a : ℤ), 0, w⟩ X 0 m = chanCodeK g N a ell k := by
  have ht : 0 ≤ Int.fract (X * (g : ℝ) ^ m) := Int.fract_nonneg _
  have hell : (ZChannel.ell ⟨(a : ℤ), 0, w⟩) = ell := hw
  have hoff : (ZChannel.off ⟨(a : ℤ), 0, w⟩) = 0 := by simp [ZChannel.off]
  have hwin : (ZChannel.gwinSize g ⟨(a : ℤ), 0, w⟩) = g ^ (ell - 1) := by
    simp [ZChannel.gwinSize, hell]
  have hz : ((a : ℤ) : ℝ) * X + ((0 : ℤ) : ℝ) * (0 : ℝ) = (a : ℝ) * X := by
    push_cast; ring
  unfold gchanCode chanCodeK
  rw [hoff, hwin, hell]
  simp only [hz, Nat.cast_zero, add_zero]
  congr 1
  · congr 1
    rw [carryTG_single]
    have h0 := hdvd 0 (by omega)
    simp only [pow_zero, mul_one] at h0
    exact floor_index a N k hN h0 _ ht hk
  · unfold winCodeG
    refine Finset.sum_congr rfl ?_
    intro j hj
    rw [Finset.mem_range] at hj
    congr 1
    exact gdigit_window_index g a N k j hg hN (hdvd (j + 1) (by omega))
      (hdvd j (by omega)) X m hk

/-- **The family state for any word length**, read off the single index
`k = ⌊N·fract(X·gᵐ)⌋`. -/
theorem gfamState_window (g : ℕ) (hg : 1 ≤ g) (ms : List ℕ) (hms : ∀ a ∈ ms, 1 ≤ a)
    (w : List ℕ) (ell : ℕ) (hw : w.length = ell) (N : ℕ) (hN : 0 < N)
    (hdvd : ∀ a ∈ ms, ∀ j, j ≤ ell - 1 → a * g ^ j ∣ N)
    (X : ℝ) (m : ℕ) :
    gfamState g (chansOfW ms w) X 0 m
      = stateOfKW g N ell ms (⌊(N : ℝ) * Int.fract (X * (g : ℝ) ^ m)⌋).toNat := by
  induction ms with
  | nil => simp [chansOfW, gfamState, stateOfKW]
  | cons a rest ih =>
    have ih := ih (fun b hb => hms b (by simp [hb])) (fun b hb => hdvd b (by simp [hb]))
    have ha : 1 ≤ a := hms a (by simp)
    simp only [chansOfW, List.map_cons, gfamState, stateOfKW]
    rw [show (Int.ofNat a) = ((a : ℕ) : ℤ) from rfl,
      gchanCode_window g a N _ ell hg w hw hN (hdvd a (by simp)) X m rfl, ← ih]
    simp only [chansOfW]
    congr 1
    simp [ZChannel.gsize, ZChannel.gwinSize, ZChannel.carrySize, ZChannel.posSum,
      ZChannel.off, ZChannel.ell, hw, ha]

end NormalNumbers.Adder
