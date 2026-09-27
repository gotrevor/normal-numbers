import NormalNumbers.JointLambertStatement

/-!
# The finite even encoding, proved

Target: `NormalNumbers.JointLambert.EvenEncoding`, frozen in
`JointLambertStatement.lean`.  Paper: `papers/2026-09-26-joint-lambert-disjunctivity.md` §2.

The paper route is a torus Fourier argument: the uniform measure on
`({2a/b^s})_{b ∈ S}`, `0 ≤ a < lcm(S)^s`, annihilates every fixed nontrivial
character once `s` is large, hence converges weakly to Haar measure on the full
torus.  The proof below is the elementary equivalent the kickoff explicitly
permits, and it is constructive: it produces `s` and `a` outright.

**The construction.**  Write `frac b s a = {2a / b^s}`.  Process the bases with the
*smallest* base last.  Two facts drive everything.

* *Free choice at one base.*  For any `A` and any window `(u,v) ⊆ [0,1]` of length
  exceeding `2 / b^s` there is an offset `α < b^s` with
  `frac b s (A + α) ∈ (u,v)` (`exists_offset_mem_window`).  The reachable set
  `{(2n mod b^s)/b^s}` is `2/b^s`-dense in `[0,1)`, and no congruence machinery is
  needed: `α = (A*(b^s-1) + n) % b^s` works because `A + α ≡ n [MOD b^s]`.
* *Cheap interference.*  That same offset moves a **larger** base `b > b₀` by only
  `2α / b^s < 2 (b₀/b)^s ≤ 2 θ^s` with `θ = b₀/(b₀+1) < 1`.  So the correction at
  the smallest base barely disturbs the bases already set.

Hence the induction on `S.card`: strip `S.min'`, solve the rest against windows
shrunk by `ε/2`, then spend exactly that slack on the single correction step at
the smallest base.

No base coprimality and no multiplicative independence is used — only that the
bases are *distinct*, which is what gives `b₀/b < 1`.  Bases `2` and `4` are
therefore covered, and so is the fully dependent triple `{2,3,6}`, where the
base-`6` coordinate is a CRT function of the base-`2` and base-`3` coordinates.
-/

open Filter
open scoped Topology BigOperators

namespace NormalNumbers.JointLambert

/-- The encoder coordinate: the fractional part read by base `b` at depth `s`. -/
noncomputable def frac (b s a : ℕ) : ℝ := Int.fract ((2 * (a : ℝ)) / (b : ℝ) ^ s)

lemma frac_nonneg (b s a : ℕ) : 0 ≤ frac b s a := Int.fract_nonneg _

lemma frac_lt_one (b s a : ℕ) : frac b s a < 1 := Int.fract_lt_one _

/-- Periodicity: shifting `a` by a multiple of `b ^ s` leaves the coordinate alone. -/
lemma frac_add_mul (b s a k : ℕ) (hb : 0 < b) :
    frac b s (a + k * b ^ s) = frac b s a := by
  have hbR : (0 : ℝ) < (b : ℝ) := by exact_mod_cast hb
  have hbs : ((b : ℝ)) ^ s ≠ 0 := by positivity
  unfold frac
  have h : (2 * ((a + k * b ^ s : ℕ) : ℝ)) / (b : ℝ) ^ s
      = (2 * (a : ℝ)) / (b : ℝ) ^ s + ((2 * k : ℕ) : ℝ) := by
    push_cast
    field_simp
    try ring
  rw [h, Int.fract_add_natCast]

/-- Adding an offset shifts the coordinate additively, provided it does not wrap. -/
lemma frac_add (b s A α : ℕ)
    (h : frac b s A + 2 * (α : ℝ) / (b : ℝ) ^ s < 1) :
    frac b s (A + α) = frac b s A + 2 * (α : ℝ) / (b : ℝ) ^ s := by
  have key : (2 * ((A + α : ℕ) : ℝ)) / (b : ℝ) ^ s
      = (Int.fract ((2 * (A : ℝ)) / (b : ℝ) ^ s) + 2 * (α : ℝ) / (b : ℝ) ^ s)
        + ((⌊(2 * (A : ℝ)) / (b : ℝ) ^ s⌋ : ℤ) : ℝ) := by
    rw [Int.fract]
    rcases eq_or_ne ((b : ℝ) ^ s) 0 with h0 | h0
    · simp [h0]
    · push_cast
      field_simp
      ring
  unfold frac at h ⊢
  rw [key, Int.fract_add_intCast, Int.fract_eq_self.2 ⟨by positivity, h⟩]

/-- **Free choice at one base.**  Every window inside `[0,1]` longer than `2 / b ^ s`
is hit by some offset strictly below `b ^ s`.  The reachable coordinates form the
`2/b^s`-spaced grid `{2n / b^s}`, so the explicit witness is a residue. -/
lemma exists_offset_mem_window (b s A : ℕ) (hb : 2 ≤ b) (u v : ℝ)
    (hu : 0 ≤ u) (hv : v ≤ 1) (hgap : u + 2 / (b : ℝ) ^ s < v) :
    ∃ α : ℕ, α < b ^ s ∧ u < frac b s (A + α) ∧ frac b s (A + α) < v := by
  set M : ℕ := b ^ s with hMdef
  have hMpos : 0 < M := Nat.pow_pos (by omega)
  have hMR : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hMpos
  have hcast : ((M : ℕ) : ℝ) = (b : ℝ) ^ s := by rw [hMdef]; push_cast; ring
  -- the grid point `2 n / M`
  set n : ℕ := ⌊u * (M : ℝ) / 2⌋₊ + 1 with hndef
  have hnfl : u * (M : ℝ) / 2 < (n : ℝ) := by
    have h1 := Nat.lt_floor_add_one (u * (M : ℝ) / 2)
    rw [hndef]; push_cast; linarith
  have hnfl' : (n : ℝ) ≤ u * (M : ℝ) / 2 + 1 := by
    have h1 : ((⌊u * (M : ℝ) / 2⌋₊ : ℕ) : ℝ) ≤ u * (M : ℝ) / 2 :=
      Nat.floor_le (by positivity)
    rw [hndef]; push_cast; linarith
  have hnlow : u < 2 * (n : ℝ) / (M : ℝ) := by
    rw [lt_div_iff₀ hMR]
    nlinarith
  have hnhigh : 2 * (n : ℝ) / (M : ℝ) ≤ u + 2 / (M : ℝ) := by
    rw [div_le_iff₀ hMR]
    have hexp : (u + 2 / (M : ℝ)) * (M : ℝ) = u * (M : ℝ) + 2 := by field_simp
    rw [hexp]
    nlinarith
  have hnv : 2 * (n : ℝ) / (M : ℝ) < v := by
    rw [← hcast] at hgap
    linarith
  have hnlt : 2 * n < M := by
    have h1 : 2 * (n : ℝ) / (M : ℝ) < 1 := lt_of_lt_of_le hnv hv
    rw [div_lt_one hMR] at h1
    exact_mod_cast h1
  -- the explicit offset: a residue congruent to `n - A`
  set α : ℕ := (n + M - A % M) % M with hαdef
  have hαlt : α < M := Nat.mod_lt _ hMpos
  have hAM : A % M < M := Nat.mod_lt _ hMpos
  have hmodeq : (A + α) % M = n := by
    have e1 : A + α ≡ A % M + (n + M - A % M) [MOD M] :=
      Nat.ModEq.add (Nat.mod_modEq A M).symm (Nat.mod_modEq _ M)
    have e2 : A % M + (n + M - A % M) = M + n := by omega
    have e3 : M + n ≡ n [MOD M] := Nat.add_modEq_left
    have : A + α ≡ n [MOD M] := (e2 ▸ e1).trans e3
    calc (A + α) % M = n % M := this
      _ = n := Nat.mod_eq_of_lt (by omega)
  obtain ⟨q, hq⟩ : ∃ q, A + α = M * q + n := ⟨(A + α) / M, by
    conv_lhs => rw [← Nat.div_add_mod (A + α) M]
    rw [hmodeq]⟩
  have hval : frac b s (A + α) = 2 * (n : ℝ) / (M : ℝ) := by
    unfold frac
    rw [← hcast]
    have hsplit : (2 * ((A + α : ℕ) : ℝ)) / (M : ℝ)
        = 2 * (n : ℝ) / (M : ℝ) + ((2 * q : ℕ) : ℝ) := by
      rw [hq]
      push_cast
      field_simp
      ring
    rw [hsplit, Int.fract_add_natCast, Int.fract_eq_self.2]
    refine ⟨by positivity, ?_⟩
    rw [div_lt_one hMR]
    exact_mod_cast hnlt
  exact ⟨α, hαlt, by rw [hval]; exact hnlow, by rw [hval]; exact hnv⟩

/-- **The encoding core.**  Induction on the number of bases, stripping the smallest
base and correcting it last.  The `ε`-gap hypothesis is uniform so that the
recursive call can be handed windows shrunk by `ε/2`. -/
theorem encoding_core :
    ∀ (N : ℕ) (S : Finset ℕ), S.card = N → (∀ b ∈ S, 2 ≤ b) →
      ∀ ε : ℝ, 0 < ε → ∃ s₀ : ℕ, ∀ s, s₀ ≤ s → ∀ lo hi : ℕ → ℝ,
        (∀ b ∈ S, 0 ≤ lo b ∧ lo b + ε ≤ hi b ∧ hi b ≤ 1) →
        ∃ a : ℕ, ∀ b ∈ S, lo b < frac b s a ∧ frac b s a < hi b := by
  intro N
  induction N with
  | zero =>
      intro S hcard _ ε _
      refine ⟨0, fun s _ lo hi _ => ⟨0, ?_⟩⟩
      intro b hbS
      rw [Finset.card_eq_zero.1 hcard] at hbS
      simp at hbS
  | succ N ih =>
      intro S hcard hb2 ε hε
      have hne : S.Nonempty := Finset.card_pos.1 (by omega)
      set b₀ := S.min' hne with hb₀def
      have hb₀S : b₀ ∈ S := S.min'_mem hne
      have hb₀2 : 2 ≤ b₀ := hb2 _ hb₀S
      have hb₀R : (1 : ℝ) < (b₀ : ℝ) := by exact_mod_cast (by omega : 1 < b₀)
      have hb₀R2 : (2 : ℝ) ≤ (b₀ : ℝ) := by exact_mod_cast hb₀2
      set S' := S.erase b₀ with hS'def
      have hcard' : S'.card = N := by
        rw [hS'def, Finset.card_erase_of_mem hb₀S, hcard]
        omega
      obtain ⟨s₀, hs₀⟩ := ih S' hcard'
        (fun b hb => hb2 b (Finset.mem_of_mem_erase hb)) (ε / 2) (by linarith)
      set θ : ℝ := (b₀ : ℝ) / ((b₀ : ℝ) + 1) with hθdef
      have hθ0 : 0 ≤ θ := by rw [hθdef]; positivity
      have hθ1 : θ < 1 := by
        rw [hθdef, div_lt_one (by linarith)]
        linarith
      have htend : Tendsto (fun s : ℕ => 2 * θ ^ s) atTop (𝓝 0) := by
        simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hθ0 hθ1).const_mul (2 : ℝ)
      obtain ⟨s₁, hs₁⟩ := Filter.eventually_atTop.1
        (htend.eventually_lt_const (show (0 : ℝ) < ε / 2 by linarith))
      refine ⟨max s₀ s₁, ?_⟩
      intro s hs lo hi hwin
      have hsmall : 2 * θ ^ s < ε / 2 := hs₁ s (le_trans (le_max_right _ _) hs)
      obtain ⟨a', ha'⟩ := hs₀ s (le_trans (le_max_left _ _) hs) lo (fun b => hi b - ε / 2)
        (by
          intro b hb
          obtain ⟨h1, h2, h3⟩ := hwin b (Finset.mem_of_mem_erase hb)
          exact ⟨h1, by linarith, by linarith⟩)
      obtain ⟨h1, h2, h3⟩ := hwin b₀ hb₀S
      -- the smallest base has fine enough grid
      have hinvb : (1 : ℝ) / (b₀ : ℝ) ≤ θ := by
        rw [hθdef, div_le_div_iff₀ (by linarith) (by linarith)]
        nlinarith
      have hgrid : 2 / (b₀ : ℝ) ^ s ≤ 2 * θ ^ s := by
        have h0 : ((b₀ : ℝ)⁻¹) ^ s ≤ θ ^ s :=
          pow_le_pow_left₀ (by positivity) (by rwa [one_div] at hinvb) s
        rw [inv_pow] at h0
        rw [div_eq_mul_inv]
        linarith
      obtain ⟨α, hαlt, hα1, hα2⟩ :=
        exists_offset_mem_window b₀ s a' hb₀2 (lo b₀) (hi b₀) h1 h3 (by linarith)
      refine ⟨a' + α, ?_⟩
      intro b hbS
      by_cases hbe : b = b₀
      · subst hbe; exact ⟨hα1, hα2⟩
      · have hbS' : b ∈ S' := Finset.mem_erase.2 ⟨hbe, hbS⟩
        obtain ⟨g1, g2⟩ := ha' b hbS'
        obtain ⟨w1, w2, w3⟩ := hwin b hbS
        have hbgt : b₀ < b := lt_of_le_of_ne (S.min'_le b hbS) (Ne.symm hbe)
        have hbR : (0 : ℝ) < (b : ℝ) := by
          exact_mod_cast (by omega : 0 < b)
        have hratio0 : (b₀ : ℝ) / (b : ℝ) ≤ θ := by
          rw [hθdef, div_le_div_iff₀ hbR (by linarith)]
          have : (b₀ : ℝ) + 1 ≤ (b : ℝ) := by exact_mod_cast (by omega : b₀ + 1 ≤ b)
          nlinarith
        have hratio : 2 * (α : ℝ) / (b : ℝ) ^ s < 2 * θ ^ s := by
          have hαR : (α : ℝ) < (b₀ : ℝ) ^ s := by
            have : (α : ℝ) < ((b₀ ^ s : ℕ) : ℝ) := by exact_mod_cast hαlt
            simpa using this
          have hpos : (0 : ℝ) < (b : ℝ) ^ s := by positivity
          have hstep : 2 * (α : ℝ) / (b : ℝ) ^ s < 2 * ((b₀ : ℝ) / (b : ℝ)) ^ s := by
            have heq : 2 * ((b₀ : ℝ) / (b : ℝ)) ^ s = 2 * (b₀ : ℝ) ^ s / (b : ℝ) ^ s := by
              rw [div_pow]; ring
            rw [heq, div_lt_div_iff₀ hpos hpos]
            nlinarith
          have hmono : ((b₀ : ℝ) / (b : ℝ)) ^ s ≤ θ ^ s :=
            pow_le_pow_left₀ (by positivity) hratio0 s
          linarith
        have hno : frac b s a' + 2 * (α : ℝ) / (b : ℝ) ^ s < 1 := by linarith
        have hpert0 : (0 : ℝ) ≤ 2 * (α : ℝ) / (b : ℝ) ^ s := by positivity
        rw [frac_add b s a' α hno]
        exact ⟨by linarith, by linarith⟩

/-- The frozen finite encoding statement, proved. -/
theorem evenEncoding : EvenEncoding := by
  intro S hb2 lo hi hwin
  rcases S.eq_empty_or_nonempty with rfl | hne
  · exact ⟨2, 2, le_refl _, le_refl _, by simp⟩
  -- uniform gap
  set ε : ℝ := (S.inf' hne (fun b => hi b - lo b)) with hεdef
  have hε : 0 < ε := by
    rw [hεdef, Finset.lt_inf'_iff]
    intro b hb
    exact sub_pos.2 (hwin b hb).2.1
  have hεle : ∀ b ∈ S, ε ≤ hi b - lo b := fun b hb => Finset.inf'_le _ hb
  obtain ⟨s₀, hs₀⟩ := encoding_core S.card S rfl hb2 ε hε
  set s : ℕ := max s₀ 2 with hsdef
  obtain ⟨a', ha'⟩ := hs₀ s (le_max_left _ _) lo hi (by
    intro b hb
    obtain ⟨h1, h2, h3⟩ := hwin b hb
    have := hεle b hb
    exact ⟨h1, by linarith, h3⟩)
  -- pad `a` upward by a common period so that `2 ≤ a`
  set P : ℕ := ∏ b ∈ S, b ^ s with hPdef
  have hPpos : 0 < P := by
    rw [hPdef]
    exact Finset.prod_pos (fun b hb => Nat.pow_pos (by have := hb2 b hb; omega))
  refine ⟨s, a' + 2 * P, le_max_right _ _, by omega, ?_⟩
  intro b hbS
  have hbpos : 0 < b := by have := hb2 b hbS; omega
  obtain ⟨k, hk⟩ : ∃ k, P = b ^ s * k := Finset.dvd_prod_of_mem (fun b => b ^ s) hbS
  have hshift : frac b s (a' + 2 * P) = frac b s a' := by
    have : a' + 2 * P = a' + (2 * k) * b ^ s := by rw [hk]; ring
    rw [this, frac_add_mul b s a' (2 * k) hbpos]
  have := ha' b hbS
  unfold frac at hshift this
  rw [hshift]
  exact this

/-- Dependent-base control, required by the kickoff: bases `2` and `4` are covered,
with no coprimality or multiplicative-independence hypothesis anywhere. -/
theorem evenEncoding_two_four :
    ∀ lo hi : ℕ → ℝ,
      (∀ b ∈ ({2, 4} : Finset ℕ), 0 ≤ lo b ∧ lo b < hi b ∧ hi b ≤ 1) →
      ∃ s a : ℕ, 2 ≤ s ∧ 2 ≤ a ∧
        ∀ b ∈ ({2, 4} : Finset ℕ), lo b < Int.fract ((2 * (a : ℝ)) / (b : ℝ) ^ s) ∧
          Int.fract ((2 * (a : ℝ)) / (b : ℝ) ^ s) < hi b :=
  evenEncoding {2, 4} (by decide)

/-- The fully dependent triple: the base-`6` coordinate is a CRT function of the
base-`2` and base-`3` coordinates, and the encoding still hits every box. -/
theorem evenEncoding_two_three_six :
    ∀ lo hi : ℕ → ℝ,
      (∀ b ∈ ({2, 3, 6} : Finset ℕ), 0 ≤ lo b ∧ lo b < hi b ∧ hi b ≤ 1) →
      ∃ s a : ℕ, 2 ≤ s ∧ 2 ≤ a ∧
        ∀ b ∈ ({2, 3, 6} : Finset ℕ), lo b < Int.fract ((2 * (a : ℝ)) / (b : ℝ) ^ s) ∧
          Int.fract ((2 * (a : ℝ)) / (b : ℝ) ^ s) < hi b :=
  evenEncoding {2, 3, 6} (by decide)

end NormalNumbers.JointLambert
