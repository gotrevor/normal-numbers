import NormalNumbers.JointLambertStatement
import NormalNumbers.JointLambertEncodingProof
import NormalNumbers.JointLambertTail

/-!
# Simultaneous Erdős–Borwein disjunctivity: the digit bridge and final assembly

This is §6 of `papers/2026-09-26-joint-lambert-disjunctivity.md`: the passage from the
arithmetic/tail package to the actual digit statement, and the assembly of the frozen
headline `JointLambertDisjunctivity`.

Ingredients, all already proved elsewhere in this repo:

* `evenEncoding` (`JointLambertEncodingProof`) — one even integer `2a` lands in a
  prescribed open box of every coordinate simultaneously;
* `exists_joint_small_tail_all_bases` (`JointLambertTail`) — one offset `n` with the
  prescribed divisor-count pattern and, at that offset, a base-`b` tail below `ε/2`
  for **every** base `b ≥ 2` at once;
* `CastingOut.erdosBorweinAtBase_eq_lambertVal` — `E_b = Σ τ(m)/bᵐ`.

The only hypotheses are the two source-faithful analytic inputs `AGP` and
`PrimeIntervalSupply`; no digit bridge is assumed, no base coprimality or
multiplicative independence is required, and the empty base set is covered.

**Boundary.**  The result is *qualitative* simultaneous disjunctivity, conditional on
`AGP` and `PrimeIntervalSupply`.  It is not normality, and not the quantitative
occurrence count of the paper.
-/

namespace NormalNumbers.JointLambert

open Finset

/-- The shifted Lambert tail read from position `N+1` is summable. -/
theorem summable_shift_tail (b : ℕ) (hb : 2 ≤ b) (w : ℕ → ℕ) (hw : ∀ m, w m ≤ m) (N : ℕ) :
    Summable (fun j : ℕ => (w (N + 1 + j) : ℝ) / (b : ℝ) ^ (j + 1)) := by
  have hb0 : (0 : ℝ) < b := by
    have : (2 : ℝ) ≤ b := by exact_mod_cast hb
    linarith
  have hs := (CastingOut.summable_lambert b hb w hw).mul_right ((b : ℝ) ^ N)
  refine ((summable_nat_add_iff (N + 1)).2 hs).congr fun j => ?_
  rw [show j + (N + 1) = N + 1 + j from by omega]
  have hex : (b : ℝ) ^ (N + 1 + j) = (b : ℝ) ^ (j + 1) * (b : ℝ) ^ N := by
    rw [← pow_add, show j + 1 + N = N + 1 + j from by omega]
  rw [hex]
  have h1 : ((b : ℝ) ^ N) ≠ 0 := by positivity
  have h2 : ((b : ℝ) ^ (j + 1)) ≠ 0 := by positivity
  field_simp

/-- Splitting a Lambert value shifted by `b^N` into its integer head and the series
read from position `N+1`. -/
theorem lambertVal_mul_pow_eq (b : ℕ) (hb : 2 ≤ b) (w : ℕ → ℕ) (hw : ∀ m, w m ≤ m) (N : ℕ) :
    CastingOut.lambertVal b w * (b : ℝ) ^ N
      = ((∑ m ∈ range (N + 1), w m * b ^ (N - m) : ℕ) : ℝ)
        + ∑' j : ℕ, (w (N + 1 + j) : ℝ) / (b : ℝ) ^ (j + 1) := by
  have hb0 : (0 : ℝ) < b := by
    have : (2 : ℝ) ≤ b := by exact_mod_cast hb
    linarith
  have hs := CastingOut.summable_lambert b hb w hw
  have hsN : Summable (fun m : ℕ => (w m : ℝ) / (b : ℝ) ^ m * (b : ℝ) ^ N) := hs.mul_right _
  have hx : CastingOut.lambertVal b w * (b : ℝ) ^ N
      = ∑' m : ℕ, ((w m : ℝ) / (b : ℝ) ^ m * (b : ℝ) ^ N) := by
    rw [CastingOut.lambertVal, tsum_mul_right]
  rw [hx, ← Summable.sum_add_tsum_nat_add (N + 1) hsN]
  have hhead : ∑ m ∈ range (N + 1), ((w m : ℝ) / (b : ℝ) ^ m * (b : ℝ) ^ N)
      = ((∑ m ∈ range (N + 1), w m * b ^ (N - m) : ℕ) : ℝ) := by
    push_cast
    refine Finset.sum_congr rfl fun m hm => ?_
    have hmN : m ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)
    have hpow : (b : ℝ) ^ m * (b : ℝ) ^ (N - m) = (b : ℝ) ^ N := pow_mul_pow_sub _ hmN
    have hbm : ((b : ℝ) ^ m) ≠ 0 := by positivity
    rw [← hpow]
    field_simp
  rw [hhead]
  congr 1
  refine tsum_congr fun j => ?_
  rw [show j + (N + 1) = N + 1 + j from by omega]
  have hex : (b : ℝ) ^ (N + 1 + j) = (b : ℝ) ^ (j + 1) * (b : ℝ) ^ N := by
    rw [← pow_add, show j + 1 + N = N + 1 + j from by omega]
  rw [hex]
  have h1 : ((b : ℝ) ^ N) ≠ 0 := by positivity
  have h2 : ((b : ℝ) ^ (j + 1)) ≠ 0 := by positivity
  field_simp

/-- **The common-offset digit identity.**

At the offset `N` (so the word starts at digit `N+1`), the divisibility pattern
`b^(j+1) ∣ τ(N+1+j)` kills every slot `j < k` other than `j = r`, the survivor
contributes exactly `2a/b^(r+1)`, and the remaining tail is the small quantity the
tail theorem controls.  Under the interior-cylinder bounds on `{2a/b^(r+1)}` and a
tail below the margin `(1/2)/b^ℓ`, the length-`ℓ` window of `E_b` at offset `N`
reads exactly `v`. -/
theorem floor_digit_of_common_offset
    (b ℓ v c a r k N : ℕ) (hb : 2 ≤ b) (hbc : b ∣ c)
    (hv : v < b ^ ℓ) (hrk : r < k)
    (hkill : ∀ j, j < k → j ≠ r → c ^ (j + 1) ∣ NormalNumbers.SwingC2.tau (N + 1 + j))
    (hsurv : NormalNumbers.SwingC2.tau (N + 1 + r) = 2 * a)
    (hlo : (v : ℝ) / (b : ℝ) ^ ℓ < Int.fract (2 * (a : ℝ) / (b : ℝ) ^ (r + 1)))
    (hhi : Int.fract (2 * (a : ℝ) / (b : ℝ) ^ (r + 1)) < ((v : ℝ) + 1 / 2) / (b : ℝ) ^ ℓ)
    (hT0 : 0 ≤ ∑' t : ℕ,
      (NormalNumbers.SwingC2.tau (N + 1 + k + t) : ℝ) / (b : ℝ) ^ (k + t + 1))
    (hT : ∑' t : ℕ, (NormalNumbers.SwingC2.tau (N + 1 + k + t) : ℝ) / (b : ℝ) ^ (k + t + 1)
            < (1 / 2) / (b : ℝ) ^ ℓ) :
    ⌊(b : ℝ) ^ ℓ * orbit b (CastingOut.erdosBorweinAtBase b) N⌋ = (v : ℤ) := by
  have hbpos : 0 < b := by omega
  have hb0 : (0 : ℝ) < b := by
    have : (2 : ℝ) ≤ b := by exact_mod_cast hb
    linarith
  have hbl0 : (0 : ℝ) < (b : ℝ) ^ ℓ := by positivity
  set τ := NormalNumbers.SwingC2.tau with hτdef
  set T : ℝ := ∑' t : ℕ, (τ (N + 1 + k + t) : ℝ) / (b : ℝ) ^ (k + t + 1) with hTdef
  set y : ℝ := Int.fract (2 * (a : ℝ) / (b : ℝ) ^ (r + 1)) with hydef
  -- the full shifted tail, split at `k`
  have hsum := summable_shift_tail b hb τ NormalNumbers.SwingC2.tau_le_self N
  have hkspl := Summable.sum_add_tsum_nat_add k hsum
  have hfar : ∑' t : ℕ, (τ (N + 1 + (t + k)) : ℝ) / (b : ℝ) ^ (t + k + 1) = T := by
    rw [hTdef]
    exact tsum_congr fun t => by
      rw [show N + 1 + (t + k) = N + 1 + k + t from by omega,
        show t + k + 1 = k + t + 1 from by omega]
  -- every killed slot is an integer
  have hG : ∀ j ∈ (range k).erase r, (τ (N + 1 + j) : ℝ) / (b : ℝ) ^ (j + 1)
      = ((τ (N + 1 + j) / b ^ (j + 1) : ℕ) : ℝ) := by
    intro j hj
    obtain ⟨hjr, hjk⟩ := Finset.mem_erase.mp hj
    have hdvd : b ^ (j + 1) ∣ τ (N + 1 + j) :=
      dvd_trans (pow_dvd_pow_of_dvd hbc (j + 1)) (hkill j (mem_range.mp hjk) hjr)
    have hne : ((b ^ (j + 1) : ℕ) : ℝ) ≠ 0 := by
      have : (0 : ℕ) < b ^ (j + 1) := Nat.pow_pos hbpos
      exact Nat.cast_ne_zero.mpr (by omega)
    rw [Nat.cast_div hdvd hne]
    push_cast
    ring
  have hrmem : r ∈ range k := mem_range.2 hrk
  have hnear : ∑ j ∈ range k, (τ (N + 1 + j) : ℝ) / (b : ℝ) ^ (j + 1)
      = ((∑ j ∈ (range k).erase r, (τ (N + 1 + j) / b ^ (j + 1)) : ℕ) : ℝ)
        + 2 * (a : ℝ) / (b : ℝ) ^ (r + 1) := by
    rw [← Finset.add_sum_erase _ _ hrmem, Finset.sum_congr rfl hG, ← Nat.cast_sum, hsurv]
    push_cast
    ring
  -- the master identity
  set Head : ℕ := ∑ m ∈ range (N + 1), τ m * b ^ (N - m) with hHead
  set Kill : ℕ := ∑ j ∈ (range k).erase r, (τ (N + 1 + j) / b ^ (j + 1)) with hKill
  have hmaster : CastingOut.erdosBorweinAtBase b * (b : ℝ) ^ N
      = ((Head + Kill : ℕ) : ℝ) + (2 * (a : ℝ) / (b : ℝ) ^ (r + 1) + T) := by
    rw [CastingOut.erdosBorweinAtBase_eq_lambertVal b hb]
    have hlam : (fun m : ℕ => m.divisors.card) = τ := rfl
    rw [hlam, lambertVal_mul_pow_eq b hb τ NormalNumbers.SwingC2.tau_le_self N,
      ← hkspl, hfar, hnear, hHead]
    push_cast
    ring
  -- read the orbit
  have hylt : y + T < ((v : ℝ) + 1) / (b : ℝ) ^ ℓ := by
    have hne : ((b : ℝ) ^ ℓ) ≠ 0 := ne_of_gt hbl0
    have : ((v : ℝ) + 1 / 2) / (b : ℝ) ^ ℓ + (1 / 2) / (b : ℝ) ^ ℓ
        = ((v : ℝ) + 1) / (b : ℝ) ^ ℓ := by
      field_simp
      ring
    linarith [hhi, hT, this]
  have hvle : (v : ℝ) + 1 ≤ (b : ℝ) ^ ℓ := by
    have : (v : ℝ) + 1 ≤ ((b ^ ℓ : ℕ) : ℝ) := by
      have : (v : ℕ) + 1 ≤ b ^ ℓ := by omega
      exact_mod_cast this
    simpa using this
  have hy0 : 0 ≤ y := Int.fract_nonneg _
  have hylt1 : y + T < 1 := by
    have h1 : ((v : ℝ) + 1) / (b : ℝ) ^ ℓ ≤ 1 := by
      rw [div_le_one hbl0]; exact hvle
    linarith
  have horb : orbit b (CastingOut.erdosBorweinAtBase b) N = y + T := by
    unfold orbit
    rw [hmaster, show ((Head + Kill : ℕ) : ℝ) = (((Head + Kill : ℕ) : ℤ) : ℝ) from by push_cast; ring,
      Int.fract_intCast_add]
    rw [show 2 * (a : ℝ) / (b : ℝ) ^ (r + 1)
        = ((⌊2 * (a : ℝ) / (b : ℝ) ^ (r + 1)⌋ : ℤ) : ℝ) + y from (Int.floor_add_fract _).symm,
      add_assoc, Int.fract_intCast_add]
    exact Int.fract_eq_self.2 ⟨by linarith, hylt1⟩
  rw [horb, Int.floor_eq_iff]
  have hlo' : (v : ℝ) < y * (b : ℝ) ^ ℓ := (div_lt_iff₀ hbl0).mp hlo
  have hTnn : 0 ≤ T * (b : ℝ) ^ ℓ := mul_nonneg hT0 hbl0.le
  have hup : (y + T) * (b : ℝ) ^ ℓ < (v : ℝ) + 1 := (lt_div_iff₀ hbl0).mp hylt
  constructor
  · push_cast
    nlinarith [hlo', hTnn]
  · push_cast
    nlinarith [hup]

/-- **Simultaneous Erdős–Borwein disjunctivity**, conditional on the two
source-faithful analytic inputs.  Every prescribed collection of words in the
constants `E_b`, `b ∈ S`, occurs at one common, arbitrarily late digit position. -/
theorem jointWords_of_inputs (hagp : AGP) (hpis : PrimeIntervalSupply) (S : Finset ℕ)
    (hb2 : ∀ b ∈ S, 2 ≤ b) : JointWords S := by
  intro lengths values hwin N
  rcases S.eq_empty_or_nonempty with rfl | hne
  · exact ⟨N, le_refl _, by simp⟩
  -- a common multiple of the bases
  set c : ℕ := ∏ b ∈ S, b with hcdef
  have hbc : ∀ b ∈ S, b ∣ c := fun b hb => Finset.dvd_prod_of_mem _ hb
  have hc2 : 2 ≤ c := by
    obtain ⟨b₀, hb₀⟩ := hne
    have h1 : b₀ ≤ c :=
      Finset.single_le_prod' (f := fun i => i) (fun i hi => by have := hb2 i hi; omega) hb₀
    have := hb2 b₀ hb₀
    omega
  -- one positive margin over the finite set
  set P : ℕ := ∏ b ∈ S, b ^ lengths b with hPdef
  have hPbig : ∀ b ∈ S, b ^ lengths b ≤ P :=
    fun b hb => Finset.single_le_prod' (f := fun i => i ^ lengths i)
      (fun i hi => Nat.one_le_pow _ _ (by have := hb2 i hi; omega)) hb
  have hPpos : 0 < P := Finset.prod_pos fun b hb => Nat.pow_pos (by have := hb2 b hb; omega)
  have hPR : (0 : ℝ) < (P : ℝ) := by exact_mod_cast hPpos
  set ε : ℝ := 1 / (P : ℝ) with hεdef
  have hε : 0 < ε := by rw [hεdef]; positivity
  -- interior cylinders for the prescribed words
  obtain ⟨s, a, hs2, ha2, hbox⟩ := evenEncoding S hb2
      (fun b => (values b : ℝ) / (b : ℝ) ^ lengths b)
      (fun b => ((values b : ℝ) + 1 / 2) / (b : ℝ) ^ lengths b) (by
        intro b hb
        have hb2' := hb2 b hb
        have hb0 : (0 : ℝ) < b := by
          have : (2 : ℝ) ≤ b := by exact_mod_cast hb2'
          linarith
        have hbl0 : (0 : ℝ) < (b : ℝ) ^ lengths b := by positivity
        obtain ⟨hlen, hval⟩ := hwin b hb
        have hvR : (values b : ℝ) + 1 ≤ (b : ℝ) ^ lengths b := by
          have h1 : (values b : ℕ) + 1 ≤ b ^ lengths b := by omega
          have h2 : ((values b : ℕ) + 1 : ℝ) ≤ ((b ^ lengths b : ℕ) : ℝ) := by
            exact_mod_cast h1
          simpa using h2
        refine ⟨by positivity, ?_, ?_⟩
        · rw [div_lt_div_iff₀ hbl0 hbl0]
          nlinarith [hbl0]
        · rw [div_le_one hbl0]; linarith)
  obtain ⟨r, rfl⟩ : ∃ r, s = r + 1 := ⟨s - 1, by omega⟩
  have hr1 : 1 ≤ r := by omega
  obtain ⟨k, n, -, hkr, hn1, hnN, hkill, hsurv, -, hall⟩ :=
    exists_joint_small_tail_all_bases hagp hpis hc2 ha2 hr1 hε 0 (N + 1)
  obtain ⟨M, rfl⟩ : ∃ M, n = M + 1 := ⟨n - 1, by omega⟩
  refine ⟨M, by omega, fun b hbS => ?_⟩
  have hb2' := hb2 b hbS
  have hb0 : (0 : ℝ) < b := by
    have : (2 : ℝ) ≤ b := by exact_mod_cast hb2'
    linarith
  have hbl0 : (0 : ℝ) < (b : ℝ) ^ lengths b := by positivity
  obtain ⟨hlen, hval⟩ := hwin b hbS
  obtain ⟨hlo, hhi⟩ := hbox b hbS
  obtain ⟨hT0, hTε⟩ := hall b hb2'
  -- the chosen margin dominates `ε/2` in this coordinate
  have hmargin : ε / 2 ≤ (1 / 2) / (b : ℝ) ^ lengths b := by
    have h1 : ((b ^ lengths b : ℕ) : ℝ) ≤ (P : ℝ) := by exact_mod_cast hPbig b hbS
    have h2 : (b : ℝ) ^ lengths b ≤ (P : ℝ) := by simpa using h1
    rw [hεdef, div_div, div_div, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [h2, hbl0]
  exact floor_digit_of_common_offset b (lengths b) (values b) c a r k M hb2' (hbc b hbS)
    hval hkr hkill hsurv hlo hhi hT0 (lt_of_lt_of_le hTε hmargin)

/-- The frozen headline, proved from the two analytic inputs. -/
theorem jointLambertDisjunctivity (hagp : AGP) (hpis : PrimeIntervalSupply) :
    JointLambertDisjunctivity := fun S hb2 => jointWords_of_inputs hagp hpis S hb2

/-- The required dependent-base control: bases `2` and `4`, with no coprimality or
multiplicative-independence hypothesis anywhere. -/
theorem jointWords_two_four (hagp : AGP) (hpis : PrimeIntervalSupply) :
    JointWords ({2, 4} : Finset ℕ) :=
  jointWords_of_inputs hagp hpis {2, 4} (by decide)

end NormalNumbers.JointLambert
