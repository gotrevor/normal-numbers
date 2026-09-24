import NormalNumbers.TwoPointDepthPeel
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.Basic

/-!
# The local (CRT) structure of the `K` shifted forms

`TwoPointDepthPeel.lean` reduced the fixed-pair crux to the **unweighted** `2K(M)`-point
correlation along the linear forms `p n + 1 + k`, `q n + 1 + k`, `k < K`.  Directive step 3 asks
for the sieve/variance read of that object.  Its arithmetic kernel is entirely local, and this
file proves it:

* **a prime `r ≥ K` divides at most ONE of the `K` forms `p n + 1 + k`** — their pairwise
  differences are `< K ≤ r` (`card_filter_shift_dvd_le_one`).  So the `K` summands
  `ω(p n + 1 + k)` never share a large prime: at primes `> K` the digit-sum
  `Σ_k b^{−k−1} ω(p n + 1 + k)` is a sum over *disjoint* prime supports — the independence the
  variance computation needs;
* **the exact local density** `#{n < r : r ∣ p n + c} = 1` for `r ∤ p` (`card_solutions_eq_one`),
  hence `#{n < r : ∃ k < K, r ∣ p n + 1 + k} = K` exactly (`card_hit_eq`).  So a prime `r` in the
  range `(K, z]` is "used" by the `p`-side with density exactly `K/r`, and by the pair with
  density at most `2K/r`.

Consequences recorded here rather than re-derived later: the small-prime part of
`MultiElliottGrowing` has all the decoupling one could ask for, and the total large-prime mass is
`Σ_{K < r ≤ z} 2K/r ≍ 2K log(log z / log K)` — which is exactly why the route's obstruction is the
*large*-prime part, not the shifts.
-/

open Finset Filter Topology

namespace NormalNumbers.CastingOut

/-- **Disjointness of large primes across shifts.**  If `r ≥ K` then a prime `r` divides at most
one of `a, a+1, …, a+K-1`: two hits differ by less than `K ≤ r`. -/
lemma eq_of_dvd_two_shifts {r a k k' K : ℕ} (hK : K ≤ r) (hk : k < K) (hk' : k' < K)
    (h : r ∣ a + k) (h' : r ∣ a + k') : k = k' := by
  rcases le_total k k' with hle | hle
  · have : r ∣ (k' - k) := by
      have := Nat.dvd_sub h' h
      simpa [Nat.add_sub_add_left] using this
    rcases Nat.eq_zero_or_pos (k' - k) with hz | hz
    · omega
    · have := Nat.le_of_dvd hz this
      omega
  · have : r ∣ (k - k') := by
      have := Nat.dvd_sub h h'
      simpa [Nat.add_sub_add_left] using this
    rcases Nat.eq_zero_or_pos (k - k') with hz | hz
    · omega
    · have := Nat.le_of_dvd hz this
      omega

/-- At most one shift is hit. -/
lemma card_filter_shift_dvd_le_one {r a K : ℕ} (hK : K ≤ r) :
    (((range K).filter (fun k => r ∣ a + k)).card) ≤ 1 := by
  classical
  rw [Finset.card_le_one]
  intro k hk k' hk'
  simp only [Finset.mem_filter, Finset.mem_range] at hk hk'
  exact eq_of_dvd_two_shifts hK hk.1 hk'.1 hk.2 hk'.2

/-- **The exact local density of one linear form.**  For a prime `r` not dividing `p`, exactly one
residue `n < r` solves `r ∣ p n + c`. -/
lemma card_solutions_eq_one {r p c : ℕ} (hr : r.Prime) (hp : ¬ (r ∣ p)) :
    (((range r).filter (fun n => r ∣ p * n + c)).card) = 1 := by
  classical
  haveI : Fact r.Prime := ⟨hr⟩
  have hp0 : ((p : ZMod r)) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    exact hp
  set x : ZMod r := -(c : ZMod r) * (p : ZMod r)⁻¹ with hx
  have hrpos : 0 < r := hr.pos
  refine Finset.card_eq_one.mpr ⟨x.val, ?_⟩
  ext n
  simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton]
  constructor
  · rintro ⟨hn, hdvd⟩
    have hcast : ((p * n + c : ℕ) : ZMod r) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr hdvd
    push_cast at hcast
    have hnx : ((n : ℕ) : ZMod r) = x := by
      rw [hx, eq_mul_inv_iff_mul_eq₀ hp0]
      linear_combination hcast
    have := ZMod.val_natCast_of_lt hn
    rw [hnx] at this
    omega
  · rintro rfl
    have hvlt : x.val < r := ZMod.val_lt x
    refine ⟨hvlt, ?_⟩
    have hcast : ((p * x.val + c : ℕ) : ZMod r) = 0 := by
      push_cast
      rw [ZMod.natCast_val, ZMod.cast_id, hx]
      field_simp
      ring
    exact (ZMod.natCast_eq_zero_iff _ _).mp hcast

/-- The double-count identity: summing the shift-hit count over one full period gives `K`. -/
lemma sum_card_shift_hits {r p K : ℕ} (hr : r.Prime) (hp : ¬ (r ∣ p)) :
    ∑ n ∈ range r, (((range K).filter (fun k => r ∣ p * n + 1 + k)).card) = K := by
  classical
  have hswap : ∑ n ∈ range r, (((range K).filter (fun k => r ∣ p * n + 1 + k)).card)
      = ∑ k ∈ range K, (((range r).filter (fun n => r ∣ p * n + (1 + k))).card) := by
    simp only [Finset.card_filter]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun n _ => ?_
    have : p * n + 1 + k = p * n + (1 + k) := by omega
    rw [this]
  rw [hswap]
  rw [Finset.sum_congr rfl fun k _ => card_solutions_eq_one (c := 1 + k) hr hp]
  simp

/-- **The exact local density of the whole `K`-shift family.**  For `r` prime, `r ∤ p` and
`K ≤ r`, exactly `K` of the `r` residues `n mod r` are used by the `p`-side. -/
theorem card_hit_eq {r p K : ℕ} (hr : r.Prime) (hp : ¬ (r ∣ p)) (hK : K ≤ r) :
    (((range r).filter (fun n => ∃ k ∈ range K, r ∣ p * n + 1 + k)).card) = K := by
  classical
  have hle : ∀ n, ((range K).filter (fun k => r ∣ p * n + 1 + k)).card ≤ 1 :=
    fun n => card_filter_shift_dvd_le_one (a := p * n + 1) hK
  have hpos : ∀ n, (∃ k ∈ range K, r ∣ p * n + 1 + k) ↔
      ((range K).filter (fun k => r ∣ p * n + 1 + k)).card = 1 := by
    intro n
    constructor
    · rintro ⟨k, hk, hdvd⟩
      have hne : ((range K).filter (fun k => r ∣ p * n + 1 + k)).Nonempty :=
        ⟨k, Finset.mem_filter.mpr ⟨hk, hdvd⟩⟩
      have h1 := Finset.card_pos.mpr hne
      have h2 := hle n
      omega
    · intro h1
      obtain ⟨k, hk⟩ : ((range K).filter (fun k => r ∣ p * n + 1 + k)).Nonempty :=
        Finset.card_pos.mp (by omega)
      simp only [Finset.mem_filter] at hk
      exact ⟨k, hk.1, hk.2⟩
  have hcard : (((range r).filter (fun n => ∃ k ∈ range K, r ∣ p * n + 1 + k)).card)
      = ∑ n ∈ range r, ((range K).filter (fun k => r ∣ p * n + 1 + k)).card := by
    rw [Finset.card_filter]
    refine Finset.sum_congr rfl fun n _ => ?_
    by_cases h : ∃ k ∈ range K, r ∣ p * n + 1 + k
    · rw [if_pos h, (hpos n).mp h]
    · rw [if_neg h]
      have h2 := hle n
      have hne : ((range K).filter (fun k => r ∣ p * n + 1 + k)).card ≠ 1 :=
        fun hc => h ((hpos n).mpr hc)
      omega
  rw [hcard, sum_card_shift_hits hr hp]

/-- **The pair version.**  At most `2K` residues mod `r` are used by the two sides together. -/
theorem card_hit_pair_le {r p q K : ℕ} (hr : r.Prime) (hp : ¬ (r ∣ p)) (hq : ¬ (r ∣ q))
    (hK : K ≤ r) :
    (((range r).filter (fun n =>
        (∃ k ∈ range K, r ∣ p * n + 1 + k) ∨ (∃ k ∈ range K, r ∣ q * n + 1 + k))).card)
      ≤ 2 * K := by
  classical
  have hsub : (range r).filter (fun n =>
      (∃ k ∈ range K, r ∣ p * n + 1 + k) ∨ (∃ k ∈ range K, r ∣ q * n + 1 + k))
      ⊆ ((range r).filter (fun n => ∃ k ∈ range K, r ∣ p * n + 1 + k))
        ∪ ((range r).filter (fun n => ∃ k ∈ range K, r ∣ q * n + 1 + k)) := by
    intro n hn
    simp only [Finset.mem_filter, Finset.mem_union, Finset.mem_range] at hn ⊢
    rcases hn.2 with h | h
    · exact Or.inl ⟨hn.1, h⟩
    · exact Or.inr ⟨hn.1, h⟩
  refine le_trans (Finset.card_le_card hsub) ?_
  refine le_trans (Finset.card_union_le _ _) ?_
  rw [card_hit_eq hr hp hK, card_hit_eq hr hq hK]
  omega

end NormalNumbers.CastingOut
