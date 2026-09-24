import NormalNumbers.TwoPointDepthPeel

/-!
# Depth is irrelevant: every admissible surface states the same problem

`pairDecorr_iff_multiElliottWeighted` (`PairDecoupleOneDigit.lean`) makes the crux equivalent to a
**fixed-depth weighted** `2K₀`-point correlation, for every fixed `K₀`.
`pairDecorr_iff_unweighted` (`TwoPointDepthPeel.lean`) makes it equivalent to a **growing-depth
unweighted** one, for every schedule meeting the carry budget.  Routing both through the crux
gives two structural facts, free but not obvious:

* **schedule invariance** — all admissible growing depths state the same problem, so there is no
  gain in choosing `K(M) ≍ log_b log M` over `K(M) = M`.  Length is not the resource;
* **the weight is exactly worth the extra depth** — a fixed-depth *weighted* correlation and a
  growing-depth *unweighted* one are equivalent.  So one cannot trade the `peelWeight` away for a
  genuinely easier statement: dropping it costs precisely an unbounded number of linear forms.

Together these close off "pick a better depth / drop the weight" as a strategy, in kernel.
-/

open Finset Filter Topology

namespace NormalNumbers.CastingOut

/-- **Schedule invariance.**  Any two admissible depth schedules state the same problem. -/
theorem multiElliottGrowing_schedule_invariant (b : ℕ) (hb : 2 ≤ b) (t : ℝ) (K K' : ℕ → ℕ)
    (hbud : ∀ p q : ℕ, p.Prime → q.Prime → p ≠ q →
      Tendsto (fun M => peelBound b p q (K M) M t) atTop (𝓝 0))
    (hbud' : ∀ p q : ℕ, p.Prime → q.Prime → p ≠ q →
      Tendsto (fun M => peelBound b p q (K' M) M t) atTop (𝓝 0)) :
    (∀ p q : ℕ, p.Prime → q.Prime → p ≠ q → MultiElliottGrowing b p q t K)
      ↔ (∀ p q : ℕ, p.Prime → q.Prime → p ≠ q → MultiElliottGrowing b p q t K') :=
  (pairDecorr_iff_unweighted b hb t K hbud).symm.trans
    (pairDecorr_iff_unweighted b hb t K' hbud')

/-- **The weight is exactly worth the extra depth.**  A fixed-depth *weighted* `2K₀`-point
correlation is equivalent to a growing-depth *unweighted* one. -/
theorem multiElliottWeighted_iff_growing (b : ℕ) (hb : 2 ≤ b) (t : ℝ) (K₀ : ℕ) (K : ℕ → ℕ)
    (hbud : ∀ p q : ℕ, p.Prime → q.Prime → p ≠ q →
      Tendsto (fun M => peelBound b p q (K M) M t) atTop (𝓝 0)) :
    (∀ p q : ℕ, p.Prime → q.Prime → p ≠ q → MultiElliottWeighted b p q K₀ t)
      ↔ (∀ p q : ℕ, p.Prime → q.Prime → p ≠ q → MultiElliottGrowing b p q t K) :=
  (pairDecorr_iff_multiElliottWeighted b hb t K₀).symm.trans
    (pairDecorr_iff_unweighted b hb t K hbud)

/-- The hypothesis-free instance: the `K₀`-depth weighted leaf equals the `K(M)=M` unweighted one,
for every `K₀`. -/
theorem multiElliottWeighted_iff_growing_id (b : ℕ) (hb : 2 ≤ b) (t : ℝ) (K₀ : ℕ) :
    (∀ p q : ℕ, p.Prime → q.Prime → p ≠ q → MultiElliottWeighted b p q K₀ t)
      ↔ (∀ p q : ℕ, p.Prime → q.Prime → p ≠ q → MultiElliottGrowing b p q t id) :=
  multiElliottWeighted_iff_growing b hb t K₀ id
    (fun p q _ _ _ => tendsto_peelBound_id b hb p q t)

/-- In particular the `K₀ = 1` **two-point weighted** leaf — the shortest statement in the
repo — already equals the full unbounded-length unweighted Elliott correlation. -/
theorem twoPointWeighted_iff_growing_id (b : ℕ) (hb : 2 ≤ b) (t : ℝ) :
    (∀ p q : ℕ, p.Prime → q.Prime → p ≠ q → MultiElliottWeighted b p q 1 t)
      ↔ (∀ p q : ℕ, p.Prime → q.Prime → p ≠ q → MultiElliottGrowing b p q t id) :=
  multiElliottWeighted_iff_growing_id b hb t 1

end NormalNumbers.CastingOut
