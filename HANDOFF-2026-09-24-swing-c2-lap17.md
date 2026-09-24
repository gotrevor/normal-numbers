# HANDOFF 2026-09-24 — swing at C2, lap 17 (K1 and K2 both DISCHARGED)

Branch `wip/swing-c2`, HEAD `cd14f74`, working tree clean, `lake build` **green** (9176 jobs).
Target file `src/NormalNumbers/SwingC2.lean` — **two** `sorry`s, one on the headline path.
Predecessor baton: `HANDOFF-2026-09-24-swing-c2-CHECKPOINT.md` (laps 1–16).

## The chain now

    ConjC2                       (CastingOut.ConjC2 — headline, kept)
      ⟸ tau_windowPrescribable
      ⟸ WindowPrescribable b tau
      ⟸ WindowShape b
      ⟸ SubLeafA b               subLeafA_of_constructionInputsB   ← NEW
      ⟸ ConstructionInputsB b    constructionInputsB_of_survivorLeaf
      ⟸ SurvivorLeaf b           survivorLeaf_of_carryLeaf         ← NEW
      ⟸ CarryLeaf b              ← THE ONLY OPEN OBLIGATION ON THE PATH

Off the path: `constructionInputs_even` (disclosed sorry, see §3).

## What landed this lap

### 1. (K1) is a theorem — `exists_kill_progression`
For a window of `L` slots with survivor `j₀`, there is a residue `n₀ mod killModulus b L` such
that EVERY `n ≡ n₀` satisfies `b^{j+1} ∣ τ(n+1+j)` for every slot `j ≠ j₀`, and the survivor
entry `n+1+j₀` is coprime to the (odd) modulus.

**The design change that makes it work quantitatively.**  Kill slot `j` with `L` DISTINCT primes
at exponent `b−1` each (each contributes the factor `(b−1)+1 = b` to `τ = ∏(v_p+1)`), NOT one
prime at exponent `b^{j+1}−1`.  Modulus drops from `exp(b^{L+1})` to `exp(O(bL⁴))`, i.e. `log M`
is polynomial in `L` while the pad budget `b^K` is exponential.
Supporting: `pow_card_dvd_tau`, `nextPrime`/`bigPrime` (Bertrand recursion with the explicit
bound `bigPrime B k + 2 ≤ 2^{k+1}(B+2)`), `factorization_shift_of_modEq`, `exists_pin_progression`
(the CRT induction), `killPrime`/`killModulus`, `killModulus_le : M ≤ 2^{b(L+5)^4}`,
`exists_pad_budget : K = 10ℓ+100 gives M ≤ 2^{b^{K/2}}`.

### 2. (K2) is a theorem — `exists_survivor_data`
In an odd progression whose survivor entry is coprime to `M`, there are `a < b^ℓ` and `r` coprime
to `M` such that EVERY odd prime `p ≡ r (mod M)` makes `2^a·p` land in the progression with
`τ(2^a·p) ≡ t (mod b^ℓ)`.  Two simplifications made this elementary:
* the exponent equation has a closed-form witness — take the even representative
  `T ∈ {2b^ℓ, t, t+b^ℓ}` of `t` and set `a = T/2 − 1` (`exists_survivor_exponent`);
* the inverse of `2` modulo an odd `M` is `(M+1)/2` on the nose, so the Dirichlet residue is
  `r = ((n₀+ℓ)·((M+1)/2)^a) % M` — no `ZMod` detour.
Dirichlet itself: `Nat.forall_exists_prime_gt_and_modEq` (mathlib, `LSeries/PrimesInAP.lean`).

### 3. Two defects of my own lap-17b statements, found and fixed
* **Parity obstruction for EVEN bases.**  `τ(m)` is odd exactly when `m` is a square, and for
  `2 ∣ b` every slot but `ℓ−1` carries a weight divisible by `b`, so the window's parity IS
  `τ(n+ℓ)`'s.  An odd target therefore forces a square survivor, which a progression need not
  admit (`M = 3`, `n₀+ℓ ≡ 2 mod 3`: no `n` in the class has `n+ℓ` square).  The lap-17b
  `SurvivorLeaf` was therefore FALSE for even `b`.  Routed around: a target `t` at length `ℓ` is
  the target `t·b` at length `ℓ+1`, and `t·b` is even — `ConstructionInputsB` +
  `subLeafA_of_constructionInputsB`.  `SurvivorLeaf` now carries the honest hypothesis
  `2 ∣ b → 2 ∣ t`.  The unrestricted `ConstructionInputs` for even `b` is kept as the disclosed
  off-path leaf `constructionInputs_even` (it needs the kill primes chosen with `ℓ−1−j` a QR —
  quadratic reciprocity + Dirichlet, a second layer `ConjC2` does not require).
* **Budget too weak by a constant.**  `M ≤ 2^{b^K}` is only borderline: a Linnik-size prime
  `p ≤ M^5` has `log p ≈ 5 log M ≈ 5 b^K`, i.e. ABOVE the budget.  Now `M ≤ 2^{b^{K/2}}` with
  `K = 10ℓ+100`, leaving all of `[M², 2^{b^K}]` free for the prime.

### 4. Structural finding (recorded in the `SurvivorLeaf` docstring)
No POINTWISE divisor bound can close (K3).  Any mechanism giving `b^{j+1} ∣ τ(n+1+j)` for all
`j < L` needs `≳ L²/2` prime-power constraints — a prime `q` serves only slots `j ≡ j₀ (mod q^b)`,
so primes below `L^{1/b}` contribute `O(L)` incidences in total — hence `log n ≳ L² log L`.  The
worst-case divisor bound there is `exp(Θ(L²))`, which exceeds `b^K ≤ b^L = exp(Θ(L))` for every
admissible `K`.  Only a typical-value statement can work.  (This retires the "worst-case τ ≤ 2√m"
family of attacks for good; lap 13's retraction was right for the wrong reason.)

## The crux, precisely: `CarryLeaf b`

    ∀ K M r a N, 0 < M → Coprime r M → a ≤ b^(K/2) → M ≤ 2^(b^(K/2)) → N ≤ b^(K/2) →
      ∃ p, N < p ∧ p.Prime ∧ p ≡ r [MOD M] ∧ carry b tau (2^a * p + K) < b^K

i.e. among the primes of ONE arithmetic progression, find one at which
`Σ_{k≥1} τ(2^a p + K + k)/b^k < b^K`.  Note the leaf caps how large `p` may be forced to be
(`N ≤ b^{K/2}`): the carry grows with `log p`, so an "arbitrarily large `p`" version is FALSE.

**Why it should be true.**  `log(2^a p) = O(b^{K/2} + log p)`; for `p` polynomial in `M` that is
`≪ b^K`.  The average of `τ(m)` for `m ≍ 2^a p` is `≍ log(2^a p) ≪ b^K`, so the exceptional set
has density `≪ log/b^K`.
**What it needs.**  That first moment ALONG THE PRIMES of the progression:
`Σ_{p ≤ Y, p ≡ r (M)} τ(2^a p + c) ≪ π(Y;M,r)·log Y` (Brun–Titchmarsh / Selberg upper-bound
sieve, moduli up to `√(2^a Y)`), plus a Linnik-type lower bound `π(Y;M,r) ≫ Y/(φ(M) log Y)` for
`Y = M^{O(1)}` so that the family is non-empty.  Both `🟡` project-scale; neither is in mathlib.

## Next actions (ordered)

1. **Decompose `CarryLeaf` further before attacking it.**  Two named sub-leaves:
   (a) `tau_sum_AP_le` — the elementary hyperbola upper bound
   `Σ_{n ≤ X, n ≡ ρ (M)} τ(n) ≤ 2(X log X / M + √X)` (no sieve; `τ(n) ≤ 2·#{d ∣ n, d ≤ √n}` and
   an exact AP count — mathlib has `Nat.Ico_filter_modEq_card`).  This is FULLY elementary and
   worth landing: it is the first moment over a FULL progression, and it already proves a
   "CarryLeaf over integers" variant.
   (b) the sieve/Linnik step that transfers (a) to the primes.
   Landing (a) turns the remaining gap into exactly the prime-transfer step.
2. **Consider the alternative that kills the transfer.**  If (K2) could be met congruentially
   rather than by a prime, `CarryLeaf` would average over a full progression and (a) alone would
   close it.  Recorded obstruction: `τ(m) ≡ t` needs `m`'s factorization known, and pinning
   valuations always leaves an uncontrolled cofactor.  Two escapes not yet refuted: (i) force the
   cofactor `= 1` by size (`D ∣ m`, `D > m/Y`) and vary the CRT data instead of `m`; (ii) two
   surviving slots so the target is a SUM of two divisor counts.  Both are cheap to think about
   and would be route-decisive.
3. **`constructionInputs_even`** (off path): the QR layer — choose the kill primes `q` with
   `ℓ−1−j` a quadratic residue mod `q` (reciprocity + Dirichlet), then a square survivor
   `m = (q^α p^β)²` with `2β+1` coprime to `b`.

## Assets unchanged

`probes/swingc2_window.py` (known-answer checked); kernel anchors `subLeafA_three_one`,
`subLeafA_three_two`, `subLeafB_three_one_0/1/2`.  All new theorems this lap are
`#print axioms`-clean (`propext, Classical.choice, Quot.sound`).
