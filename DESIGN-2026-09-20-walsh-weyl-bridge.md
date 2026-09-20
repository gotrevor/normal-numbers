# The Walsh–Weyl bridge: two Fourier transforms, one normality 🌉

Ren / Fable 5.1, host session 2026-09-20.  Origin: Trevor's question whether the FFT /
Euler-formula relationship has something to say about normal numbers.  The answer is that
normality is the assertion that one measure looks like Haar measure in **two different duals**,
and the repo so far only carries one of them.  This note freezes the missing one as a Lean
node and records what the bridge does and does not buy.

**STATUS 2026-09-20: BOTH DIRECTIONS PROVED**, `src/NormalNumbers/Walsh.lean`.

`isNormalSequence_two_iff_parityMean` - binary normality **is** the vanishing of every
nonempty parity correlation.  Standard axioms, no sorries.  The chain:

| lemma | content |
|---|---|
| `prod_one_add_eq` | each window factor collapses to `2` on agreement, `0` on disagreement |
| `matchesAt_indicator_eq` | exact Hadamard expansion of a block indicator |
| `blockMean_eq` | the summed transform, exact at every finite `N` |
| `abs_blockMean_sub_le` | inequality (A), no truncation term |
| `sum_neg_one_pow_inter_eq_zero` | orthogonality of the block signs, `S` nonempty |
| `parityChar_eq_sum` | the pointwise inverse transform (exactly one word matches) |

Words are indexed by their one-sets (`wordOf`), which turns the enumeration of binary words
into a powerset and makes orthogonality fall out of the same product collapse used for
sufficiency.  The only analysis in the file is an `O(1)/N` boundary correction.

**The one ask.**  Next is base `b` (roots of unity in place of `±1`), or stop at base two.
Neither the repo nor Mathlib has Walsh functions or Erdős-Turán (grep 2026-09-20).

## 1. Two duals

Digits `d : ℕ → {0, …, b−1}` of `x`, orbit `u_n = b^n x mod 1`.

- **Circle side** (what the repo has): characters `θ ↦ e(hθ)`, `h ∈ ℤ`.  Weyl:
  `IsNormal b x ⟺ ∀ h ≠ 0, (1/N) Σ e(h·u_n) → 0`.  Formalized 2026-09-19 as
  `equidistributed_of_weyl` (`WeylCriterion.lean`) in the direction the G₄ wiring needs.
- **Digit side** (missing): characters of the digit group `(ℤ/b)^S` for a finite offset set
  `S`.  For `b = 2` and `S ⊂ ℕ` finite nonempty, the **parity correlation**

  `P_N(S) = (1/N) Σ_{n<N} ∏_{i∈S} (−1)^{d(n+i)}`.

  General `b`: `k : S → ℤ/b` not identically zero, `χ_k(n) = ∏_{i∈S} e(k_i·d(n+i)/b)`.

The FFT analogy is exact: the circle characters at frequencies `h·b^n` are the DFT the FFT
computes; the digit characters are the **Walsh–Hadamard** transform of the block-count
vector, and the radix-`b` butterfly of Cooley–Tukey is the digit shift `x ↦ bx mod 1`.

## 2. The identity (finite, exact, no analysis)

Fix `ℓ`, `w ∈ {0,1}^ℓ`, and let `F_N(w)` be the frequency of the block `w` among the first
`N` positions.  Pointwise, `1[d(n+i) = w_i ∀ i<ℓ] = 2^{−ℓ} Σ_{S⊆[ℓ]} (−1)^{w·S} χ_S(n)`
(with `χ_∅ = 1`).  Averaging over `n`:

  `F_N(w) = 2^{−ℓ} (1 + Σ_{∅≠S⊆[ℓ]} (−1)^{w·S} P_N(S))`   and   `P_N(S) = Σ_w (−1)^{w·S} F_N(w)`.

Hence the two-sided finite bounds

  (A) `|F_N(w) − 2^{−ℓ}| ≤ 2^{−ℓ} Σ_{∅≠S⊆[ℓ]} |P_N(S)| ≤ max_{∅≠S⊆[ℓ]} |P_N(S)|`,
  (B) `|P_N(S)| ≤ Σ_{w∈{0,1}^ℓ} |F_N(w) − 2^{−ℓ}|`  (using `Σ_w (−1)^{w·S} = 0` for `S ≠ ∅`).

(A) and (B) together: **`d` is 2-normal ⟺ every parity correlation `P_N(S) → 0`.**  Same for
base `b` with `b^{−ℓ}` and the nonzero `k`.  Unlike Erdős–Turán this transfer is **lossless**:
no `1/H` truncation term, no Beurling–Selberg majorant, because both sides live on the same
finite group.

## 3. Lean node (frozen statement, base 2 first)

```lean
/-- Parity correlation of the digit sequence `s` over the offset set `S`. -/
noncomputable def parityMean (s : ℕ → ℕ) (S : Finset ℕ) (N : ℕ) : ℝ :=
  (∑ n ∈ Finset.range N, ∏ i ∈ S, (-1 : ℝ) ^ s (n + i)) / N

theorem isNormalSequence_two_iff_parity (s : ℕ → ℕ) (hs : ∀ n, s n < 2) :
    IsNormalSequence 2 s ↔
      ∀ S : Finset ℕ, S.Nonempty → Tendsto (parityMean s S) atTop (𝓝 0)
```

Ingredients: the pointwise identity (`Finset.prod` over `S` of `(1 + (−1)^{w_i}(−1)^{s(n+i)})/2`
expanded by `Finset.prod_add`), the bridge from the repo's `countOccurrences w (List.range n).map s`
to `∑ n ∈ range (N − ℓ + 1), indicator`, and the two inequalities above.  No measure theory,
no Fourier analysis; lane 2 (known result), expected one Opus/low lap.  Second target: base `b`
with `Complex.exp (2πi k d / b)`, and the real-number wrapper `IsNormal 2 x ↔ …` via `digitOf`.

## 4. What the bridge explains

- **Digit-blindness, located.**  The difference-set leaf says an instrument seeing only
  `A − A` cannot detect a forbidden block.  The Walsh instrument is a *product of digits* and
  sees the block directly: for the `11`-free set, `P_N({0,1}) = P(00) + P(11) − P(01) − P(10)`
  with `P(11) = 0` is bounded away from zero at depth 2.  Blindness is a property of the
  **circle** dual, where the Rademacher function `r_i(x) = (−1)^{d_i(x)}` has the lacunary
  Fourier series `(4/π) Σ_{h odd} sin(2π h 2^{i−1} x)/h`, so a depth-`|S|` Walsh character is a
  `∏ 1/|h_i|`-weighted sum of Weyl sums at frequencies `Σ h_i 2^{i−1}`, not absolutely
  summable.  The `1/H` loss in Erdős–Turán is the price of crossing between the duals; stay on
  the digit side and there is no loss.
- **🧯 REFUTED the same day: the G₄ "sectors" are NOT the digit characters.**  The earlier
  version of this bullet claimed (75%) that G₄'s base-4 digit character at `k = 2`, i.e.
  `(−1)^{d_n}`, stands in for `(−1)^{ω(n)}` "modulo carries", and that the 2026-09-19
  verdict's SD sector (`h = 1,3,5`) versus Chowla sector (`h ≡ 2 mod 4`) is that character
  split seen from the circle side.  The owed carry check
  (`experiments/g4_carry_parity.py`, exact base-4 digits of `G₄ = Σ ω(n)/4ⁿ`) kills it:

  | N | carry-disturbed digits | `⟨(−1)^{d_n}(−1)^{ω(n)}⟩` |
  |---:|---:|---:|
  | 50 000 | 0.212 | +0.575 |
  | 200 000 | 0.301 | +0.399 |
  | 800 000 | 0.381 | +0.238 |

  The correlation **decays toward zero** and the disturbed fraction **rises**, so the two
  parities become asymptotically uncorrelated.  The mechanism is that `ω(n)` has mean
  `log log n` and fluctuation `√(log log n)`, so overflow past `3` is not a perturbation of
  the digit stream — it is a growing share of it, first biting at `n = 210 = 2·3·5·7` (the
  carry lands on position 209, hand-derived and confirmed).  "Modulo carries" was doing all
  the work in that sentence.

  What survives: the `k = 2` means of the true digits and of the carry-free surrogate are
  both ≈ 0 and track each other (0.0011 vs 0.0026 at `N = 800 000`).  That is **not**
  evidence for the identification — two quantities both near zero agree for free — so no
  sector claim should be rebuilt on it without a discriminating statistic.

  ⚠️ Nothing here touches `Walsh.lean`: the criterion is a theorem about an arbitrary binary
  sequence and does not care where the digits came from.  What is withdrawn is the *bridge*
  from that machinery to the live G₄ wiring.

- **What it does not buy.**  Nothing about any natural constant: the Walsh criterion moves
  the unknown from "Weyl sums at `h·2^n x`" to "digit correlations", the same wall in the
  other dual.  For constructions (Stoneham, G₄) it is a bookkeeping simplification, not a
  new estimate.

## 5. Prior art (named, not swept)

The Walsh-correlation criterion is classical (Walsh functions and dyadic expansions: Walsh
1923, Fine 1949) and is the working tool of the automatic-sequences-along-squares literature
(Drmota–Mauduit–Rivat, Müllner).  This note claims no novelty for §2; the deliverable is the
Lean node and the located blindness of §4.
