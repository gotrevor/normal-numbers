# The Walsh–Weyl bridge: two Fourier transforms, one normality 🌉

Ren / Fable 5.1, host session 2026-09-20.  Origin: Trevor's question whether the FFT /
Euler-formula relationship has something to say about normal numbers.  The answer is that
normality is the assertion that one measure looks like Haar measure in **two different duals**,
and the repo so far only carries one of them.  This note freezes the missing one as a Lean
node and records what the bridge does and does not buy.

**The one ask.**  Freeze `isNormalSequence_iff_walsh` (§3) as the next small lap; it is
self-contained, finite, and fills a gap that neither the repo nor Mathlib has (grep
2026-09-20: no `Walsh`, no Erdős–Turán in `Mathlib/`).

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
- **The G₄ "sectors" are Walsh characters.**  G₄'s base-4 digits are `ω(n)` with carries.
  The depth-1 digit characters are `e(k·d/4)`, `k = 1, 2, 3`; `k = 2` is `(−1)^{d}` ≈
  `(−1)^{ω(n)}` modulo carries, a bounded multiplicative function, so its correlations are
  Chowla-shaped.  The 2026-09-19 verdict's split into an SD sector (`h = 1, 3, 5`) and a
  Chowla sector (`h ≡ 2 mod 4`) is this character split seen from the circle side.  Owed
  before anything is built on it: a check that the carry layer does not break the
  identification (confidence 75%).  If it holds, Tao–Teräväinen's logarithmically averaged
  odd-order Chowla is the external theorem nearest the `k = 2` sector, which is why
  log-density normality is the honest lane the verdict named.
- **What it does not buy.**  Nothing about any natural constant: the Walsh criterion moves
  the unknown from "Weyl sums at `h·2^n x`" to "digit correlations", the same wall in the
  other dual.  For constructions (Stoneham, G₄) it is a bookkeeping simplification, not a
  new estimate.

## 5. Prior art (named, not swept)

The Walsh-correlation criterion is classical (Walsh functions and dyadic expansions: Walsh
1923, Fine 1949) and is the working tool of the automatic-sequences-along-squares literature
(Drmota–Mauduit–Rivat, Müllner).  This note claims no novelty for §2; the deliverable is the
Lean node and the located blindness of §4.
