# Referee: `SchmidtGames.lean` cited Props (2026-10-04)

Scope: `Literature.BFSPotentialDim` (+ `BFSDimInterval`, `BFSDimCantor`), `Literature.BFSBadPotential`, the definition `PotentialWinning`, and the sets `E`, `U`, `E₂`, `BA`, `Bad`, all in `src/NormalNumbers/SchmidtGames.lean` at `41a649f8`.  No `.lean` file was edited and nothing was built.

Sources read: arXiv:1703.09015 **v3** TeX (15 Sep 2017), and the **published** PDF, Acta Arith. 188 (2019) 289-316, DOI 10.4064/aa171127-8-11 (CC-BY, from impan.pl).  Bugeaud, *Distribution modulo one and Diophantine approximation* (2012), Problem 10.36 and Theorem 7.8, read from the PDF.

## Verdicts

| Item | Verdict | Confidence |
|---|---|---|
| `BFSPotentialDim J δ` as stated, so `BFSDimInterval` and `BFSDimCantor` | **FALSE** for every compact `J`: refutable in Lean (counterexample below).  Every theorem taking `hJ` is currently vacuous. | 99% |
| `BFSPotentialDim` with `ρ ≤ 1` added | **Implied by source** (Thm 5.5 + Example 5.2 + the proof's use of regularity only at scales `β^n ρ ≤ ρ`), and weaker (`dim_A ≤ dim_H`). | 85% |
| `BFSBadPotential` | **Implied by source** (published Lemma 3.11 + Remark 4.2 + Prop 4.5).  I re-derived the proof against the Lean game; it goes through. | 95% |
| `PotentialWinning` | **Faithful** to BFS Def 4.1 for `X = ℝ`, `H` = singletons, `c > 0`. | 95% |
| `E`, `U`, `E₂`, `BA`, `Bad` | Faithful.  `E C` is exactly Bugeaud Problem 10.36's condition `‖bⁿξ‖ > b^{−c}` for every `b ≥ 2`, `n ≥ 0`. | 97% |

## 1. `BFSPotentialDim` is false as stated: the missing small-scale hypothesis

BFS Thm 5.5 (same number in v3 and in print) quantifies `K₁, K₂` "independent of `α, β, c, ρ`", but Ahlfors regularity (Def 5.1) is only "for every sufficiently small ball".  The proof sets `ρ_n = β^n ρ` and uses `μ(B(x, ρ_n)) ≍ ρ_n^δ` from `n = 0`, so it silently needs `ρ` below the regularity scale.  The Prop copies the statement with `ρ` unrestricted, and for compact `J` that is false.

**Counterexample (Lean-checkable).**  Given any `K₁, K₂ > 0`, take `β = 1/4`, `c = 1/2`, `α = min(1/(4K₂²), log 4/(2K₁))`, `ρ = 1/α`, `S = (Icc 0 1)ᶜ`.  Alice's strategy is to delete `closedBall (1/2) (1/2)` at turn 0 when `(h 0).2 ≥ ρ`, and nothing otherwise.
- *Legal:* `(1/2)^{1/2} ≤ (α ρ₀)^{1/2}` since `α ρ₀ ≥ 1`.
- *Winning:* every Bob-legal play has `ρ₀ ≥ ρ`, so the deletion happens.  An outcome in `[0,1]` is deleted, and any other outcome lies in `S`.
- *Side condition:* `α^{1/2} ≤ 1/(2K₂) = (1 − (1/4)^{1/2})/K₂` ✓.
- *Prediction:* the Prop gives `dim_H(S ∩ [0,1] ∩ closedBall (1/2) ρ) ≥ 1 − K₁α/log 4 ≥ 1/2`.  The set is `∅`, so the dimension is 0.

**Numeric tripwire.**  With `K₁ = K₂ = 10`: `α = 0.0025`, `ρ = 400`.  The Prop predicts `≥ 0.982`, and the true value is 0.  **Control:** at `ρ ≤ 1` the same strategy is illegal.  One deletion of radius `≤ αρ₀ ≤ α < 1/2` cannot cover `[0,1]`, so the counterexample disappears exactly where the proof's hypotheses hold.  The Cantor instance fails the same way, with `J = cantorSet ⊆ [0,1]` and `x₀ = 0`.

Suggested known-false sibling, to be recorded in Lean against the *current* form before it is fixed:

```lean
theorem not_BFSDimInterval_unrestricted : ¬ Literature.BFSDimInterval   -- current statement
```

**Required change (exact).**  In `Literature.BFSPotentialDim`, change `0 < ρ →` to `0 < ρ → ρ ≤ 1 →`.  Both instances satisfy regularity with uniform constants at every scale `r ≤ 1`:
- Lebesgue on `[0,1]`: `r ≤ μ(B(x,r)) ≤ 2r`.
- The Cantor measure: `(r/3)^δ ≤ μ(B(x,r)) ≤ 3^{1+δ} r^δ`.
- Decay for singletons follows (Example 5.2).

Threshold 1 is also BFS's own convention: published §2, before Thm 2.5, defines compact Ahlfors-regular `J ⊂ ℝ` by `C⁻¹ρ^δ ≤ μ(B(x,ρ)) ≤ Cρ^δ` for `0 < ρ ≤ 1`.  Also say in the docstring that the hypothesis is implicit in BFS's proof.

**Ripple (wiring only, the statements survive):**
- `le_dimH_of_potentialWinning`: add `(hr1 : r ≤ 1)` and pass it to `hBFS`.  Its callers use `r = 1/2` or `1/8` ✓.
- `codim_E_asymp`: pass `(by norm_num : (1/2:ℝ) ≤ 1)` ✓.
- `not_potentialWinning_E_small`: `ρ = 2^{−C}/2` is `≤ 1` only for `C ≥ −1`.  Add `(hC : 0 ≤ C)`, which loses nothing because `E C = ∅` for `C ≤ 1`.

## 2. `BFSBadPotential`: implied (citation number fix only)

- **Numbering:** the BA lemma is **Lemma 3.11 in print** (Lemma 3.10 in arXiv v3).  Print inserts Remark 3.9, so its 3.10 is the `M_ε` lemma.  Remark 4.2 ("Lemmas 3.10-3.12 ... are `(α,β,0,ρ,P)`-potential winning"), Prop 4.4, Prop 4.5, Example 5.2 and Thm 5.5 keep their numbers.  Change "Lemma 3.10" to "Lemma 3.11 (arXiv v3: 3.10)" in both docstrings and in the AUDIT table.
- **Re-derivation in the Lean game:**
  - *Strategy.* Delete the unique `Δ_ε(p/q)` with `ℓ < (1−2ε)q⁻² ≤ β⁻¹ℓ`, where `ℓ = 2ρ_m`, that meets `B_m`.
  - *Separation.* Two members are more than `ℓ` apart, using `q₂/q₁ < β^{−1/2} ≤ 1/ε − 1`.
  - *Legality.* The radius is `ε/q² ≤ αρ_m`.  Since there is one deletion, `r^c ≤ (αρ_m)^c` for every `c > 0`.  It is legal on arbitrary histories too.
  - *Win.* Let `m` be the first turn with `2ρ_m < (1−2ε)q⁻²`.  It exists because `ρ_m → 0`.  At `m = 0` we have `2ρ₀ ≥ β`, and at `m > 0` we have `2ρ_m ≥ β·2ρ_{m−1}`.  BFS's text writes `q⁻²` where `(1−2ε)q⁻²` is meant, which is harmless.
  - *Fit.* `BA` with all `(p,q)`, including non-reduced ones, equals BFS's `BA₁(ε)`.

## 3. `PotentialWinning` against BFS Def 4.1, quantifier by quantifier

| BFS | Lean | Match |
|---|---|---|
| Bob: `ρ₀ ≥ ρ`; `ρ_{m+1} ≥ βρ_m`, `B_{m+1} ⊂ B_m` as sets, ignoring Alice | `BobLegal` | ✓ |
| Alice: countably many `N({y}, r)`, `r > 0`, `Σ r^c ≤ (αρ_m)^c` | `ℕ → Option (ℝ×ℝ)`, `closedBall y r`, ENNReal `tsum` bound | ✓ |
| Strategy may depend on all prior moves | Depends on Bob's history (Alice's moves are a function of it) | ✓ |
| Alice wins if radii do not tend to 0, or `x∞` is deleted, or `x∞ ∈ S` | `Tendsto … → ∀ x ∈ ⋂ balls → x ∈ S ∨ deleted` | ✓ |
| `c = 0` single-deletion rule | Not modelled (all uses have `c = 1/2`) | fine |
| Legality on legal plays | Legality on **all** histories with positive last radius | Equivalent: extend a BFS strategy by `none` off Bob-legal histories (classical choice) |

Monotonicity (`mono_alpha`, `mono_rho`) and `inter` cite Prop 4.5 and Prop 4.4 correctly.  The `α`-combination in `inter`, `(α₁^c + α₂^c)^{1/c}`, is BFS (4.4).

## 4. Novelty of "`1 − dim_H E C ≍ 2^{−C}`, `dim_H U = 1`, `dim_H(U ∩ C₃) ≥ log 2/log 3`"

- **BFS** (v3 and print, full text read) has no base-`b` or `×b`-orbit application.  Bugeaud appears only for the Folding Lemma and for suggesting their Question 2 (continued fractions).
- **Bugeaud 2012** lists 10.36 as **open**.  The best result it records is Thm 7.8, `‖ξbⁿ‖ > b^{−1100b log 3b}` (exponential in `b`).  It adds only that the set of numbers that are `b`-badly approximable for every `b`, with `b`-dependent constants, has dimension 1.  So `U`-type uniformity with a polynomial `b^{−C}` is not in the book.
- **Not opened by me:** FSU Memoirs, Broderick–Fishman–Kleinbock(–Weiss), Yavicoli.  The 10-04 audit's sweep covered their citers, and BFKW-style results are qualitative (non-dense orbits), which does not give `U`.
- **Verdict.**  Not stated in the checked literature: **~65%**.  As mathematics it is close to a **direct corollary** of BFS: a per-base analogue of their Lemma 3.10 (`M_ε`), giving `α_b ≍ b^{−C}·polylog`, then the countable intersection Prop 4.4 at `c = 1/2` (`Σ_b b^{−C/2} < ∞` for `C > 2`), then Thm 5.5.  An expert would likely call it an exercise: **~75%**.  The upper half (`codim ≥ 2^{−(C+1)}`) is a classical bounded-run count.  The dimension claims are a modest, publishable-as-a-note strengthening of 10.36, not a deep result.
