# Referee: `NormalNumbers.FiniteStateSelection` cited inputs (2026-10-04)

Scope: the three `Literature.*` Props in `src/NormalNumbers/FiniteStateSelection.lean` (branch `proof/finstate`), the definitions they depend on, and the faithfulness of `PulariDPDTQuestion` / `PulariWeakening` to Pulari §5.  No `.lean` file was edited and nothing was built.

Sources read:
- Pulari, arXiv:2602.01199 **TeX source** (`main.tex`, e-print dated 3 Feb 2026 = v2): §2 (Defs 1-5), §3 Lemma 1, §4 in full, §5 in full.
- Carton-Perifel, LMCS 20(3) 2024 15:1-15:8 = arXiv:2205.00734v6, all 8 pages.
- Doty-Moser, arXiv:cs/0609096: §2 and §3, Theorems 3.3, 3.11 and 3.12.
- Mayordomo, arXiv:2208.00157: §3 (Thm 3.2, Thm 3.3 with proof) and §4 (SE, `K^{T,f}_δ`, `dim^f_FS`).
- Bourke-Hitchcock-Vinodchandran, TCS 349 (2005): abstract only ("normality is equivalent to finite-state dimension 1"); the full PDF did not load.

## Verdicts

| Prop | Verdict | Confidence | Lean fix |
|---|---|---|---|
| `Literature.cartonPerifel_normal` | **stronger than the source for `2 ≤ k ≤ 6`**, though true.  Prop 2.1 is stated for "some large enough integer k", and the paper names `k ≥ 7` as the threshold its proof reaches | 92% that the Lean statement is true; 97% that it overstates the citation | **required**: weaken to `7 ≤ k`; carry `k ∈ {5,6}` (or all `k ≥ 2`) as our own leaf (§1) |
| `Literature.fsDim_one_isNormal` | **implied by the sources, wrong theorem number.**  Doty-Moser Thm 3.11 gives only `dim_FS ≤ fsDim`, the useless direction here; the direction this Prop uses, `fsDim ≤ dim_FS`, is DM **Thm 3.12**.  Mayordomo Thm 3.2 states the fixed-`T` form directly.  The FST model matches DM | 93% | docstring only (§2) |
| `Literature.pulari_coherent_eqchar` | **implied: a faithful transcription of Pulari Thm 3** (`thm:fscoherent-eqchar`).  The `⌊·⌋` reading is exact by his Lemma 6 for `n ≥ 1`, and `n = 0` lies outside `Icc 1 N` | 90% (the 10% is Pulari's chain through Mayordomo Thm 3.3, whose Claim 3.5 proof is a sketch; I re-derived the step needed, §3) | none |

**Headline `pulariDPDTQuestion_of_lit` (`k ≥ 5`).**  It typechecks against the current Prop.  With a citation-faithful `cartonPerifel_normal` (`7 ≤ k`), it survives:
- **as is for `k ≥ 7`**;
- **for `k ∈ {5, 6}` only if a new believed leaf** for normality of `cpSeq` is added (the exact text is in §1; it is mathematically routine, ~90%).

Nothing here is false or vacuous.

## 1. `Literature.cartonPerifel_normal`

**What the source says.**  Carton-Perifel, p. 15:4, verbatim: "**Proposition 2.1.** Let A be the alphabet {0, . . . , k − 1} for some large enough integer k.  Let w_n be, for each integer n ⩾ 1, the concatenation in lexicographic order of all words of length n over A.  The deterministic pushdown transducer T_k given above compresses the normal sequence x = w₁ w̃₁ w₂ w̃₂ w₃ w̃₃ ⋯."  Then: "The proof that the sequence x is normal is an easy adaptation that the Champernowne sequence is normal [BC18, Thm 7.7.1].  The proposition states the result for k large enough.  The proof below shows that the condition k ⩾ 7 is sufficient but numerical experiments show that k ⩾ 5 is actually sufficient."  The proof of Prop 2.1 (p. 15:7) is about compression only.  It closes with "The inequality is satisfied for k ⩾ 7".  §3 contains no normality argument.

**Quantifier check.**
- `∀ k ≥ 2`: the source asserts normality only inside a proposition quantified over "large enough k", with the stated sufficient threshold `k ≥ 7`.  The "easy adaptation" remark carries no restriction on `k`, but it gives no proof either.
- **`k ≥ 5` is NOT covered by "k large enough".**  The `k ≥ 5` sentence reports *numerical experiments* about *compression*, so it is neither a proof nor a normality claim.  `k ∈ {5, 6}` and `k ∈ {2, 3, 4}` are therefore our transcription, not theirs.
- Definitions match: `normal` is overlapping-occurrence block frequency `→ (#A)^{-|w|}` for every word, the same as `IsNormalSequence`.  `w_n` is the lexicographic concatenation (`lexWord`, most significant digit first, `j = 0 … k^n−1`), and `w̃` is the reversal (`List.reverse`).  Positions 1-based vs 0-based is immaterial.

**Is the overstated part true?**  Yes, I believe so (90%), for every `k ≥ 2`.  Sketch, for a future leaf:
1. Inside complete blocks, `wₙ` contains each length-`n` word exactly `n` times cyclically (perfect necklace, ABFY16 Thm 5, which CP use in Lemma 3.4).  So every length-`ℓ` word appears `n k^{n−ℓ} ± O(ℓ)` times in `wₙ`, and the same holds in `w̃ₙ` (reversal maps occurrences of `u` to occurrences of `ũ`, and the count is uniform).
2. A prefix that ends inside `wₙ` is the Champernowne case: decompose the first `j` lexicographic words into ≤ `k−1` cylinders per depth `t`.  Non-uniform occurrences touch the fixed prefix, contributing `O((t₀+ℓ) k^{n−t₀})` for the top depth `t₀ ≥ 1`.  That is `o` of the `≍ n k^{n−1}` letters already read in `w̃_{n−1}`.
3. A prefix that ends inside `w̃ₙ` is the reverse of a suffix of `wₙ`.  Complementing digits (`a ↦ k−1−a`) reverses lexicographic order, so that suffix is the complement of a lexicographic prefix with each word reversed.  Within-word counts reduce to step 2.  Cross-word occurrences are `O(ℓ/n)` of the total, and the full `wₙ` (length `n kⁿ`) has already been read.

**Numeric tripwire** (`probes/finite_state_cp_normality_probe.py`, 5 s).  `D(N) = max_{ℓ≤3, |u|=ℓ} |freq_u(x↾N) − k^{−ℓ}|`, worst over checkpoints at every block end and at the 1/4, 1/2 and 3/4 mid-block points of the last two stages.
- Known-normal control: lexicographic concatenation `w₁w₂w₃⋯`.
- Known-non-normal control: `wₙ 0^{|wₙ|}`.

| k | sequence | length | worst D, stage n−3 | worst D, last two stages |
|---|---|---|---|---|
| 2 | CP `wₙw̃ₙ` | 393,220 | 0.0173 | **0.0137** |
| 2 | lex control (normal) | 196,610 | 0.0297 | 0.0240 |
| 2 | `wₙ0ⁿ` control (non-normal) | 393,220 | 0.4375 | 0.4375 |
| 3 | CP | 147,624 | 0.0459 | **0.0302** |
| 3 | lex control | 73,812 | 0.0727 | 0.0486 |
| 3 | `wₙ0ⁿ` control | 147,624 | 0.4813 | 0.4815 |
| 5 | CP | 224,610 | 0.1153 | **0.0600** |
| 5 | lex control | 112,305 | 0.1581 | 0.0857 |
| 5 | `wₙ0ⁿ` control | 224,610 | 0.4955 | 0.4960 |

- CP decays in step with the known-normal control and slightly faster.  That is the expected `≍1/n` Champernowne rate, set by the mid-`wₙ` checkpoints where the leading digit is frozen.
- The non-normal control stays flat, so the instrument can fail.
- Nothing distinguishes `k = 2` or `k = 5` from `k ≥ 7`.
- Side reading for the headline leaf: the coder's zero frequency at the last block end is 0.5035 / 0.5004 / 0.5002 for `k = 2/3/5` (`1/k` = 0.5/0.333/0.2).  This agrees with the audit's probe and with the `≥ 1/4` leaf.

**Required change (exact).**  Make the Literature Prop citation-faithful and move the extension into a leaf:

```lean
/-- **Carton–Perifel 2024**, Prop. 2.1 … stated for "large enough" `k`; the paper's proof
reaches `k ≥ 7` ("The inequality is satisfied for k ⩾ 7"), and normality is asserted for the
sequence in that statement.  Transcribed for exactly that range. -/
def cartonPerifel_normal : Prop :=
  ∀ (k : ℕ) [NeZero k], 7 ≤ k → IsNormalSequence k fun i => (cpSeq k i : ℕ)
```

and, in `NormalNumbers.FiniteState`:

```lean
/-- **Leaf (90%).**  `w₁w̃₁w₂w̃₂⋯` is normal in every base `k ≥ 2` (Carton–Perifel's
"easy adaptation" of [BC18, Thm 7.7.1], which they assert without a base restriction but
do not prove; for `k ≥ 7` it is `Literature.cartonPerifel_normal`).  Proof: perfect-necklace
counts inside full blocks; cylinder decomposition for a prefix ending in `wₙ`; complement +
reversal reduces a prefix ending in `w̃ₙ` to the same count. -/
theorem isNormal_cpSeq [NeZero k] (hk : 2 ≤ k) :
    IsNormalSequence k fun i => (cpSeq k i : ℕ) := by
  sorry
```

Then change `mirrorEnum_cpReal_facts_of_not_normal` to take `(hn : IsNormalSequence k fun i => (cpSeq k i : ℕ))` in place of `hCP`.  `pulariDPDTQuestion_of_lit` (`5 ≤ k`) supplies `isNormal_cpSeq`, and `mirror_not_mealy` does the same.  Optionally add a `7 ≤ k` twin `pulariDPDTQuestion_of_lit_cited` that uses only `hCP`, so the fully cited range is visible by name.  The alternative minimal fix is to restrict the headline to `7 ≤ k`, which loses `k ∈ {5,6}`.

## 2. `Literature.fsDim_one_isNormal`

**Model check against Doty-Moser §2.2** (verbatim: "A finite-state transducer (FST) is a 4-tuple T = (Q, δ, ν, q0), where Q is a nonempty, finite set of states, δ : Q × Σ → Q …, ν : Q × Σ → Σ∗ …, q0 ∈ Q …  Furthermore, we assume that every state in Q is reachable from q0").
- `Σ` is a general finite alphabet, the same for input and output.
- `T(xa) = T(x) ν(δ̂(x), a)`.
- Our `FST` matches: states `Fin (m+1)`, start `0`, `ν` into `List (Fin k)`, no injectivity.  The reachability assumption is harmless, since unreachable states never affect `run` and can be pruned.  Pulari's Def 1 is the same model.
- `infoK` is DM's / Mayordomo's `K^T(w) = min{|π| : T(π) = w}`, with `⊤` off the range, as in Pulari.

**Theorem-number problem.**  DM Theorem 3.11 is *not* `inf_T liminf K^T(S↾n)/n`.  It reads `dim_FS(S) = lim_{k→∞} liminf_n D^k_FS(S↾n)/n`, where `D^k_FS(x) = min{|π| : ∃T ∈ FST^{≤k}, T(π) = x}`.  That is a description-length-bounded class with the minimum over `T` taken *per prefix*.
- 3.11 gives `D^k ≤ K^T` for `|T| ≤ k`, hence `dim_FS(S) ≤ fsDim S`.  That is the wrong direction for "`fsDim S = 1` ⇒ normal".
- The needed direction, `fsDim S ≤ dim_FS(S)`, follows from DM **Theorem 3.12**: `dim_FS(S) = inf_{T∈FST, R∈Σ^∞, T(R)=S} liminf_m m/|T(R↾m)|`.  For such `(T,R)`, put `n_m = |T(R↾m)|`.  Then `T(R↾m) = S↾n_m`, so `K^T(S↾n_m) ≤ m` along infinitely many `n_m → ∞`.  So `liminf_n K^T(S↾n)/n ≤ liminf_m m/|T(R↾m)|`.
- Mayordomo 2208.00157 **Theorem 3.2** states the fixed-`T` form directly, attributed to [DM].
- Pulari's Lemma 1 repeats the "Theorem 3.11" attribution.  The composite is true, but our docstring should not inherit the slip.

**BHV direction.**  Only "`dim_FS = 1` ⇒ normal" is used.  The BHV abstract states "normality is equivalent to finite-state dimension 1", and Mayordomo Corollary 3.6 cites the same characterization for base `b`.  I could not load the BHV full text to confirm the alphabet generality (their definitions are over a general `Σ` per the citing papers): ~5% residual.

**Change (docstring only):** replace "Doty–Moser … Theorem 3.11 (`dim_FS(S) = inf_T liminf K^T(S↾n)/n`)" with "Doty–Moser … Theorems 3.11–3.12 (the direction used here, `inf_T liminf K^T(S↾n)/n ≤ dim_FS(S)`, is Thm 3.12; the fixed-`T` form is stated as Mayordomo arXiv:2208.00157 Thm 3.2)".  The Lean statement needs no change.

## 3. `Literature.pulari_coherent_eqchar`

**Source** (Pulari `thm:fscoherent-eqchar`, verbatim): "Let f be a finite-state coherent separator enumerator over Σ and let x∈[0,1).  Then x is f-normal if and only if the integer sequence (k^n a_n^f(x))_{n≥1} is k-adically equidistributed."  Def 8 (`def:fs-coherent`): "there exists an invertible synchronous Mealy machine M such that for every nonempty w∈Σ^n, f(w)=grid(M(w)) … (For definiteness, set f(λ)=0.)"

**Quantifier check.**
- `∀ k ≥ 2` matches Pulari's standing `k = |Σ| ≥ 2`.
- `∀ M, M.IsInvertible` matches Def 7: per-state output a permutation, `Q` finite nonempty (our `q0` gives nonemptiness).
- `mealyEnum M = grid ∘ M.run`, and `grid [] = 0` matches `f(λ) = 0`.
- `∀ x ∈ [0,1)` matches.
- The "separator enumerator" hypothesis is automatic (his Lemma 5), so omitting it is fine.
- `IsFNormal` / `fDim` are Pulari Defs 3-4 = Mayordomo §4.  Details:
  - strict `|f(w) − x| < δ`;
  - `log_k(1/δ)`;
  - `liminf` over `δ → 0⁺`, which is `𝓝[>] 0`;
  - `ℝ≥0∞` division is harmless, since `⊤` off the range agrees with the `min ∅ = ∞` convention.
- `scaled = ⌊kⁿ · bestBelow⌋`: Pulari Lemma 6 gives `kⁿ a_n^f(x) = ⌊kⁿx⌋ ∈ ℤ` for `n ≥ 1`, so the floor is the identity there.  `n = 0` is excluded by `Finset.Icc 1 N`, as is Pulari's `n ≥ 1`.
- `KAdicEquidist` matches Def 6 exactly (`m ≥ 1`, `r < k^m`, `#{1≤n≤N}/N → k^{−m}`).

**Proof soundness.**  The chain runs Lemma 7 (relabel), Prop 2, Thm 2, Thm 3.
- Lemma 7 and Prop 2 are correct.  `M∘T` is an FST on `Q_T × Q_M`; `M` is injective on `Σ*`; and `T ↦ M∘T` is surjective up to computed function via `M⁻¹∘S`.
- Thm 2 uses Mayordomo Thm 3.3.  The hard half of that (Claim 3.5) has a sketch proof ("tighter approximations can be delayed").  I re-derived the half Thm 3 actually needs, "normal `x` ⇒ `dim^{f_std}(x) ≥ 1`".  A `k^{−m}`-approximant `w` is one of three things:
  - `S↾m`, or its `±1` neighbour, which differs only on a trailing run of `0`s or `(k−1)`s;
  - a shorter grid point, which forces such a run.

  Normality makes every such run `o(m)`, since a run of `εm` at position `m` would push a digit frequency off `1/k`.  The monotone-output argument then gives `K^T(S↾j) ≤ K^T(w)` for some `j ≥ m − o(m) − L`.  The other half (`≤`, via `S↾m` itself) is immediate.
- The statement is true.  No change.

## 4. Definitions against Pulari §2-§5

| Lean | Pulari | Match |
|---|---|---|
| `grid` | `val(u)/k^{|u|}` | ✓ (0-indexed `i+1` exponent = his 1-indexed) |
| `IsSepEnum` | Def 2: `Im f ⊆ [0,1)` countable, dense | ✓ (countability automatic; `∀ 0≤a<c≤1, ∃ f w ∈ (a,c)` ⇔ dense in `[0,1)`) |
| `FST`, `run`, `infoK` | Def 1 + `K^T` | ✓ |
| `approxK`, `fDim`, `IsFNormal` | Defs 3-4 | ✓ |
| `bestBelow` | Def 5 `max{f(w) : |w|≤n, f(w)≤x}` | ✓ on nonempty finite sets; `sSup ∅ = 0` is a junk value where Pulari is undefined (see note) |
| `scaled` | `kⁿ a_n^f(x)` | ✓ given the integrality conjunct carried in `PulariDPDTQuestion` |
| `KAdicEquidist` | Def 6 | ✓ |
| `Mealy`, `IsInvertible`, `mealyEnum` | Defs 7-8 | ✓ (`Mealy` drops only the permutation clause, which `IsInvertible` restores) |
| `RTDPDT`, `IsDPDTEnum` | **undefined in Pulari**: the §2 subsection "Deterministic pushdown transducers" is an empty commented-out stub in the v2 source | Our class is real-time (no ε-moves), finite `Q`/`Z`, empty stack allowed (≡ CP's bottom marker `⊥`), `f = grid ∘ P`.  It is a **subclass** of the Carton-Perifel DPDT model (which allows ε-transitions), so an existential answer in it answers every reasonable reading |

**Note (optional hardening, not required).**  `PulariDPDTQuestion` is existential, so the `bestBelow` junk value at an empty candidate set could in principle make it easier.  The witness has `f [] = 0 ≤ x`, so the question is unaffected.  To close the loophole for future witnesses, add `(∀ n, ∃ w : List (Fin k), w.length ≤ n ∧ f w ≤ x)` as a conjunct.  It holds for `mirrorEnum` via `w = []` and `grid_nil`.

## 5. The §5 questions

Pulari §5, verbatim (v2 `main.tex`):

> "This raises the natural question of how far this correspondence persists beyond finite-state coherent relabelings.  One concrete setting is when the naming map is computable by a deterministic pushdown transducer.  In particular, does there exist such a separator enumerator $f$ and a point $x\in[0,1)$ for which the integer sequence $(k^n a_n^f(x))_{n\ge 1}$ is $k$-adically equidistributed while $\dim_{\mathrm{FS}}^{f}(x)<1$?"

> "It would be interesting to determine whether some weaker condition (e.g. levelwise surjectivity or bounded-to-one behavior on each $\Sigma^n$) suffices for the same equidistribution characterization, or whether non-invertible finite-state relabelings can already break it."

- **`PulariDPDTQuestion k`: faithful, for fixed `k`.**  It is `∃ f, IsSepEnum f ∧ IsDPDTEnum f ∧ ∃ x ∈ [0,1), integrality ∧ KAdicEquidist ∧ fDim < 1`.  The added integrality conjunct only strengthens a "yes", since Pulari presupposes "the integer sequence".  `IsDPDTEnum` is the real-time subclass, which also strengthens the "yes".  Pulari's own `O(n log n)` example is not DPDT-computable in any obvious way (`0ⁿ ↦` digits of `k^{n−1} − n` needs the length before the low digits).  The commented-out pushdown claim in his source (line 114) confirms the question was live for him.
- **`PulariWeakening k`: a faithful partial formalization of the second sentence.**  It covers "non-invertible finite-state relabelings" read as **synchronous** Mealy relabelings without the permutation condition.  That is the natural reading, since Def 8's relabelings are synchronous Mealy machines.
  - Restricting to `IsSepEnum (mealyEnum M)` is forced: Thm 3's hypothesis is "separator enumerator".
  - It does **not** cover non-synchronous finite-state relabelings (general FSTs).  The docstring and the stretch file already say so, and a write-up should say "for synchronous relabelings" in the answer's first sentence.
  - The two leaves it uses check out: a missed `u ∈ Σⁿ` empties the interval `(grid u, grid u + k^{−n})`, and levelwise surjectivity gives bijectivity at every reachable state by counting on `Σ^{n+1}`.

## Summary of required edits (none made)

1. `Literature.cartonPerifel_normal`: `2 ≤ k` → `7 ≤ k`, plus the new leaf `isNormal_cpSeq` (90%), with `mirrorEnum_cpReal_facts_of_not_normal` taking `hn` directly.  Without the leaf, the headline must drop to `7 ≤ k`.
2. `Literature.fsDim_one_isNormal` docstring: cite DM Thm 3.12 (and Mayordomo Thm 3.2) for the direction used, not Thm 3.11 alone.
3. Optional: the `bestBelow` nonempty-candidate conjunct in `PulariDPDTQuestion`.
