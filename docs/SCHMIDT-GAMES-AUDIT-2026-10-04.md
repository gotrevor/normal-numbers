# Schmidt-games lane (E1): audit and freeze, 2026-10-04

Direction: `docs/ENGINE-PROPOSALS-2026-10-04.md` §E1.  Frozen as `src/NormalNumbers/SchmidtGames.lean` (stretch in `SchmidtGamesStretch.lean`), branch `proof/games`.

## Verdict

**Run it.**  The new statement is the size of the Bugeaud 10.36 set.  Put `E C = {ξ : ‖bⁿξ‖ > b^{−C} ∀ b ≥ 2, n ≥ 0}` and `U = ⋃_C E C`.

- **Headline 1, `potentialWinning_E`** (`sorry`): for `0 < β < 1` and `ρ > 0` there is `K` with `E C` `(K·2^{−C}, β, 1/2, ρ)`-potential winning for all `C ≥ 3`.  Mathematics 90%, Lean 65% (2–4 laps).
- **Headline 2, `dimH_E₂_le`** (`sorry`): `dim_H {ξ : ‖2ⁿξ‖ > 2^{−C} ∀ n} ≤ 1 − 2^{−(C+1)}`.  A run-length count; mathematics 97%, Lean 55%.
- **Wired, sorry-free given headline 1 as a hypothesis and the cited dimension theorem:**
  - `codim_E_asymp`: `1 − dim_H E C ≍ 2^{−C}`.  Every base at once costs, up to a constant in the codimension, what base 2 alone costs.
  - `dimH_U_eq_one_of`: `dim_H U = 1`.
  - `le_dimH_U_inter_cantor_of`: `dim_H(U ∩ C₃) ≥ log 2/log 3`.
  - `le_dimH_U_inter_Bad_inter_cantor_of`: the same for `U ∩ BAD ∩ C₃`.
- **Stretch, `exists_computable_cantorPoint_mem_U_inter_Bad`**: a computable point of `U ∩ BAD ∩ C₃`.  True 75%, Lean 25%.

Freshness of the headline content: about 55%.  Nobody states the size of `U`.  But once the early-charging count from `UniformBad` is played inside the Broderick–Fishman–Simmons potential game, the rest is their machinery, and experts could call it routine.

## Referee (2026-10-04)

Full report: `docs/SCHMIDT-GAMES-REFEREE-2026-10-04.md`.

- **`BFSPotentialDim` was false as first frozen** (ρ unrestricted).  Counterexample: `S = [0,1]ᶜ`, `ρ = 1/α`; Alice deletes `closedBall (1/2) (1/2)` at turn 0.  Now in the kernel: `not_BFSPotentialDimUnrestricted` (any nonempty `J ⊆ [0,1]`, `δ > 1/2`), instances `not_BFSDimInterval_unrestricted`, `not_BFSDimCantor_unrestricted`, against the frozen old form `Literature.BFSPotentialDimUnrestricted`.
- **Fix:** `BFSPotentialDim` takes `ρ ≤ 1` (BFS §2 convention, implicit in their proof).  Ripple: `le_dimH_of_potentialWinning` gains `(hr1 : r ≤ 1)`; `not_potentialWinning_E_small` gains `(hC : 0 ≤ C)` (`E C = ∅` for `C ≤ 1`, nothing lost).  All headline conclusions unchanged.
- **`BFSBadPotential`:** implied by source (95%); cite Lemma 3.11 in print = Lemma 3.10 in arXiv v3.
- **`PotentialWinning`, `E`, `U`, `E₂`, `BA`, `Bad`:** faithful.
- **Novelty:** not stated in the literature checked, ~65%; but ~75% an expert calls it a direct corollary of BFS (per-base `M_ε` lemma giving `α_b ≍ b^{−C}·polylog`, Prop 4.4 at `c = 1/2`, Thm 5.5).  This supersedes the 55% freshness figure below.

## Negative inventory read

- `Maze.lean`: no row on games, winning sets or `U`.  The only `uniform` rows concern Vandehey `BlockForget` and casting out, which are unrelated.
- `STATUS.md`: 10.36 is unconditional (`UniformBad.bugeaud_10_36`), and 10.31 Hertling is at 12% with `blockForcing` as the crux.
- Sweeps 10-02, 10-03, 10-03b, 10-03c.  Sweep 10-03c §1.2 already sketched the cross-route on paper: `Bad_b(C)` is potential winning with `α_b^{1/2} ≍ b^{−C/2}`, giving positive dimension for `C ≈ 50` through Yavicoli's explicit BFS 5.5.  This audit upgrades that sketch to full dimension, the two-sided codimension rate, and the Cantor and BAD intersections.
- `docs/notes/bugeaud-10-36-uniform-bad.md`, and `UniformBad.lean`: the engine `exists_avoid_of_stagePotential` and the guards `not_uniformBad_of_third_le`, `not_uniformBad_largeBases_of_le_one`, `not_isNormal_of_uniformBad`.

## Prior-art searches (query → result)

1. `papers followups 2102.01186` (Falconer–Yavicoli, 17 citers): thickness, patterns, Baker–Bender (ETDS 2026, base-q expansions in (1,2)), Yavicoli–Yu 2503.09528 (finitely many bases, integers).  None treats all integer bases with a uniform constant.
2. `papers followups 0909.4251` (BBFKW, numbers normal to no base; 32 citers).
   - Färm 0904.4365 proves full dimension for countable intersections of non-dense-orbit sets with a per-map distance, not a uniform one.
   - Temur **2609.16362** (14 Sep 2026, answers Bugeaud **10.53**): a computable `ξ` with `‖bᵏξ‖ > δ_b := 154^{−2^b}`, read from the TeX source line 124.  That bound is doubly exponential in `b`, and the paper does not mention 10.36 or games.
   - Lambert–Simmons–Zheng 2512.04236, Huang–Li–Wang 2512.07686, Wu 2609.22016 and Neckrasov–Wu–Yang 2608.24401 cover twisted, β-expansion and weighted settings, not all bases.
3. `papers followups 1703.09015` (BFS potential game, 14 citers): patterns, AP gaps, the matrix potential game.  No base-`b` application.
4. Newest arXiv by author (arxiv.org/search, sorted by date):
   - Yavicoli (22 papers, newest 2609.04456): no base-`b` badly-approximable work after 2503.09528.
   - Bugeaud (newest 2609.29360): 2608.23017 (binary digits of `3ⁿ`) and 2510.02059 (b-ary expansions with irrationality exponent near 2) are not this.
   - Fishman (newest 2601.00401) and Simmons (newest 2608.25349, Ψ-rapid game for well ∩ badly approximable): neither touches this.
   - The arXiv export API was rate-limited ("Rate exceeded") for author queries, so the HTML search was used instead.
5. Web searches, each returning nothing on the uniform-in-`b` set:
   - `"absolutely winning" badly approximable "every base" "b^{-c}"` (only BAD / HAW papers);
   - `Färm "Simultaneously non-dense orbits"`;
   - `Bugeaud problem 10.36 "every base" … solved`;
   - `"potential game" "every integer base" OR "all integer bases" …`;
   - `Akhunzhanov "badly approximable" "every integer b" … Hausdorff`;
   - `"uniformly badly approximable" "integer bases" OR "all bases" … winning`;
   - `"Bugeaud" "Problem 10.36" OR "Problem 10.31" … 2025 2026 arXiv`, which gave Chen–Ye–Zheng 2604.14036 (linear recurrences; generalizes Flatto–Lagarias–Pollington–Dubickas, not this).
6. Moshchevitin, *On some open problems in Diophantine approximation*, arXiv:1202.4539 v3: the text was grepped for Akhunzhanov, "all bases", `b^n` and "lacunary".  §1.5 discusses Furstenberg's ×2×3 sequence and Peres–Schlag, not uniform-in-`b` constants.
7. BFS TeX (arXiv:1703.09015) read for the exact statements cited below.

**Folklore-risk settlement (Falconer–Yavicoli).**  F–Y would give 10.36 *existence* from a thickness bound `τ(E_b(C)) ≳ b^C`.  That bound is unproved in print, and F–Y say nothing about dimension or Cantor intersections.  The dimension statements here come from the potential game, not thickness, so F–Y is not prior art for them.  The real risk is that an expert in potential games sees the early-charging count as an exercise.  That is the 55% above.

## Cited inputs (referee needed before any outward use)

| Prop | Source | Faithfulness note |
|---|---|---|
| `Literature.BFSPotentialDim J δ`, instances `BFSDimInterval` (`[0,1]`, δ = 1) and `BFSDimCantor` (`C₃`, δ = log 2/log 3) | Broderick–Fishman–Simmons, Acta Arith. 188 (2019) 289–316, arXiv:1703.09015, **Thm 5.5** (`theorempotentialHD`) | `X = ℝ`, `H` = singletons, `η = δ` by their Example 5.2 (Ahlfors δ-regular ⟹ absolutely (δ, singletons)-decaying).  Their `dim_A` (Ahlfors dimension) is ≤ `dim_H`, so the `dim_H` form is weaker.  The referee should check two things.  (a) Theorem numbering in the published version (the arXiv counter gives 5.5; sweep 10-03c also called it "BFS Thm 5.5").  (b) That `[0,1]` Lebesgue and the Cantor measure satisfy "Ahlfors regular for sufficiently small balls centered in the support". |
| `Literature.BFSBadPotential` | BFS **Lemma 3.11** (print; arXiv v3: 3.10) + **Remark 4.2** + **Prop 4.5** | Lemma 3.11 is absolute winning with `(α,β,ρ) = (2ε/((1−2ε)β), β, β/2)`.  Remark 4.2 says the proofs show `c = 0` potential winning, and one deletion of radius ≤ αρ meets every `c > 0` budget.  The referee should check that the composite reading is faithful. |

The intersection property (BFS Prop 4.4) is **proved** for two sets (`PotentialWinning.inter`), and so are monotonicity in the set, in `α` and in `ρ`.

The definition `PotentialWinning` follows BFS Def. 4.1 for `X = ℝ` and `H` = singletons.  It departs in two places:

- It models only `c > 0`.
- Alice's legality is required only on histories whose last radius is positive.  Legal Bob play with `ρ, β > 0` always has positive radii.

## Difficulty check

- **Proved implications:** all of item 3, from headline 1 (as the hypothesis `EPotentialWinning`), headline 2, and the cited Props.  Checked with `#print axioms`: `dimH_U_eq_one_of`, `le_dimH_U_inter_Bad_inter_cantor_of`, both guards and `PotentialWinning.inter` use only the standard axioms.  `codim_E_asymp` uses `sorryAx`, through headline 2 only.
- **Unproved premise:** headline 1, with headline 2 as a routine count.
- **Mechanism for headline 1:** early charging against Bob.
  - Obstacle `N(a/bⁿ, b^{−C−n})` is charged on the first turn with `ρ_k ≤ b^{−n}`.
  - At most 4 centres of one level meet `B_k`, since they are `b^{−n} ≥ ρ_k` apart and obstacles are shorter than `b^{−n}/8`.
  - At most `1 + log_b(1/β)` levels per base land on one turn, each with radius `< b^{−C}ρ_k/β`.
  - So the `√`-budget is `≍ Σ_b b^{−C/2} ≍ 2^{−C/2}`, giving `α ≍ 2^{−C}`.
  - Turn 0, and the first turn with `ρ_k ≤ 1`, cost a constant depending on `ρ` and `β`.
  - Win: an obstacle containing the outcome meets every `B_k`, and is charged once `ρ_k ≤ b^{−n}`, which happens because `ρ_k → 0`.
- **Known-false siblings (kernel):**
  - `not_potentialWinning_E_small`: one fixed `C` is not winning at small scales, because `E C` misses `(−2^{−C}, 2^{−C})` (`E_disjoint_gap`).  So the union over `C` is essential.  Sorry-free given BFS 5.5.
  - `not_potentialWinning_isNormal`: no set of base-`b` normal numbers is potential winning for all `α`.  This is E1's guard, and shows no game argument proves normality.  Sorry-free given headline 1 as a hypothesis and BFS 5.5.
  - Exponent ≤ 1 fails even for large bases (`UniformBad.not_uniformBad_largeBases_of_le_one`).  The mechanism needs `Σ_b b^{−Cc} < ∞` with `c < 1`, hence `C > 1`, so it agrees.
- **Why the old method stalled:** classical Schmidt games (Akhunzhanov, BBFKW) charge each base at its own scale, and the countable intersection forces `α_b` to decay, so the constants become `b`-exponential.  The potential game charges early and sums budgets in `ℓ^{1/2}`, and `Σ_b b^{−C/2}` converges.

## Not adopted

- **Absolute winning of `U`.**  It would follow from FSU Memoirs Thm C.8 (`U` is `(α,β,c,ρ)`-potential winning for every `c > 0`), but needs a formal absolute game and FSU Assumption C.6.  The dimension consequences already come from BFS 5.5, so C.8 adds only C¹-invariance and intersection with other absolute-winning sets.  Possible follow-up.
- **The optimal exponent `c* = inf{C : E C ≠ ∅} ∈ [log₂ 3, 24]`.**  There is no evidence for a conjectured value, so no statement was frozen.
- **Hertling 10.31 `R` side.**  Games cannot force disjunctivity, because Alice cannot steer Bob.  That remains the `blockForcing` engine question.

## Next laps

1. `potentialWinning_E`: write the strategy (a positional function of `ρ_k`, `ρ_{k−1}`), reuse `UniformBad.encard_stage_meet_le`-style counting for the ≤ 4 centres, and bound the tsum as in `newPotential_le`.
2. `dimH_E₂_le`: run-length count `a_N ≤ 2μ^N` and a dyadic cover.
3. Stretch only after 1.
