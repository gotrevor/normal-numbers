# HANDOFF 2026-09-22 — Pair A multicutoff formalisation (laps 0–6 done: THEOREM A)

Branch `wip/g5-prime-subset`.  Running `KICKOFF-2026-09-22-multicutoff-lean.md` under the
2026-09-22 17:12 EDT attended override.  New modules only; no existing statement touched;
`PrimeModelBrunLower.lean` untouched.

## Landed (all sorry-free, `lake build` green, headlines `#print axioms` clean)

### Lap 0 — `src/NormalNumbers/PrimeModelSqrtFresh.lean`
- `SqrtFreshMassZero P` (Astra 11.1).
- `recipSumIoc_mono_left`, `recipSumIoc_split_le`, `recipSumIoc_of_le` (elementary).
- `recipSumIoc_le_rootChain_pow` : `M ≤ y^(2^K) → S_P(y,M) ≤ ρK` (integer induction).
- `recipSumIoc_le_rootChain` : **Astra 11.3**, `S_P(y,M) ≤ ρ ⌈log(log M/log y)/log 2⌉`.
- `sqrtFreshMassZero_of_freshMassZero`, `sqrtFreshMassZero_of_relDensityZero`.

Deviations from the paper (both simplifications, no loss):
- `recipSumIoc_split_le` is subadditive across **any** intermediate point, so the chain
  induction needs no ordering hypotheses and Astra's remark "the final overshoot below `y`
  is harmless" is automatic.
- For §11.4's relative-density leg the Mertens ratio is bounded unconditionally:
  `N ≤ (Nat.sqrt N)^3` for all `N ≥ 4` (from `N < (s+1)^2` and `s+2 ≤ s^2`), so
  `log N / log ⌊√N⌋ ≤ 3` and the constant is `δ(9 + 12 log 3)`, no eventual-`N` fudging.

### Lap 1 — `src/NormalNumbers/PrimeModelBlockSieve.lean` (pure combinatorics)
- `bonfPartial`, `bonfIndic`; `bonfPartial_succ` = the Bonferroni pair identity
  `∑_{i≤r}(−1)^i C(b+1,i) = (−1)^r C(b,r)`.
- `bonfIndic_le_bonfPartial` (`U ≥ I ≥ 0`), `bonfPartial_sub_le` (`U − D ≤ I`), even `r`.
- `prod_sub_prod_le`, `prod_le_prod_of_defect` : the telescoping minorant, over an arbitrary
  strict ordered commutative ring (needed so the ℤ-valued pointwise form reuses them).
- `sum_powersetCard_prod` : for a 0/1 weight, degree-`i` esym sum `= C(b,i)`.
- `bonfPoly_eq`, `defectPoly_eq`, `blockMinorant_le` = **Lemma B property 2, pointwise**.
- `sum_powerset_union_disjoint`, `prod_sum_powerset_disjoint` = **the coefficient rule**.

Deviation: the paper proves `λ(E) ∈ {−1,0,1}` by a three-case analysis on the block profile
plus a disjoint-supports argument.  `prod_sum_powerset_disjoint` shows
`λ(E) = ∏_i c_i(E ∩ B_i)` **by construction**, so `|λ| ≤ 1` and the support/level conditions
are inherited factor-by-factor.  The case analysis is never needed.

### Lap 2 — `src/NormalNumbers/PrimeModelBlockSieveModel.lean`
- `model_defect` : `E[L] ≥ (∏V)(1 − (∑D̄)e^{∑D̄})` from `V_i ≤ E[U_i] ≤ V_i(1+D̄_i)`.
  No division anywhere (`Finset.mul_prod_erase` instead of `∏_{j≠i}V_j = ∏V/V_i`).
- `exp_neg_two_mul_le_one_sub` : `e^{−2t} ≤ 1−t` on `[0,1/2]`, via `1/(1−t) ≤ 1+2t ≤ e^{2t}`.
- `esymmOn`, `esymmOn_insert` (Pascal recursion), `add_pow_ge_two_terms`,
  `factorial_mul_esymmOn_le` : **`k! e_k(g) ≤ (∑g)^k`**.  Not in mathlib (only the algebraic
  `MvPolynomial.esymm` theory exists).  Proved by induction on the block with `∀ k` in the
  motive, which avoids the usual double-counting `(k+1)e_{k+1} = ∑_p g_p e_k(B∖p)`.
- `pow_self_le_factorial_mul_exp` : `n^n ≤ n! e^n`.  `exp_one_div_eight_le` : `e/8 ≤ e^{−1}`.
- `block_defect_le` : **`e_{r+1}(g) ≤ e^{−u−l−2} ∏(1−g)`** for `r = 64d+2u+2l+4`,
  `g ≤ 1/2`, block mass `≤ 8d`.
- `geom_sum_le_inv_one_sub`, `sum_block_defect_le` (`∑_j∑_l e^{−u_j−l−2} ≤ 0.215 ∑_j e^{−u_j}`),
  `eta_bound` (`S e^S ≤ 0.3T`), `model_defect_eta` = **Lemma B property 3**, packaged:
  `E[L] ≥ (1 − 0.3T) ∏V` with `T = ∑_j e^{−u_j} ≤ 1`.

Deviations in the defect chain (both simplifications):
- Feeding `λ ≤ n/8` (equivalent to `λ ≤ 8d` given `n ≥ 64d`) into the factorial bound removes
  `d` from the exponent algebra entirely: `λ^n/n! ≤ (n/8)^n e^n/n^n = (e/8)^n`.
- `e/8 ≤ e^{−1}` replaces the paper's `e < 4` **and** `log 2 ≥ 1/2` pair; the remaining numeric
  step is the integer inequality `64d+2u+2l+5 ≥ 16d+u+l+2`.


### Lap 3 — `src/NormalNumbers/PrimeModelBlockLevel.lean`
- `prod_le_of_block_bounds` : `|E ∩ B_i| ≤ m_i`, `B_i` topped by `w_i ≥ 1` ⟹
  `∏_{p∈E} p ≤ ∏_i w_i^{m_i}`.
- `sum_half_pow`, `sum_mul_half_pow` : exact finite identities
  `∑_{l<L}2^{−l} = 2 − 2·2^{−L}`, `∑_{l<L} l 2^{−l} = 2 − (2L+2)2^{−L}`.
- `level_sum_le` : `∑_{l<L}(64d+2u+2l+5)2^{−l} ≤ 128 d + 4u + 14`.

Deviation: Fable derives `128d+4u+12` and then adds a separate `log y₁` for the defect block's
extra prime.  Giving **every** block its uniform trace bound `r_i+1` (which is what the
coefficient rule hands you anyway) gives `128d+4u+14` in one geometric sum, no special case.

### Lap 4 — the graded arithmetic sieve
`src/NormalNumbers/PrimeModelRadicalCRTGraded.lean`
- `SieveCondD` (shift `< d p` at each sieve prime, plain `j p < p` at assigned primes),
  `card_sieve_graded`, `radical_sieve_admissible_card_graded` (exactly `∏_{p∈E} d p` classes),
  `radical_sieve_count_graded` (`|count − X ∏d/(Q D e)| ≤ ∏ d`).
  The CRT infrastructure of `PrimeModelRadicalCRT` is uniform in the local counts and is reused
  verbatim; only the local condition and the product of local counts change.

`src/NormalNumbers/PrimeModelBrunCountGraded.lean`
- `SiftedCondD`, `hitUD`, `weighted_counts_le_sifted_graded`,
  `brun_remainder_le_square_graded` (`∑_E |λ E| ∏_{p∈E} d p ≤ R²`, using `d p ≤ p`),
  `main_term_factor_graded`, and
- **`graded_sifted_count_lower`** :
  `#{n<X : SiftedCondD} ≥ X/(Q ∏_A p) · ∑_{E⊆U} λ(E) ∏_{p∈E}(d p/p) − R²`.

  The weights are **abstract** here: the arithmetic needs only (i) minorisation, (ii) `|λ|≤1`,
  (iii) support level `R`.  That is the interface the combinatorial half supplies.

`src/NormalNumbers/PrimeModelBlockWeights.lean` — the explicit weights
- `coefU`, `coefD`, `lamMain`, `lamDef`, **`blockLam`**;
  `sum_powerset_coefU/coefD` (powerset form of `bonfPoly`/`defectPoly`).
- `blockLam_expand` : `∑_{E⊆U} λ(E)∏_{p∈E}x_p = ∏_i U_i − ∑_i D_i ∏_{j≠i} U_j`.
- `blockLam_abs_le_one` (i), `blockLam_support` (iii), `blockLam_minorant` (ii).

  So **Lemma B is proved end to end for one concrete `λ`**.  `blockLam_abs_le_one` goes by the
  trichotomy on the excess set `T = {i : |E∩B_i| > r_i}` (`|T|=0` main term only, `|T|=1` that
  block's defect only, `|T|≥2` everything zero) — this is where Fable's asserted "supports are
  disjoint" is actually discharged.

`src/NormalNumbers/PrimeModelBlockSieveModel.lean` (lap 4d)
- `esymmAlt`, `esymmAlt_empty`, `esymmAlt_insert`
  (`P_{r+1}(insert a B) = P_{r+1}(B) − g_a P_r(B)`), and
- `esymmAlt_bonferroni` : even truncations `≥ ∏(1−g)`, odd truncations `≤`.  Induction on `B`
  with all `r` in the motive and **both parities together** — forced, since the step at one
  parity consumes the IH at the other.  This supplies `model_defect_eta`'s hypotheses
  `V ≤ E[U]` and `E[U] ≤ V(1+D̄)` for the real weights, with **no probability theory**: Fable's
  "product measure, blocks independent" is discharged as algebra on symmetric functions.

## Where the pieces meet

    laps 1,3,4c  →  (minorise, |λ|≤1, level R)  →  graded_sifted_count_lower   [arithmetic]
    laps 2,4d    →  (V ≤ E[U] ≤ V(1+D̄), D̄ ≤ e^{−u−l−2}, ∑D̄ ≤ 0.215T)
                 →  model_defect_eta : ∑_E λ ∏g ≥ (1 − 0.3T) ∏(1−g)          [model]

The only missing link between them is the **ring-generic form of `blockLam_expand`**: it is
currently stated for `x : α → ℤ`, and the model side needs `x = g : α → ℝ`.  `coefU`/`coefD` are
ℤ-valued and `prod_sum_powerset_disjoint` is already stated over an arbitrary commutative ring,
so this is a re-statement with `(blockLam … : ℝ)` casts, not new mathematics.

---

## Lap 6 — **THEOREM A**, the graded finite window bound (all legs proved)

Branch `wip/g5-prime-subset`, HEAD `fdb3652`.  Working tree clean, `lake build` green
(9152 jobs), every headline `[propext, Classical.choice, Quot.sound]`.

| leg | lemma | file |
|---|---|---|
| E1 transfer | `KMT.windowMean_sub_windowMeanLeG_le` | `PrimeModelKMTGraded.lean` |
| E5 contraction (abstract) | `PhaseAlgebra.model_phase_norm_le_graded` | `PrimeModelPhaseAlgebraGraded.lean` |
| factorisation | `PhaseFactor.phase_factorisationG` | `PrimeModelPhaseFactorGraded.lean` |
| E5 in place | `KMT.norm_model_expectation_le_graded` | `PrimeModelKMTGradedModel.lean` |
| E4a/c | `JointLaw.joint_phase_errorG` | `PrimeModelJointLawGraded.lean` |
| **Theorem A** | `KMT.window_bound_graded` | `PrimeModelTheoremA.lean` |
| split at `m ≥ k` | `PhaseFactor.phase_factorisationGM` | `PrimeModelPhaseFactorSplit.lean` |
| E4b (per-atom) | `BlockSieve.empLaw_lower_atom_graded` | `PrimeModelLowerAtomGraded.lean` |

`window_bound_graded` states, for per-site cutoffs `y_j` (decreasing) and per-shift
thresholds `T_j`, with `∃ j₀` the least nontrivial site:

    ‖windowMeanS S k h x‖
      ≤ ∑_j a_j (2 R(y_j,x) + k/x)                                    (E1, a_j = 4π|h|/4^{j+1})
        + (2 ∑_j e^20/T_j^{1/(2 log Y)} + 2η + 2 Q (∏_j ⌊T_j⌋) R²/x)   (E4)
        + e^{2k} exp(−∑_{p ∈ P, p ≤ y_{j₀}} 1/p).                      (E5)

Structural facts proved, not assumed:
- `PhaseAlgebra.prefixA_eq_zero_of` — tiers above `j₀` contribute the factor `1` exactly, so
  the schedule above the least nontrivial site is free (Fable §2's key claim).
- `PhaseFactor.exists_prefix_count` — for a decreasing schedule the set of sites that see a
  prime is an initial segment, so the per-prime defect really is a *prefix* defect `A_{d_p}`.
- `BlockSieve.empLaw_lower_atom_graded` — the E4b hypothesis is discharged from
  `graded_brun_lower`; `PrimeModelBrunLower.lean` is untouched, as the kickoff requires.

### Deviations recorded this lap (both conservative, both in module docstrings)
1. `joint_phase_errorG`: the shift-`j` Markov moment runs over the full prime range `≤ Y`
   rather than `≤ y_j`.  The formalised radical model (`Radical.weight`) assigns every prime to
   every shift with probability `1/p`, so a shift-dependent prime family would be needed for the
   paper's sharper E4a.  The per-shift lever Theorem C′ uses — the threshold `T_j` — is kept in
   full.  Nothing downstream needs the sharper form.
2. E5 keeps the ungraded constant `e^{2k}` (from `p > k`, `∑ 1/p² ≤ 1/k`) where Fable §2 writes
   `e^{k}` (from `p > 2k`).  Same asymptotics; the `2k` split is available via
   `phase_factorisationGM` if the sharper constant is ever wanted.

## Next, in order — **SUPERSEDED 2026-09-22 by the review lap.  Do not follow item 1.**

The original item 1 ("feed `empLaw_lower_atom_graded` into `window_bound_graded`'s `hlower` with
one tier `κ = Unit`, `UU () = stateU P s`, `yy () = Y`") is **refuted**.  See
`DIRECTION.md` → CURRENT DIRECTIVE and `PENDING_WORK.md` top for the two-line refutation and the
G1–G5 decomposition that replaces it.  Item 2 (lap 7, Theorem C′) is unchanged and is still the
target; it is now reached through G1–G5 rather than through the constant class count.

---

# Lap 7 opening — REVIEW + the graded-state regrade (G1–G3 landed)

Branch `wip/g5-prime-subset`, HEAD `415acfb`.  Working tree clean, `lake build` 🟢 **9155 jobs**.
`src/` holds exactly the two pre-existing off-campaign `sorry`s
(`PrimeLambertOscillation.phaseOscillation`, `MahlerDriftOne.exists_prime_nonresidue`) — the
multicutoff campaign is sorry-free.

## The review lap's finding (commit `a11e006`)

Closing Theorem A's `hlower` at the **constant** class count `dpK k` cannot reach Theorem C′.
Two independent walls:

1. **Brun support level.**  `graded_brun_lower`'s `hdpj : ∀ j, ∀ p ∈ U j, dp p ≤ d j` forces
   `d_j ≥ k` in *every* tier, including the top one, which carries the largest `log y`.  So
   `log R ≥ 128 k log y₀`; `R² ≤ x^{1-δ}` pins `a := log y₀/log N ≤ 1/(2048 J)`; the root chain
   (Astra 11.3) at `y₀` then costs `≥ 11 + log₂ J`, and the transfer term is `≍ ρ_N log J`.
   `TailOK` pins `J ≍ min(L₃N, S_N/8)` — `J` cannot be capped without breaking the tail — so this
   is `ρ_N · L₄N`, which `ρ_N → 0` does **not** control.
2. **E4a Markov range.**  Lap 6e's recorded "harmless" deviation (moment over the full range
   `≤ Y`) gives `∑_{j<J} e^{20}/T_j^{1/(2 log Y)}`; since `log T_j / log Y → 0` as `j` grows, the
   terms tend to `e^{20}` and the sum diverges like `J e^{20}`.  `∑_j log T_j ≤ ½ log N` (the CRT
   remainder) cannot rescue it.

Both vanish exactly when the class count and the Markov range are **graded by band**, as Astra
§4/§8 has them.  The arithmetic half needs no change: `graded_brun_lower` already takes an
arbitrary `dp : ℕ → ℕ`.

Two structural facts keep the regrade cheap — both now machine-checked:

* the graded model is the pushforward of the ungraded one **with the same model expectation**
  (`Radical.radical_phase_productG_eq`), because `zSee p j = 1` above the cutoff.  So leg E5 and
  the whole phase algebra transfer **verbatim**;
* the graded law lives on the **same** state type `ι → Option (Fin k)` with dead shifts zeroed,
  so `sum_pi_prod`, `retainedBox_card_le` and `retainedBoxG_card_le` are reused verbatim.

## Landed this lap (all sorry-free, all headlines `[propext, Classical.choice, Quot.sound]`)

| leaf | file | headline |
|---|---|---|
| review | `DIRECTION.md`, `PENDING_WORK.md`, `STATUS.md` | CURRENT DIRECTIVE + G1–G5 + axiom ledger (`a11e006`) |
| **G1** | `PrimeModelRadicalGraded.lean` | `radical_site_momentG`, `radical_phase_productG_eq` (`6ba7df3`) |
| **G2** | `PrimeModelRadicalTailGraded.lean` | `radical_box_tailGG_exp20` (`9d38e11`) |
| **G3** | `PrimeModelJointGraded.lean` | `actual_stateG_sifted_iff`, `state_model_densityG`, `empLawG_lower_atom` (`415acfb`) |

* **G1** — `localWeightG k d q` gives a prime only its own `d` of the `k` shifts.
  `radical_site_momentG` : the shift-`j₀` moment is `∏_{i : j₀ < d_i}(1 + q_i(t_i−1))`, the
  product running **only over the primes that site sees**.  Plus `radical_mass_oneG`,
  `weightG_nonneg`, `radical_mult_productG`, `radical_phase_productG` and the prime forms.
  `d ≤ k` is needed exactly once, for `localWeightG_sum`.
* **G2** — closes wall 2.  `radical_box_tailGG_exp20` reaches the sharp exponent
  `1/(2 log y_j)` and needs only `p i ≤ y_j` for site `j`'s **own** primes, not a single `Y`
  dominating the family (Astra (8.4)).  The budget is discharged by `radical_moment_budget` on
  the *subtype* of live primes (`Finset.sum_subtype` bridges), so no Finset-indexed restatement
  of the Mertens budget was needed.
* **G3** — closes wall 1.  `truncState`/`IsGraded`/`actualStateG`; `actual_stateG_sifted_iff` and
  `state_model_densityG` (graded twins of the two `RadicalState` headlines); `empLawG`,
  `jointModelG` with mass one, nonnegativity, graded box tail; and `empLawG_lower_atom`, the
  per-atom estimate at a band-dependent `dp`.  Two hypotheses came out cleaner than in the
  constant-count version: `2 · dp p ≤ p` is a hypothesis on `dp` (so the prime set needs only
  `k < q` here; the caller still supplies the `2k` clip when building `dp`), and `hkdd` is gone.

## Next, in order (G4, then G5)

1. **G4** `PrimeModelTheoremAGraded.lean` — Theorem A on the graded state, with no `hlower`:
   * `statePhaseG S k y Y h (truncState k dp P s) = statePhaseG S k y Y h s`, where
     `dp q = #{j : q ≤ y_j}` (use `PhaseFactor.exists_prefix_count`, which already gives that the
     seen-set is an initial segment).  `zSee k y h q j = 1` for `q > y_j`, so the truncated
     assignments contribute the factor `1` — this is the empirical-side transfer identity.
   * hence `windowMeanLeG = ∑_g empLawG(g) · testFG(g)` (rewrite the fibres of
     `windowMeanLeG_eq_sum` through `actualStateG`).
   * model side: `∑_g jointModelG(g) testFG(g) = ∑_t jointModel(t) testFG(t)` — both equal
     `((∑_r residuePhase)/Q) · ∏_p (1 + A_{d_p}/p)`; G1's `radical_phase_productG_eq` is the
     lemma, applied with `z i = zSee k y h (i : ℕ)`.  **So `norm_model_expectation_le_graded`
     (leg E5) is reused as it stands.**
   * graded E4: `finite_phase_of_lower_atoms` is already generic in the index Finset, so
     `joint_phase_errorG`'s proof carries over with `empLawG`/`jointModelG`/`radical_box_tailGG_exp20`
     in place of the ungraded three.
2. **G5** `PrimeModelFamilyGraded.lean` — lap 7, Theorem C′.  Schedule (Astra §8/§11):
   `Z_N = ⌈exp √(log N)⌉`, `ρ_N = sup_{q ≥ Z_N} r_P(q)`, `u_N = ⌊min(√w, ρ_N^{-1/2})⌋`,
   `J = min(⌊w⌋, ⌊S_N/8⌋)`, `y_j = ⌊N^{u^{-2} 2^{-j}}⌋`, `T_j = N^{2^{-j/2}/16}`; tiers
   `UU b = P ∩ (y_b, y_{b-1}]`, `yy b = y_{b-1}`, `dd b = b` (each band is exactly ONE dyadic
   block, `cut yy b 1 = y_{b-1}^{1/2}`, so the upper tiers' `l ≥ 1` blocks are empty and `L` is
   set by the bottom tier).  Then `KMT_along` + `TailOK` (`tail_fresh` shape) and the headline
   through `isNormal_subsetLambert_of_KMT_along`.

Nothing in the paper has been refuted.  The only correction is to the *formalisation plan*: lap
6e's E4a deviation and the one-tier `hlower` plan were both recorded as harmless and are not.
