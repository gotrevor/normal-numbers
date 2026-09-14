# HANDOFF — entropy lap 37 (DEEP REFLECTION + rungs 1 & 2), 2026-09-14, Opus

**Branch** `wip/g4-entropy`.  **HEAD** `68f7ca2`.  Working tree **clean**.  `lake build` 🟢
**8972 jobs**.  Both new modules sorry-free and `#print axioms`-clean (trust triple only).
No pre-expedition file edited; `entropy_E0`/`entropy_E1`, `isDisjunctive_four/two/base`,
`primeSumAtBase_eq_primeLambertAtBase` untouched.

## 0. The lap in one line

Reflection: **normality of `G₄` is closed on this mechanism, by theorem and quantitatively**; new
objective set (the joint `t`-wise frequency theorem); rungs 1 and 2 of it both landed.

## 1. What was proved / refuted / narrowed

### Reflection (commit `f5d94e2`) — ROUTE VERDICT **CONTINUE**

E-T3/E-T4/E-T5 checked against git + the modules; **none fired**.  Laps 23–36 each closed a named
whole theorem, so no false summit.  The real defect: the lap-23 objective was **met at lap 31**
and laps 32–36 then ran five laps objective-less → new trigger **E-T7**.

Mathematical finding, now in `STATUS.md`, `DIRECTION.md`, `REFLECTION-2026-09-14-entropy.md` and
`papers/literature-review.md`'s new entropy chapter:

* `qForces_normal_iff_density_one` needs density **one**; `sum_weight_le` gives every admissible
  family over every scale `≤ 1/8`.
* `key_size`'s own slack (`Q·D₀ ≥ K·B^{2K}` vs `H_K·m_K ≤ (2(K²+1))^K·K`) ⟹ sampled density
  `≤ ½(3/K⁴)^K`; `entropy_cover_bound` pins the window at exactly `m_K = K/4` (needs both
  `m ≤ K/4` and `η⁴ ≤ 2^{−K}`).  Gap `≈ K^{4K}`.
* Cause: `GridParams.hQdvd : ∀ m ≤ U, m ∣ Q` ⟹ `Q ≥ lcm(1,…,U)`, `U ≥ B^K`.
* **Three escapes re-costed and each closed by an existing theorem — do NOT re-derive them**
  (reflection §1): varied frozen residue; shifting the real `x ↦ 2^σ x`; more scales.

### Rung 1 (commit `600bd36`) — `G4EntropyPosition.lean`

```
posAt_blockVal                              the general-`p` digit dictionary (p + ℓ ≤ m)
Sched.posFreq / abs_posFreq_sub_le_of_deficit
Sched.abs_posFreq_sub_le_primeLambertFour   ≤ 2√(400 log2·ℓ/√K)  for 2ℓ ≤ m_K
Sched.tendsto_posFreq_growing               every ℓ(K) = o(√K)
Sched.posFreq_eq_count / posFreq_eq_digits
Sched.tendsto_occursCountP_primeLambertFour
  #{(n,α,p) : OccursAt 2 G₄ v (2·kIdx(n,α)+p)} / (|P_K|·|Atom_K|·(m_K−|v|+1)) → 2^{−|v|}
```
**Every** position of the sampled windows, not the `1/ℓ` aligned fraction lap 31 counted.

### Rung 2 (commits `8b5582d`, `68f7ca2`) — `G4EntropyJoint.lean`

**E-T6 does not fire, and the answer beats the directive's guess: the deficit is NOT multiplied
by `t`.**
```
sum_patCoord_deficit_le    ∑_{b,j} (ℓt − H₂(patCoord b j)) ≤ Δ        -- the SAME Δ, zero slack
abs_avg_patCoord_prob_opt  |avg Pr[pattern] − 2^{−ℓt}| ≤ 2√(log2·ℓ·Δ/(|B|·m))
```
plus `packFin`, `patCoord`, `patRem`, `leftCoord`, `jointFam`, `jointFam_injective`,
`H₂_map_patRem_le`, `H₂_map_leftCoord_le`, `FinLaw.H₂_map_const_le`, `abs_avg_patCoord_prob_le`.
With `Δ = δ|A|` and `|B| ≈ |A|/t` the bound is `2√(log2·tℓδ/m)` — the `t = 1` bound with
`ℓ ↦ tℓ`: pinning `t` words at once costs exactly those words' bits and nothing more.

## 2. Which bottleneck moved

The objective moved (reflection lap 37, `DIRECTION.md` CURRENT DIRECTIVE): the **joint (`t`-wise)
sampled-word frequency theorem**, i.e. the sampled windows of `G₄` **decorrelate**.  Rung 1
(`t = 1`, all positions) and rung 2 (the abstract `t`-wise bound) are both done.

## 3. The next bounded test — rung 3 (scoped in `PENDING_WORK.md`'s ACTIVE section)

⚠️ **Design correction found while scoping, do this first**: `leftCoord`'s hypothesis `m ≤ ℓ*t`
**fails at the schedule** for fixed `ℓ, t` (`m_K = K/4 → ∞`).  Fix before instantiating: let all
three families land in `Fin (2^(ℓ*t + m))` (`patCoord`/`patRem` cast up, `leftCoord` casts `z α`
up); the bits bounds are unchanged and the hypothesis disappears.

Then:
1. the blocking at the schedule — `fun b s => (Fintype.equivFin _).symm ⟨b*t+s, _⟩`, injective by
   uniqueness of division;
2. `Sched.patFreq` + `abs_patFreq_sub_le_of_deficit` / `…_primeLambertFour`;
3. digit rendering → `tendsto_occursCountJoint_primeLambertFour`: the event is
   `∀ s < t, OccursAt 2 G₄ (v s) (2·kIdx(n, blk b s) + jℓ)`; `posAt_blockVal` and
   `blockVal_eq_wordVal_iff` are already general enough, the only new step is unpacking `packFin`
   into the `t` component events.

Bounded secondary, only on an E-T3 stall: **measure the wall** — `Sched.density_le_pow`
(`≤ ½(3/K⁴)^K`) and `Sched.window_needed_ge` (density `≥ 1/2` needs `mm ≥ K^{4K}·m_K`).

## 4. Lean notes harvested this lap (all verified)

- `abs_posAvg_sub_le` needs `[Nonempty A]`; `instNonemptyAtomAt i := ⟨fun _ => 0⟩` supplies it.
- `em` is ambiguous (`_root_.em` vs `Classical.em`); when a rendering lemma needs `ℓ ≤ kk i`, use
  `Tendsto.congr'` + `filter_upwards [eventually_ge_atTop v.length]` (`kk i = 40000 + i`).
- `Finset.filter_card_add_filter_neg_card_eq_card` → **`Finset.card_filter_add_card_filter_not`**.
- `Nat.pos_pow_of_pos` → `Nat.pow_pos`, and it takes ONE explicit arg (`Nat.pow_pos h`).
- `rw [if_neg h] at hc` rewrites only the first `if`; use `simp only [if_neg h] at hc` when both
  sides carry one.
- `(Fin t → Fin (2^ℓ)) ≃ Fin (2^(ℓ*t))` is
  `finFunctionFinEquiv.trans (finCongr (pow_mul 2 ℓ t).symm)`.
- To bound `H₂` of a packed tuple law, `FinLaw.H₂_map_congr_comp L _ (packFin t ℓ).injective _
  (fun _ => rfl)` strips the packing without ever unifying two `FinLaw.map`s.
- `nlinarith` wanted the scaled hypothesis explicitly:
  `mul_le_mul_of_nonneg_left hhalf (by positivity : 0 ≤ 400 * Real.log 2 * ℓ)`.
