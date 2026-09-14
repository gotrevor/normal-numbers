# HANDOFF — entropy lap 41 (the objective's endpoint, as stated), 2026-09-14, Opus

**Branch** `wip/g4-entropy`.  `lake build` 🟢 **8975 jobs**.  `G4EntropyJointPos.lean`
sorry-free and `#print axioms`-clean (trust triple).  No pre-expedition file edited.

## 0. The lap in one line

The `DIRECTION.md` 🎯 objective is now met **verbatim as stated**: a freely chosen position
`p_s` per window, not the common aligned `jℓ` of rung 3.

## 1. What was proved

On top of lap 40's abstract bound (`abs_avg_patPos_prob_opt`, `H₂_cutTuple_ge`,
`blkAt_cutCoord`):

```
Sched.abs_posPatFreq_sub_le_primeLambertFour
    ≤ 2√(800 log 2 · ℓ t / √K)         whenever 2(max pp + ℓ) ≤ m_K
Sched.tendsto_posPatFreq_primeLambertFour
patPos_eq_pack_iff
Sched.posPatFreq_eq_count / Sched.posPatFreq_eq_digits
Sched.tendsto_occursCountJointPos_primeLambertFour        -- THE ENDPOINT
```

```
 #{(n,b,j) : ∀ s < t, OccursAt 2 G₄ (v s) (2·kIdx(n, blkSched b s) + pp s + jℓ)}
 ──────────────────────────────────────────────────────────────────────────────  →  2^{−ℓt}
                     |P_K| · nblk_K · ⌊(m_K − max pp)/ℓ⌋
```

The constant is the aligned one doubled (`400 → 800`), which is the entire price of the `t`
independent offsets — the deficit itself is untouched, by `H₂_cutTuple_ge`.  `pp = 0` is
`tendsto_occursCountJoint_primeLambertFour`; `t = 1, pp = 0` is
`tendsto_occursCountT_primeLambertFour`.

**Not a normality claim.**  The sampled positions have density `≤ ⅛(2/K⁶)^K` (lap 39).

## 2. Which bottleneck moved

All of the lap-37 directive is now closed: 🎯 (rungs 1–3 at laps 37–38, then the *stated* form
at laps 40–41) and 📌 the wall (lap 39).  Per **E-T7** this lap does not pick its own next
target; the next altitude lap sets one.  The narrowing recorded at lap 40 stands: the uniform
average over ALL position vectors is not reachable by this ledger.

## 3. Lean notes harvested this lap

- `exact_mod_cast` will not reorder a product: state the real-side hypothesis in the same
  orientation as the `ℕ` one (`2 * ↑R ≤ ↑(kk i)`, not `↑R * 2 ≤ …`).
- `nlinarith` will not multiply a hypothesis by a *triple* product of atoms; supply
  `mul_le_mul_of_nonneg_left h (by positivity : 0 ≤ c₁*c₂*c₃)` explicitly, and clear the
  `√K·√K` with `linear_combination (…) * hsq` first.
