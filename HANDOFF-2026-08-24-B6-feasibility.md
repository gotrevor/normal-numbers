# HANDOFF 2026-08-24 — B6: hdom-free chain limit DONE + per-round feasibility DISCHARGED; remaining = ψ-round wiring + two-stream recursion

**Branch/HEAD**: master @ `3689dd3`, `lake build` green (8757 jobs), working tree
CLEAN. Sole active `src/` `sorry` = the B6 crux `exists_interleaved_affine_witness`
(`CFScheduleA.lean:1726`). Both B5′ headlines re-verified axiom-clean
(trust-triple `[propext, Classical.choice, Quot.sound]`).

This was a REVIEW lap that ratified the `hdom`→uniform-goodness pivot and then
ground directive items **1 (DONE)** and **2's route-decisive core (DONE)**.

## What landed (7 commits `51726d1..3689dd3`, all axiom-clean)
1. `51726d1` — review: retargeted the STALE `CURRENT DIRECTIVE` (was mandating the
   REFUTED `hdom` route) to the hdom-free uniform-goodness route; refreshed STATUS.
2. `2c61e7c` — **`chainTail_dev_prefix_var`** (`CFChainFreq`): recursion core.
   Uniform block prefix-goodness ⇒ every accumulated-tail prefix is good. The
   hdom-free replacement for `cfDiscLt_append_take`.
3. `5fe8f09` — **`chain_cf_digit_freq_tendsto_uniform`** + **`chain_orbit_equidist_uniform`**
   (`CFChainFreq`): the full hdom-free chain limit → `CFOrbitEquidist` payload.
   Hyps needed from the schedule: `hblock` (uniform block prefix-goodness, margin→0)
   + `hslack` (`∑_{i≤k}(C(s₀+i)+(|v|−1)) < ε·|w(s₀+k)|`, the `o(word)` telescoping).
4. `84ac187` — docs: item 1 DONE.
5. `4d1e5c9` — **`exists_uniform_block_param`** + **`exists_uniformly_freq_good_block_steer_len`**
   (`CFScheduleA`): per-round FEASIBILITY discharged. The len-wrapper takes only a
   min-length `L`, picks `m` large with `n₁ = m·⌊√m⌋` (so `m ≪ n₁ ≪ m²`), and
   discharges BOTH budget inequalities. Output shape (this is the interface the
   ψ-round/recursion consumes):
   `∃ u n₁, L≤|u| ∧ u≠[] ∧ (∀a∈u,1≤a) ∧ cfCylinder(wx++u)⊆(c,d) ∧`
   `  n₁²≤|u|·⌊√|u|⌋ ∧`
   `  (∀k≤|u|, ∀v∈F, |dev_v(u.take k)| < δ·k + (4⌊√|u|⌋+2|v|+n₁)) ∧ ∃x∈…`.
   The `∀k` bound is EXACTLY `hblock` shape; `n₁²≤|u|·⌊√|u|⌋` (⇒ `n₁≤|u|^{3/4}`) is
   the `o(|u|)` witness for `hslack`.
6. `3689dd3` — docs.

## NEXT — do NOT rebuild items 1 or the feasibility (they are DONE, axiom-clean)

### Item 2 remaining: wire the len-wrapper into the ψ-round
Copy-extend (NEVER edit) `exists_freq_good_extend_affine_steer` (`CFScheduleA:1600`ish)
into `exists_freq_good_extend_affine_steer_uniform`: identical interval bookkeeping,
but replace each `exists_freq_good_block_steer` call with
`exists_uniformly_freq_good_block_steer_len` (z into image interval `J_z`, x into
`(a,b)∩ψ⁻¹(J_z')`), taking a caller min-length `L`. Emit per stream: (i) the folded
uniform prefix bound, (ii) `n₁,u² ≤ |u|·⌊√|u|⌋`. Nesting/`hinv'` copy verbatim.

### Item 3: two-stream recursion `SchedStateA`/`schedStepA`/`schedA` (mirror `CFSchedule.sched`)
Per round choose `δ_s = 1/(s+1)` (→0 for `hblock` margin), `L_s = |w_s|`
(⇒ geometric growth `|w_{s+1}| ≥ 2|w_s|`). Track `C_s := 4⌊√|u_s|⌋ + 2|v| + n₁,s`.
- `hblock`: from folded bound + `δ_s→0` (pick `s₀` with `1/(s₀+1)<ε`).
- `hslack`: from geometric `|w_s|` — `∑4⌊√|u_i|⌋`, `∑n₁,i` (each `≤|u_i|^{3/4}=o(|w_i|)`
  via the exposed `n₁²≤|u|·⌊√|u|⌋`), `∑2|v|`, `∑(|v|−1)` all `o(word)` (`Filter.Tendsto`).
Feed both streams into `chain_orbit_equidist_uniform` (`CFChainFreq`) → both
`CFOrbitEquidist` → assemble `exists_interleaved_affine_witness`. Limit-gluing toolkit
READY: `eq_of_mem_iInter_Icc`, `cfCylinder_chain_volume_tendsto`,
`irrational_mem_Ioo_of_mem_iInter_cfCylinder`.

## Watch-outs
- ADDITIVE ONLY: never edit the existing `chain_cf_digit_freq_tendsto` /
  `chain_orbit_equidist` / `chainTail_dev_split*` / `exists_freq_good_extend_affine_steer`
  / any B5′-locked decl; copy-extend.
- Re-`#print axioms exists_absolutely_normal_cf_normal_khinchin` after schedule work
  (MUST stay trust-triple).
- `hslack` uses `|w(s₀+k)|` (word BEFORE the last block), NOT `|w(s₀+k+1)|`.
- `chainApp w s = w(s+1).drop|w s|`; the uniform block IS this appended word.
- The prior `HANDOFF-2026-08-24-B6-hdomfree-limit.md` is SUPERSEDED by this one.
