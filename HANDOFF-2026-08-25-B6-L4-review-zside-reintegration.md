# HANDOFF — 2026-08-25 — B6 L4 REVIEW LAP: crux proved, direction re-pointed at z-side re-integration

**Branch:** `master`  **Build:** 🟢 8757 jobs, clean tree.
**Headlines:** both B5′ (`exists_absolutely_normal_cf_normal` Tier 1, `..._khinchin`
Tier 2) = trust-triple `[propext, Classical.choice, Quot.sound]` — **DONE**.
`exists_cfNormal_and_affine_cfNormal` (B6) = `+ sorryAx`.
**Sole open `src/` sorry:** the DEAD two-stream `schedA_block_linear`
(`CFScheduleA.lean:4823`), excised once the L4 z-side lands.

## What this lap did (review lap + 2 additive commits)

1. **Review / direction refresh.** Ground-truthed by real `#print axioms`. Found the
   prior CURRENT DIRECTIVE STALE: its mandated crux `schedL4_block_linear` is PROVED
   (`030d8fb`) and its step-4 "z-side = REUSE" is REFUTED (`b178653`). Rewrote the
   CURRENT DIRECTIVE (DIRECTION.md) + refreshed STATUS.md to mandate **z-side
   re-integration, hardest-first = force `ψ(xA)` irrational**.
2. **`affineMap_irrational_of_iInter_avoids`** (additive) — reduces `ψ(xA)`
   irrationality to a schedule avoidance property: if `xA ∈ cfCylinder(w s) ∀s` and the
   chain diagonalises against `ψ⁻¹(ℚ)` (every `t` with `ψ t ∈ ℚ` is excluded by some
   stage's cylinder), then `ψ(xA)` irrational. Trivial once stated; it is the target
   the schedule must satisfy.
3. **`cfK_snoc_le_exp_ratebump`** (additive) — the route-decisive cfK check for the
   filler digit: `cfK(u++[a]) ≤ e^{(κ+log2)|u++[a]|}` for `a∈{1,2}`, `|u|≥1`,
   `cfK u ≤ e^{κ|u|}`. Needed because `schedKappaL4` is unconstrained so the same-rate
   bound `4≤e^κ` is NOT available — the rate-bump `κ→κ+log2` is.

## Design settled this lap (READ before wiring)

- **`ψ(xA)` must be forced irrational** (subtlety 1): rational `ψ(xA)` has a finite CF ⇒
  no equidistribution. `xA = ⋂ cfCylinder(wxSeq_L4 s)` is a SINGLE point, so the SCHEDULE
  must steer it off the countable null `ψ⁻¹(ℚ)` (`countable_preimage_affineMap_range_rat`).
- **Mechanism = append ONE diagonalisation filler digit per stage.** In
  `schedStepL4_exists`, after the freq-good block `u`, append `[a_s]` via
  `exists_digit_cfCylinder_notMem (S.wx++u) (enum s)` where `enum : ℕ → ℝ` enumerates
  `ψ⁻¹(ℚ)` (`Set.Countable.exists_eq_range`; nonempty as `ψ⁻¹(0)∋-r/q`). New block =
  `u ++ [a_s]`. Record conjunct `enum s ∉ cfCylinder S'.wx` (append at END of StepSpecL4
  so `wxSeq_L4_length_ge`'s trailing `-` still clumps).
- **KEEP the freq-good block `u` on the FULL hull `(a,b)`** — target-shrink is RULED OUT:
  `schedL4_block_linear` feeds `hIcc : cfCylinder S.wx ⊆ Icc a b` to
  `gaussMeasure_middle_half_hull_ge` for `¼γwx ≤ γtar` (the whole point of route B). A
  shrunk target breaks that balance.
- **Ripple of the +1 digit `blk = u++[a]` (all pieces validated this lap):**
  - `hlen` (`S.wx.length ≤ blk.length`): survives (blk longer). `wxSeq_L4_length_ge` OK.
  - `hword` (`blk.length = n₁+m²`): becomes `= n₁+m²+1`. `schedL4_block_linear` uses
    `block_len_le hword hn₁sq` (→ `≤2m²+7`); needs a `+1` variant (→ `≤2m²+8`) — trivial
    constant bump in the final linear bound.
  - `hn₁sq` (`n₁² ≤ blk.length·√blk.length`): survives (monotone in blk.length).
  - `hfreq`: at the LAST index `k=|blk|`, appending one digit shifts the count by ≤ `|v|`
    (`countOccurrences_append_le` + `count v [a] ≤ 1`) and the window by `γv ≤ 1`, so the
    slack must grow by a **constant-in-s `|v|`**: `4√+2|v|+n₁ → 4√+3|v|+n₁`. This CANNOT
    fold into `n₁` (breaks `hn₁sq` for large blocks) — it must go into the `L`-slot of
    `chain_slack_littleO`. ⇒ **generalise `chain_hfreq_of_uniform_blocks`** (`:4850`):
    bump its `hgood` slack `2*v.length → 3*v.length`, set `C` to match, pass
    `L := 3*v.length` to `chain_slack_littleO` (`:4903`). Then wrap the 2 DEAD callers
    `schedA_hfreq_x/z` (`:4918`,`:4931`) with `lt_of_lt_of_le _ (by ... )` (old `2|v|`
    bound ⇒ new `3|v|` bound; `v.length ≥ 0`).
  - `hcfKb` (`cfK blk ≤ e^{κ|blk|}`): use `cfK_snoc_le_exp_ratebump` ⇒ rate `κ+log2` for
    the block. Then `cfK_wxSeq_L4_le` (`:4398`) accumulates to rate `(κ+log2)+log2 =
    κ+2log2`; update its statement + `schedL4_block_linear`'s Nfib consumption (bigger
    rate = bigger linear constant, no structural change).

## NEXT (hardest-first) — finish DIRECTION step 1

1. **Generalise `chain_hfreq_of_uniform_blocks`** slack `2|v|→3|v|` (+ wrap the 2 dead
   callers). Small, isolated; do FIRST + commit.
2. **Rebuild `StepSpecL4` + `schedStepL4_exists`**: append `[a_s]`, add the `enum s ∉
   cfCylinder S'.wx` conjunct, re-prove `hword`(+1)/`hfreq`(+|v|, via count lemmas)/
   `hcfKb`(rate-bump helper). Fix the 4 consumers (`schedL4_block_linear`,
   `schedL4_hfreq_x`, `wxSeq_L4_length_ge`, `cfK_wxSeq_L4_le`) — mostly the `hword`+1 and
   rate bumps.
3. **`exists_xA_L4_psi_irrational`** — combine `exists_xA_L4_orbit_equidist` +
   `affineMap_irrational_of_iInter_avoids` (havoid from the new conjunct + `enum` range).
4. Then DIRECTION step 2 (Chebyshev budget + z-bad record), step 3 (Z-II transfer),
   step 4 (assemble + excise).

## Notes
- ADDITIVE ONLY 🧊: re-`#print axioms` both B5′ headlines after any schedule wiring
  (`src/ax_check_tmp.lean`) — MUST stay the trust triple.
- The cfK/freq boundary math is all validated on paper this lap (see "Ripple" above);
  the wiring is bounded plumbing, not new uncertainty.
