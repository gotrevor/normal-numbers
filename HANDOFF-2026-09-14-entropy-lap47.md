# HANDOFF — entropy laps 46–47 (alignment removed), 2026-09-14, Opus

**Branch** `wip/g4-entropy`.  `lake build` 🟢 **8977 jobs**.  `src/` sorry-free.  No `axiom`.

## 0. The two laps in one line

The `ℓ`-grid alignment of the uniform `t`-wise theorem is **gone**: `G₄`'s sampled windows
decorrelate over *every* vector of unrestricted positions, averaged, at the same rate.

## 1. What was proved — `G4EntropyJointFree.lean` (new module)

Abstract layer (lap 46):

```
mul_sqrt_eq             a√X = √(a²X)
pvPat / pvAgg           patterns at an arbitrary position vector
jjPat_eq_pvPat, patPos_eq_pvPat            (both `rfl`)
abs_alignedFamily_sub_le   |∑_{q<Q} pvAgg(pp + qℓ·1) − |B|Q·2^{−ℓt}| ≤ 2√(|B|Q·log2·Δ)
cntRes / lt_cntRes_iff / sum_range_mod_decomp   the residue split j = r + qℓ, r < ℓ
uniPosFreq m ℓ t P blk L w                  average over all pv ∈ [0,P)^t
abs_uniPosFreq_sub_le  |uniPosFreq − 2^{−ℓt}| ≤ 2t√(2log2·ℓΔ/(|B|P))   (ℓ ≤ P, P+ℓ ≤ m+1)
```

Schedule layer (lap 47), namespace `G4.Sched`, at `P = m_K − ℓ + 1`:

```
freeFreq i ℓ t x w
abs_freeFreq_sub_le_of_deficit         ≤ 2t√(8log2·ℓtδ/m_K)
abs_freeFreq_sub_le_primeLambertFour   ≤ 2t√(1600log2·ℓt/√K)
tendsto_freeFreq_primeLambertFour
pvPat_eq_pack_iff / freeFreq_eq_count / freeFreq_eq_digits
tendsto_occursCountJointFree_primeLambertFour
```

The endpoint:

```
#{(n,b,pv) : ∀ s<t, OccursAt 2 G₄ (v s) (2·kIdx(n, blkSched b s) + pv s)}
  / (|P_K| · nblk_K · (m_K − ℓ + 1)^t)  →  2^{−ℓt},
```

`pv` ranging over **all** of `[0, m_K − ℓ + 1)^t` — every position at which an `ℓ`-window fits
inside the sampled window, no alignment condition.  `#print axioms` prints the trust triple.

## 2. Which bottleneck moved

`abs_avg_patPos_prob_opt` advances its coordinate family in steps of `ℓ`; that was the *only*
source of the alignment, and `sum_range_mod_decomp` removes it by splitting any diagonal into
`ℓ` aligned families indexed by `j mod ℓ`.  The price is the factor `√2` (`Qℓ ≤ 2P` on each
residue class).  So: **alignment was an artefact of the coordinate construction, not of the
arithmetic.**

The ladder of endpoints, each strictly stronger than the last:

| lap | positions |
|---|---|
| 38 | one common aligned position `jℓ` for all `t` windows |
| 41 | a fixed offset vector `pp s`, common aligned shift |
| 45 | **all** aligned vectors `jj ∈ [0,⌊m_K/ℓ⌋)^t`, averaged |
| 47 | **all** vectors `pv ∈ [0,m_K−ℓ+1)^t`, averaged — no alignment |

## 3. The next bounded test

The remaining weakening is the **averaging over `pv`**: all four endpoints are `ℓ¹` statements.
A per-vector (`ℓ∞`) statement — *for each fixed* `pv`, the frequency tends to `2^{−ℓt}`,
uniformly in `pv` — is genuinely open: the capacity argument bounds a sum of `P^t` deviations,
and nothing so far forbids one vector carrying all of it.  Two bounded probes:

1. **A partial `ℓ∞` result for free**: lap 41's `tendsto_occursCountJointPos_…` already gives
   each *fixed offset vector* `pp` at the aligned shifts; combine with the residue split to get
   each fixed `pv` at a *fixed* `pv`, i.e. `ℓ∞` over positions but still averaging over the
   common shift `j`.  Check whether `abs_alignedFamily_sub_le` at `Q = 1` is vacuous (it is:
   `2√(|B|·log2·Δ)` against a mass of `|B|`), which is the honest statement of the obstruction.
2. **Quantify the obstruction**: the deficit `Δ = δ·|Atom|` is `50√K·|Atom|` while a single
   position vector holds `|B|·2^{−ℓt}` mass; record the exact `K`-threshold at which an `ℓ∞`
   claim would need `Δ = o(|B|)` rather than `o(|B|P)`.  A negative result's value is its
   constant.

## Claim limits (unchanged)

Nothing here is a statement about the normality of `G₄`; normality on this mechanism is closed
(lap 37/39).  All endpoints concern the *sampled* positions only.
