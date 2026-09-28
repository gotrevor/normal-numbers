# HANDOFF twopoint lap 22 — the elementary pairing route is rigid, hence dead

Branch `wip/twopoint-avg`.  New file `src/NormalNumbers/TwoPointPairingRigidity.lean`,
sorry-free, axioms `[propext, Classical.choice, Quot.sound]` (`pairing_shift` needs only
`[propext, Quot.sound]` — it is pure `ring`).

## Advance on the crux: a sub-approach tried and refuted, in kernel

Lap 21 proposed constructing `σ` by a multiplicative move `p·σ(m)+1 = r·(pm+1)` (which raises
`ω` of the `p`-dilate by exactly one when `r ∤ pm+1`).  This lap settles what that forces.

* **`pairing_shift`** — the shape is forced: with `r = pk+1` and `σ(m) = rm + k`,

      p·σ(m)+1 = r·(p·m+1) ,      q·σ(m)+1 = r·(q·m+1) + (q−p)·k .

  The `q`-dilate is the corresponding multiple **plus the nonzero additive defect `(q−p)k`**, and
  `ω(r(qm+1) + (q−p)k)` has no relation to `ω(qm+1)`.  So `z` is not constant on `A` and lap 21's
  hypothesis fails.
* **`no_elementary_pairing`** — the rigidity with no `ω` in sight: if `σ` satisfies
  `p·σ(m)+1 = r·(pm+1)` *and* `q·σ(m)+1 = s·(qm+1)` at two consecutive `m`, with `p ≠ q`,
  `p,q ≠ 0`, then `r = s = 1` — `σ` is the identity and the rotation is trivial.

**Verdict.**  The two dilates cannot be decoupled by an elementary substitution.  This is
precisely the rigidity that makes two-point Chowla/Elliott hard, now isolated as a two-line
algebraic fact about the leaf.  Lap 21's *tool* (`norm_sum_le_of_rotation`) stays correct and
available; the *construction* sketched there is refuted.

## Where the run stands

`ConjC1` = Delange + one arithmetic leaf (`conjC1_of_delange_twoPointGram`), with the entire
Kátai/BSZ step kernel-checked (`katai_master`, `katai_mean_sq`).  Four attacks on the leaf, all
priced in kernel:

| route | status |
|---|---|
| trivial per-pair estimates | insufficient by an unbounded factor (lap 13) |
| `ℓ¹` averaging over multipliers | no gain: budget `L²`, mass `M(w) ≫ L²` (lap 13) |
| `ℓ²` / fourth moment | demands an exact evaluation of a `≥ N²/8` quantity (laps 15–18) |
| rotation pairing, multiplicative `σ` | rigid: forces `σ = id` (lap 22) |

Positive side: the leaf follows from a per-pair relative saving `L(w)²/(2π(w))` (lap 19), which
the deficit identity (lap 20) and the rotation bound (lap 21) convert into concrete finite
targets.

## Next attack (lap 23)

The remaining honest direction is non-elementary: a pairing that changes `ω` on both dilates by
amounts whose *difference* is fixed, i.e. `σ` with `ω(pσ+1) − ω(qσ+1) = ω(pm+1) − ω(qm+1) + 1`.
`pairing_shift` says a single multiplicative move cannot do it; the next question is whether a
*pair* of moves can — `σ(m) = r m + k` composed with a `q`-side correction, i.e. solving
`p σ + 1 = r(pm+1)` and `q σ + 1 = s(qm+1) + d` with `d` ranging over a small fixed set, so that
`z` takes finitely many values and the rotation bound applies blockwise.  `pairing_shift` already
gives `d = (q−p)k` exactly; the question is whether `r(qm+1) + (q−p)k` can be forced into a
prescribed `ω`-class for a positive density of `m` — a sieve question, not an Elliott question,
and therefore possibly tractable.

## Confidence
- `twoPointWeightedAvg_all` TRUE: 88%.
- `twoPointGramSum` leaf TRUE: 80%; provable with known techniques: 6%.
- The blockwise-rotation variant (lap 23) yields the saving: 15%.
