# HANDOFF twopoint — lap 66, 2026-09-25: **TT2025 §5.2 formalised — the alternating sum cancels the depth-`K` head**

Branch `wip/twopoint-avg`.  Full `lake build` green (**9304 jobs**).  All new declarations
`#print axioms`-clean.  **No `sorry`.**  New file `src/NormalNumbers/TwoPointC3Alt.lean` and new
probe `probes/c3_alt_cancellation.py`; no frozen file touched.

## The advance — the last untouched directive item

`DIRECTION.md` rung 3 ends by naming TT2025 §5.2, *"taking an alternating sum to cancel terms"*
(*"inspired by the theory of the Gowers uniformity norms"*), as **the literature's way to reduce a
growing-depth combination to pairwise correlations**, with the note that the repo has no analogue.
It now has one, as a theorem:

    altSum_depthHead_eq_zero :
      ∑_{S ⊆ Fin K} (−1)^{|S|} ∑_{h=1}^{K} ω_{>P}((n + altShift p₀ v h S).toNat) · b^{−h} = 0

i.e. TT2025 **(5.8)**: the alternating sum over `ε ∈ {0,1}^K` annihilates the entire depth-`K` head
of the tail, at the cost of `2^K` shifted copies.  Pieces:

* `altToggle`, `altToggle_involutive`, `altToggle_ne`, `neg_one_pow_altToggle_card` — the toggle of
  one coordinate of `ε`, as a subset of `Fin K`, and the fact that it flips the parity of `|ε|`.
* **`altSum_eq_zero_of_indep`** — the engine, and the whole idea in one line: *if the summand
  factors through a quantity invariant under toggling one coordinate, the alternating sum
  vanishes.*  A sign-reversing involution (`Finset.sum_ninvolution`), no arithmetic, any `CommRing`,
  any outer function.
* `altShift` = TT2025 (5.7) `r_{S,h} = p₀h + ∑_{k∈S}(h−(k+1))v_k` (the repo's `Fin K` index `k`
  stands for the paper's `k+1`), and **`altShift_toggle_eq`**: for `1 ≤ h ≤ K` the shift is
  independent of coordinate `h−1`, because the coefficient `h−k` vanishes at `k=h`.  That single
  vanishing coefficient *is* the trick.
* `altSum_shift_eq_zero` (any function of the shifted argument), `altSum_omegaLarge_eq_zero`.

**Scope, stated honestly.**  Only the *combinatorial* half is formalised — and it is the half the
repo lacked.  The identity is **unconditional on the primality of the `p_ε`**: primality enters the
paper only through the congruence (5.5) that puts the tail in `δ_p` form, not through the
cancellation.  The analytic half (the `δ_{p_ε}` remainders negligible; `p_ε` simultaneously prime,
arrangeable by a sieve) is not touched.

**Independent check** (`probes/c3_alt_cancellation.py`, stdlib only, with a hand-computed anchor
`K=3, p₀=7, v=(5,11,17), h=1 → shifts {7,−4,−27,−38}` each hit once with each sign): for every
`K ≤ 8`, frequencies `h = 1..K` cancel and `h = K+1` does **not**.  The boundary is sharp, which
also rules out an off-by-one in the `Fin K` indexing.

## Where this leaves the route

Rungs 2/3 proved the depth must grow; §5.2 is how the literature pays for growing depth.  The next
obstruction is now visible and quantitative: the trade costs `2^K` terms against a `b^{−K}` gain, so
the alternating combination is useful when `2^K b^{−K} → 0`, i.e. **`b ≥ 3`** — matching TT2025's own
remark that base `b > 2` is *"somewhat easier"* than `b = 2`, and matching `ConjC3`'s hypothesis
`3 ≤ b` exactly.  That coincidence is a good sign for the route, and is the first place the repo's
`b ≥ 3` has been explained by the method rather than assumed.

## Ladder state

| rung | statement | commit |
|---|---|---|
| 0 | `isRichSubpoly_of_weylTailAlmostAll` | `6978dd5` |
| 1 | `addCharTail_depthOne` | `29a4d7d` (lap 61) |
| 2 | `tendsto_mean_tailLarge_atTop` | `81606d2` |
| 3 | `addCharTail_iff_depthWeighted`, `no_constant_depth_budget`, `addCharTail_iff_plain_of_budget` | `f7f8d1c` |
| 3′ | `peelBudget_id`, `tailLarge_le_log` — the pin unconditional | `7021f54` |
| 3″ | `altSum_depthHead_eq_zero` — TT2025 §5.2 | this lap |

## NEXT SESSION

1. **Quantify the `2^K` vs `b^{−K}` trade as a theorem.**  With `tailLarge_le_log` (lap 65) and
   `altSum_depthHead_eq_zero`, prove: the alternating combination of the tails is
   `≤ 2^K·b^{−K}·(log₂(·)+1)`, hence `→ 0` for `b ≥ 3` along `K → ∞`.  This is the first
   *unconditional* statement in the campaign that uses `b ≥ 3` essentially, and it is a short lap.
2. **The adjacent unconditional item** `SwingC3Signed.lean` names and nobody did:
   `∏_{P<p≤K} ‖primeFactor b p h‖ → 0` (one-term bound into `norm_primeFactor_sq_le`, then
   `mertens_lower`).
3. **Harden rung 0**: derive `ScalesDense` from a log-density hypothesis on the exceptional set.
4. The sieve half of §5.2 (`p_ε` all prime) is a Chinese-remainder + Brun/Selberg statement; the
   repo has `KICKOFF-brun-*` machinery on `master`.  Check before re-deriving.

## Confidence
- `twoPointWeightedAvg_all` TRUE 90%; provable with known techniques 3% (untouched, as ratified).
- `WeylTailHypothesis` TRUE 97%; provable at every scale with known techniques 8%.
- `WeylTailAlmostAll` from 2026 literature 70%; ⇒ `IsRichSubpoly` **in the kernel**.
- Depth resource fully characterised: **certain**.  §5.2's cancellation: **in the kernel**.
