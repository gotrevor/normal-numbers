# FINDINGS — PairDecouple, the refutation direction (lap 1)

**Branch** `wip/pd-refute` · objective `KICKOFF-2026-09-24-pd-refute.md`
**Verdict so far: NO counterexample, and the checklist is now discharged as theorems.**
**Confidence that `PairDecouple` is TRUE: 92%** (up from Ren's 85% prior).

Target: `not_pairDecouple_all` in `src/NormalNumbers/PairDecoupleRefute.lean` (ratified, still an
open `sorry`).  `PairDecouple b p q t` (`SwingC1Decouple.lean`) is the sole open input of
`conjC1_of_delange_katai_decouple`.

## 0. What `PairDecouple` actually says, after the twist

`progMean_pairRemainder` (`PairDecoupleLower.lean`, proved this lap).  On the class `c mod Q`,
`Q = primorialLe P`, the truncation `truncPairTail b P p q ·` is the CONSTANT
`truncPairTail b P p q c`, because it is exactly `Q`-periodic.  Hence with
`f n = e(t·pairTail b p q n)` and `A c = e(t·truncPairTail b P p q c)`,

> `progMean B Q R c = conj(A c) · progMean f Q R c`,

so `pairDefect` is the mean absolute deviation of the **twisted** class means
`conj(A c)·M_c(R)` of the *pair correlation itself*.  `PairDecouple` therefore reads:

> the ONLY dependence of the class-`c` mean of `f` on `c mod Q` is the deterministic
> small-prime model factor `A(c)`.

That is the honest statement of leaf (D), and it is the statement the checklist below attacks.

## 1. The checklist, discharged (all machine-checked, trust triple)

| # | attack (kickoff §2) | fate | theorem |
|---|---|---|---|
| 1 | shifts `k` with `p ∣ 1+k`, so `p ∣ pn+1+k` for every `n` | **fails.** `p ∣ pn+k ⟺ p ∣ k`, so `p`'s whole contribution to `omegaTail b (pn)` is the constant `1/(b^p−1)`; a constant summand in the exponent leaves the class deviation untouched | `primePeriodicTerm_mul_self`, `classDeviation_phase_add_primePeriodicTerm_self` (`PairDecoupleAttacks.lean`) |
| 2 | the `n = 0` term | **fails.** `pairRemainder b P p q 0 = 0` for every `b,P,p,q`, so `B 0 = 1` — and perturbing `B` on `[0,n₀)` moves the defect by `≤ 4n₀/(QR)` | `pairRemainder_zero`, `classDeviation_perturb`, `classDeviation_perturb_zero` |
| 3 | `p, q` sharing a prime for every `n` in a class | **fails, and this IS the CRT reason.** If `r ∣ pn+k` for every `n ≡ c (mod Q)` then `r ∣ pQ`, so `r = p` or `r ≤ P`: no prime beyond the cut is pinned by the class | `no_prime_dvd_class_beyond_cut` |
| 4 | `P` with `p ≤ P` (`p ∣ Q`) | **no bias, but it does relocate content**: see §2 | `pairLocalFactor_eq_one_of_congr` |
| 5 | the `R`-indexing of `progMean` vs `fullMean` over `Q·R` terms | **no mismatch.**  `fullMean B (Q·R)` IS the mean of the `Q` progression means (`fullMean_eq_periodMean_progMean`), so `pairDefect` is a genuine mean absolute deviation, `∈ [0,2]` | `pairDefect_nonneg` |
| 6 | `P < 2` | **`pairDefect ≡ 0`**: modulus `1`, one class.  A counterexample needs `P ≥ 2` | `pairDefect_tendsto_zero_of_lt_two` |

## 2. A genuine structural finding: the split is VACUOUS on a whole family of pairs

`pairLocalFactor b t r p q = 1` **exactly** when `p ≡ q (mod r)`
(`pairLocalFactor_eq_one_of_congr`).  Consequently:

* **The `∀ᶠ r` of lap 32's separation bound `norm_pairLocalFactor_le` cannot be dropped.**  At the
  finitely many primes `r ∣ p − q` the local factor has modulus exactly `1`; there is no gain.
  (Audit anchor in the file: `pairLocalFactor b t 2 3 5 = 1` for every `b, t`.)
* If `p ≡ q` modulo **every** prime `r ≤ P`, i.e. `primorialLe P ∣ p − q`, then the model term
  `∏_{r≤P} pairLocalFactor = 1` exactly and `pairDefect b P p q t R` is the **raw** class
  deviation of the pair correlation `f` (`pairDefect_eq_classDev_of_congr`).  For those pairs the
  whole of `PairDecorr` sits in the defect at that cut: the model/decoupling split of
  `SwingC1Decouple` buys nothing there.  Such pairs exist at every cut: `(5,11)` at `P = 3`,
  `(7,37)` at `P = 5`, `(11,431)` at `P = 7` — each verified in Lean.
* Smallest nontrivial instance of all: `P = 2` with `p, q` odd gives
  `pairDefect b 2 p q t R = ‖progMean f 2 R 0 − progMean f 2 R 1‖/2`
  (`pairDefect_two_of_odd`), i.e. literally *"the even-`n` and odd-`n` means of the pair
  correlation agree asymptotically"*.

**This is where a counterexample would have to live**, and it is where the numerics were pointed.

## 3. The refutation engine (so a future counterexample is cashable)

Two certificates, both proved, both finitary:

* **Test functions.**  For every `χ` on `ℤ/Q` with `‖χ‖ ≤ 1` and `∑_c χ(c) = 0`,
  `‖(1/Q)∑_c χ(c)·progMean B Q R c‖ ≤ pairDefect b P p q t R`
  (`norm_test_le_classDeviation` / `norm_test_le_pairDefect`).  With `χ(c) = e(−ac/Q)` this is
  `Q−1` *computable* lower bounds; a refutation is one `(P, a)` whose bound stays away from `0`.
* **The two-sided pin.**
  `‖fullMean f (Q·R)‖ ≤ 2·pairDefect + ‖∏_{r≤P} pairLocalFactor‖` (`norm_fullMean_pairTail_le`),
  whose contrapositive `not_pairDecouple_of_pairCorr_ge` needs no hypothesis on `P` (the cut is
  chosen from the *proved* model decay).  So **refuting `PairDecouple` ⟺ refuting `PairDecorr`
  at the same pair**: there is no cheaper boundary route.  That is itself the lap's sharpest
  negative result — the frozen statement has no soft spot.

## 4. The numbers (`probes/pair_defect.py`, stdlib only — no numpy, no egress)

Exact `ω` by sieve; the tail by the exact backward recurrence `T(M) = (ω(M+1)+T(M+1))/b`, so
there is no `k`-truncation at all.  Controls: `C1` (`B≡1` ⇒ defect `0`), `C2` (`B(n)=e(an/Q)` ⇒
defect **exactly 1**, `LB(a)=1`), `C3` (`B(n)=e(φn)` against the closed-form geometric sum),
`C5` (`∑_k ω(k)/b^k = ∑_r 1/(b^r−1)` to 16 digits), and `C4`, the real one: `pairRemainder`
computed by two independent routes (full `ω` minus the closed-form `truncPairTail`; and a sieve
on `ω_{>P}`) agree to `≤ 9e-16` on **every** case run.

* `data-2026-09-24-pair-defect.txt` — `b∈{3,4}`, `m∈{1,2,4}`, `P∈{2,3,5,7}`, `N ≤ 1.2e5`.
  Every `defect` and every `maxLB` **decays monotonically** in `R`, roughly like `1/log N`.
  No refutation signal.
* `data-2026-09-24-pair-defect-degenerate.txt` — the §2 family.  `|periodMean A| = 1.000000`
  exactly, in all ten cases (the Lean theorem, numerically). `|fullB| = |fullf|` exactly, as it
  must be.  `maxLB` decays, but SLOWLY: e.g. `(3,1,5,11,P=3)` gives `0.00985 → 0.00958` over
  `R ×8`.  `(b=4)` is an order of magnitude smaller.
* `data-2026-09-24-pair-defect-bands.txt` — **the mechanism.**  Restrict the remainder to primes
  in `(P, y]`.  For FIXED `y` the class deviation decays like `R^{-1/2}…R^{-1}`, exactly the CRT
  rate `O(y/R)` — and it is **exactly 0** whenever the relevant residues equidistribute exactly
  (e.g. `p=5,q=11,P=3,y=5`: only the prime `5` is in the band and `5 ∣ R`, so the class means are
  equal to machine precision).  The band defect then *grows* with `y` to a peak around
  `y ≈ 10^5 ≈ N/2` — the artificial bias of a truncation that is too coarse, i.e. lap 33's
  finding quantified — and **drops back** by a factor 4–5 when all primes are restored.  So the
  full remainder's residual deviation is not carried by any single band; there is cancellation
  across bands, and no band shows a persistent floor.

## 5. Why I now believe `PairDecouple` is TRUE (92%)

The class deviation is a **relative** quantity, and the band decomposition shows it is produced
entirely by the CRT counting error of finitely many primes plus a cross-band cancellation.  For
every fixed `y` it *provably* → 0 (attack 3), and the `y → ∞` excess is not merely small, it is
*smaller* than the intermediate truncations — the opposite of what a conspiracy looks like.  The
observed residual decays at about `(log N)^{-1/2}`, which is the expected Delange-type error
scale for this object; the slow rate is why the numerics cannot *settle* it, not evidence against.

The remaining 8% is concentrated in exactly one place: `Q` is fixed *before* `R → ∞`, so the
primes `r ≍ N` are the only ones no CRT argument reaches, and nothing here rules out a
conspiracy between `n mod Q` and the largest prime factor of `pn+k`.  That is the crux for the
positive direction too.

## 6. The next refutation probe, if this line is continued

1. **Largest-prime-factor conditioning.**  Split `n < QR` by `P⁺(pn+1)` above/below `√N` and
   compute the class deviation of each part separately.  If the class bias lives in the
   large-`P⁺` part, that isolates the only unreached regime; if it does not, `PairDecouple` is
   effectively settled numerically.
2. **`m` large.**  `t = m/b` with `m ≡ ±1 (mod b)` huge reweights the `k`-tail (the `b^L` part of
   `m = b^L+1` kills the first `L` digits mod 1).  The `m = 4, b = 3` row already shows the
   correlation collapsing (`|fullf| = 0.0024` at `N=1.2e5`); a scan in `m` tests whether some `m`
   makes the *relative* deviation grow.
3. Do **not** re-attack the boundary cases: §1 closed all six as theorems.
