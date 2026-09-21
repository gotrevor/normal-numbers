# NN: keep both proofs, simplify the specialized route

Ren / Astra, 2026-09-20.  Implements Trevor's decision: work up the simpler proof, **do not abandon the original**.  The KMT derivation remains a live mathematical route, not merely a discarded historical draft.  Confidence in this allocation: 90%.

## What each route is for

| Route | Retain and develop | What it would establish here |
|---|---|---|
| [Original KMT constant audit](/Users/gotrevor/src/normal-numbers/papers/kmt-2023-prop43-k-dependence.md) | Connection to the broader correlation theorem, general multiplicative-function decomposition, source mapping, and referee corrections | The quantitative input needed by the selected-prime normality construction, with controlled dependence on window length |
| [Specialized prime-model proof](prime-model-complement-2026-09-20.md) | Strong multiplicativity, consecutive shifts, exact small-prime conditioning, and the probability-complement shortcut | The same specialized input, with candidate bounds log C₁=O(k), log C₂=O(k log(k+2)) |

The second argument is shorter because it uses extra structure, not because it subsumes the first theorem.  Keep the first route available for generalizations where that structure fails.  In particular, arbitrary multiplicative functions can depend on prime valuations even at the small primes; a residue modulo a primorial no longer captures their entire small-prime contribution.

The two routes **share sieve theory**.  They are useful cross-checks of the decomposition and constant bookkeeping, not two logically independent verifications of every analytic input.  Both remain candidate paper arguments pending their outstanding audits.  Neither proves normality of G₄ or a classical constant.  Their immediate target is the selected-prime Lambert construction.

Preserve the original files and their git history.  Corrections should remain visible as corrections, not be overwritten by a story in which the proof was always obvious.  No historical-novelty campaign is needed.  No changes were made here to Fable's active research files or running jobs.

## Source issue: resolved during this work

Fable's referee report correctly identified that Thorner–Zaman's printed (6.2) is not the standard sieve dimension condition.  My first shortcut draft also needed that citation repaired.  At g=k/p, the standard local factor is p/(p−k), whereas their printed single-sieve specialization is (p−k)/(p−2k).  These cannot be interchanged: k=2,p=3 gives 3 versus −1; k=1,p=2 makes the printed denominator vanish.

While I worked out the 4k alternative below, Fable found a cleaner source.  **Matomäki–Teräväinen, Lemma 9.1** states the standard interval hypothesis, bounded squarefree-supported weights, pointwise upper/lower inequalities, and the explicit relative error e^(9κ−s)K¹⁰ for s≥9κ+1 together.  I checked the statement directly.  The original route records this in repo commit `457753b`; its local source text is `papers/matomaki-teravainen-2023-products-of-primes-in-ap.txt`.  [Primary source](https://arxiv.org/html/2301.07679#S9).

Therefore the specialized proof now invokes that lemma and retains the original cutoff k.  It does **not** need the stronger Thorner–Zaman hypothesis, an assumed correction to their formula, or a book-access detour.  This resolves the source choice, not every remaining calculation in either proof.

The revised shortcut includes an explicit uniform dimension calculation.  Primes immediately above k need no Taylor approximation:

\[
\prod_{k<p\le2k}\frac p{p-k}
\le\prod_{n=k+1}^{2k}\frac n{n-k}
=\binom{2k}{k}\le4^k.
\]

For p>2k, putting t=k/p gives

\[
-\log(1-k/p)+k\log(1-1/p)
\le-\log(1-t)-t\le t^2.
\]

The total quadratic error is at most k/2.  With an absolute dimension-one Mertens interval constant C₀, one can take K_k=(4e^(1/2)C₀)^k.  Thus log K_k=O(k), uniformly in the tuple being sieved.  This calculation is part of the actual mainline proof.

## A useful correction to the referee report itself

The report's §6 says the inequality

\[
|1+w|\le\exp(\operatorname{Re}w+|w|^2/2)
\]

requires |w|<1.  It does not.  For every complex w, set t=2 Re w+|w|²=|1+w|²−1≥−1.  Then |1+w|²=1+t≤e^t, and take square roots.  This is a complete proof of the global inequality.

That correction does **not** license a separate nonuniform expansion involving 1/(1−k/p).  The report's warning about primes just above k still deserves attention wherever such expansions occur.  The shortcut's exact model factor uses A=Σ_j(z_j−1), |A|≤2k, so the global inequality applies directly and costs only e^(2k).

## Preserved alternative: satisfy the stronger printed hypothesis

This was worked out before Fable's new source arrived.  It is retained for the mathematical record, **not** as another required branch or protection layer.

Use Q=∏_{p≤4k}p instead of ∏_{p≤k}p; condition on those primes exactly.  For sifted primes g≤k/p<1/4, the printed factor is positive and bounded by (p−k)/(p−2k).  With t=k/p,

\[
\log\frac{p-k}{p-2k}+k\log(1-1/p)
\le-\log(1-2t)-2t\le4t^2.
\]

Summing over p>4k costs at most k, so the stronger interval condition holds with K_k=(eC₀)^k.  All model, counting, and complement steps still work.  The larger primorial has log Q=O(k log(k+2)) by a trivial bound and does not spoil the final constant growth.

Under this alternative, apply **Thorner–Zaman Theorem 6.1 with g′=g and g″=0**.  Only d₂=1 survives in the reduced composition.  Its threshold is s>9k+1+10 log K_k.  Writing η=e^(9k−s)K_k¹⁰<1, its upper multiplier is (1+η)² and its lower multiplier is 1−η.  Hence use relative error 3η, not η.  These are the source's stated conditions and multipliers.  [Primary source](https://arxiv.org/html/1803.02823#S6).

The phase bound then costs at most e^(k/2) from the quadratic term and e^(4k) from omitted small-prime mass, so e^(5k) suffices.  This too would fit the existing selected-prime construction.  The current mainline needs neither this larger cutoff nor the extra threshold bookkeeping.

## Bounded next work for Fable

1. **Audit the shortcut's arithmetic interface first.**  For each small tuple and residue, check the progression, the one forbidden root when p divides D, the k roots otherwise, and the exact main term μ(d)/Q.  Confirm that both sieve inequalities apply to the squarefree product of forbidden primes.  Check that aggregating the root-count remainder gives x^(−3/8)(1+log x)^(k−1).
2. **Formalize the complement lemma separately.**  For probability laws μ,ν and retained set B, inside L¹ error Δ implies ν(Bᶜ)≤μ(Bᶜ)+Δ and total L¹ error≤2μ(Bᶜ)+2Δ.  This reusable node has no sieve dependency.  Prove it before specializing to complex phases.
3. **Audit the original route on its own terms.**  Use the now-resolved source.  Close its small-prime/degenerate-density case and recheck the ε′ factor, level-versus-length distinction, and completion constant.  Do not erase these obligations because a shorter proof exists.
4. **Converge at one named interface.**  Let each route separately establish the same `KMT_quant₂` statement and growth hypotheses.  The selected-prime construction should consume that interface once.  Keep unproved analytic nodes explicit while formalizing the elementary probability and CRT steps around them.

This is a work allocation, not a treadmill launch.  The original and specialized papers should have disjoint writers until an explicit handoff.

## Persistent controls

The existing [prime-model CLI](/Users/gotrevor/personal/claude/knowledge/core/projects/instruments/prime_model_certificate.py) now includes `sieve-factor` alongside local-valuation, CRT-phase, and complement controls.  Its [external pytest suite](/Users/gotrevor/personal/claude/knowledge/core/projects/instruments/test_prime_model_certificate.py) invokes the real CLI and checks hand-derived rational answers.  It records the standard-versus-printed distinction, including the zero denominator and an assigned-prime example.  All fourteen controls passed on 2026-09-20.  These controls prevent algebraic regressions; they do not prove the analytic estimates.

Run from the KB repository:

```sh
knowledge/core/projects/instruments/prime_model_certificate.py test -q
```
