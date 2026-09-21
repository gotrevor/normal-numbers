# LITERATURE 2026-09-20 — sweep for `PrefixDecay` (k-point ω-twist correlations, natural density, all scales)

Sweep by a fresh Opus agent (web + arXiv API), brief and report in the KB session log; ids below re-checked by Ren
against `export.arxiv.org` (titles + dates) on 2026-09-20 23:46 EDT.  Papers were NOT all opened by Ren - the
"disqualifying feature" column is the agent's reading, marked as such.

**Target.** `PrefixDecay h` (`G4WindowK.lean`): `Σ_{m<M} ∏_{j≤k} e(h/4^j)^{ω(m+j)} = o(M)` along ALL `M`, uniformly for
`k ≤ log₂log₂log₂M`, every `h ≠ 0`.  An Elliott-type `k`-point correlation of DIFFERENT non-pretentious multiplicative
functions at consecutive shifts; natural averaging; all scales; `k` growing.

**Verdict (agent 92%, Ren agrees): nothing gives it, and nothing gives even `k = 2` at natural density along all scales.**

| id | authors, date | what it gives | why it does not reach the target |
|---|---|---|---|
| 2512.01739 | Tao–Teräväinen, 2025-12 (our local `papers/tao-teravainen-2025-quantitative-correlations.txt` is this paper) | 2-point, natural average over `(N,2N]`, saving `𝓛^{-c}` | outside an exceptional set of scales; 2 points only.  Their §4: triple correlations and removing the exceptional set "do not appear to be within current technology"; Tao's blog post for it: "the standard limitation … either requires logarithmic averaging, or is restricted to almost all scales rather than all scales" (agent's quote, not opened by Ren) |
| 2304.05344 | Klurman–Mangerel–Teräväinen, 2023-04 | `(1/x)Σ f(n+h₁)f̄(n+h₂) → 0` for non-pretentious `f`, unweighted | only along a set of `x` of full upper logarithmic density; single `f`, not distinct `f_j` |
| 2412.17583 | Charamaras–Richter, 2024-12 | `Ω(n)`, `Ω(n+1)` asymptotically independent along logarithmic averages, quantitative (double-log saving); with `a(m)=z^m`, `b(m)=w^m` this IS the `k=2` Ω-twist correlation | logarithmic averaging; shift 1 only |
| 2608.26814 | Tardy, 2026-08 | `(f(n), g(n+1))` dense-orbit recurrence for distinct unimodular c.m. `f, g` | logarithmic lower density; recurrence, not a decay bound |
| 2306.09929 | Mangerel, 2023-06 | `f(n) = f(n+h)` has log density 0 when `Σ_{|f(p)|≠1} 1/p = ∞` | hypothesis fails for unimodular twists `z^ω` |
| 2310.19357 | Pilatte, 2023-10 | the engine behind TT 2512.01739 (two-point log Chowla, power-log saving) | logarithmic |
| others | Kim 2603.23250 (ternary, conditional, averaged); Wang 2609.14492 / 2608.16108, Menon 2607.15574 (MRT-type, averaged over shifts); Guo 2608.23500 (log, Liouville, **unverified single-author preprint - do not cite**) | | none natural-density-all-scales; none tracks `k` growing |

**Two structural facts recorded from this pass (Ren).**
1. Gowers-norm technology (Green–Tao–Ziegler; Tao–Teräväinen quantitative Gowers uniformity of `μ`) does not apply: all
   forms `n + j` share the same linear part, so the pattern is degenerate - `PrefixDecay` is Chowla-type, not a
   "non-degenerate linear pattern".
2. `WindowDecay ⇔ WindowDecayK` (both directions by `window_tail_tendsto_zero`), but neither implies nor is implied by
   2-point decay; the `J`-point window correlation is a different statement from the `k=2` case.  So `PrefixDecay`'s
   difficulty is *morally* the natural-density Elliott class, not provably bounded below by it.  The axis "number of
   shifts growing with the scale, with explicit loss" appears untouched in the literature in ANY averaging - the
   triple-log leverage of `windowK` has no known result to spend it on.

**Consequence for the graph.** `PrefixDecay` stays 🔴 with no known mechanism; no lap is warranted on it.  The nearest
known objects are log-averaged (Charamaras–Richter for our exact `k=2` twist) or almost-all-scales (TT 2512.01739).
A *conditional* rung is available if ever wanted: "G₄ is normal along a log-density-1 set of scales" would need only the
almost-all-scales technology extended to `k → ∞` sites, which is still open (TT §4), so even that is not a lap.
