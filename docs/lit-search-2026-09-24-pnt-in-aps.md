# Lit search: PNT in arithmetic progressions in Lean (2026-09-24)

Question: is our `psiAP_tendsto` (`src/NormalNumbers/DelangeSlotAP.lean`), `ψ(X; q, a)/X → 1/φ(q)`
for fixed `q`, `gcd(a,q) = 1`, new?  **No.  It is a duplicate of PNT+'s `WeakPNT_AP`, and weaker
than what PNT+ carries.**

| Source (instrument) | What exists |
|---|---|
| PNT+ (`AlexKontorovich/PrimeNumberTheoremAnd`, clone at origin/main 55270df) | `WeakPNT_AP` (`Wiener.lean`): `cumsum (Λ on class a mod q) N / N → 1/φ(q)`.  `Consequences.lean`: `chebyshev_asymptotic_pnt` (θ(x;q,a) ~ x/φ(q), `IsEquivalent`), `dirichlet_thm`.  No π(x;q,a) form found (grep of `Consequences.lean` only).  Blueprint next AP target: Chebotarev. |
| mathlib (grep of origin/master 045acef0f7) | Dirichlet's theorem only (`Mathlib/NumberTheory/LSeries/PrimesInAP.lean`, Loeffler–Stoll; `docs/100.yaml` #48).  No asymptotic.  Open PRs not searched. |
| Uniform versions (grep/READMEs only, not built) | Siegel–Walfisz claimed in `subfish-zhou/goldbach-lean`; Bombieri–Vinogradov efforts in `kimihiro64/bombieri-vinogradov`, `amellendijk/lean-bombieri-vinogradov` (modulo S–W). |
| Lean Zulip (`zulip-ro`) | No "PrimesInAP" hits; `WeakPNT_AP_prelim` solved by Aristotle (Jan 2026). |
| Isabelle AFP | Dirichlet's theorem (`Dirichlet_L`, Eberl).  PNT in APs not checked. |

Our proof uses mathlib's `vonMangoldt.LFunctionResidueClassAux` nonvanishing package through the
vendored `WeakPNT_AP_prelim`.  It is fine as a port for the Delange slot; the only thing that
would be new is a π(x;q,a) corollary or an error term, and Siegel–Walfisz is already claimed elsewhere.
