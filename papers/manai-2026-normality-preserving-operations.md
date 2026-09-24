# Manai 2026 — pin note (added 2026-09-23)

C. Manai, *On Normality Preserving Operations*, arXiv:2609.24665 (v1, 2026-09-21).  PDF alongside
(gitignored).

## Coverage

Read: abstract, §1 statements (Theorems 1.1–1.4), statement of Thm 2.4 (Hochman–Shmerkin) and
Cor 2.6.  Not read: proofs.

## What it says

- **Thm 1.1** (Wall; Dayan–Ganguly–Weiss, re-proved self-contained): the multipliers γ with
  γ·N_b ⊆ N_b are exactly ℚ∖{0}; same for absolute normality (via Hochman–Shmerkin).
- **Thm 1.2** (extends Rauzy): translation x ↦ x + a preserves absolute normality iff a is
  completely deterministic in every integer base.  Proof: sparse random perturbation.
- **Thm 1.3:** a locally C² map preserving base-b normality on an interval is constant or
  affine `ax + c`, a ∈ ℚ∖{0}, c deterministic.
- **Thm 1.4:** sharp: a non-affine C^{1,1} diffeomorphism preserves normality in every base.

## Why it matters here

Closure facts for any transfer step of the form "normal x ⟹ f(x) normal": only rational scalings
and deterministic translations are safe, and C² nonlinear maps never are.  Checks a candidate
transport route before it is walked (cf. `normal-numbers-disjunctivity-transport-audit-2026-09-14.md`).
