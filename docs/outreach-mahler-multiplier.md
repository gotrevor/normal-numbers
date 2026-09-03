# Outreach dossier: the Mahler multiplier bound 📬

**Who to email when `M(g,k) ≤ g^(k+1)` (and the elementary route) is formalized and ready to
share.**  Compiled 2026-09-02 from primary sources; a codex session raised the names and this file
re-verified each claim independently.  Addresses below came from author-hosted pages and the
published papers themselves, not from memory.

⚠️ Nothing here is a decision to send.  Trevor sends; Ren drafts.  Before drafting, re-check the
"open question" framing against `ON-LINE-FINDINGS-2026-09-02-berend-boshernitzan-1994.md` and
reconcile the two bounds (`g^(k+1)` vs the elementary `(g+3)gᵏ`) into one honest statement.

## The hook 🎯

Berend–Boshernitzan, *On a result of Mahler on the decimal expansions of (nα)*, Acta Arith. **66**
(1994) 315–322, write: *"We do not know whether it is true in general that `M(g,k) < g^(k+1)`."*
Our unconditional `m ≤ g^(k+1)` answers that stated question, removing the factor 2 their Case IV
argument costs them (their Case I already remarks that `g^(k+1)` would suffice there).  Paired with
their Thm 3.2 (`(1−ε)g^(k+1)` for every non-prime-power base) it pins `M(g,k) ≍ g^(k+1)`
asymptotically sharp.  Method is also different: Dirichlet + arithmetic progressions + an exact
shadow recursion, where theirs is orbit-closure / ε-net via Furstenberg–Glasner.

📌 Attribute, don't claim: the lower bound `M(g,k) ≥ t(gᵏ−1)` in `MahlerLowerBoundGeneral.lean` **is**
B–B Theorem 3.1.  That module is a formalization of a known theorem.

## The four names

| Person | Status | Address | Why them |
|---|---|---|---|
| **Daniel Berend** | Professor Emeritus, Depts. of Math and of CS, Ben-Gurion University, Beer-Sheva 84105, Israel.  Active: Abramoff–Berend–Kolesnik, *Density modulo 1 and Hardy fields*, Israel J. Math. **267** (2025) 171–203 | `berend@cs.bgu.ac.il` | It is **his question**.  Still publishing in the same dynamical neighborhood, extending Boshernitzan's density-mod-1 work |
| **Michael Boshernitzan** | 🕯️ **Died 28 Aug 2019**, aged 69, after a long illness (Rice professor of mathematics) | — | Do not write.  Named here so no draft ever addresses him |
| **R. Thangadurai** | Professor of Number Theory, Harish-Chandra Research Institute, Prayagraj | `thanga@hri.res.in` | Co-author of *A note on Mahler's theorem – II*, Proc. Indian Acad. Sci. (Math. Sci.) **135** (2025), paper 39, DOI `10.1007/s12044-025-00848-z` — whose abstract still treats `2g^(k+1)` as the operative unconditional bound |
| **Aparna Tripathi** | HRI; co-author on the 2025 paper.  (Reported as Thangadurai's PhD student — *unverified here*, his page does not list students in static HTML) | `aparnatripathi@hri.res.in` | Same paper; the active junior hand on exactly this constant |

Emails for Thangadurai and Tripathi are printed on the 2025 paper itself
(`papers/thangadurai-tripathi-2025-mahler-ii.pdf`); Berend's is from his contact page,
`https://www.cs.bgu.ac.il/~berend/contact.html`.  ⚠️ His publication list
(`~berend/pub/pub.html`) stops in 1999 and is **not** a freshness instrument — the 2025 paper is
not on it.

## Audience calibration 📊

The real audience is these three living mathematicians and their immediate circle, not AI-math
spectators.  Rough read (codex's numbers, kept as its estimate, not re-derived):

- Specialist interest from Thangadurai/Tripathi: high (~95%) — their 2025 paper is literally on this
  constant.
- Berend: equally worth writing; it is his open question and he is active nearby.
- Broader number-theory notice: modest.
- Lean/AI splash: small (~30%).  "AI solved a small open problem" is no longer inherently
  newsworthy; lead with the mathematics, not the formalization.

## When drafting ✍️

- One email per recipient group, and **the subject line names the other party** (Berend's subject
  should not read like a form letter shared with HRI).
- Lead with the answered question and the constant.  The Lean certificate is a *supporting* detail,
  one sentence.
- Substantially Ren-written outward prose carries the AI-authorship line, in Trevor's register.
- ⚠️ Anything about who has or hasn't already done this is a **negative search result**, not an
  absence — see `docs/tower-novelty-audit-2026-08-29.md` and keep the outward claim to "we did not
  find," with the expert check explicitly invited.
