# Bailey–Borwein §4, the complete answer (RESEARCH SKETCH, UNREFEREED)

> **Status (2026-10-16):** research-subagent sketch; **independent referee: headline ACCEPT (~92%),
> Lemma 3′ ACCEPT, Corollary J ACCEPT, T-B′ ACCEPT, L1 ACCEPT, L2 ACCEPT; Theorem C and the
> single-class shortcut ACCEPT WITH MINOR REPAIRS** (below).  Referee instrument independent of the
> author's (`tmp/referee-bb-full/den.py`, 300/300 vs full Fraction); exhaustive same-class search:
> 11,364 pairs, 409k exact evaluations, no cancelling pair.  Not yet Lean (L1, L2 queued).  Builds on `papers/2026-10-16-stoneham-sums-normal.md` (Theorem A).  Scratch, predictors and
> pre-registrations: `tmp/bb-full/` (`PREREG-1.txt`, `PREREG-2.txt`, `dmeasure.py`, `predict.py`,
> `probe1`–`probe7`).  Confidences are the author's.

## Answer

- **The literal question (q = 1, m = 1):** α_{b,c₁} + α_{b,c₂} is b-normal for **every** pair
  c₁, c₂ ≥ 2 coprime to b, and so is α_{b,c₁} − α_{b,c₂}.  (92% true / 88% proved, modulo F3 =
  Vandehey Cor 1.2.)
- **General families** Σ qᵢ α_{b^{mᵢ},cᵢ}: decided by a finite cyclotomic computation per
  multiplicative class of the cᵢ (Theorem C).
- **Joint normality**: a per-class rank condition (Corollary J); for one prime p it is
  ℚ-linear independence of ω_p(b)^{mᵢ} (Theorem T-B′, proving the T-B dichotomy both ways).
- The non-normal direction is elementary (no F3).

## Referee repairs (to apply when formalizing)

1. **Single-class shortcut.**  Pieces are ≥ c·D with c possibly < 1 and the last piece is truncated,
   so "complete sums only (Lemma 2.3)" is the wrong tool.  Use completion:
   |Σ_{n<J} e(abⁿ/D)| ≤ (J/T + 1)·√D·(1 + log D), T = ord_D b ≫ D for D ∈ ℕ_P (twisted sums over
   ⟨b⟩ bounded by √D).  This makes T-B′, the same-class BB pairs and all single-class results
   **free of F3**.
2. **Theorem C presentation.**  Define P_g to include the period of u^j mod d_ℓ, and handle the
   eventual (not pure) periodicity when gcd(u, d_ℓ) > 1 (e.g. g = 10, ℓ = 5).
3. The "never silent" argument simplifies: at the top s*, Σ_{s<P} μ(J−s)g^s with |μ| ∈ {0,1,2} is
   nonzero under every complex embedding once g ≥ 3, so the case split is redundant.
4. Stale risk note: the referee flagged F3 as an unrefereed preprint; it is published
   (J. Anal. Math. 138 (2019), doi:10.1007/s11854-019-0038-2), and a Lean proof of it is running.

## (a) Characterization

x = Σ qᵢ α_{b^{mᵢ},cᵢ}, cᵢ ≥ 2 coprime to b, qᵢ ∈ ℚ.  Group by primitive base g (cᵢ = g^{sᵢ}, g not
a perfect power; same class ⟺ multiplicatively dependent).  mᵢ = g^{aᵢ} m′ᵢ, g ∤ m′ᵢ.

- Atom coefficients λ_g(m′, j) = Σ_{i : m′ᵢ = m′, sᵢ | j − aᵢ} qᵢ g^{aᵢ}, periodic in j with period
  S_g = lcm sᵢ (from the Mahler identity α_{b^{mg},g} = g·α_{b^m,g} − b^{−mg}).
- For each prime ℓ | g: ω_ℓ = Teichmüller lift of b in ℤ_ℓ (order d_ℓ = ord_ℓ b); for ℓ = 2,
  ω₂ := 1 (exponents m·c^k are even).  u_ℓ = g/ℓ^{v_ℓ(g)}, μ_ℓ(m′, j) = λ_g(m′, j)·ω_ℓ^{−m′u_ℓ^j}.
- Phase t = log_g n mod P_g; j_{m′}(t) = ⌊t − log_g m′⌋; J = max j_{m′}.
- Γ_{g,ℓ}(t) = Σ_{m′} g^{J − j_{m′}} (1 − g^P)^{−1} Σ_{s<P} μ_ℓ(m′, j_{m′} − s) g^s ∈ ℚ(ζ_{d_ℓ});
  zero-testing is exact arithmetic mod Φ_d.
- Class g is **silent** at t iff Γ_{g,ℓ}(t) = 0 for all ℓ | g; **persistent** iff silent at no t.

**Theorem C.**  x is b-normal ⟺ no real t has every class phase t/log g mod P_g in the interior of
that class's silent set.  One persistent class ⟹ normal.  With ≤ 2 non-persistent classes:
non-normal ⟺ every class has a silent phase (Kronecker, log g/log g′ ∉ ℚ).  With ≥ 3 classes the
"∃ real t" form is exact; reducing it to "each class has a silent phase" needs ℚ-independence of
the 1/log g (Schanuel-type, open).  Pointwise dichotomy: eventually D_n ≤ C (all classes silent)
or D_n ≥ κ n^ρ.

**Corollary J.**  (α_{b^{mᵢ},cᵢ}) jointly normal ⟺ for every class g and phase t, the ℚ-linear map
q_g ↦ (Γ_{g,ℓ}(t))_{ℓ|g} is injective.  A class holds at most Σ_{ℓ|g} φ(d_ℓ) members.

**Theorem T-B′ (g = p prime).**  (α_{b^{mᵢ}, p^{sᵢ}}) jointly normal ⟺ the ω_p(b)^{mᵢ} are
ℚ-linearly independent.  The sᵢ are irrelevant; at most φ(ord_p b) members; never two for
p ∈ {2, 3}.  Pairs: ⟺ ord_p(b) ∤ 2(m₂ − m₁).

## (b) Proof outline (differences from Theorem A)

§3, Lemma 1, Lemma 2, kick count unchanged.  Lemma 3 → **Lemma 3′**:
1. (K) ℓ | N ⇒ b^N ≡ ω_ℓ^N mod ℓ^{v_ℓ(N)+1}; ℓ = 2: b^{2M} ≡ 1 mod 2^{v₂(2M)+2}.  (Lean: finite-level
   substitute w = b^{ℓ^K} mod ℓ^{K+1}.)
2. Polar part: v_ℓ(S_n − bⁿΦ_ℓ(n)) ≥ min v_ℓ(qᵢ), Φ_ℓ(n) = Σ_{ℓ|cᵢ} qᵢ Σ_{k≤Kᵢ(n)} ω_ℓ^{−mᵢcᵢ^k} cᵢ^{−k}.
3. Periodic tail: Φ_ℓ = Σ_{g∋ℓ} g^{−J_g(n)} Γ_{g,ℓ}(phase) + O_ℓ(1).
4. Rate separation: distinct primitive g, g′ have v_ℓ(g)/log g ≠ v_ℓ(g′)/log g′, so non-silent
   classes sit at ℓ-depths differing by ≫ log n and the deepest survives.
5. D_n ≤ C ⟺ all classes silent; else D_n ≥ κ n^{v_ℓ(g) log ℓ / log g}; D_n ∈ ℕ_P, gcd(D_n, b) = 1,
   D_n ≤ L nʳ.

§5: silent long pieces counted trivially (total o(N) by hypothesis); κN^{r/2} → κN^{ρ/2}; ε = 1/(2r+1)
still works.  **Single-class combinations** have pieces of length ≥ c·D, so only F3's J ≥ m branch
(Vandehey Lemma 2.3, complete sums) is needed (~85%): covers T-B′, same-class BB pairs, α₂,₃ + α₂,₉.

Non-normal direction: if d̄(Z) > 0 then {bⁿx} is within C₀/n of (1/C!)ℤ/ℤ on Z, contradicting u.d.

**Why the literal BB pair is never silent.**  Same class, m = 1: λ(j) ∈ {0, 1, 2}.  g prime, or
2 | g, or 3 | g: the twist ω^{u^j} is constant, Γ a positive multiple of a unit.  Otherwise g ≥ 35:
the top g-digit dominates under every complex embedding (2(g^{s*} − 1)/(g − 1) < g^{s*}).
Differences: digits in {−1, 0, 1}, Σ_{t<t*} g^t < g^{t*}.  Different classes: each class has one
family, hence persistent.

**Elementary witnesses (Lean targets, `StonehamSums.lean` template).**
- **(L1)** For every prime p ∤ b: α_{b,p} − (p+1)α_{b,p²} = Σ_{j odd} b^{−p^{j+1}} N_j,
  N_j = (b^{(p−1)p^j} − 1)/p^j ∈ ℤ; base-b digits p^{j+1}+1..p^{j+2} vanish: not simply normal.
  (Hand-checked by the attended session for p = 3, b = 2.)
- **(L2)** α_{3,7} − α_{9,7} + α_{27,7} = Σ_k M_k 3^{−3·7^k}, M_k = Φ₆(3^{7^k})/7^k ∈ ℤ; zeros on
  (3·7^k, 7^{k+1}].
- General lemma: p^{k+1} | Φ_d(b^{p^k}) for d = ord_p b (2657/2657 checks).

## (c) Refuted guesses

- "Newest term survives" is sufficient, not necessary: α_{b,3} − 4α_{b,27} cancels its top two
  levels at J ≡ 0 (3), but Γ = 9, 1, −23 ≠ 0: normal.
- "Sharing a prime causes failure": false; α_{5,2} + qα_{5,6} and α_{2,3} + qα_{2,15} normal ∀q.
- "Joint normality is pairwise": false; α_{3,7}, α_{9,7}, α_{27,7} pairwise jointly 3-normal, the
  triple not (H11).
- "Composite classes behave like primes with trivial ω": false, b-dependent: (α_{2,15}, α_{2,225})
  jointly 2-normal, α_{4,15} − 16α_{4,225} not.
- Same-class pairs, m = 1, g prime: q₁α_{b,g^{s₁}} + q₂α_{b,g^{s₂}} silent iff
  q₂/q₁ = −g^{(J mod s₁) − (J mod s₂)}(g^{s₂} − 1)/(g^{s₁} − 1) for some J; q₁α_{b,3} + q₂α_{b,9}
  fails exactly for q₂/q₁ ∈ {−4, −4/3} (post-hoc).
- Predictor bug: ω₂ = ±1 → 34 mismatches (seeds 1, 3); fixed to ω₂ := 1 post-hoc.

## (d) Probes (exact D_n on every inter-kick piece up to N = 10⁶⁰)

| Probe | Status | Result |
|---|---|---|
| C1 α₂,₃+α₂,₅ grows; C2 α₂,₃+α₄,₃ bounded on [2·3^k, 3^{k+1}) | pre-registered | PASS |
| H1–H5, H9–H11, H13–H15 silent windows as predicted (D = 1) | pre-registered | PASS |
| H6/H7/H8 q-grids, 18 H11 pairs | pre-registered | PASS |
| H12 | pre-reg slip (c = 4 shares a prime with b = 2) | dropped |
| J1–J8 ranks, 65,871 BB-pair phase checks | pre-registered | PASS |
| Blind random families, seeds 4–6 | post-fix, never run before | 450 trials, 0 mismatches |
| Blind, all 6 seeds | post-fix | 900 trials, ~46.8k pieces, ~5.2k silent, 0 mismatches |
| Digit windows (C2, H2, H10, H11) | pre-registered cases | silent windows 1 distinct 12-word; normal controls 3552–3906/4096 |
| Multi-class density of {D ≤ 10³} | post-hoc | 2 classes 0.10–0.63, 3 classes 0–0.62; control 0 |

## (e) Confidence (author's)

Theorem C 90% true / ~85% proved mod F3 (non-normal half ~95%).  Corollary J, T-B′ 90/85 mod F3
(complete-sum branch only).  Literal BB pairs and differences 92/88 mod F3.  L1, L2 98/97,
elementary.  Evidence: theory sketch + exact-arithmetic probes; nothing Lean-checked.
