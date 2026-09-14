*Repo copy of the attended brief `~/personal/claude/knowledge/core/projects/normal-numbers-entropy-expedition-fable-2026-09-14.md`, staged 2026-09-14 by Ren (Claude).  Operator decisions for this run live in `KICKOFF-2026-09-14-entropy-expedition.md` and the DIRECTION override; where they and this brief differ on engine or model, the kickoff wins (grind laps run on Opus, not Fable - Fable budget).  Read this file before editing.*

# Fable expedition: from arithmetic-sample entropy toward ordinary normality

Fable: establish exactly what the completed G4 arithmetic mechanism says about digit entropy, then prove or explicitly refute a frozen transfer statement to ordinary digit frequencies.  The objective is mathematical progress toward normality, not an expanding queue of routine formalizations.  A precise counterexample is a successful outcome.

Prepared by Ren (OpenAI Codex), 2026-09-14, at Trevor's request.  This document prepares the expedition; no treadmill was launched.  When dispatched as the new campaign instruction, it supersedes the previous G5 objective for this expedition.  Preserve the existing G4 and G5 work.

## 1. Starting point and scope

Repository: `/Users/gotrevor/src/normal-numbers`.  Checked for this brief: clean branch `wip/g4-disjunctivity`, HEAD `bad77d8`.  Recheck before editing.

Already proved:

\[
G_b=\sum_{p\text{ prime}}\frac1{b^p-1}
    =\sum_{n\ge1}\frac{\omega(n)}{b^n}
\]

is disjunctive in base b for every integer b≥3.  G4 is also binary-disjunctive.  In plain language: **fix any finite word first; however far you have read, another occurrence lies ahead.**  This does not assert a frequency, nor does it mean that after each prefix we choose a different word that has not appeared yet.

This expedition fixes **x = G4 and binary digits**, using the elementary base-four arithmetic construction.  It does not resume Ω, G2, Mahler, or ln-two work.  Base-four orbit position k corresponds to binary shift 2k; losing that factor changes the sampling law.

The entropy statement below remains a candidate.  The overnight proof did not formalize it.  Normality remains open.  Ren's prioritization confidence is 80%, not an 80% probability of proving normality in this campaign.

Read first:

1. [Overnight source review](normal-numbers-g4-overnight-review-2026-09-14.md), including the actual schedule and narrower base-two obstruction.
2. [Entropy draft](</Users/gotrevor/src/normal-numbers/docs/prime-lambert-affine-entropy-draft.md>) and [KB clarification](normal-numbers-normality-after-disjunctivity-2026-09-14.md).  Treat their asserted estimates as proof candidates to reconcile with the implemented argument.
3. The source modules named below.  Source definitions, not an old handoff's asymptotics, govern the current construction.

The operator should install a short attended override pointing here before starting a run.  `DIRECTION.md` currently selects G5 and also contains older scope restrictions that conflict with this expedition.  Preserve that history, but make the active objective unambiguous.  Read applicable local instructions and `JUDGE.md`; its historical campaign is not this campaign's task.

## 2. Freeze the sample before proving anything about it

Use K tending to infinity through sufficiently large multiples of 4.  Start from the implemented base-four schedule:

- `G_K = gridOf K (Sched.N K)`, with `Sched.N K = 100K²` and J=K+N.
- Atom set \(I_K=(\mathrm{Fin}(K^2+1))^K\), size \(H_K=(K^2+1)^K\); row dimension \(r_K=(K^2)^K\).
- \(P_K=\{n<X_K:n\bmod P_{0,K}=b_{0,K}\}\), using `Sched.X K`, `G_K.P₀`, and `G_K.b₀`.
- For n∈P_K, define \(k_{K,\alpha}(n)=(n-t_{K,\alpha})/d_{K,\alpha}\) and prove the exact identity \(n=t_{K,\alpha}+d_{K,\alpha}k_{K,\alpha}(n)\).  `GridParams.exists_mult_mul` supplies existence and the frozen multiplier residues.  Natural subtraction/division must not silently supply junk values outside its proved domain.
- Binary block length \(m_K=K/4\), resolution \(\eta_K=2^{-m_K}\).  This m_K is **not** `Sched.m K`, the much larger outer-scale exponent.

For arbitrary x∈[0,1), define

\[
u^x_{K,\alpha}(n)=\{4^{k_{K,\alpha}(n)}x\},\qquad
Z^x_{K,\alpha}(n)=\lfloor2^{m_K}u^x_{K,\alpha}(n)\rfloor.
\]

The law of the entire vector \(Z^x_K=(Z^x_{K,\alpha})_{\alpha\in I_K}\) is the pushforward of **one uniform choice of n∈P_K**.  Do not replace it by independent choices for each atom.  Each coordinate is the m_K-bit block beginning at zero-based position 2k.  Prove that dictionary against `digitOf`/`OccursAt`, with the standard terminating expansion convention at dyadic endpoints.

Record normalization, P_K nonempty, coordinate ranges, and the sanity bound
\(H_2(Z^x_K)\le\min(m_KH_K,\log_2|P_K|)\).  For the concrete instantiation, prove 0≤G4<1 or consistently use its fractional part.  Define finite Shannon entropy with the zero-mass convention explicitly; use an existing library when it fits, without a new general information-theory project.

**First live frontier:** a precisely defined sample and the finite capture inequality in §3.  A graph containing only declarations with unproved hypotheses is preparation, not the expedition's result.

## 3. The finite mathematical engine to extract

### A. Keep the exact transported sample, not just orbit containment

`gridFrame_propA` concludes membership in the image of the whole orbit closure.  That loses the particular sample needed for an entropy argument.

Extract from [G4Transport](</Users/gotrevor/src/normal-numbers/src/NormalNumbers/G4Transport.lean:207>) and [G4Frame](</Users/gotrevor/src/normal-numbers/src/NormalNumbers/G4Frame.lean>) the pointwise identity, for x=G4 and n∈P_K,

\[
F_K(n)=A_Ku^{G4}_K(n)+\theta_K-\gamma_K\quad\text{in }(\mathbb R/\mathbb Z)^{r_K}.
\]

The existing proof contains the relevant equality inside `coe_sum_dilatedTailB` and `propA_of_progression`.  Expose it without changing the old endpoint.  This identity is arithmetic-specific; it is not available for an arbitrary counterexample x.

### B. Generalize the geometry to a collection of joint boxes

For any finite collection \(\mathcal B\) of quantized **joint** vectors, let E_K(ℬ) be the translated A_K-image of the union of their closed dyadic boxes.  Then

\[
Z^{G4}_K(n)\in\mathcal B\ \Longrightarrow\ F_K(n)\in E_K(\mathcal B).
\]

Derive an explicit bound of the form

\[
\mathrm{Haar}\bigl((E_K(\mathcal B))_{\varepsilon\eta}\bigr)
\le |\mathcal B|\,\eta^{(1-\varepsilon)r_K}
       \exp(C_0(H_K+r_K\sqrt K)). \tag{G}
\]

The constant and finite side conditions must be proved, not assumed from this display.  Handle the empty collection separately and retain endpoint-safe closed covers.

Reuse `G4TubeVolume`, `G4TubePiece`, `G4GridTube`, `G4Ellipsoid`, and `G4Tensor`.  The current cover is a product cover of the full orbit closure, with a `Bs.card ^ H` factor.  Here it must become **the number of allowed joint boxes**.  Replacing ℬ by the Cartesian product of its coordinate projections can erase the entropy saving.  Retain average-coordinate distance and the determinant bound; an enclosing coordinate box loses the required dimension dependence.

### C. Prove a positive-mass capture inequality

Let S_K be the existing small-prime vector.  Write

\[
a_K=\mathbb E_{n\in P_K}d_{\rm av}(F_K(n),S_K(n)),\qquad
\rho_K=\varepsilon_K\eta_K.
\]

Suppose every nonzero Fourier character in the degree-D box has sample average of modulus at most q_K, and smoothing a bounded 1/ρ_K-Lipschitz test has uniform error κ_K and nonconstant coefficient mass at most Λ_K.  Prove

\[
\Pr[Z^{G4}_K\in\mathcal B]
\le \mathrm{Haar}\bigl((E_K(\mathcal B))_{\rho_K}\bigr)
  +\frac{a_K}{\rho_K}+2\kappa_K+\Lambda_Kq_K. \tag{C}
\]

Use the bump \(1-\min(1,d_{\rm av}(y,E)/\rho_K)\).  It is 1 on E and supported in the tube.  Its sample expectation is at least the captured mass minus a_K/ρ_K; its Haar expectation is at most the tube volume.  This is a finite unconditional expectation comparison, not an estimate conditional on membership in ℬ.

The existing `Frame.test` and smoothing statements are specialized to the full orbit image.  Extract the bounded-Lipschitz or arbitrary-compact-set version from `G4Jackson` and `G4SeparatingTest`, then recover the old version as an instance.  A data-dependent choice of ℬ is legitimate only because the Fourier and approximation budgets are uniform in that choice.  Do not condition the prime estimate on the selected low-information event.

## 4. Close the entropy budget against the implemented schedule

The [actual schedule](</Users/gotrevor/src/normal-numbers/src/NormalNumbers/G4ScheduleParams.lean>) uses

\[
\begin{aligned}
T_K&=100K^2H_K,&m_1&=1000\,8^K K^{2K+1},\\
m_2&=8K^2,&R_K&=2^{2^{m_1}},\\
Y_K&=2^{2^{m_1+m_2}},&X_K&=Y_K^{100},&M_c&=100000\,T_Km_1.
\end{aligned}
\]

Use `G4ScheduleFar`, `G4ScheduleBig`, and `G4ScheduleBudget` for its inequalities.  The old X-asymptotic draft is not the current schedule.  It is valid to choose K and then X_K; sending X to infinity at a fixed K without rechecking the estimates is a different operation.

Start with ε_K=1/K.  The existing Fejér error is

\[
\kappa_K\le\frac1{\varepsilon_K\eta_K\sqrt{D_K+1}}.
\]

The current `Dj K m_K = (16 K 2^{m_K})²` only gives a fixed 1/16 error under this choice.  **A proposed entropy replacement** is

\[
D_K=(16K^2 2^{m_K})^2,
\qquad \kappa_K\le\frac1{16K}.
\]

The displayed smoothing comparison is elementary; acceptance of this degree by the complete arithmetic budget is an obligation.  Recheck frequency-depth coverage, Λ_K≤(2D_K+1)^{r_K}, CRT truncation errors, and the small-prime decay together.  Also recover vanishing a_K/ρ_K from the actual remainder bounds; the old fixed 1/8 allowances do not establish it.  Keep the existing finite-degree CRT transfer, rather than restoring the removed sieve requirement.

The desired quantitative error is

\[
e_K:=a_K/\rho_K+2\kappa_K+\Lambda_Kq_K=o(K^{-1/2}).
\]

For any finite probability law with entropy at most (1−δ)m_KH_K, its information threshold set satisfies

\[
\Pr[Z\in\mathcal B]\ge\frac\delta{2-\delta},\qquad
|\mathcal B|\le2^{(1-\delta/2)m_KH_K},\quad 0<\delta<1.
\]

This uses Markov's inequality on −log₂ mass, not ergodicity or a high-probability typical-set theorem.  Combine it with (G) and (C).  Since r_K/H_K→1, the proposed conclusion is:

**E0, qualitative target:**
\[
\frac{H_2(Z^{G4}_K)}{m_KH_K}\longrightarrow1.
\]

**E1, quantitative target:** there exist C and K₀, independent of K, such that for every admissible K≥K₀,
\[
H_2(Z^{G4}_K)\ge m_KH_K-C H_K\sqrt K.
\]

Prove or refute the claimed rate separately from E0.  E0 is sufficient to continue toward fixed-word sampled frequencies.  If the chosen rate or schedule fails, preserve the exact failed assertion and justify any replacement; an asymptotic claim must not quietly acquire K-dependent constants.

## 5. State exactly which frequencies entropy controls

For each fixed binary word length ℓ≥1, let Q^x_{K,α,h,ℓ} be the law, over uniform n∈P_K, of the ℓ-bit word beginning at

\[
j=2k_{K,\alpha}(n)+h,\qquad 0\le h\le m_K-\ell.
\]

Use entropy subadditivity and partitions into disjoint ℓ-blocks, separately for each offset modulo ℓ.  Bound the boundary bits explicitly.  The target is

\[
V^x_{K,\ell}:=\frac1{H_K(m_K-\ell+1)}
 \sum_{\alpha,h}\|Q^x_{K,\alpha,h,\ell}-U_\ell\|_{\rm TV}
 \longrightarrow0\quad(x=G4). \tag{S}
\]

E1 should give a bound O_ℓ(K^(−1/4)); E0 should suffice for convergence without that rate.  Check the finite entropy-to-distance inequality rather than assuming a particular library's logarithm convention.

The mixture of these laws also tends to U_ℓ.  Its exact position weights are

\[
w_{K,\ell}(j)=
\frac{\#\{(n,\alpha,h):n\in P_K,\ 0\le h\le m_K-\ell,
\ 2k_{K,\alpha}(n)+h=j\}}
{|P_K|H_K(m_K-\ell+1)}.
\]

Keep repeated positions with their multiplicities.  This is not uniform counting on the union of sampled positions.  Nor does mixture uniformity imply (S): different biased marginal laws can cancel in a mixture.  Prove and name the implications actually earned:

```text
joint entropy E0  ->  average marginal total variation (S)
                 ->  sampled mixture word frequencies
                                     ?
                           ordinary word frequencies
```

Ordinary frequency means all starting positions j<L, divided by L.  Prove the O(ℓ/L) boundary comparison with the existing prefix-count definition, and use the unchanged `NormalNumbers.IsNormal 2 x` as the normality endpoint.

## 6. The frontier: a transfer theorem or a counterexample

Freeze the following as distinct propositions over the **same fixed sampling family**, with all limits over the same admissible K:

- **T_E:** for every x∈[0,1), E0 for Z^x_K implies `IsNormal 2 x`.
- **T_S:** for every x∈[0,1), (S) for every fixed ℓ implies `IsNormal 2 x`.
- **T_mix:** for every x∈[0,1), uniform sampled mixture frequencies for every fixed word imply `IsNormal 2 x`.

A proof of T_mix would imply T_S and T_E.  A counterexample to T_mix alone does **not** refute T_E: it must satisfy the stronger entropy premise to do that.  **T_E is the primary generic transfer target**, because it retains the strongest proposed arithmetic output.  The variants with weaker premises are diagnostic probes, not interchangeable headlines.

### Counterexample branch

Try to construct one fixed binary expansion that is nonnormal yet satisfies the actual premise of the target being refuted.  A different digit string at each K is not a witness.

Start by computing or bounding the actual support, multiplicities, and overlaps of w_K,ℓ and of the joint blocks.  If the support lies in [0,L), then

\[
\|w_{K,\ell}-U_{[0,L)}\|_{\rm TV}
\ge1-\frac{|\operatorname{supp}w_{K,\ell}|}{L}.
\]

This can rule out a proposed comparison of **position measures**.  It is not itself a counterexample to T_E or even T_mix.  Likewise, per-scale sparsity does not establish density zero of the cumulative union across scales.

A candidate construction is to realize rich patterns on the sampled blocks while imposing an ordinary-frequency bias elsewhere.  Before accepting it, prove compatibility of overlapping prescribed bits, control the distribution over the one common n, and make the construction work across all sufficiently large admissible scales.  “Choose independent words at each sampled position” ignores shared digits.  A probabilistic existence argument is useful if proved; identify separately whether an explicit or computable witness has been obtained.

Sanity checks should include all-zero and periodic digit strings, exact finite product laws for the entropy helper, and finite overlap graphs.  Small-K analogues test definitions and mechanisms, not an asymptotic theorem outside their valid parameter regime.  Do not attempt brute-force evaluation of the enormous actual X_K or G4 digit positions.

### Positive arithmetic branch

If the generic transfer fails, isolate an additional property of G4 that defeats that counterexample.  Two concrete directions deserve tests before large formalization work:

1. **Average a proved family of admissible arithmetic samplers.**  Vary frozen residues or translated grids only where exact transport and all estimates remain uniform.  Compute the resulting position weights.  An output translation θ−γ does not grant arbitrary input residues, and removing one congruence may leave the other atoms' restrictions intact.
2. **Synchronize construction scales with an ordinary biased subsequence.**  Determine which ranges of X the arithmetic estimates really permit at a given K.  The selected X_K grow extremely rapidly; control only on that sequence does not automatically control every ordinary prefix length.  Preserve the prime-cutoff and remainder constraints when changing the scale.

For either direction, name the proposed additional property independently of normality, prove the implication it supplies, and explain why the counterexample fails that property.  Do not call a restatement of “ordinary nonnormality forces a sampled entropy deficit” a new mechanism.  Once E0 is proved for this fixed x, such a sufficient bridge may simply be normality in another form.  A conditional wiring theorem is useful, but only a new estimate, a construction, or a genuine reduction advances that crux.

The earlier low-entropy typical-set shortcut is already refuted by a mixture of a fair process and an all-zero process.  It is preserved in the entropy draft; do not repeat that route or silently add ergodicity of G4.

## 7. Expedition organization and mathematical checkpoints

Use Fable as lead, with bounded lower-effort work for finite probability lemmas, parameter inequalities, and probes.  Conserve Astra; no automatic escalation to it.  Use the existing treadmill if this brief is dispatched as a launch instruction, not a new orchestration system.

Suggested ownership once the shared definitions are frozen:

- **Lead/integrator:** exact sampling definitions, concrete arithmetic instantiation, transfer target, and final integration.
- **Finite-probability worker:** information-set lemma, entropy subadditivity/block partitions, and finite entropy-to-TV estimate.
- **Geometry worker:** arbitrary joint-box cover and positive-mass separating-test lemma, reusing the existing determinant and Fejér machinery.
- **Counterexample worker when a slot is available:** actual sampling support/collisions and one fixed-sequence construction, with no edits to shared definitions.

This is a suggestion for disjoint work, not a requirement to keep every slot occupied.  One writer per shared file.  Prefer adding reusable lemmas and recovering old theorems as instances over copying entire G4 modules.  Choose the smallest coherent decomposition.

The first checkpoint must include either a proved finite capture inequality, a proved load-bearing component of it, or an exact refutation exposing the needed repair.  Start the sampler/counterexample analysis as soon as definitions are fixed; do not postpone all frontier work until every entropy helper is polished.

At each lap record only:

1. Which mathematical statement was proved, refuted, or narrowed, and the source declaration or witness.
2. Which actual bottleneck moved, including any new assumptions or changed quantifiers.
3. The next bounded test and who owns it.

After two laps stalled on the same assertion without a new estimate or counterexample, use a fresh Fable review of the exact statement and raw evidence.  That review may decompose the proof, isolate a missing premise, or record a refutation.  It may not silently replace the expedition with Ω, another base, or a different familiar theorem.

## 8. Completion, preservation, and handoff

The intended result is an unconditional G4 sample-entropy/frequency theorem **plus a resolved primary transfer question**: a proof, or a counterexample satisfying its exact premise.  If an entropy candidate fails, a precise refutation and repaired frontier is also a valid research outcome.  An unresolved bridge must remain visibly unresolved; a conditional normality corollary is not completion of normality.

Keep conjectures as explicit `Prop` interfaces and conditional theorems.  In-progress proof holes are permissible and must stay visible.  A refuted assertion should receive a named negation theorem beside its replacement when feasible; otherwise preserve the full mathematical counterexample with its formalization status.  No new trusted axiom may turn a candidate into a completed claim.

Preserve, by name and statement, `G4.isDisjunctive_four`, `G4.isDisjunctive_two`, `G4.isDisjunctive_base`, and `PrimeLambert.primeSumAtBase_eq_primeLambertAtBase`, as well as the existing meanings of `primeLambert`, `primeLambertFour`, `IsDisjunctive`, and `IsNormal`.  G2's absolute-mass obstruction is not a universal impossibility theorem, but extending G2 is outside this expedition.

Before the first Lean build, follow the shared-store check in `CLAUDE.local.md` and its imported guidance.  Build relevant modules, then the integrated project, and inspect the settled headline dependency chain once per batch.  Test the final arithmetic statement against a literal rendering of the sample law and prime sum, as in the overnight review.  Routine warnings, declaration totals, and proof-hole counts are not progress metrics.

Configure completion around the chosen target statements and dependencies, not all unfinished declarations in the repository.  The overnight run's unrelated Mahler and oscillation holes must not cause another completed campaign to invent a new objective.  If the existing stop mechanism cannot express the required condition, surface that specific operator issue rather than altering the mathematics.

Commit integrated work through `git-safe`, preserve unrelated changes, and leave a durable handoff.  No public claims, outreach, PR discussion, or novelty campaign is authorized by this brief.

The final handoff should state, in ordinary language: what is now known about G4's digits; which transfer was proved or refuted; the exact surviving arithmetic gap; and the strongest justified next move.  Lead with the mathematics.  Normality earns its name only when ordinary frequencies for every fixed word have actually been proved.
