<!-- Moved from the 2026-10-05 session scratchpad; scripts in experiments/persistence/, papers in ~/personal/papers/. -->
# Persistence, nonzero even targets: can we run Fonga + Brier et al.? 🔢

**Verdict: infeasible as a direct run (~90% confident).**  The finite procedure is real.  But its dominant cost is the `12^(k+1)` residue enumeration in Brier et al.'s sieve, and Fonga's bound does not touch it.  It actually *weakens* their first filter, by a factor of `tmax+1` (about 30-80).  Even after symmetry reduction, stage 1 alone is ~10^18 (δ=2) to ~10^24 (δ=6, 8) modular checks.  The lifting stages multiply that further.  Brier et al. called it "prohibitive", and the numbers below agree.

Sources: Brier, Clavier, Gutsche, Naccache, arXiv:2110.04263 (stored `~/personal/papers/2110.04263.pdf`); Fonga, arXiv:2608.27802 v1, 28 Aug 2026 (`~/personal/papers/2608.27802.pdf`).  Both were read in full via `pdftotext` (text in this dir: `brier.txt`, `fonga.txt`).

## 1. Definitions

- `S(n)` = product of the decimal digits.  **Terminal digit** `Δ(n)` = the single digit the iteration `n, S(n), S²(n), …` reaches.  Persistence = the number of steps to reach it.
- **Backward graph** `A_δ`: start from δ.  For each `s ∈ V_δ` and each `x` with `S²(x) = s`, add the vertex `y = S(x)` and the edge `s → y`.  Every vertex is a 7-smooth integer, so it is automatically a digit product.  If `A_δ` is finite, its longest path bounds the persistence of every number with target δ.

## 2. What Brier et al. proved, and how

- **Theorem (2110.04263):** Δ ∈ {1,3,7,9} ⇒ persistence ≤ 1, and Δ = 5 ⇒ persistence ≤ 5.
- **Shape of the reduction:**
  1. They guess a finite candidate graph `B_δ ⊆ A_δ`.
  2. They prove it closed: `s ∈ U_δ, S²(x) = s ⇒ S(x) ∈ U_δ`.
  3. Write `y = S(x)`.  Then `S(y) = s`, so the non-1 digits of `y` form one of the finitely many digit factorizations of `s`.  Arbitrarily many 1s are allowed.
  4. With `y = (10^L − 1)/9 + Σ (d_i − 1)10^{a_i}` and `y = 2^t 3^u 5^v 7^w`, each factorization gives one exponential Diophantine equation: `10^{a0} − 1 + Σ 9(d_i−1)10^{a_i} = 2^t 3^{u+2} 7^w`.  The `a_i` are distinct and below `a0`.
  5. For odd δ, `t = 0`.  The 5-power is handled separately (§3.1 of the paper), giving 44 equations with at most 8 terms.
- **Resolution: a modular sieve, not Baker theory.**
  - **Stage 1:** enumerate all `a mod 12` tuples (`12^(k+1)` of them).  Check `LHS ≡ 3^u 7^w` mod `m12 = (10^12−1)/189 = 11·13·37·101·9901`.  On that modulus `10^a` depends only on `a mod 12`, and `u mod 9900`, `w mod 900` are free.
  - **Lifting:** lift to `m24`, then `m48`, using the primes 73, 137, 99990001, 17 and 9999999900000001 to learn `u` and `w` modulo larger orders (their Tables 1-2).
  - **Final step:** work mod `2^9·5^6` to decide, for each `i`, whether `a_i < 12` or `a_i ≥ 12`.
  - Every surviving candidate was either a known vertex or violated the distinctness/ordering condition (R).  This is their Appendix B.
- **Why even δ failed for them (§5):**
  1. The `2^t` on the right-hand side has unbounded `t`, which destroys the 2-adic filtering.  This is their Conjecture 2.
  2. The size: `12^30 ≈ 2^107` tuples for the *easiest* even target.  Their words: "totally out of reach", "prohibitive", and "within the reach of Grover's algorithm on a quantum computer".

## 3. What Fonga bounds

- **Object:** `A_10(ν)` = all decimal integers with exactly `ν_d` copies of each digit `d ∈ 2..9`, no 0, and any number of 1s.  Fonga bounds `sup v_2(x)` over this infinite family.
- **Corollary 3.2 (explicit bound):** `v2(x) ≤ ⌊ρ·c^q + (c^q−1)/(c−1)·log2 B⌋`, where:
  - `c = log2 10`
  - `q = Σν_d`
  - `B = 1 + 9Σ(d−1)ν_d`
  - `ρ ∈ {3,2,1,0}`: 3 if ν₂ > 0; otherwise 2 if ν₆ > 0; otherwise 1 if ν₄ + ν₈ > 0; otherwise 0.

  The bound is exponential in `q`.  For our families it reaches 10^16 to 10^24, so it is useless in practice.
- **Theorem 4.1 (exact maximum):** a finite DFS from the least-significant digit computes the exact maximum.
  - The key fact (eq. 13): once a digit sits at position `r > v2(T)`, no later digit can change the valuation.
  - So only positions `≤ v2(partial sum)` branch.
  - This proves Brier's Conjecture 2.  I checked the argument and believe it is correct (~90%).
- **The finite procedure Fonga proposes (§5), per even δ:** for each `s ∈ U_δ` and each `n ∈ F(s)`:
  1. compute `tmax(D(n))`;
  2. for each `t ≤ tmax`, run the Brier sieve;
  3. check that every survivor lies in `U_δ`.

  Fonga explicitly does **not** run it ("beyond the scope of this paper").
- **Caveat on "finite algorithm":** the sieve always terminates, but it is only *conclusive* if every residue-class candidate eventually dies or resolves to a true solution.  That is a Hasse-principle-type property of exponential equations.  Bertók-Hajdu conjecture it in general but it is not proved (memory).  So running the procedure gives a proof only if it happens to close, as it did for odd δ.

## 4. Size of the computation (measured, this directory)

**Reproduction (`graphs.py`).** I enumerated every `2^a 3^b 7^c < 10^60`, and separately `< 10^200`, and built `B_δ`.  The result matches Brier's Table 3 exactly:

| δ | \|U_δ\| | families | max k+1 | hardest s | longest path ⇒ persistence bound |
|---|---|---|---|---|---|
| 2 | 33 | 1117 | 30 | 2^26·3^3 | **6** |
| 4 | 9 | 1062 | 32 | 2^23·3^7·7 | **5** |
| 6 | 84 | 6377 | 37 | 2^24·3^6·7^6 | **8** |
| 8 | 51 | 4774 | 45 | 2^39·3^3·7^2 | **6** |

So the prize theorem would actually be **"nonzero target ⇒ persistence ≤ 8"**, which is stronger than ≤ 11.  It is consistent with Smeets' class-representative table in the OEIS A003001 comments (max persistence 6/5/8/6 for final digits 2/4/6/8).

**Fonga tmax (`fonga_tmax.py`, Theorem 4.1 DFS).**
- The DFS reproduces Fonga's table: {4,4,7} → 7, {2,2,2,2,7} → 13, {2,2,4,7} → 15, {2,7,8} → 9.
- It agrees with an independent brute force on small families (`test_fonga.py`).
- Brier's Table 4 row "(4,7,8)" is a typo for {2,7,8}, since 4·7·8 = 224 ≠ 112.
- With a 20 ms/family budget in pure Python, the exact `tmax` finished for 2374 of 13330 families.
- Observed: the median `tmax` grows about 3q (q=9 → 37, q=18 → 57), and the maximum seen is 89.
- The DFS itself is exponential.  A C version with branch-and-bound is needed for the big families.  That is a sub-risk, but small next to the sieve.

**Stage-1 prototype (`stage1.py`, Brier Algorithm 1 adapted to `2^t`).**
- `|⟨3,7⟩ mod m12| = 8,910,000` out of `m12 = 5.29·10^9`, so the odd-target pass rate is 1.68·10^-3.
- **Correctness check:** the known solutions 98, 189 and 128421199872 all pass.
- **Family {8³,4,9²,7}** (s = 1161216, δ = 4):
  - 4.9·10^7 multiset-reduced tuples × 27 values of t
  - pass rate **4.6·10^-2** summed over t, which is 28× weaker than for odd targets
  - throughput 2.1·10^7 checks/s in numpy on one core
- **Totals.**  The tuple counts use the multiset reduction: identical digits give multisets of residues, `12·Π C(ν_d+11, 11)`.  For families whose `tmax` did not finish I assumed `tmax = 60`, which probably *underestimates* the large ones.

| δ | naive Σ12^(k+1) | multiset Σ | stage-1 checks (×(tmax+1)) | stage-1 survivors | naive lift to mod 24 (×2^(k+1)) |
|---|---|---|---|---|---|
| 2 | 10^32.5 | 10^16.5 | **10^18.3** | 10^15.5 | 10^22.6 |
| 4 | 10^34.6 | 10^19.4 | **10^21.2** | 10^18.4 | 10^26.0 |
| 6 | 10^40.1 | 10^22.1 | **10^23.9** | 10^21.2 | 10^30.3 |
| 8 | 10^48.7 | 10^22.2 | **10^24.0** | 10^21.2 | 10^31.5 |

- **Wall clock**, at an optimistic 10^9 checks/s/core (bitset membership in C):
  - stage 1 for δ = 2 is about 60 core-years;
  - δ = 4 is about 5·10^4 core-years;
  - δ = 6 and δ = 8 are about 3·10^7 core-years each.
- Lifting dominates after that.  Meet-in-the-middle on the `±` sign choices mod `10^12+1` cuts `2^(k+1)` to roughly `2^((k+1)/2)` per survivor.  Even so, δ = 2 stays around 10^19 operations.
- **Cheap part:** 63/19/125/116 families (δ = 2/4/6/8) are ≤ 10^6 tuples, and 796/149/2678/871 are ≤ 10^12.  The cost sits in a heavy tail: the many-small-digit factorizations of the leaf vertices.
- A proof needs **every** family of **every** vertex, so partial runs give no persistence theorem.

**Ideas that might change the order of magnitude** (untested):
- **(a)** Stage 1 depends only on `(a0 mod 12, W_r = Σ(d−1)·#{digits at residue r})`.  So stage 1 is a reachability DP over ≤ 12·m12 ≈ 6·10^10 residues, and each family costs minutes.  This kills the stage-1 cost but not the lifting, which needs actual tuples.
- **(b)** Fonga's eq. 13 pins `y mod 10^(t+1)` per DFS leaf.  All unpinned digits lie above position `t`, which gives `3^u 7^w mod 5^(t+1)` for free and removes pinned digits from the unknowns.
- **(c)** Chaffin's computation (OEIS A003001 comment, unverified by me): every 7-smooth `p` with `10^140 < p < 10^20000` contains a 0 digit.  So any missing vertex has **> 20000 digits** with ≤ 44 non-1 digits, and therefore has gaps of ≥ 444 ones.
  - That invites a Baker/Matveev cluster-by-cluster argument with LLL reduction (de Weger style) (memory).
  - The bound compounds over up to 45 clusters, and the branching across gap patterns probably explodes.
  - It is unclear whether this is effective in practice.
  - This is the only route I see that is a genuinely different *mechanism* and not a faster sieve.

## 5. Prior work / has anyone run it?

- **Forward citations of 2110.04263:** `papers followups` and the Semantic Scholar API both find exactly one, Fonga 2608.27802.
- **Web search:** found nothing else.  Nobody appears to have run Fonga's procedure.  Fonga is 5 weeks old and states the run is future work.
- **OEIS A003001 comments:**
  - Chaffin: the persistence-k digit products are all below 10^140 up to 10^20000.
  - Peters, 2023: a(12) > 2.67·10^30000.
  - Smeets: counts by final digit.
  - None of these attempt the even-target proof.
- **A121105** is just the trajectory of 679.  It is not relevant.

## 6. Lean angle (short)

- **Statement:** `∀ n, Δ n ≠ 0 → persistence n ≤ 8`.
- **Data:**
  - the four `U_δ` lists;
  - `F(s)` enumeration, which is decidable;
  - Fonga's Theorem 4.1, which is elementary (Lemma 2.2 plus the DFS recursion);
  - per family, a **sieve certificate tree**: nodes `(t, a mod M, u mod m_u, w mod m_w)`, with each leaf closed by a `decide`-able modular contradiction or an explicit `y ∈ U_δ`.
- **Size:** about the survivor count, 10^15+ leaves.  That is far beyond kernel or `native_decide` checking.
- **The realistic Lean shape:** a verified *checker* (the sieve proved sound in Lean) run compiled, trusting `native_decide`.  This only makes sense after an algorithmic breakthrough shrinks the tree.
- The odd-target theorem (44 equations, ≤ 8 terms) would be a feasible Lean certificate, but it is a known result.

## 7. Difficulty check

- **Proved implications:**
  - odd targets (Brier);
  - bounded `v2` on families (Fonga);
  - `B_δ ⊆ A_δ`, with longest paths 6/5/8/6;
  - numerically, no missing vertex below 10^20000 (Chaffin, an unverified computation).
- **Unproved premise:** closure (17) of `B_δ` for δ ∈ {2,4,6,8}.
- **Mechanism offered:** the Brier sieve with Fonga's `t`-range.
  - It is sound and finite, but its conclusiveness rests on a Hasse-type principle.
  - It costs ~10^18 to 10^24 stage-1 checks plus lifting.
  - No mechanism is known that makes it run.
  - The plausible alternative is Baker + LLL on the >20000-digit ones-heavy tail.  It is untested, and I am not confident it is tractable (~25%).
- **Target digit 0 stays open, and is the real conjecture.**
  - `A_0` is infinite: every 7-smooth number containing a 0 digit is a vertex.  Brier's footnote 9 says "d = 0 can not be treated by our method".
  - All known persistence-11 numbers end in 0.
  - Bounding persistence there needs the finiteness of 7-smooth zeroless numbers.  Even "2^86 is the last zeroless power of 2" is open (memory).
  - So even full success here proves "≤ 8 for nonzero targets" and leaves Conjecture A open.

## Files

All in `/private/tmp/claude-501/-Users-gotrevor-personal/e3e9b974-4f0e-4526-9fc8-f69c666eadcd/scratchpad/persistence/`:

- `graphs.py`: B_δ rebuild and family enumeration → `families.json`
- `fonga_tmax.py`: Theorem 4.1 DFS, Corollary 3.2 bound, and sizes → `family_metrics.json` (run: 4m18s)
- `stage1.py`: Brier Algorithm 1 with `2^t`
- `test_fonga.py`: pytest with paper known answers, the Table 3 reproduction, and the brute-force cross-check (4 pass)
