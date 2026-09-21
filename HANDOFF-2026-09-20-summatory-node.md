# HANDOFF 2026-09-20 — the summatory node lap (`G4WiringSummatory.lean`)

Branch `wip/g5-prime-subset`.  Executed `KICKOFF-2026-09-20-summatory-node-lap.md` exactly:
new file `src/NormalNumbers/G4WiringSummatory.lean` (1701 lines), pure addition — `git diff a435c2e`
deletes no line of any existing file.

## Result

**The file is sorry-free and all three headline theorems are axiom-clean**
(`[propext, Classical.choice, Quot.sound]`, `#print axioms` at the bottom of the file):

* `roughIndependenceAt_two_of_summatory : RoughSummatory h → RoughIndependenceAt h 2`
* `parityDiscrepancy_of_summatory : h ≠ 0 → ¬ ChowlaSector h → RoughSummatory h → ParityDiscrepancy h`
* `isNormal_G4_of_summatory : (∀ h ≠ 0 off Chowla, RoughSummatory h) → (Chowla sector WindowDecay)
   → SiteDecayFull → IsNormal 4 (primeLambertAtBase 4)`

So **off the Chowla sector the whole G₄ window law now rests on ONE analytic input**, the frozen
Selberg–Delange-with-shifts node `RoughSummatory h`.  All ratified statements (`roughProd`,
`roughClassSum`, `sdExponent`, `sdMain`, `RoughSummatory`, `roughClassSum_zero_add_one`,
`sdExponent_Icc_succ`, `roughPrefixMean_eq_classSum`, `roughSiteMean_eq_classSum`, and the three
wirings) are in the file verbatim.

## How the two wirings go through

Write `L = log N`, `x = log 2 / L`, `z_j = e(h/4^j)`, `κ_s = sdExponent h s`, `q^j = 4^{-j}`.

**Common core (`node_winDiff`, `sdMain_diff_eq`, `node_winApprox`, `summatory_means_approx`).**
A window quantity is the node at `2N` minus the node at `N`.  Summing both parity classes,
`2(main(2N) − main(N))/N = c_s L^{κ_s}(2(1+x)^{κ_s} − 1)`, and
`‖2(1+x)^κ − 2‖ ≤ 4‖κ‖x` (`norm_ofReal_one_add_cpow_sub_one_le`).  The node's own error, moved from
`2N` to `N`, costs a factor `≤ 3` (`Re κ ≤ 0`, `log 2N ≥ log N ≥ 1`).  Result, with
`A := 6C + 16πB|h|` and the SAME `A` for both families because `‖κ_{\{k\}}‖ ≤ 4π|h| 4^{-k}`:

* `‖roughPrefixMean N h k − c_{[1,k]} L^{κ_k}‖ ≤ (A/L) L^{Re κ_k}`
* `‖roughSiteMean N h k 2 − c_{\{k\}} L^{z_k−1}‖ ≤ (A 4^{-k}/L) L^{Re(z_k−1)}`
* and the parity-class *difference* clause (main terms cancel identically), same bounds.

**Wiring 1.**  `c(J) := c_{[1,J]} / ∏_{j≤J} c_{\{j\}}`.  Writing `S_j = c_j L^{z_j−1}(1+w_j)` with
`‖w_j‖ ≤ A4^{-j}/(δL)`, the prefix/product discrepancy is
`(P_J − c_{[1,J]}L^{κ_J}) − c_{[1,J]}L^{κ_J}(∏(1+w_j) − 1)`, of norm `≤ (A + 2AB/3δ)/L · L^{Re κ_J}`
(`prod_one_add_le` + `norm_prod_sub_prod_rel` from `G4WiringRough`).  The RHS needs
`∏_{j≤J}‖S_j‖ ≥ δ' L^{Re κ_J}` uniformly in `J`: `prod_Icc_split_lower` (new) splits at a cut `j₀`
chosen by `exists_geom_cut` — a crude `δ/2` bound below the cut, Weierstrass `1 − Σ ε_j ≥ 1/2` above.
`∏_j L^{Re(z_j−1)} = L^{Re κ_J}` is `prod_rpow_sdExponent` / `prod_cpow_sdExponent`.

**Wiring 2.**  `parityDisc N j r = c_o Σ_e − c_e Σ_o = (N/2)(Σ_e − Σ_o) + ((c_o−c_e)/2)(Σ_e+Σ_o)`;
`|c_o − c_e| ≤ 1` is now an exact count (`card_parity_Ico`:
`2·#{n ∈ [a,b) : n ≡ t} + [b ≡ t] = (b−a) + [a ≡ t]`).  `Σ_e − Σ_o` is the node's parity-class
difference, whose main terms cancel **exactly** — this is the clause that dissolves the bootstrap
circularity.  The RHS is converted by
`fullSiteMean − halfAvg·roughSiteMean = ((z_j−1)/2)(Σ_e − Σ_o)/N` (`fullSiteMean_sub_halfAvg_mul`),
giving `‖fullSiteMean N h j‖ ≥ (1 − (2π|h| + B+1 + KA)4^{-j}) L^{Re(z_j−1)}` and `≥ p₂ L^{Re(z_j−1)}`;
the same split lemma gives `∏_{j≤J}‖fullSiteMean‖ ≥ δ₂ L^{Re κ_J}` uniformly in `J`.  The additive
`N/2` is absorbed honestly: `Re κ ≥ −4π|h|` (bounded, `J`-independently) and
`(log N)^{m+1} ≤ c·N` eventually (`eventually_rpow_log_le`, `log_le_of_rpow_le`).

**The `j > windowJ N` range is elementary and is now proved** (`parityDisc_tail_small`), not assumed.
`ParityDiscrepancy`'s site clause quantifies over ALL `j ≥ 1`, where the node is silent for
`j > windowJ N`.  There nothing is needed: `tail_log_le` shows
`(log₂ N)·(log₂(2N+j)) ≤ 4^j` for `j > windowJ N` (from `Nat.lt_pow_succ_log_self`,
`2N+j ≤ 2N·2^j`, `j ≤ 2^{j−1}`), hence every phase is within `8π|h|/log N` of `1`;
`parityDisc` of a constant vanishes (`norm_parityDisc_tail`) and `‖fullSiteMean N h j‖ ≥ 1/2`.

## What resisted / what is new machinery

Nothing resisted to the point of a sorry.  Two things were more work than the kickoff anticipated:

1. The `∀ j ≥ 1` (not `j ≤ windowJ N`) quantifier in the frozen `ParityDiscrepancy`.  Handled by the
   new elementary tail block above.  Worth remembering: any future node-shaped statement should be
   checked against the *quantifier range* of the target, not just its shape.
2. Uniform-in-`J` product lower bounds appear three times (site constants, rough site means, full
   site means).  They are now one reusable lemma pair, `exists_geom_cut` + `prod_Icc_split_lower`
   (with `prod_ge_one_sub_sum` on top of `G4WiringRough.one_sub_sum_le_prod`).

## Does the probe's parity-class clause deserve a sharper test?  **Yes.**

`RoughSummatory` asserts the SAME constant `c_s` on both parity classes.  Wiring 2 uses this
**exactly** — the whole parity node is the statement that the two class main terms cancel with no
residue, so an error in this clause is not absorbed anywhere.  Probe 11 only tested it to within the
expected `O(1/log M)` scale term (prefix parity ratios `0.928 / 0.961 / 1.051` at `h = 1/3/5`), i.e.
the clause is *consistent, not sharply tested*.

Concrete test to run: measure `R_s(M, a=0)/R_s(M, a=1)` at two scales `M` and `4M` and check the
deviation from `1` **shrinks like `1/log M`** rather than tending to a constant `≠ 1`.  If it tends
to a constant `≠ 1`, the node must be restated with class-dependent constants `c_s^{(a)}` plus
`|c_s^{(0)} − c_s^{(1)}| ≤ C/log M`; Wiring 2 then picks up one extra error term of exactly that
size and goes through unchanged (Wiring 1 is untouched, it only ever uses the class SUM).

## Next crux

The only open obligation off the Chowla sector is now `RoughSummatory h` itself: Selberg–Delange
with shifts for `∏_{j∈s} e(h ω_{>2}(m+j)/4^j)` summed over a parity class.  The natural next lap is
to split it into (a) the Dirichlet-series/Landau–Selberg–Delange input for a single shift set `s`
on the full range, and (b) the parity-class refinement (a character-twist by `χ_{mod 2}`, i.e. the
same series over odd `m`), which is where the equal-constant clause lives.
