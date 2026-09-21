# KICKOFF 2026-09-20 — the fixed-K question, settled: `windowK` and the o(1) crux `PrefixDecay`

Branch `wip/g5-prime-subset`.  Engine Opus/low.  New file `src/NormalNumbers/G4WindowK.lean`, importing
`NormalNumbers.G4WiringCRT` and `NormalNumbers.G4FarTail`.  **Do not change any existing statement**; add new ones.
Operator: Ren, attended; fired under Trevor's "keep going!" (2026-09-20).

## Why

`HANDOFF-2026-09-21-summatory-split.md` asked whether the G₄ wiring can run with a FIXED number of sites `K`
instead of `k ≤ windowJ N = ⌊log₂log₂N⌋ + 1`.  Probe 13 (`probes/window_truncation.py`, data
`probes/data-2026-09-20-window-truncation.txt`) answers: **no for fixed K, yes for `K ≈ log₂log₂log₂N`**.  The
`K`-site and `J`-site window means differ by an L¹ tail `𝔼_n ‖∏_{K<j≤J} f_j − 1‖ ≤ 4π|h|·(avg ω on the window)·4^{-K}/3`;
measured `|W_K − W_J| = 0.33 / 0.10 / 0.023 / 0.005` at `K = 1..4` (`h = 1`, `N = 2^24`), scaling like `4^{-K}` and
NOT shrinking with `N` (`0.030 → 0.026 → 0.023` at `K = 3` over `N = 2^16 → 2^24`).  So the tail must be killed
by `K → ∞`, but only through the *average* of `ω` (`≈ log log N`), not its maximum (`≈ log N`) which is what
`windowJ` was built for.  Hence the schedule can drop from double-log to **triple-log** in `N`.

Second, and the real point: for **decay** (which is all `WindowDecay` needs) nothing forces an asymptotic.  The
crux in its cleanest form is the o(1) statement `PrefixDecay h` below: partial sums of the full phase product
`∏_{j≤k} e(h ω(m+j)/4^j)` are `o(M)`, uniformly for `k ≤ windowK M`, for every `h ≠ 0` - **no sector split**,
no main terms, no constants, no rate.  Everything in `G4WiringSummatory`/`G4SummatorySplit` remains valid as the
SD-sector *asymptotic* route; this file adds the minimal *decay* route beside it.

## Vocabulary

`G4WiringCRT.lean`: `ePhase`, `truncTail J n = ∑_{j<J} ω(n+j+1)/4^{j+1}`, `fullWindowMean N J h`, `windowJ`,
`WindowDecay`, `isNormal_G4_of_windowDecay`, `norm_ePhase_sub : ‖ePhase a − ePhase b‖ ≤ 4π|a − b|`,
`tail_error_uniform` (its proof is the template for `window_tail_tendsto_zero`), `tendsto_windowJ`.
`G4FarTail.lean`: `sum_omegaR_add_le : ∑_{n∈P} ω(n+ρ) ≤ |P|·log((X+ρ)(log(X+ρ)+1)/|P|)/log 2` for
`P ⊆ range X` - use it with `P = Ico N (2N)`, `X = 2N`, `ρ = j`: the window average of `ω(n+j)` is
`≤ log(2(1+j/N)... ) ≲ log₂ log N + O(1)`.

## The ratified new statements (verbatim; only their proofs are yours)

```lean
/-- The triple-log site schedule: `2^{windowK N} > log₂ log₂ N`, so `4^{windowK N} > (log₂ log₂ N)²`. -/
def windowK (N : ℕ) : ℕ := Nat.log 2 (Nat.log 2 (Nat.log 2 N)) + 1

theorem windowK_le_windowJ (N : ℕ) : windowK N ≤ windowJ N
theorem windowK_mono : Monotone windowK
theorem tendsto_windowK : Tendsto windowK atTop atTop

/-- Dropping sites `K < j ≤ J` costs the L¹ tail of the phase, by the Lipschitz bound on `ePhase`. -/
theorem norm_fullWindowMean_sub_le (N : ℕ) (h : ℤ) (K J : ℕ) (hK : K ≤ J) (hN : 0 < N) :
    ‖fullWindowMean N J h - fullWindowMean N K h‖
      ≤ 4 * Real.pi * |(h : ℝ)|
          * (∑ n ∈ Finset.Ico N (2 * N), ∑ j ∈ Finset.Ico K J, omegaR (n + j + 1) / (4 : ℝ) ^ (j + 1)) / N

/-- The tail is `o(1)` along `K = windowK N`: the window average of `ω` is `O(log log N)` (`sum_omegaR_add_le`)
while `4^{windowK N} ≥ (log₂ log₂ N)²`. -/
theorem window_tail_tendsto_zero (h : ℤ) :
    Tendsto (fun N : ℕ => ‖fullWindowMean N (windowJ N) h - fullWindowMean N (windowK N) h‖) atTop (𝓝 0)

/-- **Node N0′**: window decay along the triple-log schedule. -/
def WindowDecayK (h : ℤ) : Prop :=
  Tendsto (fun N => fullWindowMean N (windowK N) h) atTop (𝓝 0)

theorem windowDecay_of_windowDecayK {h : ℤ} (hK : WindowDecayK h) : WindowDecay h

theorem isNormal_G4_of_windowDecayK (hW : ∀ h : ℤ, h ≠ 0 → WindowDecayK h) :
    IsNormal 4 (primeLambertAtBase 4)

/-- Partial sums of the full `k`-site phase product. -/
noncomputable def fullPrefixSum (h : ℤ) (k M : ℕ) : ℂ :=
  ∑ m ∈ Finset.range M, ePhase (h * truncTail k m)

/-- **The crux in o(1) form, no sectors**: Elliott-type decay for the `ω`-twists
`∏_{j≤k} e(h/4^j)^{ω(m+j)}` at `k` shifts, uniformly for `k ≤ windowK M`, for every `h ≠ 0`. -/
def PrefixDecay (h : ℤ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ M : ℕ in atTop, ∀ k, 1 ≤ k → k ≤ windowK M → ‖fullPrefixSum h k M‖ ≤ ε * M

theorem fullWindowMean_eq_prefixSum (N J : ℕ) (h : ℤ) :
    fullWindowMean N J h = (fullPrefixSum h J (2 * N) - fullPrefixSum h J N) / N

theorem windowDecayK_of_prefixDecay {h : ℤ} (hP : PrefixDecay h) : WindowDecayK h

/-- **Headline**: G₄ is normal in base 4 if the `ω`-twist correlations decay at triple-log many shifts. -/
theorem isNormal_G4_of_prefixDecay (hP : ∀ h : ℤ, h ≠ 0 → PrefixDecay h) :
    IsNormal 4 (primeLambertAtBase 4)
```

## Leaves, in order (commit a compiling skeleton with named sorries FIRST)

1. `windowK` facts: `Nat.log` monotone (`Nat.log_mono_right`), `Nat.log 2 (Nat.log 2 N) ≥ Nat.log 2 (Nat.log 2 (Nat.log 2 N))`
   since `Nat.log 2 m ≤ m`; `tendsto_windowK` from `Nat.log` → ∞ (mirror `tendsto_windowJ`).
2. `norm_fullWindowMean_sub_le`: `truncTail J n − truncTail K n = ∑_{j∈Ico K J} ω(n+j+1)/4^{j+1}` (`Finset.sum_Ico_consecutive`
   or `Finset.range_eq_Ico` + `Finset.sum_Ico_eq_sub`), then `norm_ePhase_sub`, `norm_sum_le`, `div` by `N`.
3. `window_tail_tendsto_zero`: swap the sums; for each `j` bound `∑_{n∈Ico N 2N} ω(n+j+1)` by `sum_omegaR_add_le`
   (`X = 2N`, `ρ = j+1`); the `j`-dependence inside the log is harmless (`j ≤ windowJ N ≤ N`); sum the geometric
   series `∑_{j≥K} 4^{-(j+1)} ≤ 4^{-K}/3`; then show `(log(2N·(log(2N+windowJ N+1)+1)·2/N)/log 2) / 4^{windowK N} → 0`:
   numerator `≤ log₂(4 (log(3N)+1)) = O(log log N)`, denominator `≥ (Nat.log 2 (Nat.log 2 N))²` via
   `Nat.lt_pow_succ_log_self`.  Model on `tail_error_uniform`.
4. `windowDecay_of_windowDecayK`: `‖W_J‖ ≤ ‖W_J − W_K‖ + ‖W_K‖`, both → 0 (`squeeze_zero`).
5. `isNormal_G4_of_windowDecayK := isNormal_G4_of_windowDecay (fun h hh => windowDecay_of_windowDecayK (hW h hh))`.
6. `fullWindowMean_eq_prefixSum` (`Finset.sum_Ico_eq_sub` after `range (2N) = Ico 0 (2N)`),
   `windowDecayK_of_prefixDecay`: given `ε`, eventually both `M = N` and `M = 2N` are in range and `windowK N ≤ windowK (2N)`
   (`windowK_mono`), so `‖W_K‖ ≤ (ε·2N + ε·N)/N = 3ε`; `Metric.tendsto_atTop`.
7. `isNormal_G4_of_prefixDecay`.

`PrefixDecay`/`WindowDecayK` are frozen nodes, **never proved**.  If leaf 3 resists after a real attempt, leave the
resisting inequality as a named `sorry` with a comment and finish the wiring on top of it - the wiring theorems are the
deliverable.  `native_decide`, long `omega`/`nlinarith`, deprecations are fine.  Report the crux advance, not the sorry
count.  `lake build NormalNumbers.G4WindowK` green before every commit; `git-safe` only.  End with
`HANDOFF-2026-09-20-windowK.md` and STOP - when the override at the top of `DIRECTION.md` is done there is no fallback
objective (every section below it is DONE or CLOSED).
