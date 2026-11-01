# c2-adversary: verdicts on extra-status/c2-worker.md

Inspected only `CutoffRigidity/Extra/C2Langevin.lean` and the worker's claims, against `Challenge.lean` (OU statements, lines 438, 637, 649;
`IsEuclideanDiffusion`/`IsEuclideanLangevin` in Statements.lean/Challenge.lean) and `cutcur-lean.tex`. No human review claimed.

Checks run: `lake build CutoffRigidity.Extra.C2Langevin` (OK, only an unrelated deprecation warning); `#print axioms` on all 9 theorems in the file
(`toC2`, `toSmooth`, `c2Uniqueness_of_smooth`, `isEuclideanLangevinC2_quadratic_iff`, `exists_isLangevin_of_C2`, `ou_fisher_information_C2`,
`ou_mean_start_cutoff_C2`, `ou_lp_infty_fails_C2`, `langevin_fisher_decay_C2_of_unique`): all exactly propext, Classical.choice, Quot.sound. No sorry,
no stray `#print axioms` in the file. Scratch files (outside the repo): scratchpad `ax.lean`, `vac.lean`.

## Claim 1 (three OU statements with C2 hypotheses): ACCEPT, but it is not progress on the item
* Statement comparison: each `_C2` statement is literally the Challenge/`_K` statement with `IsEuclideanLangevin` replaced by `IsEuclideanLangevinC2`;
  conclusions are identical text, no junk-value tricks. Proof is by the iff below.
* `isEuclideanLangevinC2_quadratic_iff` is correct: `ρ/2‖x‖²+c` is C^infty, so the two hypotheses are equivalent. Hence the Challenge OU statements
  were never restricted (the Challenge docstring already says "`V` is automatically `C^∞`"). The `_C2` theorems are cosmetic restatements and add
  nothing mathematically; the lead should not count them as discharging any of the 18 genuinely restricted statements (and need not add them to
  Challenge.lean at all).
* Vacuity: witness compiled in scratch (`vac.lean`, no sorry): for every `d`, `ρ > 0` there are `c` (= log of the partition function) and `Pt` with
  `IsEuclideanLangevinC2 (fun x => ρ/2*‖x‖^2 + c) Pt` (uses `normalized_gibbs_probability_memLp_two`, `exists_euclideanLangevin`, `toC2`). The
  hypothesis is satisfiable, and is only satisfiable for the right `c` (probability Gibbs), which is as in the `_K` statements.

## Claim 2 (`C2Uniqueness V` holds for C^infty V, not vacuous): ACCEPT
* `c2Uniqueness_of_smooth` is a direct instance of the project's `isEuclideanDiffusion_unique`; correct. `C2Uniqueness V` is a statement about V only,
  with no hypothesis on the Gibbs measure, which is harmless (hypothesis `hp` is supplied in the smooth lemma).
* Not vacuous in the sense that matters: for smooth convex V with probability Gibbs measure `IsEuclideanDiffusion V P` has the witness `langevinKernel`
  (`exists_euclideanLangevin`), so the quantification is over a nonempty set, and the conclusion is a real identification. Worker's wording "not
  vacuous" is fine. Caveat: `C2Uniqueness` for a general C² V is not claimed to be false, and mathematically it is true for convex C² V with probability
  Gibbs measure; it is only unproved.

## Claim 3 (`exists_isLangevin_of_C2` transfer given C2Uniqueness + convexity): ACCEPT
* Hypotheses: `IsEuclideanLangevinC2`, `C2Uniqueness V`, `0 ≤ Hess V` pointwise (for C² V equivalent to convexity). Conclusion identical in form to the
  smooth transfer lemma (`IsLangevin V B P X` plus `P.map (X x₀ t) = Pt t x₀`). `IsLangevin` already uses `ContDiff ℝ 2`, and the lemmas
  `isLangevinSolution_langevinProcess`, `langevinKernel_apply_eq_process_law`, `isEuclideanDiffusion_langevinKernel` already take C² (they compile
  with `hL.1 : ContDiff ℝ 2 V`), so existence of the carrier and of the Kolmogorov equation for `langevinKernel` is already C²-complete; the sole gap is
  identification of an arbitrary `Pt`. The conditional is the right shape: `hU` is used exactly once, to identify `Pt` with `langevinKernel`.
* No degenerate-case trick found. `langevin_fisher_decay_C2_of_unique` is a faithful conditional copy; a conditional theorem does not discharge the item
  and the worker says so.

## Claim 4 (general C² uniqueness blocked, 3000-6000 lines): ACCEPT as an honest report, with two corrections to the analysis
1. "Needs Schauder/W^{2,p}" is true only of the particular Perron/resolvent proof reused from the smooth case, not of the mathematics. I found no route
   that is genuinely cheap; the alternatives also cost the same order. None is verified, sizes are my estimates.
2. Cheaper-route search (all unverified, no Lean written):
   * (a) Pathwise/probabilistic: for convex V the SDE has pathwise uniqueness for free (monotone drift), and the carrier exists already. The missing
     step is identifying an arbitrary semigroup `Pt` with it, i.e. solving the martingale problem from the forward equation; needs path-space
     construction (Kolmogorov continuity) and a martingale-representation/weak-solution argument, absent from Mathlib. Larger. Agree with the worker.
   * (b) One-sided Lipschitz / Lumer-Phillips on the forward equation. Reduction (modest, ~500-800 lines, reuse `bridge_of_minimal` bookkeeping):
     if `(λ - L)(C_c^∞)` is norm-dense in `C_0(ℝ^d)` for some/all λ>0 then two Markov semigroups solving the forward equation have equal resolvents on a
     dense set, hence (sup-norm contraction + Laplace-transform uniqueness using continuity of `t ↦ ∫ g dP_t` from the forward equation) `P = Q`. By
     Hahn-Banach, density is equivalent to: a finite signed measure ν with `∫(λf - Lf) dν = 0` for all `f ∈ C_c^∞` is zero. The convexity enters in the
     cutoff step (`x·(∇V(x)-∇V(0)) ≥ 0` controls `∇V·∇χ_R` one-sidedly), as the worker noted. The hard part is regularity of the measure ν: show ν has an
     L¹ (then H¹_loc, H²_loc) density for C^1 drift, then Kato/L¹-dissipativity with cutoffs. The first step (measure → L¹ density) needs
     Bessel/Newtonian-potential-type kernel estimates or heat-kernel mollification with a commutator estimate (DiPerna-Lions/Friedrichs for measures with
     b ∈ W^{1,∞}_loc); neither is in the library. Estimate for the whole route: 2500-4000 lines, medium-high risk, i.e. the same order as the worker's
     figure; its advantage is that it needs only H²-type regularity of a solution of an elliptic equation with C^1 coefficients, avoiding C^{2,α}
     Schauder theory and the uniform-in-ε gradient bound for `Kk`.
   * (c) Reduction to smooth by mollification `V_ε`: needs a stability statement `P` vs `Q^ε` which itself is the uniqueness problem for the limit.
     No shortcut found; worker's sketch (Bakry-Emery gradient bound + Dynkin with cutoff) is plausible but long.
   * (d) Dimension-dependent partial fix (speculative): the library regularity ladder (H^{m+2} for C^{m+1} coefficients) gives `u ∈ C²` once
     `V ∈ C^k` with `k > d/2 + 2` or so; this would extend the kernel statements to finite-regularity V for fixed d but not uniformly in d, and the
     sequence statements (cutoff, n → ∞ dimensions) need all d. Requires checking that `MSmooth`-based proofs can be run with finite regularity;
     not cheap either and would not remove the restriction. Not recommended.
* Verdict on the project-level consequence: the 18 statements remain C^∞-restricted; the correct record is "blocked: uniqueness of the forward
  Kolmogorov equation for C² convex drift", with the conditional `C2Uniqueness` as the precise missing hypothesis. The existing note in the docs that
  the restriction is a deliberate trade-off stays accurate.

## Summary table
| Claim | Verdict |
|---|---|
| 1. OU `_C2` statements | ACCEPT (correct but vacuous improvement; Challenge OU statements already unrestricted; do not report as progress) |
| 2. `C2Uniqueness` for smooth V, nonvacuous | ACCEPT |
| 3. `exists_isLangevin_of_C2` conditional transfer | ACCEPT |
| 4. General C² uniqueness blocked | ACCEPT (honest); no cheaper route found; analysis slightly overstates "Schauder needed" but alternatives are equally large |

No REPAIR items. Suggested wording fix only: in `c2-worker.md`, say that the three OU theorems are restatements (iff-equivalent), not recoveries.
