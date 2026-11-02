# R4 adversary report: C^2 uniqueness (CutoffRigidity/Extra/C2Uniq1..12.lean)

Verdict: **ACCEPT** (no repair needed). No human review is claimed.

## What I did (all from the files, worker notes read only for the integration recipe)

1. Recompiled: `lake build CutoffRigidity.Extra.C2Uniq12` succeeds (only linter warnings, from DissipEq4 etc.).
   `grep sorry|axiom|native_decide|#print|admit|unsafe|implemented_by|opaque` over the twelve files: no hits.
2. `#print axioms` on all 108 theorems/lemmas of the twelve files (scratch `scratchpad/Ax.lean`, outside the repo):
   every one is `[propext, Classical.choice, Quot.sound]`; none uses sorryAx.
3. Read the whole core by hand (C2Uniq1, 2, 3, 5, 6, 7 and the cutoff statement of 4).
4. Mechanical statement diff vs `Challenge.lean` (script `scratchpad/diff.py`): see section 3.
5. Non-vacuity witness outside the repo (`scratchpad/Witness.lean`, compiles, clean axioms): see section 4.

## 1. Mathematical verification of the core (no flaw found)

Conventions: L_V = Delta - <grad V, grad .>, backward family w_tau = K_tau g of the smooth approximant W_n, d/dtau w = L_W w.
* `generator_mul_sub`: L_V(chi f) - chi L_W f = chi<grad W - grad V, grad f> + f Delta chi + 2<grad chi, grad f> - f<grad V, grad chi>. Checked by hand, correct.
* `error_lower`: lower bound of the four terms. Term 1 uses |grad V - grad W| <= delta on supp chi only (chi = 0 elsewhere, handled with chi != 0). Terms 2, 3 are two-sided. Term 4 -f<grad V, grad chi> >= -f A/R needs only the ONE-sided bound <grad V, grad chi> <= A/R and f >= 0 (it multiplies f = w_tau >= 0), then f <= K. This is exactly where convexity enters: chi radial non-increasing, so <grad V, grad chi> = chi'(|y|)/|y| <grad V(y), y> and <grad V(y), y> >= -|grad V(0)||y| from monotonicity of grad V. Correct and sufficient. (`exists_cutoff` takes exactly this hypothesis `hVa`.)
* `core_upper`: Theta(s) = e^{-lam s}F(s) + int_0^s phi + (Err/lam^2)e^{-lam s}, F = U(chi w_s). I recomputed Theta' = e^{-lam s}(Hh - lam F + chi(x) w_s(x) - Err/lam) = -e^{-lam s}(Eh + Err/lam) <= 0 using the resolvent identity lam F - Hh - Eh = chi(x) w_s(x) and Eh >= -Err/lam (`resU_ge` on the pointwise bound; U of a constant a is a/lam by the Markov property). Antitone on [0,inf) (continuity at 0 from `continuous_resU_w`, derivative on s>0), limit S -> inf with domination. Gives chi(x) r_n(x) <= U(chi g)(x) + Err/lam^2. Correct.
* Differentiation under the integral signs (`hasDerivAt_resU_w`): dominated by C (uniform bound of L_W w_tau, depends on n but is used only for domination, never in Err). Fine.
* `resU_close` (mass trick): applies `core_upper` to (g, w) and to (K - g, K - w) (`IsBackward.const_sub`, uses K_tau 1 = 1, i.e. Markov property of the library kernel, built into `exists_backward` through `0 <= w <= K`). Combined with U(chi K) <= K/lam and chi g = g, chi(x) = 1 gives |r_n(x) - U g(x)| <= Err/lam^2. Err = delta G + K A/R^2 + 2(A/R)G + K A/R: G (Bakry-Emery, Hess W_n >= 1/(n+1) > 0, factor e^{-rho tau} <= 1), K, A do not depend on n or on P. Order of limits in `resU_eq_of_nonneg` is correct: R chosen first (depends on lam, eps, K, G, A, x, supp g), then delta, then N = N(2R, delta) from `Wm_grad_close` (local uniform convergence only), then n = N. The bound is P-independent, so U_{P1} g(x) and U_{P2} g(x) are both within Err/lam^2 of the same number r_n(x).
* P-side hypotheses used: only `IsEuclideanDiffusion` (Markov, Chapman-Kolmogorov, Dynkin for C_c^infty). `continuous_semi_cs` gets continuity of s -> P_s h(x) for continuous compactly supported h by Lipschitz (Dynkin + semigroup + Markov) for C_c^infty and uniform approximation by mollification. `resU_dynkin` applies the Dynkin identity only to test functions chi*w_tau in C_c^infty (w_tau smooth because W_n smooth, chi smooth compactly supported): no extension of Dynkin to C_c^2 is needed. L_V(chi w) is continuous with compact support because V in C^1 suffices. Nothing is smuggled: no Gibbs integrability of V, no existence assumed.
* Laplace uniqueness at lam = m+2 for bounded continuous phi, then measure uniqueness via C_c^infty (`measure_eq_of_integral_smooth`): standard and compiled.
* Mass-loss/explosion is excluded by `IsMarkovKernel` (probability measures) in the definition `IsEuclideanDiffusion`, as in the Challenge text. Consistent with known facts: grad V of a convex function is monotone, so -grad V is one-sided Lipschitz and the SDE has pathwise uniqueness and no explosion.
* Observation (not a flaw): the proof only uses V in C^1 and convexity (C^2 enters via `Wm_hess` through the library lemma on the smooth mollification and the statements' hypothesis). Uniqueness for convex C^1 potentials is also true classically (monotone drift). No contradiction with known counterexamples (those need non-monotone, non-Lyapunov drifts).

## 2. Hypothesis check of the headline theorem

`euclideanDiffusion_unique_convex (hV : ContDiff R 2 V) (hc : ConvexOn R univ V) (h1 h2 : IsEuclideanDiffusion V P_i) t x : P1 t x = P2 t x`,
`c2Unique_of_convex (hV) (hHess : forall x z, 0 <= fderiv (fderiv V) x z z) : C2Unique V`. No Gibbs hypothesis, as claimed. `C2Unique` is literally the same text as `C2Uniqueness` of `C2Langevin.lean` (restated only because that def is not `@[expose]`d).

## 3. Faithfulness of the ported `_C2` statements (mechanical diff)

The diff normalises `IsEuclideanLangevin -> IsEucLangevin2`, `IsRigidSequenceK -> IsRigidSeqK2` and the theorem name, and compares against the Challenge.lean statement text. Result: 19 statements are IDENTICAL up to namespace qualification (`CutCur.`, `CutCur.C2U.`), except `convex_interaction_cutoff_C2` where in addition `ContDiff R infinity (W n)` became `ContDiff R 2 (W n)` (intended). `IsEucLangevin2` = `ContDiff 2 V and IsProbabilityMeasure (gibbs V) and IsEuclideanDiffusion V Pt`, i.e. `IsEuclideanLangevin` with infinity -> 2 (the Challenge docstring itself already says "amendment: C^2 in IsLangevin"). `IsRigidSeqK2` is `IsRigidSequenceK` with `IsEucLangevin2`.

Covered (Challenge statements with a `_C2` twin):
isLangevinSolution_map_eq_kernel_of_rigid, main_wasserstein_estimate, wasserstein_cutoff, information_cutoff, lp_cutoff, convex_interaction_cutoff, product_condition_cutoff, eigenmap_is_ou, wasserstein_cutoff_weak, information_cutoff_weak, mixing_time_rigid, mixing_time_w2_rigid, mixing_time_kl_rigid, langevin_w2_contraction, langevin_entropy_decay, langevin_fisher_decay, langevin_fisher_dini, langevin_dissipation_ge_K', langevin_dissipation_dirac_K (19). Extras: langevin_dissipation_core_C2, isLangevinSolution_map_eq_kernel_C2, langevin_dissipation_eq_C2/C2'/eq_dirac_C2 (DissipEq, imports the still untracked DissipEq5).

Not covered by a `_C2` twin, with consequence:
* `temperature_cutoff` (hypothesis `IsSigmaLangevin`, own `ContDiff R infinity` clause) and, through it, Sigma.lean: not ported (worker says so). Needs the small repair listed in section 5.
* `normalization_cutoff`: no IsEuclideanLangevin hypothesis (generic kernels): unaffected.
* `ou_mean_start_cutoff`, `ou_lp_infty_fails`, `ou_fisher_information`: potentials rho/2|x|^2+c are smooth, so the clause is automatic; after the definition change they keep their text, only the transfer lemma they call must be swapped.
* `dyson_ou_static`, `temperature_bakry_emery`, `temperature_sde`, Riemannian block: no kernel hypothesis, unaffected.

## 4. Non-vacuity (scratch, outside the repo): `/tmp/claude-1000/-chome-djay-S--Publis-2025-CRAS-CF-lean/25ce202f-e16f-4c7d-901c-94cac4f5c39d/scratchpad/Witness.lean`

d = 1. u(t) = int_0^t |s| ds, w(t) = int_0^t u (so w'' = |t|), W(x) = w(x_0), V0 = (2/2)|x|^2 + W, Z = int e^{-V0}, V = V0 + log Z. Proved in Lean (axioms propext/Classical.choice/Quot.sound, no sorry):
`cV : ContDiff R 2 V`, `notC3V : not ContDiff R 3 V` (restriction to the axis would make |t| differentiable at 0), `convV : ConvexOn R univ V`, `gibbs_prob : IsProbabilityMeasure (gibbs V)`, `hess`,
`witness_exists : exists Pt, IsEucLangevin2 V Pt` (from `exists_euclideanLangevin_C2`), `witness_unique : C2Unique V` (from `c2Unique_of_convex`).
So the new statements are non-vacuous on a genuinely C^2, non-C^3 potential (the smooth case is not hiding the result).

## 5. Integration plan (for the lead)

Dependency warning: C2Uniq3 imports `Extra.EuclideanDiffusion`, so `EuclideanDiffusion.lean` cannot itself import the new uniqueness (cycle). Keep it, and do the swaps downstream.

A. Challenge.lean / Statements.lean text changes (Challenge is at 995/1000 lines: net zero lines, only edits inside lines)
 1. `IsEuclideanLangevin`: `ContDiff R infinity V` -> `ContDiff R 2 V`; update docstring (remove "`isEuclideanDiffusion_unique` ... bridge_final" claim: uniqueness now `euclideanDiffusion_unique_convex`, for convex V; say convexity is not part of the definition but of the statements via `hHess`/`RigidCurvature`).
 2. `IsRigidSequenceK`: no text change (through IsEuclideanLangevin); docstring amendment.
 3. `convex_interaction_cutoff`: hypothesis `ContDiff R infinity (W n)` -> `ContDiff R 2 (W n)`; the pairwise_interaction docstring already says C^2.
 4. `IsSigmaLangevin`: `ContDiff R infinity V` -> `ContDiff R 2 V` (only needed for temperature_cutoff; the statement text of temperature_cutoff does not change). Docstrings of `main_wasserstein_estimate`, `lp_cutoff`... that say "Amendment: V in C^infinity" must be updated to "V in C^2".
 5. No change: `IsEuclideanDiffusion`, `IsSigmaDiffusion` (their f-clauses stay C_c^infty), all OU, Dyson, Riemannian statements.
 Then update comparator.json/formalization.yaml/audit text mentioning "C^infinity" for these statements.

B. Solution-side lemma swaps (statement texts of Solution stay literally equal to Challenge)
 Replace by the `CutCur.C2U` versions of C2Uniq8 (they take `IsEucLangevin2`, which becomes definitionally `IsEuclideanLangevin` after A.1; recommend making `IsEucLangevin2 := IsEuclideanLangevin` an abbrev or deleting it and using the Statements def):
 * `exists_isLangevin_of_isEuclideanLangevin` -> `exists_isLangevin_of_C2` (same arguments, uses `euclideanDiffusion_unique_convex`), in: EuclideanKernelStatements (l. 108, 147, 219, 236, 254), Dissip3 (42, 69), Dissip4 (77), DissipEq5 (150, 220), EuclideanWasserstein (64).
 * `exists_isLangevin_of_rigid` -> `exists_isLangevin_of_rigid_C2`: EigenmapOUK (42), EuclideanWasserstein (36).
 * `exists_isRigidSequence_of_K` -> `exists_isRigidSequence_of_K2`: EuclideanKernelStatements (383), EuclideanCutoffs (59, 72, 191, 209, 231), EuclideanWeakK (49), EuclideanWasserstein (47), and `temperature_cutoff_K` (l. 383 region).
 * `exists_langevinSeq_of_K` -> `exists_langevinSeq_of_K2`: EuclideanCutoffs (100, 133), EuclideanWeakK (31).
 * `isEuclideanDiffusion_eq_langevinKernel hB hL.1 hL.2.1 ...` (SdeId1.lean l. 38) -> `euclideanDiffusion_unique_convex ... (isEuclideanDiffusion_langevinKernel ...)` as in `isLangevinSolution_map_eq_kernel_C2` (C2Uniq11).
 * Alternatively replace each `_K` theorem body by its `_C2` twin from C2Uniq9/10/11/12 (identical statements), moving C2Uniq1..12 below the Extra files that need them in the import graph, or inserting the C2Uniq chain before EuclideanKernelStatements/EuclideanCutoffs.
 * Where `hL.1` is used as C^infty: FisherDecayGeneral l. 32 and MixingTimeW2KL l. 102-137 take `IsLangevin` (carrier) and only need C^2: no change. `EuclideanKernelStatements` l. 370 only `of_le`. Verified by reading; the full-suite rebuild will confirm.
 * `exists_euclideanLangevin` (EuclideanDiffusion l. 109, smooth hypothesis) -> `exists_euclideanLangevin_C2` (also takes C^2 only); `exists_euclideanLangevin_of_smooth` (Riemannian `Kk`) still needs C^infty and no convexity, keep it with an explicit `ContDiff R infinity V` hypothesis and drop it from the C^2 story (it must not be used for C^2 V).
 * `C2Langevin.lean`: now obsolete (`C2Uniqueness` conditional) except as a comparison; docstring claims uniqueness "NOT proved for non-smooth V": stale, update or delete.

C. Where the smooth case is genuinely used and C^2 breaks (flags)
 1. `isEuclideanDiffusion_unique` / `isEuclideanLangevin_unique` (EuclideanDiffusion l. 80-93) use the Riemannian `bridge_final`, needing C^infty, finite Gibbs, NO convexity. Under C^2 `IsEuclideanLangevin` they no longer typecheck. Uses: Sigma.lean (`sigmaLangevin_eq_timeChange`, `isSigmaLangevin_unique`, `isEuclideanLangevin_invariant`, `isSigmaLangevin_invariant`, `temperature_kernel`) and `isEuclideanDiffusion_eq_langevinKernel`. Options: keep them with an explicit `ContDiff R infinity V` argument (smooth only: then `temperature_kernel` keeps `hV : ContDiff R infinity V` and gets an extra hypothesis, which it already has), or give them convex-C^2 versions (uniqueness: trivial via `euclideanDiffusion_unique_convex`; invariance under the unique kernel: not yet ported, would need the Brownian-carrier route `langevinKernel_gibbs_invariant`, needing Hess >= 0). `temperature_kernel` and `isSigmaLangevin_*` are NOT Challenge statements and not in comparator.json (grep), so keeping them smooth-only costs nothing for the Comparator.
 2. `isSigmaLangevin_iff` (Sigma.lean l. 118): the helper `hc : ContDiff infinity V <-> ContDiff infinity (V/sigma^2)` must be re-stated at order 2 (`div_const`, `mul_const` work verbatim). `isEuclideanLangevin_of_sigma` (EuclideanKernelStatements l. 36) likewise. `temperature_cutoff_K` already has `hHess` (convexity); after those two edits it goes through `exists_isRigidSequence_of_K2`.
 3. `exists_sigmaLangevin` (no convexity, via `exists_euclideanLangevin_of_smooth`): keep with smooth hypothesis.
 4. Statement `temperature_cutoff` itself does not need any change except IsSigmaLangevin's clause (A.4).

D. Definitions/statements affected by the integration
 Definitions: `IsEuclideanLangevin`, `IsRigidSequenceK`, `IsSigmaLangevin` (clause only). Statements whose hypothesis becomes weaker (strictly stronger theorems): the 19 listed in section 3, plus the three OU kernel statements (automatic), plus `temperature_cutoff`. No Dyson or temperature_kernel statement is affected in the Challenge (temperature_kernel/Sigma.lean keep a smooth hypothesis).

## 6. Residual risks / notes
* C2Uniq12 imports the untracked DissipEq5; integrate DissipEq items first.
* Statement texts in Statements.lean and Challenge.lean must be edited identically (mirror), then run the full suite and the sandboxed Comparator.
* I did not rebuild the whole project with the proposed swaps (cannot edit shared files); the swap list is from static reading and grep, the lead's full-suite run is the final check.
