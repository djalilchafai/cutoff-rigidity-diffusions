# c2sigma adversary report (Sphere17, C2Sigma1, C2Sigma2)

Verdict: ACCEPT (two non-blocking remarks).

Checks done independently
- `lake build CutoffRigidity.Extra.C2Sigma2 CutoffRigidity.Extra.Sphere17`: success. `#print axioms` on k1_fails, isSigmaLangevin2_iff,
  isSigmaLangevin2_unique(not printed separately: printed OK), normalization_cutoff_C2, temperature_cutoff_C2, temperature_kernel_C2,
  isEucLangevin2_invariant: only propext, Classical.choice, Quot.sound. grep sorry/axiom/native_decide in the 3 files: none.
- Statement diff vs Challenge.lean: normalization_cutoff_C2 is textually identical to normalization_cutoff (only namespace prefixes CutCur.).
  temperature_cutoff_C2 identical to temperature_cutoff except `IsSigmaLangevin` -> `C2U.IsSigmaLangevin2` in hY (hypotheses hσ,hρ,hHess,hgap,hliminf,hc and conclusion same).
- IsSigmaLangevin2 = ContDiff ℝ 2 V ∧ IsProbabilityMeasure (gibbs (V/σ²)) ∧ IsSigmaDiffusion V σ Pt; Challenge IsSigmaLangevin has ContDiff ℝ ∞ V in the
  first clause and is otherwise identical. Same for IsEucLangevin2 vs IsEuclideanLangevin.
- Vacuity: temperature_kernel_C2 proves existence of Pt with IsSigmaLangevin2 for every C² V with Hess ≥ ρ > 0, probability Gibbs, any σ>0, via exists_euclideanLangevin_C2 + time change
  (no C³). Concrete non-C³ instance: d=1, V = x²/2 + |x|^(5/2) (C², not C³ at 0, Hess ≥ 1, Gibbs integrable), any σ ≠ 1 works. Not formalised as an explicit instance, but the
  existence theorem is general so the class is nonempty and strictly larger than the C^∞ one. Uniqueness (isSigmaLangevin2_unique) needs only convexity (Hess ≥ 0), via
  euclideanDiffusion_unique_convex; invariance needs Hess ≥ r > 0, stated as such.
- k1_fails: hypotheses are just hd: 2 ≤ d, probability weighted volume with constant potential; satisfiable (Sph.round_sphere supplies μ,c). The statement is ¬(1 ≤ k₁ ∧ k₁ ≤ d), the exact
  negation of the conclusion of riemannian_k1_bounds. mFirstEigenDim is a finrank (junk 0 if infinite-dim): the proof handles this honestly (1 ≤ k₁ gives finite dimension, then the
  d+1 independent eigenclasses contradict k₁ ≤ d); the k₁ = 0 case makes the statement true trivially, which is consistent with "conclusion fails". Not an argument by junk value.

Remarks (non-blocking)
1. k1_fails does not itself carry hCD/ρ>0: to claim "hgap cannot be dropped in riemannian_k1_bounds" one combines it with Sph.round_sphere (CD(d-1), gap d ≠ d-1). A packaged
   statement `∃ μ c ρ, ... hCD ∧ ¬conclusion` would be more self-contained; it is a 3-line wrapper from round_sphere + k1_fails.
2. Both ρ-hypothesis and hHess in temperature_cutoff_C2 force convexity, so no convexity gap; liminf/hgap unchanged.

Solution swaps needed if IsSigmaLangevin and IsEuclideanLangevin become C² in Challenge (all use `apply CutoffRigidity.Paper.X <;> assumption`):
- IsSigmaLangevin: temperature_cutoff -> body from temperature_cutoff_C2 (swap isEuclideanLangevin_of_sigma -> C2U.isEucLangevin2_of_sigma, _K -> _K2). Sigma.lean: isSigmaLangevin_iff -> isSigmaLangevin2_iff,
  sigmaLangevin_eq_timeChange, isSigmaLangevin_unique -> isSigmaLangevin2_unique (add Hess ≥ 0), isEuclideanLangevin_invariant -> isEucLangevin2_invariant, temperature_kernel -> temperature_kernel_C2,
  exists_sigmaLangevin keeps explicit C^∞ hypothesis (or use exists_euclideanLangevin_C2 + convexity).
- IsEuclideanLangevin (Solution.lean theorems, with C2Uniq replacement): isLangevinSolution_map_eq_kernel_of_rigid -> ..._of_rigid_C2 (C2Uniq11); main_wasserstein_estimate -> main_wasserstein_estimate_C2;
  convex_interaction_cutoff -> convex_interaction_cutoff_C2; product_condition_cutoff -> product_condition_cutoff_C2; eigenmap_is_ou -> eigenmap_is_ou_C2 (C2Uniq11);
  wasserstein_cutoff_weak -> wasserstein_cutoff_weak_C2; ou_fisher_information, ou_mean_start_cutoff, ou_lp_infty_fails: OU potentials are C^∞, only need the hL hypothesis reproved via
  IsEucLangevin2 (check per case; ou files may need the of_smooth/C2 transfer); langevin_w2_contraction -> _C2; langevin_entropy_decay -> _C2; langevin_fisher_decay -> _C2;
  langevin_fisher_dini -> _C2; langevin_dissipation_ge_K' -> langevin_dissipation_ge_C2'; langevin_dissipation_dirac_K -> langevin_dissipation_dirac_C2 (C2Uniq10/12 also has langevin_dissipation_eq_*).
  Also rigid-sequence statements (IsRigidSequenceK users: wasserstein_cutoff, information_cutoff, lp_cutoff, mixing_time_*, information_cutoff_weak) -> the _C2 versions in C2Uniq9.
  Not verified by me: I did not compile the swaps; the exact hypothesis shapes of each _C2 theorem should be diffed against the Challenge statements by the lead.
