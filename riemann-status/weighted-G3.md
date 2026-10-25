# Workstream A, task G3: smooth cutoffs on complete Riemannian manifolds

STATUS: DONE, fully checked (no sorry/axiom; axioms = propext, Classical.choice, Quot.sound).
No upstream/other files edited. New files (all under CutoffRigidity/Riemann/, all build with `lake build`):

* WeightedProperLength.lean : `CutCur.ApproxSegment`, `properSpace_of_approxSegment`
  (complete + locally compact metric space with the approximate-segment property is proper;
  Cohn-Vossen argument).
* WeightedProper.lean : `edist_ne_top_of_connected`, `isContinuousRiemannianBundle_tangent`,
  `approxSegment_of_riemannian`, `riemannianMetricSpace`, `properSpace_of_complete_riemannian`
  (Hopf-Rinow), `isCompact_edist_le` (edist-closed balls compact),
  `sigmaCompactSpace_of_complete_riemannian`.
* WeightedMollify.lean : `exists_contDiff_approx_lip` (pure analysis: bump-function mollification
  of u with |u(b+hw)-u(b)| <= |h| N(w) gives smooth G, |G-u|<=delta, |dG(a)w|<=N(w) on B(a0,R/2)).
* WeightedChartLip.lean : `symmAt`, `eventually_symmAt_norm` (sharp 2-distortion of tangent norms
  of the chart frame), `edist_extChartAt_symm_le` (edist of chart-inverse of two points <=
  r*||frame_p(b'-b)||).
* WeightedLocalSmooth.lean : `exists_local_smooth` (local smoothing of a 1-Lipschitz f, gradient
  constant 4, in `mvfderiv` form).
* WeightedGradHelpers.lean : `mgrad_inner`, `abs_mvfderiv_le_norm_mgrad`, `norm_mgrad_le_of`,
  `continuous_norm_mgrad`, `mvfderiv_congr_ev`, `mdiffAt_finset_sum`, `mvfderiv_finset_sum`,
  `mvfderiv_comp_real`.
* WeightedSmoothing.lean : `exists_smooth_lip_approx` (smooth g, |g-f|<=1, ||mgrad g||<=5 for any
  1-Lipschitz f on a sigma-compact connected-or-finite-edist Riemannian manifold; partition of
  unity + local mollification).
* WeightedCutoffs.lean : `exists_deriv_smoothTransition_bound` and the main result

  theorem CutCur.weightedCutoffs_of_complete (F) [NormedAddCommGroup F] [InnerProductSpace R F]
    [FiniteDimensional R F] {M} [EMetricSpace M] [ChartedSpace F M] [IsManifold 𝓘(R,F) ∞ M]
    [RiemannianBundle ..] [IsContMDiffRiemannianBundle ..] [IsRiemannianManifold 𝓘(R,F) M]
    [ConnectedSpace M] [CompleteSpace M] : CutCur.WeightedCutoffs F M

  (no MeasurableSpace/BorelSpace on F needed; it uses `borel F` internally.)
Note: the explicit argument `F` comes first (variable `include F`).

Open: nothing for G3.
