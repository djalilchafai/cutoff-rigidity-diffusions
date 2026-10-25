# diff-KUWB-D: interpolation along a C^1 curve (DONE, no sorry)
Files: CutoffRigidity/Riemann/DiffKuwada1.lean (hasDerivAt_comp_curve, continuous_speed, curve_mvt),
DiffKuwada2.lean (young_aux, curve_dini_step), DiffKuwada3.lean (curve_G_continuousOn, curve_interp_aux,
curve_interpolation), umbrella DiffKuwada.lean. Axioms: propext, Classical.choice, Quot.sound.
Statement: namespace CutoffRigidity.Riemann.Diff, variables F, M as standard (only EMetricSpace M, ChartedSpace,
IsManifold, RiemannianBundle, IsContMDiffRiemannianBundle used). Explicit arg F, then hγ h1..h6 as in the task:
theorem curve_interpolation (hγ : ContMDiff 𝓘(ℝ,ℝ) 𝓘(ℝ,F) 1 γ) (h1..h6 as specified) :
  W (1/2) (γ 1) - W0 (γ 0) ≤ c ^ 2 * (∫ τ in (0:ℝ)..1, ‖mfderiv 𝓘(ℝ,ℝ) 𝓘(ℝ,F) γ τ 1‖) ^ 2
No c ≥ 0 needed. Plan was correct as written. DiffKuwPre not imported (not needed).
