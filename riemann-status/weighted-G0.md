# Workstream A, G0: regularity (`CutCur.WeightedRegular`) -- DONE, fully checked

Final theorem (file `CutoffRigidity/Riemann/WeightedRegular.lean`, axioms: propext, Classical.choice, Quot.sound):
`theorem CutCur.weightedRegular (V : M → ℝ) (hV : MSmooth F V) : CutCur.WeightedRegular F V`
(same variables as Challenge `section Riemannian`; no extra hypotheses).

No upstream/existing file was edited. New files (all build, no sorry):
* `Riemann/WeightedRegularChart.lean`: `coord`, `chartFrame_coord`, `coord_chartFrame`, `contMDiffAt_coord`,
  `contMDiffAt_section_of_coord`, `contMDiffAt_chartFrame'` (order-∞ chart frames, at every point of the chart),
  `contDiffAt_chartMetric`, `contDiffAt_chartMetric_inverse`, `contDiffAt_coordinateRiemannianGradient`,
  (G0.1) `contMDiff_manifoldGradient_top` / `contMDiff_mgrad` (mgrad f is a C^∞ section),
  (G0.2) `msmooth_carre`.
* `Riemann/WeightedRegularKoszul.lean`: `contMDiffAt_mvfderiv_frame`, `contMDiffAt_koszul` (Koszul expression in
  the chart frame is smooth, using `ContMDiffAt.mlieBracket_vectorField`), `hessCoeff`, `contDiffAt_hessCoeff`
  (coefficients <∇_{E_u}Y,E_w> of Levi-Civita derivative of smooth Y are smooth in the chart coordinate).
* `Riemann/WeightedRegularTrace.lean`: `chartFrameInv`, `hessOp = G⁻¹K`, `hessGram`, `trace_conj_aux`,
  `chartFrameInv_comp_hessOp_eq`, `trace_levi_eq` (tr ∇Y = tr(G⁻¹K)), `hessNormSq_eq` (tr A*A = tr(G⁻¹ P)).
* `Riemann/WeightedRegular.lean`: `trCLM`, `contDiffAt_hessOp`, `contDiffAt_hessGram`, `contMDiffAt_of_coord`,
  (G0.3) `msmooth_mlaplacian`, (G0.4) `msmooth_mHessNormSq` (smooth, not only continuous), `weightedRegular`.

Method: everything proved only at order ∞ (not arbitrary n). Smoothness of Levi-Civita is obtained from the
Koszul formula `leviCivitaConnection_apply_inner` applied to the chart frame + inverse chart metric; traces are
transported to the model space via the chart trivialization.
