# Workstream A, G1: integration by parts (DONE, fully checked)

Final theorem (file `CutoffRigidity/Riemann/WeightedIBPGlobal.lean`, namespace `CutCur`):
`weightedIBP_of_isWeightedVolume {V : M → ℝ} (hV : MSmooth F V) {μ : Measure M}
  (hμ : IsWeightedVolume F μ V) [IsFiniteMeasure μ] : WeightedIBP F μ V`
(`[MeasurableSpace F] [BorelSpace F] [MeasurableSpace M] [BorelSpace M]`, no connectedness/completeness).
Axioms: propext, Classical.choice, Quot.sound only. No sorry. No upstream file edited.

Files (all built, all < 210 lines), import chain Chart -> Local -> Coord -> LocalIBP -> Global:
* WeightedIBPChart: chart-frame calculus at every point of the chart (frame C^1, chartMetric C^1 on the
  target, bracket [e_u, Y] in the chart, Koszul formula `inner_leviCivita_chartFrame_self`).
* WeightedIBPLocal: Jacobi for the density, `chartRiemannianVolumeDensity_mul_trace`:
  D * tr(nabla Y) = d D (Yc) + D * tr(d Yc).
* WeightedIBPCoord: `chartWeight`, `inner_manifoldGradient_chart`, `chartWeight_mul_generator`
  (rho * L v = d rho (Yc) + rho * tr d Yc), C^1 of gradient coordinates, continuity of Gamma.
* WeightedIBPEuclid: Euclidean divergence theorem (`chart_divergence_zero`).
* WeightedIBPTransfer: `integral_eq_chart_integral` (integrals through the density hypothesis).
* WeightedIBPDensity: `CutCur.chartVolumeDensity_pos`, `continuousOn_chartVolumeDensity`,
  `chartVolumeDensity_eq_riemannian` (requested by the `weighted` agent).
* WeightedIBPContinuity: `continuous_carre`, `continuousAt_mgenerator`.
* WeightedIBPLocalIBP: `weightedIBP_of_chart` (u supported in one chart source).
* WeightedIBPGlobal: finite partition of unity built by hand from bump functions (no sigma-compactness),
  `IBPFor` additivity, final theorem.
No Challenge junk-value issue arose.
