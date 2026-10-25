module

public import CutoffRigidity.Riemann.DiffChart

/-! # Transfer of `L²` estimates through a chart (workstream DIR)

`μ` pushed forward by the chart is `ρ dz` on the target.  The measure `ν = κ dz` with
`κ = ρ/(‖G‖+1)` satisfies `κ ≤ ρ`, `ρ ‖∇ã‖² κ⁻¹ ...` and is the natural measure for the `L²`
theory of the weak gradient: `∫ κ ‖∇ã‖² dz ≤ ∫ Γ(a,a) dμ`, `∫ κ ã² dz ≤ ∫ a² dμ`.
-/

@[expose] public section

open Bundle MeasureTheory Filter Set
open scoped Manifold ContDiff ENNReal Topology

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace CutoffRigidity.Riemann.Diff

open CutCur

section Transfer

variable (F : Type) [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]
  {M : Type} [EMetricSpace M] [ChartedSpace F M] [IsManifold 𝓘(ℝ, F) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, F) ∞ F (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [MeasurableSpace M] [BorelSpace M]
  {V : M → ℝ} (hV : MSmooth F V) {μ : Measure M} (hμ : IsWeightedVolume F μ V) (x₀ : M)

include hμ in
/-- The pushforward of `μ|source` by the chart is `ρ dz` on the target. -/
theorem chart_map_eq :
    (μ.restrict (chartAt F x₀).source).map (chartAt F x₀) =
      (volume.restrict (chartAt F x₀).target).withDensity
        fun z => ENNReal.ofReal (chartRho F V x₀ z) := by
  rw [hμ x₀]
  refine withDensity_congr_ae ?_
  filter_upwards [ae_restrict_mem (chartAt F x₀).open_target.measurableSet] with z hz
  rw [chartRho_eq F V x₀ hz]

include hV in
theorem measurable_chartRho_aemeasurable :
    AEMeasurable (fun z => ENNReal.ofReal (chartRho F V x₀ z))
      (volume.restrict (chartAt F x₀).target) := by
  have hcont : ContinuousOn (chartRho F V x₀) (chartAt F x₀).target := fun z hz =>
    (contDiffAt_chartRho F hV x₀ (by rw [CutoffRigidity.extChartAt_target_eq]; exact hz)).continuousAt.continuousWithinAt
  exact ENNReal.measurable_ofReal.comp_aemeasurable
    (hcont.aemeasurable (chartAt F x₀).open_target.measurableSet)

include hV hμ in
/-- **Change of variables for lower integrals.** -/
theorem lintegral_chart (h : M → ℝ≥0∞) (hh : Measurable h) :
    ∫⁻ z in (chartAt F x₀).target, ENNReal.ofReal (chartRho F V x₀ z) * h ((chartAt F x₀).symm z) =
      ∫⁻ x in (chartAt F x₀).source, h x ∂μ := by
  set φ := chartAt F x₀ with hφ
  have hTm : MeasurableSet φ.target := φ.open_target.measurableSet
  have hSm : MeasurableSet φ.source := φ.open_source.measurableSet
  have hmap := chart_map_eq F hμ x₀
  have hsymm : AEMeasurable φ.symm (volume.restrict φ.target) :=
    φ.continuousOn_symm.aemeasurable hTm
  have hH : AEMeasurable (fun z => h (φ.symm z)) (volume.restrict φ.target) :=
    hh.comp_aemeasurable hsymm
  have hφm : AEMeasurable φ (μ.restrict φ.source) := φ.continuousOn.aemeasurable hSm
  have hH' : AEMeasurable (fun z => h (φ.symm z)) ((volume.restrict φ.target).withDensity
      fun z => ENNReal.ofReal (chartRho F V x₀ z)) :=
    hH.mono_ac (withDensity_absolutelyContinuous _ _)
  calc ∫⁻ z in φ.target, ENNReal.ofReal (chartRho F V x₀ z) * h (φ.symm z)
      = ∫⁻ z, h (φ.symm z) ∂((volume.restrict φ.target).withDensity
          fun z => ENNReal.ofReal (chartRho F V x₀ z)) := by
        rw [lintegral_withDensity_eq_lintegral_mul₀ (measurable_chartRho_aemeasurable F hV x₀) hH]
        rfl
    _ = ∫⁻ z, h (φ.symm z) ∂((μ.restrict φ.source).map φ) := by rw [hmap]
    _ = ∫⁻ x, h (φ.symm (φ x)) ∂(μ.restrict φ.source) := by
        refine lintegral_map' ?_ hφm
        rw [hmap]
        exact hH'
    _ = ∫⁻ x in φ.source, h x ∂μ := by
        refine setLIntegral_congr_fun hSm fun x hx => ?_
        rw [φ.left_inv hx]

/-- The weight `κ = ρ/(‖G‖+1)` (note `κ ≤ ρ`, `κ ‖v‖² ≤ ρ ⟪a v, v⟫`). -/
noncomputable def chartKappa (V : M → ℝ) (x₀ : M) (z : F) : ℝ :=
  chartRho F V x₀ z / (‖chartMetric (I := 𝓘(ℝ, F)) x₀ z‖ + 1)

/-- The measure `ν = κ dz` on the chart target. -/
noncomputable def chartNu (V : M → ℝ) (x₀ : M) : Measure F :=
  (volume.restrict (chartAt F x₀).target).withDensity fun z =>
    ENNReal.ofReal (chartKappa F V x₀ z)

theorem chartKappa_pos (V : M → ℝ) (x₀ : M) {z : F} (hz : z ∈ (chartAt F x₀).target) :
    0 < chartKappa F V x₀ z := by
  unfold chartKappa
  exact div_pos (chartRho_pos F V x₀ hz) (by positivity)

theorem chartKappa_le (V : M → ℝ) (x₀ : M) {z : F} (hz : z ∈ (chartAt F x₀).target) :
    chartKappa F V x₀ z ≤ chartRho F V x₀ z := by
  unfold chartKappa
  have h1 := chartRho_pos F V x₀ hz
  rw [div_le_iff₀ (by positivity)]
  nlinarith [norm_nonneg (chartMetric (I := 𝓘(ℝ, F)) x₀ z)]

set_option synthInstance.maxHeartbeats 200000 in
include hV in
theorem continuousOn_chartKappa : ContinuousOn (chartKappa F V x₀) (chartAt F x₀).target := by
  intro z hz
  have hz' : z ∈ (extChartAt 𝓘(ℝ, F) x₀).target := by
    rw [CutoffRigidity.extChartAt_target_eq]; exact hz
  have h1 : ContinuousAt (chartRho F V x₀) z := (contDiffAt_chartRho F hV x₀ hz').continuousAt
  have h2 : ContinuousAt (fun w => ‖chartMetric (I := 𝓘(ℝ, F)) x₀ w‖) z :=
    ContinuousAt.comp (g := fun G : F →L[ℝ] F →L[ℝ] ℝ => ‖G‖) (f := chartMetric (I := 𝓘(ℝ, F)) x₀)
      (continuous_norm (E := F →L[ℝ] F →L[ℝ] ℝ)).continuousAt (contDiffAt_chartMetric_target_top F x₀ hz').continuousAt
  exact (h1.div (h2.add continuousAt_const)
    (by show ‖chartMetric (I := 𝓘(ℝ, F)) x₀ z‖ + 1 ≠ 0; positivity)).continuousWithinAt

include hV in
theorem aemeasurable_chartKappa :
    AEMeasurable (fun z => ENNReal.ofReal (chartKappa F V x₀ z))
      (volume.restrict (chartAt F x₀).target) :=
  ENNReal.measurable_ofReal.comp_aemeasurable
    ((continuousOn_chartKappa F hV x₀).aemeasurable (chartAt F x₀).open_target.measurableSet)

include hV hμ in
/-- `ν`-integrals of functions transported from `M` are dominated by `μ`-integrals. -/
theorem lintegral_chartNu_comp (h : M → ℝ≥0∞) (hh : Measurable h) :
    ∫⁻ z, h ((chartAt F x₀).symm z) ∂(chartNu F V x₀) ≤ ∫⁻ x, h x ∂μ := by
  set φ := chartAt F x₀ with hφ
  have hTm : MeasurableSet φ.target := φ.open_target.measurableSet
  have hH : AEMeasurable (fun z => h (φ.symm z)) (volume.restrict φ.target) :=
    hh.comp_aemeasurable (φ.continuousOn_symm.aemeasurable hTm)
  unfold chartNu
  rw [lintegral_withDensity_eq_lintegral_mul₀ (aemeasurable_chartKappa F hV x₀) hH]
  calc ∫⁻ z in φ.target, (fun z => ENNReal.ofReal (chartKappa F V x₀ z)) z * h (φ.symm z)
      ≤ ∫⁻ z in φ.target, ENNReal.ofReal (chartRho F V x₀ z) * h (φ.symm z) := by
        refine setLIntegral_mono' hTm fun z hz => ?_
        exact mul_le_mul_left (ENNReal.ofReal_le_ofReal (chartKappa_le F V x₀ hz)) _
    _ = ∫⁻ x in φ.source, h x ∂μ := lintegral_chart F hV hμ x₀ h hh
    _ ≤ ∫⁻ x, h x ∂μ := setLIntegral_le_lintegral _ _

include hV hμ in
theorem chartNu_univ_le : chartNu F V x₀ Set.univ ≤ μ Set.univ := by
  have := lintegral_chartNu_comp F hV hμ x₀ (fun _ => 1) measurable_const
  simpa [lintegral_const] using this

include hV hμ in
theorem isFiniteMeasure_chartNu [IsFiniteMeasure μ] : IsFiniteMeasure (chartNu F V x₀) :=
  ⟨lt_of_le_of_lt (chartNu_univ_le F hV hμ x₀) (measure_lt_top _ _)⟩

end Transfer

end CutoffRigidity.Riemann.Diff
