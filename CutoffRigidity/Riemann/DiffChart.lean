module

public import CutoffRigidity.Riemann.DiffMarkov2
public import CutoffRigidity.Riemann.WeightedIBPLocalIBP

/-! # Chart coefficients of the form of `-𝓛` (workstream DIR)

In the chart `φ = chartAt F x₀` the weighted volume is `ρ dz` with
`ρ = e^{-V∘φ⁻¹} · chartVolumeDensity` and `Γ(u,v) ∘ φ⁻¹ = ⟪a ∇(v∘φ⁻¹), ∇(u∘φ⁻¹)⟫`, where
`a = (chartMetric)⁻¹` is the inverse metric.  We prove that `a` and `ρ` are `C^∞` on the chart
target, `a` symmetric positive definite, `ρ > 0` (the hypotheses of the elliptic regularity theory
of workstream REGn), and the chart formula for `∫ Γ(φ, f) dμ`.
-/

@[expose] public section

open Bundle MeasureTheory Filter Set VectorField
open scoped Manifold ContDiff ENNReal Topology

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace CutoffRigidity.Riemann.Diff

section Smooth

variable (F : Type*) [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  {M : Type*} [TopologicalSpace M] [ChartedSpace F M] [IsManifold 𝓘(ℝ, F) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, F) ∞ F (fun x : M => TangentSpace 𝓘(ℝ, F) x)]

open CutoffRigidity

/-- The actual chart frame is `C^∞` at every point of the chart source. -/
theorem contMDiffAt_chartFrame_source_top {x₀ y : M} (hy : y ∈ (chartAt F x₀).source) (u : F) :
    ContMDiffAt 𝓘(ℝ, F) 𝓘(ℝ, F).tangent ∞ (T% (chartFrame (I := 𝓘(ℝ, F)) x₀ u)) y := by
  have hy' : y ∈ (trivializationAt F (TangentSpace 𝓘(ℝ, F)) x₀).baseSet := by simpa using hy
  rw [Trivialization.contMDiffAt_section_iff (trivializationAt F (TangentSpace 𝓘(ℝ, F)) x₀) hy']
  apply (contMDiffAt_const (c := u)).congr_of_eventuallyEq
  filter_upwards [(chartAt F x₀).open_source.mem_nhds hy] with y' hy''
  have hy3 : y' ∈ (trivializationAt F (TangentSpace 𝓘(ℝ, F)) x₀).baseSet := by simpa using hy''
  change (trivializationAt F (TangentSpace 𝓘(ℝ, F)) x₀ ⟨y', chartFrame (I := 𝓘(ℝ, F)) x₀ u y'⟩).2 = _
  rw [← Bundle.Trivialization.continuousLinearMapAt_apply_of_mem ℝ _ hy3]
  exact (trivializationAt F (TangentSpace 𝓘(ℝ, F)) x₀).continuousLinearMapAt_symmL hy3 u

/-- The chart metric is `C^∞` at every point of the chart target. -/
theorem contDiffAt_chartMetric_target_top (x₀ : M) {z : F}
    (hz : z ∈ (extChartAt 𝓘(ℝ, F) x₀).target) :
    ContDiffAt ℝ ∞ (chartMetric (I := 𝓘(ℝ, F)) x₀) z := by
  have hsymm : ContMDiffAt 𝓘(ℝ, F) 𝓘(ℝ, F) ∞ (extChartAt 𝓘(ℝ, F) x₀).symm z :=
    (contMDiffOn_extChartAt_symm x₀).contMDiffAt (extChartAt_target_nhds hz)
  rw [← contDiffWithinAt_univ]
  apply contDiffWithinAt_clm_apply.mpr
  intro u
  apply contDiffWithinAt_clm_apply.mpr
  intro v
  have hI : ContMDiffAt 𝓘(ℝ, F) 𝓘(ℝ, ℝ) ∞
      (fun y' ↦ inner ℝ (chartFrame (I := 𝓘(ℝ, F)) x₀ u y')
        (chartFrame (I := 𝓘(ℝ, F)) x₀ v y')) ((extChartAt 𝓘(ℝ, F) x₀).symm z) :=
    ContMDiffAt.inner_bundle (E := TangentSpace 𝓘(ℝ, F))
      (contMDiffAt_chartFrame_source_top F (extChartAt_symm_mem_source hz) u)
      (contMDiffAt_chartFrame_source_top F (extChartAt_symm_mem_source hz) v)
  have hreal := (hI.comp z hsymm).contDiffAt.contDiffWithinAt (s := univ)
  simpa only [Function.comp_def, chartMetric_apply] using hreal


theorem chartMetric_symm_apply (x₀ : M) (z u v : F) :
    chartMetric (I := 𝓘(ℝ, F)) x₀ z u v = chartMetric (I := 𝓘(ℝ, F)) x₀ z v u := by
  simp only [chartMetric_apply]
  exact real_inner_comm _ _

theorem chartMetric_pos (x₀ : M) {z : F} (hz : z ∈ (extChartAt 𝓘(ℝ, F) x₀).target) {v : F}
    (hv : v ≠ 0) : 0 < chartMetric (I := 𝓘(ℝ, F)) x₀ z v v := by
  rw [chartMetric_apply]
  apply real_inner_self_pos.mpr
  intro hh
  apply hv
  have hy : (extChartAt 𝓘(ℝ, F) x₀).symm z ∈ (chartAt F x₀).source := extChartAt_symm_mem_source hz
  let t := trivializationAt F (TangentSpace 𝓘(ℝ, F)) x₀
  have hyt : (extChartAt 𝓘(ℝ, F) x₀).symm z ∈ t.baseSet := by simpa [t] using hy
  have he := congrArg (t.continuousLinearMapAt ℝ ((extChartAt 𝓘(ℝ, F) x₀).symm z)) hh
  change t.continuousLinearMapAt ℝ ((extChartAt 𝓘(ℝ, F) x₀).symm z)
    (t.symmL ℝ ((extChartAt 𝓘(ℝ, F) x₀).symm z) v) = _ at he
  rw [t.continuousLinearMapAt_symmL hyt, map_zero] at he
  exact he

/-- The inverse metric `a = G⁻¹` of the chart, as an endomorphism of `F`
(`⟪a v, w⟫ = ⟪v, G⁻¹ w⟫`-form: `G (a v) = ⟪v, ·⟫`). -/
noncomputable def chartCoeff (x₀ : M) (z : F) : F →L[ℝ] F :=
  (chartMetric (I := 𝓘(ℝ, F)) x₀ z).inverse.comp (innerSL ℝ)

theorem chartMetric_chartCoeff (x₀ : M) {z : F} (hz : z ∈ (extChartAt 𝓘(ℝ, F) x₀).target)
    (v w : F) : chartMetric (I := 𝓘(ℝ, F)) x₀ z (chartCoeff F x₀ z v) w = inner ℝ v w := by
  have hinv := chartMetric_isInvertible_of_mem_target (I := 𝓘(ℝ, F)) x₀ hz
  have h := (hinv.inverse_apply_eq (y := innerSL ℝ v)
    (x := chartCoeff F x₀ z v)).1 rfl
  have := congrArg (fun L : StrongDual ℝ F => L w) h
  simpa using this.symm

theorem chartCoeff_symm (x₀ : M) {z : F} (hz : z ∈ (extChartAt 𝓘(ℝ, F) x₀).target) (v w : F) :
    inner ℝ (chartCoeff F x₀ z v) w = inner ℝ v (chartCoeff F x₀ z w) := by
  have h1 := chartMetric_chartCoeff F x₀ hz v (chartCoeff F x₀ z w)
  have h2 := chartMetric_chartCoeff F x₀ hz w (chartCoeff F x₀ z v)
  rw [real_inner_comm] at h2
  rw [← h1, ← h2, chartMetric_symm_apply]

theorem inner_chartCoeff_self (x₀ : M) {z : F} (hz : z ∈ (extChartAt 𝓘(ℝ, F) x₀).target) (v : F) :
    inner ℝ (chartCoeff F x₀ z v) v = chartMetric (I := 𝓘(ℝ, F)) x₀ z (chartCoeff F x₀ z v)
      (chartCoeff F x₀ z v) := by
  have := chartMetric_chartCoeff F x₀ hz v (chartCoeff F x₀ z v)
  rw [real_inner_comm] at this
  exact this.symm

theorem inner_chartCoeff_self_nonneg (x₀ : M) {z : F}
    (hz : z ∈ (extChartAt 𝓘(ℝ, F) x₀).target) (v : F) : 0 ≤ inner ℝ (chartCoeff F x₀ z v) v := by
  rw [inner_chartCoeff_self F x₀ hz]
  by_cases h : chartCoeff F x₀ z v = 0
  · simp [h]
  · exact (chartMetric_pos F x₀ hz h).le

theorem chartCoeff_eq_zero (x₀ : M) {z : F} (hz : z ∈ (extChartAt 𝓘(ℝ, F) x₀).target) {v : F}
    (h : chartCoeff F x₀ z v = 0) : v = 0 := by
  have := chartMetric_chartCoeff F x₀ hz v
  have h2 : ∀ w, inner ℝ v w = 0 := fun w => by rw [← this w, h]; simp
  exact inner_self_eq_zero.1 (h2 v)

theorem inner_chartCoeff_self_pos (x₀ : M) {z : F} (hz : z ∈ (extChartAt 𝓘(ℝ, F) x₀).target)
    {v : F} (hv : v ≠ 0) : 0 < inner ℝ (chartCoeff F x₀ z v) v := by
  rw [inner_chartCoeff_self F x₀ hz]
  exact chartMetric_pos F x₀ hz fun h => hv (chartCoeff_eq_zero F x₀ hz h)

/-- Quantitative form of ellipticity in terms of the operator norm of the metric:
`‖v‖² ≤ ‖G‖ ⟪a v, v⟫`. -/
theorem norm_sq_le_chartCoeff (x₀ : M) {z : F} (hz : z ∈ (extChartAt 𝓘(ℝ, F) x₀).target) (v : F) :
    ‖v‖ ^ 2 ≤ ‖chartMetric (I := 𝓘(ℝ, F)) x₀ z‖ * inner ℝ (chartCoeff F x₀ z v) v := by
  set G := chartMetric (I := 𝓘(ℝ, F)) x₀ z with hG
  set x := chartCoeff F x₀ z v with hx
  have hxv : G x v = ‖v‖ ^ 2 := by
    rw [chartMetric_chartCoeff F x₀ hz, real_inner_self_eq_norm_sq]
  have hcs : (G x v) ^ 2 ≤ G x x * G v v := by
    simp only [hG, chartMetric_apply]
    have := real_inner_mul_inner_self_le (chartFrame (I := 𝓘(ℝ, F)) x₀ x ((extChartAt 𝓘(ℝ, F) x₀).symm z))
      (chartFrame (I := 𝓘(ℝ, F)) x₀ v ((extChartAt 𝓘(ℝ, F) x₀).symm z))
    nlinarith [this]
  have hGv : G v v ≤ ‖G‖ * ‖v‖ ^ 2 := by
    have := G.le_opNorm₂ v v
    calc G v v ≤ |G v v| := le_abs_self _
      _ ≤ ‖G‖ * ‖v‖ * ‖v‖ := by simpa [Real.norm_eq_abs] using this
      _ = ‖G‖ * ‖v‖ ^ 2 := by ring
  have hGx : 0 ≤ G x x := by
    by_cases h : x = 0
    · simp [h]
    · exact (chartMetric_pos F x₀ hz h).le
  rw [inner_chartCoeff_self F x₀ hz]
  by_cases hv0 : v = 0
  · simp [hv0]
  · have hvpos : 0 < ‖v‖ ^ 2 := by positivity
    rw [hxv] at hcs
    have h3 : (‖v‖ ^ 2) ^ 2 ≤ G x x * (‖G‖ * ‖v‖ ^ 2) :=
      hcs.trans (mul_le_mul_of_nonneg_left hGv hGx)
    have h4 : ‖v‖ ^ 2 * ‖v‖ ^ 2 ≤ (‖G‖ * G x x) * ‖v‖ ^ 2 := by nlinarith
    exact le_of_mul_le_mul_right h4 hvpos

theorem exists_chartCoeff_elliptic (x₀ : M) {z : F} (hz : z ∈ (extChartAt 𝓘(ℝ, F) x₀).target) :
    ∃ c > 0, ∀ v : F, c * ‖v‖ ^ 2 ≤ inner ℝ (chartCoeff F x₀ z v) v := by
  refine ⟨1 / (‖chartMetric (I := 𝓘(ℝ, F)) x₀ z‖ + 1), by positivity, fun v => ?_⟩
  have h1 := norm_sq_le_chartCoeff F x₀ hz v
  have h2 := inner_chartCoeff_self_nonneg F x₀ hz v
  have h3 := norm_nonneg (chartMetric (I := 𝓘(ℝ, F)) x₀ z)
  rw [one_div, inv_mul_le_iff₀ (by positivity)]
  nlinarith

theorem contDiffAt_chartCoeff (x₀ : M) {z : F} (hz : z ∈ (extChartAt 𝓘(ℝ, F) x₀).target) :
    ContDiffAt ℝ ∞ (chartCoeff F x₀) z := by
  have h1 : ContDiffAt ℝ ∞ (fun w => (chartMetric (I := 𝓘(ℝ, F)) x₀ w).inverse) z :=
    (chartMetric_isInvertible_of_mem_target (I := 𝓘(ℝ, F)) x₀ hz).contDiffAt_map_inverse.comp z
      (contDiffAt_chartMetric_target_top F x₀ hz)
  exact h1.clm_comp contDiffAt_const

theorem contDiffOn_chartCoeff (x₀ : M) : ContDiffOn ℝ ∞ (chartCoeff F x₀) (chartAt F x₀).target :=
  fun z hz => (contDiffAt_chartCoeff F x₀ (by rw [extChartAt_target_eq]; exact hz)).contDiffWithinAt

end Smooth

section Rho

open CutCur

variable (F : Type) [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]
  {M : Type} [EMetricSpace M] [ChartedSpace F M] [IsManifold 𝓘(ℝ, F) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, F) ∞ F (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [MeasurableSpace M] [BorelSpace M]

/-- The density `ρ = e^{-V∘φ⁻¹} · √det g` of `μ` in the chart `chartAt F x₀`. -/
noncomputable def chartRho (V : M → ℝ) (x₀ : M) : F → ℝ := CutoffRigidity.chartWeight (F := F) x₀ V

theorem chartRho_eq (V : M → ℝ) (x₀ : M) {z : F} (hz : z ∈ (chartAt F x₀).target) :
    chartRho F V x₀ z = Real.exp (-V ((chartAt F x₀).symm z)) * chartVolumeDensity F x₀ z := by
  rw [CutCur.chartVolumeDensity_eq_riemannian F x₀ hz]
  rfl

theorem chartRho_pos (V : M → ℝ) (x₀ : M) {z : F} (hz : z ∈ (chartAt F x₀).target) :
    0 < chartRho F V x₀ z := by
  rw [chartRho_eq F V x₀ hz]
  exact mul_pos (Real.exp_pos _) (CutCur.chartVolumeDensity_pos F x₀ hz)

theorem contDiffAt_chartVolumeDensity_top (x₀ : M) {z : F}
    (hz : z ∈ (extChartAt 𝓘(ℝ, F) x₀).target) :
    ContDiffAt ℝ ∞ (CutoffRigidity.chartRiemannianVolumeDensity (I := 𝓘(ℝ, F)) x₀) z := by
  have hEntry (i j : Fin (Module.finrank ℝ F)) :
      ContDiffAt ℝ ∞ (fun w => CutoffRigidity.chartRiemannianGram (I := 𝓘(ℝ, F)) x₀ w i j) z :=
    ((contDiffAt_chartMetric_target_top F x₀ hz).clm_apply contDiffAt_const).clm_apply
      contDiffAt_const
  have hDet : ContDiffAt ℝ ∞ (fun w => (CutoffRigidity.chartRiemannianGram (I := 𝓘(ℝ, F)) x₀ w).det)
      z := by
    classical
    simp only [Matrix.det_apply]
    fun_prop
  have hPos : 0 < (CutoffRigidity.chartRiemannianGram (I := 𝓘(ℝ, F)) x₀ z).det := by
    rw [← CutoffRigidity.chartRiemannianVolumeDensity_sq]
    exact sq_pos_of_pos (CutoffRigidity.chartRiemannianVolumeDensity_pos x₀ hz)
  have hh := hDet.sqrt hPos.ne'
  convert! hh using 1
  funext w
  exact CutoffRigidity.chartRiemannianVolumeDensity_eq_sqrt x₀ w

theorem contDiffAt_chartRho {V : M → ℝ} (hV : MSmooth F V) (x₀ : M) {z : F}
    (hz : z ∈ (extChartAt 𝓘(ℝ, F) x₀).target) : ContDiffAt ℝ ∞ (chartRho F V x₀) z := by
  have h1 : ContDiffAt ℝ ∞ (V ∘ (extChartAt 𝓘(ℝ, F) x₀).symm) z := by
    have hsymm : ContMDiffAt 𝓘(ℝ, F) 𝓘(ℝ, F) ∞ (extChartAt 𝓘(ℝ, F) x₀).symm z :=
      (contMDiffOn_extChartAt_symm x₀).contMDiffAt (extChartAt_target_nhds hz)
    exact ((hV _).comp z hsymm).contDiffAt
  exact ((Real.contDiff_exp.contDiffAt (x := -(V ((extChartAt 𝓘(ℝ, F) x₀).symm z)))).comp z
    h1.neg).mul (contDiffAt_chartVolumeDensity_top F x₀ hz)

theorem contDiffOn_chartRho {V : M → ℝ} (hV : MSmooth F V) (x₀ : M) :
    ContDiffOn ℝ ∞ (chartRho F V x₀) (chartAt F x₀).target :=
  fun z hz => (contDiffAt_chartRho F hV x₀ (by rw [CutoffRigidity.extChartAt_target_eq]; exact hz)).contDiffWithinAt

end Rho

section Pairing

open CutCur

variable (F : Type) [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]
  {M : Type} [EMetricSpace M] [ChartedSpace F M] [IsManifold 𝓘(ℝ, F) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, F) ∞ F (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [MeasurableSpace M] [BorelSpace M]

/-- Coordinate formula: for `z` in the chart target,
`Γ(u,v)(φ⁻¹ z) = ⟪∇(u∘φ⁻¹)(z), a(z) ∇(v∘φ⁻¹)(z)⟫` for smooth `u, v`. -/
theorem carre_chart_formula (x₀ : M) {z : F} (hz : z ∈ (chartAt F x₀).target) {u v : M → ℝ}
    (hu : MSmooth F u) (hv : MSmooth F v) :
    carre F u v ((chartAt F x₀).symm z) =
      inner ℝ (gradient (u ∘ (chartAt F x₀).symm) z)
        (chartCoeff F x₀ z (gradient (v ∘ (chartAt F x₀).symm) z)) := by
  have hz' : z ∈ (extChartAt 𝓘(ℝ, F) x₀).target := by
    rw [CutoffRigidity.extChartAt_target_eq]; exact hz
  have hu2 : ContMDiff 𝓘(ℝ, F) 𝓘(ℝ, ℝ) 2 u := hu.of_le (WithTop.coe_le_coe.mpr le_top)
  have hv2 : ContMDiff 𝓘(ℝ, F) 𝓘(ℝ, ℝ) 2 v := hv.of_le (WithTop.coe_le_coe.mpr le_top)
  have h1 := CutoffRigidity.inner_manifoldGradient_chart (v := v) x₀ hz'
    ((hu2 _).mdifferentiableAt (by norm_num))
  have h2 := CutoffRigidity.coordinateRiemannianGradient_eq_chartCoordinateField (I := 𝓘(ℝ, F)) x₀ hz'
    ((hv2 _).mdifferentiableAt (by norm_num))
  have h3 : chartCoeff F x₀ z (gradient (v ∘ (chartAt F x₀).symm) z) =
      CutoffRigidity.chartCoordinateField (I := 𝓘(ℝ, F)) x₀
        (CutoffRigidity.manifoldGradient 𝓘(ℝ, F) v) z := by
    rw [← h2]
    simp only [chartCoeff, ContinuousLinearMap.comp_apply, CutoffRigidity.coordinateRiemannianGradient]
    congr 1
    ext w
    simp [gradient]
  rw [h3]
  change inner ℝ (CutoffRigidity.manifoldGradient 𝓘(ℝ, F) u _) (CutoffRigidity.manifoldGradient 𝓘(ℝ, F) v _) = _
  refine h1.trans ?_
  simp only [gradient, InnerProductSpace.toDual_symm_apply]
  rfl

/-- Pairing `∫ Γ(u,v) dμ` in a chart, for `u` supported in the chart source. -/
theorem integral_carre_chart {V : M → ℝ} (hV : MSmooth F V) {μ : Measure M}
    (hμ : IsWeightedVolume F μ V) (x₀ : M) {u v : M → ℝ} (hu : MSmooth F u) (hv : MSmooth F v)
    (hS : tsupport u ⊆ (chartAt F x₀).source) :
    ∫ x, carre F u v x ∂μ = ∫ z in (chartAt F x₀).target, chartRho F V x₀ z *
      inner ℝ (gradient (u ∘ (chartAt F x₀).symm) z)
        (chartCoeff F x₀ z (gradient (v ∘ (chartAt F x₀).symm) z)) := by
  classical
  set φ := chartAt F x₀ with hφ
  set T := φ.target with hTdef
  have hTo : IsOpen T := φ.open_target
  have hTm : MeasurableSet T := hTo.measurableSet
  have hTe : ∀ z ∈ T, z ∈ (extChartAt 𝓘(ℝ, F) x₀).target := fun z hz => by
    rw [CutoffRigidity.extChartAt_target_eq]; exact hz
  have hμ' : (μ.restrict φ.source).map φ =
      (volume.restrict T).withDensity fun z => ENNReal.ofReal (chartRho F V x₀ z) := by
    rw [hμ x₀]
    refine withDensity_congr_ae ?_
    filter_upwards [ae_restrict_mem hTm] with z hz
    rw [chartRho_eq F V x₀ hz]
  have hρcont : ContinuousOn (chartRho F V x₀) T := fun z hz =>
    (contDiffAt_chartRho F hV x₀ (hTe z hz)).continuousAt.continuousWithinAt
  have hρnn : ∀ z ∈ T, 0 ≤ chartRho F V x₀ z := fun z hz => (chartRho_pos F V x₀ hz).le
  have hcarc : ContinuousOn (carre F u v ∘ φ.symm) T :=
    (continuous_carre F hu hv).comp_continuousOn φ.continuousOn_symm
  have hcar0 : ∀ x, x ∉ φ.source → carre F u v x = 0 := fun x hx =>
    carre_eq_zero_off_tsupport F v (fun h => hx (hS h))
  rw [CutoffRigidity.integral_eq_chart_integral x₀ hμ' hρcont hρnn hcarc hcar0]
  refine setIntegral_congr_fun hTm (fun z hz => ?_)
  rw [carre_chart_formula F x₀ hz hu hv]

end Pairing

end CutoffRigidity.Riemann.Diff
