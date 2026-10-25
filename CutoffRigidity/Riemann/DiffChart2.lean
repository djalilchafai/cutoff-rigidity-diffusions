module

public import CutoffRigidity.Riemann.DiffChart1

/-! # The coordinate gradient of a test function is controlled in `L²(ν)` by the energy
(workstream DIR) -/

@[expose] public section

open Bundle MeasureTheory Filter Set
open scoped Manifold ContDiff ENNReal Topology

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace CutoffRigidity.Riemann.Diff

open CutCur

theorem eLpNorm_two_sq {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E] {f : α → E}
    {μ : Measure α} (hf : AEStronglyMeasurable f μ) :
    eLpNorm f 2 μ ^ 2 = ∫⁻ x, ‖f x‖ₑ ^ 2 ∂μ := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by simp) hf]
  have h2 : (2 : ℝ≥0∞).toReal = 2 := by simp
  rw [h2, ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
  norm_num

section Grad

variable (F : Type) [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]
  {M : Type} [EMetricSpace M] [ChartedSpace F M] [IsManifold 𝓘(ℝ, F) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, F) ∞ F (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [MeasurableSpace M] [BorelSpace M]

/-- The coordinate gradient `∇(a∘φ⁻¹)` in the chart `chartAt F x₀`. -/
noncomputable def chartGrad (x₀ : M) (a : M → ℝ) (z : F) : F :=
  gradient (a ∘ (chartAt F x₀).symm) z

theorem contDiffOn_chartCoord (x₀ : M) {a : M → ℝ} (ha : MSmooth F a) :
    ContDiffOn ℝ ∞ (a ∘ (chartAt F x₀).symm) (chartAt F x₀).target := by
  intro z hz
  have hz' : z ∈ (extChartAt 𝓘(ℝ, F) x₀).target := by
    rw [CutoffRigidity.extChartAt_target_eq]; exact hz
  have hsymm : ContMDiffAt 𝓘(ℝ, F) 𝓘(ℝ, F) ∞ (extChartAt 𝓘(ℝ, F) x₀).symm z :=
    (contMDiffOn_extChartAt_symm x₀).contMDiffAt (extChartAt_target_nhds hz')
  exact ((ha _).comp z hsymm).contDiffAt.contDiffWithinAt

theorem differentiableAt_chartCoord (x₀ : M) {a : M → ℝ} (ha : MSmooth F a) {z : F}
    (hz : z ∈ (chartAt F x₀).target) :
    DifferentiableAt ℝ (a ∘ (chartAt F x₀).symm) z :=
  ((contDiffOn_chartCoord F x₀ ha).contDiffAt ((chartAt F x₀).open_target.mem_nhds hz)).differentiableAt
    (by simp)

theorem continuousOn_chartGrad (x₀ : M) {a : M → ℝ} (ha : MSmooth F a) :
    ContinuousOn (chartGrad F x₀ a) (chartAt F x₀).target := by
  have h := (contDiffOn_chartCoord F x₀ ha).continuousOn_fderiv_of_isOpen
    (chartAt F x₀).open_target (by simp)
  exact (InnerProductSpace.toDual ℝ F).symm.continuous.comp_continuousOn h

theorem chartGrad_sub (x₀ : M) {a b : M → ℝ} (ha : MSmooth F a) (hb : MSmooth F b) {z : F}
    (hz : z ∈ (chartAt F x₀).target) :
    chartGrad F x₀ (a - b) z = chartGrad F x₀ a z - chartGrad F x₀ b z := by
  have h1 := differentiableAt_chartCoord F x₀ ha hz
  have h2 := differentiableAt_chartCoord F x₀ hb hz
  unfold chartGrad gradient
  have : (a - b) ∘ (chartAt F x₀).symm = (a ∘ (chartAt F x₀).symm) - (b ∘ (chartAt F x₀).symm) := rfl
  rw [this, fderiv_sub h1 h2, map_sub]

/-- Pointwise energy bound `κ ‖∇ã‖² ≤ ρ Γ(a,a)∘φ⁻¹`. -/
theorem chartKappa_mul_norm_sq_le (V : M → ℝ) (x₀ : M) {a : M → ℝ} (ha : MSmooth F a) {z : F}
    (hz : z ∈ (chartAt F x₀).target) :
    chartKappa F V x₀ z * ‖chartGrad F x₀ a z‖ ^ 2 ≤
      chartRho F V x₀ z * carre F a a ((chartAt F x₀).symm z) := by
  have hz' : z ∈ (extChartAt 𝓘(ℝ, F) x₀).target := by
    rw [CutoffRigidity.extChartAt_target_eq]; exact hz
  have hcar := carre_chart_formula F x₀ hz ha ha
  have hnorm := norm_sq_le_chartCoeff F x₀ hz' (chartGrad F x₀ a z)
  have hsym := chartCoeff_symm F x₀ hz' (chartGrad F x₀ a z) (chartGrad F x₀ a z)
  have hnn := inner_chartCoeff_self_nonneg F x₀ hz' (chartGrad F x₀ a z)
  have hrho := chartRho_pos F V x₀ hz
  have hG := norm_nonneg (chartMetric (I := 𝓘(ℝ, F)) x₀ z)
  unfold chartKappa
  rw [hcar]
  show _ ≤ chartRho F V x₀ z * inner ℝ (chartGrad F x₀ a z) (chartCoeff F x₀ z (chartGrad F x₀ a z))
  rw [real_inner_comm]
  rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
  nlinarith [mul_nonneg hrho.le hnn, mul_nonneg hrho.le hG, mul_nonneg (mul_nonneg hrho.le hG) hnn]

section Estimates

variable {V : M → ℝ} (hV : MSmooth F V) {μ : Measure M} [IsFiniteMeasure μ]
  (hμ : IsWeightedVolume F μ V) (x₀ : M)

theorem chartNu_ac : chartNu F V x₀ ≪ volume.restrict (chartAt F x₀).target :=
  withDensity_absolutelyContinuous _ _

include hV in
theorem integrable_carre_test (a b : testSub F M) :
    Integrable (fun x => carre F (a : M → ℝ) (b : M → ℝ) x) μ := by
  have hs : MSmooth F (carre F (a : M → ℝ) (b : M → ℝ)) := (weightedRegular V hV).1 _ _ a.2.1 b.2.1
  exact hs.continuous.integrable_of_hasCompactSupport (hasCompactSupport_carre F _ a.2.2)

include hV hμ in
/-- Transport of measurable functions from `M` to the chart does not increase the `L²`-norms
(`ν ≤ ρ dz`). -/
theorem eLpNorm_chartNu_comp_le {H : M → ℝ} (hH : Measurable H) :
    AEStronglyMeasurable (fun z => H ((chartAt F x₀).symm z)) (chartNu F V x₀) ∧
      eLpNorm (fun z => H ((chartAt F x₀).symm z)) 2 (chartNu F V x₀) ≤ eLpNorm H 2 μ := by
  have hTm : MeasurableSet (chartAt F x₀).target := (chartAt F x₀).open_target.measurableSet
  have hmeas : AEMeasurable (fun z => H ((chartAt F x₀).symm z))
      (volume.restrict (chartAt F x₀).target) :=
    hH.comp_aemeasurable ((chartAt F x₀).continuousOn_symm.aemeasurable hTm)
  have hasm : AEStronglyMeasurable (fun z => H ((chartAt F x₀).symm z)) (chartNu F V x₀) :=
    (hmeas.aestronglyMeasurable).mono_ac (chartNu_ac F x₀)
  refine ⟨hasm, ?_⟩
  have h1 := eLpNorm_two_sq hasm
  have h2 := eLpNorm_two_sq (hH.aestronglyMeasurable (μ := μ))
  have h3 := lintegral_chartNu_comp F hV hμ x₀ (fun x => ‖H x‖ₑ ^ 2)
    ((hH.enorm).pow_const 2)
  have h4 : eLpNorm (fun z => H ((chartAt F x₀).symm z)) 2 (chartNu F V x₀) ^ 2 ≤
      eLpNorm H 2 μ ^ 2 := by
    rw [h1, h2]; exact h3
  exact (ENNReal.pow_le_pow_left_iff (by norm_num)).1 h4

include hV hμ in
/-- The energy controls the `L²(ν)` norm of the coordinate gradient. -/
theorem chartGrad_lintegral_le (a : testSub F M) :
    ∫⁻ z, ‖chartGrad F x₀ (a : M → ℝ) z‖ₑ ^ 2 ∂(chartNu F V x₀) ≤
      ENNReal.ofReal (∫ x, carre F (a : M → ℝ) (a : M → ℝ) x ∂μ) := by
  set φ := chartAt F x₀ with hφ
  have hTm : MeasurableSet φ.target := φ.open_target.measurableSet
  have hgm : AEMeasurable (fun z => ‖chartGrad F x₀ (a : M → ℝ) z‖ₑ ^ 2)
      (volume.restrict φ.target) :=
    (((continuousOn_chartGrad F x₀ a.2.1).aestronglyMeasurable hTm).enorm).pow_const 2
  unfold chartNu
  rw [lintegral_withDensity_eq_lintegral_mul₀ (aemeasurable_chartKappa F hV x₀) hgm]
  have hΓm : Measurable (fun x => ENNReal.ofReal (carre F (a : M → ℝ) (a : M → ℝ) x)) :=
    ENNReal.measurable_ofReal.comp (continuous_carre F a.2.1 a.2.1).measurable
  calc ∫⁻ z in φ.target, (fun z => ENNReal.ofReal (chartKappa F V x₀ z)) z *
        ‖chartGrad F x₀ (a : M → ℝ) z‖ₑ ^ 2
      ≤ ∫⁻ z in φ.target, ENNReal.ofReal (chartRho F V x₀ z) *
          ENNReal.ofReal (carre F (a : M → ℝ) (a : M → ℝ) (φ.symm z)) := by
        refine setLIntegral_mono' hTm fun z hz => ?_
        have h := chartKappa_mul_norm_sq_le F V x₀ a.2.1 hz
        have hκ := (chartKappa_pos F V x₀ hz).le
        have e1 : ‖chartGrad F x₀ (a : M → ℝ) z‖ₑ ^ 2 =
            ENNReal.ofReal (‖chartGrad F x₀ (a : M → ℝ) z‖ ^ 2) := by
          rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
        have hρ := (chartRho_pos F V x₀ hz).le
        show ENNReal.ofReal (chartKappa F V x₀ z) * _ ≤ _
        rw [e1, ← ENNReal.ofReal_mul hκ, ← ENNReal.ofReal_mul hρ]
        exact ENNReal.ofReal_le_ofReal h
    _ = ∫⁻ x in φ.source, ENNReal.ofReal (carre F (a : M → ℝ) (a : M → ℝ) x) ∂μ :=
        lintegral_chart F hV hμ x₀ _ hΓm
    _ ≤ ∫⁻ x, ENNReal.ofReal (carre F (a : M → ℝ) (a : M → ℝ) x) ∂μ :=
        setLIntegral_le_lintegral _ _
    _ = ENNReal.ofReal (∫ x, carre F (a : M → ℝ) (a : M → ℝ) x ∂μ) := by
        rw [ofReal_integral_eq_lintegral_ofReal (integrable_carre_test F hV (μ := μ) a a)
          (Eventually.of_forall fun x => carre_nonneg F _ x)]

end Estimates

end Grad

end CutoffRigidity.Riemann.Diff
