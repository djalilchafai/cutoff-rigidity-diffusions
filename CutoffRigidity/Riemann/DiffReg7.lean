module

public import CutoffRigidity.Riemann.DiffReg6

/-! # Interior sup estimate, part 3: local estimate in a chart (workstream KER-REG) -/

@[expose] public section

open Bundle MeasureTheory Filter Set Topology
open scoped ContDiff ENNReal Manifold

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace CutoffRigidity.Riemann.Diff

open CutCur

section Local

variable (F : Type) [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]
  {M : Type} [EMetricSpace M] [ChartedSpace F M] [IsManifold 𝓘(ℝ, F) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, F) ∞ F (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [MeasurableSpace M] [BorelSpace M]
  [IsRiemannianManifold 𝓘(ℝ, F) M] [ConnectedSpace M] [CompleteSpace M]
  {V : M → ℝ} (hV : MSmooth F V) {μ : Measure M} [IsFiniteMeasure μ]
  (hμ : IsWeightedVolume F μ V) (x₀ : M)

include hV hμ in
/-- Comparison of the chart `L²` norm of `χ' w̃` with the `L²(μ|W)` norm of `w`. -/
theorem chart_L2_compare {W : Set M} (hW : IsOpen W) {χ' : F → ℝ} (hχc : Continuous χ')
    (hχcs : HasCompactSupport χ')
    (hsub : tsupport χ' ⊆ (chartAt F x₀).target ∩ (chartAt F x₀).symm ⁻¹' W) :
    ∃ c₁ : ℝ, 0 ≤ c₁ ∧ ∀ w : M → ℝ, Continuous w → Integrable (fun y => w y ^ 2) (μ.restrict W) →
      ∫ z, (χ' z * w ((chartAt F x₀).symm z)) ^ 2 ≤ c₁ * ∫ y in W, w y ^ 2 ∂μ := by
  set φ := chartAt F x₀ with hφ
  have hTm : MeasurableSet φ.target := φ.open_target.measurableSet
  have hK : IsCompact (tsupport χ') := hχcs
  have hKT : tsupport χ' ⊆ φ.target := hsub.trans inter_subset_left
  obtain ⟨δ, hδ, hδK⟩ := hK.exists_forall_le'
    ((contDiffOn_chartRho F hV x₀).continuousOn.mono hKT) (a := 0)
    (fun z hz => chartRho_pos F V x₀ (hKT hz))
  obtain ⟨B, hB⟩ := hχcs.exists_bound_of_continuous hχc
  have hc₁ : 0 ≤ B ^ 2 / δ := by positivity
  refine ⟨B ^ 2 / δ, hc₁, fun w hwc hint => ?_⟩
  set f : F → ℝ := fun z => (χ' z * w (φ.symm z)) ^ 2 with hf
  have hf0 : ∀ z, z ∉ tsupport χ' → f z = 0 := fun z hz => by
    simp [hf, image_eq_zero_of_notMem_tsupport hz]
  have hwT : ContinuousOn (fun z => w (φ.symm z)) φ.target :=
    hwc.comp_continuousOn φ.continuousOn_symm
  have hI : Integrable f := by
    have h1 : IntegrableOn f φ.target := by
      refine integrableOn_target_of_support F x₀ hχcs hKT ?_ hf0
      exact (hχc.continuousOn.mul hwT).pow 2
    refine h1.integrable_of_forall_notMem_eq_zero fun z hz => hf0 z (fun h => hz (hKT h))
  set ind : M → ℝ := W.indicator (fun y => w y ^ 2) with hind
  have hind0 : ∀ y, 0 ≤ ind y := fun y => Set.indicator_nonneg (fun _ _ => sq_nonneg _) y
  have hindm : Measurable ind := (hwc.measurable.pow_const 2).indicator hW.measurableSet
  set G : M → ℝ≥0∞ := fun y => ENNReal.ofReal (ind y) with hG
  have hGm : Measurable G := hindm.ennreal_ofReal
  have hindi : Integrable ind μ := (integrable_indicator_iff hW.measurableSet).2 hint
  have hJ : ∫ x, ind x ∂μ = ∫ y in W, w y ^ 2 ∂μ := integral_indicator hW.measurableSet
  have hJ0 : 0 ≤ ∫ y in W, w y ^ 2 ∂μ := setIntegral_nonneg hW.measurableSet fun y _ => sq_nonneg _
  have hpt : ∀ z ∈ φ.target, ENNReal.ofReal (f z) ≤
      ENNReal.ofReal (B ^ 2 / δ) * (ENNReal.ofReal (chartRho F V x₀ z) * G (φ.symm z)) := by
    intro z hz
    have hρ := chartRho_pos F V x₀ hz
    rw [hG]
    simp only
    rw [← ENNReal.ofReal_mul hρ.le, ← ENNReal.ofReal_mul hc₁]
    refine ENNReal.ofReal_le_ofReal ?_
    by_cases hzK : z ∈ tsupport χ'
    · have hW' : φ.symm z ∈ W := (hsub hzK).2
      have hi : ind (φ.symm z) = w (φ.symm z) ^ 2 := by simp [hind, hW']
      rw [hi]
      have h1 : χ' z ^ 2 ≤ B ^ 2 := by
        have := hB z
        rw [Real.norm_eq_abs] at this
        exact sq_le_sq' (by linarith [abs_nonneg (χ' z), neg_abs_le (χ' z)]) (by linarith [le_abs_self (χ' z)])
      have h2 : B ^ 2 ≤ B ^ 2 / δ * chartRho F V x₀ z := by
        have := hδK z hzK
        calc B ^ 2 = B ^ 2 / δ * δ := by field_simp
          _ ≤ _ := mul_le_mul_of_nonneg_left this hc₁
      calc f z = χ' z ^ 2 * w (φ.symm z) ^ 2 := by simp [hf, mul_pow]
        _ ≤ B ^ 2 * w (φ.symm z) ^ 2 := mul_le_mul_of_nonneg_right h1 (sq_nonneg _)
        _ ≤ (B ^ 2 / δ * chartRho F V x₀ z) * w (φ.symm z) ^ 2 :=
            mul_le_mul_of_nonneg_right h2 (sq_nonneg _)
        _ = _ := by ring
    · rw [hf0 z hzK]
      exact mul_nonneg hc₁ (mul_nonneg hρ.le (hind0 _))
  have hsupp : Function.support (fun z => ENNReal.ofReal (f z)) ⊆ φ.target := by
    intro z hz
    by_contra hzT
    apply hz
    simp [hf0 z (fun h => hzT (hKT h))]
  have hchain : ENNReal.ofReal (∫ z, f z) ≤
      ENNReal.ofReal (B ^ 2 / δ * ∫ y in W, w y ^ 2 ∂μ) := by
    rw [ofReal_integral_eq_lintegral_ofReal hI (Filter.Eventually.of_forall fun z => sq_nonneg _),
      ← setLIntegral_eq_of_support_subset hsupp]
    calc ∫⁻ z in φ.target, ENNReal.ofReal (f z)
        ≤ ∫⁻ z in φ.target, ENNReal.ofReal (B ^ 2 / δ) *
            (ENNReal.ofReal (chartRho F V x₀ z) * G (φ.symm z)) :=
          setLIntegral_mono' hTm hpt
      _ = ENNReal.ofReal (B ^ 2 / δ) * ∫⁻ z in φ.target,
            ENNReal.ofReal (chartRho F V x₀ z) * G (φ.symm z) :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ = ENNReal.ofReal (B ^ 2 / δ) * ∫⁻ x in φ.source, G x ∂μ := by
          rw [lintegral_chart F hV hμ x₀ G hGm]
      _ ≤ ENNReal.ofReal (B ^ 2 / δ) * ∫⁻ x, G x ∂μ :=
          mul_le_mul' le_rfl (setLIntegral_le_lintegral _ _)
      _ = ENNReal.ofReal (B ^ 2 / δ * ∫ y in W, w y ^ 2 ∂μ) := by
          rw [ENNReal.ofReal_mul hc₁, ← hJ, ofReal_integral_eq_lintegral_ofReal hindi
            (Filter.Eventually.of_forall hind0)]
  exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hc₁ hJ0)).1 hchain

end Local

end CutoffRigidity.Riemann.Diff
