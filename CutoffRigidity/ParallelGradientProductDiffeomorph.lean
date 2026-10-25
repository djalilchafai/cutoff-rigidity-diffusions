module

public import CutoffRigidity.CompleteBoundedFlowJointC1
public import CutoffRigidity.ParallelGradientLevelMetric
public import CutoffRigidity.SmoothRegularLevelMaps

/-! # The actual parallel-gradient product is a `C¹` diffeomorphism
The original canonical complete flow constructs the product map; the actual
level atlas and joint flow regularity establish smoothness in both directions.
-/

@[expose] public section
open Bundle Set
open scoped Manifold ContDiff Topology NNReal ENNReal
set_option backward.isDefEq.respectTransparency false

namespace CutoffRigidity
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [EMetricSpace M] [ChartedSpace H M] [IsManifold I 2 M]
  [BoundarylessManifold I M] [CompleteSpace M] [PreconnectedSpace M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)]
  [IsRiemannianManifold I M]
  {X : (x : M) → TangentSpace I x} (hX : ContMDiff I I.tangent 1 (T% X))
  (hpX : ∀ x, CovariantDerivative.leviCivitaConnection I M X x = 0)
  {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) 2 f)
  (hgrad : ∀ x v, mvfderiv I f x v = inner ℝ (X x) v)

/-- The actual product homeomorphism is genuinely `C¹` jointly in its real
coordinate and its actual level-manifold coordinate. -/
theorem contMDiff_unitParallelGradientLevelHomeomorph (x₀ : M) (hne : X x₀ ≠ 0) :
    letI := parallelGradientLevelChartedSpace hX hpX hf hgrad x₀ hne
    ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin (Module.finrank ℝ E - 1)))) I 1
      (unitParallelGradientLevelHomeomorph hX hpX (hf.mdifferentiable (by norm_num)) hgrad x₀ hne) := by
  letI := parallelGradientLevelChartedSpace hX hpX hf hgrad x₀ hne
  have hY := hX.const_smul_section (a := ‖X x₀‖⁻¹)
  have hb := unitParallelField_enorm_le_one hX hpX x₀ hne
  have hflow := contMDiff_completeBoundedFlow_joint hY hb
  have hinc := (contMDiff_parallelGradientLevel_inclusion hX hpX hf hgrad x₀ hne).of_le one_le_two
  have hq : ContMDiff
      (𝓘(ℝ, ℝ).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin (Module.finrank ℝ E - 1))))
      (I.prod 𝓘(ℝ, ℝ)) 1 (fun p : ℝ × {y : M // f y = 0} ↦ (p.2.val, p.1)) :=
    (hinc.comp contMDiff_snd).prodMk contMDiff_fst
  convert! hflow.comp hq using 1

/-- The actual inverse product map is genuinely `C¹`, using the proved smooth
criterion for maps into the actual regular level. -/
theorem contMDiff_unitParallelGradientLevelHomeomorph_symm (x₀ : M) (hne : X x₀ ≠ 0) :
    letI := parallelGradientLevelChartedSpace hX hpX hf hgrad x₀ hne
    ContMDiff I (𝓘(ℝ, ℝ).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin (Module.finrank ℝ E - 1)))) 1
      (unitParallelGradientLevelHomeomorph hX hpX (hf.mdifferentiable (by norm_num)) hgrad x₀ hne).symm := by
  letI := parallelGradientLevelChartedSpace hX hpX hf hgrad x₀ hne
  let e := unitParallelGradientLevelHomeomorph hX hpX (hf.mdifferentiable (by norm_num)) hgrad x₀ hne
  have hY := hX.const_smul_section (a := ‖X x₀‖⁻¹)
  have hb := unitParallelField_enorm_le_one hX hpX x₀ hne
  have hflow := contMDiff_completeBoundedFlow_joint hY hb
  have hscale : ContDiff ℝ 1 (fun r : ℝ ↦ r / ‖X x₀‖) := contDiff_id.div_const _
  have htime : ContMDiff I 𝓘(ℝ, ℝ) 1 (fun x ↦ -f x / ‖X x₀‖) :=
    hscale.contMDiff.comp (hf.of_le one_le_two).neg
  have hg : ContMDiff I I 1 (fun x ↦ (e.symm x).2.val) := by
    convert! hflow.comp (contMDiff_id.prodMk htime) using 1
  have hlevel : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin (Module.finrank ℝ E - 1))) 1
      (fun x ↦ (e.symm x).2) := by
    convert! contMDiff_into_smoothRegularLevel hf X
      (parallelGradient_differential_ne_zero hX hpX hgrad x₀ hne) hg
      (fun x ↦ (e.symm x).2.property) using 1
  have hreal : ContMDiff I 𝓘(ℝ, ℝ) 1 (fun x ↦ f x / ‖X x₀‖) :=
    hscale.contMDiff.comp (hf.of_le one_le_two)
  convert! hreal.prodMk hlevel using 1

/-- The original flow product is an actual `C¹` diffeomorphism. Neither a
splitting nor differentiability of the product map is assumed. -/
noncomputable def unitParallelGradientLevelDiffeomorph (x₀ : M) (hne : X x₀ ≠ 0) :
    letI := parallelGradientLevelChartedSpace hX hpX hf hgrad x₀ hne
    Diffeomorph (𝓘(ℝ, ℝ).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin (Module.finrank ℝ E - 1))))
      I (ℝ × {y : M // f y = 0}) M 1 := by
  letI := parallelGradientLevelChartedSpace hX hpX hf hgrad x₀ hne
  exact
    { toEquiv := (unitParallelGradientLevelHomeomorph hX hpX
        (hf.mdifferentiable (by norm_num)) hgrad x₀ hne).toEquiv
      contMDiff_toFun := contMDiff_unitParallelGradientLevelHomeomorph hX hpX hf hgrad x₀ hne
      contMDiff_invFun := contMDiff_unitParallelGradientLevelHomeomorph_symm hX hpX hf hgrad x₀ hne }

end CutoffRigidity
