module

public import CutoffRigidity.SmoothRiemannianPullbackMetric

/-! # The actual induced Riemannian metric on the parallel-gradient level -/

@[expose] public section
open Bundle Set
open scoped Manifold ContDiff Topology
set_option backward.isDefEq.respectTransparency false

namespace CutoffRigidity
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [EMetricSpace M] [ChartedSpace H M] [IsManifold I 2 M]
  [BoundarylessManifold I M] [CompleteSpace M] [PreconnectedSpace M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)]
  [IsRiemannianManifold I M]

/-- The actual zero-level metric is induced from the original metric by the
actual inclusion differential. All immersion obligations have been proved. -/
@[instance_reducible] noncomputable def parallelGradientLevelRiemannianBundle
    {X : (x : M) → TangentSpace I x} (hX : ContMDiff I I.tangent 1 (T% X))
    (hpX : ∀ x, CovariantDerivative.leviCivitaConnection I M X x = 0)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) 2 f)
    (hgrad : ∀ x v, mvfderiv I f x v = inner ℝ (X x) v)
    (x₀ : M) (hne : X x₀ ≠ 0) :
    letI := parallelGradientLevelChartedSpace hX hpX hf hgrad x₀ hne
    letI := isManifold_parallelGradientLevel hX hpX hf hgrad x₀ hne
    RiemannianBundle (fun x : {y : M // f y = 0} ↦
      TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin (Module.finrank ℝ E - 1))) x) := by
  letI := parallelGradientLevelChartedSpace hX hpX hf hgrad x₀ hne
  letI := isManifold_parallelGradientLevel hX hpX hf hgrad x₀ hne
  exact immersionPullbackRiemannianBundle (Subtype.val : {y : M // f y = 0} → M)
    (injective_mfderiv_parallelGradientLevel_inclusion hX hpX hf hgrad x₀ hne)

/-- The actual inclusion preserves tangent norms for the constructed actual
level metric. This conclusion does not assume an isometric immersion. -/
theorem norm_mfderiv_parallelGradientLevel_inclusion
    {X : (x : M) → TangentSpace I x} (hX : ContMDiff I I.tangent 1 (T% X))
    (hpX : ∀ x, CovariantDerivative.leviCivitaConnection I M X x = 0)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) 2 f)
    (hgrad : ∀ x v, mvfderiv I f x v = inner ℝ (X x) v)
    (x₀ : M) (hne : X x₀ ≠ 0) :
    letI := parallelGradientLevelChartedSpace hX hpX hf hgrad x₀ hne
    letI := isManifold_parallelGradientLevel hX hpX hf hgrad x₀ hne
    letI := parallelGradientLevelRiemannianBundle hX hpX hf hgrad x₀ hne
    ∀ (x : {y : M // f y = 0})
      (v : TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin (Module.finrank ℝ E - 1))) x),
      ‖(mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin (Module.finrank ℝ E - 1))) I
        (Subtype.val : {y : M // f y = 0} → M) x) v‖ = ‖v‖ := by
  letI := parallelGradientLevelChartedSpace hX hpX hf hgrad x₀ hne
  letI := isManifold_parallelGradientLevel hX hpX hf hgrad x₀ hne
  exact norm_mfderiv_immersionPullback (Subtype.val : {y : M // f y = 0} → M)
    (injective_mfderiv_parallelGradientLevel_inclusion hX hpX hf hgrad x₀ hne)

/-- The constructed induced metric is genuinely `C¹`, derived from the actual
`C²` level inclusion and the original actual `C¹` metric. -/
theorem isContMDiffRiemannianBundle_parallelGradientLevel
    {X : (x : M) → TangentSpace I x} (hX : ContMDiff I I.tangent 1 (T% X))
    (hpX : ∀ x, CovariantDerivative.leviCivitaConnection I M X x = 0)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) 2 f)
    (hgrad : ∀ x v, mvfderiv I f x v = inner ℝ (X x) v)
    (x₀ : M) (hne : X x₀ ≠ 0) :
    letI := parallelGradientLevelChartedSpace hX hpX hf hgrad x₀ hne
    letI := isManifold_parallelGradientLevel hX hpX hf hgrad x₀ hne
    letI := parallelGradientLevelRiemannianBundle hX hpX hf hgrad x₀ hne
    IsContMDiffRiemannianBundle
      𝓘(ℝ, EuclideanSpace ℝ (Fin (Module.finrank ℝ E - 1))) 1
      (EuclideanSpace ℝ (Fin (Module.finrank ℝ E - 1)))
      (fun x : {y : M // f y = 0} ↦
        TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin (Module.finrank ℝ E - 1))) x) := by
  letI := parallelGradientLevelChartedSpace hX hpX hf hgrad x₀ hne
  letI := isManifold_parallelGradientLevel hX hpX hf hgrad x₀ hne
  exact isContMDiffRiemannianBundle_immersionPullback
    (Subtype.val : {y : M // f y = 0} → M)
    (contMDiff_parallelGradientLevel_inclusion hX hpX hf hgrad x₀ hne)
    (injective_mfderiv_parallelGradientLevel_inclusion hX hpX hf hgrad x₀ hne)

end CutoffRigidity
