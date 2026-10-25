module

public import CutoffRigidity.SmoothRegularLevelManifold

/-! # Actual smooth maps into the constructed regular level -/

@[expose] public section
open Bundle Set
open scoped Manifold ContDiff Topology
set_option backward.isDefEq.respectTransparency false

namespace CutoffRigidity
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 2 M]
  [BoundarylessManifold I M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {K : Type*} [TopologicalSpace K] {J : ModelWithCorners ℝ F K}
  {P : Type*} [TopologicalSpace P] [ChartedSpace K P]

/-- A genuine `C¹` ambient map whose image is in the actual regular level
is genuinely `C¹` into the constructed level manifold. The level regularity
is proved from its actual coordinate extensions. -/
theorem contMDiff_into_smoothRegularLevel {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) 2 f) (X : (y : M) → TangentSpace I y)
    (hregular : ∀ x, mvfderiv I f x (X x) ≠ 0)
    {g : P → M} (hg : ContMDiff J I 1 g) (hzero : ∀ z, f (g z) = 0) :
    letI := smoothRegularLevelChartedSpace hf X hregular
    ContMDiff J 𝓘(ℝ, EuclideanSpace ℝ (Fin (Module.finrank ℝ E - 1))) 1
      (fun z ↦ (⟨g z, hzero z⟩ : {y : M // f y = 0})) := by
  letI := smoothRegularLevelChartedSpace hf X hregular
  let intoLevel : P → {y : M // f y = 0} := fun z ↦ ⟨g z, hzero z⟩
  have hcont : Continuous intoLevel := hg.continuous.subtype_mk hzero
  intro z
  rw [contMDiffAt_iff_target]
  refine ⟨hcont.continuousAt, ?_⟩
  let d := smoothRegularLevelData hf X hregular (intoLevel z)
  have hy : g z ∈ d.ambientChart.source :=
    (d.mem_levelChart_source (intoLevel z)).mp d.center_mem_levelChart_source
  have hcomp := ((d.contMDiffAt_forwardExtension hy).of_le one_le_two).comp z (hg z)
  simp only [extChartAt_coe, modelWithCornersSelf_coe, Function.id_comp]
  change ContMDiffAt J 𝓘(ℝ, EuclideanSpace ℝ (Fin (Module.finrank ℝ E - 1))) 1
    (d.levelChart ∘ intoLevel) z
  have heq : d.levelChart ∘ intoLevel = d.forwardExtension ∘ g := by
    funext y
    exact d.levelChart_apply (intoLevel y)
  rw [heq]
  exact hcomp

end CutoffRigidity
