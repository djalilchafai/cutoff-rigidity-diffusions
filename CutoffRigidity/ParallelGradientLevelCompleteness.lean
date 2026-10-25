module

public import CutoffRigidity.ParallelGradientZeroProjection
public import CutoffRigidity.RiemannianTangentMetricMap

/-! # Intrinsic distance and completeness of the actual parallel-gradient level
The genuine retraction contracts tangent norms. Its actual path-length
contraction and the actual inclusion identify intrinsic and ambient distances.
-/

@[expose] public section
open Bundle Set Manifold
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

local notation "F₀" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E - 1))
local notation "J₀" => 𝓘(ℝ, F₀)
local notation "N₀" => {y : M // f y = 0}

/-- The genuine induced level distance equals the original ambient distance,
proved in both directions from actual path-length comparisons. -/
theorem riemannianEDist_parallelGradientLevel_eq_edist (x₀ : M) (hne : X x₀ ≠ 0) :
    letI := parallelGradientLevelChartedSpace hX hpX hf hgrad x₀ hne
    letI := isManifold_parallelGradientLevel hX hpX hf hgrad x₀ hne
    letI := parallelGradientLevelRiemannianBundle hX hpX hf hgrad x₀ hne
    ∀ y z : N₀, riemannianEDist J₀ y z = edist y.val z.val := by
  letI := parallelGradientLevelChartedSpace hX hpX hf hgrad x₀ hne
  letI := isManifold_parallelGradientLevel hX hpX hf hgrad x₀ hne
  letI := parallelGradientLevelRiemannianBundle hX hpX hf hgrad x₀ hne
  dsimp only
  intro y z
  have hproj := contMDiff_unitParallelGradient_zeroProjection hX hpX hf hgrad x₀ hne
  have hprojNorm := norm_mfderiv_unitParallelGradient_zeroProjection_le hX hpX hf hgrad x₀ hne
  have hinc := (contMDiff_parallelGradientLevel_inclusion hX hpX hf hgrad x₀ hne).of_le one_le_two
  have hincNorm := norm_mfderiv_parallelGradientLevel_inclusion hX hpX hf hgrad x₀ hne
  apply le_antisymm
  · have h := riemannianEDist_le_edist_of_norm_mfderiv_le_between hproj hprojNorm y.val z.val
    simpa only [unitParallelGradient_zeroProjection_inclusion] using h
  · rw [IsRiemannianManifold.out (I := I)]
    exact riemannianEDist_le_riemannianEDist_of_norm_mfderiv_le_between hinc
      (fun x v ↦ (hincNorm x v).le) y z

/-- The actual inherited metric is the genuine Riemannian metric of the
constructed level manifold, rather than an assumed distance identification. -/
theorem isRiemannianManifold_parallelGradientLevel (x₀ : M) (hne : X x₀ ≠ 0) :
    letI := parallelGradientLevelChartedSpace hX hpX hf hgrad x₀ hne
    letI := isManifold_parallelGradientLevel hX hpX hf hgrad x₀ hne
    letI := parallelGradientLevelRiemannianBundle hX hpX hf hgrad x₀ hne
    IsRiemannianManifold J₀ N₀ := by
  letI := parallelGradientLevelChartedSpace hX hpX hf hgrad x₀ hne
  letI := isManifold_parallelGradientLevel hX hpX hf hgrad x₀ hne
  letI := parallelGradientLevelRiemannianBundle hX hpX hf hgrad x₀ hne
  exact ⟨fun y z ↦ (riemannianEDist_parallelGradientLevel_eq_edist hX hpX hf hgrad x₀ hne y z).symm⟩

/-- The paper's actual level factor is complete for its genuine induced
Riemannian distance: distance equality was proved above and closedness supplies
completeness for this same inherited distance. -/
theorem completeRiemannian_parallelGradientLevel (x₀ : M) (hne : X x₀ ≠ 0) :
    letI := parallelGradientLevelChartedSpace hX hpX hf hgrad x₀ hne
    letI := isManifold_parallelGradientLevel hX hpX hf hgrad x₀ hne
    letI := parallelGradientLevelRiemannianBundle hX hpX hf hgrad x₀ hne
    IsRiemannianManifold J₀ N₀ ∧ CompleteSpace N₀ :=
  ⟨isRiemannianManifold_parallelGradientLevel hX hpX hf hgrad x₀ hne,
    completeSpace_parallelGradient_zeroLevel (hf.mdifferentiable (by norm_num))⟩

end CutoffRigidity
