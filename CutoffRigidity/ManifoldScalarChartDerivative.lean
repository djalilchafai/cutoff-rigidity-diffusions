module

public import CutoffRigidity.RiemannianChartFrames
public import Mathlib.Geometry.Manifold.Riemannian.Basic

/-! # Actual scalar derivatives in actual manifold charts -/

@[expose] public section
open Bundle Set Filter
open scoped Manifold Topology
set_option backward.isDefEq.respectTransparency false
attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace normedSpaceTangentSpaceVectorSpace

namespace CutoffRigidity

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 2 M]
  [BoundarylessManifold I M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]

/-- A scalar chart derivative in the actual coordinate direction of `X` equals
the original intrinsic differential applied to the original tangent vector. -/
theorem fderiv_chartScalar_direction (x₀ : M) {f : M → ℝ}
    (hf : MDifferentiableAt I 𝓘(ℝ, ℝ) f x₀)
    (X : (x : M) → TangentSpace I x) :
    (fderiv ℝ (f ∘ (extChartAt I x₀).symm) (extChartAt I x₀ x₀))
      (chartCoordinateField (I := I) x₀ X (extChartAt I x₀ x₀)) =
      mvfderiv I f x₀ (X x₀) := by
  let e := extChartAt I x₀
  let z := e x₀
  have hRange : range I ∈ 𝓝 z := range_mem_nhds_isInteriorPoint
    (BoundarylessManifold.isInteriorPoint (I := I) (x := x₀))
  have hsymm : MDifferentiableAt 𝓘(ℝ, E) I e.symm z :=
    (mdifferentiableWithinAt_extChartAt_symm (mem_extChartAt_target x₀)).mdifferentiableAt hRange
  have hf' : MDifferentiableAt I 𝓘(ℝ, ℝ) f (e.symm z) := by
    simpa only [e, z, extChartAt_to_inv] using hf
  have hcoord := (hf'.hasMFDerivAt.comp z hsymm.hasMFDerivAt).hasFDerivAt
  haveI : T2Space ℝ := inferInstance
  have heq := congrArg (fun L : E →L[ℝ] ℝ ↦
    L (chartCoordinateField (I := I) x₀ X z)) hcoord.fderiv
  have hDir : (mfderiv 𝓘(ℝ, E) I e.symm z)
      (chartCoordinateField (I := I) x₀ X z) = X (e.symm z) := by
    change (mfderiv 𝓘(ℝ, E) I e.symm z)
      ((mfderivWithin 𝓘(ℝ, E) I e.symm (range I) z).inverse (X (e.symm z))) = _
    rw [← mfderivWithin_of_mem_nhds hRange]
    have hinv := isInvertible_mfderivWithin_extChartAt_symm (I := I) (mem_extChartAt_target x₀)
    exact (hinv.inverse_apply_eq.mp rfl).symm
  change _ = (mfderiv I 𝓘(ℝ, ℝ) f (e.symm z))
    ((mfderiv 𝓘(ℝ, E) I e.symm z) (chartCoordinateField (I := I) x₀ X z)) at heq
  rw [hDir] at heq
  change _ = (mfderiv I 𝓘(ℝ, ℝ) f x₀) (X x₀)
  exact heq.trans (congrArg (fun y : M ↦ (mfderiv I 𝓘(ℝ, ℝ) f y) (X y))
    (extChartAt_to_inv (I := I) x₀))

end CutoffRigidity
