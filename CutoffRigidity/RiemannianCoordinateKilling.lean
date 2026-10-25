module

public import CutoffRigidity.RiemannianChartMetric
public import CutoffRigidity.ParallelFieldKilling
public import Mathlib.Geometry.Manifold.Riemannian.Basic

/-! # The intrinsic parallel-field Killing identity in actual metric coordinates
Actual chart-constant frames convert the actual Levi-Civita identity into the
explicit coefficient identity used by the actual variational metric estimate.
-/

@[expose] public section
open Bundle Set Filter VectorField
open scoped Manifold ContDiff Topology
set_option backward.isDefEq.respectTransparency false

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

namespace CutoffRigidity

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 2 M]
  [BoundarylessManifold I M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)]

/-- The genuine derivative of the genuine chart metric in the genuine
coordinate direction equals the intrinsic derivative of the Gram function. -/
theorem fderiv_chartMetric_direction (x₀ : M) (X : (x : M) → TangentSpace I x) (u v : E) :
    ((fderiv ℝ (chartMetric (I := I) x₀) (extChartAt I x₀ x₀))
      (chartCoordinateField (I := I) x₀ X (extChartAt I x₀ x₀))) u v =
    mvfderiv I (fun y ↦ inner ℝ (chartFrame (I := I) x₀ u y)
      (chartFrame (I := I) x₀ v y)) x₀ (X x₀) := by
  let e := extChartAt I x₀
  let z := e x₀
  let f : M → ℝ := fun y ↦ inner ℝ (chartFrame (I := I) x₀ u y) (chartFrame (I := I) x₀ v y)
  have hRange : range I ∈ 𝓝 z := range_mem_nhds_isInteriorPoint
    (BoundarylessManifold.isInteriorPoint (I := I) (x := x₀))
  have hsymm : MDifferentiableAt 𝓘(ℝ, E) I e.symm z :=
    (mdifferentiableWithinAt_extChartAt_symm (mem_extChartAt_target x₀)).mdifferentiableAt hRange
  have hf : MDifferentiableAt I 𝓘(ℝ, ℝ) f (e.symm z) := by
    simpa only [e, z, extChartAt_to_inv] using
      (contMDiffAt_chartFrame_inner (I := I) x₀ u v).mdifferentiableAt one_ne_zero
  have hcoord := (hf.hasMFDerivAt.comp z hsymm.hasMFDerivAt).hasFDerivAt
  have hMetricFD := ((contDiffAt_chartMetric (I := I) x₀).differentiableAt one_ne_zero).hasFDerivAt
  have hpair := (hMetricFD.clm_apply (hasFDerivAt_const u z)).clm_apply (hasFDerivAt_const v z)
  change HasFDerivAt (f ∘ e.symm) _ z at hpair
  have heq := congrArg (fun L : E →L[ℝ] ℝ ↦
    L (chartCoordinateField (I := I) x₀ X z)) (hpair.unique hcoord)
  simp only [add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply, zero_apply, map_zero, zero_add] at heq
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

/-- Parallelism for the actual Levi-Civita connection yields the exact raw
Killing coefficient identity for the original Riemannian metric. -/
theorem coordinate_killing_of_parallel
    (x₀ : M) {X : (x : M) → TangentSpace I x}
    (hX : MDifferentiableAt I I.tangent (T% X) x₀)
    (hpX : CovariantDerivative.leviCivitaConnection I M X x₀ = 0) (u v : E) :
    ((fderiv ℝ (chartMetric (I := I) x₀) (extChartAt I x₀ x₀))
      (chartCoordinateField (I := I) x₀ X (extChartAt I x₀ x₀))) u v +
      chartMetric (I := I) x₀ (extChartAt I x₀ x₀)
        ((fderiv ℝ (chartCoordinateField (I := I) x₀ X) (extChartAt I x₀ x₀)) u) v +
      chartMetric (I := I) x₀ (extChartAt I x₀ x₀) u
        ((fderiv ℝ (chartCoordinateField (I := I) x₀ X) (extChartAt I x₀ x₀)) v) = 0 := by
  have h := parallel_field_killing_identity hX
    ((contMDiffAt_chartFrame (I := I) x₀ u).mdifferentiableAt one_ne_zero)
    ((contMDiffAt_chartFrame (I := I) x₀ v).mdifferentiableAt one_ne_zero) hpX
  rw [mlieBracket_chartFrame, mlieBracket_chartFrame] at h
  rw [fderiv_chartMetric_direction]
  rw [chartMetric_center_apply, chartMetric_center_apply]
  have hneg (w : E) : chartFrame (I := I) x₀ (-w) x₀ = -chartFrame (I := I) x₀ w x₀ :=
    (chartFrameCLM (I := I) x₀ x₀).map_neg w
  simp only [hneg, inner_neg_left, inner_neg_right] at h
  linarith

end CutoffRigidity
