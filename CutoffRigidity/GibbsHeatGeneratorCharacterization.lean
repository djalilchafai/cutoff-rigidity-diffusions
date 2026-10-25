module

public import CutoffRigidity.GibbsHeatMarkov
public import CutoffRigidity.LangevinL2Operator
public import CutoffRigidity.GibbsHeatGenerator
public import Mathlib.Analysis.Calculus.TangentCone.Real

/-! # The full strong generator domain of actual Gibbs form heat

Symmetry transfers a strong derivative at zero to duality against every
actual operator-domain test. Self-adjointness then puts the initial value
in the true operator graph. Thus graph membership and strong right time
differentiability are equivalent, not merely one-way generator consistency.
-/

public section

namespace CutoffRigidity

open MeasureTheory Set Filter Topology

variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

/-- The canonical heat has exactly the actual self-adjoint generator domain. -/
theorem gibbsHeatSemigroup_hasDerivWithinAt_zero_iff_graph {V : E → ℝ}
    (hV : ContDiff ℝ 2 V) (hp : IsProbabilityMeasure (gibbsMeasure volume V))
    (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (u g : E →₂[gibbsMeasure volume V] ℝ) :
    HasDerivWithinAt (fun s : ℝ => gibbsHeatSemigroup hV hp ρ hρ hHess s.toNNReal u)
      (-g) (Ici 0) 0 ↔ (u,g) ∈ (gibbsPositiveGenerator hV hp).graph := by
  constructor
  · intro hu
    let A := gibbsPositiveGenerator hV hp
    have hpair (v h : E →₂[gibbsMeasure volume V] ℝ) (hvh : (v,h) ∈ A.graph) :
        inner ℝ g v = inner ℝ u h := by
      have hv := gibbsHeatSemigroup_hasDerivWithinAt_operatorGraph hV hp ρ hρ hHess 0 le_rfl v h hvh
      have hl := hu.inner ℝ ((hasDerivAt_const (0 : ℝ) v).hasDerivWithinAt)
      have hr := ((hasDerivAt_const (0 : ℝ) u).hasDerivWithinAt).inner ℝ hv
      have heq : (fun s : ℝ => inner ℝ (gibbsHeatSemigroup hV hp ρ hρ hHess s.toNNReal u) v) =
          (fun s : ℝ => inner ℝ u (gibbsHeatSemigroup hV hp ρ hρ hHess s.toNNReal v)) :=
        funext (fun s => gibbsHeatSemigroup_symmetric hV hp ρ hρ hHess s.toNNReal u v)
      rw [heq] at hl
      have he := UniqueDiffWithinAt.eq_deriv (Ici (0 : ℝ)) (uniqueDiffWithinAt_Ici 0) hl hr
      simp only [inner_zero_right, inner_zero_left, add_zero, zero_add, inner_neg_left,
        inner_neg_right, Real.toNNReal_zero, gibbsHeatSemigroup_zero, ContinuousLinearMap.id_apply] at he
      linarith
    have hself := gibbsPositiveGenerator_selfAdjoint hV hp
    change A.adjoint = A at hself
    have hgraph : A.graph = A.graph.adjoint := by
      calc
        A.graph = A.adjoint.graph := congrArg LinearPMap.graph hself.symm
        _ = _ := LinearPMap.adjoint_graph_eq_graph_adjoint (gibbsPositiveGenerator_dense_domain hV hp)
    change (u,g) ∈ A.graph
    rw [hgraph, Submodule.mem_adjoint_iff]
    intro v h hvh
    have hh := hpair v h hvh
    change inner ℝ h u - inner ℝ v g = 0
    have he1 := real_inner_comm h u
    have he2 := real_inner_comm v g
    linarith
  · intro hug
    simpa only [Real.toNNReal_zero, gibbsHeatSemigroup_zero, ContinuousLinearMap.id_apply] using
      gibbsHeatSemigroup_hasDerivWithinAt_operatorGraph hV hp ρ hρ hHess 0 le_rfl u g hug

/-- Exact full-domain generator characterization for the actual Brownian
Langevin L² semigroup, through the proved full semigroup identification. -/
theorem langevinL2Operator_hasDerivWithinAt_zero_iff_graph
    {Ω : Type*} [MeasurableSpace Ω] {B : NNReal → Ω → E} {P : Measure Ω}
    (hB : IsEuclideanBrownian B P)
    {V : E → ℝ} (hV : ContDiff ℝ 2 V) (hp : IsProbabilityMeasure (gibbsMeasure volume V))
    (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (u g : E →₂[gibbsMeasure volume V] ℝ) :
    HasDerivWithinAt (fun s : ℝ => langevinL2Operator hB hV hp ρ hρ hHess s.toNNReal u)
      (-g) (Ici 0) 0 ↔ (u,g) ∈ (gibbsPositiveGenerator hV hp).graph := by
  simp_rw [langevinL2Operator_eq_gibbsHeatSemigroup]
  exact gibbsHeatSemigroup_hasDerivWithinAt_zero_iff_graph hV hp ρ hρ hHess u g

end CutoffRigidity
