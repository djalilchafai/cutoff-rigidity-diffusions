module
public import CutoffRigidity.C1WeakLangevinDomain
public import CutoffRigidity.LangevinWeakBackwardEquation
public import CutoffRigidity.LangevinStrongL2Evolution

/-! # Actual stochastic compact-test evolution lies in the true A domain

The actual C¹ transition expectation has a derived bounded gradient and
satisfies the proved ordinary weak backward equation. The genuine weighted
C¹ domain bridge then identifies its true self-adjoint operator value.
No stochastic invariance or operator-domain hypothesis is assumed.
-/
public section
namespace CutoffRigidity
open MeasureTheory ProbabilityTheory Filter Topology
variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

/-- Every time, including zero, of the actual Brownian compact-test L²
curve belongs to the genuine self-adjoint operator graph. -/
theorem langevinCompactTestLp_mem_operatorGraph
    {B : NNReal → Ω → E} {P : Measure Ω} (hB : IsEuclideanBrownian B P)
    {V g : E → ℝ} (hV : ContDiff ℝ 2 V)
    (hprob : IsProbabilityMeasure (gibbsMeasure volume V))
    (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g) (t : NNReal) :
    (langevinCompactTestLp hB hV ρ hρ.le hHess hg.continuous hgc (gibbsMeasure volume V) t,
      -langevinCompactTestLp hB hV ρ hρ.le hHess
        (continuous_langevinDifferentialOperator hV hg) (hasCompactSupport_langevinDifferentialOperator V hgc)
          (gibbsMeasure volume V) t) ∈ (gibbsPositiveGenerator hV hprob).graph := by
  let := hprob
  let q : E → ℝ := fun x => ∫ y, g y ∂langevinKernel V B P t x
  have hq : ContDiff ℝ 1 q := contDiff_one_langevinKernel_integral hB hV ρ hρ.le hHess
    (hg.of_le (by norm_num)) hgc t
  obtain ⟨L, hLip⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hgc hg (by norm_num)
  have hqLip := lipschitzWith_langevinKernel_integral hB hV ρ hρ.le hHess
    (hg.of_le (by norm_num)) hgc hLip t
  have hgradBound (x : E) : ‖gradient q x‖ ≤ Real.exp (-ρ * (t : ℝ)) * L := by
    have hNorm : ‖gradient q x‖ = ‖fderiv ℝ q x‖ :=
      (InnerProductSpace.toDual ℝ E).symm.norm_map _
    rw [hNorm]
    exact norm_fderiv_le_of_lipschitz ℝ hqLip
  have hgrad : MemLp (gradient q) 2 (gibbsMeasure volume V) :=
    MemLp.of_bound (continuous_gradient_of_c1 hq).aestronglyMeasurable _
      (Eventually.of_forall hgradBound)
  apply c1_weak_langevin_mem_operatorGraph_of_ae hV hprob ρ hρ hHess hq hgrad
  · exact langevinCompactTestLp_coeFn hB hV ρ hρ.le hHess hg.continuous hgc (gibbsMeasure volume V) t
  · exact langevinCompactTestLp_coeFn hB hV ρ hρ.le hHess
      (continuous_langevinDifferentialOperator hV hg) (hasCompactSupport_langevinDifferentialOperator V hgc)
        (gibbsMeasure volume V) t
  · intro ψ hψ hψc
    exact langevinKernel_weak_backward_equation hB hV hg hgc ρ hρ.le hHess hψ hψc t

end CutoffRigidity
