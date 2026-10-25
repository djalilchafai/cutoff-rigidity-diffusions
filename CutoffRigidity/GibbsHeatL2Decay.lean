module

public import CutoffRigidity.GibbsHeatMarkov
public import CutoffRigidity.GibbsHeatGenerator
public import CutoffRigidity.GibbsOperatorDomainPDE
public import CutoffRigidity.GibbsOperatorCurvatureGap

/-! # Actual L² ergodic decay of form heat

Curvature Poincare supplies genuine graph coercivity on the mean-zero
space. The actual strong heat equation then yields exponential norm decay,
with no spectral-decay premise.
-/

public section

namespace CutoffRigidity

open MeasureTheory Set Filter Topology

variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

/-- Symmetry and preservation of actual constants preserve actual mean zero. -/
theorem gibbsHeatSemigroup_mem_meanZero {V : E → ℝ}
    (hV : ContDiff ℝ 2 V) (hp : IsProbabilityMeasure (gibbsMeasure volume V))
    (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (t : NNReal) (u : E →₂[gibbsMeasure volume V] ℝ) (hu : u ∈ gibbsMeanZeroSpace hp) :
    gibbsHeatSemigroup hV hp ρ hρ hHess t u ∈ gibbsMeanZeroSpace hp := by
  rw [gibbsMeanZeroSpace, Submodule.mem_orthogonal_singleton_iff_inner_left] at hu ⊢
  rw [gibbsHeatSemigroup_symmetric, gibbsHeatSemigroup_constant]
  exact hu

/-- The actual generator graph has curvature coercivity on actual mean zero. -/
theorem gibbsPositiveGenerator_graph_coercive_meanZero {V : E → ℝ}
    (hV : ContDiff ℝ 2 V) (hp : IsProbabilityMeasure (gibbsMeasure volume V))
    (hd : 0 < d) (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (u g : E →₂[gibbsMeasure volume V] ℝ)
    (hug : (u,g) ∈ (gibbsPositiveGenerator hV hp).graph)
    (hu : u ∈ gibbsMeanZeroSpace hp) : ρ * ‖u‖ ^ 2 ≤ inner ℝ g u := by
  let v := gibbsOperatorGraphSobolevLift hV hp u g
  have hv := gibbsOperatorGraphSobolevLift_inclusion hV hp u g hug
  have hc := gibbsCurvaturePoincare hV hp hd ρ hρ hHess v (hv.symm ▸ hu)
  have he := gibbsOperatorGraph_weak_equation hV hp u g hug v
  rw [hv] at hc he
  rwa [he] at hc

/-- Exponential L² decay for every genuine mean-zero operator-domain test. -/
theorem gibbsHeatSemigroup_norm_le_exp_meanZero {V : E → ℝ}
    (hV : ContDiff ℝ 2 V) (hp : IsProbabilityMeasure (gibbsMeasure volume V))
    (hd : 0 < d) (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (u g : E →₂[gibbsMeasure volume V] ℝ)
    (hug : (u,g) ∈ (gibbsPositiveGenerator hV hp).graph)
    (hu : u ∈ gibbsMeanZeroSpace hp) {T : ℝ} (hT : 0 ≤ T) :
    ‖gibbsHeatSemigroup hV hp ρ hρ hHess T.toNNReal u‖ ≤ Real.exp (-ρ * T) * ‖u‖ := by
  let P := gibbsHeatSemigroup hV hp ρ hρ hHess
  have hc : ContinuousOn (fun s : ℝ => P s.toNNReal u) (Icc 0 T) :=
    ((continuous_gibbsHeatSemigroup_apply hV hp ρ hρ hHess u).comp continuous_real_toNNReal).continuousOn
  have hdiss (s : ℝ) (hs : s ∈ Ioo 0 T) :
      inner ℝ (P s.toNNReal u) (-P s.toNNReal g) ≤ -ρ * ‖P s.toNNReal u‖ ^ 2 := by
    have hb := gibbsPositiveGenerator_graph_coercive_meanZero hV hp hd ρ hρ hHess
      (P s.toNNReal u) (P s.toNNReal g)
      (gibbsHeatSemigroup_preserves_operatorGraph hV hp ρ hρ hHess s.toNNReal u g hug)
      (gibbsHeatSemigroup_mem_meanZero hV hp ρ hρ hHess s.toNNReal u hu)
    rw [inner_neg_right]
    have he := real_inner_comm (P s.toNNReal u) (P s.toNNReal g)
    nlinarith
  have hh := norm_contraction_of_dissipative_derivative hT hc
    (fun s hs => gibbsHeatSemigroup_hasDerivAt_operatorGraph hV hp ρ hρ hHess s hs.1 u g hug) hdiss
  simpa only [P, Real.toNNReal_zero, gibbsHeatSemigroup_zero, ContinuousLinearMap.id_apply] using hh

end CutoffRigidity
