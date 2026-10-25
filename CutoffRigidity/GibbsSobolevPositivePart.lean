module
public import CutoffRigidity.GibbsSobolevContractionLimit
public import CutoffRigidity.SmoothPositivePart
public import Mathlib.Analysis.SpecificLimits.Basic

/-! # Positive-part closure of the genuine weighted H¹ graph

The positive-part map is obtained by explicit square-root regularization.
No nonsmooth Sobolev chain rule is assumed.
-/
public section
namespace CutoffRigidity
open MeasureTheory Filter Topology
variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

theorem gibbsSobolev_positive_part
    {V : E → ℝ} (hV : ContDiff ℝ 2 V)
    (hprob : IsProbabilityMeasure (gibbsMeasure volume V))
    (u : gibbsSobolevGraph hV hprob) :
    ∃ (v : gibbsSobolevGraph hV hprob),
      (gibbsSobolevInclusion hV hprob v =ᵐ[gibbsMeasure volume V]
        fun x => max (gibbsSobolevInclusion hV hprob u x) 0) ∧
      (gibbsSobolevDerivative hV hprob v =ᵐ[gibbsMeasure volume V]
        fun x => positivePartSlope (gibbsSobolevInclusion hV hprob u x) • gibbsSobolevDerivative hV hprob u x) ∧
      ‖gibbsSobolevDerivative hV hprob v‖ ≤ ‖gibbsSobolevDerivative hV hprob u‖ := by
  let ε : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hε (n : ℕ) : 0 < ε n := by dsimp [ε]; positivity
  have hlim : Tendsto ε atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  exact gibbsSobolev_normal_contraction_limit hV hprob
    (fun n => smoothPositivePart (ε n))
    (fun n => contDiff_smoothPositivePart (hε n))
    (fun n => smoothPositivePart_zero (hε n))
    (fun n => abs_deriv_smoothPositivePart_le (hε n))
    (LipschitzWith.id.max_const 0) (by simp)
    (smoothPositivePart_tendsto hlim)
    (deriv_smoothPositivePart_tendsto hε hlim)
    abs_positivePartSlope_le u

/-- The actual Dirichlet energy decreases under positive-part truncation. -/
theorem gibbsSobolev_positive_part_energy
    {V : E → ℝ} (hV : ContDiff ℝ 2 V)
    (hprob : IsProbabilityMeasure (gibbsMeasure volume V))
    (u : gibbsSobolevGraph hV hprob) :
    ∃ (v : gibbsSobolevGraph hV hprob),
      (gibbsSobolevInclusion hV hprob v =ᵐ[gibbsMeasure volume V]
        fun x => max (gibbsSobolevInclusion hV hprob u x) 0) ∧
      gibbsDirichletEnergy hV hprob v v ≤ gibbsDirichletEnergy hV hprob u u := by
  obtain ⟨v, hv, _, hnorm⟩ := gibbsSobolev_positive_part hV hprob u
  refine ⟨v, hv, ?_⟩
  change inner ℝ (gibbsSobolevDerivative hV hprob v) (gibbsSobolevDerivative hV hprob v) ≤ _
  simp only [gibbsDirichletEnergy, real_inner_self_eq_norm_sq]
  exact pow_le_pow_left₀ (norm_nonneg _) hnorm 2

end CutoffRigidity
