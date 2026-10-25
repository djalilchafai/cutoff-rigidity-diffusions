module
public import CutoffRigidity.LangevinInformationEvolution
public import CutoffRigidity.LangevinEntropyFinite

/-! # Actual positive-time Fisher finiteness from deterministic initial data

Entropy regularization at half the time and the genuine full-domain
Fisher entropy endpoint give finiteness with no smooth density assumption.
-/
public section
namespace CutoffRigidity
open MeasureTheory ProbabilityTheory InformationTheory
open scoped NNReal ENNReal
variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

theorem relativeFisherInformation_langevinKernel_ne_top
    {B : NNReal → Ω → E} {P : Measure Ω} (hB : IsEuclideanBrownian B P)
    {V : E → ℝ} (hV : ContDiff ℝ 2 V) (hp : IsProbabilityMeasure (gibbsMeasure volume V))
    (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (T : NNReal) (hT : 0 < T) (x : E) :
    letI := langevinKernel_isMarkovKernel hB hV ρ hρ.le hHess T
    relativeFisherInformation hV hp (langevinKernel V B P T x) ≠ ⊤ := by
  let t : NNReal := T / 2
  have ht : 0 < t := by dsimp [t]; positivity
  have htR : (0 : ℝ) < (t : ℝ) := by exact_mod_cast ht
  have he : t+t=T := by dsimp [t]; ring
  let := langevinKernel_isMarkovKernel hB hV ρ hρ.le hHess T
  let := langevinKernel_isMarkovKernel hB hV ρ hρ.le hHess t
  have hKL : klDiv (langevinKernel V B P t x) (gibbsMeasure volume V) ≠ ⊤ := by
    have hh := klDiv_langevinKernel_ne_top hB hV hp ρ hρ hHess x t htR
    simpa only [@Real.toNNReal_coe t] using hh
  have hh := langevinKernel_fisher_entropy_endpoint_add hB hV hp ρ hρ hHess (Measure.dirac x) t t ht
  have hBound : relativeFisherInformation hV hp (langevinKernel V B P T x) ≤
      klDiv (langevinKernel V B P t x) (gibbsMeasure volume V) / ENNReal.ofReal t := by
    simpa only [he,langevinKernel_comp_dirac] using hh
  exact ne_top_of_le_ne_top (ENNReal.div_ne_top hKL (ENNReal.ofReal_ne_zero_iff.mpr htR)) hBound

end CutoffRigidity
