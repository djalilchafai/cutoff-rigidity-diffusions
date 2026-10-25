module
public import CutoffRigidity.LangevinInformationEvolution
public import CutoffRigidity.LangevinEntropyFinite

/-! # The written exponential entropy and Fisher transport upper bounds

Regularization at time one, genuine entropy/Fisher decay, and the actual
Fisher entropy-endpoint bound give the source estimates for arbitrary
initial probability laws. No information estimate is an input hypothesis.
-/
public section
namespace CutoffRigidity
open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal NNReal
variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

theorem klDiv_langevinKernel_le_exp_transport
    {B : NNReal → Ω → E} {P : Measure Ω} (hB : IsEuclideanBrownian B P)
    {V : E → ℝ} (hV : ContDiff ℝ 2 V) (hp : IsProbabilityMeasure (gibbsMeasure volume V))
    (hdim : 0 < d) (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (ν : Measure E) [IsProbabilityMeasure ν] (t : NNReal) (ht : 1 ≤ t) :
    klDiv (langevinKernel V B P t ∘ₘ ν) (gibbsMeasure volume V) ≤
      ENNReal.ofReal (Real.exp (-2 * ρ * ((t : ℝ) - 1)) / 2) *
        squaredWasserstein ν (gibbsMeasure volume V) := by
  have hh := langevinKernel_entropy_contraction_add hB hV hp hdim ρ hρ hHess ν 1 (t-1)
  have he : (1 : NNReal) + (t - 1) = t := add_tsub_cancel_of_le ht
  rw [he, NNReal.coe_sub ht] at hh
  have hr := klDiv_langevinKernel_le_squaredWasserstein_div_time hB hV hp ρ hρ hHess ν 1 (by norm_num)
  norm_num only [Real.toNNReal_one, mul_one] at hr
  calc
    _ ≤ ENNReal.ofReal (Real.exp (-2 * ρ * ((t : ℝ) - 1))) *
        klDiv (langevinKernel V B P 1 ∘ₘ ν) (gibbsMeasure volume V) := hh
    _ ≤ ENNReal.ofReal (Real.exp (-2 * ρ * ((t : ℝ) - 1))) *
        (ENNReal.ofReal (1 / 2) * squaredWasserstein ν (gibbsMeasure volume V)) :=
      mul_le_mul' le_rfl hr
    _ = _ := by
      rw [← mul_assoc, ← ENNReal.ofReal_mul (Real.exp_nonneg _)]
      congr 1
      apply congrArg ENNReal.ofReal
      ring

theorem relativeFisherInformation_langevinKernel_le_exp_transport
    {B : NNReal → Ω → E} {P : Measure Ω} (hB : IsEuclideanBrownian B P)
    {V : E → ℝ} (hV : ContDiff ℝ 2 V) (hp : IsProbabilityMeasure (gibbsMeasure volume V))
    (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (ν : Measure E) [IsProbabilityMeasure ν] (t : NNReal) (ht : 2 ≤ t) :
    letI := langevinKernel_isMarkovKernel hB hV ρ hρ.le hHess t
    relativeFisherInformation hV hp (langevinKernel V B P t ∘ₘ ν) ≤
      ENNReal.ofReal (Real.exp (-2 * ρ * ((t : ℝ) - 2)) / 2) *
        squaredWasserstein ν (gibbsMeasure volume V) := by
  let := langevinKernel_isMarkovKernel hB hV ρ hρ.le hHess t
  let := langevinKernel_isMarkovKernel hB hV ρ hρ.le hHess 1
  let := langevinKernel_isMarkovKernel hB hV ρ hρ.le hHess 2
  have hstep := langevinKernel_fisher_entropy_endpoint_add hB hV hp ρ hρ hHess ν 1 1 (by norm_num)
  norm_num only [one_add_one_eq_two, NNReal.coe_one, ENNReal.ofReal_one, div_one] at hstep
  have hr := klDiv_langevinKernel_le_squaredWasserstein_div_time hB hV hp ρ hρ hHess ν 1 (by norm_num)
  norm_num only [Real.toNNReal_one, mul_one] at hr
  have hd := relativeFisherInformation_langevinKernel_le hB hV hp ρ hρ hHess
    (langevinKernel V B P 2 ∘ₘ ν) (t-2)
  have he : (2 : NNReal) + (t - 2) = t := add_tsub_cancel_of_le ht
  have hc : relativeFisherInformation hV hp (langevinKernel V B P t ∘ₘ ν) ≤
      ENNReal.ofReal (Real.exp (-2 * ρ * ((t : ℝ) - 2))) *
        relativeFisherInformation hV hp (langevinKernel V B P 2 ∘ₘ ν) := by
    simpa only [Measure.comp_assoc, langevinKernel_comp hB hV ρ hρ.le hHess, he,
      NNReal.coe_sub ht, NNReal.coe_ofNat] using hd
  calc
    _ ≤ ENNReal.ofReal (Real.exp (-2 * ρ * ((t : ℝ) - 2))) *
        relativeFisherInformation hV hp (langevinKernel V B P 2 ∘ₘ ν) := hc
    _ ≤ ENNReal.ofReal (Real.exp (-2 * ρ * ((t : ℝ) - 2))) *
        (ENNReal.ofReal (1 / 2) * squaredWasserstein ν (gibbsMeasure volume V)) :=
      mul_le_mul' le_rfl (hstep.trans hr)
    _ = _ := by
      rw [← mul_assoc, ← ENNReal.ofReal_mul (Real.exp_nonneg _)]
      congr 1
      apply congrArg ENNReal.ofReal
      ring

end CutoffRigidity
