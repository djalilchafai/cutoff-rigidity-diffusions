module
public import CutoffRigidity.LangevinStrongL1Continuity
public import CutoffRigidity.RNDensityTotalVariation

/-! # Genuine short-time total-variation continuity on the full AC domain

Actual RN evolution, full strong L¹ continuity and the genuine event
supremum definition of total variation discharge the continuity claim.
-/
public section
namespace CutoffRigidity
open MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal
variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

theorem tendsto_L1_rnDeriv_langevinKernel_zero
    {B : NNReal → Ω → E} {P : Measure Ω} (hB : IsEuclideanBrownian B P)
    {V : E → ℝ} (hV : ContDiff ℝ 2 V) (hp : IsProbabilityMeasure (gibbsMeasure volume V))
    (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (ν : Measure E) [IsProbabilityMeasure ν] (hAC : ν ≪ gibbsMeasure volume V) :
    Tendsto (fun t : NNReal => ∫ x,
      |((langevinKernel V B P t ∘ₘ ν).rnDeriv (gibbsMeasure volume V) x).toReal -
        (ν.rnDeriv (gibbsMeasure volume V) x).toReal| ∂gibbsMeasure volume V) (𝓝 0) (𝓝 0) := by
  have hh := tendsto_langevinKernel_L1_zero hB hV hp ρ hρ hHess
    (Measure.measurable_rnDeriv ν (gibbsMeasure volume V)).ennreal_toReal
    (integrable_toReal_rnDeriv_finite ν (gibbsMeasure volume V))
  apply hh.congr'
  apply Eventually.of_forall
  intro t
  apply integral_congr_ae
  filter_upwards [langevinKernel_rnDeriv_toReal hB hV hp ρ hρ hHess ν hAC t] with x hx
  rw [hx, Real.norm_eq_abs]

theorem tendsto_totalVariationDistance_langevinKernel_zero
    {B : NNReal → Ω → E} {P : Measure Ω} (hB : IsEuclideanBrownian B P)
    {V : E → ℝ} (hV : ContDiff ℝ 2 V) (hp : IsProbabilityMeasure (gibbsMeasure volume V))
    (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (ν : Measure E) [IsProbabilityMeasure ν] (hAC : ν ≪ gibbsMeasure volume V) :
    Tendsto (fun t : NNReal => totalVariationDistance (langevinKernel V B P t ∘ₘ ν) ν)
      (𝓝 0) (𝓝 0) := by
  let := hp
  have hMarkov (t : NNReal) : IsMarkovKernel (langevinKernel V B P t) :=
    langevinKernel_isMarkovKernel hB hV ρ hρ.le hHess t
  apply squeeze_zero (fun t => by let := hMarkov t; exact totalVariationDistance_nonneg _ _) _
    (tendsto_L1_rnDeriv_langevinKernel_zero hB hV hp ρ hρ hHess ν hAC)
  intro t
  let := hMarkov t
  exact totalVariationDistance_le_L1_rnDeriv _ _ (gibbsMeasure volume V)
    (langevinKernel_comp_absolutelyContinuous hB hV hp ρ hρ hHess ν hAC t) hAC

end CutoffRigidity
