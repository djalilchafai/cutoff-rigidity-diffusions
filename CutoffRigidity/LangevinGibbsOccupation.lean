module
public import CutoffRigidity.LangevinKilledOccupation
public import CutoffRigidity.LangevinKernel

/-! # Genuine Gibbs-initial Brownian killed occupation bounds

The driving law is the actual continuous sqrt-two Brownian path law, and
the initial law is the actual Gibbs measure with its proved density bound.
No stationary law or invariance premise is introduced.
-/
public section
namespace CutoffRigidity
open MeasureTheory ProbabilityTheory
open scoped ENNReal
variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

theorem gibbs_brownian_killedOccupation_le_volume
    {Ω : Type*} [MeasurableSpace Ω] {B : NNReal → Ω → E} {P : Measure Ω}
    (hB : IsEuclideanBrownian B P)
    {V : E → ℝ} (hV : ContDiff ℝ 2 V)
    (hprob : IsProbabilityMeasure (gibbsMeasure volume V))
    (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z) (R : ℝ) :
    ∃ K : NNReal, ∀ T : ℝ, 0 ≤ T →
      langevinKilledOccupation V (gibbsMeasure volume V) (brownianNoiseLaw B P) T R ≤
        (ENNReal.ofReal (Real.exp (‖gradient V 0‖ ^ 2 / ρ - V 0)) *
          ENNReal.ofReal (Real.exp ((K : ℝ) * T)) ^ d * ENNReal.ofReal T) • volume := by
  let := hprob
  let := brownianNoiseLaw_isProbabilityMeasure hB
  obtain ⟨K, hK⟩ := langevinKilledOccupation_le_volume hV ρ hρ.le hHess R
  exact ⟨K, fun T hT => hK (gibbsMeasure volume V) (brownianNoiseLaw B P) _
    (gibbsMeasure_le_smul_volume hV ρ hρ hHess) T hT⟩

end CutoffRigidity
