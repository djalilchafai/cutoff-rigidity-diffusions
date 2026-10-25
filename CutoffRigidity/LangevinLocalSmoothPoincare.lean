module
public import CutoffRigidity.LangevinLocalPoincare
public import CutoffRigidity.FiniteMeasureC1Poincare

/-! # Genuine local Poincare on the complete smooth energy domain

The source variance interpolation, followed by proved cutoff and
mollification limits, supplies the actual local Poincare hypothesis used
in Salez's varentropy argument. No local inequality is assumed.
-/
public section
namespace CutoffRigidity
open MeasureTheory ProbabilityTheory
variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

/-- Exact curvature local Poincare for every actual C¹ L² energy test of a
genuine Langevin transition law. -/
theorem langevinKernel_hasLocalSmoothPoincare
    {B : NNReal → Ω → E} {P : Measure Ω} (hB : IsEuclideanBrownian B P)
    {V : E → ℝ} (hV : ContDiff ℝ 2 V)
    (hp : IsProbabilityMeasure (gibbsMeasure volume V))
    (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (T : ℝ) (hT : 0 ≤ T) (x : E) :
    HasLocalSmoothPoincare (langevinKernel V B P T.toNNReal x)
      ((1-Real.exp (-2*ρ*T))/ρ) := by
  let := langevinKernel_isMarkovKernel hB hV ρ hρ.le hHess T.toNNReal
  apply c1_poincare_of_compact_c2
  intro g hg hgc
  exact langevinKernel_local_poincare_compact_c2 hB hV hp hg hgc ρ hρ hHess T hT x

/-- The precise full-domain local bound with coefficient 2T appearing in
Salez's proof, derived from the actual diffusion. -/
theorem langevinKernel_hasLocalSmoothPoincare_time
    {B : NNReal → Ω → E} {P : Measure Ω} (hB : IsEuclideanBrownian B P)
    {V : E → ℝ} (hV : ContDiff ℝ 2 V)
    (hp : IsProbabilityMeasure (gibbsMeasure volume V))
    (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (T : ℝ) (hT : 0 ≤ T) (x : E) :
    HasLocalSmoothPoincare (langevinKernel V B P T.toNNReal x) (2*T) := by
  let := langevinKernel_isMarkovKernel hB hV ρ hρ.le hHess T.toNNReal
  apply c1_poincare_of_compact_c2
  intro g hg hgc
  exact langevinKernel_local_poincare_compact_c2_time hB hV hp hg hgc ρ hρ hHess T hT x

end CutoffRigidity
