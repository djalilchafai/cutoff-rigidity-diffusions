module
public import CutoffRigidity.LangevinEntropyVariationalCost
public import CutoffRigidity.KLCompactVariational

/-! # Full entropy-cost regularization of the actual Langevin kernel

The proved compact-test budgets and the genuine variational characterization
of relative entropy apply to every initial probability law, including singular
laws. All transition/domain/functional inequalities are derived internally.
-/
public section
namespace CutoffRigidity
open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal NNReal
variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

theorem klDiv_langevinKernel_le_squaredWasserstein
    {B : NNReal → Ω → E} {P : Measure Ω} (hB : IsEuclideanBrownian B P)
    {V : E → ℝ} (hV : ContDiff ℝ 2 V) (hp : IsProbabilityMeasure (gibbsMeasure volume V))
    (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (ν : Measure E) [IsProbabilityMeasure ν] (T : ℝ) (hT : 0 < T) :
    klDiv (langevinKernel V B P T.toNNReal ∘ₘ ν) (gibbsMeasure volume V) ≤
      ENNReal.ofReal (ρ / (2 * (Real.exp (2 * ρ * T) - 1))) *
        squaredWasserstein ν (gibbsMeasure volume V) := by
  let := hp
  let := langevinKernel_isMarkovKernel hB hV ρ hρ.le hHess T.toNNReal
  apply klDiv_le_of_compact_c2_tests
  intro φ hφ hφc
  exact langevinKernel_compact_entropy_test_le_cost hB hV hp ρ hρ hHess ν φ hφ hφc T hT

/-- The coarser time bound used explicitly in the written entropy proof. -/
theorem klDiv_langevinKernel_le_squaredWasserstein_div_time
    {B : NNReal → Ω → E} {P : Measure Ω} (hB : IsEuclideanBrownian B P)
    {V : E → ℝ} (hV : ContDiff ℝ 2 V) (hp : IsProbabilityMeasure (gibbsMeasure volume V))
    (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (ν : Measure E) [IsProbabilityMeasure ν] (T : ℝ) (hT : 0 < T) :
    klDiv (langevinKernel V B P T.toNNReal ∘ₘ ν) (gibbsMeasure volume V) ≤
      ENNReal.ofReal (1 / (2 * T)) * squaredWasserstein ν (gibbsMeasure volume V) := by
  apply (klDiv_langevinKernel_le_squaredWasserstein hB hV hp ρ hρ hHess ν T hT).trans
  apply mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl
  have hden : 0 < Real.exp (2 * ρ * T) - 1 :=
    sub_pos.mpr (Real.one_lt_exp_iff.mpr (by positivity))
  apply (div_le_div_iff₀ (mul_pos (by norm_num) hden) (mul_pos (by norm_num) hT)).mpr
  have hh := Real.add_one_le_exp (2 * ρ * T)
  nlinarith

end CutoffRigidity
