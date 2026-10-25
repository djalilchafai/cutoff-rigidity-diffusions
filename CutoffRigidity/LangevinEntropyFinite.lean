module
public import CutoffRigidity.LangevinEntropyRegularization
public import CutoffRigidity.BarycenterWasserstein

/-! # Actual positive-time entropy finiteness and absolute continuity

Quadratic Gibbs moments and the proved entropy-cost regularization apply
to a genuine deterministic initial law. No density existence is assumed.
-/
public section
namespace CutoffRigidity
open MeasureTheory ProbabilityTheory InformationTheory Filter
open scoped ENNReal NNReal
variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

theorem langevinKernel_comp_dirac (V : E → ℝ) (B : NNReal → Ω → E) (P : Measure Ω)
    (t : NNReal) (x : E) : langevinKernel V B P t ∘ₘ Measure.dirac x = langevinKernel V B P t x := by
  exact Measure.dirac_bind (Kernel.measurable _) x

theorem squaredWasserstein_dirac_gibbs_ne_top
    {V : E → ℝ} (hV : ContDiff ℝ 2 V) (hp : IsProbabilityMeasure (gibbsMeasure volume V))
    (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z) (x : E) :
    squaredWasserstein (Measure.dirac x) (gibbsMeasure volume V) ≠ ⊤ := by
  let := hp
  have hlp : MemLp (fun y : E => x - y) 2 (gibbsMeasure volume V) :=
    (memLp_const x).sub (gibbs_memLp_two_id_of_hessian_bound hV ρ hρ hHess)
  have hi := hlp.norm.integrable_sq
  rw [squaredWasserstein_dirac]
  have he : (∫⁻ y : E, edist x y ^ 2 ∂gibbsMeasure volume V) =
      ENNReal.ofReal (∫ y : E, ‖x-y‖ ^ 2 ∂gibbsMeasure volume V) := by
    rw [ofReal_integral_eq_lintegral_ofReal hi (Eventually.of_forall fun y => sq_nonneg _)]
    apply lintegral_congr
    intro y
    rw [edist_dist, dist_eq_norm, ENNReal.ofReal_pow (norm_nonneg _) 2]
  rw [he]
  exact ENNReal.ofReal_ne_top

theorem klDiv_langevinKernel_ne_top
    {B : NNReal → Ω → E} {P : Measure Ω} (hB : IsEuclideanBrownian B P)
    {V : E → ℝ} (hV : ContDiff ℝ 2 V) (hp : IsProbabilityMeasure (gibbsMeasure volume V))
    (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (x : E) (T : ℝ) (hT : 0 < T) :
    klDiv (langevinKernel V B P T.toNNReal x) (gibbsMeasure volume V) ≠ ⊤ := by
  have hh := klDiv_langevinKernel_le_squaredWasserstein_div_time hB hV hp ρ hρ hHess
    (Measure.dirac x) T hT
  rw [langevinKernel_comp_dirac] at hh
  exact ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    (squaredWasserstein_dirac_gibbs_ne_top hV hp ρ hρ hHess x)) hh

/-- Existence of the true transition RN density is a consequence of the
proved finite entropy, including for a deterministic initial state. -/
theorem langevinKernel_absolutelyContinuous_gibbs
    {B : NNReal → Ω → E} {P : Measure Ω} (hB : IsEuclideanBrownian B P)
    {V : E → ℝ} (hV : ContDiff ℝ 2 V) (hp : IsProbabilityMeasure (gibbsMeasure volume V))
    (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (x : E) (T : ℝ) (hT : 0 < T) :
    langevinKernel V B P T.toNNReal x ≪ gibbsMeasure volume V := by
  exact (klDiv_ne_top_iff.mp (klDiv_langevinKernel_ne_top hB hV hp ρ hρ hHess x T hT)).1

end CutoffRigidity
