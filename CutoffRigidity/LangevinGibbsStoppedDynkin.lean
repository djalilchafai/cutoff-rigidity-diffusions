module
public import CutoffRigidity.LangevinJointDynkinMeasurability

/-! # Actual Gibbs-initial stopped Dynkin expectation

Fixed-initial optional expectation is integrated by genuine product Fubini,
using joint exit/function measurability and a bound uniform in the initial
state. No invariant-law premise occurs.
-/
public section
namespace CutoffRigidity
open MeasureTheory ProbabilityTheory Set Filter Topology
variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

theorem langevinDynkinProcess_integrable_joint_exit
    {P : Measure Ω} [IsFiniteMeasure P] (ν : Measure E) [IsFiniteMeasure ν]
    {V f : E → ℝ} (hV : ContDiff ℝ 2 V) (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (κ : ℝ) (hκ : 0 ≤ κ)
    (hHess : ∀ x z : E, κ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    {C : Ω → C(ℝ, E)} (hC : Measurable C) (R : ℝ) (T : NNReal) :
    Integrable (fun p : E × Ω => langevinDynkinProcess V f C p.1
      (langevinExitTime V C p.1 R T p.2) p.2) (ν.prod P) := by
  have hm := (langevinDynkinProcess_jointly_stronglyMeasurable_initial_time hV hf κ hκ hHess hC).comp_measurable
    ((langevinExitTime_jointly_measurable_initial hV κ hκ hHess hC R T).prodMk measurable_id)
  obtain ⟨K, hK⟩ := langevinDynkinProcess_uniform_initial_bound hV hf hfc C T
  apply Integrable.mono' (integrable_const K) hm.aestronglyMeasurable
  exact Eventually.of_forall (fun p => hK p.1 _ (langevinExitTime_le_horizon V C p.1 R T p.2) p.2)

/-- Genuine compact-test stopped Dynkin expectation for an arbitrary finite
initial law independent of the actual Brownian driving noise. -/
theorem langevinDynkinProcess_integral_joint_exit
    {B : NNReal → Ω → E} {P : Measure Ω} (hB : IsEuclideanBrownian B P)
    (ν : Measure E) [IsFiniteMeasure ν]
    {V f : E → ℝ} (hV : ContDiff ℝ 2 V) (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (κ : ℝ) (hκ : 0 ≤ κ)
    (hHess : ∀ x z : E, κ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    {C : Ω → C(ℝ, E)} (hC : Measurable C)
    (hCeq : ∀ᵐ ω ∂P, ∀ r : ℝ, C ω r = brownianDrivingPath B ω r)
    (R : ℝ) (T : NNReal) :
    (∫ p : E × Ω, langevinDynkinProcess V f C p.1
      (langevinExitTime V C p.1 R T p.2) p.2 ∂ν.prod P) = 0 := by
  let := hB.isProbabilityMeasure
  rw [integral_prod _ (langevinDynkinProcess_integrable_joint_exit ν hV hf hfc κ hκ hHess hC R T)]
  apply integral_eq_zero_of_ae
  exact Eventually.of_forall (fun x => langevinDynkinProcess_integral_stopping_time hB hV hf hfc κ hκ hHess
    x hC hCeq T (langevinExitTime_isStoppingTime hV κ hκ hHess hC x R T)
      (langevinExitTime_le_horizon V C x R T))

/-- The initial measure is the actual Gibbs probability, and the driving
noise is the actual Brownian continuous version. -/
theorem gibbs_langevinDynkinProcess_integral_joint_exit
    {B : NNReal → Ω → E} {P : Measure Ω} (hB : IsEuclideanBrownian B P)
    {V f : E → ℝ} (hV : ContDiff ℝ 2 V) (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (hprob : IsProbabilityMeasure (gibbsMeasure volume V))
    (κ : ℝ) (hκ : 0 ≤ κ)
    (hHess : ∀ x z : E, κ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    {C : Ω → C(ℝ, E)} (hC : Measurable C)
    (hCeq : ∀ᵐ ω ∂P, ∀ r : ℝ, C ω r = brownianDrivingPath B ω r)
    (R : ℝ) (T : NNReal) :
    (∫ p : E × Ω, langevinDynkinProcess V f C p.1
      (langevinExitTime V C p.1 R T p.2) p.2 ∂(gibbsMeasure volume V).prod P) = 0 := by
  let := hprob
  exact langevinDynkinProcess_integral_joint_exit hB (gibbsMeasure volume V) hV hf hfc κ hκ hHess hC hCeq R T

theorem gibbs_langevinJointHitBy_measure_tendsto_zero
    {B : NNReal → Ω → E} {P : Measure Ω} (hB : IsEuclideanBrownian B P)
    {V : E → ℝ} (hV : ContDiff ℝ 2 V)
    (hprob : IsProbabilityMeasure (gibbsMeasure volume V))
    (κ : ℝ) (hκ : 0 ≤ κ)
    (hHess : ∀ x z : E, κ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    {C : Ω → C(ℝ, E)} (hC : Measurable C) (T : NNReal) :
    Tendsto (fun R : ℝ => ((gibbsMeasure volume V).prod P) (langevinJointHitBy V C R T)) atTop (𝓝 0) := by
  let := hprob
  let := hB.isProbabilityMeasure
  exact langevinJointHitBy_measure_tendsto_zero hV κ hκ hHess hC T (gibbsMeasure volume V) P

end CutoffRigidity
