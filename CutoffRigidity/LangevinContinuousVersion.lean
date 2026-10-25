module

public import CutoffRigidity.LangevinMarkovProperty

/-! # A measurable continuous version of the actual Langevin process

A genuinely measurable continuous driving-path version gives a genuinely
measurable continuous Langevin realization. It agrees with the original
constructed Brownian Langevin process simultaneously at all times a.e.
The joint measurability below is derived from actual path continuity and
actual fixed-time solution-map measurability.
-/

public section

namespace CutoffRigidity

open Set MeasureTheory ProbabilityTheory
open scoped NNReal Topology

variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

/-- The canonical solution driven by a measurable continuous noise-path version. -/
@[expose] noncomputable def continuousLangevinVersion
    (V : E → ℝ) (C : Ω → C(ℝ, E)) (x₀ : E) (t : ℝ≥0) (ω : Ω) : E :=
  langevinEvaluation V t (x₀, C ω)

omit [MeasurableSpace Ω] in
/-- Every sample path of the version is genuinely continuous. -/
theorem continuousLangevinVersion_continuous
    {V : E → ℝ} (hV : ContDiff ℝ 2 V) (κ : ℝ) (hκ : 0 ≤ κ)
    (hHess : ∀ x z, κ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (C : Ω → C(ℝ, E)) (x₀ : E) (ω : Ω) :
    Continuous (fun t => continuousLangevinVersion V C x₀ t ω) := by
  have hp := langevinSolution_continuousOn hV κ hκ hHess (C ω).continuous x₀
  exact hp.comp_continuous continuous_subtype_val (fun t => t.property)

/-- Every fixed-time value is genuinely measurable, without completing the sample space. -/
theorem continuousLangevinVersion_measurable
    {V : E → ℝ} (hV : ContDiff ℝ 2 V) (κ : ℝ) (hκ : 0 ≤ κ)
    (hHess : ∀ x z, κ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    {C : Ω → C(ℝ, E)} (hC : Measurable C) (x₀ : E) (t : ℝ≥0) :
    Measurable (continuousLangevinVersion V C x₀ t) :=
  (langevinEvaluation_continuous hV κ hκ hHess t).measurable.comp (measurable_const.prodMk hC)

/-- Actual joint time/sample measurability follows from continuous paths and measurable evaluations. -/
theorem continuousLangevinVersion_jointly_stronglyMeasurable
    {V : E → ℝ} (hV : ContDiff ℝ 2 V) (κ : ℝ) (hκ : 0 ≤ κ)
    (hHess : ∀ x z, κ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    {C : Ω → C(ℝ, E)} (hC : Measurable C) (x₀ : E) :
    StronglyMeasurable (Function.uncurry (continuousLangevinVersion V C x₀)) :=
  stronglyMeasurable_uncurry_of_continuous_of_stronglyMeasurable
    (continuousLangevinVersion_continuous hV κ hκ hHess C x₀)
    (fun t => (continuousLangevinVersion_measurable hV κ hκ hHess hC x₀ t).stronglyMeasurable)

/-- The version is indistinguishable from the actual Brownian-driven process. -/
theorem continuousLangevinVersion_eq_process_ae
    {B : ℝ≥0 → Ω → E} {P : Measure Ω} {V : E → ℝ}
    {C : Ω → C(ℝ, E)} (hCeq : ∀ᵐ ω ∂P, ∀ r : ℝ, C ω r = brownianDrivingPath B ω r)
    (x₀ : E) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0, continuousLangevinVersion V C x₀ t ω = langevinProcess V B x₀ t ω := by
  filter_upwards [hCeq] with ω hω
  intro t
  have hw : (C ω : ℝ → E) = brownianDrivingPath B ω := funext hω
  exact congrArg (fun w => langevinSolution V w x₀ (t : ℝ)) hw

omit [MeasurableSpace Ω] in
/-- The actual state of the version is a function of its finite history, pointwise. -/
theorem continuousLangevinVersion_eq_history_evaluation
    {V : E → ℝ} (hV : ContDiff ℝ 2 V) (κ : ℝ) (hκ : 0 ≤ κ)
    (hHess : ∀ x z, κ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (C : Ω → C(ℝ, E)) (x₀ : E) (t : ℝ≥0) (ω : Ω) :
    continuousLangevinVersion V C x₀ t ω =
      intervalLangevinEvaluation V t.property (x₀, (C ω).restrict (Icc 0 (t : ℝ))) :=
  (intervalLangevinEvaluation_restrict hV κ hκ hHess t.property x₀ (C ω)).symm

end CutoffRigidity
