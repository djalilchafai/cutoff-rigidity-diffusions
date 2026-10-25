module

public import CutoffRigidity.LangevinMeasurability
public import CutoffRigidity.LangevinTransport
public import Mathlib.Probability.Kernel.Composition.Prod
public import Mathlib.Probability.Kernel.Composition.MapComap
public import Mathlib.Probability.Kernel.Composition.MeasureComp

/-!
# Actual Brownian Langevin transition kernels and transport contraction

The noise law is the actual law of the continuous Brownian driving path.
The proved jointly continuous Langevin evaluation turns independent initial
state and noise into a genuine measurable Markov kernel. Its deterministic
start is identified with the actual Brownian-driven solution law. Synchronous
contraction then gives quadratic Wasserstein contraction for arbitrary initial
probability measures. The fixed global continuous-path noise space uses the
compact-open topology; nonanticipativity identifies its evaluation with the
corresponding finite-interval construction.

The semigroup identity and Gibbs invariance are separate requirements.
-/

public section

open Set MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal

namespace CutoffRigidity

variable {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] [DecidableEq ι]

local notation "E" => EuclideanSpace ℝ ι

/-- The actual law of the continuous Brownian driving path, with its genuine
compact-open Borel structure. -/
@[expose] noncomputable def brownianNoiseLaw
    (B : ℝ≥0 → Ω → E) (P : Measure Ω) : Measure C(ℝ, E) :=
  P.map (brownianContinuousDrivingPath B)

/-- The corresponding actual compact-interval Brownian path law, obtained
by the genuine measurable restriction map. -/
@[expose] noncomputable def brownianIntervalNoiseLaw
    (B : ℝ≥0 → Ω → E) (P : Measure Ω) (t : ℝ≥0) : Measure C(Icc 0 (t : ℝ), E) :=
  (brownianNoiseLaw B P).map (fun w => w.restrict (Icc 0 (t : ℝ)))

theorem brownianNoiseLaw_isProbabilityMeasure
    {B : ℝ≥0 → Ω → E} {P : Measure Ω} (hB : IsEuclideanBrownian B P) :
    IsProbabilityMeasure (brownianNoiseLaw B P) := by
  let := hB.isProbabilityMeasure
  unfold brownianNoiseLaw
  infer_instance

/-- Evaluation of the actual selected solution on a continuous driving path. -/
@[expose] noncomputable def langevinEvaluation (V : E → ℝ) (t : ℝ≥0)
    (p : E × C(ℝ, E)) : E := langevinSolution V p.2 p.1 t

omit [DecidableEq ι] in
theorem langevinEvaluation_continuous
    {V : E → ℝ} (hV : ContDiff ℝ 2 V) (rate : ℝ) (hrate : 0 ≤ rate)
    (hHess : ∀ x z : E, rate * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (t : ℝ≥0) : Continuous (langevinEvaluation V t) :=
  langevinSolution_evaluation_continuous hV rate hrate hHess t.property

/-- The genuine measurable Langevin kernel obtained from independent initial
state and actual Brownian noise, followed by the actual solution evaluation. -/
@[expose] noncomputable def langevinKernel
    (V : E → ℝ) (B : ℝ≥0 → Ω → E) (P : Measure Ω) (t : ℝ≥0) : Kernel E E :=
  ((Kernel.id : Kernel E E).prod (Kernel.const E (brownianNoiseLaw B P))).map
    (langevinEvaluation V t)

theorem langevinKernel_apply_noiseLaw
    {B : ℝ≥0 → Ω → E} {P : Measure Ω} (hB : IsEuclideanBrownian B P)
    {V : E → ℝ} (hV : ContDiff ℝ 2 V) (rate : ℝ) (hrate : 0 ≤ rate)
    (hHess : ∀ x z : E, rate * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (t : ℝ≥0) (x : E) :
    langevinKernel V B P t x = (brownianNoiseLaw B P).map
      (fun w => langevinEvaluation V t (x, w)) := by
  let := brownianNoiseLaw_isProbabilityMeasure hB
  have hm := (langevinEvaluation_continuous hV rate hrate hHess t).measurable
  rw [langevinKernel, Kernel.map_apply _ hm, Kernel.prod_apply, Kernel.id_apply,
    Kernel.const_apply, Measure.dirac_prod, Measure.map_map hm measurable_prodMk_left]
  rfl

/-- Nonanticipativity identifies the kernel with the equivalent construction
from the actual compact-interval Brownian law and interval evaluation. -/
theorem langevinKernel_apply_intervalNoiseLaw
    {B : ℝ≥0 → Ω → E} {P : Measure Ω} (hB : IsEuclideanBrownian B P)
    {V : E → ℝ} (hV : ContDiff ℝ 2 V) (rate : ℝ) (hrate : 0 ≤ rate)
    (hHess : ∀ x z : E, rate * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (t : ℝ≥0) (x : E) :
    langevinKernel V B P t x = (brownianIntervalNoiseLaw B P t).map
      (fun w => intervalLangevinEvaluation V t.property (x, w)) := by
  have hm : Measurable (fun w : C(Icc 0 (t : ℝ), E) =>
      intervalLangevinEvaluation V t.property (x, w)) :=
    ((intervalLangevinEvaluation_continuous hV rate hrate hHess t.property).comp
      (continuous_const.prodMk continuous_id)).measurable
  rw [langevinKernel_apply_noiseLaw hB hV rate hrate hHess]
  calc
    _ = (brownianNoiseLaw B P).map (fun w : C(ℝ, E) =>
        intervalLangevinEvaluation V t.property (x, w.restrict (Icc 0 (t : ℝ)))) := by
      apply Measure.map_congr
      exact Filter.Eventually.of_forall fun w =>
        (intervalLangevinEvaluation_restrict hV rate hrate hHess t.property x w).symm
    _ = _ :=
      (Measure.map_map hm (ContinuousMap.continuous_restrict (Icc 0 (t : ℝ))).measurable).symm

/-- The actual Langevin transition kernel is Markov. -/
theorem langevinKernel_isMarkovKernel
    {B : ℝ≥0 → Ω → E} {P : Measure Ω} (hB : IsEuclideanBrownian B P)
    {V : E → ℝ} (hV : ContDiff ℝ 2 V) (rate : ℝ) (hrate : 0 ≤ rate)
    (hHess : ∀ x z : E, rate * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (t : ℝ≥0) : IsMarkovKernel (langevinKernel V B P t) := by
  let := brownianNoiseLaw_isProbabilityMeasure hB
  constructor
  intro x
  rw [langevinKernel_apply_noiseLaw hB hV rate hrate hHess]
  infer_instance

/-- Deterministic-start transition laws coincide with the actual canonical
Brownian-driven Langevin solution laws. -/
theorem langevinKernel_apply_eq_process_law
    {B : ℝ≥0 → Ω → E} {P : Measure Ω} (hB : IsEuclideanBrownian B P)
    {V : E → ℝ} (hV : ContDiff ℝ 2 V) (rate : ℝ) (hrate : 0 ≤ rate)
    (hHess : ∀ x z : E, rate * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (t : ℝ≥0) (x : E) : langevinKernel V B P t x = P.map (langevinProcess V B x t) := by
  rw [langevinKernel_apply_noiseLaw hB hV rate hrate hHess]
  have hm : Measurable (fun w : C(ℝ, E) => langevinEvaluation V t (x, w)) :=
    ((langevinEvaluation_continuous hV rate hrate hHess t).comp
      (continuous_const.prodMk continuous_id)).measurable
  rw [brownianNoiseLaw, hm.aemeasurable.map_map_of_aemeasurable
    (brownianContinuousDrivingPath_aemeasurable hB)]
  apply Measure.map_congr
  filter_upwards [brownianContinuousDrivingPath_coe_ae hB] with ω hω
  change langevinSolution V (brownianContinuousDrivingPath B ω) x t =
    langevinSolution V (brownianDrivingPath B ω) x t
  rw [hω]

/-- The actual transition kernel at time zero is the identity kernel. -/
theorem langevinKernel_zero
    {B : ℝ≥0 → Ω → E} {P : Measure Ω} (hB : IsEuclideanBrownian B P)
    {V : E → ℝ} (hV : ContDiff ℝ 2 V) (rate : ℝ) (hrate : 0 ≤ rate)
    (hHess : ∀ x z : E, rate * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z) :
    langevinKernel V B P 0 = Kernel.id := by
  let := hB.isProbabilityMeasure
  apply Kernel.ext
  intro x
  rw [langevinKernel_apply_eq_process_law hB hV rate hrate hHess]
  have heq : langevinProcess V B x 0 =ᵐ[P] fun _ => x := by
    filter_upwards [brownianDrivingPath_continuous_ae hB] with ω hω
    exact langevinSolution_initial hV rate hrate hHess hω x
  rw [Measure.map_congr heq, Measure.map_const, measure_univ, one_smul, Kernel.id_apply]

/-- Kernel updates are the actual independent random-map updates used by
synchronous quadratic transport. -/
theorem langevinKernel_comp_eq_randomMapLaw
    {B : ℝ≥0 → Ω → E} {P : Measure Ω} (hB : IsEuclideanBrownian B P)
    {V : E → ℝ} (hV : ContDiff ℝ 2 V) (rate : ℝ) (hrate : 0 ≤ rate)
    (hHess : ∀ x z : E, rate * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (t : ℝ≥0) (μ : Measure E) [IsProbabilityMeasure μ] :
    (langevinKernel V B P t) ∘ₘ μ = randomMapLaw μ (brownianNoiseLaw B P) (langevinEvaluation V t) := by
  let := brownianNoiseLaw_isProbabilityMeasure hB
  have hm := (langevinEvaluation_continuous hV rate hrate hHess t).measurable
  rw [langevinKernel, ← Measure.map_comp μ _ hm, ← Measure.compProd_eq_comp_prod,
    Measure.compProd_const]
  rfl

/-- Genuine quadratic Wasserstein contraction for the actual Brownian-driven
Langevin kernel and arbitrary initial probability laws. All path construction
and solution-measurability obligations are discharged by proved theorems. -/
theorem squaredWasserstein_langevinKernel_comp_le
    {B : ℝ≥0 → Ω → E} {P : Measure Ω} (hB : IsEuclideanBrownian B P)
    {V : E → ℝ} (hV : ContDiff ℝ 2 V) (rate : ℝ) (hrate : 0 ≤ rate)
    (hHess : ∀ x z : E, rate * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (t : ℝ≥0) (μ ν : Measure E) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    squaredWasserstein ((langevinKernel V B P t) ∘ₘ μ) ((langevinKernel V B P t) ∘ₘ ν) ≤
      ENNReal.ofReal (Real.exp (-2 * rate * t)) * squaredWasserstein μ ν := by
  let := brownianNoiseLaw_isProbabilityMeasure hB
  have hm := (langevinEvaluation_continuous hV rate hrate hHess t).measurable
  have h := langevin_update_transport_contraction hV rate hHess (brownianNoiseLaw B P)
    (fun w : C(ℝ, E) => (w : ℝ → E)) (fun x w => langevinSolution V w x) t.property
    (fun x w => langevinSolution_isLangevinPathOn hV rate hrate hHess w.continuous x t.property) hm μ ν
  rw [langevinKernel_comp_eq_randomMapLaw hB hV rate hrate hHess,
    langevinKernel_comp_eq_randomMapLaw hB hV rate hrate hHess]
  exact h

end CutoffRigidity
