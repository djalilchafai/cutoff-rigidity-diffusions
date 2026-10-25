module

public import CutoffRigidity.LangevinContinuity
public import CutoffRigidity.LangevinBrownian
public import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousMap
public import Mathlib.Topology.ContinuousMap.SecondCountableSpace

/-!
# Measurability of the actual Brownian-driven Langevin solution

Almost surely continuous Brownian sample paths are bundled into genuine
continuous maps, with zero used on the exceptional set. Their coordinate
measurability implies null measurability in continuous-path space, hence
almost-everywhere measurability because that Borel space is countably generated.
Joint continuity of the actual deterministic solution evaluation then proves
measurability of the Brownian-driven solution at each fixed time.

The stochastic solution's measurability is proved here, not included as an
assumption in its definition. Adaptedness and Markov identities are separate.
-/

public section

open MeasureTheory ProbabilityTheory
open scoped Topology NNReal

namespace CutoffRigidity

/-- A continuous-map-valued random variable is a.e. measurable when all its
evaluations are. The proof uses the actual evaluation-generated Borel algebra
and its countable generation, rather than a pointwise-to-path assumption. -/
theorem aemeasurable_continuousMap_of_aemeasurable_eval
    {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E]
    [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E]
    {P : Measure Ω} {g : Ω → C(ℝ, E)}
    (h : ∀ t : ℝ, AEMeasurable (fun ω => g ω t) P) : AEMeasurable g P := by
  have hm : Measurable (fun ω : NullMeasurableSpace Ω P => g ω) := by
    apply ContinuousMap.measurable_iff_eval.mpr
    intro t
    exact (h t).nullMeasurable.measurable'
  have hnull : NullMeasurable g P := hm
  exact hnull.aemeasurable

variable {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]

/-- Bundle the actual Brownian noise as a continuous path wherever it is
continuous; set it to zero on the null exceptional set. -/
@[expose] noncomputable def brownianContinuousDrivingPath
    (B : ℝ≥0 → Ω → EuclideanSpace ℝ ι) (ω : Ω) : C(ℝ, EuclideanSpace ℝ ι) := by
  classical
  exact if h : Continuous (brownianDrivingPath B ω) then ⟨brownianDrivingPath B ω, h⟩ else 0

theorem brownianContinuousDrivingPath_coe_ae
    {B : ℝ≥0 → Ω → EuclideanSpace ℝ ι} {P : Measure Ω} (hB : IsEuclideanBrownian B P) :
    (fun ω => (brownianContinuousDrivingPath B ω : ℝ → EuclideanSpace ℝ ι)) =ᵐ[P]
      brownianDrivingPath B := by
  filter_upwards [brownianDrivingPath_continuous_ae hB] with ω hω
  simp only [brownianContinuousDrivingPath, dite_eq_left hω]
  rfl

theorem brownianDrivingPath_aemeasurable_eval
    {B : ℝ≥0 → Ω → EuclideanSpace ℝ ι} {P : Measure Ω} (hB : IsEuclideanBrownian B P)
    (t : ℝ) : AEMeasurable (fun ω => brownianDrivingPath B ω t) P := by
  classical
  exact (hB.aemeasurable_eval t.toNNReal).const_smul (Real.sqrt 2)

/-- The continuous Brownian noise path is an actual a.e. measurable random
element of continuous-path space. -/
theorem brownianContinuousDrivingPath_aemeasurable
    {B : ℝ≥0 → Ω → EuclideanSpace ℝ ι} {P : Measure Ω} (hB : IsEuclideanBrownian B P) :
    AEMeasurable (brownianContinuousDrivingPath B) P := by
  apply aemeasurable_continuousMap_of_aemeasurable_eval
  intro t
  have heq : (fun ω => brownianContinuousDrivingPath B ω t) =ᵐ[P]
      (fun ω => brownianDrivingPath B ω t) :=
    (brownianContinuousDrivingPath_coe_ae hB).mono fun _ h => congrFun h t
  exact (brownianDrivingPath_aemeasurable_eval hB t).congr heq.symm

/-- The actual canonical Brownian-driven Langevin process is a.e. measurable
at every fixed time, derived from continuous-path measurability and the proved
joint continuity of the deterministic solution map. -/
theorem langevinProcess_aemeasurable_eval
    {B : ℝ≥0 → Ω → EuclideanSpace ℝ ι} {P : Measure Ω} (hB : IsEuclideanBrownian B P)
    {V : EuclideanSpace ℝ ι → ℝ} (hV : ContDiff ℝ 2 V)
    (rate : ℝ) (hrate : 0 ≤ rate)
    (hHess : ∀ x z : EuclideanSpace ℝ ι,
      rate * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (x₀ : EuclideanSpace ℝ ι) (t : ℝ≥0) : AEMeasurable (langevinProcess V B x₀ t) P := by
  have hcont : Continuous (fun w : C(ℝ, EuclideanSpace ℝ ι) => langevinSolution V w x₀ t) :=
    (langevinSolution_evaluation_continuous hV rate hrate hHess t.property).comp
      (continuous_const.prodMk continuous_id)
  have hm := hcont.measurable.comp_aemeasurable (brownianContinuousDrivingPath_aemeasurable hB)
  apply hm.congr
  filter_upwards [brownianContinuousDrivingPath_coe_ae hB] with ω hω
  change langevinSolution V (brownianContinuousDrivingPath B ω) x₀ t =
    langevinSolution V (brownianDrivingPath B ω) x₀ t
  rw [hω]

end CutoffRigidity
