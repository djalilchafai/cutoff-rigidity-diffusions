module

public import CutoffRigidity.Brownian
public import CutoffRigidity.LangevinGlobalExistence
public import CutoffRigidity.LangevinSolution

/-!
# Brownian driving paths and Langevin trajectory existence

The Brownian motion is the genuine independent-coordinate process of
`Brownian.lean`. Its almost-surely continuous samples drive the actual
Langevin integral equation. This does not yet construct a jointly measurable,
adapted solution family or identify its transition semigroup.
-/

public section

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace CutoffRigidity

variable {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]

/-- The paper's `sqrt 2` Brownian noise, continuously extended to negative
times by its time-zero value for the deterministic ODE construction. -/
@[expose] noncomputable def brownianDrivingPath
    (B : ℝ≥0 → Ω → EuclideanSpace ℝ ι) (ω : Ω) (t : ℝ) : EuclideanSpace ℝ ι :=
  Real.sqrt 2 • B t.toNNReal ω

/-- The actual selected trajectory driven by each Brownian sample. Measurability
and adaptedness are separate obligations, not fields assumed by this definition. -/
@[expose] noncomputable def langevinProcess (V : EuclideanSpace ℝ ι → ℝ)
    (B : ℝ≥0 → Ω → EuclideanSpace ℝ ι) (x₀ : EuclideanSpace ℝ ι)
    (t : ℝ≥0) (ω : Ω) : EuclideanSpace ℝ ι :=
  langevinSolution V (brownianDrivingPath B ω) x₀ t

theorem brownianDrivingPath_continuous_ae
    {B : ℝ≥0 → Ω → EuclideanSpace ℝ ι} {P : Measure Ω}
    (hB : IsEuclideanBrownian B P) :
    ∀ᵐ ω ∂P, Continuous (brownianDrivingPath B ω) := by
  filter_upwards [hB.continuous_paths] with ω hω
  change Continuous (fun t : ℝ => (Real.sqrt 2 : ℝ) • B t.toNNReal ω)
  exact (continuous_const : Continuous (fun _ : ℝ => Real.sqrt 2)).smul
    (hω.comp continuous_real_toNNReal)

theorem brownianDrivingPath_initial_zero_ae
    {B : ℝ≥0 → Ω → EuclideanSpace ℝ ι} {P : Measure Ω}
    (hB : IsEuclideanBrownian B P) : ∀ᵐ ω ∂P, brownianDrivingPath B ω 0 = 0 := by
  filter_upwards [hB.initial_ae_eq_zero] with ω hω
  simp [brownianDrivingPath, hω]

/-- Almost every genuine Brownian sample admits a Langevin trajectory on
any fixed finite horizon, derived from deterministic existence. -/
theorem brownian_langevin_path_exists_ae
    {B : ℝ≥0 → Ω → EuclideanSpace ℝ ι} {P : Measure Ω}
    (hB : IsEuclideanBrownian B P)
    {V : EuclideanSpace ℝ ι → ℝ} (hV : ContDiff ℝ 2 V)
    (rate : ℝ) (hrate : 0 ≤ rate)
    (hHess : ∀ x z : EuclideanSpace ℝ ι,
      rate * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (x₀ : EuclideanSpace ℝ ι) (T : ℝ) (hT : 0 ≤ T) :
    ∀ᵐ ω ∂P, ∃ X : ℝ → EuclideanSpace ℝ ι,
      IsLangevinPathOn V (brownianDrivingPath B ω) x₀ X T := by
  filter_upwards [brownianDrivingPath_continuous_ae hB] with ω hω
  exact exists_langevin_path_on hV rate hrate hHess hω x₀ hT

/-- The actual Brownian samples admit a single trajectory on all forward
finite horizons. Joint measurability and adaptedness remain to be proved. -/
theorem brownian_global_langevin_path_exists_ae
    {B : ℝ≥0 → Ω → EuclideanSpace ℝ ι} {P : Measure Ω}
    (hB : IsEuclideanBrownian B P)
    {V : EuclideanSpace ℝ ι → ℝ} (hV : ContDiff ℝ 2 V)
    (rate : ℝ) (hrate : 0 ≤ rate)
    (hHess : ∀ x z : EuclideanSpace ℝ ι,
      rate * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (x₀ : EuclideanSpace ℝ ι) :
    ∀ᵐ ω ∂P, ∃ X : ℝ → EuclideanSpace ℝ ι,
      ∀ T ≥ 0, IsLangevinPathOn V (brownianDrivingPath B ω) x₀ X T := by
  filter_upwards [brownianDrivingPath_continuous_ae hB] with ω hω
  exact exists_global_langevin_path hV rate hrate hHess hω x₀

/-- Almost surely the selected family is continuous in forward time. -/
theorem langevinProcess_continuous_paths_ae
    {B : ℝ≥0 → Ω → EuclideanSpace ℝ ι} {P : Measure Ω}
    (hB : IsEuclideanBrownian B P)
    {V : EuclideanSpace ℝ ι → ℝ} (hV : ContDiff ℝ 2 V)
    (rate : ℝ) (hrate : 0 ≤ rate)
    (hHess : ∀ x z : EuclideanSpace ℝ ι,
      rate * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (x₀ : EuclideanSpace ℝ ι) :
    ∀ᵐ ω ∂P, Continuous (fun t => langevinProcess V B x₀ t ω) := by
  filter_upwards [brownianDrivingPath_continuous_ae hB] with ω hω
  exact (langevinSolution_continuousOn hV rate hrate hHess hω x₀).comp_continuous
    continuous_subtype_val (fun t => t.property)

/-- The selected trajectories satisfy precisely the paper's additive-noise
integral equation, almost surely and simultaneously at every forward time. -/
theorem langevinProcess_integral_equation_ae
    {B : ℝ≥0 → Ω → EuclideanSpace ℝ ι} {P : Measure Ω}
    (hB : IsEuclideanBrownian B P)
    {V : EuclideanSpace ℝ ι → ℝ} (hV : ContDiff ℝ 2 V)
    (rate : ℝ) (hrate : 0 ≤ rate)
    (hHess : ∀ x z : EuclideanSpace ℝ ι,
      rate * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (x₀ : EuclideanSpace ℝ ι) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      langevinProcess V B x₀ t ω = x₀ + Real.sqrt 2 • B t ω -
        ∫ s in 0..(t : ℝ), gradient V (langevinProcess V B x₀ s.toNNReal ω) := by
  filter_upwards [brownianDrivingPath_continuous_ae hB,
    brownianDrivingPath_initial_zero_ae hB] with ω hω hzero
  intro t
  have h := (langevinSolution_isLangevinPathOn hV rate hrate hHess hω x₀
    t.property).2 t ⟨t.property, le_rfl⟩
  have hi : (∫ s in 0..(t : ℝ), gradient V (langevinSolution V (brownianDrivingPath B ω) x₀ s)) =
      ∫ s in 0..(t : ℝ), gradient V (langevinProcess V B x₀ s.toNNReal ω) := by
    apply intervalIntegral.integral_congr
    intro s hs
    have hs0 : (0 : ℝ) ≤ s := (le_min le_rfl t.property).trans hs.1
    change gradient V (langevinSolution V (brownianDrivingPath B ω) x₀ s) =
      gradient V (langevinSolution V (brownianDrivingPath B ω) x₀ (s.toNNReal : ℝ))
    rw [Real.coe_toNNReal s hs0]
  rw [hi, hzero, sub_zero] at h
  simpa only [langevinProcess, brownianDrivingPath, Real.toNNReal_coe] using h

end CutoffRigidity
