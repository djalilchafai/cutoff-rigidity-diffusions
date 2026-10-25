module
public import CutoffRigidity.InvariantKernelL2
public import CutoffRigidity.LangevinGibbsInvariance

/-! # Full stochastic/form L² semigroup identification

The actual nonlinear Brownian kernel is lifted using its proved genuine
Gibbs invariance. Compact-test identification and actual smooth density
then identify the resulting contraction with canonical form heat on all L².
-/
public section
namespace CutoffRigidity
open MeasureTheory ProbabilityTheory Filter Topology
variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

@[expose] noncomputable def langevinL2Operator
    {B : NNReal → Ω → E} {P : Measure Ω} (hB : IsEuclideanBrownian B P)
    {V : E → ℝ} (hV : ContDiff ℝ 2 V) (hp : IsProbabilityMeasure (gibbsMeasure volume V))
    (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (t : NNReal) : (E →₂[gibbsMeasure volume V] ℝ) →L[ℝ] (E →₂[gibbsMeasure volume V] ℝ) := by
  let := hp
  let := langevinKernel_isMarkovKernel hB hV ρ hρ.le hHess t
  exact invariantKernelL2Operator (langevinKernel V B P t)
    (langevinKernel_gibbs_invariant hB hV hp ρ hρ hHess t)

theorem langevinL2Operator_coeFn
    {B : NNReal → Ω → E} {P : Measure Ω} (hB : IsEuclideanBrownian B P)
    {V : E → ℝ} (hV : ContDiff ℝ 2 V) (hp : IsProbabilityMeasure (gibbsMeasure volume V))
    (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (t : NNReal) (u : E →₂[gibbsMeasure volume V] ℝ) :
    langevinL2Operator hB hV hp ρ hρ hHess t u =ᵐ[gibbsMeasure volume V]
      fun x => ∫ y, u y ∂langevinKernel V B P t x := by
  let := hp
  let := langevinKernel_isMarkovKernel hB hV ρ hρ.le hHess t
  exact invariantKernelL2Operator_coeFn (langevinKernel V B P t)
    (langevinKernel_gibbs_invariant hB hV hp ρ hρ hHess t) u

/-- Full actual L² identification, with neither invariance nor equality
of the stochastic and form operators supplied as a premise. -/
theorem langevinL2Operator_eq_gibbsHeatSemigroup
    {B : NNReal → Ω → E} {P : Measure Ω} (hB : IsEuclideanBrownian B P)
    {V : E → ℝ} (hV : ContDiff ℝ 2 V) (hp : IsProbabilityMeasure (gibbsMeasure volume V))
    (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z) (t : NNReal) :
    langevinL2Operator hB hV hp ρ hρ hHess t = gibbsHeatSemigroup hV hp ρ hρ hHess t := by
  let := hp
  let := langevinKernel_isMarkovKernel hB hV ρ hρ.le hHess t
  have hInv := langevinKernel_gibbs_invariant hB hV hp ρ hρ hHess t
  apply DFunLike.coe_injective
  apply Continuous.ext_on (compactGibbsGeneratorDomain_dense V hp)
    (langevinL2Operator hB hV hp ρ hρ hHess t).continuous
    (gibbsHeatSemigroup hV hp ρ hρ hHess t).continuous
  intro u hu
  let v : compactGibbsGeneratorDomain V := ⟨u, hu⟩
  let f := compactGibbsRepresentative V v
  have hf := (compactGibbsRepresentative_spec V v).1
  have hfc := (compactGibbsRepresentative_spec V v).2.1
  have hrep : u =ᵐ[gibbsMeasure volume V] f := (compactGibbsRepresentative_spec V v).2.2.symm
  have hinput : (hf.continuous.memLp_of_hasCompactSupport hfc).toLp f = u :=
    Lp.ext ((hf.continuous.memLp_of_hasCompactSupport hfc).coeFn_toLp.trans hrep.symm)
  have hK : langevinL2Operator hB hV hp ρ hρ hHess t u =
      langevinCompactTestLp hB hV ρ hρ.le hHess hf.continuous hfc (gibbsMeasure volume V) t := by
    apply Lp.ext
    exact (langevinL2Operator_coeFn hB hV hp ρ hρ hHess t u).trans
      ((invariantKernel_integral_congr_ae (langevinKernel V B P t) hInv hrep).trans
        (langevinCompactTestLp_coeFn hB hV ρ hρ.le hHess hf.continuous hfc (gibbsMeasure volume V) t).symm)
  rw [hK, langevinCompactTestLp_eq_gibbsHeatSemigroup hB hV hp ρ hρ hHess hf hfc t, hinput]

theorem norm_langevinL2Operator_le_one
    {B : NNReal → Ω → E} {P : Measure Ω} (hB : IsEuclideanBrownian B P)
    {V : E → ℝ} (hV : ContDiff ℝ 2 V) (hp : IsProbabilityMeasure (gibbsMeasure volume V))
    (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z) (t : NNReal) :
    ‖langevinL2Operator hB hV hp ρ hρ hHess t‖ ≤ 1 := by
  rw [langevinL2Operator_eq_gibbsHeatSemigroup hB hV hp ρ hρ hHess t]
  exact norm_gibbsHeatSemigroup_le_one hV hp ρ hρ hHess t

theorem langevinL2Operator_add
    {B : NNReal → Ω → E} {P : Measure Ω} (hB : IsEuclideanBrownian B P)
    {V : E → ℝ} (hV : ContDiff ℝ 2 V) (hp : IsProbabilityMeasure (gibbsMeasure volume V))
    (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z) (s t : NNReal) :
    langevinL2Operator hB hV hp ρ hρ hHess (s + t) =
      (langevinL2Operator hB hV hp ρ hρ hHess s).comp (langevinL2Operator hB hV hp ρ hρ hHess t) := by
  simp_rw [langevinL2Operator_eq_gibbsHeatSemigroup hB hV hp ρ hρ hHess]
  exact gibbsHeatSemigroup_add hV hp ρ hρ hHess s t

theorem continuous_langevinL2Operator_apply
    {B : NNReal → Ω → E} {P : Measure Ω} (hB : IsEuclideanBrownian B P)
    {V : E → ℝ} (hV : ContDiff ℝ 2 V) (hp : IsProbabilityMeasure (gibbsMeasure volume V))
    (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (u : E →₂[gibbsMeasure volume V] ℝ) :
    Continuous (fun t : NNReal => langevinL2Operator hB hV hp ρ hρ hHess t u) := by
  simp_rw [langevinL2Operator_eq_gibbsHeatSemigroup hB hV hp ρ hρ hHess]
  exact continuous_gibbsHeatSemigroup_apply hV hp ρ hρ hHess u

theorem langevinL2Operator_zero
    {B : NNReal → Ω → E} {P : Measure Ω} (hB : IsEuclideanBrownian B P)
    {V : E → ℝ} (hV : ContDiff ℝ 2 V) (hp : IsProbabilityMeasure (gibbsMeasure volume V))
    (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z) :
    langevinL2Operator hB hV hp ρ hρ hHess 0 = ContinuousLinearMap.id ℝ _ := by
  rw [langevinL2Operator_eq_gibbsHeatSemigroup hB hV hp ρ hρ hHess 0]
  exact gibbsHeatSemigroup_zero hV hp ρ hρ hHess

theorem langevinL2Operator_symmetric
    {B : NNReal → Ω → E} {P : Measure Ω} (hB : IsEuclideanBrownian B P)
    {V : E → ℝ} (hV : ContDiff ℝ 2 V) (hp : IsProbabilityMeasure (gibbsMeasure volume V))
    (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (t : NNReal) (f g : E →₂[gibbsMeasure volume V] ℝ) :
    inner ℝ (langevinL2Operator hB hV hp ρ hρ hHess t f) g =
      inner ℝ f (langevinL2Operator hB hV hp ρ hρ hHess t g) := by
  rw [langevinL2Operator_eq_gibbsHeatSemigroup hB hV hp ρ hρ hHess t]
  exact gibbsHeatSemigroup_symmetric hV hp ρ hρ hHess t f g

end CutoffRigidity
