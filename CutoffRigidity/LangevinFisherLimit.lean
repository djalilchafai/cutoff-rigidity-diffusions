module
public import CutoffRigidity.LangevinL1Density
public import CutoffRigidity.FisherLowerSemicontinuity
public import CutoffRigidity.HellingerL2Convergence

/-! # Genuine L¹ and Fisher limit transfer for actual transition laws

Actual RN density evolution and invariant-kernel contraction transfer the
input L¹ convergence. Hellinger convergence and closed-gradient energy lower
semicontinuity then control canonical Fisher information after transition.
-/
public section
namespace CutoffRigidity
open MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal ENNReal
variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

theorem tendsto_L1_rnDeriv_langevinKernel
    {B : NNReal → Ω → E} {P : Measure Ω} (hB : IsEuclideanBrownian B P)
    {V : E → ℝ} (hV : ContDiff ℝ 2 V) (hp : IsProbabilityMeasure (gibbsMeasure volume V))
    (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (ν : Measure E) [IsProbabilityMeasure ν]
    (νn : ℕ → Measure E) [∀ n, IsProbabilityMeasure (νn n)]
    (hAC : ν ≪ gibbsMeasure volume V) (hACn : ∀ n, νn n ≪ gibbsMeasure volume V)
    (hlim : Tendsto (fun n => ∫ x,
      |((νn n).rnDeriv (gibbsMeasure volume V) x).toReal -
        (ν.rnDeriv (gibbsMeasure volume V) x).toReal| ∂gibbsMeasure volume V) atTop (𝓝 0))
    (t : NNReal) :
    Tendsto (fun n => ∫ x,
      |((langevinKernel V B P t ∘ₘ νn n).rnDeriv (gibbsMeasure volume V) x).toReal -
        ((langevinKernel V B P t ∘ₘ ν).rnDeriv (gibbsMeasure volume V) x).toReal|
        ∂gibbsMeasure volume V) atTop (𝓝 0) := by
  let := hp
  let μ := gibbsMeasure volume V
  let K := langevinKernel V B P t
  let := langevinKernel_isMarkovKernel hB hV ρ hρ.le hHess t
  have hInv : K ∘ₘ μ = μ := langevinKernel_gibbs_invariant hB hV hp ρ hρ hHess t
  apply squeeze_zero (fun n => integral_nonneg (fun x => abs_nonneg _)) ?_ hlim
  intro n
  have hh := invariantKernel_L1_contraction K hInv
    (Measure.measurable_rnDeriv (νn n) μ).ennreal_toReal (Measure.measurable_rnDeriv ν μ).ennreal_toReal
    (integrable_toReal_rnDeriv_finite (νn n) μ) (integrable_toReal_rnDeriv_finite ν μ)
  have heq : (∫ x, |((K ∘ₘ νn n).rnDeriv μ x).toReal - ((K ∘ₘ ν).rnDeriv μ x).toReal| ∂μ) =
      ∫ x, |(∫ y, ((νn n).rnDeriv μ y).toReal ∂K x) - ∫ y, (ν.rnDeriv μ y).toReal ∂K x| ∂μ := by
    apply integral_congr_ae
    filter_upwards [langevinKernel_rnDeriv_toReal hB hV hp ρ hρ hHess (νn n) (hACn n) t,
      langevinKernel_rnDeriv_toReal hB hV hp ρ hρ hHess ν hAC t] with x hn hx
    rw [hn, hx]
  exact heq.trans_le hh

theorem relativeFisherInformation_langevinKernel_le_liminf_of_L1_rnDeriv
    {B : NNReal → Ω → E} {P : Measure Ω} (hB : IsEuclideanBrownian B P)
    {V : E → ℝ} (hV : ContDiff ℝ 2 V) (hp : IsProbabilityMeasure (gibbsMeasure volume V))
    (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (ν : Measure E) [IsProbabilityMeasure ν]
    (νn : ℕ → Measure E) [∀ n, IsProbabilityMeasure (νn n)]
    (hAC : ν ≪ gibbsMeasure volume V) (hACn : ∀ n, νn n ≪ gibbsMeasure volume V)
    (hlim : Tendsto (fun n => ∫ x,
      |((νn n).rnDeriv (gibbsMeasure volume V) x).toReal -
        (ν.rnDeriv (gibbsMeasure volume V) x).toReal| ∂gibbsMeasure volume V) atTop (𝓝 0))
    (t : NNReal) :
    letI := langevinKernel_isMarkovKernel hB hV ρ hρ.le hHess t
    relativeFisherInformation hV hp (langevinKernel V B P t ∘ₘ ν) ≤
      liminf (fun n => relativeFisherInformation hV hp (langevinKernel V B P t ∘ₘ νn n)) atTop := by
  let := hp
  let K := langevinKernel V B P t
  let : IsMarkovKernel K := langevinKernel_isMarkovKernel hB hV ρ hρ.le hHess t
  let : IsProbabilityMeasure (K ∘ₘ ν) := inferInstance
  let : ∀ n, IsProbabilityMeasure (K ∘ₘ νn n) := fun n => inferInstance
  have hRoot := tendsto_squareRootRNDensityLp_of_L1_rnDeriv (gibbsMeasure volume V)
    (K ∘ₘ ν) (fun n => K ∘ₘ νn n)
    (tendsto_L1_rnDeriv_langevinKernel hB hV hp ρ hρ hHess ν νn hAC hACn hlim t)
  exact relativeFisherInformation_le_liminf_of_squareRoot_tendsto hV hp (K ∘ₘ ν)
    (fun n => K ∘ₘ νn n)
    (langevinKernel_comp_absolutelyContinuous hB hV hp ρ hρ hHess ν hAC t)
    (fun n => langevinKernel_comp_absolutelyContinuous hB hV hp ρ hρ hHess (νn n) (hACn n) t) hRoot

end CutoffRigidity
