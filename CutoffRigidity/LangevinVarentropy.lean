module
public import CutoffRigidity.WeakLogLikelihoodPoincare
public import CutoffRigidity.LangevinTransitionLocalDomination
public import CutoffRigidity.LangevinFisherFinite

/-! # Genuine Salez varentropy bound for actual Langevin transitions

The actual transition RN density is locally bounded by the proved power
Harnack argument. Canonical positive-time Fisher and entropy are finite.
Weak RN-root logarithmic approximation therefore discharges every domain
obligation in the written local Poincare application, even from a point mass.
-/
public section
namespace CutoffRigidity
open MeasureTheory ProbabilityTheory InformationTheory Set
open scoped NNReal ENNReal
variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

/-- Full source-domain varentropy control with the exact curvature factor.
No classical density, log-likelihood regularity, second moment of the log,
local domination, or information-value premise is supplied. -/
theorem langevinKernel_varentropy_le_fisher
    {B : NNReal → Ω → E} {P : Measure Ω} (hB : IsEuclideanBrownian B P)
    {V : E → ℝ} (hV : ContDiff ℝ 2 V) (hp : IsProbabilityMeasure (gibbsMeasure volume V))
    (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (T : NNReal) (hT : 0 < T) (x : E) :
    letI := langevinKernel_isMarkovKernel hB hV ρ hρ.le hHess T
    MemLp (llr (langevinKernel V B P T x) (gibbsMeasure volume V)) 2 (langevinKernel V B P T x) ∧
      varentropy (langevinKernel V B P T x) (gibbsMeasure volume V) ≠ ⊤ ∧
      (varentropy (langevinKernel V B P T x) (gibbsMeasure volume V)).toReal ≤
        ((1-Real.exp (-2*ρ*T))/ρ) *
          (relativeFisherInformation hV hp (langevinKernel V B P T x)).toReal := by
  let := langevinKernel_isMarkovKernel hB hV ρ hρ.le hHess T
  have hTR : (0:ℝ) < T := by exact_mod_cast hT
  have hC : 0 ≤ (1-Real.exp (-2*ρ*T))/ρ := by
    apply div_nonneg _ hρ.le
    apply sub_nonneg.mpr
    exact Real.exp_le_one_iff.mpr (by nlinarith [T.property])
  have hPI := langevinKernel_hasLocalSmoothPoincare hB hV hp ρ hρ hHess T T.property x
  rw [@Real.toNNReal_coe T] at hPI
  apply varentropy_le_fisher_of_local_poincare hV hp _
    (relativeFisherInformation_langevinKernel_ne_top hB hV hp ρ hρ hHess T hT x)
    (by simpa only [@Real.toNNReal_coe T] using klDiv_langevinKernel_ne_top hB hV hp ρ hρ hHess x T hTR)
    _ hC hPI
  intro K hK
  obtain ⟨M,hM,hBound⟩ := langevinKernel_restrict_le_volume hB hV hp ρ hρ hHess T hT x K hK
  exact ⟨ENNReal.ofReal M,ENNReal.ofReal_ne_top,hBound⟩

/-- The genuine factor 2T used in Salez's entropy-window proof. -/
theorem langevinKernel_varentropy_le_time_fisher
    {B : NNReal → Ω → E} {P : Measure Ω} (hB : IsEuclideanBrownian B P)
    {V : E → ℝ} (hV : ContDiff ℝ 2 V) (hp : IsProbabilityMeasure (gibbsMeasure volume V))
    (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (T : NNReal) (hT : 0 < T) (x : E) :
    letI := langevinKernel_isMarkovKernel hB hV ρ hρ.le hHess T
    MemLp (llr (langevinKernel V B P T x) (gibbsMeasure volume V)) 2 (langevinKernel V B P T x) ∧
      varentropy (langevinKernel V B P T x) (gibbsMeasure volume V) ≠ ⊤ ∧
      (varentropy (langevinKernel V B P T x) (gibbsMeasure volume V)).toReal ≤
        (2*(T:ℝ)) * (relativeFisherInformation hV hp (langevinKernel V B P T x)).toReal := by
  let := langevinKernel_isMarkovKernel hB hV ρ hρ.le hHess T
  have hh := langevinKernel_varentropy_le_fisher hB hV hp ρ hρ hHess T hT x
  refine ⟨hh.1,hh.2.1,hh.2.2.trans ?_⟩
  apply mul_le_mul_of_nonneg_right _ ENNReal.toReal_nonneg
  apply (div_le_iff₀ hρ).mpr
  have he := Real.add_one_le_exp (-2*ρ*T)
  nlinarith


/-- The genuine reverse-Pinsker/local-Poincare comparison used in the Salez
window differential inequality. Only the actual TV threshold and the
large-entropy branch are premises; all information domains are derived. -/
theorem langevinKernel_entropy_fisher_of_tv
    {B : NNReal → Ω → E} {P : Measure Ω} (hB : IsEuclideanBrownian B P)
    {V : E → ℝ} (hV : ContDiff ℝ 2 V) (hp : IsProbabilityMeasure (gibbsMeasure volume V))
    (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (T : NNReal) (hT : 0 < T) (x : E)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (hTV : totalVariationDistance (langevinKernel V B P T x) (gibbsMeasure volume V) ≤ 1-ε)
    (hLarge : 1/ε < (klDiv (langevinKernel V B P T x) (gibbsMeasure volume V)).toReal) :
    letI := langevinKernel_isMarkovKernel hB hV ρ hρ.le hHess T
    (ε*(klDiv (langevinKernel V B P T x) (gibbsMeasure volume V)).toReal-1)^2 ≤
      (2*(T:ℝ))*(relativeFisherInformation hV hp (langevinKernel V B P T x)).toReal := by
  let := hp
  let := langevinKernel_isMarkovKernel hB hV ρ hρ.le hHess T
  have hd := langevinKernel_varentropy_le_time_fisher hB hV hp ρ hρ hHess T hT x
  have hTR : (0:ℝ)<T := by exact_mod_cast hT
  have hAC := langevinKernel_absolutelyContinuous_gibbs hB hV hp ρ hρ hHess x T hTR
  rw [@Real.toNNReal_coe T] at hAC
  have hrev := klDiv_toReal_le_varentropy_of_tv_le (langevinKernel V B P T x)
    (gibbsMeasure volume V) hAC hd.1 hε hε1 hTV
  have hsqrt : ε*(klDiv (langevinKernel V B P T x) (gibbsMeasure volume V)).toReal-1 ≤
      Real.sqrt (variance (llr (langevinKernel V B P T x) (gibbsMeasure volume V))
        (langevinKernel V B P T x)) := by
    have hh := (le_div_iff₀ hε).mp hrev
    nlinarith
  have hpos : 0 ≤ ε*(klDiv (langevinKernel V B P T x) (gibbsMeasure volume V)).toReal-1 := by
    have hh := (div_lt_iff₀ hε).mp hLarge
    nlinarith
  have hsq := (sq_le_sq₀ hpos (Real.sqrt_nonneg _)).mpr hsqrt
  rw [Real.sq_sqrt (variance_nonneg _ _)] at hsq
  exact hsq.trans hd.2.2

end CutoffRigidity
