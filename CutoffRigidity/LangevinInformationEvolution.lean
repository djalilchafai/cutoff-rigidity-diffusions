module
public import CutoffRigidity.FiniteEntropyCoreApproximation
public import CutoffRigidity.LangevinCoreApproximationTransfer
public import CutoffRigidity.LangevinEntropyRegularization

/-! # Full actual entropy evolution and Fisher entropy-endpoint bounds

Every finite-entropy law has genuine positive compact C² approximants.
The proved core estimates and actual limit transfers therefore give the
written evolution bounds without a smooth-density or approximation premise.
-/
public section
namespace CutoffRigidity
open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal NNReal
variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

theorem langevinKernel_entropy_contraction
    {B : NNReal → Ω → E} {P : Measure Ω} (hB : IsEuclideanBrownian B P)
    {V : E → ℝ} (hV : ContDiff ℝ 2 V) (hp : IsProbabilityMeasure (gibbsMeasure volume V))
    (hdim : 0 < d) (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (ν : Measure E) [IsProbabilityMeasure ν] (T : ℝ) (hT : 0 ≤ T) :
    klDiv (langevinKernel V B P T.toNNReal ∘ₘ ν) (gibbsMeasure volume V) ≤
      ENNReal.ofReal (Real.exp (-2 * ρ * T)) * klDiv ν (gibbsMeasure volume V) := by
  let := hp
  by_cases hfin : klDiv ν (gibbsMeasure volume V) ≠ ⊤
  · have hAC := (klDiv_ne_top_iff.mp hfin).1
    obtain ⟨c,g,hg,hgc,hc,hFloor,hNorm,hL1,hKL⟩ :=
      exists_finite_entropy_probability_core_L1_KL_approx (gibbsMeasure volume V) ν hAC hfin
    exact langevinKernel_entropy_contraction_of_core_approx hB hV hp ρ hρ hHess ν hAC
      c g hg hgc hc hFloor hNorm hL1 hKL hdim T hT
  · have hh : klDiv ν (gibbsMeasure volume V) = ⊤ := not_ne_iff.mp hfin
    rw [hh, ENNReal.mul_top (ENNReal.ofReal_ne_zero_iff.mpr (Real.exp_pos _))]
    exact le_top

theorem langevinKernel_fisher_entropy_endpoint
    {B : NNReal → Ω → E} {P : Measure Ω} (hB : IsEuclideanBrownian B P)
    {V : E → ℝ} (hV : ContDiff ℝ 2 V) (hp : IsProbabilityMeasure (gibbsMeasure volume V))
    (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (ν : Measure E) [IsProbabilityMeasure ν] (T : ℝ) (hT : 0 < T) :
    letI := langevinKernel_isMarkovKernel hB hV ρ hρ.le hHess T.toNNReal
    relativeFisherInformation hV hp (langevinKernel V B P T.toNNReal ∘ₘ ν) ≤
      klDiv ν (gibbsMeasure volume V) / ENNReal.ofReal T := by
  let := hp
  by_cases hfin : klDiv ν (gibbsMeasure volume V) ≠ ⊤
  · have hAC := (klDiv_ne_top_iff.mp hfin).1
    obtain ⟨c,g,hg,hgc,hc,hFloor,hNorm,hL1,hKL⟩ :=
      exists_finite_entropy_probability_core_L1_KL_approx (gibbsMeasure volume V) ν hAC hfin
    exact langevinKernel_fisher_entropy_endpoint_of_core_approx hB hV hp ρ hρ hHess ν hAC
      c g hg hgc hc hFloor hNorm hL1 hKL T hT
  · have hh : klDiv ν (gibbsMeasure volume V) = ⊤ := not_ne_iff.mp hfin
    simp only [hh, ENNReal.top_div_of_ne_top ENNReal.ofReal_ne_top]
    exact le_top

/-- Entropy contraction after an arbitrary actual positive-time evolution. -/
theorem langevinKernel_entropy_contraction_add
    {B : NNReal → Ω → E} {P : Measure Ω} (hB : IsEuclideanBrownian B P)
    {V : E → ℝ} (hV : ContDiff ℝ 2 V) (hp : IsProbabilityMeasure (gibbsMeasure volume V))
    (hdim : 0 < d) (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (ν : Measure E) [IsProbabilityMeasure ν] (s t : NNReal) :
    klDiv (langevinKernel V B P (s+t) ∘ₘ ν) (gibbsMeasure volume V) ≤
      ENNReal.ofReal (Real.exp (-2 * ρ * t)) *
        klDiv (langevinKernel V B P s ∘ₘ ν) (gibbsMeasure volume V) := by
  let := langevinKernel_isMarkovKernel hB hV ρ hρ.le hHess s
  have hh := langevinKernel_entropy_contraction hB hV hp hdim ρ hρ hHess
    (langevinKernel V B P s ∘ₘ ν) t t.property
  have he : (t : ℝ).toNNReal = t := @Real.toNNReal_coe t
  simpa only [he, Measure.comp_assoc, langevinKernel_comp hB hV ρ hρ.le hHess] using hh

/-- The written Fisher entropy endpoint after any actual earlier evolution. -/
theorem langevinKernel_fisher_entropy_endpoint_add
    {B : NNReal → Ω → E} {P : Measure Ω} (hB : IsEuclideanBrownian B P)
    {V : E → ℝ} (hV : ContDiff ℝ 2 V) (hp : IsProbabilityMeasure (gibbsMeasure volume V))
    (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (ν : Measure E) [IsProbabilityMeasure ν] (s t : NNReal) (ht : 0 < t) :
    letI := langevinKernel_isMarkovKernel hB hV ρ hρ.le hHess (s+t)
    relativeFisherInformation hV hp (langevinKernel V B P (s+t) ∘ₘ ν) ≤
      klDiv (langevinKernel V B P s ∘ₘ ν) (gibbsMeasure volume V) / ENNReal.ofReal t := by
  let := langevinKernel_isMarkovKernel hB hV ρ hρ.le hHess s
  have hh := langevinKernel_fisher_entropy_endpoint hB hV hp ρ hρ hHess
    (langevinKernel V B P s ∘ₘ ν) t ht
  have he : (t : ℝ).toNNReal = t := @Real.toNNReal_coe t
  simpa only [he, Measure.comp_assoc, langevinKernel_comp hB hV ρ hρ.le hHess] using hh

end CutoffRigidity
