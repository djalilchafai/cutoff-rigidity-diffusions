module

public import CutoffRigidity.RelativeFisherInformation
public import CutoffRigidity.GibbsSobolevC1
public import Mathlib.Analysis.SpecialFunctions.Sqrt

/-! # Canonical Fisher information of genuine positive C¹ densities

The square root of the actual RN density is placed in the actual closed
Gibbs gradient graph using the proved C¹ domain theorem. No C² density or
supplied Fisher formula is required. Uniform convexity is used precisely
through that closed-domain theorem.
-/

public section

namespace CutoffRigidity

open MeasureTheory

variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

/-- The C¹ representative version of the canonical closed Fisher identity. -/
theorem relativeFisherInformation_eq_of_c1_squareRoot {V g : E → ℝ}
    (hV : ContDiff ℝ 2 V) (hprob : IsProbabilityMeasure (gibbsMeasure volume V))
    (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (ν : Measure E) [IsFiniteMeasure ν] (hν : ν ≪ gibbsMeasure volume V)
    (hg : ContDiff ℝ 1 g)
    (hRN : squareRootRNDensity ν (gibbsMeasure volume V) =ᵐ[gibbsMeasure volume V] g)
    (hgrad : MemLp (gradient g) 2 (gibbsMeasure volume V)) :
    relativeFisherInformation hV hprob ν =
      ENNReal.ofReal (4 * ∫ x, ‖gradient g x‖ ^ 2 ∂gibbsMeasure volume V) := by
  have hglp : MemLp g 2 (gibbsMeasure volume V) :=
    (memLp_congr_ae hRN).mp (squareRootRNDensity_memLp ν (gibbsMeasure volume V))
  have heq : squareRootRNDensityLp ν (gibbsMeasure volume V) = hglp.toLp g :=
    MemLp.toLp_congr _ _ hRN
  let G := closedGibbsGradient hV hprob
  have hgraph : (hglp.toLp g, hgrad.toLp (gradient g)) ∈ G.graph :=
    c1_function_mem_closedGibbsGradient_graph hV hprob ρ hρ hHess hg hglp hgrad
  rw [← heq] at hgraph
  have hD := G.mem_domain_of_mem_graph hgraph
  have hval : G ⟨squareRootRNDensityLp ν (gibbsMeasure volume V), hD⟩ =
      hgrad.toLp (gradient g) := (G.image_iff hD).mpr hgraph |>.symm
  rw [relativeFisherInformation_eq_closed_energy hV hprob ν hν hD, hval]
  congr 2
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hgrad.coeFn_toLp] with x hx
  rw [hx, real_inner_self_eq_norm_sq]

/-- The genuine RN square root of a nonnegative actual density. -/
theorem squareRootRNDensity_withDensity_ofReal {μ : Measure E} [SigmaFinite μ]
    {f : E → ℝ} (hf : Measurable f) (hn : ∀ x, 0 ≤ f x) :
    squareRootRNDensity (μ.withDensity (fun x => ENNReal.ofReal (f x))) μ =ᵐ[μ]
      fun x => Real.sqrt (f x) := by
  filter_upwards [Measure.rnDeriv_withDensity μ hf.ennreal_ofReal] with x hx
  change Real.sqrt ((_ : ENNReal).toReal) = _
  rw [hx, ENNReal.toReal_ofReal (hn x)]

/-- Actual square-root chain rule at exactly C¹ regularity. -/
theorem gradient_sqrt_positive {f : E → ℝ} (hf : Differentiable ℝ f)
    (hpos : ∀ x, 0 < f x) (x : E) :
    gradient (fun y => Real.sqrt (f y)) x =
      (1 / (2 * Real.sqrt (f x))) • gradient f x := by
  apply ext_inner_right ℝ
  intro z
  rw [inner_gradient_left, fderiv_sqrt (hf x) (hpos x).ne',
    real_inner_smul_left, inner_gradient_left]
  simp only [smul_apply, smul_eq_mul]

private theorem norm_gradient_sqrt_sq {f : E → ℝ} (hf : Differentiable ℝ f)
    (hpos : ∀ x, 0 < f x) (x : E) :
    ‖gradient (fun y => Real.sqrt (f y)) x‖ ^ 2 =
      (1 / 4 : ℝ) * (‖gradient f x‖ ^ 2 / f x) := by
  rw [gradient_sqrt_positive hf hpos x, norm_smul, Real.norm_eq_abs, mul_pow,
    sq_abs, div_pow, one_pow, mul_pow, Real.sq_sqrt (hpos x).le]
  field_simp
  ring

/-- The canonical extended Fisher information equals the actual weighted
energy for a normalized positive C¹ density, on its explicit integrable
score domain. The law is genuinely constructed with `withDensity`. -/
theorem relativeFisherInformation_withDensity_c1 {V f : E → ℝ}
    (hV : ContDiff ℝ 2 V) (hprob : IsProbabilityMeasure (gibbsMeasure volume V))
    (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (hf : ContDiff ℝ 1 f) (hpos : ∀ x, 0 < f x)
    (hνprob : IsProbabilityMeasure
      ((gibbsMeasure volume V).withDensity (fun x => ENNReal.ofReal (f x))))
    (hI : Integrable (fun x => ‖gradient f x‖ ^ 2 / f x) (gibbsMeasure volume V)) :
    letI := hνprob
    relativeFisherInformation hV hprob
      ((gibbsMeasure volume V).withDensity (fun x => ENNReal.ofReal (f x))) =
        ENNReal.ofReal (∫ x, ‖gradient f x‖ ^ 2 / f x ∂gibbsMeasure volume V) := by
  let := hprob
  let := hνprob
  have hs : ContDiff ℝ 1 (fun x => Real.sqrt (f x)) := hf.sqrt (fun x => (hpos x).ne')
  have hgrad : MemLp (gradient (fun x => Real.sqrt (f x))) 2 (gibbsMeasure volume V) := by
    apply (memLp_two_iff_integrable_sq_norm (continuous_gradient_of_c1 hs).aestronglyMeasurable).mpr
    change Integrable (fun x => ‖gradient (fun y => Real.sqrt (f y)) x‖ ^ 2) (gibbsMeasure volume V)
    simpa only [norm_gradient_sqrt_sq (hf.differentiable one_ne_zero) hpos] using hI.const_mul (1 / 4 : ℝ)
  rw [relativeFisherInformation_eq_of_c1_squareRoot hV hprob ρ hρ hHess _
    (withDensity_absolutelyContinuous _ _) hs
    (squareRootRNDensity_withDensity_ofReal hf.continuous.measurable (fun x => (hpos x).le)) hgrad]
  simp only [norm_gradient_sqrt_sq (hf.differentiable one_ne_zero) hpos, integral_const_mul]
  congr 1
  ring

/-- A positive lower bound and the actual L² gradient supply the score
integrability; bounded C¹ gradients under probability laws are a special case. -/
theorem integrable_weighted_gradient_of_memLp {μ : Measure E} {f : E → ℝ}
    (hf : ContDiff ℝ 1 f) {m : ℝ} (hm : 0 < m) (hlow : ∀ x, m ≤ f x)
    (hgrad : MemLp (gradient f) 2 μ) :
    Integrable (fun x => ‖gradient f x‖ ^ 2 / f x) μ := by
  have hgc := continuous_gradient_of_c1 hf
  have hpos (x : E) : 0 < f x := hm.trans_le (hlow x)
  have hc : Continuous (fun x => ‖gradient f x‖ ^ 2 / f x) :=
    (hgc.norm.pow 2).div hf.continuous (fun x => (hpos x).ne')
  apply (hgrad.norm.integrable_sq.mul_const m⁻¹).mono' hc.aestronglyMeasurable
  filter_upwards with x
  rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (sq_nonneg _) (hpos x).le)]
  simpa only [Pi.mul_apply, div_eq_mul_inv] using
    (div_le_div_of_nonneg_left (sq_nonneg ‖gradient f x‖) hm (hlow x))

/-- Exact canonical Fisher information on normalized C¹ densities with a
positive lower bound and an actual L² gradient. No density upper bound or
C² density premise is necessary. -/
theorem relativeFisherInformation_withDensity_c1_of_memLp {V f : E → ℝ}
    (hV : ContDiff ℝ 2 V) (hprob : IsProbabilityMeasure (gibbsMeasure volume V))
    (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (hf : ContDiff ℝ 1 f) (m : ℝ) (hm : 0 < m) (hlow : ∀ x, m ≤ f x)
    (hνprob : IsProbabilityMeasure
      ((gibbsMeasure volume V).withDensity (fun x => ENNReal.ofReal (f x))))
    (hgrad : MemLp (gradient f) 2 (gibbsMeasure volume V)) :
    letI := hνprob
    relativeFisherInformation hV hprob
      ((gibbsMeasure volume V).withDensity (fun x => ENNReal.ofReal (f x))) =
        ENNReal.ofReal (∫ x, ‖gradient f x‖ ^ 2 / f x ∂gibbsMeasure volume V) :=
  relativeFisherInformation_withDensity_c1 hV hprob ρ hρ hHess hf
    (fun x => hm.trans_le (hlow x)) hνprob
    (integrable_weighted_gradient_of_memLp hf hm hlow hgrad)

/-- The actual RN square root belongs to the canonical closed Sobolev
domain on the C¹ score-integrability domain. -/
theorem c1_density_squareRoot_mem_closed_domain {V f : E → ℝ}
    (hV : ContDiff ℝ 2 V) (hprob : IsProbabilityMeasure (gibbsMeasure volume V))
    (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (hf : ContDiff ℝ 1 f) (hpos : ∀ x, 0 < f x)
    (hνprob : IsProbabilityMeasure
      ((gibbsMeasure volume V).withDensity (fun x => ENNReal.ofReal (f x))))
    (hI : Integrable (fun x => ‖gradient f x‖ ^ 2 / f x) (gibbsMeasure volume V)) :
    letI := hνprob
    squareRootRNDensityLp
      ((gibbsMeasure volume V).withDensity (fun x => ENNReal.ofReal (f x)))
      (gibbsMeasure volume V) ∈ (closedGibbsGradient hV hprob).domain := by
  let := hprob
  let := hνprob
  let ν := (gibbsMeasure volume V).withDensity (fun x => ENNReal.ofReal (f x))
  let g := fun x => Real.sqrt (f x)
  have hs : ContDiff ℝ 1 g := hf.sqrt (fun x => (hpos x).ne')
  have hRN := squareRootRNDensity_withDensity_ofReal (μ := gibbsMeasure volume V)
    hf.continuous.measurable (fun x => (hpos x).le)
  have hgLp : MemLp g 2 (gibbsMeasure volume V) :=
    (memLp_congr_ae hRN).mp (squareRootRNDensity_memLp ν _)
  have hgrad : MemLp (gradient g) 2 (gibbsMeasure volume V) := by
    change MemLp (gradient (fun x => Real.sqrt (f x))) 2 (gibbsMeasure volume V)
    apply (memLp_two_iff_integrable_sq_norm (continuous_gradient_of_c1 hs).aestronglyMeasurable).mpr
    change Integrable (fun x => ‖gradient (fun y => Real.sqrt (f y)) x‖ ^ 2) (gibbsMeasure volume V)
    simpa only [norm_gradient_sqrt_sq (hf.differentiable one_ne_zero) hpos] using hI.const_mul (1 / 4 : ℝ)
  have hgraph := c1_function_mem_closedGibbsGradient_graph hV hprob ρ hρ hHess hs hgLp hgrad
  have heq : squareRootRNDensityLp ν (gibbsMeasure volume V) = hgLp.toLp g :=
    MemLp.toLp_congr _ _ hRN
  rw [← heq] at hgraph
  exact (closedGibbsGradient hV hprob).mem_domain_of_mem_graph hgraph

/-- Real-valued identity and finiteness for the actual C¹ density Fisher
functional, with no use of `toReal` at an infinite information value. -/
theorem relativeFisherInformation_toReal_withDensity_c1 {V f : E → ℝ}
    (hV : ContDiff ℝ 2 V) (hprob : IsProbabilityMeasure (gibbsMeasure volume V))
    (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (hf : ContDiff ℝ 1 f) (hpos : ∀ x, 0 < f x)
    (hνprob : IsProbabilityMeasure
      ((gibbsMeasure volume V).withDensity (fun x => ENNReal.ofReal (f x))))
    (hI : Integrable (fun x => ‖gradient f x‖ ^ 2 / f x) (gibbsMeasure volume V)) :
    letI := hνprob
    (relativeFisherInformation hV hprob
      ((gibbsMeasure volume V).withDensity (fun x => ENNReal.ofReal (f x)))).toReal =
        ∫ x, ‖gradient f x‖ ^ 2 / f x ∂gibbsMeasure volume V := by
  let := hνprob
  rw [relativeFisherInformation_withDensity_c1 hV hprob ρ hρ hHess hf hpos hνprob hI,
    ENNReal.toReal_ofReal (integral_nonneg (fun x => div_nonneg (sq_nonneg _) (hpos x).le))]

end CutoffRigidity
