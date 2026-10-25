module

public import CutoffRigidity.RelativeFisherInformation
public import CutoffRigidity.SalezEntropyWindow
public import CutoffRigidity.FisherDissipation

/-! # Smooth exponential densities and actual relative Fisher information

The extended closed-gradient functional is identified with the genuine score
integral for an actual normalized exponential density. No heat-flow density
regularity or curvature-to-local-Poincaré assertion is made here.
-/

public section

namespace CutoffRigidity

open MeasureTheory ProbabilityTheory InformationTheory Filter

variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

/-- The actual exponential density law, with normalization stated explicitly
by a probability-measure hypothesis in the theorems below. -/
@[expose] noncomputable def exponentialDensityMeasure (μ : Measure E) (u : E → ℝ) : Measure E :=
  μ.withDensity (fun x => ENNReal.ofReal (Real.exp (u x)))

private theorem exp_half_sq (s : ℝ) : Real.exp (s / 2) ^ 2 = Real.exp s := by
  rw [pow_two, ← Real.exp_add]
  congr 1
  ring

/-- The actual square-root RN density is the classical exponential half
representative, almost everywhere under the actual reference law. -/
theorem squareRootRNDensity_exponential {μ : Measure E} [SigmaFinite μ]
    {u : E → ℝ} (hu : Measurable u) :
    squareRootRNDensity (exponentialDensityMeasure μ u) μ =ᵐ[μ]
      fun x => Real.exp (u x / 2) := by
  filter_upwards [Measure.rnDeriv_withDensity μ hu.exp.ennreal_ofReal] with x hx
  change (exponentialDensityMeasure μ u).rnDeriv μ x = _ at hx
  change Real.sqrt ((_ : ENNReal).toReal) = _
  rw [hx, ENNReal.toReal_ofReal (Real.exp_nonneg _), ← exp_half_sq (u x),
    Real.sqrt_sq (Real.exp_nonneg _)]

/-- The RN information content of the actual exponential density law is
its stated smooth logarithm, almost everywhere under both laws. -/
theorem llr_exponentialDensityMeasure {μ : Measure E} [SigmaFinite μ]
    {u : E → ℝ} (hu : Measurable u) :
    llr (exponentialDensityMeasure μ u) μ =ᵐ[μ] u := by
  filter_upwards [Measure.rnDeriv_withDensity μ hu.exp.ennreal_ofReal] with x hx
  change (exponentialDensityMeasure μ u).rnDeriv μ x = _ at hx
  rw [llr, hx, ENNReal.toReal_ofReal (Real.exp_nonneg _), Real.log_exp]

theorem llr_exponentialDensityMeasure_selfAE {μ : Measure E} [SigmaFinite μ]
    {u : E → ℝ} (hu : Measurable u) :
    llr (exponentialDensityMeasure μ u) μ =ᵐ[exponentialDensityMeasure μ u] u :=
  (withDensity_absolutelyContinuous _ _).ae_eq (llr_exponentialDensityMeasure hu)

/-- The actual classical gradient of the square-root density. -/
theorem gradient_exp_half {u : E → ℝ} (hu : Differentiable ℝ u) (x : E) :
    gradient (fun y => Real.exp (u y / 2)) x =
      (Real.exp (u x / 2) / 2) • gradient u x := by
  apply ext_inner_right ℝ
  intro z
  have hd := (((hu x).hasFDerivAt.const_mul (1 / 2 : ℝ)).exp).fderiv
  have hd' : fderiv ℝ (fun y => Real.exp (u y / 2)) x =
      Real.exp (u x / 2) • ((1 / 2 : ℝ) • fderiv ℝ u x) := by
    convert! hd using 1 <;> simp only [div_eq_mul_inv, one_mul, mul_comm]
  rw [inner_gradient_left, hd',
    real_inner_smul_left, inner_gradient_left]
  simp only [smul_apply, smul_eq_mul]
  ring

private theorem norm_gradient_exp_half_sq {u : E → ℝ} (hu : Differentiable ℝ u) (x : E) :
    ‖gradient (fun y => Real.exp (u y / 2)) x‖ ^ 2 =
      (1 / 4 : ℝ) * (Real.exp (u x) * ‖gradient u x‖ ^ 2) := by
  rw [gradient_exp_half hu x, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (div_nonneg (Real.exp_nonneg _) (by norm_num)), mul_pow, div_pow, exp_half_sq]
  ring

/-- Actual integrability of the score under the density law supplies the
L² gradient needed for membership in the canonical closed energy domain. -/
theorem memLp_gradient_exp_half {μ : Measure E} {u : E → ℝ} (hu : ContDiff ℝ 2 u)
    (hI : Integrable (fun x => ‖gradient u x‖ ^ 2) (exponentialDensityMeasure μ u)) :
    MemLp (gradient (fun x => Real.exp (u x / 2))) 2 μ := by
  have hm := hu.continuous.measurable.exp.ennreal_ofReal
  have hw : Integrable (fun x => Real.exp (u x) * ‖gradient u x‖ ^ 2) μ := by
    have hh := (integrable_withDensity_iff_integrable_smul' hm (by simp)).mp hI
    simpa only [ENNReal.toReal_ofReal (Real.exp_nonneg _), smul_eq_mul] using hh
  have hg : ContDiff ℝ 2 (fun x => Real.exp (u x / 2)) := (hu.div_const 2).exp
  apply (memLp_two_iff_integrable_sq_norm
    (continuous_gradient_of_c1 (hg.of_le (by norm_num))).aestronglyMeasurable).mpr
  simpa only [norm_gradient_exp_half_sq (hu.differentiable (by norm_num))] using hw.const_mul (1 / 4 : ℝ)

/-- Genuine Fisher information equals the actual score integral for an
actual normalized C² exponential density. -/
theorem relativeFisherInformation_exponential {V u : E → ℝ}
    (hV : ContDiff ℝ 2 V) (hprob : IsProbabilityMeasure (gibbsMeasure volume V))
    (hu : ContDiff ℝ 2 u)
    (hνprob : IsProbabilityMeasure (exponentialDensityMeasure (gibbsMeasure volume V) u))
    (hI : Integrable (fun x => ‖gradient u x‖ ^ 2)
      (exponentialDensityMeasure (gibbsMeasure volume V) u)) :
    relativeFisherInformation hV hprob (exponentialDensityMeasure (gibbsMeasure volume V) u) =
      ENNReal.ofReal (∫ x, ‖gradient u x‖ ^ 2
        ∂exponentialDensityMeasure (gibbsMeasure volume V) u) := by
  let := hprob
  let := hνprob
  have hAC : exponentialDensityMeasure (gibbsMeasure volume V) u ≪ gibbsMeasure volume V :=
    withDensity_absolutelyContinuous _ _
  rw [relativeFisherInformation_eq_of_c2_squareRoot hV hprob _
    hAC (hu.div_const 2).exp
    (squareRootRNDensity_exponential hu.continuous.measurable) (memLp_gradient_exp_half hu hI)]
  congr 1
  rw [show (fun x => ‖gradient (fun y => Real.exp (u y / 2)) x‖ ^ 2) =
    (fun x => (1 / 4 : ℝ) * (Real.exp (u x) * ‖gradient u x‖ ^ 2)) from
      funext (norm_gradient_exp_half_sq (hu.differentiable (by norm_num))), integral_const_mul]
  rw [exponentialDensityMeasure, integral_withDensity_eq_integral_toReal_smul
    hu.continuous.measurable.exp.ennreal_ofReal (by simp)]
  simp only [ENNReal.toReal_ofReal (Real.exp_nonneg _), smul_eq_mul]
  ring

/-- Actual C² half-density membership in the closed Gibbs H¹ graph,
with inclusion equal to the canonical RN square-root L² class. -/
theorem exponential_squareRoot_mem_closed_domain {V u : E → ℝ}
    (hV : ContDiff ℝ 2 V) (hprob : IsProbabilityMeasure (gibbsMeasure volume V))
    (hu : ContDiff ℝ 2 u)
    (hνprob : IsProbabilityMeasure (exponentialDensityMeasure (gibbsMeasure volume V) u))
    (hI : Integrable (fun x => ‖gradient u x‖ ^ 2)
      (exponentialDensityMeasure (gibbsMeasure volume V) u)) :
    letI := hνprob
    squareRootRNDensityLp (exponentialDensityMeasure (gibbsMeasure volume V) u)
      (gibbsMeasure volume V) ∈ (closedGibbsGradient hV hprob).domain := by
  let := hνprob
  let := hprob
  let ν := exponentialDensityMeasure (gibbsMeasure volume V) u
  let g := fun x => Real.exp (u x / 2)
  have hRN := squareRootRNDensity_exponential (μ := gibbsMeasure volume V) hu.continuous.measurable
  have hgLp : MemLp g 2 (gibbsMeasure volume V) :=
    (memLp_congr_ae hRN).mp (squareRootRNDensity_memLp ν _)
  have hggrad := memLp_gradient_exp_half hu hI
  have hgraph := c2_function_mem_closedGibbsGradient_graph hV hprob
    (hu.div_const 2).exp hgLp hggrad
  have heq : squareRootRNDensityLp ν (gibbsMeasure volume V) = hgLp.toLp g :=
    MemLp.toLp_congr _ _ hRN
  rw [← heq] at hgraph
  exact (closedGibbsGradient hV hprob).mem_domain_of_mem_graph hgraph

/-- Actual entropy for the exponential density, with information-content
integrability explicit. The formula retains genuine ENNReal KL. -/
theorem klDiv_exponentialDensityMeasure {μ : Measure E} [IsProbabilityMeasure μ]
    {u : E → ℝ} (hu : Measurable u)
    (hνprob : IsProbabilityMeasure (exponentialDensityMeasure μ u))
    (hInt : Integrable u (exponentialDensityMeasure μ u)) :
    klDiv (exponentialDensityMeasure μ u) μ =
      ENNReal.ofReal (∫ x, u x ∂exponentialDensityMeasure μ u) := by
  let := hνprob
  have hAE := llr_exponentialDensityMeasure_selfAE (μ := μ) hu
  have hLLR : Integrable (llr (exponentialDensityMeasure μ u) μ)
      (exponentialDensityMeasure μ u) := hInt.congr hAE.symm
  have hAC : exponentialDensityMeasure μ u ≪ μ := withDensity_absolutelyContinuous _ _
  rw [klDiv_of_ac_of_integrable hAC hLLR,
    integral_congr_ae hAE]
  simp

/-- Genuine local Poincaré on the actual smooth logarithmic density yields
an estimate on actual varentropy by the actual closed Fisher functional. -/
theorem varentropy_exponential_le_relativeFisherInformation {V u : E → ℝ}
    (hV : ContDiff ℝ 2 V) (hprob : IsProbabilityMeasure (gibbsMeasure volume V))
    (hu : ContDiff ℝ 2 u)
    (hνprob : IsProbabilityMeasure (exponentialDensityMeasure (gibbsMeasure volume V) u))
    (hI : Integrable (fun x => ‖gradient u x‖ ^ 2)
      (exponentialDensityMeasure (gibbsMeasure volume V) u))
    (hL2 : MemLp u 2 (exponentialDensityMeasure (gibbsMeasure volume V) u))
    (C : ℝ) (hC : 0 ≤ C)
    (hP : HasLocalSmoothPoincare (exponentialDensityMeasure (gibbsMeasure volume V) u) C) :
    varentropy (exponentialDensityMeasure (gibbsMeasure volume V) u) (gibbsMeasure volume V) ≤
      ENNReal.ofReal C * relativeFisherInformation hV hprob
        (exponentialDensityMeasure (gibbsMeasure volume V) u) := by
  let := hprob
  let := hνprob
  have hAE := llr_exponentialDensityMeasure_selfAE
    (μ := gibbsMeasure volume V) hu.continuous.measurable
  have hvar : varentropy (exponentialDensityMeasure (gibbsMeasure volume V) u)
      (gibbsMeasure volume V) = ENNReal.ofReal
        (variance u (exponentialDensityMeasure (gibbsMeasure volume V) u)) := by
    rw [varentropy, evariance_congr hAE, ← hL2.ofReal_variance_eq]
  rw [hvar, relativeFisherInformation_exponential hV hprob hu hνprob hI,
    ← ENNReal.ofReal_mul hC]
  exact ENNReal.ofReal_le_ofReal (hP u (hu.of_le (by norm_num)) hL2 hI)

/-- The actual canonical Fisher value is finite on the smooth score
integrability domain; its real value is the actual score integral. -/
theorem relativeFisherInformation_toReal_exponential {V u : E → ℝ}
    (hV : ContDiff ℝ 2 V) (hprob : IsProbabilityMeasure (gibbsMeasure volume V))
    (hu : ContDiff ℝ 2 u)
    (hνprob : IsProbabilityMeasure (exponentialDensityMeasure (gibbsMeasure volume V) u))
    (hI : Integrable (fun x => ‖gradient u x‖ ^ 2)
      (exponentialDensityMeasure (gibbsMeasure volume V) u)) :
    (relativeFisherInformation hV hprob (exponentialDensityMeasure (gibbsMeasure volume V) u)).toReal =
      ∫ x, ‖gradient u x‖ ^ 2 ∂exponentialDensityMeasure (gibbsMeasure volume V) u := by
  rw [relativeFisherInformation_exponential hV hprob hu hνprob hI,
    ENNReal.toReal_ofReal (integral_nonneg (fun _ => sq_nonneg _))]

/-- The real-valued local information inequality with genuine canonical
Fisher information, ready for the actual entropy-dissipation comparison. -/
theorem varentropy_toReal_exponential_le_relativeFisherInformation {V u : E → ℝ}
    (hV : ContDiff ℝ 2 V) (hprob : IsProbabilityMeasure (gibbsMeasure volume V))
    (hu : ContDiff ℝ 2 u)
    (hνprob : IsProbabilityMeasure (exponentialDensityMeasure (gibbsMeasure volume V) u))
    (hI : Integrable (fun x => ‖gradient u x‖ ^ 2)
      (exponentialDensityMeasure (gibbsMeasure volume V) u))
    (hL2 : MemLp u 2 (exponentialDensityMeasure (gibbsMeasure volume V) u))
    (C : ℝ)
    (hP : HasLocalSmoothPoincare (exponentialDensityMeasure (gibbsMeasure volume V) u) C) :
    (varentropy (exponentialDensityMeasure (gibbsMeasure volume V) u) (gibbsMeasure volume V)).toReal ≤
      C * (relativeFisherInformation hV hprob
        (exponentialDensityMeasure (gibbsMeasure volume V) u)).toReal := by
  let := hprob
  let := hνprob
  rw [relativeFisherInformation_toReal_exponential hV hprob hu hνprob hI]
  have hAE := llr_exponentialDensityMeasure_selfAE
    (μ := gibbsMeasure volume V) hu.continuous.measurable
  have heq : (varentropy (exponentialDensityMeasure (gibbsMeasure volume V) u)
      (gibbsMeasure volume V)).toReal =
      variance u (exponentialDensityMeasure (gibbsMeasure volume V) u) := by
    exact variance_congr hAE
  rw [heq]
  exact hP u (hu.of_le (by norm_num)) hL2 hI

end CutoffRigidity
