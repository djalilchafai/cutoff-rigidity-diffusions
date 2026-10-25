module

public import CutoffRigidity.SmoothFisherInformation
public import CutoffRigidity.EntropyDissipation
public import CutoffRigidity.DissipationBounds

/-! # Genuine information evolution on an explicit smooth PDE domain

These are analytic-domain consequences of the actual density and mixed
gradient PDEs. The hypotheses contain raw regularity, integration-by-parts,
and dominated differentiation obligations, not information decay estimates.
Canonical Langevin heat-density regularity is a separate unproved bridge.
-/

public section

namespace CutoffRigidity

open MeasureTheory Filter Topology Set InformationTheory

variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

/-- The raw smooth density evolution domain. Every bound below is an
ordinary dominating function for actual PDE integrands. -/
structure SmoothInformationEvolutionDomain (V : E → ℝ) (u : ℝ → E → ℝ) (t₀ : ℝ) where
  neighborhood : Set ℝ
  nhds : neighborhood ∈ 𝓝 t₀
  spatial : ∀ t ∈ neighborhood, ContDiff ℝ 2 (u t)
  spatial₀ : ContDiff ℝ 3 (u t₀)
  probability : ∀ t ∈ neighborhood,
    IsProbabilityMeasure (exponentialDensityMeasure (gibbsMeasure volume V) (u t))
  entropyIntegrable : ∀ t ∈ neighborhood, Integrable
    (fun x => Real.exp (u t x) * u t x) (gibbsMeasure volume V)
  scoreIntegrable : ∀ t ∈ neighborhood, Integrable
    (fun x => Real.exp (u t x) * ‖gradient (u t) x‖ ^ 2) (gibbsMeasure volume V)
  entropyIBP : EntropyIntegrationDomain V (fun x => Real.exp (u t₀ x))
  fisherIBP : FisherIntegrationDomain V (u t₀)
  densityPDE : ∀ᵐ x ∂gibbsMeasure volume V, ∀ t ∈ neighborhood,
    HasDerivAt (fun r => Real.exp (u r x))
      (langevinDifferentialOperator V (fun y => Real.exp (u t y)) x) t
  gradientPDE : ∀ᵐ x ∂gibbsMeasure volume V, ∀ t ∈ neighborhood,
    HasDerivAt (fun r => gradient (u r) x)
      (gradient (langevinDifferentialOperator (fun y => V y - u t y) (u t)) x) t
  entropyDerivativeMeasurable : AEStronglyMeasurable
    (fun x => (1 + u t₀ x) * langevinDifferentialOperator V (fun y => Real.exp (u t₀ y)) x)
    (gibbsMeasure volume V)
  fisherDerivativeMeasurable : AEStronglyMeasurable (fisherVariationIntegrand V (u t₀))
    (gibbsMeasure volume V)
  entropyBound : E → ℝ
  entropyDominated : ∀ᵐ x ∂gibbsMeasure volume V, ∀ t ∈ neighborhood,
    ‖(1 + u t x) * langevinDifferentialOperator V (fun y => Real.exp (u t y)) x‖ ≤ entropyBound x
  entropyBoundIntegrable : Integrable entropyBound (gibbsMeasure volume V)
  fisherBound : E → ℝ
  fisherDominated : ∀ᵐ x ∂gibbsMeasure volume V, ∀ t ∈ neighborhood,
    ‖fisherVariationIntegrand V (u t) x‖ ≤ fisherBound x
  fisherBoundIntegrable : Integrable fisherBound (gibbsMeasure volume V)

private theorem score_integrable_exponential {μ : Measure E} {u : E → ℝ}
    (hu : Measurable u) (hI : Integrable (fun x => Real.exp (u x) * ‖gradient u x‖ ^ 2) μ) :
    Integrable (fun x => ‖gradient u x‖ ^ 2) (exponentialDensityMeasure μ u) := by
  apply (integrable_withDensity_iff_integrable_smul' hu.exp.ennreal_ofReal (by simp)).mpr
  simpa only [ENNReal.toReal_ofReal (Real.exp_nonneg _), smul_eq_mul] using hI

/-- Actual canonical Fisher information is the weighted score integral on
the explicit smooth normalized-density domain. -/
theorem relativeFisherInformation_toReal_eq_weighted_score {V u : E → ℝ}
    (hV : ContDiff ℝ 2 V) (hprob : IsProbabilityMeasure (gibbsMeasure volume V))
    (hu : ContDiff ℝ 2 u)
    (hνprob : IsProbabilityMeasure (exponentialDensityMeasure (gibbsMeasure volume V) u))
    (hI : Integrable (fun x => Real.exp (u x) * ‖gradient u x‖ ^ 2) (gibbsMeasure volume V)) :
    (relativeFisherInformation hV hprob (exponentialDensityMeasure (gibbsMeasure volume V) u)).toReal =
      ∫ x, Real.exp (u x) * ‖gradient u x‖ ^ 2 ∂gibbsMeasure volume V := by
  rw [relativeFisherInformation_toReal_exponential hV hprob hu hνprob
    (score_integrable_exponential hu.continuous.measurable hI), exponentialDensityMeasure,
    integral_withDensity_eq_integral_toReal_smul hu.continuous.measurable.exp.ennreal_ofReal (by simp)]
  simp only [ENNReal.toReal_ofReal (Real.exp_nonneg _), smul_eq_mul]

private theorem klDiv_toReal_exponential_weighted {μ : Measure E} [IsProbabilityMeasure μ]
    {u : E → ℝ} (hu : Measurable u)
    (hνprob : IsProbabilityMeasure (exponentialDensityMeasure μ u)) :
    (klDiv (exponentialDensityMeasure μ u) μ).toReal = ∫ x, Real.exp (u x) * u x ∂μ := by
  let := hνprob
  have hAC : exponentialDensityMeasure μ u ≪ μ := withDensity_absolutelyContinuous _ _
  rw [klDiv_toReal_eq_mean_llr _ _ hAC,
    integral_congr_ae (llr_exponentialDensityMeasure_selfAE hu), exponentialDensityMeasure,
    integral_withDensity_eq_integral_toReal_smul hu.exp.ennreal_ofReal (by simp)]
  simp only [ENNReal.toReal_ofReal (Real.exp_nonneg _), smul_eq_mul]

/-- The actual KL derivative equals minus the actual canonical Fisher
information, derived from the density PDE and raw entropy IBP domain. -/
theorem hasDerivAt_klDiv_eq_neg_relativeFisherInformation {V : E → ℝ}
    (hV : ContDiff ℝ 2 V) (hprob : IsProbabilityMeasure (gibbsMeasure volume V))
    (u : ℝ → E → ℝ) (t₀ : ℝ) (D : SmoothInformationEvolutionDomain V u t₀) :
    letI := D.probability t₀ (mem_of_mem_nhds D.nhds)
    HasDerivAt (fun t => (klDiv (exponentialDensityMeasure (gibbsMeasure volume V) (u t))
      (gibbsMeasure volume V)).toReal)
      (-(relativeFisherInformation hV hprob
        (exponentialDensityMeasure (gibbsMeasure volume V) (u t₀))).toReal) t₀ := by
  let := hprob
  have ht₀ : t₀ ∈ D.neighborhood := mem_of_mem_nhds D.nhds
  let := D.probability t₀ ht₀
  have hraw := hasDerivAt_density_entropy_eq_neg_fisher (hV.differentiable (by norm_num))
    (fun t x => Real.exp (u t x)) D.nhds (fun _ _ _ => Real.exp_pos _)
    (D.spatial t₀ ht₀).exp D.entropyIBP D.densityPDE ?_
    (by simpa only [Real.log_exp] using D.entropyIntegrable t₀ ht₀)
    (by simpa only [Real.log_exp] using D.entropyDerivativeMeasurable) D.entropyBound
    (by simpa only [Real.log_exp] using D.entropyDominated) D.entropyBoundIntegrable
  · have hscore : (∫ x, ‖gradient (fun y => Real.exp (u t₀ y)) x‖ ^ 2 / Real.exp (u t₀ x)
        ∂gibbsMeasure volume V) =
        (relativeFisherInformation hV hprob (exponentialDensityMeasure (gibbsMeasure volume V) (u t₀))).toReal := by
      rw [relativeFisherInformation_toReal_eq_weighted_score hV hprob
        (D.spatial t₀ ht₀) (D.probability t₀ ht₀) (D.scoreIntegrable t₀ ht₀)]
      apply integral_congr_ae
      exact Eventually.of_forall (fun x => exp_density_fisher_integrand
        (((D.spatial t₀ ht₀).differentiable (by norm_num)) x))
    rw [hscore] at hraw
    apply hraw.congr_of_eventuallyEq
    filter_upwards [D.nhds] with t ht
    rw [klDiv_toReal_exponential_weighted (D.spatial t ht).continuous.measurable (D.probability t ht)]
    simp only [Real.log_exp]
  · filter_upwards [D.nhds] with t ht
    simp only [Real.log_exp]
    convert! ((D.spatial t ht).exp.continuous.mul (D.spatial t ht).continuous).aestronglyMeasurable using 1

/-- The actual canonical Fisher functional along a normalized exponential
measure curve. The normalization witnesses only supply finite-law instances. -/
@[expose] noncomputable def exponentialCurveRelativeFisherInformation {V : E → ℝ}
    (hV : ContDiff ℝ 2 V) (hprob : IsProbabilityMeasure (gibbsMeasure volume V))
    (u : ℝ → E → ℝ)
    (hνprob : ∀ t, IsProbabilityMeasure (exponentialDensityMeasure (gibbsMeasure volume V) (u t)))
    (t : ℝ) : ENNReal := by
  let := hνprob t
  exact relativeFisherInformation hV hprob (exponentialDensityMeasure (gibbsMeasure volume V) (u t))

/-- The derivative inequality for genuine canonical Fisher information,
proved from the actual density and mixed-gradient PDEs and weighted Bochner
IBP. No Fisher-dissipation inequality occurs among the hypotheses. -/
theorem relativeFisherInformation_dissipation_le {V : E → ℝ}
    (hV : ContDiff ℝ 2 V) (hprob : IsProbabilityMeasure (gibbsMeasure volume V))
    (u : ℝ → E → ℝ)
    (hνprob : ∀ t, IsProbabilityMeasure (exponentialDensityMeasure (gibbsMeasure volume V) (u t)))
    (t₀ : ℝ) (D : SmoothInformationEvolutionDomain V u t₀)
    (ρ : ℝ) (hcurv : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z) :
    ∃ I' : ℝ, HasDerivAt (fun t =>
        (exponentialCurveRelativeFisherInformation hV hprob u hνprob t).toReal) I' t₀ ∧
      I' ≤ -2 * ρ * (exponentialCurveRelativeFisherInformation hV hprob u hνprob t₀).toReal := by
  have ht₀ : t₀ ∈ D.neighborhood := mem_of_mem_nhds D.nhds
  have hEq (t : ℝ) (ht : t ∈ D.neighborhood) :
      (exponentialCurveRelativeFisherInformation hV hprob u hνprob t).toReal =
      ∫ x, ‖gradient (fun y => Real.exp (u t y)) x‖ ^ 2 / Real.exp (u t x)
        ∂gibbsMeasure volume V := by
    rw [exponentialCurveRelativeFisherInformation,
      relativeFisherInformation_toReal_eq_weighted_score hV hprob
        (D.spatial t ht) (hνprob t) (D.scoreIntegrable t ht)]
    apply integral_congr_ae
    exact Eventually.of_forall (fun x => (exp_density_fisher_integrand
      (((D.spatial t ht).differentiable (by norm_num)) x)).symm)
  have hmeas : ∀ᶠ t in 𝓝 t₀, AEStronglyMeasurable
      (fun x => Real.exp (u t x) * ‖gradient (u t) x‖ ^ 2) (gibbsMeasure volume V) := by
    filter_upwards [D.nhds] with t ht
    have hg := continuous_gradient_of_c1 ((D.spatial t ht).of_le (by norm_num))
    convert! ((D.spatial t ht).exp.continuous.mul (hg.norm.pow 2)).aestronglyMeasurable using 1
  obtain ⟨I', hraw, hbound⟩ := smooth_fisher_dissipation_le hV u D.nhds
    D.spatial D.spatial₀ D.fisherIBP D.densityPDE D.gradientPDE hmeas
    D.fisherDerivativeMeasurable D.fisherBound D.fisherDominated D.fisherBoundIntegrable ρ hcurv
  refine ⟨I', hraw.congr_of_eventuallyEq ?_, ?_⟩
  · filter_upwards [D.nhds] with t ht
    exact hEq t ht
  · rw [hEq t₀ ht₀]
    exact hbound

/-- Genuine canonical Fisher information decays exponentially on every
interval on which the raw PDE/domain obligations are discharged. -/
theorem relativeFisherInformation_exponential_decay {V : E → ℝ}
    (hV : ContDiff ℝ 2 V) (hprob : IsProbabilityMeasure (gibbsMeasure volume V))
    (u : ℝ → E → ℝ)
    (hνprob : ∀ t, IsProbabilityMeasure (exponentialDensityMeasure (gibbsMeasure volume V) (u t)))
    {a b : ℝ} (hab : a ≤ b)
    (D : ∀ t ∈ Icc a b, SmoothInformationEvolutionDomain V u t)
    (ρ : ℝ) (hcurv : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z) :
    (exponentialCurveRelativeFisherInformation hV hprob u hνprob b).toReal ≤
      Real.exp (-2 * ρ * (b - a)) *
        (exponentialCurveRelativeFisherInformation hV hprob u hνprob a).toReal := by
  let I := fun t => (exponentialCurveRelativeFisherInformation hV hprob u hνprob t).toReal
  have hAll (t : ℝ) (ht : t ∈ Icc a b) :
      ∃ I' : ℝ, HasDerivAt I I' t ∧ I' ≤ -2 * ρ * I t :=
    relativeFisherInformation_dissipation_le hV hprob u hνprob t (D t ht) ρ hcurv
  have hc : ContinuousOn I (Icc a b) := by
    intro t ht
    obtain ⟨r, hr, _⟩ := hAll t ht
    exact hr.continuousAt.continuousWithinAt
  have hd (t : ℝ) (ht : t ∈ Ioo a b) : HasDerivAt I (deriv I t) t := by
    obtain ⟨r, hr, _⟩ := hAll t (Ioo_subset_Icc_self ht)
    exact hr.differentiableAt.hasDerivAt
  have hi (t : ℝ) (ht : t ∈ Ioo a b) : deriv I t ≤ -(2 * ρ) * I t := by
    obtain ⟨r, hr, hb⟩ := hAll t (Ioo_subset_Icc_self ht)
    rw [hr.deriv]
    nlinarith
  have hh := exponential_decay_of_deriv_le_on (rate := 2 * ρ) hab hc hd hi
  convert! hh using 1
  congr 2
  ring

/-- The actual information domain supplies finite canonical Fisher,
so the evolution theorems do not silently turn infinite information into 0. -/
theorem exponentialCurveRelativeFisherInformation_ne_top {V : E → ℝ}
    (hV : ContDiff ℝ 2 V) (hprob : IsProbabilityMeasure (gibbsMeasure volume V))
    (u : ℝ → E → ℝ)
    (hνprob : ∀ t, IsProbabilityMeasure (exponentialDensityMeasure (gibbsMeasure volume V) (u t)))
    (t : ℝ) (D : SmoothInformationEvolutionDomain V u t) :
    exponentialCurveRelativeFisherInformation hV hprob u hνprob t ≠ ⊤ := by
  have ht : t ∈ D.neighborhood := mem_of_mem_nhds D.nhds
  rw [exponentialCurveRelativeFisherInformation,
    relativeFisherInformation_exponential hV hprob (D.spatial t ht) (hνprob t)
      (score_integrable_exponential (D.spatial t ht).continuous.measurable (D.scoreIntegrable t ht))]
  exact ENNReal.ofReal_ne_top

/-- Source `eqHI` for actual KL and canonical relative Fisher: the density
PDE gives entropy dissipation and actual curvature gives Fisher monotonicity.
No Fisher upper bound or entropy-dissipation inequality is assumed. -/
theorem relativeFisherInformation_le_entropy_div {V : E → ℝ}
    (hV : ContDiff ℝ 2 V) (hprob : IsProbabilityMeasure (gibbsMeasure volume V))
    (u : ℝ → E → ℝ)
    (hνprob : ∀ t, IsProbabilityMeasure (exponentialDensityMeasure (gibbsMeasure volume V) (u t)))
    {a b : ℝ} (hab : a < b)
    (D : ∀ t ∈ Icc a b, SmoothInformationEvolutionDomain V u t)
    (ρ : ℝ) (hρ : 0 ≤ ρ)
    (hcurv : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z) :
    exponentialCurveRelativeFisherInformation hV hprob u hνprob b ≤
      ENNReal.ofReal ((klDiv (exponentialDensityMeasure (gibbsMeasure volume V) (u a))
        (gibbsMeasure volume V)).toReal / (b - a)) := by
  let H := fun t => (klDiv (exponentialDensityMeasure (gibbsMeasure volume V) (u t))
    (gibbsMeasure volume V)).toReal
  let I := fun t => (exponentialCurveRelativeFisherInformation hV hprob u hνprob t).toReal
  have hHD (t : ℝ) (ht : t ∈ Icc a b) : HasDerivAt H (-I t) t :=
    hasDerivAt_klDiv_eq_neg_relativeFisherInformation hV hprob u t (D t ht)
  have hID (t : ℝ) (ht : t ∈ Icc a b) :
      ∃ r : ℝ, HasDerivAt I r t ∧ r ≤ -2 * ρ * I t :=
    relativeFisherInformation_dissipation_le hV hprob u hνprob t (D t ht) ρ hcurv
  have hcH : ContinuousOn H (Icc a b) :=
    fun t ht => (hHD t ht).continuousAt.continuousWithinAt
  have hcI : ContinuousOn I (Icc a b) := by
    intro t ht
    obtain ⟨r, hr, _⟩ := hID t ht
    exact hr.continuousAt.continuousWithinAt
  have hdI (t : ℝ) (ht : t ∈ Ioo a b) : HasDerivAt I (deriv I t) t := by
    obtain ⟨r, hr, _⟩ := hID t (Ioo_subset_Icc_self ht)
    exact hr.differentiableAt.hasDerivAt
  have hiI (t : ℝ) (ht : t ∈ Ioo a b) : deriv I t ≤ -2 * ρ * I t := by
    obtain ⟨r, hr, hh⟩ := hID t (Ioo_subset_Icc_self ht)
    rw [hr.deriv]
    exact hh
  have hanti : AntitoneOn I (Icc a b) := antitoneOn_of_dissipative_derivative hρ
    hcI hdI (fun _ _ => ENNReal.toReal_nonneg) hiI
  have hbound := dissipation_endpoint_le_entropy_div hab hcH
    (fun t ht => hHD t (Ioo_subset_Icc_self ht)) hcI hanti ENNReal.toReal_nonneg
  rw [← ENNReal.ofReal_toReal
    (exponentialCurveRelativeFisherInformation_ne_top hV hprob u hνprob b (D b ⟨hab.le, le_rfl⟩))]
  exact ENNReal.ofReal_le_ofReal hbound

/-- The entropy domain makes genuine KL finite, independently of any
formal use of its `toReal` in the differential identities. -/
theorem klDiv_ne_top_of_smoothInformationEvolutionDomain {V : E → ℝ}
    (hprob : IsProbabilityMeasure (gibbsMeasure volume V))
    (u : ℝ → E → ℝ) (t : ℝ) (D : SmoothInformationEvolutionDomain V u t) :
    klDiv (exponentialDensityMeasure (gibbsMeasure volume V) (u t))
      (gibbsMeasure volume V) ≠ ⊤ := by
  let := hprob
  have ht : t ∈ D.neighborhood := mem_of_mem_nhds D.nhds
  let := D.probability t ht
  have hm := (D.spatial t ht).continuous.measurable
  have huInt : Integrable (u t) (exponentialDensityMeasure (gibbsMeasure volume V) (u t)) := by
    apply (integrable_withDensity_iff_integrable_smul' hm.exp.ennreal_ofReal (by simp)).mpr
    simpa only [ENNReal.toReal_ofReal (Real.exp_nonneg _), smul_eq_mul] using D.entropyIntegrable t ht
  have hLLR : Integrable (llr (exponentialDensityMeasure (gibbsMeasure volume V) (u t))
      (gibbsMeasure volume V)) (exponentialDensityMeasure (gibbsMeasure volume V) (u t)) :=
    huInt.congr (llr_exponentialDensityMeasure_selfAE hm).symm
  have hAC : exponentialDensityMeasure (gibbsMeasure volume V) (u t) ≪ gibbsMeasure volume V :=
    withDensity_absolutelyContinuous _ _
  exact klDiv_ne_top hAC hLLR

/-- Source `eqexpdecI` for genuine extended-valued canonical Fisher
information, with finiteness derived from the actual smooth PDE domain. -/
theorem relativeFisherInformation_exponential_decay_ennreal {V : E → ℝ}
    (hV : ContDiff ℝ 2 V) (hprob : IsProbabilityMeasure (gibbsMeasure volume V))
    (u : ℝ → E → ℝ)
    (hνprob : ∀ t, IsProbabilityMeasure (exponentialDensityMeasure (gibbsMeasure volume V) (u t)))
    {a b : ℝ} (hab : a ≤ b)
    (D : ∀ t ∈ Icc a b, SmoothInformationEvolutionDomain V u t)
    (ρ : ℝ) (hcurv : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z) :
    exponentialCurveRelativeFisherInformation hV hprob u hνprob b ≤
      ENNReal.ofReal (Real.exp (-2 * ρ * (b - a))) *
        exponentialCurveRelativeFisherInformation hV hprob u hνprob a := by
  have hbound := relativeFisherInformation_exponential_decay hV hprob u hνprob hab D ρ hcurv
  have hfa := exponentialCurveRelativeFisherInformation_ne_top hV hprob u hνprob a
    (D a ⟨le_rfl, hab⟩)
  have hfb := exponentialCurveRelativeFisherInformation_ne_top hV hprob u hνprob b
    (D b ⟨hab, le_rfl⟩)
  calc
    _ = ENNReal.ofReal (exponentialCurveRelativeFisherInformation hV hprob u hνprob b).toReal :=
      (ENNReal.ofReal_toReal hfb).symm
    _ ≤ ENNReal.ofReal (Real.exp (-2 * ρ * (b - a)) *
        (exponentialCurveRelativeFisherInformation hV hprob u hνprob a).toReal) :=
      ENNReal.ofReal_le_ofReal hbound
    _ = _ := by rw [ENNReal.ofReal_mul (Real.exp_nonneg _), ENNReal.ofReal_toReal hfa]

end CutoffRigidity
