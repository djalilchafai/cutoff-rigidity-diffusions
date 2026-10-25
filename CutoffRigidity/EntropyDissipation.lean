module

public import CutoffRigidity.GibbsEnergy
public import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.InformationTheory.KullbackLeibler.Basic

/-!
# Entropy dissipation on an explicit smooth integration domain

The static identity and dominated time differentiation below use the actual
Gibbs measure and Langevin differential expression. Their integrability and
regularity hypotheses are explicit domain obligations. This is not a theorem
that arbitrary Langevin transition densities satisfy those obligations, nor a
replacement for general Sobolev Fisher information.
-/

public section

namespace CutoffRigidity

open MeasureTheory Filter Topology

variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

/-- The precise integration-by-parts domain for testing `Lf` by `1 + log f`.
All fields are ordinary integrability statements, not dissipation estimates. -/
structure EntropyIntegrationDomain (V f : E → ℝ) : Prop where
  logDf : ∀ i : Fin d, Integrable
    (fun x => (1 + Real.log (f x)) * fderiv ℝ f x (EuclideanSpace.single i 1))
    (gibbsMeasure volume V)
  logDDf : ∀ i : Fin d, Integrable
    (fun x => (1 + Real.log (f x)) *
      fderiv ℝ (fun y => fderiv ℝ f y (EuclideanSpace.single i 1)) x
        (EuclideanSpace.single i 1)) (gibbsMeasure volume V)
  scoreSq : ∀ i : Fin d, Integrable
    (fun x => (fderiv ℝ f x (EuclideanSpace.single i 1)) ^ 2 / f x)
    (gibbsMeasure volume V)
  logDrift : ∀ i : Fin d, Integrable
    (fun x => (1 + Real.log (f x)) * fderiv ℝ V x (EuclideanSpace.single i 1) *
      fderiv ℝ f x (EuclideanSpace.single i 1)) (gibbsMeasure volume V)

/-- The genuine Fréchet derivative of the entropy test function. -/
theorem fderiv_one_add_log_density (f : E → ℝ) {x : E}
    (hf : DifferentiableAt ℝ f x) (hpos : 0 < f x) (v : E) :
    fderiv ℝ (fun y => 1 + Real.log (f y)) x v = fderiv ℝ f x v / f x := by
  rw [((hf.hasFDerivAt.log hpos.ne').const_add 1).fderiv]
  simp only [smul_apply, smul_eq_mul]
  ring

/-- The actual gradient chain rule for the entropy test function. -/
theorem gradient_one_add_log_density (f : E → ℝ) {x : E}
    (hf : DifferentiableAt ℝ f x) (hpos : 0 < f x) :
    gradient (fun y => 1 + Real.log (f y)) x = (f x)⁻¹ • gradient f x := by
  apply ext_inner_right ℝ
  intro v
  rw [inner_gradient_left, fderiv_one_add_log_density f hf hpos,
    real_inner_smul_left, inner_gradient_left]
  ring

/-- Static entropy dissipation against the actual Gibbs measure, obtained by
using `1 + log f` in the proved Gibbs integration-by-parts formula. -/
theorem integral_entropy_test_langevin_eq_neg_fisher
    {V f : E → ℝ} (hV : Differentiable ℝ V) (hf : ContDiff ℝ 2 f)
    (hpos : ∀ x, 0 < f x) (hdom : EntropyIntegrationDomain V f) :
    (∫ x, (1 + Real.log (f x)) * langevinDifferentialOperator V f x
      ∂gibbsMeasure volume V) =
      -(∫ x, ‖gradient f x‖ ^ 2 / f x ∂gibbsMeasure volume V) := by
  have hfd : Differentiable ℝ f := hf.differentiable (by norm_num)
  have hlog : Differentiable ℝ (fun y => 1 + Real.log (f y)) :=
    (hfd.log (fun x => (hpos x).ne')).const_add 1
  have hprod (i : Fin d) :
      (fun x => fderiv ℝ (fun y => 1 + Real.log (f y)) x (EuclideanSpace.single i 1) *
        fderiv ℝ f x (EuclideanSpace.single i 1)) =
      fun x => (fderiv ℝ f x (EuclideanSpace.single i 1)) ^ 2 / f x := by
    funext x
    rw [fderiv_one_add_log_density f (hfd x) (hpos x)]
    ring
  have hscore (i : Fin d) : Integrable
      (fun x => fderiv ℝ (fun y => 1 + Real.log (f y)) x (EuclideanSpace.single i 1) *
        fderiv ℝ f x (EuclideanSpace.single i 1)) (gibbsMeasure volume V) := by
    rw [hprod]
    exact hdom.scoreSq i
  have h := integral_mul_langevin_eq_neg_gradient_inner hV hlog hf
    hdom.logDf hdom.logDDf hscore hdom.logDrift
  have hinner (x : E) : inner ℝ (gradient (fun y => 1 + Real.log (f y)) x) (gradient f x) =
      ‖gradient f x‖ ^ 2 / f x := by
    rw [gradient_one_add_log_density f (hfd x) (hpos x), real_inner_smul_left,
      real_inner_self_eq_norm_sq]
    ring
  simpa only [hinner] using h

/-- Dominated differentiation of the actual density entropy integral.
The derivative bound is an explicit analytic hypothesis about the displayed
integrand, not an assumed entropy dissipation estimate. -/
theorem hasDerivAt_integral_density_mul_log
    {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (f D : ℝ → α → ℝ) {t₀ : ℝ} {s : Set ℝ} (hs : s ∈ 𝓝 t₀)
    (hpos : ∀ᵐ x ∂μ, ∀ t ∈ s, 0 < f t x)
    (htime : ∀ᵐ x ∂μ, ∀ t ∈ s, HasDerivAt (fun u => f u x) (D t x) t)
    (hmeas : ∀ᶠ t in 𝓝 t₀, AEStronglyMeasurable (fun x => f t x * Real.log (f t x)) μ)
    (hint : Integrable (fun x => f t₀ x * Real.log (f t₀ x)) μ)
    (hDmeas : AEStronglyMeasurable (fun x => (1 + Real.log (f t₀ x)) * D t₀ x) μ)
    (bound : α → ℝ)
    (hbound : ∀ᵐ x ∂μ, ∀ t ∈ s, ‖(1 + Real.log (f t x)) * D t x‖ ≤ bound x)
    (hboundInt : Integrable bound μ) :
    Integrable (fun x => (1 + Real.log (f t₀ x)) * D t₀ x) μ ∧
      HasDerivAt (fun t => ∫ x, f t x * Real.log (f t x) ∂μ)
        (∫ x, (1 + Real.log (f t₀ x)) * D t₀ x ∂μ) t₀ := by
  apply hasDerivAt_integral_of_dominated_loc_of_deriv_le hs hmeas hint hDmeas hbound hboundInt
  filter_upwards [hpos, htime] with x hx hd
  intro t ht
  have h := (Real.hasDerivAt_mul_log (hx t ht).ne').comp t (hd t ht)
  convert h using 1
  · ext u
    rfl
  · ring

/-- Smooth-domain entropy dissipation for an actual density solving the
Langevin forward equation relative to its invariant Gibbs measure.
Heat-kernel regularity and dominance for the paper's processes remain to be
proved before applying this domain theorem to those transition densities. -/
theorem hasDerivAt_density_entropy_eq_neg_fisher
    {V : E → ℝ} (hV : Differentiable ℝ V) (f : ℝ → E → ℝ)
    {t₀ : ℝ} {s : Set ℝ} (hs : s ∈ 𝓝 t₀)
    (hpos : ∀ t ∈ s, ∀ x, 0 < f t x)
    (hf : ContDiff ℝ 2 (f t₀)) (hdom : EntropyIntegrationDomain V (f t₀))
    (htime : ∀ᵐ x ∂gibbsMeasure volume V, ∀ t ∈ s,
      HasDerivAt (fun u => f u x) (langevinDifferentialOperator V (f t) x) t)
    (hmeas : ∀ᶠ t in 𝓝 t₀,
      AEStronglyMeasurable (fun x => f t x * Real.log (f t x)) (gibbsMeasure volume V))
    (hint : Integrable (fun x => f t₀ x * Real.log (f t₀ x)) (gibbsMeasure volume V))
    (hDmeas : AEStronglyMeasurable
      (fun x => (1 + Real.log (f t₀ x)) * langevinDifferentialOperator V (f t₀) x)
      (gibbsMeasure volume V))
    (bound : E → ℝ)
    (hbound : ∀ᵐ x ∂gibbsMeasure volume V, ∀ t ∈ s,
      ‖(1 + Real.log (f t x)) * langevinDifferentialOperator V (f t) x‖ ≤ bound x)
    (hboundInt : Integrable bound (gibbsMeasure volume V)) :
    HasDerivAt (fun t => ∫ x, f t x * Real.log (f t x) ∂gibbsMeasure volume V)
      (-(∫ x, ‖gradient (f t₀) x‖ ^ 2 / f t₀ x ∂gibbsMeasure volume V)) t₀ := by
  have h := (hasDerivAt_integral_density_mul_log (gibbsMeasure volume V) f
    (fun t x => langevinDifferentialOperator V (f t) x) hs
    (Filter.Eventually.of_forall fun x t ht => hpos t ht x) htime hmeas hint hDmeas
    bound hbound hboundInt).2
  rw [integral_entropy_test_langevin_eq_neg_fisher hV hf
    (hpos t₀ (mem_of_mem_nhds hs)) hdom] at h
  exact h

/-- For a normalized positive integrable density, the displayed density entropy
is the genuine Kullback--Leibler divergence of its weighted probability law. -/
theorem klDiv_withDensity_eq_density_entropy
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
    (f : α → ℝ) (hf : Measurable f) (hpos : ∀ x, 0 ≤ f x)
    (hfInt : Integrable f μ) (hnorm : ∫ x, f x ∂μ = 1)
    (hentropy : Integrable (fun x => f x * Real.log (f x)) μ) :
    InformationTheory.klDiv (μ.withDensity (fun x => ENNReal.ofReal (f x))) μ =
      ENNReal.ofReal (∫ x, f x * Real.log (f x) ∂μ) := by
  let ν := μ.withDensity (fun x => ENNReal.ofReal (f x))
  have hprob : IsProbabilityMeasure ν := by
    constructor
    dsimp [ν]
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
      ← ofReal_integral_eq_lintegral_ofReal hfInt (Filter.Eventually.of_forall hpos), hnorm]
    simp
  have hAC : ν ≪ μ := withDensity_absolutelyContinuous _ _
  have hRN : (fun x => (ν.rnDeriv μ x).toReal) =ᵐ[μ] f := by
    filter_upwards [Measure.rnDeriv_withDensity μ (by fun_prop :
      Measurable (fun x => ENNReal.ofReal (f x)))] with x hx
    rw [hx, ENNReal.toReal_ofReal (hpos x)]
  have hfun : (fun x => InformationTheory.klFun (ν.rnDeriv μ x).toReal) =ᵐ[μ]
      (fun x => f x * Real.log (f x) + 1 - f x) := by
    filter_upwards [hRN] with x hx
    rw [hx]
    rfl
  have hInt : Integrable (fun x => InformationTheory.klFun (ν.rnDeriv μ x).toReal) μ :=
    ((hentropy.add (integrable_const 1)).sub hfInt).congr hfun.symm
  have hllr := (InformationTheory.integrable_klFun_rnDeriv_iff hAC).mp hInt
  rw [InformationTheory.klDiv_eq_integral_klFun, ite_eq_left ⟨hAC, hllr⟩,
    integral_congr_ae hfun]
  have hsub := integral_sub (hentropy.add (integrable_const 1)) hfInt
  have hadd := integral_add hentropy (integrable_const 1)
  simp only [Pi.add_apply] at hsub hadd
  rw [hsub, hadd, integral_const, hnorm]
  simp

end CutoffRigidity
