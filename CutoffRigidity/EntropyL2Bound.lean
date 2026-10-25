module

public import Mathlib.InformationTheory.KullbackLeibler.Basic
public import CutoffRigidity.GibbsHeatL2Decay

/-! # Genuine relative entropy is bounded by the squared density error

The scalar logarithm inequality controls Mathlib's actual KL integrand.
The genuine Radon--Nikodym density then gives finiteness and the L² bound,
without assuming log-integrability or an entropy formula.
-/

public section

namespace CutoffRigidity

open MeasureTheory InformationTheory Filter

/-- The exact KL integrand is below the squared distance to equilibrium. -/
theorem klFun_le_sq_sub_one {a : ℝ} (ha : 0 ≤ a) : klFun a ≤ (a - 1) ^ 2 := by
  rcases eq_or_lt_of_le ha with hzero | hpos
  · rw [← hzero]
    norm_num [klFun]
  · have hh := mul_le_mul_of_nonneg_left (Real.log_le_sub_one_of_pos hpos) ha
    unfold klFun
    nlinarith

/-- Actual relative entropy of a genuine L² probability density is finite
and bounded by its true squared density error. -/
theorem klDiv_withDensity_le_L2_error
    {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsProbabilityMeasure μ]
    {f : X → ℝ} (hfm : Measurable f) (hf : MemLp f 2 μ) (hfn : ∀ x, 0 ≤ f x)
    (hν : IsProbabilityMeasure (μ.withDensity (fun x => ENNReal.ofReal (f x)))) :
    klDiv (μ.withDensity (fun x => ENNReal.ofReal (f x))) μ ≤
      ENNReal.ofReal (∫ x, (f x - 1) ^ 2 ∂μ) := by
  have := hν
  have hi : Integrable (fun x => (f x - 1) ^ 2) μ := by
    simpa only [Pi.sub_apply] using (hf.sub (memLp_const (1 : ℝ))).integrable_sq
  rw [klDiv_eq_lintegral_klFun_of_ac (withDensity_absolutelyContinuous _ _),
    ofReal_integral_eq_lintegral_ofReal hi (Filter.Eventually.of_forall (fun x => sq_nonneg _))]
  apply lintegral_mono_ae
  filter_upwards [Measure.rnDeriv_withDensity μ hfm.ennreal_ofReal] with x hx
  rw [hx, ENNReal.toReal_ofReal (hfn x)]
  exact ENNReal.ofReal_le_ofReal (klFun_le_sq_sub_one (hfn x))

/-- Log-likelihood integrability is derived from the actual L² density bound. -/
theorem klDiv_withDensity_ne_top_of_memLp_two
    {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsProbabilityMeasure μ]
    {f : X → ℝ} (hfm : Measurable f) (hf : MemLp f 2 μ) (hfn : ∀ x, 0 ≤ f x)
    (hν : IsProbabilityMeasure (μ.withDensity (fun x => ENNReal.ofReal (f x)))) :
    klDiv (μ.withDensity (fun x => ENNReal.ofReal (f x))) μ ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.ofReal_ne_top (klDiv_withDensity_le_L2_error hfm hf hfn hν)

/-- The corresponding true real entropy bound, with no hidden ∞ truncation. -/
theorem toReal_klDiv_withDensity_le_L2_error
    {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsProbabilityMeasure μ]
    {f : X → ℝ} (hfm : Measurable f) (hf : MemLp f 2 μ) (hfn : ∀ x, 0 ≤ f x)
    (hν : IsProbabilityMeasure (μ.withDensity (fun x => ENNReal.ofReal (f x)))) :
    (klDiv (μ.withDensity (fun x => ENNReal.ofReal (f x))) μ).toReal ≤
      ∫ x, (f x - 1) ^ 2 ∂μ := by
  have hh := ENNReal.toReal_mono ENNReal.ofReal_ne_top (klDiv_withDensity_le_L2_error hfm hf hfn hν)
  simpa only [ENNReal.toReal_ofReal (integral_nonneg (fun x => sq_nonneg _))] using hh

end CutoffRigidity
