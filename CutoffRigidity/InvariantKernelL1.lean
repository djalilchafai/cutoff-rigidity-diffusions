module
public import CutoffRigidity.InvariantKernelL2

/-! # Genuine invariant-kernel L¹ contraction -/
public section
namespace CutoffRigidity
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal
variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

/-- Actual Fubini and the norm-of-integral inequality give L¹ membership
of actual Markov averages, with no L¹ operator or contraction premise. -/
theorem invariantKernel_integral_integrable
    (K : Kernel X X) [IsMarkovKernel K] (hInv : K ∘ₘ μ = μ)
    {f : X → ℝ} (hm : Measurable f) (hf : Integrable f μ) :
    Integrable (fun x => ∫ y, f y ∂K x) μ := by
  have hi : Integrable f (K ∘ₘ μ) := by rw [hInv]; exact hf
  have hNorm := Measure.integrable_integral_norm_of_integrable_comp hi
  apply hNorm.mono' hm.stronglyMeasurable.integral_kernel.aestronglyMeasurable
  exact Eventually.of_forall (fun x => norm_integral_le_integral_norm _)

/-- Genuine L¹ contraction for arbitrary measurable integrable signed
inputs under an actually invariant Markov kernel. -/
theorem invariantKernel_L1_contraction
    (K : Kernel X X) [IsMarkovKernel K] (hInv : K ∘ₘ μ = μ)
    {f g : X → ℝ} (hfm : Measurable f) (hgm : Measurable g)
    (hf : Integrable f μ) (hg : Integrable g μ) :
    (∫ x, |(∫ y, f y ∂K x) - ∫ y, g y ∂K x| ∂μ) ≤
      ∫ x, |f x - g x| ∂μ := by
  have hdiff : Integrable (fun x => f x - g x) μ := hf.sub hg
  have hInt := invariantKernel_integral_integrable K hInv (hfm.sub hgm) hdiff
  have hNormInt : Integrable (fun x => ∫ y, |f y - g y| ∂K x) μ := by
    have hi : Integrable (fun x => f x - g x) (K ∘ₘ μ) := by rw [hInv]; exact hdiff
    simpa only [Real.norm_eq_abs] using Measure.integrable_integral_norm_of_integrable_comp hi
  have hh := integral_mono hInt.abs hNormInt (fun x => by
    simpa only [Real.norm_eq_abs, Pi.sub_apply] using norm_integral_le_integral_norm (fun y => f y - g y))
  have hEq : (∫ x, |(∫ y, f y ∂K x) - ∫ y, g y ∂K x| ∂μ) =
      ∫ x, |∫ y, (f y - g y) ∂K x| ∂μ := by
    apply integral_congr_ae
    filter_upwards [invariantKernel_integrable_ae K hInv hf, invariantKernel_integrable_ae K hInv hg] with x hfx hgx
    rw [integral_sub hfx hgx]
  rw [hEq]
  exact hh.trans_eq (integral_invariantKernel K hInv hdiff.abs)

end CutoffRigidity
