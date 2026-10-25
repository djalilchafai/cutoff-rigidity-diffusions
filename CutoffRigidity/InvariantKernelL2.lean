module
public import CutoffRigidity.TransportMoments
public import Mathlib.Probability.Kernel.Composition.IntegralCompProd
public import Mathlib.Probability.Moments.Variance

/-! # Actual invariant Markov kernels on L²

Jensen, genuine kernel Fubini, and invariant-measure null-set transport give
an actual contraction on L² equivalence classes, with no operator premise.
-/
public section
namespace CutoffRigidity
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
variable {α : Type*} [MeasurableSpace α] {μ : Measure α}
  (κ : Kernel α α) [IsMarkovKernel κ] (hInv : κ ∘ₘ μ = μ)
include hInv

omit [IsMarkovKernel κ] in
/-- Invariance transports actual representative null sets through the kernel. -/
theorem invariantKernel_integral_congr_ae {f g : α → ℝ} (hfg : f =ᵐ[μ] g) :
    (fun x => ∫ y, f y ∂κ x) =ᵐ[μ] fun x => ∫ y, g y ∂κ x := by
  have hh : f =ᵐ[κ ∘ₘ μ] g := by rw [hInv]; exact hfg
  filter_upwards [Measure.ae_ae_of_ae_comp hh] with x hx
  exact integral_congr_ae hx

omit [IsMarkovKernel κ] in
/-- Actual kernel Fubini supplies local integrability almost everywhere. -/
theorem invariantKernel_integrable_ae {f : α → ℝ} (hf : Integrable f μ) :
    ∀ᵐ x ∂μ, Integrable f (κ x) := by
  have hh : Integrable f (κ ∘ₘ μ) := by rw [hInv]; exact hf
  rw [Measure.comp_eq_comp_const_apply] at hh
  simpa only [Kernel.const_apply] using hh.ae_of_comp

omit [IsMarkovKernel κ] in
/-- Actual kernel Fubini preserves the integral of every integrable input. -/
theorem integral_invariantKernel {f : α → ℝ} (hf : Integrable f μ) :
    (∫ x, ∫ y, f y ∂κ x ∂μ) = ∫ y, f y ∂μ := by
  have hh : Integrable f (κ ∘ₘ μ) := by rw [hInv]; exact hf
  rw [Measure.comp_eq_comp_const_apply] at hh
  have he := Kernel.integral_comp hh
  rw [← Measure.comp_eq_comp_const_apply, hInv] at he
  simpa only [Kernel.const_apply] using he.symm

omit [IsMarkovKernel κ] in
/-- The actual integral of the squared input is integrable under μ. -/
theorem invariantKernel_integral_sq_integrable {f : α → ℝ} (hf : MemLp f 2 μ) :
    Integrable (fun x => ∫ y, f y ^ 2 ∂κ x) μ := by
  have hh : Integrable (fun y => f y ^ 2) (κ ∘ₘ μ) := by rw [hInv]; exact hf.integrable_sq
  rw [Measure.comp_eq_comp_const_apply] at hh
  simpa only [Kernel.const_apply] using hh.integral_comp

/-- Jensen is derived from actual probability variance, at almost every
state where the input has its genuine local L² integrability. -/
theorem invariantKernel_jensen_sq (f : α →₂[μ] ℝ) :
    ∀ᵐ x ∂μ, (∫ y, f y ∂κ x) ^ 2 ≤ ∫ y, f y ^ 2 ∂κ x := by
  filter_upwards [invariantKernel_integrable_ae κ hInv (Lp.memLp f).integrable_sq] with x hx
  have hlocal : MemLp (fun y => f y) 2 (κ x) :=
    (memLp_two_iff_integrable_sq (Lp.stronglyMeasurable f).aestronglyMeasurable).mpr hx
  have hh := variance_nonneg (fun y => f y) (κ x)
  rw [variance_eq_sub hlocal] at hh
  simpa only [Pi.pow_apply] using sub_nonneg.mp hh

/-- Actual averaging of a genuine L² representative remains in L². -/
theorem invariantKernel_memLp_integral (f : α →₂[μ] ℝ) :
    MemLp (fun x => ∫ y, f y ∂κ x) 2 μ := by
  have hm := (Lp.stronglyMeasurable f).integral_kernel (κ := κ)
  apply (memLp_two_iff_integrable_sq hm.aestronglyMeasurable).mpr
  apply (invariantKernel_integral_sq_integrable κ hInv (Lp.memLp f)).mono' (hm.pow 2).aestronglyMeasurable
  filter_upwards [invariantKernel_jensen_sq κ hInv f] with x hx
  change ‖(∫ y, f y ∂κ x) ^ 2‖ ≤ _
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact hx

@[expose] noncomputable def invariantKernelL2Apply (f : α →₂[μ] ℝ) : α →₂[μ] ℝ :=
  (invariantKernel_memLp_integral κ hInv f).toLp (fun x => ∫ y, f y ∂κ x)

theorem invariantKernelL2Apply_coeFn (f : α →₂[μ] ℝ) :
    invariantKernelL2Apply κ hInv f =ᵐ[μ] fun x => ∫ y, f y ∂κ x :=
  (invariantKernel_memLp_integral κ hInv f).coeFn_toLp

theorem norm_invariantKernelL2Apply_le (f : α →₂[μ] ℝ) :
    ‖invariantKernelL2Apply κ hInv f‖ ≤ ‖f‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  have hK := invariantKernel_memLp_integral κ hInv f
  change ‖hK.toLp _‖ ^ 2 ≤ _
  rw [norm_toLp_sq]
  have hi := integral_mono_ae hK.integrable_sq (invariantKernel_integral_sq_integrable κ hInv (Lp.memLp f))
    (invariantKernel_jensen_sq κ hInv f)
  calc
    _ ≤ ∫ x, ∫ y, f y ^ 2 ∂κ x ∂μ := hi
    _ = ∫ y, f y ^ 2 ∂μ := integral_invariantKernel κ hInv (Lp.memLp f).integrable_sq
    _ = ‖f‖ ^ 2 := by simpa only [Lp.toLp_coeFn] using (norm_toLp_sq (Lp.memLp f)).symm

variable [IsProbabilityMeasure μ]

@[expose] noncomputable def invariantKernelL2LinearMap : (α →₂[μ] ℝ) →ₗ[ℝ] (α →₂[μ] ℝ) where
  toFun := invariantKernelL2Apply κ hInv
  map_add' f g := by
    have hiF := invariantKernel_integrable_ae κ hInv ((Lp.memLp f).integrable (by norm_num))
    have hiG := invariantKernel_integrable_ae κ hInv ((Lp.memLp g).integrable (by norm_num))
    have hrep : (fun x => ∫ y, (f + g) y ∂κ x) =ᵐ[μ] fun x => ∫ y, f y + g y ∂κ x :=
      invariantKernel_integral_congr_ae κ hInv (Lp.coeFn_add f g)
    apply Lp.ext
    filter_upwards [invariantKernelL2Apply_coeFn κ hInv (f + g),
      Lp.coeFn_add (invariantKernelL2Apply κ hInv f) (invariantKernelL2Apply κ hInv g),
      invariantKernelL2Apply_coeFn κ hInv f, invariantKernelL2Apply_coeFn κ hInv g,
      hrep, hiF, hiG] with x hx hy hf hg he hif hig
    rw [hx, hy, Pi.add_apply, hf, hg, he]
    exact integral_add hif hig
  map_smul' r f := by
    change invariantKernelL2Apply κ hInv (r • f) = r • invariantKernelL2Apply κ hInv f
    have hrep : (fun x => ∫ y, (r • f) y ∂κ x) =ᵐ[μ] fun x => ∫ y, r • f y ∂κ x :=
      invariantKernel_integral_congr_ae κ hInv (Lp.coeFn_smul r f)
    apply Lp.ext
    filter_upwards [invariantKernelL2Apply_coeFn κ hInv (r • f),
      Lp.coeFn_smul r (invariantKernelL2Apply κ hInv f), invariantKernelL2Apply_coeFn κ hInv f,
      hrep] with x hx hy hf he
    rw [hx, hy, Pi.smul_apply, hf, he]
    exact integral_smul r _

/-- Actual invariant Markov averaging, constructed as a bounded linear
contraction on the genuine L² equivalence classes. -/
@[expose] noncomputable def invariantKernelL2Operator : (α →₂[μ] ℝ) →L[ℝ] (α →₂[μ] ℝ) :=
  (invariantKernelL2LinearMap κ hInv).mkContinuous 1
    (fun f => by
      change ‖invariantKernelL2Apply κ hInv f‖ ≤ 1 * ‖f‖
      rw [one_mul]
      exact norm_invariantKernelL2Apply_le κ hInv f)

theorem invariantKernelL2Operator_coeFn (f : α →₂[μ] ℝ) :
    invariantKernelL2Operator κ hInv f =ᵐ[μ] fun x => ∫ y, f y ∂κ x :=
  invariantKernelL2Apply_coeFn κ hInv f

theorem norm_invariantKernelL2Operator_le_one : ‖invariantKernelL2Operator κ hInv‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro f
  change ‖invariantKernelL2Apply κ hInv f‖ ≤ 1 * ‖f‖
  rw [one_mul]
  exact norm_invariantKernelL2Apply_le κ hInv f

/-- Genuine invariant-kernel averaging preserves pointwise almost-everywhere
nonnegativity of the actual L² representatives. -/
theorem invariantKernelL2Operator_preserves_nonneg (f : α →₂[μ] ℝ)
    (hf : ∀ᵐ x ∂μ, 0 ≤ f x) :
    ∀ᵐ x ∂μ, 0 ≤ invariantKernelL2Operator κ hInv f x := by
  have hh : ∀ᵐ x ∂(κ ∘ₘ μ), 0 ≤ f x := by rw [hInv]; exact hf
  filter_upwards [invariantKernelL2Operator_coeFn κ hInv f, Measure.ae_ae_of_ae_comp hh] with x hx hpos
  rw [hx]
  exact integral_nonneg_of_ae hpos

/-- The actual L² averaging operator preserves Gibbs/initial integration
by genuine invariant-kernel Fubini. -/
theorem integral_invariantKernelL2Operator (f : α →₂[μ] ℝ) :
    (∫ x, invariantKernelL2Operator κ hInv f x ∂μ) = ∫ x, f x ∂μ := by
  rw [integral_congr_ae (invariantKernelL2Operator_coeFn κ hInv f)]
  exact integral_invariantKernel κ hInv ((Lp.memLp f).integrable (by norm_num))

end CutoffRigidity
