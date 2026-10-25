module

public import CutoffRigidity.GibbsSobolevClassical

/-! # Actual scalar normal-contraction calculus

The actual gradient chain rule and classical compact graph composition are
proved directly from Fréchet derivatives. They will be passed through the
closed graph, rather than assuming a Sobolev chain rule.
-/

public section

namespace CutoffRigidity

open MeasureTheory

variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

/-- The actual scalar outer-composition gradient chain rule. -/
theorem gradient_scalar_outer_comp {ψ : ℝ → ℝ} {f : E → ℝ}
    (hψ : Differentiable ℝ ψ) (hf : Differentiable ℝ f) (x : E) :
    gradient (ψ ∘ f) x = deriv ψ (f x) • gradient f x := by
  apply ext_inner_right ℝ
  intro z
  rw [inner_gradient_left, real_inner_smul_left, inner_gradient_left]
  have hd := (hψ (f x)).hasDerivAt.comp_hasFDerivAt x (hf x).hasFDerivAt
  rw [hd.fderiv]
  rfl

/-- A smooth normal contraction is genuinely one-Lipschitz. -/
theorem scalar_normal_contraction_lipschitz {ψ : ℝ → ℝ} (hψ : Differentiable ℝ ψ)
    (hbound : ∀ r, |deriv ψ r| ≤ 1) : LipschitzWith 1 ψ := by
  apply lipschitzWith_of_nnnorm_deriv_le hψ
  intro r
  change |deriv ψ r| ≤ (1 : ℝ)
  exact hbound r

/-- The genuine gradient of a normal contraction is pointwise contracted. -/
theorem norm_gradient_scalar_normal_comp_le {ψ : ℝ → ℝ} {f : E → ℝ}
    (hψ : Differentiable ℝ ψ) (hf : Differentiable ℝ f)
    (hbound : ∀ r, |deriv ψ r| ≤ 1) (x : E) :
    ‖gradient (ψ ∘ f) x‖ ≤ ‖gradient f x‖ := by
  rw [gradient_scalar_outer_comp hψ hf, norm_smul, Real.norm_eq_abs]
  exact mul_le_of_le_one_left (norm_nonneg _) (hbound _)

/-- Actual classical L² functions with L² gradients remain in the genuine
closed Gibbs graph after smooth normal contraction. -/
theorem scalar_normal_comp_classical_graph
    {V f : E → ℝ} (hV : ContDiff ℝ 2 V) (hprob : IsProbabilityMeasure (gibbsMeasure volume V))
    (hf : ContDiff ℝ 2 f) (hfLp : MemLp f 2 (gibbsMeasure volume V))
    (hgLp : MemLp (gradient f) 2 (gibbsMeasure volume V))
    {ψ : ℝ → ℝ} (hψ : ContDiff ℝ 2 ψ) (hψ0 : ψ 0 = 0)
    (hbound : ∀ r, |deriv ψ r| ≤ 1) :
    ∃ (hcomp : MemLp (ψ ∘ f) 2 (gibbsMeasure volume V))
      (hgrad : MemLp (gradient (ψ ∘ f)) 2 (gibbsMeasure volume V)),
      (hcomp.toLp (ψ ∘ f), hgrad.toLp (gradient (ψ ∘ f))) ∈ (closedGibbsGradient hV hprob).graph := by
  have hψd := hψ.differentiable (by norm_num)
  have hfd := hf.differentiable (by norm_num)
  have hcLp := (scalar_normal_contraction_lipschitz hψd hbound).comp_memLp hψ0 hfLp
  have hcG : MemLp (gradient (ψ ∘ f)) 2 (gibbsMeasure volume V) := by
    apply hgLp.of_le_mul (c := 1)
      (continuous_gradient_of_c1 ((hψ.comp hf).of_le (by norm_num))).aestronglyMeasurable
    exact Filter.Eventually.of_forall (fun x => by
      simpa only [one_mul] using norm_gradient_scalar_normal_comp_le hψd hfd hbound x)
  exact ⟨hcLp, hcG, c2_function_mem_closedGibbsGradient_graph hV hprob (hψ.comp hf) hcLp hcG⟩

end CutoffRigidity
