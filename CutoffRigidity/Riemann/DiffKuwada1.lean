module

public import CutoffRigidity.Riemann.WeightedGradHelpers

/-! # Interpolation along a `C^1` curve: calculus on `M` -/

@[expose] public section

open Bundle MeasureTheory Filter Set Topology
open scoped Manifold ContDiff ENNReal NNReal Topology

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace CutoffRigidity.Riemann.Diff

open CutCur

section Curve

variable (F : Type) [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  {M : Type} [EMetricSpace M] [ChartedSpace F M] [IsManifold 𝓘(ℝ, F) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, F) ∞ F (fun x : M => TangentSpace 𝓘(ℝ, F) x)]

include F

theorem hasDerivAt_comp_curve {γ : ℝ → M} (hγ : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, F) 1 γ)
    {U : M → ℝ} (hU : MSmooth F U) (s : ℝ) :
    HasDerivAt (fun t => U (γ t)) (mvfderiv 𝓘(ℝ, F) U (γ s) (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, F) γ s 1)) s := by
  have h1 : MDifferentiableAt 𝓘(ℝ, F) 𝓘(ℝ, ℝ) U (γ s) :=
    (hU.mdifferentiable (by simp)) _
  have h2 : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, F) γ s := (hγ.mdifferentiable (by simp)) _
  have h3 := h1.hasMFDerivAt.comp s h2.hasMFDerivAt
  have h4 := (hasMFDerivAt_iff_hasFDerivAt.1 h3).hasDerivAt
  exact h4

theorem continuous_speed {γ : ℝ → M} (hγ : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, F) 1 γ) :
    Continuous (fun τ : ℝ => ‖mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, F) γ τ 1‖) := by
  have := isContinuousRiemannianBundle_tangent (F := F) (M := M)
  have hc : Continuous (fun τ : ℝ =>
      (⟨γ τ, mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, F) γ τ 1⟩ : TotalSpace F (fun x : M => TangentSpace 𝓘(ℝ, F) x))) :=
    (hγ.continuous_tangentMap le_rfl).comp
      (((tangentBundleModelSpaceHomeomorph 𝓘(ℝ, ℝ) (H := ℝ)).symm.continuous).comp
        (continuous_id.prodMk continuous_const) :
        Continuous (fun τ : ℝ => (⟨τ, (1:ℝ)⟩ : TangentBundle 𝓘(ℝ, ℝ) ℝ)))
  have h2 : Continuous (fun τ : ℝ => inner ℝ (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, F) γ τ 1)
      (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, F) γ τ 1)) :=
    Continuous.inner_bundle (E := fun x : M => TangentSpace 𝓘(ℝ, F) x) hc hc
  have h3 := Real.continuous_sqrt.comp h2
  refine h3.congr (fun x => ?_)
  simp [Real.sqrt_sq (norm_nonneg _)]

theorem curve_mvt {γ : ℝ → M} (hγ : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, F) 1 γ)
    {U : M → ℝ} (hU : MSmooth F U) {τ z B : ℝ} (hτz : τ ≤ z)
    (hB : ∀ s ∈ Icc τ z, ‖mgrad F U (γ s)‖ * ‖mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, F) γ s 1‖ ≤ B) :
    U (γ z) - U (γ τ) ≤ B * (z - τ) := by
  have key := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := fun t => U (γ t)) (s := Icc τ z) (C := B)
    (f' := fun s => mvfderiv 𝓘(ℝ, F) U (γ s) (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, F) γ s 1))
    (fun s _ => (hasDerivAt_comp_curve F hγ hU s).hasDerivWithinAt)
    (fun s hs => by
      rw [Real.norm_eq_abs]
      exact (abs_mvfderiv_le_norm_mgrad F U _ _).trans (hB s hs))
    (convex_Icc τ z) (left_mem_Icc.2 hτz) (right_mem_Icc.2 hτz)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.2 hτz)] at key
  exact (le_abs_self _).trans key

end Curve
end CutoffRigidity.Riemann.Diff
