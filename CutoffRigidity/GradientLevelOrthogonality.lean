module

public import CutoffRigidity.ParallelGradientProductDiffeomorph

/-! # Actual gradients are orthogonal to actual constant-level tangent maps -/

@[expose] public section
open Bundle Set
open scoped Manifold ContDiff Topology
set_option backward.isDefEq.respectTransparency false

namespace CutoffRigidity
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {K : Type*} [TopologicalSpace K] {J : ModelWithCorners ℝ F K}
  {M P : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [TopologicalSpace P] [ChartedSpace K P]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]

/-- Differentiating an actual constant-level map proves that its actual
tangent image is orthogonal to the actual original gradient. -/
theorem inner_gradient_mfderiv_eq_zero_of_constant
    {f : M → ℝ} {g : P → M} {z : P}
    (hf : MDifferentiableAt I 𝓘(ℝ, ℝ) f (g z)) (hg : MDifferentiableAt J I g z)
    (X : (x : M) → TangentSpace I x)
    (hgrad : ∀ v, mvfderiv I f (g z) v = inner ℝ (X (g z)) v)
    {c : ℝ} (hc : f ∘ g = fun _ ↦ c) (v : TangentSpace J z) :
    inner ℝ (X (g z)) ((mfderiv J I g z) v) = 0 := by
  have hchain := mfderiv_comp z hf hg
  have hzero : @Eq (F →L[ℝ] ℝ) (mfderiv J 𝓘(ℝ, ℝ) (f ∘ g) z) 0 := by
    rw [mfderiv_congr hc, mfderiv_const]
  have hvec := congrArg (fun L : F →L[ℝ] ℝ ↦ L v) (hchain.symm.trans hzero)
  have hscalar := congrArg (NormedSpace.fromTangentSpace (𝕜 := ℝ) (f (g z))) hvec
  change mvfderiv I f (g z) ((mfderiv J I g z) v) = 0 at hscalar
  rw [hgrad] at hscalar
  exact hscalar

end CutoffRigidity
