module

public import CutoffRigidity.Extra.Sphere16

/-! # Sphere, stage 17: `hgap` cannot be dropped in `riemannian_k1_bounds`

On the round sphere the conclusion `1 ≤ k₁ ≤ d` fails: `k₁ = 0` violates `1 ≤ k₁`, and `k₁ ≥ 1` makes the first
eigenspace finite-dimensional, which contradicts the `d + 1` independent eigenfunction classes of `Sph.first_eigenspace_large`.
-/

@[expose] public section

open Bundle Filter Set VectorField MeasureTheory
open scoped Manifold ContDiff Topology

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

namespace CutoffRigidity.Extra.Sphere

open CutCur CutoffRigidity CutoffRigidity.Extra

namespace Sph

variable (d : ℕ)

local notation "Fd" => EuclideanSpace ℝ (Fin d)

/-- On the round sphere (`d ≥ 2`, any probability weighted volume), `¬ (1 ≤ k₁ ≤ d)`. -/
theorem k1_fails (hd : 2 ≤ d) {μ : Measure (Sph d)} [IsProbabilityMeasure μ] {c : ℝ}
    (hμ : IsWeightedVolume Fd μ (fun _ => c)) :
    ¬ (1 ≤ mFirstEigenDim Fd μ (fun _ : Sph d => c) ∧
       mFirstEigenDim Fd μ (fun _ : Sph d => c) ≤ d) := by
  rintro ⟨h1, h2⟩
  obtain ⟨u, hu, hmem⟩ := first_eigenspace_large d hd hμ
  have hpos : 0 < Module.finrank ℝ (Submodule.span ℝ
    {u : Sph d →₂[μ] ℝ | ∃ f, IsMEigenfunction Fd μ (fun _ : Sph d => c)
      (mSpectralGap Fd μ) f ∧ f =ᵐ[μ] u}) := h1
  have := Module.finite_of_finrank_pos hpos
  have hin : ∀ i, u i ∈ Submodule.span ℝ
    {u : Sph d →₂[μ] ℝ | ∃ f, IsMEigenfunction Fd μ (fun _ : Sph d => c)
      (mSpectralGap Fd μ) f ∧ f =ᵐ[μ] u} := fun i =>
    Submodule.subset_span (hmem i)
  set W := Submodule.span ℝ
    {u : Sph d →₂[μ] ℝ | ∃ f, IsMEigenfunction Fd μ (fun _ : Sph d => c)
      (mSpectralGap Fd μ) f ∧ f =ᵐ[μ] u} with hW
  have hli : LinearIndependent ℝ (fun i => (⟨u i, hin i⟩ : W)) :=
    LinearIndependent.of_comp W.subtype hu
  have := hli.fintype_card_le_finrank
  have h2' : Module.finrank ℝ W ≤ d := h2
  simp at this
  omega

end Sph

end CutoffRigidity.Extra.Sphere
