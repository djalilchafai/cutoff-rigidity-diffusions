module

public import CutoffRigidity.Extra.Sphere14
public import CutoffRigidity.Extra.Sphere11

/-! # Sphere, stage 15: `λ₁ = d` and `CD(d-1,∞)` on the actual round sphere `S^d`; failure of `hgap`

Final statements for `Sph d` (the unit sphere of `ℝ^{d+1}` with its Riemannian structure in the project's sense).
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

/-- **`λ₁ = d` on the round sphere `S^d`** (`d ≥ 2`): for every probability measure with
`IsWeightedVolume` for a constant potential (i.e. the normalized Riemannian volume). -/
theorem gap_eq (hd : 2 ≤ d) {μ : Measure (Sph d)} [IsProbabilityMeasure μ] {c : ℝ}
    (hμ : IsWeightedVolume Fd μ (fun _ => c)) : mSpectralGap Fd μ = d := by
  haveI := connectedSpace d (by omega)
  exact le_antisymm (gap_bounds d hd hμ).2
    (sphere_gap_ge (finrank_model d) hd (isIsometricSphereMap d) hμ)

/-- The hypothesis `hgap : λ₁ = ρ` fails on the round sphere for the Bakry-Émery constant `ρ = d - 1`. -/
theorem gap_ne_rho (hd : 2 ≤ d) {μ : Measure (Sph d)} [IsProbabilityMeasure μ] {c : ℝ}
    (hμ : IsWeightedVolume Fd μ (fun _ => c)) : mSpectralGap Fd μ ≠ (d : ℝ) - 1 := by
  rw [gap_eq d hd hμ]; intro h; linarith

/-- **The round sphere** (`d ≥ 2`): a probability measure `μ = e^{-c} vol_g` exists, `CD(d-1,∞)` holds, `d - 1` is
the optimal constant, and `λ₁ = d ≠ d - 1`. -/
theorem round_sphere (hd : 2 ≤ d) :
    ∃ (μ : Measure (Sph d)) (c : ℝ), IsProbabilityMeasure μ ∧ IsWeightedVolume Fd μ (fun _ => c) ∧
      CD Fd ((d : ℝ) - 1) (fun _ : Sph d => c) ∧ (∀ ρ : ℝ, (d : ℝ) - 1 < ρ → ¬ CD Fd ρ (fun _ : Sph d => c)) ∧
      mSpectralGap Fd μ = d ∧ mSpectralGap Fd μ ≠ (d : ℝ) - 1 := by
  obtain ⟨μ, c, hP, hμ⟩ := exists_isWeightedVolume d (by omega)
  haveI := hP
  exact ⟨μ, c, hP, hμ, CD_sphere d c, fun ρ hρ => not_CD_sphere d (by omega) c hρ,
    gap_eq d hd hμ, gap_ne_rho d hd hμ⟩

end Sph

end CutoffRigidity.Extra.Sphere
