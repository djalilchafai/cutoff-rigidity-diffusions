module

public import CutoffRigidity.Extra.Sphere8
public import CutoffRigidity.Extra.Sphere10

/-! # Sphere, stage 11: `d - 1 ≤ λ₁ ≤ d` on the actual round sphere `S^d` -/

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

/-- **`d - 1 ≤ λ₁ ≤ d` on the round sphere `S^d`** (`d ≥ 2`), for every probability measure with
`IsWeightedVolume` (constant potential), i.e. the normalized Riemannian volume. -/
theorem gap_bounds (hd : 2 ≤ d) {μ : Measure (Sph d)} [IsProbabilityMeasure μ] {c : ℝ}
    (hμ : IsWeightedVolume Fd μ (fun _ => c)) :
    (d : ℝ) - 1 ≤ mSpectralGap Fd μ ∧ mSpectralGap Fd μ ≤ d := by
  haveI := connectedSpace d (by omega)
  refine ⟨?_, sphere_gap_le (finrank_model d) (by omega) (isIsometricSphereMap d) hμ⟩
  refine CutoffRigidity.Paper.mSpectralGap_ge_of_CD Fd (by rw [finrank_model]; omega)
    (contMDiff_const (c := c)) hμ ?_ (CD_sphere d c)
  have : (2 : ℝ) ≤ d := by exact_mod_cast hd
  linarith

end Sph

end CutoffRigidity.Extra.Sphere
