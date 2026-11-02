module

public import CutoffRigidity.Extra.Sphere5

/-! # Sphere, stage 6: the Riemannian distance, completeness, connectedness; `CD(d-1,∞)` on the actual sphere -/

@[expose] public section

open Bundle Filter Set VectorField MeasureTheory
open scoped Manifold ContDiff Topology

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

namespace CutoffRigidity.Extra.Sphere

open CutCur CutCur.WBoch CutoffRigidity CutoffRigidity.Extra

namespace Sph

variable (d : ℕ)

local notation "𝔼" => EuclideanSpace ℝ (Fin (d + 1))
local notation "Fd" => EuclideanSpace ℝ (Fin d)

set_option maxHeartbeats 2000000 in
set_option synthInstance.maxHeartbeats 400000 in
/-- The extended distance of `S^d` is its Riemannian distance. -/
noncomputable instance : EMetricSpace (Sph d) := EMetricSpace.ofRiemannianMetric 𝓘(ℝ, Fd) (Sph d)

instance : IsRiemannianManifold 𝓘(ℝ, Fd) (Sph d) := ⟨fun _ _ => rfl⟩

instance : CompleteSpace (Sph d) := inferInstance

lemma connectedSpace (hd : 1 ≤ d) : ConnectedSpace (Sph d) := by
  have h : 1 < Module.rank ℝ 𝔼 := by
    rw [← Module.finrank_eq_rank, finrank_euclideanSpace_fin]
    exact_mod_cast Nat.succ_lt_succ (Nat.lt_of_succ_le hd)
  have := isConnected_sphere h (0 : 𝔼) (r := 1) zero_le_one
  exact (isConnected_iff_connectedSpace.mp this : ConnectedSpace (Metric.sphere (0 : 𝔼) 1))

/-- `val : S^d → ℝ^{d+1}` is an isometric immersion into the unit sphere (Item6a's format). -/
lemma isIsometricSphereMap : IsIsometricSphereMap Fd (val d) := by
  refine ⟨fun x => ?_, contMDiff_val d, fun x v w => rfl⟩
  have := x.2
  simp [val]

lemma finrank_model : Module.finrank ℝ Fd = d := by simp

/-- **`Ric = (d-1) g` on the round sphere `S^d`**, for the project's `mRic`. -/
theorem mRic_eq (x : Sph d) (v w : TangentSpace 𝓘(ℝ, Fd) x) :
    mRic Fd x v w = ((d : ℝ) - 1) * inner ℝ v w :=
  sphere_mRic (finrank_model d) (isIsometricSphereMap d) x v w

/-- **`CD(d-1, ∞)` on the round sphere `S^d`** (any constant potential, i.e. the Laplace-Beltrami generator). -/
theorem CD_sphere (c : ℝ) : CD Fd ((d : ℝ) - 1) (fun _ : Sph d => c) :=
  sphere_CD (finrank_model d) (isIsometricSphereMap d) c

/-- `ρ = d - 1` is optimal on `S^d` (`d ≥ 1`). -/
theorem not_CD_sphere (hd : 1 ≤ d) (c : ℝ) {ρ : ℝ} (hρ : (d : ℝ) - 1 < ρ) :
    ¬ CD Fd ρ (fun _ : Sph d => c) := by
  have : Nonempty (Sph d) := ⟨⟨EuclideanSpace.single 0 1, by simp⟩⟩
  exact sphere_not_CD (finrank_model d) hd (isIsometricSphereMap d) (Classical.arbitrary _) c hρ

end Sph

end CutoffRigidity.Extra.Sphere
