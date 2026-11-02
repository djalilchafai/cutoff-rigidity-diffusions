module

public import CutoffRigidity.Extra.Sphere4
public import CutoffRigidity.Riemann.SplitMetric

/-! # Sphere, stage 5: the actual round sphere `S^d ⊂ ℝ^{d+1}` as a Riemannian manifold in the project's sense

`Sph d` is `Metric.sphere (0 : ℝ^{d+1}) 1` as a new type, carrying Mathlib's smooth structure (stereographic
charts, model `ℝ^d`), the Riemannian metric induced by the inclusion (project's `immersionPullbackRiemannianBundle`,
smooth of order `∞`) and the Riemannian distance (`EMetricSpace.ofRiemannianMetric`, which makes
`IsRiemannianManifold` true by construction).  We show `Ric = (d-1) g` and `CD(d-1,∞)` on it.
-/

@[expose] public section

open Bundle Filter Set VectorField MeasureTheory
open scoped Manifold ContDiff Topology

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

namespace CutoffRigidity.Extra.Sphere

open CutCur CutCur.WBoch CutoffRigidity CutoffRigidity.Extra

/-- The unit sphere of `ℝ^{d+1}` (a type synonym, to carry the Riemannian distance). -/
def Sph (d : ℕ) : Type := Metric.sphere (0 : EuclideanSpace ℝ (Fin (d + 1))) 1

namespace Sph

variable (d : ℕ)

local notation "𝔼" => EuclideanSpace ℝ (Fin (d + 1))
local notation "Fd" => EuclideanSpace ℝ (Fin d)

instance fact_finrank : Fact (Module.finrank ℝ 𝔼 = d + 1) := ⟨by simp⟩

instance : TopologicalSpace (Sph d) := inferInstanceAs (TopologicalSpace (Metric.sphere (0 : 𝔼) 1))
instance : T3Space (Sph d) := inferInstanceAs (T3Space (Metric.sphere (0 : 𝔼) 1))
instance : CompactSpace (Sph d) := inferInstanceAs (CompactSpace (Metric.sphere (0 : 𝔼) 1))
noncomputable instance : ChartedSpace Fd (Sph d) := inferInstanceAs (ChartedSpace Fd (Metric.sphere (0 : 𝔼) 1))
instance : IsManifold 𝓘(ℝ, Fd) ∞ (Sph d) := inferInstanceAs (IsManifold 𝓘(ℝ, Fd) ∞ (Metric.sphere (0 : 𝔼) 1))
instance : BoundarylessManifold 𝓘(ℝ, Fd) (Sph d) :=
  inferInstanceAs (BoundarylessManifold 𝓘(ℝ, Fd) (Metric.sphere (0 : 𝔼) 1))
instance : MeasurableSpace (Sph d) := inferInstanceAs (MeasurableSpace (Metric.sphere (0 : 𝔼) 1))
instance : BorelSpace (Sph d) := inferInstanceAs (BorelSpace (Metric.sphere (0 : 𝔼) 1))

/-- The inclusion `S^d → ℝ^{d+1}`. -/
def val (x : Sph d) : 𝔼 := Subtype.val (p := fun y => y ∈ Metric.sphere (0 : 𝔼) 1) x

lemma contMDiff_val : ContMDiff 𝓘(ℝ, Fd) 𝓘(ℝ, 𝔼) ∞ (val d) :=
  contMDiff_coe_sphere (E := 𝔼) (n := d)

lemma injective_mfderiv_val (x : Sph d) :
    Function.Injective (mfderiv 𝓘(ℝ, Fd) 𝓘(ℝ, 𝔼) (val d) x) :=
  injective_mvfderiv_subtypeVal_sphere (E := 𝔼) (n := d) x

noncomputable instance : RiemannianBundle (fun x : Sph d => TangentSpace 𝓘(ℝ, Fd) x) :=
  immersionPullbackRiemannianBundle (val d) (injective_mfderiv_val d)

set_option synthInstance.maxHeartbeats 400000 in
instance : IsContMDiffRiemannianBundle 𝓘(ℝ, Fd) ∞ Fd (fun x : Sph d => TangentSpace 𝓘(ℝ, Fd) x) :=
  CutoffRigidity.Riemann.isContMDiffRiemannianBundle_immersionPullback_top (val d)
    (contMDiff_val d) (injective_mfderiv_val d)

instance : IsContinuousRiemannianBundle Fd (fun x : Sph d => TangentSpace 𝓘(ℝ, Fd) x) :=
  by
    obtain ⟨g, hg, hgg⟩ := (inferInstance : IsContMDiffRiemannianBundle 𝓘(ℝ, Fd) ∞ Fd
      (fun x : Sph d => TangentSpace 𝓘(ℝ, Fd) x)).exists_contMDiff
    exact ⟨g, hg.continuous, hgg⟩

end Sph

end CutoffRigidity.Extra.Sphere
