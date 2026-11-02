module

public import CutoffRigidity.Extra.Sphere6
public import CutoffRigidity.Extra.Sphere7

/-! # Sphere, stage 8: a probability measure on `S^d` with `IsWeightedVolume`, and `d - 1 ≤ λ₁` -/

@[expose] public section

open Bundle Filter Set VectorField MeasureTheory
open scoped Manifold ContDiff Topology

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

namespace CutoffRigidity.Extra.Sphere

open CutCur CutoffRigidity CutoffRigidity.Extra

namespace Sph

variable (d : ℕ)

local notation "𝔼" => EuclideanSpace ℝ (Fin (d + 1))
local notation "Fd" => EuclideanSpace ℝ (Fin d)

lemma chart_source_compl_subsingleton (x : Sph d) : ((chartAt Fd x).source)ᶜ.Subsingleton := by
  have h : (chartAt Fd x).source = ({-(show Metric.sphere (0 : 𝔼) 1 from x)})ᶜ :=
    stereographic'_source (E := 𝔼) (n := d) (-(show Metric.sphere (0 : 𝔼) 1 from x))
  rw [h, compl_compl]
  exact Set.subsingleton_singleton

lemma hnull_sph (hd : 1 ≤ d) (x₁ x₀ : Sph d) :
    volume ((chartAt Fd x₀) '' ((chartAt Fd x₀).source ∩ ((chartAt Fd x₁).source)ᶜ)) = 0 := by
  have : Nontrivial Fd := by
    have : NeZero d := ⟨by omega⟩
    infer_instance
  have hs : ((chartAt Fd x₀) '' ((chartAt Fd x₀).source ∩ ((chartAt Fd x₁).source)ᶜ)).Subsingleton :=
    (Set.Subsingleton.anti (chart_source_compl_subsingleton d x₁) inter_subset_right).image _
  exact hs.measure_zero volume

/-- **A probability measure on the round sphere with `IsWeightedVolume`** (the normalized Riemannian volume,
`μ = e^{-c} vol_g` for a constant `c`). -/
theorem exists_isWeightedVolume (hd : 1 ≤ d) :
    ∃ (μ : Measure (Sph d)) (c : ℝ), IsProbabilityMeasure μ ∧ IsWeightedVolume Fd μ (fun _ => c) := by
  have : Nonempty (Sph d) := ⟨⟨EuclideanSpace.single 0 1, by simp⟩⟩
  exact exists_probability_isWeightedVolume (F := Fd) (Classical.arbitrary (Sph d)) (hnull_sph d hd _)

end Sph

end CutoffRigidity.Extra.Sphere
