module
public import CutoffRigidity.GibbsHeatGenerator
public import Mathlib.Analysis.InnerProductSpace.Calculus

/-! # Actual canonical heat weak forward equation on genuine compact tests

The initial L² class is arbitrary. Test-domain membership comes from the
actual self-adjoint A graph; compact C² tests use the proved generator
extension, with the paper's L=-A sign.
-/
public section
namespace CutoffRigidity
open MeasureTheory Filter Topology
variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

theorem gibbsHeatSemigroup_weak_integral
    {V : E → ℝ} (hV : ContDiff ℝ 2 V)
    (hprob : IsProbabilityMeasure (gibbsMeasure volume V))
    (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (t : NNReal) (f u g : E →₂[gibbsMeasure volume V] ℝ)
    (hg : (u, g) ∈ (gibbsPositiveGenerator hV hprob).graph) :
    inner ℝ (gibbsHeatSemigroup hV hprob ρ hρ hHess t f) u = inner ℝ f u -
      ∫ s in (0 : ℝ)..(t : ℝ), inner ℝ (gibbsHeatSemigroup hV hprob ρ hρ hHess s.toNNReal f) g := by
  let P := gibbsHeatSemigroup hV hprob ρ hρ hHess
  have hc : Continuous (fun s : ℝ => P s.toNNReal g) :=
    (continuous_gibbsHeatSemigroup_apply hV hprob ρ hρ hHess g).comp continuous_real_toNNReal
  have hcomm := (innerSL ℝ f).intervalIntegral_comp_comm (μ := volume) (hc.intervalIntegrable 0 (t : ℝ))
  change (∫ s in (0 : ℝ)..(t : ℝ), inner ℝ f (P s.toNNReal g)) =
    inner ℝ f (∫ s in (0 : ℝ)..(t : ℝ), P s.toNNReal g) at hcomm
  calc
    _ = inner ℝ f (P t u) := gibbsHeatSemigroup_symmetric hV hprob ρ hρ hHess t f u
    _ = inner ℝ f u - inner ℝ f (∫ s in (0 : ℝ)..(t : ℝ), P s.toNNReal g) := by
      rw [gibbsHeatSemigroup_integral_of_graph hV hprob ρ hρ hHess t u g hg, inner_sub_right]
    _ = _ := by
      rw [← hcomm]
      congr 1
      apply intervalIntegral.integral_congr
      intro s _
      exact (gibbsHeatSemigroup_symmetric hV hprob ρ hρ hHess s.toNNReal f g).symm

theorem gibbsHeatSemigroup_weak_hasDerivWithinAt
    {V : E → ℝ} (hV : ContDiff ℝ 2 V)
    (hprob : IsProbabilityMeasure (gibbsMeasure volume V))
    (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (t : ℝ) (ht : 0 ≤ t) (f u g : E →₂[gibbsMeasure volume V] ℝ)
    (hg : (u, g) ∈ (gibbsPositiveGenerator hV hprob).graph) :
    HasDerivWithinAt (fun s : ℝ => inner ℝ (gibbsHeatSemigroup hV hprob ρ hρ hHess s.toNNReal f) u)
      (-inner ℝ (gibbsHeatSemigroup hV hprob ρ hρ hHess t.toNNReal f) g) (Set.Ici 0) t := by
  have hd := gibbsHeatSemigroup_hasDerivWithinAt_operatorGraph hV hprob ρ hρ hHess t ht u g hg
  have hconst : HasDerivWithinAt (fun _ : ℝ => f) 0 (Set.Ici 0) t := hasDerivWithinAt_const _ _ _
  have he := HasDerivWithinAt.inner ℝ hconst hd
  have hval : inner ℝ f (-gibbsHeatSemigroup hV hprob ρ hρ hHess t.toNNReal g) +
      inner ℝ (0 : E →₂[gibbsMeasure volume V] ℝ) (gibbsHeatSemigroup hV hprob ρ hρ hHess t.toNNReal u) =
      -inner ℝ (gibbsHeatSemigroup hV hprob ρ hρ hHess t.toNNReal f) g := by
    rw [inner_neg_right, inner_zero_left, add_zero, gibbsHeatSemigroup_symmetric]
  rw [hval] at he
  exact he.congr_of_mem
    (fun s _ => gibbsHeatSemigroup_symmetric hV hprob ρ hρ hHess s.toNNReal f u) ht

/-- The true weak forward equation against genuine compact C² tests. -/
theorem gibbsHeatSemigroup_weak_compact_integral
    {V : E → ℝ} (hV : ContDiff ℝ 2 V)
    (hprob : IsProbabilityMeasure (gibbsMeasure volume V))
    (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (t : NNReal) (f : E →₂[gibbsMeasure volume V] ℝ) (φ : compactGibbsGeneratorDomain V) :
    inner ℝ (gibbsHeatSemigroup hV hprob ρ hρ hHess t f) (φ : E →₂[gibbsMeasure volume V] ℝ) =
      inner ℝ f (φ : E →₂[gibbsMeasure volume V] ℝ) +
      ∫ s in (0 : ℝ)..(t : ℝ), inner ℝ (gibbsHeatSemigroup hV hprob ρ hρ hHess s.toNNReal f)
        (compactGibbsGenerator hV hprob φ) := by
  have he := gibbsHeatSemigroup_weak_integral hV hprob ρ hρ hHess t f φ
    (-compactGibbsGenerator hV hprob φ) (compactGibbsGenerator_graph_mem_positiveGenerator hV hprob φ)
  simpa only [inner_neg_right, intervalIntegral.integral_neg, sub_neg_eq_add] using he

/-- The forward derivative uses the actual compact Langevin generator. -/
theorem gibbsHeatSemigroup_weak_compact_hasDerivWithinAt
    {V : E → ℝ} (hV : ContDiff ℝ 2 V)
    (hprob : IsProbabilityMeasure (gibbsMeasure volume V))
    (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (t : ℝ) (ht : 0 ≤ t) (f : E →₂[gibbsMeasure volume V] ℝ) (φ : compactGibbsGeneratorDomain V) :
    HasDerivWithinAt
      (fun s : ℝ => inner ℝ (gibbsHeatSemigroup hV hprob ρ hρ hHess s.toNNReal f) (φ : E →₂[gibbsMeasure volume V] ℝ))
      (inner ℝ (gibbsHeatSemigroup hV hprob ρ hρ hHess t.toNNReal f) (compactGibbsGenerator hV hprob φ)) (Set.Ici 0) t := by
  have he := gibbsHeatSemigroup_weak_hasDerivWithinAt hV hprob ρ hρ hHess t ht f φ
    (-compactGibbsGenerator hV hprob φ) (compactGibbsGenerator_graph_mem_positiveGenerator hV hprob φ)
  simpa only [inner_neg_right, neg_neg] using he

end CutoffRigidity
