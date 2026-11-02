module

public import CutoffRigidity.Extra.C2Uniq6

/-! # `C²` uniqueness, stage 6: `C2Uniqueness V` for convex `C²` potentials -/

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace CutCur

open MeasureTheory ProbabilityTheory Filter Topology Set
open Bundle
open scoped ENNReal NNReal ContDiff Manifold

namespace C2U

variable {d : ℕ} {V : Rd d → ℝ}

theorem eq_of_integral_smooth {μ ν : Measure (Rd d)} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (h : ∀ g : Rd d → ℝ, ContDiff ℝ ∞ g → HasCompactSupport g → ∫ y, g y ∂μ = ∫ y, g y ∂ν) :
    μ = ν := by
  have hcut : WeightedCutoffs (Rd d) (Rd d) := weightedCutoffs_of_complete (Rd d)
  haveI : SigmaCompactSpace (Rd d) := inferInstance
  exact CutoffRigidity.Riemann.Diff.measure_eq_of_integral_smooth (Rd d) hcut (fun g hg hgc =>
    h g (contMDiff_iff_contDiff.1 hg) hgc)


/-- **`C²` uniqueness** (convex case): two Euclidean diffusion semigroups of a convex `C²` potential
coincide. No assumption on the Gibbs measure is needed. -/
theorem euclideanDiffusion_unique_convex {P₁ P₂ : ℝ≥0 → Kernel (Rd d) (Rd d)}
    (hV : ContDiff ℝ 2 V) (hc : ConvexOn ℝ univ V)
    (h₁ : IsEuclideanDiffusion V P₁) (h₂ : IsEuclideanDiffusion V P₂) (t : ℝ≥0) (x : Rd d) :
    P₁ t x = P₂ t x := by
  have hV1 : ContDiff ℝ 1 V := hV.of_le (by norm_cast)
  haveI : IsProbabilityMeasure (P₁ t x) := (h₁.1 t).isProbabilityMeasure x
  haveI : IsProbabilityMeasure (P₂ t x) := (h₂.1 t).isProbabilityMeasure x
  refine eq_of_integral_smooth fun g hg hgc => ?_
  obtain ⟨B, hB⟩ := hg.continuous.bounded_above_of_compact_support hgc
  have hB' : ∀ y, |g y| ≤ B := fun y => by simpa [Real.norm_eq_abs] using hB y
  set φ : ℝ → ℝ := fun s => (∫ y, g y ∂P₁ s.toNNReal x) - ∫ y, g y ∂P₂ s.toNNReal x with hφ
  have hφc : Continuous φ :=
    (continuous_semi_cs_real h₁ hV1 hg.continuous hgc x).sub
      (continuous_semi_cs_real h₂ hV1 hg.continuous hgc x)
  have hφb : ∀ s, |φ s| ≤ B + B := fun s =>
    (abs_sub _ _).trans (add_le_add (abs_integral_le_of_bound h₁ hB' _ x) (abs_integral_le_of_bound h₂ hB' _ x))
  have hz : ∀ m : ℕ, ∫ s in Ioi (0 : ℝ), Real.exp (-((m : ℝ) + 2) * s) * φ s = 0 := by
    intro m
    have hl : (0 : ℝ) < (m : ℝ) + 2 := by positivity
    have h1 := resU_eq hV hc h₁ h₂ hl hg hgc x
    unfold resU at h1
    have : ∫ s in Ioi (0 : ℝ), Real.exp (-((m : ℝ) + 2) * s) * φ s =
        (∫ s in Ioi (0 : ℝ), Real.exp (-((m : ℝ) + 2) * s) * ∫ y, g y ∂P₁ s.toNNReal x) -
        ∫ s in Ioi (0 : ℝ), Real.exp (-((m : ℝ) + 2) * s) * ∫ y, g y ∂P₂ s.toNNReal x := by
      rw [← integral_sub (resU_integrableOn h₁ hV1 hg.continuous hgc hl x)
        (resU_integrableOn h₂ hV1 hg.continuous hgc hl x)]
      refine integral_congr_ae (Eventually.of_forall fun s => ?_)
      simp only [hφ, mul_sub]
    rw [this, h1, sub_self]
  have := CutoffRigidity.Riemann.Diff.laplace_unique hφc hφb hz (t : ℝ) t.2
  simpa [hφ, sub_eq_zero] using this

/-- Uniqueness of the Euclidean diffusion semigroup of `V` (same statement as `C2Uniqueness V` of
`C2Langevin.lean`, whose body is not exposed to importers, hence restated here). -/
def C2Unique {d : ℕ} (V : Rd d → ℝ) : Prop :=
  ∀ P₁ P₂ : ℝ≥0 → Kernel (Rd d) (Rd d), IsEuclideanDiffusion V P₁ → IsEuclideanDiffusion V P₂ →
    ∀ t x, P₁ t x = P₂ t x

/-- **`C²` uniqueness for convex potentials** (`Hess V ≥ 0`). -/
theorem c2Unique_of_convex (hV : ContDiff ℝ 2 V)
    (hHess : ∀ x z : Rd d, 0 ≤ fderiv ℝ (fderiv ℝ V) x z z) : C2Unique V := by
  intro P₁ P₂ h₁ h₂ t x
  exact euclideanDiffusion_unique_convex hV
    (CutoffRigidity.NoBm.convexOn_univ_of_hessian_nonneg hV hHess) h₁ h₂ t x

end C2U

end CutCur
