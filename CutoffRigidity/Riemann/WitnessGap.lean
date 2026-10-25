module

public import CutoffRigidity.Riemann.WitnessGauss
public import CutoffRigidity.Paper.GapUpper
public import CutoffRigidity.GibbsOperatorCurvatureGap

/-! # Witness (part 4): spectral gap of the Gaussian on `ℝ^k`

`CutCur.spectralGap (gaussPot k ρ) = ρ` (upper bound by the affine eigenfunction `⟨e₀, x⟩`,
lower bound by the Bakry-Émery bound of the library), and its transfer to the manifold-side
`mSpectralGap`.
-/

@[expose] public section

open Bundle MeasureTheory ProbabilityTheory
open scoped Manifold ContDiff ENNReal NNReal Topology

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

namespace CutoffRigidity.Riemann.Witness

open CutCur CutoffRigidity

variable {k : ℕ}

theorem spectralGap_gaussPot (ρ : ℝ) (hρ : 0 < ρ) (hk : 0 < k) :
    CutCur.spectralGap (gaussPot k ρ) = ρ := by
  have hV := contDiff_gaussPot (k := k) ρ
  have hV2 : ContDiff ℝ 2 (gaussPot k ρ) := hV.of_le (by norm_cast)
  have hp : IsProbabilityMeasure (gibbsMeasure volume (gaussPot k ρ)) :=
    isProbabilityMeasure_gibbs_gaussPot ρ hρ
  have hHess : ∀ x z : Rd k, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ (gaussPot k ρ)) x z z := fun x z =>
    (hessian_gaussPot ρ x z).ge
  let a : Rd k := EuclideanSpace.single ⟨0, hk⟩ 1
  have ha : a ≠ 0 := by
    intro h
    have := congrArg (fun v : Rd k => v ⟨0, hk⟩) h
    simp [a] at this
  have heigen : ∀ x : Rd k, langevinDifferentialOperator (gaussPot k ρ)
      (fun y => inner ℝ a y + 0) x = -ρ * (inner ℝ a x + 0) := by
    rw [affine_eigenfunction_iff_drift]
    intro x
    rw [gradient_gaussPot, inner_smul_right, add_zero]
  obtain ⟨hne, hle⟩ := Paper.spectralGap_le_of_affine_eigenfunction_aux
    (hV.differentiable (by simp)) a ha ρ hρ heigen hp
  refine le_antisymm hle ?_
  rw [CutCur.spectralGap]
  refine le_csInf hne ?_
  rintro r ⟨g, hg, hgc, hvar, rfl⟩
  rw [le_div_iff₀ hvar]
  have h1 := gibbsSpectralGap_ge_curvature hV2 hp hk ρ hρ hHess
  have h2 := Paper.gibbsSpectralGap_mul_variance_le hV2 hp hk ρ hρ hHess hg hgc
  nlinarith [variance_nonneg g (CutCur.gibbs (gaussPot k ρ))]

/-- The manifold-side gap on flat space is the Euclidean one. -/
theorem mSpectralGap_rd (V : Rd k → ℝ) :
    mSpectralGap (Rd k) (gibbs V) = CutCur.spectralGap V := by
  unfold mSpectralGap CutCur.spectralGap
  congr 1
  ext r
  simp only [Set.mem_ofPred_eq]
  constructor
  · rintro ⟨f, hf, hc, hv, hr⟩
    refine ⟨f, contMDiff_iff_contDiff.1 hf, hc, hv, ?_⟩
    rw [hr]
    congr 2
    funext x
    rw [norm_tangentSpace_vectorSpace, mgrad_rd]
  · rintro ⟨f, hf, hc, hv, hr⟩
    refine ⟨f, contMDiff_iff_contDiff.2 hf, hc, hv, ?_⟩
    rw [hr]
    congr 2
    funext x
    rw [norm_tangentSpace_vectorSpace, mgrad_rd]

end CutoffRigidity.Riemann.Witness
