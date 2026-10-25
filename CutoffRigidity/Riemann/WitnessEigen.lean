module

public import CutoffRigidity.Riemann.WitnessGap
public import CutoffRigidity.Paper.GaussianFactorization
public import CutoffRigidity.EigenfunctionC2Rigidity
public import CutoffRigidity.EuclideanGaussianSplitting
public import CutoffRigidity.FirstEigenspaceAffineCoordinates

/-! # Witness (part 5): the first eigenspace of the Gaussian on `ℝ^k` has dimension `k` -/

@[expose] public section

open Bundle MeasureTheory ProbabilityTheory
open scoped Manifold ContDiff ENNReal NNReal Topology

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

namespace CutoffRigidity.Riemann.Witness

open CutCur CutoffRigidity

variable {k : ℕ}

/-- The eigen-row space of the Gaussian potential is everything. -/
theorem affineEigenRows_gaussPot (ρ : ℝ) : affineEigenRows (gaussPot k ρ) ρ = ⊤ := by
  refine Submodule.eq_top_iff'.2 fun a x => ?_
  change inner ℝ a (gradient (gaussPot k ρ) x - gradient (gaussPot k ρ) 0) = ρ * inner ℝ a x
  rw [gradient_gaussPot, gradient_gaussPot]
  simp [inner_smul_right]

/-- `k₁ = k` for the Euclidean Gaussian. -/
theorem firstEigenDim_gaussPot (ρ : ℝ) (hρ : 0 < ρ) (hk : 0 < k) :
    CutCur.firstEigenDim (gaussPot k ρ) = k := by
  have hV := contDiff_gaussPot (k := k) ρ
  have hV2 : ContDiff ℝ 2 (gaussPot k ρ) := hV.of_le (by norm_cast)
  have hp : IsProbabilityMeasure (gibbsMeasure volume (gaussPot k ρ)) :=
    isProbabilityMeasure_gibbs_gaussPot ρ hρ
  have hHess : ∀ x z : Rd k, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ (gaussPot k ρ)) x z z := fun x z =>
    (hessian_gaussPot ρ x z).ge
  have hgap := spectralGap_gaussPot (k := k) ρ hρ hk
  have hrig : CutCur.RigidCurvature (gaussPot k ρ) :=
    ⟨by rw [hgap]; exact hρ, fun x z => by rw [hgap]; exact hHess x z⟩
  have hG : gibbsSpectralGap hV2 hp = ρ := by
    have := Paper.spectralGap_eq_gibbsSpectralGap hV2 hp hrig
    rw [hgap] at this
    exact this.symm
  have hdim := firstEigenspace_finrank_eq_affine_rows hV2 hp ρ hρ hHess hG
  rw [Paper.firstEigenDim_eq hV2 hp hrig, hdim, affineEigenRows_gaussPot]
  simp

/-- Manifold-side eigenfunctions on flat `ℝ^k` are the Euclidean ones. -/
theorem isMEigenfunction_iff_gaussPot (ρ : ℝ) (hρ : 0 < ρ) (f : Rd k → ℝ) :
    IsMEigenfunction (Rd k) (gibbs (gaussPot k ρ)) (gaussPot k ρ) ρ f ↔
      CutCur.IsEigenfunction (gaussPot k ρ) ρ f := by
  have hV := contDiff_gaussPot (k := k) ρ
  have hV2 : ContDiff ℝ 2 (gaussPot k ρ) := hV.of_le (by norm_cast)
  have hHess : ∀ x z : Rd k, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ (gaussPot k ρ)) x z z := fun x z =>
    (hessian_gaussPot ρ x z).ge
  constructor
  · rintro ⟨hf, hL, he⟩
    have hf' : ContDiff ℝ ∞ f := contMDiff_iff_contDiff.1 hf
    have hf2 : ContDiff ℝ 2 f := hf'.of_le (by norm_cast)
    refine ⟨hf2, hL, fun x => ?_⟩
    rw [Paper.generator_eq_langevinDifferentialOperator _ hf2]
    rw [← mgenerator_rd hf2]
    exact he x
  · rintro ⟨hf2, hL, he⟩
    have he' : ∀ x, langevinDifferentialOperator (gaussPot k ρ) f x = -ρ * f x := fun x => by
      rw [← Paper.generator_eq_langevinDifferentialOperator _ hf2]; exact he x
    have hp : IsProbabilityMeasure (gibbsMeasure volume (gaussPot k ρ)) :=
      isProbabilityMeasure_gibbs_gaussPot ρ hρ
    have haff := c2_L2_eigenfunction_is_affine hV2 hf2 hL ρ hρ.le hHess he'
    have hfe : f = fun x => f 0 + inner ℝ (gradient f 0) x := funext haff
    have hf' : ContDiff ℝ ∞ f := by
      rw [hfe]
      exact contDiff_const.add (innerSL ℝ (gradient f 0)).contDiff
    refine ⟨contMDiff_iff_contDiff.2 hf', hL, fun x => ?_⟩
    rw [mgenerator_rd hf2]
    exact he' x

/-- `k₁ = k` on the manifold side: `mFirstEigenDim = k` for the Gaussian on flat `ℝ^k`. -/
theorem mFirstEigenDim_gaussPot (ρ : ℝ) (hρ : 0 < ρ) (hk : 0 < k) :
    mFirstEigenDim (Rd k) (gibbs (gaussPot k ρ)) (gaussPot k ρ) = k := by
  have hgap : mSpectralGap (Rd k) (gibbs (gaussPot k ρ)) = ρ := by
    rw [mSpectralGap_rd, spectralGap_gaussPot ρ hρ hk]
  refine Eq.trans ?_ (firstEigenDim_gaussPot ρ hρ hk)
  rw [CutCur.firstEigenDim, CutCur.firstEigenspace, spectralGap_gaussPot ρ hρ hk, mFirstEigenDim,
    hgap]
  have hS : {u : Rd k →₂[gibbs (gaussPot k ρ)] ℝ | ∃ f, IsMEigenfunction (Rd k)
      (gibbs (gaussPot k ρ)) (gaussPot k ρ) ρ f ∧ f =ᵐ[gibbs (gaussPot k ρ)] u} =
      {u : Rd k →₂[gibbs (gaussPot k ρ)] ℝ | ∃ f, CutCur.IsEigenfunction (gaussPot k ρ) ρ f ∧
        f =ᵐ[gibbs (gaussPot k ρ)] u} := by
    ext u
    constructor
    · rintro ⟨f, hf, hae⟩
      exact ⟨f, (isMEigenfunction_iff_gaussPot ρ hρ f).1 hf, hae⟩
    · rintro ⟨f, hf, hae⟩
      exact ⟨f, (isMEigenfunction_iff_gaussPot ρ hρ f).2 hf, hae⟩
  rw [hS]

end CutoffRigidity.Riemann.Witness
