module

public import CutoffRigidity.Riemann.DiffLSI
public import CutoffRigidity.Extra.Temperature
public import CutoffRigidity.Riemann.WitnessBochner

/-! # Brownian-free logarithmic Sobolev inequality on `ℝ^d` for smooth potentials (step 1)

The Riemannian Bakry-Emery machinery of the project (analytic construction of the diffusion
kernel, no Brownian motion) specialised to flat `ℝ^d`.
-/

public section

open MeasureTheory ProbabilityTheory Set Bundle
open scoped ContDiff ENNReal NNReal Manifold

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

namespace CutoffRigidity.NoBm

variable {d : ℕ}

/-- LSI for smooth compactly supported tests on `ℝ^d`, smooth potential with `Hess V ≥ ρ`. -/
theorem lsi_smooth_compact {V : CutCur.Rd d → ℝ} (hV : ContDiff ℝ ∞ V)
    (hp : IsProbabilityMeasure (CutCur.gibbs V)) {ρ : ℝ} (hρ : 0 < ρ)
    (hH : ∀ x z : CutCur.Rd d, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    {f : CutCur.Rd d → ℝ} (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f) :
    CutCur.entropyOf (CutCur.gibbs V) (fun x => f x ^ 2) ≤
      2 / ρ * ∫ x, ‖gradient f x‖ ^ 2 ∂CutCur.gibbs V := by
  have hVs : CutCur.MSmooth (CutCur.Rd d) V := contMDiff_iff_contDiff.2 hV
  have hCD : CutCur.CD (CutCur.Rd d) ρ V := (CutoffRigidity.Paper.cd_euclid_iff hV ρ).2 hH
  have hL := CutoffRigidity.Riemann.Diff.lsi_of_CD (CutCur.Rd d) hVs
    (CutoffRigidity.Riemann.Witness.isWeightedVolume_gibbs V) hρ hCD
  have := hL ⟨f, contMDiff_iff_contDiff.2 hf, hfc⟩
  simpa [CutoffRigidity.Riemann.Diff.entL, CutCur.entropyOf,
    CutoffRigidity.Riemann.Witness.carre_rd, real_inner_self_eq_norm_sq] using this

end CutoffRigidity.NoBm
