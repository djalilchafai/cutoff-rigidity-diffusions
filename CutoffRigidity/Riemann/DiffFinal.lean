module

public import CutoffRigidity.Riemann.DiffAssembleCanonical
public import CutoffRigidity.Riemann.DiffPerron6
public import CutoffRigidity.Riemann.DiffKuwMain
public import CutoffRigidity.Riemann.DiffLSI
public import CutoffRigidity.Riemann.DiffGapAttained2
public import CutoffRigidity.Riemann.DiffBEMain

/-! # Theorem 1.9 without extra hypotheses

`CutoffRigidity.Paper.riemannian_wasserstein_estimate` has exactly the type of the Challenge
theorem: the only hypotheses on `Pt` is `IsDiffusionSemigroup F V Pt`.  The proof combines

* the identification `Pt = Kk` with the canonical kernel (`bridge_final`),
* the canonical diffusion (`KerCanonical`, Bakry-Emery gradient bound, Kuwada contraction),
* attainment of the gap through the log-Sobolev inequality (`gap_attained_of_LSI`, `lsi_of_CD`),
* the Wasserstein estimate from a canonical diffusion (`riemannian_wasserstein_estimate_of_canonical`).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Bundle
open scoped ENNReal NNReal Manifold ContDiff RealInnerProductSpace
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

namespace CutoffRigidity.Paper

section Riemannian

open CutCur CutoffRigidity.Riemann CutoffRigidity.Riemann.Diff

variable (F : Type) [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]
  {M : Type} [EMetricSpace M] [ChartedSpace F M] [IsManifold 𝓘(ℝ, F) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, F) ∞ F (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [IsRiemannianManifold 𝓘(ℝ, F) M] [ConnectedSpace M] [CompleteSpace M]
  [MeasurableSpace M] [BorelSpace M]

theorem riemannian_wasserstein_estimate {V : M → ℝ} (hV : ContMDiff 𝓘(ℝ, F) 𝓘(ℝ, ℝ) ∞ V)
    {μ : Measure M} [IsProbabilityMeasure μ] (hμ : IsWeightedVolume F μ V) {ρ : ℝ} (hρ : 0 < ρ)
    (hCD : CD F ρ V) (hgap : mSpectralGap F μ = ρ) {Pt : ℝ≥0 → Kernel M M}
    (hP : IsDiffusionSemigroup F V Pt) (t : ℝ≥0) :
    let q := Real.exp (-2 * ρ * t)
    let lower := fun Λ : ℝ≥0∞ => ENNReal.ofReal (q / ρ) * Λ +
      ENNReal.ofReal (mFirstEigenDim F μ V * (1 - Real.sqrt (1 - q)) ^ 2 / ρ)
    let W := fun x₀ => wasserstein2 (Pt t x₀) μ ^ 2
    (∀ S : Set M, S.Nonempty →
      lower (⨆ x₀ ∈ S, mLambda F μ V x₀) ≤ ⨆ x₀ ∈ S, W x₀ ∧
      ⨆ x₀ ∈ S, W x₀ ≤ ENNReal.ofReal q * ⨆ x₀ ∈ S, ∫⁻ x, edist x₀ x ^ 2 ∂μ) ∧
    ∀ (m : M) (R : ℝ), 0 ≤ R → mLambda F μ V m = 0 →
      lower (ENNReal.ofReal (ρ * R ^ 2)) ≤ ⨆ x₀ ∈ {x | edist m x ≤ ENNReal.ofReal R}, W x₀ := by
  have hVs : MSmooth F V := hV
  have hpos : 0 < mFirstEigenDim F μ V :=
    gap_attained_of_LSI F hVs hμ hρ hCD hgap (lsi_of_CD F hVs hμ hρ hCD hgap)
  have hK : CanonicalDiffusion F V μ ρ (Kk F hVs hμ) :=
    KerCanonical.toCanonical F (kerCanonical_Kk F hVs hμ) (gradBound_of_CD F hVs hμ hρ hCD)
      (contraction_of_CD F hVs hμ hρ hCD)
  exact riemannian_wasserstein_estimate_of_canonical F hV hμ hρ hCD hgap hpos (Kk F hVs hμ) hK
    (fun t x => bridge_final F hVs hμ hP t x) t

end Riemannian

end CutoffRigidity.Paper
