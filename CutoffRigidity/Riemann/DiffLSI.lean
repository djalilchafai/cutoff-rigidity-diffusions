module

public import CutoffRigidity.Riemann.DiffBEMain
public import CutoffRigidity.Riemann.DiffLSIMain
public import CutoffRigidity.Extra.RiemannLichnerowicz

/-! # Final deliverable of workstream BE: `lsi_of_CD`

Log-Sobolev inequality with constant `ρ` from `CD(ρ,∞)` (Bakry-Emery), for the standing hypotheses
(the Poincare inequality used for ergodicity comes from `poincare_of_CD`, so no spectral-gap hypothesis is needed).
-/

@[expose] public section

open Bundle MeasureTheory ProbabilityTheory Filter Set
open scoped Manifold ContDiff ENNReal NNReal Topology

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

namespace CutoffRigidity.Riemann.Diff

open CutCur

variable (F : Type) [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]
  {M : Type} [EMetricSpace M] [ChartedSpace F M] [IsManifold 𝓘(ℝ, F) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, F) ∞ F (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [MeasurableSpace M] [BorelSpace M]
  [IsRiemannianManifold 𝓘(ℝ, F) M] [ConnectedSpace M] [CompleteSpace M]
  {V : M → ℝ} (hV : MSmooth F V) {μ : Measure M} [IsProbabilityMeasure μ]
  (hμ : IsWeightedVolume F μ V) {ρ : ℝ} (hρ : 0 < ρ) (hCD : CD F ρ V)

include hV hμ hρ hCD in
/-- **Log-Sobolev inequality** `Ent_μ(f²) ≤ (2/ρ) ∫Γf` from `CD(ρ,∞)`. -/
theorem lsi_of_CD : LSI F V μ ρ :=
  lsi_of_strong_BE F (kerCanonical_Kk F hV hμ) hV (CutCur.weightedIBP_of_isWeightedVolume F hV hμ)
    (CutCur.weightedRegular V hV) (CutCur.weightedCutoffs_of_complete F) hρ
    (beStrong_of_CD F hV hμ hρ hCD) (poincare_of_CD F hV hμ hρ hCD)

end CutoffRigidity.Riemann.Diff
