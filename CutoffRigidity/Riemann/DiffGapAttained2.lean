module

public import CutoffRigidity.Riemann.DiffRellich
public import CutoffRigidity.Riemann.DiffTight
public import CutoffRigidity.Riemann.DiffGapAttained

/-! # Attainment of the spectral gap from the log-Sobolev inequality (workstream HPOS)

`gap_attained_of_LSI`: under `LSI F V μ ρ` (to be supplied by the Bakry-Emery workstream), the spectral
gap `ρ` is attained, i.e. `0 < mFirstEigenDim F μ V`.
-/

@[expose] public section

open Bundle MeasureTheory Filter Set
open scoped Manifold ContDiff ENNReal Topology

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace CutoffRigidity.Riemann.Diff

open CutCur

section Final

variable (F : Type) [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]
  {M : Type} [EMetricSpace M] [ChartedSpace F M] [IsManifold 𝓘(ℝ, F) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, F) ∞ F (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [MeasurableSpace M] [BorelSpace M]
  [IsRiemannianManifold 𝓘(ℝ, F) M] [ConnectedSpace M] [CompleteSpace M]
  {V : M → ℝ} (hV : MSmooth F V) {μ : Measure M} [IsProbabilityMeasure μ]
  (hμ : IsWeightedVolume F μ V) {ρ : ℝ} (hρ : 0 < ρ) (hCD : CD F ρ V)
  (hgap : mSpectralGap F μ = ρ)

include hV hμ hρ hCD hgap in
/-- **Attainment of the spectral gap from LSI.** -/
theorem gap_attained_of_LSI (hLSI : LSI F V μ ρ) : 0 < mFirstEigenDim F μ V :=
  gap_attained_of_compact F hV hμ hρ hCD hgap
    (Qball_totallyBounded_of_tail F hV hμ (fun C ε hε => tail_of_LSI F hρ hLSI C ε hε))

end Final

end CutoffRigidity.Riemann.Diff
