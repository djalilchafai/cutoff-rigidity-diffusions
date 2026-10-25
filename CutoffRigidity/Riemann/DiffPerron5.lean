module

public import CutoffRigidity.Riemann.DiffPerron4
public import CutoffRigidity.Riemann.DiffKer

/-! # Final composition: `Pt = Kk` for every diffusion semigroup

* `minimalResolvent_Kk`: the canonical kernel `Kk F hV hμ` of `exists_kernel` has the Perron
  property `MinimalResolvent`;
-/

@[expose] public section

open Bundle MeasureTheory Filter Set ProbabilityTheory
open scoped Manifold ContDiff ENNReal Topology NNReal

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
  {V : M → ℝ} (hV : MSmooth F V) {μ : Measure M} [IsFiniteMeasure μ]
  (hμ : IsWeightedVolume F μ V)

theorem resolventRepr_Kk : ResolventRepr F hV hμ (Kk F hV hμ) :=
  fun _ hlam g hg hc => resolvent_repr F hV hμ hlam g hg hc

/-- **`minimalResolvent_of_canonical`**: the canonical kernel has the Perron property. -/
theorem minimalResolvent_Kk : MinimalResolvent F V (Kk F hV hμ) :=
  minimalResolvent_of_repr F hV hμ (resolventRepr_Kk F hV hμ)

end Final

end CutoffRigidity.Riemann.Diff
