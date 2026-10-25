module

public import CutoffRigidity.Riemann.DiffPerron5
public import CutoffRigidity.Riemann.DiffBridge1

/-! # Final composition: `Pt = Kk` for every diffusion semigroup

`bridge_final`: every `Pt` with `IsDiffusionSemigroup F V Pt` equals the canonical kernel
`Kk F hV hμ` of `exists_kernel`.  (This module imports both `DiffKer` and `DiffBridge1`; the two
define `continuous_semi_time`, see `riemann-status/diff-PERRON.md`.)
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

/-- **`bridge_final`**: every diffusion semigroup is the canonical kernel. -/
theorem bridge_final {Pt : ℝ≥0 → Kernel M M} (hP : IsDiffusionSemigroup F V Pt) :
    ∀ (t : ℝ≥0) (x : M), Pt t x = Kk F hV hμ t x :=
  bridge_of_minimal F hP (isDiffusionSemigroup_Kk F hV hμ) hV (minimalResolvent_Kk F hV hμ)

include hV hμ in
/-- **Uniqueness**: any `Kk'` with `KerCanonical` (in particular the one of `exists_kernel`) and any
diffusion semigroup `Pt` coincide. -/
theorem bridge_final_canonical {Pt Kk' : ℝ≥0 → Kernel M M} (hP : IsDiffusionSemigroup F V Pt)
    (hK : KerCanonical F V μ Kk') : ∀ (t : ℝ≥0) (x : M), Pt t x = Kk' t x := fun t x =>
  (bridge_final F hV hμ hP t x).trans
    (bridge_final F hV hμ hK.dynkin t x).symm

end Final

end CutoffRigidity.Riemann.Diff
