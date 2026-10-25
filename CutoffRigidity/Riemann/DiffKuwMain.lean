module

public import CutoffRigidity.Riemann.DiffKuw
public import CutoffRigidity.Riemann.DiffBEMain

/-! # KUW-B main: the contraction (A10) and `CanonicalDiffusion` from `CD(ρ)`

Bridges the workstream-BE statement `BEPointwise` (on `testSub F M`) to `BETestFun` (smooth compactly
supported functions) and concludes `contraction_of_CD`, `exists_canonical`.
-/

@[expose] public section

open Bundle MeasureTheory ProbabilityTheory Filter Set Topology
open scoped Manifold ContDiff ENNReal NNReal Topology

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace CutoffRigidity.Riemann.Diff

open CutCur

section Main

variable (F : Type) [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]
  {M : Type} [EMetricSpace M] [ChartedSpace F M] [IsManifold 𝓘(ℝ, F) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, F) ∞ F (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [MeasurableSpace M] [BorelSpace M]
  [IsRiemannianManifold 𝓘(ℝ, F) M] [ConnectedSpace M] [CompleteSpace M]
  {V : M → ℝ} {μ : Measure M} {ρ : ℝ}

include F

theorem betestFun_of_bePointwise {Kk : ℝ≥0 → Kernel M M}
    (h : BEPointwise F V μ ρ Kk) : BETestFun F V μ ρ Kk := fun f hs hc t x =>
  h ⟨f, hs, hc⟩ t x

/-- **A10**: `W₂(K_t(x,·),μ)² ≤ e^{-2ρt} ∫ d(x,y)² dμ(y)` for the canonical heat kernel. -/
theorem contraction_of_CD (hV : MSmooth F V) [IsProbabilityMeasure μ]
    (hμ : IsWeightedVolume F μ V) (hρ : 0 < ρ) (hCD : CD F ρ V) (t : ℝ≥0) (x : M) :
    CutCur.wasserstein2 (Kk F hV hμ t x) μ ^ 2 ≤
      ENNReal.ofReal (Real.exp (-2 * ρ * t)) * ∫⁻ y, edist x y ^ 2 ∂μ :=
  contraction_of_BE F hV hμ (betestFun_of_bePointwise F (bePointwise_of_CD F hV hμ hρ hCD)) t x

/-- The canonical diffusion exists (all fields of `CanonicalDiffusion`). -/
theorem exists_canonical (hV : MSmooth F V) [IsProbabilityMeasure μ]
    (hμ : IsWeightedVolume F μ V) (hρ : 0 < ρ) (hCD : CD F ρ V) :
    ∃ Kk : ℝ≥0 → Kernel M M, CanonicalDiffusion F V μ ρ Kk := by
  exact ⟨Kk F hV hμ, KerCanonical.toCanonical F (kerCanonical_Kk F hV hμ)
    (gradBound_of_CD F hV hμ hρ hCD) (contraction_of_CD F hV hμ hρ hCD)⟩

end Main

end CutoffRigidity.Riemann.Diff
