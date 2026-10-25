module

public import CutoffRigidity.Riemann.DiffusionRegular
public import CutoffRigidity.Riemann.WeightedInterface

/-! # Interface `CanonicalDiffusion` between the workstreams of the diffusion programme

See `riemann-status/DIFFUSION_PLAN.md` §4.1.  Tier A (Friedrichs diffusion `Kk` built in `L²(μ)`)
produces a `CanonicalDiffusion`; Tier B (identification `Pt = Kk`) and Tier C (the Wasserstein
estimate) consume it.
-/

@[expose] public section

open Bundle MeasureTheory ProbabilityTheory Filter Set
open scoped Manifold ContDiff ENNReal NNReal Topology

namespace CutoffRigidity.Riemann.Diff

open CutCur

variable (F : Type) [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  {M : Type} [EMetricSpace M] [ChartedSpace F M] [IsManifold 𝓘(ℝ, F) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, F) ∞ F (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [MeasurableSpace M]

/-- `Pₜ f (x) = ∫ f dPₜ(x,·)`. -/
noncomputable def semi (Pt : ℝ≥0 → Kernel M M) (t : ℝ≥0) (f : M → ℝ) : M → ℝ :=
  fun x => ∫ y, f y ∂(Pt t x)

/-- Output of Tier A, input of Tiers B and C. -/
structure CanonicalDiffusion (V : M → ℝ) (μ : Measure M) (ρ : ℝ) (Kk : ℝ≥0 → Kernel M M) :
    Prop where
  markov : ∀ t, IsMarkovKernel (Kk t)
  dynkin : IsDiffusionSemigroup F V Kk
  invariant : ∀ t, μ.bind (Kk t) = μ
  eigen : ∀ (c : ℝ) (u : M → ℝ), MSmooth F u → MemLp u 2 μ →
      (∀ x, mgenerator F V u x = -c * u x) →
      ∀ (t : ℝ≥0) (x : M), Integrable u (Kk t x) ∧ ∫ y, u y ∂Kk t x = Real.exp (-c * t) * u x
  smoothing : ∀ g, MSmooth F g → HasCompactSupport g → ∀ t, MSmooth F (semi Kk t g) ∧
      mgenerator F V (semi Kk t g) = semi Kk t (mgenerator F V g) ∧
      ∃ C : ℝ, ∀ (s : ℝ≥0) x, |semi Kk s g x| ≤ C ∧ ‖mgrad F (semi Kk s g) x‖ ≤ C ∧
        |mgenerator F V (semi Kk s g) x| ≤ C
  contraction : ∀ (t : ℝ≥0) (x : M), CutCur.wasserstein2 (Kk t x) μ ^ 2 ≤
      ENNReal.ofReal (Real.exp (-2 * ρ * t)) * ∫⁻ y, edist x y ^ 2 ∂μ

end CutoffRigidity.Riemann.Diff
