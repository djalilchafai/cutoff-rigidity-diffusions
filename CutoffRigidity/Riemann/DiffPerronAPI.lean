module

public import CutoffRigidity.Riemann.DiffAPI

/-! # Interface of the Perron/bridge route (`riemann-status/CO_PLAN.md`, sections 2.3 and 4)

* `resolventU P lam g x = ∫₀^∞ e^{-lam s} Pₛ g (x) ds`;
* `MinimalResolvent F V Kk`: the Perron property of the resolvent of `Kk`: it is approached from
  below at every point by compactly supported smooth subsolutions `(lam - 𝓛) f ≤ g`.
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

/-- The resolvent `U^P_λ g (x) = ∫₀^∞ e^{-λ s} Pₛ g(x) ds` of a kernel family. -/
noncomputable def resolventU (Pt : ℝ≥0 → Kernel M M) (lam : ℝ) (g : M → ℝ) (x : M) : ℝ :=
  ∫ s in Set.Ioi (0 : ℝ), Real.exp (-lam * s) * semi Pt s.toNNReal g x

/-- Perron property of the resolvent of `Kk`: for smooth compactly supported `g ≥ 0`, `lam > 0`,
`x`, and `η > 0` there is a smooth compactly supported subsolution `(lam - 𝓛) f ≤ g` with
`U^K_lam g (x) - η ≤ f x`. -/
def MinimalResolvent (V : M → ℝ) (Kk : ℝ≥0 → Kernel M M) : Prop :=
  ∀ lam : ℝ, 0 < lam → ∀ g : M → ℝ, MSmooth F g → HasCompactSupport g → (∀ x, 0 ≤ g x) →
    ∀ (x : M) (η : ℝ), 0 < η →
    ∃ f : M → ℝ, MSmooth F f ∧ HasCompactSupport f ∧
      (∀ y, lam * f y - mgenerator F V f y ≤ g y) ∧ resolventU Kk lam g x - η ≤ f x

end CutoffRigidity.Riemann.Diff
