module

public import CutoffRigidity.Riemann.WeightedInterface
public import CutoffRigidity.RiemannianChartFrames

/-! # G2 (Bochner inequality): shared definitions

`nab F X Y` is the Levi-Civita derivative `∇_X Y` of the vector field `Y` along the vector
field `X`, and `curv F X Y Z` the expression `∇_X ∇_Y Z - ∇_Y ∇_X Z - ∇_{[X,Y]} Z` (a curvature
expression, shown tensorial in `Workstream G2`). `SmAt F X x` says that the field `X` is smooth
at `x`.
-/

@[expose] public section
open Bundle Filter Set VectorField
open scoped Manifold ContDiff Topology
set_option backward.isDefEq.respectTransparency false

namespace CutCur.WBoch

section Defs

variable (F : Type) [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  {M : Type} [EMetricSpace M] [ChartedSpace F M] [IsManifold 𝓘(ℝ, F) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, F) ∞ F (fun x : M => TangentSpace 𝓘(ℝ, F) x)]

/-- `Y` is a smooth section of the tangent bundle at `x`. -/
def SmAt (X : (y : M) → TangentSpace 𝓘(ℝ, F) y) (x : M) : Prop :=
  ContMDiffAt 𝓘(ℝ, F) 𝓘(ℝ, F).tangent ∞ (T% X) x

/-- The Levi-Civita derivative `∇_X Y` of the field `Y` along the field `X`. -/
noncomputable def nab (X Y : (y : M) → TangentSpace 𝓘(ℝ, F) y) :
    (y : M) → TangentSpace 𝓘(ℝ, F) y :=
  fun y => CovariantDerivative.leviCivitaConnection 𝓘(ℝ, F) M Y y (X y)

/-- `∇_X ∇_Y Z - ∇_Y ∇_X Z - ∇_{[X,Y]} Z` at `x`. -/
noncomputable def curv (X Y Z : (y : M) → TangentSpace 𝓘(ℝ, F) y) (x : M) :
    TangentSpace 𝓘(ℝ, F) x :=
  CovariantDerivative.leviCivitaConnection 𝓘(ℝ, F) M (nab F Y Z) x (X x)
    - CovariantDerivative.leviCivitaConnection 𝓘(ℝ, F) M (nab F X Z) x (Y x)
    - CovariantDerivative.leviCivitaConnection 𝓘(ℝ, F) M Z x
        (mlieBracket 𝓘(ℝ, F) X Y x)

/-- Smoothness of the Levi-Civita derivative of smooth fields (the hypothesis under which the
tensor calculus is carried out; it is discharged by the Koszul-formula argument). -/
def NabSmooth (M : Type) [EMetricSpace M] [ChartedSpace F M] [IsManifold 𝓘(ℝ, F) ∞ M]
    [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
    [IsContMDiffRiemannianBundle 𝓘(ℝ, F) ∞ F (fun x : M => TangentSpace 𝓘(ℝ, F) x)] : Prop :=
  ∀ (X Y : (y : M) → TangentSpace 𝓘(ℝ, F) y) (x : M), SmAt F X x → SmAt F Y x → SmAt F (nab F X Y) x

end Defs

end CutCur.WBoch
