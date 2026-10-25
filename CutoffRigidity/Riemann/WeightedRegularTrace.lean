module

public import CutoffRigidity.Riemann.WeightedRegularKoszul
public import CutoffRigidity.RiemannianDifferentialOperators

/-! # G0 (part 3): trace formulas in a chart frame

For `z` in the chart target, the Laplacian `tr ∇Y` and the Hessian norm `tr (∇Y)^*(∇Y)` of the
Levi-Civita derivative at `e.symm z` are `tr (G⁻¹ K)` and `tr (G⁻¹ P)` in terms of the chart metric
`G = chartMetric x₀ z` and the coefficients `K = hessCoeff Y x₀ z`.
-/

@[expose] public section
open Bundle Set Filter
open scoped Manifold ContDiff Topology
set_option backward.isDefEq.respectTransparency false

namespace CutCur.WReg

set_option linter.unusedSectionVars false

variable {F : Type} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  {M : Type} [EMetricSpace M] [ChartedSpace F M] [IsManifold 𝓘(ℝ, F) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, F) ∞ F (fun x : M => TangentSpace 𝓘(ℝ, F) x)]

open CutoffRigidity

/-- The continuous inverse of the chart frame at `y`. -/
noncomputable def chartFrameInv (x₀ y : M) : TangentSpace 𝓘(ℝ, F) y →L[ℝ] F :=
  (trivializationAt F (TangentSpace 𝓘(ℝ, F)) x₀).continuousLinearMapAt ℝ y

theorem chartFrame_chartFrameInv {x₀ y : M} (hy : y ∈ (chartAt F x₀).source)
    (v : TangentSpace 𝓘(ℝ, F) y) :
    chartFrameCLM (I := 𝓘(ℝ, F)) x₀ y (chartFrameInv x₀ y v) = v :=
  (trivializationAt F (TangentSpace 𝓘(ℝ, F)) x₀).symmL_continuousLinearMapAt
    (mem_baseSet_of_mem_source (F := F) hy) v

theorem chartFrameInv_chartFrame {x₀ y : M} (hy : y ∈ (chartAt F x₀).source) (u : F) :
    chartFrameInv x₀ y (chartFrameCLM (I := 𝓘(ℝ, F)) x₀ y u) = u :=
  (trivializationAt F (TangentSpace 𝓘(ℝ, F)) x₀).continuousLinearMapAt_symmL
    (mem_baseSet_of_mem_source (F := F) hy) u

theorem mem_source_of_mem_target {x₀ : M} {z : F}
    (hz : z ∈ (extChartAt 𝓘(ℝ, F) x₀).target) :
    (extChartAt 𝓘(ℝ, F) x₀).symm z ∈ (chartAt F x₀).source := by
  simpa only [extChartAt_source] using (extChartAt 𝓘(ℝ, F) x₀).map_target hz

/-- Coordinate expression `G⁻¹ K` of the Levi-Civita derivative of `Y`. -/
noncomputable def hessOp (Y : (y : M) → TangentSpace 𝓘(ℝ, F) y) (x₀ : M) (z : F) : F →L[ℝ] F :=
  (chartMetric (I := 𝓘(ℝ, F)) x₀ z).inverse ∘L hessCoeff Y x₀ z

/-- Coordinate expression of the Gram form of the Levi-Civita derivative. -/
noncomputable def hessGram (Y : (y : M) → TangentSpace 𝓘(ℝ, F) y) (x₀ : M) (z : F) :
    F →L[ℝ] F →L[ℝ] ℝ :=
  (chartMetric (I := 𝓘(ℝ, F)) x₀ z).bilinearComp (hessOp Y x₀ z) (hessOp Y x₀ z)

theorem trace_conj_aux {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    (T : F →ₗ[ℝ] V) (S : V →ₗ[ℝ] F) (hTS : T ∘ₗ S = LinearMap.id) (A : V →ₗ[ℝ] V) :
    LinearMap.trace ℝ F (S ∘ₗ A ∘ₗ T) = LinearMap.trace ℝ V A := by
  have := LinearMap.trace_comp_comm' (R := ℝ) (A ∘ₗ T) S
  rw [LinearMap.comp_assoc] at this
  rw [this, hTS]
  simp

theorem chartFrameInv_comp_hessOp_eq {x₀ : M} {z : F}
    (hz : z ∈ (extChartAt 𝓘(ℝ, F) x₀).target) (Y : (y : M) → TangentSpace 𝓘(ℝ, F) y) :
    chartFrameInv x₀ ((extChartAt 𝓘(ℝ, F) x₀).symm z) ∘L
        (CovariantDerivative.leviCivitaConnection 𝓘(ℝ, F) M Y
          ((extChartAt 𝓘(ℝ, F) x₀).symm z)) ∘L
        chartFrameCLM (I := 𝓘(ℝ, F)) x₀ ((extChartAt 𝓘(ℝ, F) x₀).symm z) = hessOp Y x₀ z := by
  have hy := mem_source_of_mem_target (x₀ := x₀) hz
  ext u
  symm
  apply (chartMetric_isInvertible_of_mem_target (I := 𝓘(ℝ, F)) x₀ hz).inverse_apply_eq.mpr
  ext w
  rw [chartMetric_apply]
  change hessCoeff Y x₀ z u w = _
  rw [hessCoeff_apply]
  simp only [ContinuousLinearMap.comp_apply]
  change _ = inner ℝ (chartFrameCLM (I := 𝓘(ℝ, F)) x₀ _ (chartFrameInv x₀ _ (_ ))) _
  rw [chartFrame_chartFrameInv hy]
  rfl

theorem trace_levi_eq {x₀ : M} {z : F}
    (hz : z ∈ (extChartAt 𝓘(ℝ, F) x₀).target) (Y : (y : M) → TangentSpace 𝓘(ℝ, F) y) :
    LinearMap.trace ℝ (TangentSpace 𝓘(ℝ, F) ((extChartAt 𝓘(ℝ, F) x₀).symm z))
        (CovariantDerivative.leviCivitaConnection 𝓘(ℝ, F) M Y
          ((extChartAt 𝓘(ℝ, F) x₀).symm z)).toLinearMap =
      LinearMap.trace ℝ F (hessOp Y x₀ z).toLinearMap := by
  have hy := mem_source_of_mem_target (x₀ := x₀) hz
  rw [← chartFrameInv_comp_hessOp_eq hz Y]
  exact (trace_conj_aux (chartFrameCLM (I := 𝓘(ℝ, F)) x₀ _).toLinearMap
    (chartFrameInv x₀ _).toLinearMap (by ext v; exact chartFrame_chartFrameInv hy v) _).symm

theorem hessNormSq_eq {x₀ : M} {z : F}
    (hz : z ∈ (extChartAt 𝓘(ℝ, F) x₀).target) (f : M → ℝ) :
    manifoldHessianNormSq 𝓘(ℝ, F) f ((extChartAt 𝓘(ℝ, F) x₀).symm z) =
      LinearMap.trace ℝ F ((chartMetric (I := 𝓘(ℝ, F)) x₀ z).inverse ∘L
        hessGram (manifoldGradient 𝓘(ℝ, F) f) x₀ z).toLinearMap := by
  have hy := mem_source_of_mem_target (x₀ := x₀) hz
  have hop := chartFrameInv_comp_hessOp_eq hz (manifoldGradient 𝓘(ℝ, F) f)
  rw [manifoldHessianNormSq_eq_trace_adjoint]
  set A := CovariantDerivative.leviCivitaConnection 𝓘(ℝ, F) M (manifoldGradient 𝓘(ℝ, F) f)
    ((extChartAt 𝓘(ℝ, F) x₀).symm z) with hA
  have h1 := trace_conj_aux (chartFrameCLM (I := 𝓘(ℝ, F)) x₀ _).toLinearMap
    (chartFrameInv x₀ _).toLinearMap (by ext v; exact chartFrame_chartFrameInv hy v)
    ((A.adjoint.comp A).toLinearMap)
  rw [← h1]
  congr 1
  have : (chartFrameInv x₀ ((extChartAt 𝓘(ℝ, F) x₀).symm z) ∘L (A.adjoint.comp A) ∘L
      chartFrameCLM (I := 𝓘(ℝ, F)) x₀ ((extChartAt 𝓘(ℝ, F) x₀).symm z)) =
      (chartMetric (I := 𝓘(ℝ, F)) x₀ z).inverse ∘L
        hessGram (manifoldGradient 𝓘(ℝ, F) f) x₀ z := by
    ext u
    symm
    apply (chartMetric_isInvertible_of_mem_target (I := 𝓘(ℝ, F)) x₀ hz).inverse_apply_eq.mpr
    ext w
    change chartMetric (I := 𝓘(ℝ, F)) x₀ z (hessOp _ x₀ z u) (hessOp _ x₀ z w) = _
    have hu : hessOp (manifoldGradient 𝓘(ℝ, F) f) x₀ z u =
        chartFrameInv x₀ _ (A (chartFrameCLM (I := 𝓘(ℝ, F)) x₀ _ u)) :=
      (ContinuousLinearMap.ext_iff.mp hop u).symm
    have hw : hessOp (manifoldGradient 𝓘(ℝ, F) f) x₀ z w =
        chartFrameInv x₀ _ (A (chartFrameCLM (I := 𝓘(ℝ, F)) x₀ _ w)) :=
      (ContinuousLinearMap.ext_iff.mp hop w).symm
    rw [hu, hw, chartMetric_apply, chartMetric_apply]
    change inner ℝ (chartFrameCLM (I := 𝓘(ℝ, F)) x₀ _ (chartFrameInv x₀ _ _))
        (chartFrameCLM (I := 𝓘(ℝ, F)) x₀ _ (chartFrameInv x₀ _ _)) =
      inner ℝ (chartFrameCLM (I := 𝓘(ℝ, F)) x₀ _ (chartFrameInv x₀ _ _)) _
    rw [chartFrame_chartFrameInv hy, chartFrame_chartFrameInv hy, chartFrame_chartFrameInv hy]
    change _ = inner ℝ (ContinuousLinearMap.adjoint A
      (A (chartFrameCLM (I := 𝓘(ℝ, F)) x₀ _ u))) (chartFrameCLM (I := 𝓘(ℝ, F)) x₀ _ w)
    rw [ContinuousLinearMap.adjoint_inner_left]
  exact congrArg ContinuousLinearMap.toLinearMap this

end CutCur.WReg
