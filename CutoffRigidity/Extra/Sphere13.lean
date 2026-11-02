module

public import CutoffRigidity.Extra.Sphere12

/-! # Sphere, stage 13: dimensional Bochner inequality `(Δf)² ≤ d ‖Hess f‖²` -/

@[expose] public section

open Bundle Filter Set VectorField MeasureTheory
open scoped Manifold ContDiff Topology

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

namespace CutoffRigidity.Extra.Sphere

open CutCur

variable {F : Type} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]
  {M : Type} [EMetricSpace M] [ChartedSpace F M] [IsManifold 𝓘(ℝ, F) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, F) ∞ F (fun x : M => TangentSpace 𝓘(ℝ, F) x)]

/-- Cauchy-Schwarz for the trace: `(Δ f)² ≤ dim · ‖Hess f‖²`. -/
theorem mlaplacian_sq_le (f : M → ℝ) (x : M) :
    (mlaplacian F f x) ^ 2 ≤ (Module.finrank ℝ F : ℝ) * mHessSq F f x := by
  unfold mlaplacian mHessSq
  set b := stdOrthonormalBasis ℝ (TangentSpace 𝓘(ℝ, F) x) with hb
  set v : Fin (Module.finrank ℝ (TangentSpace 𝓘(ℝ, F) x)) → TangentSpace 𝓘(ℝ, F) x := fun i =>
    CovariantDerivative.leviCivitaConnection 𝓘(ℝ, F) M (mgrad F f) x (b i) with hv
  have h1 : ∀ i, (inner ℝ (v i) (b i)) ^ 2 ≤ ‖v i‖ ^ 2 := by
    intro i
    have := abs_real_inner_le_norm (v i) (b i)
    have hbn : ‖b i‖ = 1 := b.orthonormal.1 i
    rw [hbn, mul_one] at this
    calc (inner ℝ (v i) (b i)) ^ 2 = |inner ℝ (v i) (b i)| ^ 2 := (sq_abs _).symm
      _ ≤ ‖v i‖ ^ 2 := by gcongr
  have h2 := sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun i => inner ℝ (v i) (b i))
  simp only [Finset.card_univ, Fintype.card_fin] at h2
  have hd : Module.finrank ℝ (TangentSpace 𝓘(ℝ, F) x) = Module.finrank ℝ F := rfl
  calc (∑ i, inner ℝ (v i) (b i)) ^ 2
      ≤ (Module.finrank ℝ (TangentSpace 𝓘(ℝ, F) x) : ℝ) * ∑ i, (inner ℝ (v i) (b i)) ^ 2 := by exact_mod_cast h2
    _ ≤ (Module.finrank ℝ F : ℝ) * ∑ i, ‖v i‖ ^ 2 := by
        have hcast : (Module.finrank ℝ (TangentSpace 𝓘(ℝ, F) x) : ℝ) = (Module.finrank ℝ F : ℝ) := by
          exact_mod_cast hd
        rw [hcast]
        exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => h1 i) (Nat.cast_nonneg _)

end CutoffRigidity.Extra.Sphere
