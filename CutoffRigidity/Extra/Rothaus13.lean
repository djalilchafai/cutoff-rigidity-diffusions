module

public import Mathlib
public import CutoffRigidity.Extra.Rothaus12

/-! # Rothaus remark (stage 13): finite spaces, the form `E f = ∑ w(x,y) (f x - f y)²`

On a finite probability space with full support, the Dirichlet form of a symmetric-or-not weight array `w ≥ 0`.
This stage proves the Poincaré inequality from irreducibility (compactness of the unit sphere of mean-zero functions).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology

namespace CutoffRigidity.Rothaus

section Finite

variable {X : Type*} [Fintype X] [MeasurableSpace X] [MeasurableSingletonClass X] (μ : Measure X)
  [IsProbabilityMeasure μ]

/-- The Dirichlet form of the weights `w` on a finite space, with all functions as domain. -/
noncomputable def finiteForm (w : X → X → ℝ) (hw : ∀ x y, 0 ≤ w x y) : Form μ where
  Q := Set.univ
  E f := ∑ x, ∑ y, w x y * (f x - f y) ^ 2
  smul_mem _ _ _ := Set.mem_univ _
  add_const_mem _ _ _ := Set.mem_univ _
  E_nonneg f _ := Finset.sum_nonneg fun x _ => Finset.sum_nonneg fun y _ =>
    mul_nonneg (hw x y) (sq_nonneg _)
  E_smul c f _ := by
    simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => by ring
  E_add_const c f _ := by
    simp only [add_sub_add_right_eq_sub]
  memLp f _ := MemLp.of_discrete
  integrable_Θ f _ := Integrable.of_finite

theorem finiteForm_E (w : X → X → ℝ) (hw : ∀ x y, 0 ≤ w x y) (f : X → ℝ) :
    (finiteForm μ w hw).E f = ∑ x, ∑ y, w x y * (f x - f y) ^ 2 := rfl

theorem finiteForm_Q (w : X → X → ℝ) (hw : ∀ x y, 0 ≤ w x y) :
    (finiteForm μ w hw).Q = Set.univ := rfl

theorem sum_real_singleton : ∑ x, μ.real {x} = 1 := by
  rw [sum_measureReal_singleton]; simp

theorem integral_finite (f : X → ℝ) : ∫ x, f x ∂μ = ∑ x, μ.real {x} * f x := by
  rw [integral_fintype Integrable.of_finite]; simp

theorem variance_finite (f : X → ℝ) :
    variance f μ = ∑ x, μ.real {x} * f x ^ 2 - (∑ x, μ.real {x} * f x) ^ 2 := by
  rw [variance_eq_sub MemLp.of_discrete]
  simp only [Pi.pow_apply]
  rw [integral_finite, integral_finite]

end Finite

end CutoffRigidity.Rothaus
