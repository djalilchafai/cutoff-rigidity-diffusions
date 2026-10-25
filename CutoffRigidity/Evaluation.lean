module

public import Mathlib.Analysis.InnerProductSpace.Dual

/-!
# Basis independence of the evaluation norm

This file formalizes the Riesz-representation and Parseval argument of
Remark 1.2 in `cutcur-lean.tex`. An evaluation map is supplied as an actual
continuous linear functional on the finite-dimensional first eigenspace.
The analytic construction of that eigenspace and its pointwise evaluation
on canonical eigenfunction representatives is a separate obligation.
-/

public section

namespace CutoffRigidity

/-- Parseval identifies the sum of squared absolute evaluations with the
squared norm of the Riesz representative of the evaluation functional. -/
theorem sum_abs_sq_evaluation_eq_riesz_norm_sq
    {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [Fintype ι]
    (ℓ : E →L[ℝ] ℝ) (b : OrthonormalBasis ι ℝ E) :
    ∑ i : ι, |ℓ (b i)| ^ 2 = ‖(InnerProductSpace.toDual ℝ E).symm ℓ‖ ^ 2 := by
  simpa only [InnerProductSpace.toDual_symm_apply, sq_abs] using
    b.sum_sq_inner_left ((InnerProductSpace.toDual ℝ E).symm ℓ)

/-- The same evaluation sum is the squared operator norm of evaluation. -/
theorem sum_abs_sq_evaluation_eq_norm_sq
    {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [Fintype ι]
    (ℓ : E →L[ℝ] ℝ) (b : OrthonormalBasis ι ℝ E) :
    ∑ i : ι, |ℓ (b i)| ^ 2 = ‖ℓ‖ ^ 2 := by
  rw [sum_abs_sq_evaluation_eq_riesz_norm_sq, (InnerProductSpace.toDual ℝ E).symm.norm_map]

/-- The expression defining Λ does not depend on the choice of orthonormal
basis, including the choice of a finite indexing type. -/
theorem sum_abs_sq_evaluation_basis_independent
    {E ι κ : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [Fintype ι] [Fintype κ]
    (ℓ : E →L[ℝ] ℝ) (b : OrthonormalBasis ι ℝ E) (c : OrthonormalBasis κ ℝ E) :
    ∑ i : ι, |ℓ (b i)| ^ 2 = ∑ j : κ, |ℓ (c j)| ^ 2 := by
  rw [sum_abs_sq_evaluation_eq_norm_sq, sum_abs_sq_evaluation_eq_norm_sq]

/-- Consequently the supremum over orthonormal bases in the definition of Λ
is redundant. The supplied basis ensures that the indexing set is nonempty. -/
theorem sSup_sum_abs_sq_evaluation_eq_norm_sq
    {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [Fintype ι]
    (ℓ : E →L[ℝ] ℝ) (b : OrthonormalBasis ι ℝ E) :
    sSup (Set.range fun c : OrthonormalBasis ι ℝ E => ∑ i : ι, |ℓ (c i)| ^ 2) =
      ‖ℓ‖ ^ 2 := by
  have hrange :
      (Set.range fun c : OrthonormalBasis ι ℝ E => ∑ i : ι, |ℓ (c i)| ^ 2) =
        {‖ℓ‖ ^ 2} := by
    ext y
    constructor
    · rintro ⟨c, rfl⟩
      exact sum_abs_sq_evaluation_eq_norm_sq ℓ c
    · intro hy
      have hy' : y = ‖ℓ‖ ^ 2 := hy
      exact ⟨b, (sum_abs_sq_evaluation_eq_norm_sq ℓ b).trans hy'.symm⟩
  rw [hrange, csSup_singleton]

end CutoffRigidity
