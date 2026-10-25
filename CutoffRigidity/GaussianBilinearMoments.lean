module

public import CutoffRigidity.GaussianMoments
public import CutoffRigidity.GeneratorIntertwining

/-!
# Gaussian averaging of a genuine continuous bilinear form

The trace identity is used when deriving the infinitesimal Brownian generator
from Taylor expansion. All product integrability follows from Gaussian L²
moments; no covariance or integrability assumption is supplied by the caller.
-/

public section

namespace CutoffRigidity

open MeasureTheory ProbabilityTheory

variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

/-- Products of actual standard Gaussian coordinates are integrable. -/
theorem integrable_mul_coordinate_stdGaussian (i j : Fin d) :
    Integrable (fun z : E => z i * z j) (stdGaussian E) := by
  have hi : MemLp (fun z : E => z i) 2 (stdGaussian E) :=
    IsGaussian.memLp_dual (stdGaussian E) (EuclideanSpace.proj i) 2 (by norm_num)
  have hj : MemLp (fun z : E => z j) 2 (stdGaussian E) :=
    IsGaussian.memLp_dual (stdGaussian E) (EuclideanSpace.proj j) 2 (by norm_num)
  exact hi.integrable_mul hj

/-- The coordinate covariance comes from the actual standard Gaussian law. -/
theorem integral_mul_coordinate_stdGaussian (i j : Fin d) :
    (∫ z : E, z i * z j ∂stdGaussian E) = if i = j then 1 else 0 := by
  have hm : MemLp (id : E → E) 2 (stdGaussian E) :=
    IsGaussian.memLp_id (stdGaussian E) 2 (by norm_num)
  have h := covarianceBilin_apply hm (EuclideanSpace.single i (1 : ℝ)) (EuclideanSpace.single j (1 : ℝ))
  simp only [id_eq] at h
  rw [covarianceBilin_stdGaussian, integral_id_stdGaussian] at h
  change inner ℝ (EuclideanSpace.single i (1 : ℝ)) (EuclideanSpace.single j (1 : ℝ)) =
    ∫ z : E, inner ℝ (EuclideanSpace.single i (1 : ℝ)) (z - 0) *
      inner ℝ (EuclideanSpace.single j (1 : ℝ)) (z - 0) ∂stdGaussian E at h
  simpa [EuclideanSpace.inner_single_left, PiLp.single_apply, eq_comm] using h.symm

/-- A continuous bilinear quadratic form is integrable under the standard Gaussian. -/
theorem integrable_bilinear_diagonal_stdGaussian (H : E →L[ℝ] E →L[ℝ] ℝ) :
    Integrable (fun z : E => H z z) (stdGaussian E) := by
  have heq : (fun z : E => H z z) = fun z => ∑ i : Fin d, ∑ j : Fin d,
      z i * z j * H (EuclideanSpace.single i (1 : ℝ)) (EuclideanSpace.single j (1 : ℝ)) :=
    funext (fun z => bilinear_euclidean_coordinate_expansion H z z)
  rw [heq]
  apply integrable_finsetSum
  intro i _
  apply integrable_finsetSum
  intro j _
  exact (integrable_mul_coordinate_stdGaussian i j).mul_const _

/-- Gaussian expectation of a genuine bilinear form is its Euclidean trace. -/
theorem integral_bilinear_diagonal_stdGaussian (H : E →L[ℝ] E →L[ℝ] ℝ) :
    (∫ z : E, H z z ∂stdGaussian E) =
      ∑ i : Fin d, H (EuclideanSpace.single i (1 : ℝ)) (EuclideanSpace.single i (1 : ℝ)) := by
  have heq : (fun z : E => H z z) = fun z => ∑ i : Fin d, ∑ j : Fin d,
      z i * z j * H (EuclideanSpace.single i (1 : ℝ)) (EuclideanSpace.single j (1 : ℝ)) :=
    funext (fun z => bilinear_euclidean_coordinate_expansion H z z)
  rw [heq]
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro i _
    rw [integral_finsetSum]
    · simp_rw [integral_mul_const, integral_mul_coordinate_stdGaussian]
      simp
    · intro j _
      exact (integrable_mul_coordinate_stdGaussian i j).mul_const _
  · intro i _
    apply integrable_finsetSum
    intro j _
    exact (integrable_mul_coordinate_stdGaussian i j).mul_const _

end CutoffRigidity
