module
public import CutoffRigidity.GibbsSobolevC1

/-! # Actual Lebesgue integration by parts for a global C¹ function

Only the test is compact. This supplies the exact ordinary weak-Laplace
identity needed to turn the stochastic C¹ backward equation into Gibbs
variational domain membership at V's assumed C² regularity.
-/
public section
namespace CutoffRigidity
open MeasureTheory
variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

theorem c1_volume_weak_derivative_compact_test {f ψ : E → ℝ}
    (hf : ContDiff ℝ 1 f) (hψ : ContDiff ℝ 1 ψ) (hψc : HasCompactSupport ψ) (j : Fin d) :
    (∫ x, f x * coordinateDerivative j ψ x) = -(∫ x, coordinateDerivative j f x * ψ x) := by
  let v := EuclideanSpace.single j (1 : ℝ)
  have hfd := hf.differentiable (by norm_num)
  have hψd := hψ.differentiable (by norm_num)
  have hDf : Continuous (fun x => fderiv ℝ f x v) := by
    simp_rw [v, fderiv_single_eq_gradient_coordinate]
    exact (EuclideanSpace.proj j).continuous.comp (continuous_gradient_of_c1 hf)
  have hDψ : Continuous (fun x => fderiv ℝ ψ x v) := by
    simp_rw [v, fderiv_single_eq_gradient_coordinate]
    exact (EuclideanSpace.proj j).continuous.comp (continuous_gradient_of_c1 hψ)
  have hDψc : HasCompactSupport (fun x => fderiv ℝ ψ x v) := hψc.fderiv_apply ℝ v
  have h1 : Integrable (fun x => fderiv ℝ f x v * ψ x) volume :=
    (hDf.mul hψ.continuous).integrable_of_hasCompactSupport hψc.mul_left
  have h2 : Integrable (fun x => f x * fderiv ℝ ψ x v) volume :=
    (hf.continuous.mul hDψ).integrable_of_hasCompactSupport hDψc.mul_left
  have h3 : Integrable (fun x => f x * ψ x) volume :=
    (hf.continuous.mul hψ.continuous).integrable_of_hasCompactSupport hψc.mul_left
  exact integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable h1 h2 h3 (fun x _ => hfd x) (fun x _ => hψd x)

/-- Actual global C¹/compact C² weak Laplace integration by parts. -/
theorem c1_integral_mul_laplacian_compact_test {f ψ : E → ℝ}
    (hf : ContDiff ℝ 1 f) (hψ : ContDiff ℝ 2 ψ) (hψc : HasCompactSupport ψ) :
    (∫ x, f x * euclideanLaplacian ψ x) = -(∫ x, inner ℝ (gradient f x) (gradient ψ x)) := by
  have hDi (i : Fin d) : ContDiff ℝ 1 (coordinateDerivative i ψ) := c1_coordinateDerivative_of_c2 hψ i
  have hDic (i : Fin d) : HasCompactSupport (coordinateDerivative i ψ) :=
    hψc.fderiv_apply ℝ (EuclideanSpace.single i 1)
  have hDD (i : Fin d) : Continuous (coordinateDerivative i (coordinateDerivative i ψ)) := by
    change Continuous (fun x => fderiv ℝ (coordinateDerivative i ψ) x (EuclideanSpace.single i 1))
    simp_rw [fderiv_single_eq_gradient_coordinate]
    exact (EuclideanSpace.proj i).continuous.comp (continuous_gradient_of_c1 (hDi i))
  have hDDc (i : Fin d) : HasCompactSupport (coordinateDerivative i (coordinateDerivative i ψ)) :=
    (hDic i).fderiv_apply ℝ (EuclideanSpace.single i 1)
  have hleft (i : Fin d) : Integrable (fun x => f x * coordinateDerivative i (coordinateDerivative i ψ) x) volume :=
    (hf.continuous.mul (hDD i)).integrable_of_hasCompactSupport (hDDc i).mul_left
  have hDf (i : Fin d) : Continuous (coordinateDerivative i f) := by
    change Continuous (fun x => fderiv ℝ f x (EuclideanSpace.single i 1))
    simp_rw [fderiv_single_eq_gradient_coordinate]
    exact (EuclideanSpace.proj i).continuous.comp (continuous_gradient_of_c1 hf)
  have hright (i : Fin d) : Integrable (fun x => coordinateDerivative i f x * coordinateDerivative i ψ x) volume :=
    ((hDf i).mul (hDi i).continuous).integrable_of_hasCompactSupport (hDic i).mul_left
  have hp (x : E) : inner ℝ (gradient f x) (gradient ψ x) =
      ∑ i : Fin d, coordinateDerivative i f x * coordinateDerivative i ψ x := by
    rw [PiLp.inner_apply]
    apply Finset.sum_congr rfl
    intro i _
    rw [Real.inner_apply, coordinateDerivative, coordinateDerivative,
      fderiv_single_eq_gradient_coordinate, fderiv_single_eq_gradient_coordinate]
  simp_rw [hp]
  change (∫ x, f x * ∑ i : Fin d, coordinateDerivative i (coordinateDerivative i ψ) x) = _
  simp_rw [Finset.mul_sum]
  rw [integral_finsetSum _ (fun i _ => hleft i), integral_finsetSum _ (fun i _ => hright i), ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  exact c1_volume_weak_derivative_compact_test hf (hDi i) (hDic i) i

end CutoffRigidity
