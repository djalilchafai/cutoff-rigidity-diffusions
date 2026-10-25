module
public import CutoffRigidity.GibbsEulerApproximation

/-! # Genuine symmetry and positivity of implicit Euler approximations -/
public section
namespace CutoffRigidity
open MeasureTheory Filter Topology
variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

theorem gibbsEulerStep_isSelfAdjoint
    {V : E → ℝ} (hV : ContDiff ℝ 2 V)
    (hprob : IsProbabilityMeasure (gibbsMeasure volume V)) (t : NNReal) (n : ℕ) :
    IsSelfAdjoint (gibbsEulerStep hV hprob t n) := by
  unfold gibbsEulerStep
  split_ifs with ht
  · apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
    exact gibbsScaledL2Resolvent_symmetric hV hprob _ _
  · apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
    intro f g
    rfl

theorem gibbsEulerApproximation_symmetric
    {V : E → ℝ} (hV : ContDiff ℝ 2 V)
    (hprob : IsProbabilityMeasure (gibbsMeasure volume V)) (t : NNReal) (n : ℕ)
    (f g : E →₂[gibbsMeasure volume V] ℝ) :
    inner ℝ (gibbsEulerApproximation hV hprob t n f) g =
      inner ℝ f (gibbsEulerApproximation hV hprob t n g) :=
  (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
    ((gibbsEulerStep_isSelfAdjoint hV hprob t n).pow (n + 1))) f g

theorem gibbsEulerStep_constant
    {V : E → ℝ} (hV : ContDiff ℝ 2 V)
    (hprob : IsProbabilityMeasure (gibbsMeasure volume V)) (t : NNReal) (n : ℕ) (c : ℝ) :
    gibbsEulerStep hV hprob t n (gibbsConstantLp hprob c) = gibbsConstantLp hprob c := by
  unfold gibbsEulerStep
  split_ifs with ht
  · exact gibbsScaledL2Resolvent_constant hV hprob _ _ c
  · rfl

theorem gibbsEulerApproximation_constant
    {V : E → ℝ} (hV : ContDiff ℝ 2 V)
    (hprob : IsProbabilityMeasure (gibbsMeasure volume V)) (t : NNReal) (n : ℕ) (c : ℝ) :
    gibbsEulerApproximation hV hprob t n (gibbsConstantLp hprob c) = gibbsConstantLp hprob c := by
  have hh := clm_pow_apply_eigen (gibbsEulerStep hV hprob t n) 1 (gibbsConstantLp hprob c)
    (by simpa only [one_smul] using gibbsEulerStep_constant hV hprob t n c) (n + 1)
  change (gibbsEulerStep hV hprob t n ^ (n + 1)) (gibbsConstantLp hprob c) = _
  simpa only [one_pow, one_smul] using hh

theorem gibbsEulerStep_preserves_nonneg
    {V : E → ℝ} (hV : ContDiff ℝ 2 V)
    (hprob : IsProbabilityMeasure (gibbsMeasure volume V)) (t : NNReal) (n : ℕ)
    (f : E →₂[gibbsMeasure volume V] ℝ) (hf : ∀ᵐ x ∂gibbsMeasure volume V, 0 ≤ f x) :
    ∀ᵐ x ∂gibbsMeasure volume V, 0 ≤ gibbsEulerStep hV hprob t n f x := by
  unfold gibbsEulerStep
  split_ifs with ht
  · exact gibbsScaledL2Resolvent_preserves_nonneg hV hprob _ _ f hf
  · exact hf

theorem gibbsEulerApproximation_preserves_nonneg
    {V : E → ℝ} (hV : ContDiff ℝ 2 V)
    (hprob : IsProbabilityMeasure (gibbsMeasure volume V)) (t : NNReal) (n : ℕ)
    (f : E →₂[gibbsMeasure volume V] ℝ) (hf : ∀ᵐ x ∂gibbsMeasure volume V, 0 ≤ f x) :
    ∀ᵐ x ∂gibbsMeasure volume V, 0 ≤ gibbsEulerApproximation hV hprob t n f x := by
  have hh (k : ℕ) : ∀ᵐ x ∂gibbsMeasure volume V, 0 ≤ ((gibbsEulerStep hV hprob t n) ^ k) f x := by
    induction k with
    | zero => exact hf
    | succ k ih =>
      rw [pow_succ', mul_apply_eq_comp]
      exact gibbsEulerStep_preserves_nonneg hV hprob t n _ ih
  exact hh (n + 1)

end CutoffRigidity
