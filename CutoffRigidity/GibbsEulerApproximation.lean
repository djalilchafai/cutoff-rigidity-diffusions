module
public import CutoffRigidity.GibbsScaledResolventOrder
public import CutoffRigidity.StrongContractionLimit
public import CutoffRigidity.GibbsSpectralEigenspaces
public import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds

/-! # Actual implicit-Euler approximations to Gibbs heat evolution -/
public section
namespace CutoffRigidity
open MeasureTheory Filter Topology
variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

@[expose] noncomputable def gibbsEulerStep
    {V : E → ℝ} (hV : ContDiff ℝ 2 V)
    (hprob : IsProbabilityMeasure (gibbsMeasure volume V)) (t : NNReal) (n : ℕ) :
    (E →₂[gibbsMeasure volume V] ℝ) →L[ℝ] (E →₂[gibbsMeasure volume V] ℝ) :=
  if ht : 0 < (t : ℝ) then
    gibbsScaledL2Resolvent hV hprob ((t : ℝ) / (n + 1)) (div_pos ht (by positivity))
  else ContinuousLinearMap.id ℝ _

@[expose] noncomputable def gibbsEulerApproximation
    {V : E → ℝ} (hV : ContDiff ℝ 2 V)
    (hprob : IsProbabilityMeasure (gibbsMeasure volume V)) (t : NNReal) (n : ℕ) :
    (E →₂[gibbsMeasure volume V] ℝ) →L[ℝ] (E →₂[gibbsMeasure volume V] ℝ) :=
  (gibbsEulerStep hV hprob t n) ^ (n + 1)

theorem norm_gibbsEulerStep_apply_le
    {V : E → ℝ} (hV : ContDiff ℝ 2 V)
    (hprob : IsProbabilityMeasure (gibbsMeasure volume V)) (t : NNReal) (n : ℕ)
    (u : E →₂[gibbsMeasure volume V] ℝ) : ‖gibbsEulerStep hV hprob t n u‖ ≤ ‖u‖ := by
  unfold gibbsEulerStep
  split_ifs with ht
  · exact norm_gibbsScaledL2Resolvent_apply_le hV hprob _ _ u
  · exact le_rfl

theorem norm_gibbsEulerApproximation_apply_le
    {V : E → ℝ} (hV : ContDiff ℝ 2 V)
    (hprob : IsProbabilityMeasure (gibbsMeasure volume V)) (t : NNReal) (n : ℕ)
    (u : E →₂[gibbsMeasure volume V] ℝ) : ‖gibbsEulerApproximation hV hprob t n u‖ ≤ ‖u‖ :=
  norm_clm_pow_apply_le _ (norm_gibbsEulerStep_apply_le hV hprob t n) _ u

theorem gibbsEulerApproximation_zero
    {V : E → ℝ} (hV : ContDiff ℝ 2 V)
    (hprob : IsProbabilityMeasure (gibbsMeasure volume V)) (n : ℕ) :
    gibbsEulerApproximation hV hprob 0 n = ContinuousLinearMap.id ℝ _ := by
  have hs : gibbsEulerStep hV hprob 0 n = ContinuousLinearMap.id ℝ _ := by
    unfold gibbsEulerStep
    exact dite_eq_right (not_lt.mpr le_rfl)
  change gibbsEulerStep hV hprob 0 n ^ (n + 1) = _
  rw [hs]
  change (1 : (E →₂[gibbsMeasure volume V] ℝ) →L[ℝ] (E →₂[gibbsMeasure volume V] ℝ)) ^ (n + 1) = 1
  exact one_pow _

theorem gibbsEulerApproximation_operatorEigen
    {V : E → ℝ} (hV : ContDiff ℝ 2 V)
    (hprob : IsProbabilityMeasure (gibbsMeasure volume V)) (t : NNReal) (ht : 0 < (t : ℝ))
    (rate : ℝ) (hrate : 0 ≤ rate) (u : E →₂[gibbsMeasure volume V] ℝ)
    (hu : (u, rate • u) ∈ (gibbsPositiveGenerator hV hprob).graph) (n : ℕ) :
    gibbsEulerApproximation hV hprob t n u =
      ((1 + (t : ℝ) / (n + 1) * rate)⁻¹ ^ (n + 1)) • u := by
  apply clm_pow_apply_eigen
  unfold gibbsEulerStep
  rw [dite_eq_left ht]
  exact gibbsScaledL2Resolvent_operatorEigen hV hprob _ _ rate hrate u hu

theorem implicitEulerMultiplier_tendsto (a : ℝ) :
    Tendsto (fun n : ℕ => (1 + a / (n + 1))⁻¹ ^ (n + 1)) atTop (𝓝 (Real.exp (-a))) := by
  have hh := ((Real.tendsto_one_add_div_pow_exp a).comp (tendsto_add_atTop_nat 1)).inv₀ (Real.exp_ne_zero a)
  simpa only [Function.comp_apply, Nat.cast_add, Nat.cast_one, ← inv_pow, ← Real.exp_neg] using hh

theorem gibbsEulerApproximation_tendsto_operatorEigen
    {V : E → ℝ} (hV : ContDiff ℝ 2 V)
    (hprob : IsProbabilityMeasure (gibbsMeasure volume V)) (t : NNReal)
    (rate : ℝ) (hrate : 0 ≤ rate) (u : E →₂[gibbsMeasure volume V] ℝ)
    (hu : (u, rate • u) ∈ (gibbsPositiveGenerator hV hprob).graph) :
    Tendsto (fun n => gibbsEulerApproximation hV hprob t n u) atTop
      (𝓝 (Real.exp (-(t : ℝ) * rate) • u)) := by
  by_cases ht : 0 < (t : ℝ)
  · have hh := (implicitEulerMultiplier_tendsto ((t : ℝ) * rate)).smul_const u
    have heq (n : ℕ) :
        gibbsEulerApproximation hV hprob t n u = (1 + ((t : ℝ) * rate) / (n + 1))⁻¹ ^ (n + 1) • u := by
      rw [gibbsEulerApproximation_operatorEigen hV hprob t ht rate hrate u hu]
      congr 3
      ring
    simpa only [← heq, neg_mul] using hh
  · have ht0 : t = 0 := NNReal.eq (le_antisymm (le_of_not_gt ht) t.property)
    subst t
    simp [gibbsEulerApproximation_zero]

/-- All actual L² vectors have genuine implicit-Euler strong limits.
The compact-resolvent spectral span and uniform contraction prove this. -/
theorem gibbsEulerApproximation_exists_limit
    {V : E → ℝ} (hV : ContDiff ℝ 2 V)
    (hprob : IsProbabilityMeasure (gibbsMeasure volume V))
    (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (t : NNReal) (u : E →₂[gibbsMeasure volume V] ℝ) :
    ∃ v, Tendsto (fun n => gibbsEulerApproximation hV hprob t n u) atTop (𝓝 v) := by
  let F := gibbsEulerApproximation hV hprob t
  let S := strongConvergenceDomain F
  have hs : IsClosed (S : Set (E →₂[gibbsMeasure volume V] ℝ)) :=
    strongConvergenceDomain_isClosed F (norm_gibbsEulerApproximation_apply_le hV hprob t)
  have hle : (⨆ rate : ℝ, gibbsOperatorEigenspace hV hprob rate) ≤ S := by
    apply iSup_le
    intro rate u hu
    by_cases hu0 : u = 0
    · subst u
      exact S.zero_mem
    · have hrate : 0 ≤ rate := gibbsOperatorEigenvalue_nonneg hV hprob rate ⟨u, hu⟩
        (by intro hh; exact hu0 (congrArg Subtype.val hh))
      exact ⟨Real.exp (-(t : ℝ) * rate) • u,
        gibbsEulerApproximation_tendsto_operatorEigen hV hprob t rate hrate u hu⟩
  have hi : Sᗮ = ⊥ := by
    have hh := Submodule.orthogonal_le hle
    rw [gibbsOperator_eigenspaces_orthogonal_eq_bot hV hprob ρ hρ hHess] at hh
    exact le_antisymm hh bot_le
  let : CompleteSpace S := hs.completeSpace_coe
  have htop : S = ⊤ := Submodule.orthogonal_eq_bot_iff.mp hi
  have hu : u ∈ S := by rw [htop]; trivial
  exact hu

end CutoffRigidity
