module

public import CutoffRigidity.GibbsStationarity

/-! # Genuine compact-test Bochner coercivity

For actual C² potentials and compact C³ tests, compact support discharges
all integration domains. The squared actual Langevin differential operator
has the exact integrated Hessian identity and curvature coercivity. No
spectral-domain or semigroup regularity assertion is assumed here.
-/

public section

namespace CutoffRigidity

open MeasureTheory

variable {d : ℕ}

/-- The actual Langevin differential expression is C¹ on C³ tests for a
C² potential; no smoothness of a semigroup is assumed. -/
theorem contDiff_one_langevinDifferentialOperator
    {V f : EuclideanSpace ℝ (Fin d) → ℝ} (hV : ContDiff ℝ 2 V) (hf : ContDiff ℝ 3 f) :
    ContDiff ℝ 1 (langevinDifferentialOperator V f) := by
  have hV1 (i : Fin d) : ContDiff ℝ 1 (coordinateDerivative i V) := by
    apply contDiff_coordinateDerivative
    convert hV using 1
    norm_num
  have hf1 (i : Fin d) : ContDiff ℝ 2 (coordinateDerivative i f) := by
    apply contDiff_coordinateDerivative
    convert hf using 1
    norm_num
  have hf2 (i j : Fin d) : ContDiff ℝ 1 (coordinateDerivative j (coordinateDerivative i f)) := by
    apply contDiff_coordinateDerivative
    convert hf1 i using 1
    norm_num
  have heq : langevinDifferentialOperator V f = fun x =>
      (∑ i : Fin d, coordinateDerivative i (coordinateDerivative i f) x) -
        ∑ i : Fin d, coordinateDerivative i V x * coordinateDerivative i f x :=
    funext (langevin_eq_coordinate_sum V f)
  rw [heq]
  have hf1' (i : Fin d) : ContDiff ℝ 1 (coordinateDerivative i f) := (hf1 i).of_le (by norm_num)
  fun_prop

/-- Compact differentiated tests allow a C¹ multiplier in the genuine
weighted energy identity. All products are integrable by compact support. -/
theorem gibbs_energy_compact_differentiated_test_c1
    {V f g : EuclideanSpace ℝ (Fin d) → ℝ} (hV : ContDiff ℝ 2 V)
    (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g) :
    (∫ x, f x * langevinDifferentialOperator V g x ∂gibbsMeasure volume V) =
      -(∫ x, inner ℝ (gradient f x) (gradient g x) ∂gibbsMeasure volume V) := by
  have hDg (i : Fin d) : ContDiff ℝ 1 (coordinateDerivative i g) := by
    apply contDiff_coordinateDerivative
    convert hg using 1
    norm_num
  have hDf (i : Fin d) : ContDiff ℝ 0 (coordinateDerivative i f) := by
    apply contDiff_coordinateDerivative
    convert hf using 1
    norm_num
  have hDV (i : Fin d) : ContDiff ℝ 1 (coordinateDerivative i V) := by
    apply contDiff_coordinateDerivative
    convert hV using 1
    norm_num
  have hDD (i : Fin d) : Continuous (coordinateDerivative i (coordinateDerivative i g)) := by
    have h : ContDiff ℝ 0 (coordinateDerivative i (coordinateDerivative i g)) := by
      apply contDiff_coordinateDerivative
      convert hDg i using 1
      norm_num
    exact h.continuous
  have hDc (i : Fin d) : HasCompactSupport (coordinateDerivative i g) :=
    hgc.fderiv_apply ℝ (EuclideanSpace.single i 1)
  have hDDc (i : Fin d) : HasCompactSupport (coordinateDerivative i (coordinateDerivative i g)) :=
    (hDc i).fderiv_apply ℝ (EuclideanSpace.single i 1)
  apply integral_mul_langevin_eq_neg_gradient_inner (hV.differentiable (by norm_num))
    (hf.differentiable (by norm_num)) hg
  · intro i
    change Integrable (fun x => f x * coordinateDerivative i g x) _
    apply integrable_gibbs_of_continuous_hasCompactSupport hV.continuous
      (hf.continuous.mul (hDg i).continuous)
    simpa only [Pi.mul_def] using (hDc i).mul_left (f := f)
  · intro i
    change Integrable (fun x => f x * coordinateDerivative i (coordinateDerivative i g) x) _
    apply integrable_gibbs_of_continuous_hasCompactSupport hV.continuous (hf.continuous.mul (hDD i))
    simpa only [Pi.mul_def] using (hDDc i).mul_left (f := f)
  · intro i
    change Integrable (fun x => coordinateDerivative i f x * coordinateDerivative i g x) _
    apply integrable_gibbs_of_continuous_hasCompactSupport hV.continuous
      ((hDf i).continuous.mul (hDg i).continuous)
    simpa only [Pi.mul_def] using (hDc i).mul_left (f := coordinateDerivative i f)
  · intro i
    change Integrable (fun x => f x * coordinateDerivative i V x * coordinateDerivative i g x) _
    apply integrable_gibbs_of_continuous_hasCompactSupport hV.continuous
      ((hf.continuous.mul (hDV i).continuous).mul (hDg i).continuous)
    simpa only [Pi.mul_def] using (hDc i).mul_left (f := fun x => f x * coordinateDerivative i V x)

/-- Exact integrated Bochner identity for the squared actual differential
generator on its compact C³ core, with every domain premise discharged. -/
theorem integral_langevin_sq_eq_hessian_energy_compact
    {V f : EuclideanSpace ℝ (Fin d) → ℝ} (hV : ContDiff ℝ 2 V) (hf : ContDiff ℝ 3 f)
    (hfc : HasCompactSupport f) :
    (∫ x, langevinDifferentialOperator V f x ^ 2 ∂gibbsMeasure volume V) =
      (∫ x, ∑ i : Fin d, ∑ j : Fin d,
        coordinateDerivative j (coordinateDerivative i f) x ^ 2 ∂gibbsMeasure volume V) +
      (∫ x, fderiv ℝ (fderiv ℝ V) x (gradient f x) (gradient f x) ∂gibbsMeasure volume V) := by
  have he := gibbs_energy_compact_differentiated_test_c1 hV
    (contDiff_one_langevinDifferentialOperator hV hf) (hf.of_le (by norm_num)) hfc
  have hb := integrated_bochner_identity hV hf (bochnerIntegrationDomain_of_hasCompactSupport hV hf hfc)
  calc
    _ = ∫ x, langevinDifferentialOperator V f x * langevinDifferentialOperator V f x
        ∂gibbsMeasure volume V := by simp only [pow_two]
    _ = -(∫ x, inner ℝ (gradient (langevinDifferentialOperator V f) x) (gradient f x)
        ∂gibbsMeasure volume V) := he
    _ = -(∫ x, inner ℝ (gradient f x) (gradient (langevinDifferentialOperator V f) x)
        ∂gibbsMeasure volume V) := by
      congr 1
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun x => real_inner_comm _ _)
    _ = _ := hb

/-- Compact C³ tests have genuine integrable squared gradient against the
actual Gibbs measure, without a global moment premise. -/
theorem integrable_gradient_norm_sq_compact
    {V f : EuclideanSpace ℝ (Fin d) → ℝ} (hV : Continuous V) (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) :
    Integrable (fun x => ‖gradient f x‖ ^ 2) (gibbsMeasure volume V) := by
  have hG : HasCompactSupport (gradient f) :=
    (hfc.fderiv ℝ).comp_left (g := (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin d))).symm) (by simp)
  have hc : HasCompactSupport (fun x => ‖gradient f x‖ ^ 2) :=
    hG.comp_left (g := fun z => ‖z‖ ^ 2) (by simp)
  exact integrable_gibbs_of_continuous_hasCompactSupport hV
    ((differentiable_gradient_of_contDiff_two hf).continuous.norm.pow 2) hc

/-- Curvature coercivity with its nonnegative squared-Hessian remainder on
the actual compact C³ test core. -/
theorem integral_langevin_sq_ge_curvature_gradient_hessian_compact
    {V f : EuclideanSpace ℝ (Fin d) → ℝ} (hV : ContDiff ℝ 2 V) (hf : ContDiff ℝ 3 f)
    (hfc : HasCompactSupport f) (ρ : ℝ)
    (hHess : ∀ x z, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z) :
    ρ * (∫ x, ‖gradient f x‖ ^ 2 ∂gibbsMeasure volume V) +
      (∫ x, ∑ i : Fin d, ∑ j : Fin d,
        coordinateDerivative j (coordinateDerivative i f) x ^ 2 ∂gibbsMeasure volume V) ≤
      (∫ x, langevinDifferentialOperator V f x ^ 2 ∂gibbsMeasure volume V) := by
  have hb := integrated_bochner_inequality hV hf (bochnerIntegrationDomain_of_hasCompactSupport hV hf hfc)
    (integrable_gradient_norm_sq_compact hV.continuous (hf.of_le (by norm_num)) hfc) ρ hHess
  have hid := integral_langevin_sq_eq_hessian_energy_compact hV hf hfc
  rw [integrated_bochner_identity hV hf (bochnerIntegrationDomain_of_hasCompactSupport hV hf hfc)] at hb
  rwa [← hid] at hb

/-- The compact-test source Bochner coercivity, with no integration-domain
or spectral assumption hidden in the hypotheses. -/
theorem integral_langevin_sq_ge_curvature_gradient_compact
    {V f : EuclideanSpace ℝ (Fin d) → ℝ} (hV : ContDiff ℝ 2 V) (hf : ContDiff ℝ 3 f)
    (hfc : HasCompactSupport f) (ρ : ℝ)
    (hHess : ∀ x z, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z) :
    ρ * (∫ x, ‖gradient f x‖ ^ 2 ∂gibbsMeasure volume V) ≤
      (∫ x, langevinDifferentialOperator V f x ^ 2 ∂gibbsMeasure volume V) := by
  have h := integral_langevin_sq_ge_curvature_gradient_hessian_compact hV hf hfc ρ hHess
  have hn : 0 ≤ (∫ x, ∑ i : Fin d, ∑ j : Fin d,
      coordinateDerivative j (coordinateDerivative i f) x ^ 2 ∂gibbsMeasure volume V) :=
    integral_nonneg (fun x => Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => sq_nonneg _)))
  linarith

end CutoffRigidity
