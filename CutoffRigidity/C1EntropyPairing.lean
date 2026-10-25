module
public import CutoffRigidity.C1FisherInformation
public import CutoffRigidity.EntropyDissipation
public import CutoffRigidity.GibbsOperatorDomainPDE

/-! # Entropy pairing on the true C¹ operator domain

The logarithmic test is placed in the actual closed H¹ graph from C¹
regularity and explicit positive bounds. The genuine operator/form equation
then gives the entropy energy identity without a C² density premise.
-/
public section
namespace CutoffRigidity
open MeasureTheory Filter
variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

/-- Explicit uniform control of the entropy derivative on a positive interval. -/
theorem norm_one_add_log_le_of_bounds {a m M : ℝ}
    (hm : 0 < m) (ha : m ≤ a) (hM : a ≤ M) :
    ‖1 + Real.log a‖ ≤ 1 + |Real.log m| + |Real.log M| := by
  have hlo := Real.log_le_log hm ha
  have hhi := Real.log_le_log (hm.trans_le ha) hM
  have hlog : |Real.log a| ≤ |Real.log m| + |Real.log M| := by
    rw [abs_le]
    constructor
    · have hh := neg_abs_le (Real.log m)
      linarith [abs_nonneg (Real.log M)]
    · have hh := le_abs_self (Real.log M)
      linarith [abs_nonneg (Real.log m)]
  have hh := norm_add_le (1 : ℝ) (Real.log a)
  simp only [Real.norm_eq_abs, abs_one] at hh ⊢
  linarith

/-- The genuine logarithmic entropy test belongs to H¹ on the explicit
positive bounded C¹ density domain. -/
theorem entropy_test_memLp {μ : Measure E} [IsProbabilityMeasure μ] {f : E → ℝ}
    (hf : ContDiff ℝ 1 f) {m M : ℝ} (hm : 0 < m)
    (hlow : ∀ x, m ≤ f x) (hup : ∀ x, f x ≤ M)
    (hg : MemLp (gradient f) 2 μ) :
    MemLp (fun x => 1 + Real.log (f x)) 2 μ ∧
      MemLp (gradient (fun x => 1 + Real.log (f x))) 2 μ := by
  have hpos (x : E) : 0 < f x := hm.trans_le (hlow x)
  have hlog : ContDiff ℝ 1 (fun x => 1 + Real.log (f x)) :=
    contDiff_const.add (hf.log (fun x => (hpos x).ne'))
  constructor
  · exact MemLp.of_bound hlog.continuous.aestronglyMeasurable
      (1 + |Real.log m| + |Real.log M|)
      (Eventually.of_forall (fun x => norm_one_add_log_le_of_bounds hm (hlow x) (hup x)))
  · apply (memLp_two_iff_integrable_sq_norm (continuous_gradient_of_c1 hlog).aestronglyMeasurable).mpr
    apply (hg.norm.integrable_sq.const_mul (m⁻¹ ^ 2)).mono'
      ((continuous_gradient_of_c1 hlog).norm.pow 2).aestronglyMeasurable
    filter_upwards with x
    change ‖‖gradient (fun y => 1 + Real.log (f y)) x‖ ^ 2‖ ≤ _
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _),
      gradient_one_add_log_density f (hf.differentiable one_ne_zero x) (hpos x), norm_smul,
      Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (hpos x).le), mul_pow]
    have hi : (f x)⁻¹ ≤ m⁻¹ := inv_anti₀ hm (hlow x)
    exact mul_le_mul_of_nonneg_right
      ((sq_le_sq₀ (inv_nonneg.mpr (hpos x).le) (inv_nonneg.mpr hm.le)).mpr hi) (sq_nonneg _)

/-- True operator-domain entropy pairing for actual C¹ representatives.
All logarithmic Sobolev membership is derived from the displayed bounds. -/
theorem c1_operatorGraph_entropy_pairing {V f h : E → ℝ}
    (hV : ContDiff ℝ 2 V) (hp : IsProbabilityMeasure (gibbsMeasure volume V))
    (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (hf : ContDiff ℝ 1 f) (hfLp : MemLp f 2 (gibbsMeasure volume V))
    (hg : MemLp (gradient f) 2 (gibbsMeasure volume V))
    {m M : ℝ} (hm : 0 < m) (hlow : ∀ x, m ≤ f x) (hup : ∀ x, f x ≤ M)
    (U H : E →₂[gibbsMeasure volume V] ℝ)
    (hUH : (U, H) ∈ (gibbsPositiveGenerator hV hp).graph)
    (hU : U =ᵐ[gibbsMeasure volume V] f) (hH : H =ᵐ[gibbsMeasure volume V] h) :
    (∫ x, (1 + Real.log (f x)) * h x ∂gibbsMeasure volume V) =
      ∫ x, ‖gradient f x‖ ^ 2 / f x ∂gibbsMeasure volume V := by
  let := hp
  let μ := gibbsMeasure volume V
  let ψ := fun x => 1 + Real.log (f x)
  have hpos (x : E) : 0 < f x := hm.trans_le (hlow x)
  have hψ : ContDiff ℝ 1 ψ := contDiff_const.add (hf.log (fun x => (hpos x).ne'))
  obtain ⟨hψLp, hGψLp⟩ := entropy_test_memLp hf hm hlow hup hg
  let vf := c1GibbsSobolevLift hV hp ρ hρ hHess hf hfLp hg
  let vψ := c1GibbsSobolevLift hV hp ρ hρ hHess hψ hψLp hGψLp
  have hUf : U = hfLp.toLp f := Lp.ext (hU.trans hfLp.coeFn_toLp.symm)
  have hlift : gibbsOperatorGraphSobolevLift hV hp U H = vf := by
    apply gibbsSobolevInclusion_injective hV hp
    rw [gibbsOperatorGraphSobolevLift_inclusion hV hp U H hUH]
    exact hUf
  have hh := gibbsOperatorGraph_weak_equation hV hp U H hUH vψ
  rw [hlift] at hh
  have hleft : gibbsDirichletEnergy hV hp vf vψ =
      ∫ x, ‖gradient f x‖ ^ 2 / f x ∂μ := by
    rw [gibbsDirichletEnergy, L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hg.coeFn_toLp, hGψLp.coeFn_toLp] with x hgf hgψ
    change inner ℝ (hg.toLp (gradient f) x) (hGψLp.toLp (gradient ψ) x) = _
    rw [hgf, hgψ, gradient_one_add_log_density f (hf.differentiable one_ne_zero x) (hpos x),
      inner_smul_right, real_inner_self_eq_norm_sq]
    ring
  have hright : inner ℝ H (gibbsSobolevInclusion hV hp vψ) =
      ∫ x, ψ x * h x ∂μ := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hH, hψLp.coeFn_toLp] with x hx hxψ
    change inner ℝ (H x) (hψLp.toLp ψ x) = _
    rw [hx, hxψ, Real.inner_apply, mul_comm]
  rw [hleft, hright] at hh
  exact hh.symm

end CutoffRigidity
