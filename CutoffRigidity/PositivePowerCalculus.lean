module
public import CutoffRigidity.C1EntropyPairing
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-! # Actual positive power calculus for the Gross interpolation

Real powers of actual positive bounded C¹ functions have their actual
gradients and genuine H¹ membership. The power energy pairing uses the
true self-adjoint generator graph, not a supplied integration identity.
-/
public section
namespace CutoffRigidity
open MeasureTheory Filter Set
open scoped Topology NNReal ENNReal
variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

/-- Actual real-power gradient at every positive differentiability point. -/
theorem gradient_rpow_at_positive {f : E → ℝ} {x : E}
    (hf : DifferentiableAt ℝ f x) (hpos : 0 < f x) (p : ℝ) :
    gradient (fun y => f y^p) x = (p*f x^(p-1)) • gradient f x := by
  apply ext_inner_right ℝ
  intro z
  rw [inner_gradient_left,real_inner_smul_left,inner_gradient_left,
    (hf.hasFDerivAt.rpow_const (Or.inl hpos.ne')).fderiv]
  rfl

/-- Bounded positive powers belong to actual L²; their true gradients
are L² whenever the original actual gradient is L². -/
theorem positive_c1_rpow_memLp
    (μ : Measure E) [IsProbabilityMeasure μ] {f : E → ℝ} (hf : ContDiff ℝ 1 f)
    (hgrad : MemLp (gradient f) 2 μ) {m M p : ℝ}
    (hm : 0 < m) (hlow : ∀ x,m ≤ f x) (hupp : ∀ x,f x ≤ M) (hp : 1 ≤ p) :
    MemLp (fun x => f x^p) 2 μ ∧ MemLp (gradient (fun x => f x^p)) 2 μ := by
  have hpos (x : E) : 0 < f x := hm.trans_le (hlow x)
  have hM : 0 < M := (hpos 0).trans_le (hupp 0)
  have hC : ContDiff ℝ 1 (fun x => f x^p) := hf.rpow_const_of_ne (fun x => (hpos x).ne')
  constructor
  · apply MemLp.of_bound hC.continuous.aestronglyMeasurable (M^p)
    apply Eventually.of_forall
    intro x
    rw [Real.norm_of_nonneg (Real.rpow_nonneg (hpos x).le _)]
    exact Real.rpow_le_rpow (hpos x).le (hupp x) (by linarith)
  · apply hgrad.of_le_mul (c := p*M^(p-1)) (continuous_gradient_of_c1 hC).aestronglyMeasurable
    apply Eventually.of_forall
    intro x
    rw [gradient_rpow_at_positive (hf.differentiable one_ne_zero x) (hpos x),norm_smul,
      Real.norm_of_nonneg (mul_nonneg (by linarith) (Real.rpow_nonneg (hpos x).le _))]
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (hpos x).le (hupp x) (by linarith)) (by linarith)

/-- The genuine operator-domain power energy identity. The displayed
operator graph and representative are actual objects; the test-domain and
power integration-by-parts identity are derived. -/
theorem c1_operatorGraph_power_pairing {V f h : E → ℝ}
    (hV : ContDiff ℝ 2 V) (hp : IsProbabilityMeasure (gibbsMeasure volume V))
    (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E,ρ*‖z‖^2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (hf : ContDiff ℝ 1 f) (hfLp : MemLp f 2 (gibbsMeasure volume V))
    (hgrad : MemLp (gradient f) 2 (gibbsMeasure volume V))
    {m M p : ℝ} (hm : 0 < m) (hlow : ∀ x,m ≤ f x) (hupp : ∀ x,f x ≤ M) (hP : 2 ≤ p)
    (U H : E →₂[gibbsMeasure volume V] ℝ)
    (hGraph : (U,H) ∈ (gibbsPositiveGenerator hV hp).graph)
    (hU : U =ᵐ[gibbsMeasure volume V] f) (hH : H =ᵐ[gibbsMeasure volume V] h) :
    (∫ x,f x^(p-1)*h x ∂gibbsMeasure volume V) =
      (p-1)*∫ x,f x^(p-2)*‖gradient f x‖^2 ∂gibbsMeasure volume V := by
  let := hp
  let μ := gibbsMeasure volume V
  let ψ := fun x => f x^(p-1)
  have hpos (x : E) : 0 < f x := hm.trans_le (hlow x)
  have hψ : ContDiff ℝ 1 ψ := hf.rpow_const_of_ne (fun x => (hpos x).ne')
  obtain ⟨hψLp,hGψLp⟩ := positive_c1_rpow_memLp μ hf hgrad hm hlow hupp (show 1 ≤ p-1 by linarith)
  let vf := c1GibbsSobolevLift hV hp ρ hρ hHess hf hfLp hgrad
  let vψ := c1GibbsSobolevLift hV hp ρ hρ hHess hψ hψLp hGψLp
  have hUf : U = hfLp.toLp f := Lp.ext (hU.trans hfLp.coeFn_toLp.symm)
  have hlift : gibbsOperatorGraphSobolevLift hV hp U H = vf := by
    apply gibbsSobolevInclusion_injective hV hp
    rw [gibbsOperatorGraphSobolevLift_inclusion hV hp U H hGraph]
    exact hUf
  have hh := gibbsOperatorGraph_weak_equation hV hp U H hGraph vψ
  rw [hlift] at hh
  have hLeft : gibbsDirichletEnergy hV hp vf vψ =
      (p-1)*∫ x,f x^(p-2)*‖gradient f x‖^2 ∂μ := by
    rw [gibbsDirichletEnergy,L2.inner_def,← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [hgrad.coeFn_toLp,hGψLp.coeFn_toLp] with x hgf hgψ
    change inner ℝ (hgrad.toLp (gradient f) x) (hGψLp.toLp (gradient ψ) x) = _
    rw [hgf,hgψ,gradient_rpow_at_positive (hf.differentiable one_ne_zero x) (hpos x),
      inner_smul_right,real_inner_self_eq_norm_sq]
    have he : p-1-1 = p-2 := by ring
    rw [he]
    ring
  have hRight : inner ℝ H (gibbsSobolevInclusion hV hp vψ) = ∫ x,f x^(p-1)*h x ∂μ := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hH,hψLp.coeFn_toLp] with x hx hxψ
    change inner ℝ (H x) (hψLp.toLp ψ x) = _
    rw [hx,hxψ,Real.inner_apply,mul_comm]
  rw [hLeft,hRight] at hh
  exact hh.symm

end CutoffRigidity
