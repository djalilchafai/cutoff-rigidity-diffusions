module
public import CutoffRigidity.PositivePowerCalculus
public import CutoffRigidity.LangevinPositiveSquareInterpolation
public import CutoffRigidity.LangevinEntropyInterpolation
public import CutoffRigidity.LangevinDeBruijn

/-! # Actual source power energy identity for Langevin profiles -/
public section
namespace CutoffRigidity
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal
variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

/-- The source positive compact-perturbation transition profile satisfies
the exact Gross power integration identity. Its full operator domain and
all power test domains are derived from the actual stochastic evolution. -/
theorem langevinPositiveProfile_power_pairing
    {B : NNReal → Ω → E} {P : Measure Ω} (hB : IsEuclideanBrownian B P)
    {V g : E → ℝ} (hV : ContDiff ℝ 2 V)
    (hp : IsProbabilityMeasure (gibbsMeasure volume V))
    (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g)
    (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E,ρ*‖z‖^2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (c m : ℝ) (hm : 0 < m) (hpos : ∀ x,m ≤ c+g x)
    (p : ℝ) (hP : 2 ≤ p) (r : ℝ) :
    (∫ x,(langevinPositiveProfile V g B P c r x)^(p-1)*
      langevinProfileGenerator V g B P r x ∂gibbsMeasure volume V) =
      -(p-1)*∫ x,(langevinPositiveProfile V g B P c r x)^(p-2)*
        ‖gradient (langevinPositiveProfile V g B P c r) x‖^2 ∂gibbsMeasure volume V := by
  let := hp
  let μ := gibbsMeasure volume V
  let q := langevinPositiveProfile V g B P c r
  let D := langevinProfileGenerator V g B P r
  have hq : ContDiff ℝ 1 q := contDiff_const.add
    (contDiff_one_langevinKernel_integral hB hV ρ hρ.le hHess (hg.of_le (by norm_num)) hgc r.toNNReal)
  obtain ⟨A,hA,hqB⟩ := langevinPositiveProfile_uniform_norm_bound hB hV hg hgc ρ hρ hHess c
  have hqLp : MemLp q 2 μ := MemLp.of_bound hq.continuous.aestronglyMeasurable A
    (Eventually.of_forall (hqB r))
  obtain ⟨G,hG,hGrad⟩ := langevinPositiveProfile_gradient_bound hB hV hg hgc ρ hρ hHess c r
  have hgqLp : MemLp (gradient q) 2 μ := MemLp.of_bound
    (continuous_gradient_of_c1 hq).aestronglyMeasurable G (Eventually.of_forall hGrad)
  let U := gibbsConstantLp hp c + langevinCompactTestLp hB hV ρ hρ.le hHess hg.continuous hgc μ r.toNNReal
  let H := -langevinCompactTestLp hB hV ρ hρ.le hHess
    (continuous_langevinDifferentialOperator hV hg) (hasCompactSupport_langevinDifferentialOperator V hgc) μ r.toNNReal
  have hGraph : (U,H) ∈ (gibbsPositiveGenerator hV hp).graph := by
    have hh := (gibbsPositiveGenerator hV hp).graph.add_mem (gibbsConstantLp_graph_mem hV hp c)
      (langevinCompactTestLp_mem_operatorGraph hB hV hp ρ hρ hHess hg hgc r.toNNReal)
    simpa only [Prod.mk_add_mk,zero_add] using hh
  have hUrep : U =ᵐ[μ] q := by
    filter_upwards [Lp.coeFn_add (gibbsConstantLp hp c)
      (langevinCompactTestLp hB hV ρ hρ.le hHess hg.continuous hgc μ r.toNNReal),
      (memLp_const c : MemLp (fun _ : E => c) 2 μ).coeFn_toLp,
      langevinCompactTestLp_coeFn hB hV ρ hρ.le hHess hg.continuous hgc μ r.toNNReal] with x hadd hc hx
    change _ = c+_
    have hc' : (gibbsConstantLp hp c : E → ℝ) x = c := by convert! hc using 1
    rw [hadd,Pi.add_apply,hc',hx]
  have hHrep : H =ᵐ[μ] fun x => -D x := by
    filter_upwards [Lp.coeFn_neg (langevinCompactTestLp hB hV ρ hρ.le hHess
      (continuous_langevinDifferentialOperator hV hg) (hasCompactSupport_langevinDifferentialOperator V hgc) μ r.toNNReal),
      langevinCompactTestLp_coeFn hB hV ρ hρ.le hHess (continuous_langevinDifferentialOperator hV hg)
        (hasCompactSupport_langevinDifferentialOperator V hgc) μ r.toNNReal] with x hneg hx
    rw [hneg,Pi.neg_apply,hx]
    rfl
  have hh := c1_operatorGraph_power_pairing hV hp ρ hρ hHess hq hqLp hgqLp hm
    (langevinPositiveProfile_lower hB hV hg hgc ρ hρ.le hHess c m hpos r)
    (fun x => (le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using hqB r x)) hP
    U H hGraph hUrep hHrep
  simp only [mul_neg,integral_neg] at hh
  change (∫ x,q x^(p-1)*D x ∂μ) = -(p-1)*∫ x,q x^(p-2)*‖gradient q x‖^2 ∂μ
  linarith only [hh]

end CutoffRigidity
