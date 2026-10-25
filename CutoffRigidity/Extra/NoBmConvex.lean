module

public import CutoffRigidity.ConvexInteractionCurvature
public import CutoffRigidity.GibbsMoments
public import Mathlib.Analysis.Calculus.BumpFunction.Convolution
public import Mathlib.Analysis.Calculus.BumpFunction.Normed
public import Mathlib.Analysis.Convolution

/-! # Brownian-free LSI: a `C²` function with nonnegative Hessian is convex -/

public section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ContDiff ENNReal NNReal Convolution

namespace CutoffRigidity.NoBm

variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

set_option maxHeartbeats 1000000 in
/-- A `C²` function with nonnegative Hessian is convex. -/
theorem convexOn_univ_of_hessian_nonneg {U : E → ℝ} (hU : ContDiff ℝ 2 U)
    (h : ∀ x z : E, 0 ≤ fderiv ℝ (fderiv ℝ U) x z z) : ConvexOn ℝ univ U := by
  refine ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩
  set z : E := y - x with hz
  let g : ℝ → ℝ := fun t => U (x + t • z)
  have hline (t : ℝ) : HasDerivAt (fun s : ℝ => x + s • z) z t := by
    simpa using ((hasDerivAt_id t).smul_const z).const_add x
  have hdU : Differentiable ℝ U := hU.differentiable (by norm_num)
  have hdU2 : Differentiable ℝ (fderiv ℝ U) :=
    (hU.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  have hgd (t : ℝ) : HasDerivAt g (fderiv ℝ U (x + t • z) z) t :=
    (hdU (x + t • z)).hasFDerivAt.comp_hasDerivAt t (hline t)
  have hident : deriv g = fun t => fderiv ℝ U (x + t • z) z := funext fun t => (hgd t).deriv
  have hgd2 (t : ℝ) : HasDerivAt (deriv g) (fderiv ℝ (fderiv ℝ U) (x + t • z) z z) t := by
    rw [hident]
    have hchain := ((hdU2 (x + t • z)).hasFDerivAt.comp_hasDerivAt t (hline t)).clm_apply
      (hasDerivAt_const t z)
    simpa using hchain
  have hg : ConvexOn ℝ univ g := by
    refine convexOn_univ_of_deriv2_nonneg (fun t => (hgd t).differentiableAt)
      (fun t => (hgd2 t).differentiableAt) (fun t => ?_)
    simp only [Function.iterate_succ, Function.iterate_zero, Function.comp_apply, id]
    rw [(hgd2 t).deriv]
    exact h _ _
  have := hg.2 (mem_univ 0) (mem_univ 1) ha hb hab
  have e : a = 1 - b := by linarith
  simp only [g, smul_eq_mul, zero_smul, add_zero, mul_zero, mul_one, zero_add, one_smul] at this
  have e2 : x + b • z = a • x + b • y := by
    rw [hz, e, smul_sub, sub_smul, one_smul]; abel
  rw [e2, show x + z = y by rw [hz]; abel] at this
  simpa [smul_eq_mul] using this

end CutoffRigidity.NoBm
