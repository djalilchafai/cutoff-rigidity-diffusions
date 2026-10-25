module
public import CutoffRigidity.GibbsHeatMarkov
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! # Actual Bochner time integrals of canonical Gibbs heat evolution -/
public section
namespace CutoffRigidity
open MeasureTheory Filter Topology
variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

@[expose] noncomputable def gibbsHeatTimeIntegral
    {V : E → ℝ} (hV : ContDiff ℝ 2 V)
    (hprob : IsProbabilityMeasure (gibbsMeasure volume V))
    (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (t : NNReal) : (E →₂[gibbsMeasure volume V] ℝ) →L[ℝ] (E →₂[gibbsMeasure volume V] ℝ) := by
  let P := gibbsHeatSemigroup hV hprob ρ hρ hHess
  have hc (u : E →₂[gibbsMeasure volume V] ℝ) : Continuous (fun s : ℝ => P s.toNNReal u) :=
    (continuous_gibbsHeatSemigroup_apply hV hprob ρ hρ hHess u).comp continuous_real_toNNReal
  let F : (E →₂[gibbsMeasure volume V] ℝ) →ₗ[ℝ] (E →₂[gibbsMeasure volume V] ℝ) := {
    toFun := fun u => ∫ s in (0 : ℝ)..(t : ℝ), P s.toNNReal u
    map_add' := fun u v => by
      simp only [map_add]
      exact intervalIntegral.integral_add (hc u |>.intervalIntegrable _ _) (hc v |>.intervalIntegrable _ _)
    map_smul' := fun c u => by
      simp only [map_smul]
      exact intervalIntegral.integral_smul c _ }
  refine F.mkContinuous (t : ℝ) (fun u => ?_)
  change ‖∫ s in (0 : ℝ)..(t : ℝ), P s.toNNReal u‖ ≤ (t : ℝ) * ‖u‖
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := (t : ℝ))
    (fun s _ => norm_gibbsHeatSemigroup_apply_le hV hprob ρ hρ hHess s.toNNReal u)
  convert! hb using 1
  rw [sub_zero]
  exact (mul_comm (t : ℝ) ‖u‖).trans (congrArg (‖u‖ * ·) (abs_of_nonneg t.property).symm)

theorem gibbsHeatTimeIntegral_apply
    {V : E → ℝ} (hV : ContDiff ℝ 2 V)
    (hprob : IsProbabilityMeasure (gibbsMeasure volume V))
    (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (t : NNReal) (u : E →₂[gibbsMeasure volume V] ℝ) :
    gibbsHeatTimeIntegral hV hprob ρ hρ hHess t u =
      ∫ s in (0 : ℝ)..(t : ℝ), gibbsHeatSemigroup hV hprob ρ hρ hHess s.toNNReal u := rfl

theorem gibbsHeatTimeIntegral_operatorEigen
    {V : E → ℝ} (hV : ContDiff ℝ 2 V)
    (hprob : IsProbabilityMeasure (gibbsMeasure volume V))
    (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (t : NNReal) (rate : ℝ) (hrate : 0 ≤ rate) (u : E →₂[gibbsMeasure volume V] ℝ)
    (hu : (u, rate • u) ∈ (gibbsPositiveGenerator hV hprob).graph) :
    gibbsHeatTimeIntegral hV hprob ρ hρ hHess t u =
      (∫ s in (0 : ℝ)..(t : ℝ), Real.exp (-s * rate)) • u := by
  rw [gibbsHeatTimeIntegral_apply, ← intervalIntegral.integral_smul_const]
  apply intervalIntegral.integral_congr
  intro s hs
  have hs0 : 0 ≤ s := by
    exact (le_min le_rfl t.property).trans hs.1
  have he := gibbsHeatSemigroup_operatorEigen hV hprob ρ hρ hHess s.toNNReal rate hrate u hu
  simpa only [Real.coe_toNNReal s hs0] using he

/-- Scalar FTC identity behind the actual resolvent evolution equation. -/
theorem heat_resolvent_scalar_identity (t rate : ℝ) (hrate : 0 ≤ rate) :
    Real.exp (-t * rate) * (1 + rate)⁻¹ = (1 + rate)⁻¹ -
      (1 - (1 + rate)⁻¹) * (∫ s in (0 : ℝ)..t, Real.exp (-s * rate)) := by
  have hd (s : ℝ) : HasDerivAt (fun s : ℝ => Real.exp (-s * rate)) (Real.exp (-s * rate) * (-rate)) s := by
    have ha : HasDerivAt (fun s : ℝ => -s * rate) (-rate) s := by
      convert (hasDerivAt_id s).mul_const (-rate) using 1
      · funext x
        simp only [id_eq]
        ring
      · ring
    convert ha.exp using 1
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := 0) (b := t) (fun s _ => hd s)
    ((by fun_prop : Continuous (fun s : ℝ => Real.exp (-s * rate) * (-rate))).intervalIntegrable 0 t)
  have hi' : (∫ s in (0 : ℝ)..t, Real.exp (-s * rate)) * (-rate) = Real.exp (-t * rate) - 1 := by
    simpa only [intervalIntegral.integral_mul_const, neg_zero, zero_mul, Real.exp_zero] using hi
  have hc : 1 + rate ≠ 0 := ne_of_gt (by linarith)
  have hc0 : (1 + rate) * (1 + rate)⁻¹ = 1 := mul_inv_cancel₀ hc
  have hm := congrArg (fun x : ℝ => x * (∫ s in (0 : ℝ)..t, Real.exp (-s * rate))) hc0
  have hm2 := congrArg (fun x : ℝ => x * (1 + rate)⁻¹) hi'
  nlinarith only [hc0, hm, hm2]

end CutoffRigidity
