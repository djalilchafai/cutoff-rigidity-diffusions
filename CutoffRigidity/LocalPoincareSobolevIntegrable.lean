module
public import CutoffRigidity.LocalPoincareSobolev
public import CutoffRigidity.GibbsSobolevBoundedChain
public import CutoffRigidity.VarianceFatou

/-! # Full integrable weak domain of genuine local Poincare

Bounded normal contractions of actual closed H¹ vectors yield the second
moment of an integrable weak test, using centered Fatou. Neither that second
moment nor a smooth representative is assumed.
-/
public section
namespace CutoffRigidity
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal
variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

theorem contDiff_two_smoothNormalTruncation (n : ℕ) : ContDiff ℝ 2 (smoothNormalTruncation n) := by
  have hh : ContDiff ℝ 2 (fun r : ℝ => Real.arctan (r / ((n : ℝ)+1))) :=
    (Real.contDiff_arctan : ContDiff ℝ 2 Real.arctan).comp (contDiff_id.div_const ((n : ℝ)+1))
  exact contDiff_const.mul hh

set_option maxHeartbeats 800000 in
theorem localPoincare_integrable_gibbsSobolev
    {V : E → ℝ} (hV : ContDiff ℝ 2 V)
    (hp : IsProbabilityMeasure (gibbsMeasure volume V))
    (ν : Measure E) [IsProbabilityMeasure ν] (hAC : ν ≪ gibbsMeasure volume V)
    (C : ℝ) (hC : 0 ≤ C) (hP : HasLocalSmoothPoincare ν C)
    (hloc : ∀ K : Set E, IsCompact K → ∃ M : ENNReal, M ≠ ⊤ ∧ ν.restrict K ≤ M • volume)
    (u : gibbsSobolevGraph hV hp)
    (hU : Integrable (fun x => gibbsSobolevInclusion hV hp u x) ν)
    (hD : MemLp (fun x => gibbsSobolevDerivative hV hp u x) 2 ν) :
    MemLp (fun x => gibbsSobolevInclusion hV hp u x) 2 ν ∧
      variance (fun x => gibbsSobolevInclusion hV hp u x) ν ≤
        C * ∫ x, ‖gibbsSobolevDerivative hV hp u x‖^2 ∂ν := by
  let U := gibbsSobolevInclusion hV hp u
  let D := gibbsSobolevDerivative hV hp u
  let fn := fun n : ℕ => fun x : E => smoothNormalTruncation n (U x)
  have hfnM (n : ℕ) : AEStronglyMeasurable (fn n) ν :=
    (contDiff_smoothNormalTruncation n).continuous.comp_aestronglyMeasurable (Lp.stronglyMeasurable U).aestronglyMeasurable
  have hfnLp (n : ℕ) : MemLp (fn n) 2 ν := MemLp.of_bound (hfnM n) (((n : ℝ)+1)*(Real.pi/2))
    (Eventually.of_forall (fun x => smoothNormalTruncation_abs_le_bound n (U x)))
  have hvar (n : ℕ) : variance (fn n) ν ≤ C * ∫ x, ‖D x‖^2 ∂ν := by
    obtain ⟨v,hv,hDv,_⟩ := gibbsSobolev_smooth_normal_contraction hV hp
      (contDiff_two_smoothNormalTruncation n)
      (by simp [smoothNormalTruncation]) (deriv_smoothNormalTruncation_abs_le_one n) u
    have hdBound : ∀ᵐ x ∂ν, ‖gibbsSobolevDerivative hV hp v x‖ ≤ ‖D x‖ := by
      filter_upwards [hAC.ae_eq hDv] with x hx
      rw [hx,norm_smul,Real.norm_eq_abs]
      exact mul_le_of_le_one_left (norm_nonneg _) (deriv_smoothNormalTruncation_abs_le_one n (U x))
    have hDvLp : MemLp (fun x => gibbsSobolevDerivative hV hp v x) 2 ν := by
      apply hD.of_le_mul (c := 1) (Lp.stronglyMeasurable _).aestronglyMeasurable
      simpa only [one_mul] using hdBound
    have hVBound : ∀ᵐ x ∂ν, ‖gibbsSobolevInclusion hV hp v x‖ ≤ ((n : ℝ)+1)*(Real.pi/2) := by
      filter_upwards [hAC.ae_eq hv] with x hx
      rw [hx,Real.norm_eq_abs]
      exact smoothNormalTruncation_abs_le_bound n (U x)
    have hh := localPoincare_bounded_gibbsSobolev hV hp ν C hP hloc v _ (by positivity) hVBound hDvLp
    rw [variance_congr (hAC.ae_eq hv)] at hh
    apply hh.trans
    apply mul_le_mul_of_nonneg_left _ hC
    apply integral_mono_ae hDvLp.norm.integrable_sq hD.norm.integrable_sq
    filter_upwards [hdBound] with x hx
    exact pow_le_pow_left₀ (norm_nonneg _) hx 2
  have hmean : Tendsto (fun n => ∫ x, fn n x ∂ν) atTop (𝓝 (∫ x, U x ∂ν)) := by
    apply tendsto_integral_of_dominated_convergence (fun x => ‖U x‖) hfnM hU.norm
      (fun n => Eventually.of_forall (fun x => smoothNormalTruncation_abs_le n (U x)))
      (Eventually.of_forall (fun x => tendsto_smoothNormalTruncation (U x)))
  exact memLp_two_and_variance_le_of_ae_tendsto ν hfnLp (Lp.stronglyMeasurable U).aestronglyMeasurable hmean
    (Eventually.of_forall (fun x => tendsto_smoothNormalTruncation (U x))) hvar

end CutoffRigidity
