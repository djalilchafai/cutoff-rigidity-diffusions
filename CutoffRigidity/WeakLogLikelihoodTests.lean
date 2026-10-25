module
public import CutoffRigidity.LocalPoincareSobolevIntegrable
public import CutoffRigidity.GibbsSobolevBoundedChain
public import CutoffRigidity.RelativeFisherInformation
public import Mathlib.MeasureTheory.VectorMeasure.Decomposition.RadonNikodym

/-! # Actual bounded weak log-likelihood tests

The closed RN-root chain rule, genuine local compact approximation and the
actual Radon--Nikodym integral identity give the weighted score bound.
No smooth representative of the density or Fisher value is assumed.
-/
public section
namespace CutoffRigidity
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal
variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

set_option maxHeartbeats 750000 in
theorem memLp_variance_closed_root_test_le
    {V : E → ℝ} (hV : ContDiff ℝ 2 V)
    (hp : IsProbabilityMeasure (gibbsMeasure volume V))
    (ν : Measure E) [IsProbabilityMeasure ν] (hAC : ν ≪ gibbsMeasure volume V)
    (C : ℝ) (hC : 0 ≤ C) (hP : HasLocalSmoothPoincare ν C)
    (hloc : ∀ K : Set E, IsCompact K → ∃ M : ENNReal, M ≠ ⊤ ∧ ν.restrict K ≤ M • volume)
    (u : gibbsSobolevGraph hV hp)
    (hRN : ∀ᵐ x ∂gibbsMeasure volume V,
      (gibbsSobolevInclusion hV hp u x)^2 = (ν.rnDeriv (gibbsMeasure volume V) x).toReal)
    {ψ : ℝ → ℝ} (hψ : ContDiff ℝ 2 ψ) (hψ0 : ψ 0=0)
    (K : ℝ) (hK : 0 < K)
    (hψD : ∀ r, |deriv ψ r| ≤ K)
    (hψInt : Integrable (fun x => ψ (gibbsSobolevInclusion hV hp u x)) ν)
    (hscore : ∀ r, r^2 * (deriv ψ r)^2 ≤ 4) :
    MemLp (fun x => ψ (gibbsSobolevInclusion hV hp u x)) 2 ν ∧
    variance (fun x => ψ (gibbsSobolevInclusion hV hp u x)) ν ≤
      C * (4*‖gibbsSobolevDerivative hV hp u‖^2) := by
  let hpG : IsProbabilityMeasure (gibbsMeasure volume V) := hp
  let μ := gibbsMeasure volume V
  let hpμ : IsProbabilityMeasure μ := hp
  let hdec : ν.HaveLebesgueDecomposition μ := Measure.haveLebesgueDecomposition_of_sigmaFinite ν μ
  let U := gibbsSobolevInclusion hV hp u
  let D := gibbsSobolevDerivative hV hp u
  obtain ⟨v,hv,hDv⟩ := gibbsSobolev_smooth_bounded_derivative_chain hV hp hψ hψ0 K hK hψD u
  let A := gibbsSobolevDerivative hV hp v
  have hnonneg (x : E) : 0 ≤ (ν.rnDeriv μ x).toReal * ‖A x‖^2 := by positivity
  have hbound : ∀ᵐ x ∂μ, (ν.rnDeriv μ x).toReal * ‖A x‖^2 ≤ 4*‖D x‖^2 := by
    filter_upwards [hRN,hDv] with x hr hd
    change (ν.rnDeriv μ x).toReal * ‖gibbsSobolevDerivative hV hp v x‖^2 ≤ _
    rw [← hr,hd,norm_smul,Real.norm_eq_abs,mul_pow,sq_abs]
    nlinarith [mul_le_mul_of_nonneg_right (hscore (U x)) (sq_nonneg ‖D x‖)]
  have hi : Integrable (fun x => (ν.rnDeriv μ x).toReal * ‖A x‖^2) μ := by
    apply ((Lp.memLp D).norm.integrable_sq.const_mul 4).mono'
      (((Measure.measurable_rnDeriv ν μ).ennreal_toReal.aestronglyMeasurable).mul
        ((Lp.stronglyMeasurable A).aestronglyMeasurable.norm.pow 2))
    filter_upwards [hbound] with x hx
    change ‖(ν.rnDeriv μ x).toReal * ‖A x‖^2‖ ≤ _
    rw [Real.norm_of_nonneg (hnonneg x)]
    exact hx
  have hIA : Integrable (fun x => ‖A x‖^2) ν :=
    (integrable_rnDeriv_smul_iff hAC).mp (by simpa only [smul_eq_mul] using hi)
  have hALp : MemLp (fun x => A x) 2 ν :=
    (memLp_two_iff_integrable_sq_norm (Lp.stronglyMeasurable A).aestronglyMeasurable).mpr hIA
  have henergy : (∫ x, ‖A x‖^2 ∂ν) ≤ 4*‖D‖^2 := by
    rw [← integral_rnDeriv_smul hAC]
    change (∫ x, (ν.rnDeriv μ x).toReal * ‖A x‖^2 ∂μ) ≤ _
    have hh := integral_mono_ae hi ((Lp.memLp D).norm.integrable_sq.const_mul 4) hbound
    rw [integral_const_mul] at hh
    have he : (∫ x, ‖D x‖^2 ∂μ)=‖D‖^2 := by
      rw [← real_inner_self_eq_norm_sq,L2.inner_def]
      simp only [real_inner_self_eq_norm_sq]
      rfl
    rwa [he] at hh
  have hVInt : Integrable (fun x => gibbsSobolevInclusion hV hp v x) ν :=
    (integrable_congr (hAC.ae_eq hv)).mpr hψInt
  obtain ⟨hVLp,hpi⟩ := localPoincare_integrable_gibbsSobolev hV hp ν hAC C hC hP hloc v hVInt hALp
  rw [variance_congr (hAC.ae_eq hv)] at hpi
  exact ⟨(memLp_congr_ae (hAC.ae_eq hv)).mp hVLp,
    hpi.trans (mul_le_mul_of_nonneg_left henergy hC)⟩

end CutoffRigidity
