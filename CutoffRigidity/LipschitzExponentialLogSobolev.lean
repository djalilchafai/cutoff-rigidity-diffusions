module
public import CutoffRigidity.LipschitzLogSobolev
public import CutoffRigidity.HopfLaxExponentialRegularity

/-! # Genuine exponential-test logarithmic Sobolev inequality -/
public section
namespace CutoffRigidity
open MeasureTheory ProbabilityTheory InformationTheory Filter Set
open scoped Topology NNReal ENNReal
variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

/-- An exponential of a bounded Lipschitz real test is truly globally
Lipschitz, with an actual finite constant. -/
theorem exists_lipschitzWith_exp_mul_bounded {f : E → ℝ} {L : NNReal}
    (hL : LipschitzWith L f) (M : ℝ) (hf : ∀ x,|f x| ≤ M)
    {a : ℝ} (ha : 0 ≤ a) :
    ∃ C : NNReal, LipschitzWith C (fun x => Real.exp (a*f x)) := by
  refine ⟨⟨Real.exp (a*M)*(a*L),by positivity⟩,LipschitzWith.of_dist_le_mul ?_⟩
  intro x y
  have hRange (z : E) : a*f z ≤ a*M := mul_le_mul_of_nonneg_left (abs_le.mp (hf z)).2 ha
  have he := Convex.norm_image_sub_le_of_norm_deriv_le
    (fun z (_hz : z ∈ Iic (a*M)) => Real.differentiableAt_exp)
    (fun z (hz : z ∈ Iic (a*M)) => by
      rw [Real.deriv_exp,Real.norm_of_nonneg (Real.exp_nonneg _)]
      exact Real.exp_le_exp.mpr hz)
    (convex_Iic (a*M)) (hRange y) (hRange x)
  change ‖Real.exp (a*f x)-Real.exp (a*f y)‖ ≤ (Real.exp (a*M)*(a*L))*‖x-y‖
  apply he.trans
  have hd : ‖a*f x-a*f y‖ ≤ (a*L)*‖x-y‖ := by
    rw [← mul_sub,norm_mul,Real.norm_of_nonneg ha]
    exact (mul_le_mul_of_nonneg_left (hL.norm_sub_le x y) ha).trans_eq (by ring)
  exact (mul_le_mul_of_nonneg_left hd (Real.exp_nonneg _)).trans_eq (by ring)

/-- The actual scalar exponential gradient chain rule at an actual
Rademacher differentiability point. -/
theorem gradient_exp_mul_at {f : E → ℝ} {x : E} (hf : DifferentiableAt ℝ f x) (a : ℝ) :
    gradient (fun y => Real.exp (a*f y)) x = (a*Real.exp (a*f x)) • gradient f x := by
  apply ext_inner_right ℝ
  intro z
  rw [inner_gradient_left,real_inner_smul_left,inner_gradient_left]
  have hh := (hf.hasFDerivAt.const_mul a).exp
  rw [hh.fderiv]
  simp only [smul_apply,smul_eq_mul]
  ring

set_option maxHeartbeats 1000000 in
/-- The actual exponential-test LSI needed by Hamilton–Jacobi
hypercontractivity, with genuine a.e. gradient chain rule and domain. -/
theorem logSobolev_exp_bounded_lipschitz
    {B : NNReal → Ω → E} {P : Measure Ω} (hB : IsEuclideanBrownian B P)
    {V f : E → ℝ} (hV : ContDiff ℝ 2 V)
    (hp : IsProbabilityMeasure (gibbsMeasure volume V)) (hd : 0 < d)
    (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ*‖z‖^2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    {L : NNReal} (hLip : LipschitzWith L f) (M : ℝ) (hBound : ∀ x,|f x| ≤ M)
    (a : ℝ) (ha : 0 ≤ a) :
    let μ := gibbsMeasure volume V
    let Z := ∫ x,Real.exp (a*f x) ∂μ
    (∫ x,Real.exp (a*f x)*(a*f x) ∂μ)-Z*Real.log Z ≤
      (a^2/(2*ρ))*∫ x,Real.exp (a*f x)*‖gradient f x‖^2 ∂μ := by
  let := hp
  let μ := gibbsMeasure volume V
  let ψ := fun x => Real.exp ((a/2)*f x)
  obtain ⟨C,hC⟩ := exists_lipschitzWith_exp_mul_bounded hLip M hBound (show 0 ≤ a/2 by positivity)
  have hψB (x : E) : ‖ψ x‖ ≤ Real.exp ((a/2)*M) := by
    rw [Real.norm_of_nonneg (Real.exp_nonneg _)]
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (abs_le.mp (hBound x)).2 (by positivity))
  have hSq (x : E) : ψ x^2 = Real.exp (a*f x) := by
    dsimp only [ψ]
    rw [← Real.exp_nat_mul]
    congr 1
    norm_num
    ring
  have hEntropy (x : E) : ψ x^2*Real.log (ψ x^2) = Real.exp (a*f x)*(a*f x) := by
    rw [hSq,Real.log_exp]
  have hGrad : (fun x => ‖gradient ψ x‖^2) =ᵐ[μ]
      (fun x => (a^2/4)*(Real.exp (a*f x)*‖gradient f x‖^2)) := by
    filter_upwards [(gibbsMeasure_absolutelyContinuous volume V).ae_le
      (hLip.ae_differentiableAt (μ := volume))] with x hx
    rw [gradient_exp_mul_at hx (a/2),norm_smul,mul_pow,Real.norm_eq_abs,sq_abs,mul_pow]
    change (a/2)^2*(ψ x^2)*‖gradient f x‖^2 = _
    rw [hSq]
    ring
  have hh := logSobolev_entropy_bounded_positive_lipschitz hB hV hp hd ρ hρ hHess
    hC (Real.exp ((a/2)*M)) hψB (fun x => Real.exp_pos _)
  dsimp only at hh ⊢
  rw [integral_congr_ae (Eventually.of_forall hEntropy),
    integral_congr_ae (Eventually.of_forall hSq),integral_congr_ae hGrad,integral_const_mul] at hh
  convert hh using 1
  ring

end CutoffRigidity
