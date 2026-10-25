module
public import CutoffRigidity.PositivePowerCalculus
public import CutoffRigidity.LipschitzLogSobolev

/-! # The genuine power logarithmic Sobolev inequality for Gross's curve -/
public section
namespace CutoffRigidity
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal
variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

/-- Positive bounded real powers of an actual C¹ Lipschitz test are
actually Lipschitz, with the derivative bound explicitly derived. -/
theorem positive_c1_rpow_lipschitz {f : E → ℝ} (hf : ContDiff ℝ 1 f)
    {L : NNReal} (hL : LipschitzWith L f) {m M p : ℝ} (hm : 0 < m)
    (hlow : ∀ x,m ≤ f x) (hupp : ∀ x,f x ≤ M) (hp : 1 ≤ p) :
    LipschitzWith (Real.toNNReal (p*M^(p-1)*L)) (fun x => f x^p) := by
  have hpos (x : E) : 0 < f x := hm.trans_le (hlow x)
  have hM : 0 < M := (hpos 0).trans_le (hupp 0)
  have hP : 0 ≤ p := by linarith
  have hC : ContDiff ℝ 1 (fun x => f x^p) := hf.rpow_const_of_ne (fun x => (hpos x).ne')
  apply lipschitzWith_of_nnnorm_fderiv_le (hC.differentiable one_ne_zero)
  intro x
  change ‖fderiv ℝ (fun x => f x^p) x‖ ≤ (Real.toNNReal (p*M^(p-1)*L) : ℝ)
  rw [Real.coe_toNNReal _ (by positivity)]
  have hn : ‖gradient (fun x => f x^p) x‖ = ‖fderiv ℝ (fun x => f x^p) x‖ :=
    (InnerProductSpace.toDual ℝ E).symm.norm_map _
  rw [← hn,gradient_rpow_at_positive (hf.differentiable one_ne_zero x) (hpos x),norm_smul,
    Real.norm_of_nonneg (mul_nonneg hP (Real.rpow_nonneg (hpos x).le _))]
  exact mul_le_mul (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow (hpos x).le (hupp x) (by linarith)) hP)
    (norm_gradient_le_of_lipschitz hL x) (norm_nonneg _) (by positivity)

/-- Actual unnormalized logarithmic Sobolev for f^p, the exact power
inequality used in Gross's variable-exponent differentiation. -/
theorem logSobolev_positive_c1_power
    {B : NNReal → Ω → E} {P : Measure Ω} (hB : IsEuclideanBrownian B P)
    {V f : E → ℝ} (hV : ContDiff ℝ 2 V)
    (hp : IsProbabilityMeasure (gibbsMeasure volume V)) (hd : 0 < d)
    (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E,ρ*‖z‖^2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (hf : ContDiff ℝ 1 f) {L : NNReal} (hL : LipschitzWith L f)
    {m M p : ℝ} (hm : 0 < m) (hlow : ∀ x,m ≤ f x) (hupp : ∀ x,f x ≤ M) (hP : 2 ≤ p) :
    let μ := gibbsMeasure volume V
    let Z := ∫ x,f x^p ∂μ
    (∫ x,f x^p*Real.log (f x^p) ∂μ)-Z*Real.log Z ≤
      (p^2/(2*ρ))*∫ x,f x^(p-2)*‖gradient f x‖^2 ∂μ := by
  have hpos (x : E) : 0 < f x := hm.trans_le (hlow x)
  have hM : 0 < M := (hpos 0).trans_le (hupp 0)
  let ψ := fun x => f x^(p/2)
  have hLip := positive_c1_rpow_lipschitz hf hL hm hlow hupp (show 1 ≤ p/2 by linarith)
  have hBound (x : E) : ‖ψ x‖ ≤ M^(p/2) := by
    rw [Real.norm_of_nonneg (Real.rpow_nonneg (hpos x).le _)]
    exact Real.rpow_le_rpow (hpos x).le (hupp x) (by linarith)
  have hSq (x : E) : ψ x^2 = f x^p := by
    dsimp only [ψ]
    rw [← Real.rpow_natCast,← Real.rpow_mul (hpos x).le]
    congr 1
    norm_num
  have hGrad (x : E) : ‖gradient ψ x‖^2 = (p^2/4)*(f x^(p-2)*‖gradient f x‖^2) := by
    rw [gradient_rpow_at_positive (hf.differentiable one_ne_zero x) (hpos x) (p/2),
      norm_smul,mul_pow,Real.norm_eq_abs,sq_abs,mul_pow]
    have he : (f x^(p/2-1))^2 = f x^(p-2) := by
      rw [← Real.rpow_natCast,← Real.rpow_mul (hpos x).le]
      congr 1
      norm_num
      ring
    rw [he]
    ring
  have hh := logSobolev_entropy_bounded_positive_lipschitz hB hV hp hd ρ hρ hHess hLip
    (M^(p/2)) hBound (fun x => Real.rpow_pos_of_pos (hpos x) _)
  dsimp only at hh ⊢
  have hEnt (x : E) : ψ x^2*Real.log (ψ x^2) = f x^p*Real.log (f x^p) := by rw [hSq]
  rw [integral_congr_ae (Eventually.of_forall hEnt),integral_congr_ae (Eventually.of_forall hSq),
    integral_congr_ae (Eventually.of_forall hGrad),integral_const_mul] at hh
  convert hh using 1
  ring

end CutoffRigidity
