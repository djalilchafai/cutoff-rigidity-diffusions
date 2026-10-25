module
public import CutoffRigidity.GibbsSobolevLipschitz
public import CutoffRigidity.LogSobolevClosedRoot
public import CutoffRigidity.EntropyL2Bound
public import CutoffRigidity.FiniteEntropyDensityTruncation

/-! # The actual logarithmic Sobolev inequality for bounded Lipschitz tests -/
public section
namespace CutoffRigidity
open MeasureTheory ProbabilityTheory InformationTheory Filter Set
open scoped Topology NNReal ENNReal
variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

/-- A bounded measurable square has an integrable actual KL integrand. -/
theorem integrable_klFun_square_of_bounded (μ : Measure E) [IsProbabilityMeasure μ]
    {f : E → ℝ} (hfm : Measurable f) (M : ℝ) (hBound : ∀ x, ‖f x‖ ≤ M) :
    Integrable (fun x => klFun (f x^2)) μ := by
  have hMeas : AEStronglyMeasurable (fun x => klFun (f x^2)) μ :=
    (measurable_klFun.comp (hfm.pow_const 2)).aestronglyMeasurable
  apply (integrable_const ((M^2+1)^2)).mono' hMeas
  apply Eventually.of_forall
  intro x
  rw [Real.norm_of_nonneg (klFun_nonneg (sq_nonneg _))]
  apply (klFun_le_sq_sub_one (sq_nonneg _)).trans
  have hSq : f x^2 ≤ M^2 := by
    simpa only [Real.norm_eq_abs,sq_abs] using
      (sq_le_sq₀ (norm_nonneg _) ((norm_nonneg (f 0)).trans (hBound 0))).mpr (hBound x)
  nlinarith [sq_nonneg (f x),sq_nonneg M]

/-- Normalized bounded Lipschitz tests satisfy the genuine real LSI;
Rademacher, weak derivatives, and actual closed-domain membership are
proved by the bounded Lipschitz H¹ lift rather than supplied as premises. -/
theorem logSobolev_normalized_bounded_lipschitz
    {B : NNReal → Ω → E} {P : Measure Ω} (hB : IsEuclideanBrownian B P)
    {V f : E → ℝ} (hV : ContDiff ℝ 2 V)
    (hp : IsProbabilityMeasure (gibbsMeasure volume V)) (hd : 0 < d)
    (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ*‖z‖^2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    {L : NNReal} (hLip : LipschitzWith L f) (M : ℝ) (hBound : ∀ x, ‖f x‖ ≤ M)
    (hNorm : ∫ x,f x^2 ∂gibbsMeasure volume V = 1) :
    (∫ x,klFun (f x^2) ∂gibbsMeasure volume V) ≤
      (2/ρ)*∫ x,‖gradient f x‖^2 ∂gibbsMeasure volume V := by
  let := hp
  let μ := gibbsMeasure volume V
  obtain ⟨u,hu,hDu⟩ := exists_gibbsSobolev_of_bounded_lipschitz hV hp ρ hρ hHess hLip M hBound
  have hU : ‖gibbsSobolevInclusion hV hp u‖^2 = 1 := by
    rw [← real_inner_self_eq_norm_sq,L2.inner_def]
    calc
      _ = ∫ x,f x^2 ∂μ := by
        apply integral_congr_ae
        filter_upwards [hu] with x hx
        rw [hx,Real.inner_apply]; ring
      _ = 1 := hNorm
  have hD : ‖gibbsSobolevDerivative hV hp u‖^2 = ∫ x,‖gradient f x‖^2 ∂μ := by
    rw [← real_inner_self_eq_norm_sq,L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hDu] with x hx
    rw [hx,real_inner_self_eq_norm_sq]
  have hLSI := logSobolev_closed_normalized_root hB hV hp hd ρ hρ hHess u hU
  rw [hD] at hLSI
  have hAE : (fun x => ENNReal.ofReal (klFun (gibbsSobolevInclusion hV hp u x^2))) =ᵐ[μ]
      (fun x => ENNReal.ofReal (klFun (f x^2))) := hu.mono (fun x hx => by dsimp only; rw [hx])
  rw [lintegral_congr_ae hAE] at hLSI
  have hInt := integrable_klFun_square_of_bounded μ hLip.continuous.measurable M hBound
  rw [← ofReal_integral_eq_lintegral_ofReal hInt (Eventually.of_forall (fun x => klFun_nonneg (sq_nonneg _)))] at hLSI
  exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg (div_nonneg (by norm_num) hρ.le)
    (integral_nonneg (fun x => sq_nonneg _)))).mp hLSI

set_option maxHeartbeats 1000000 in
/-- Unnormalized real logarithmic Sobolev for actual bounded positive
Lipschitz functions. The expression on the left is exactly Entμ(f²). -/
theorem logSobolev_unnormalized_bounded_positive_lipschitz
    {B : NNReal → Ω → E} {P : Measure Ω} (hB : IsEuclideanBrownian B P)
    {V f : E → ℝ} (hV : ContDiff ℝ 2 V)
    (hp : IsProbabilityMeasure (gibbsMeasure volume V)) (hd : 0 < d)
    (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ*‖z‖^2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    {L : NNReal} (hLip : LipschitzWith L f) (M : ℝ) (hBound : ∀ x, ‖f x‖ ≤ M)
    (hpos : ∀ x,0 < f x) :
    let μ := gibbsMeasure volume V
    let A := ∫ x,f x^2 ∂μ
    (∫ x,klFun (f x^2) ∂μ)-A*Real.log A+(A-1) ≤
      (2/ρ)*∫ x,‖gradient f x‖^2 ∂μ := by
  let := hp
  let μ := gibbsMeasure volume V
  let A := ∫ x,f x^2 ∂μ
  have hfLp : MemLp f 2 μ := MemLp.of_bound hLip.continuous.aestronglyMeasurable M (Eventually.of_forall hBound)
  have hSqI : Integrable (fun x => f x^2) μ := hfLp.integrable_sq
  have hSqPos (x : E) : 0 < f x^2 := sq_pos_of_pos (hpos x)
  have hA : 0 < A := by
    apply (integral_pos_iff_support_of_nonneg (fun x => sq_nonneg (f x)) hSqI).mpr
    have he : Function.support (fun x => f x^2) = univ := by
      ext x; simp only [Function.mem_support,ne_eq,Set.mem_univ,iff_true]; exact (hSqPos x).ne'
    rw [he]; simp
  have hRoot : 0 < Real.sqrt A := Real.sqrt_pos.mpr hA
  obtain ⟨u,hu,hDu⟩ := exists_gibbsSobolev_of_bounded_lipschitz hV hp ρ hρ hHess hLip M hBound
  have hU : ‖gibbsSobolevInclusion hV hp u‖^2 = A := by
    rw [← real_inner_self_eq_norm_sq,L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hu] with x hx
    rw [hx,Real.inner_apply]; ring
  have hD : ‖gibbsSobolevDerivative hV hp u‖^2 = ∫ x,‖gradient f x‖^2 ∂μ := by
    rw [← real_inner_self_eq_norm_sq,L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hDu] with x hx
    rw [hx,real_inner_self_eq_norm_sq]
  let v := (Real.sqrt A)⁻¹ • u
  have hVNorm : ‖gibbsSobolevInclusion hV hp v‖^2 = 1 := by
    rw [map_smul,norm_smul,mul_pow,Real.norm_eq_abs,sq_abs,inv_pow,Real.sq_sqrt hA.le,hU]
    exact inv_mul_cancel₀ hA.ne'
  have hVD : ‖gibbsSobolevDerivative hV hp v‖^2 = (∫ x,‖gradient f x‖^2 ∂μ)/A := by
    rw [map_smul,norm_smul,mul_pow,Real.norm_eq_abs,sq_abs,inv_pow,Real.sq_sqrt hA.le,hD]
    ring
  have hVAe : gibbsSobolevInclusion hV hp v =ᵐ[μ] (fun x => f x/Real.sqrt A) := by
    change gibbsSobolevInclusion hV hp ((Real.sqrt A)⁻¹ • u) =ᵐ[μ] _
    rw [map_smul]
    filter_upwards [Lp.coeFn_smul (Real.sqrt A)⁻¹ (gibbsSobolevInclusion hV hp u),hu] with x hx huX
    rw [hx,Pi.smul_apply,smul_eq_mul,huX]
    ring
  have hLSI := logSobolev_closed_normalized_root hB hV hp hd ρ hρ hHess v hVNorm
  rw [hVD] at hLSI
  have hAE : (fun x => ENNReal.ofReal (klFun (gibbsSobolevInclusion hV hp v x^2))) =ᵐ[μ]
      (fun x => ENNReal.ofReal (klFun (f x^2/A))) := by
    filter_upwards [hVAe] with x hx
    rw [hx,div_pow,Real.sq_sqrt hA.le]
  rw [lintegral_congr_ae hAE] at hLSI
  have hGN (x : E) : ‖f x/Real.sqrt A‖ ≤ M/Real.sqrt A := by
    rw [norm_div,Real.norm_of_nonneg hRoot.le]
    gcongr
    exact hBound x
  have hKNI : Integrable (fun x => klFun (f x^2/A)) μ := by
    have hh := integrable_klFun_square_of_bounded μ (hLip.continuous.measurable.div_const (Real.sqrt A))
      (M/Real.sqrt A) hGN
    simpa only [div_pow,Real.sq_sqrt hA.le] using hh
  rw [← ofReal_integral_eq_lintegral_ofReal hKNI (Eventually.of_forall
    (fun x => klFun_nonneg (div_nonneg (sq_nonneg _) hA.le)))] at hLSI
  have hReal := (ENNReal.ofReal_le_ofReal_iff (mul_nonneg (div_nonneg (by norm_num) hρ.le)
    (div_nonneg (integral_nonneg (fun x => sq_nonneg _)) hA.le))).mp hLSI
  have hKLI := integrable_klFun_square_of_bounded μ hLip.continuous.measurable M hBound
  have hKI := integral_klFun_div_mass μ hSqI hSqPos hKLI hA
  change (∫ x,klFun (f x^2/A) ∂μ) = _ at hKI
  rw [hKI] at hReal
  have hh := mul_le_mul_of_nonneg_right hReal hA.le
  have heL : ((∫ x,klFun (f x^2) ∂μ)/A-Real.log A+(1-1/A))*A =
      (∫ x,klFun (f x^2) ∂μ)-A*Real.log A+(A-1) := by field_simp
  have heR : ((2/ρ)*((∫ x,‖gradient f x‖^2 ∂μ)/A))*A =
      (2/ρ)*(∫ x,‖gradient f x‖^2 ∂μ) := by field_simp
  rw [heL,heR] at hh
  exact hh

/-- The unnormalized inequality in the usual actual integral entropy
form, with all integrability supplied by bounded Lipschitz regularity. -/
theorem logSobolev_entropy_bounded_positive_lipschitz
    {B : NNReal → Ω → E} {P : Measure Ω} (hB : IsEuclideanBrownian B P)
    {V f : E → ℝ} (hV : ContDiff ℝ 2 V)
    (hp : IsProbabilityMeasure (gibbsMeasure volume V)) (hd : 0 < d)
    (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ*‖z‖^2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    {L : NNReal} (hLip : LipschitzWith L f) (M : ℝ) (hBound : ∀ x, ‖f x‖ ≤ M)
    (hpos : ∀ x,0 < f x) :
    let μ := gibbsMeasure volume V
    let A := ∫ x,f x^2 ∂μ
    (∫ x,f x^2*Real.log (f x^2) ∂μ)-A*Real.log A ≤
      (2/ρ)*∫ x,‖gradient f x‖^2 ∂μ := by
  let := hp
  let μ := gibbsMeasure volume V
  have hh := logSobolev_unnormalized_bounded_positive_lipschitz hB hV hp hd ρ hρ hHess hLip M hBound hpos
  have hKL := integrable_klFun_square_of_bounded μ hLip.continuous.measurable M hBound
  have hSq : Integrable (fun x => f x^2) μ :=
    (MemLp.of_bound hLip.continuous.aestronglyMeasurable M (Eventually.of_forall hBound) : MemLp f 2 μ).integrable_sq
  have hEq (x : E) : f x^2*Real.log (f x^2) = klFun (f x^2)+f x^2-1 := by rw [klFun_apply]; ring
  have hIntegral : (∫ x,f x^2*Real.log (f x^2) ∂μ) =
      (∫ x,klFun (f x^2) ∂μ)+(∫ x,f x^2 ∂μ)-1 := by
    have hs := integral_sub (hKL.add hSq) (integrable_const (1:ℝ))
    have ha := integral_add hKL hSq
    simp only [Pi.add_def] at hs ha
    rw [integral_congr_ae (Eventually.of_forall hEq),hs,ha,integral_const]
    simp only [measureReal_def,measure_univ,ENNReal.toReal_one,one_smul]
  dsimp only at hh ⊢
  rw [hIntegral]
  linarith

end CutoffRigidity
