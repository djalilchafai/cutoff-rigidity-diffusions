module
public import CutoffRigidity.HopfLaxExponentialInequality
public import CutoffRigidity.EuclideanLipschitzTransportDuality
public import CutoffRigidity.KLVariationalMeasure

/-! # Genuine Talagrand inequality for the source strongly convex Gibbs law

The cited Hamilton–Jacobi proof supplies the actual infimum-convolution
exponential inequality. Genuine bounded-Lipschitz Kantorovich strong
duality and the actual KL exponential variational bound then control the
original infimum over actual couplings. No transport or duality bound is
supplied as a source premise.
-/
public section
namespace CutoffRigidity
open MeasureTheory ProbabilityTheory InformationTheory Filter Set
open scoped Topology NNReal ENNReal BoundedContinuousFunction
variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

set_option maxHeartbeats 1200000 in
/-- The actual quadratic transport cost is bounded by actual KL for every
initial probability law, including singular and infinite-entropy laws. -/
theorem squaredWasserstein_le_two_div_curvature_klDiv
    {B : NNReal → Ω → E} {P : Measure Ω} (hB : IsEuclideanBrownian B P)
    {V : E → ℝ} (hV : ContDiff ℝ 2 V)
    (hp : IsProbabilityMeasure (gibbsMeasure volume V)) (hd : 0 < d)
    (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ*‖z‖^2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (ν : Measure E) [IsProbabilityMeasure ν] :
    squaredWasserstein ν (gibbsMeasure volume V) ≤
      ENNReal.ofReal (2/ρ)*klDiv ν (gibbsMeasure volume V) := by
  let := hp
  let μ := gibbsMeasure volume V
  by_cases hFin : klDiv ν μ = ⊤
  · rw [hFin,ENNReal.mul_top (ne_of_gt (ENNReal.ofReal_pos.mpr (div_pos (by norm_num) hρ)))]
    exact le_top
  have hBudget : squaredWasserstein ν μ ≤ ENNReal.ofReal ((2/ρ)*(klDiv ν μ).toReal) := by
    apply squaredWasserstein_le_of_lipschitz_dual_budget ν μ
    intro f g L J hf hg hdual
    let a := ρ/2
    let G := ∫ y,g y ∂μ
    let ψ := fun y : E => -g y
    let Q := hopfLax (1/2:ℝ) ψ
    let φ := fun x : E => a*f x+a*G
    have ha : 0 < a := by dsimp only [a]; positivity
    have hψB (x : E) : |ψ x| ≤ ‖g‖ := by
      simpa only [ψ,abs_neg,Real.norm_eq_abs] using g.norm_coe_le_norm x
    have hQCont := (lipschitzWith_hopfLax (by norm_num : (0:ℝ) ≤ 1/2) hψB hg.neg).continuous
    have hQUpper (x : E) : Q x ≤ ‖g‖ :=
      (hopfLax_bounds (by norm_num : (0:ℝ) ≤ 1/2) hψB x).2.trans (abs_le.mp (hψB x)).2
    have hfQ (x : E) : f x ≤ Q x := by
      change f x ≤ hopfLax (1/2:ℝ) ψ x
      rw [hopfLax,ite_eq_left (by norm_num : (0:ℝ)<1/2)]
      apply le_csInf (range_nonempty _)
      rintro _ ⟨y,rfl⟩
      have hh := hdual x y
      dsimp only [ψ]
      norm_num
      linarith
    have hPhiMeas : Measurable φ := (f.continuous.measurable.const_mul a).add_const (a*G)
    have hPhiB (x : E) : ‖φ x‖ ≤ a*‖f‖+|a*G| := by
      apply (norm_add_le _ _).trans
      rw [norm_mul,Real.norm_of_nonneg ha.le,Real.norm_eq_abs]
      exact add_le_add (mul_le_mul_of_nonneg_left (f.norm_coe_le_norm x) ha.le) le_rfl
    have hEQI : Integrable (fun x => Real.exp (a*Q x)) μ := by
      apply (integrable_const (Real.exp (a*‖g‖))).mono'
        (Real.continuous_exp.comp (hQCont.const_mul a)).aestronglyMeasurable
      apply Eventually.of_forall
      intro x
      change ‖Real.exp (a*Q x)‖ ≤ Real.exp (a*‖g‖)
      rw [Real.norm_of_nonneg (Real.exp_nonneg _)]
      exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (hQUpper x) ha.le)
    have hEφI : Integrable (fun x => Real.exp (φ x)) μ := by
      apply (integrable_const (Real.exp (a*‖f‖+|a*G|))).mono' hPhiMeas.exp.aestronglyMeasurable
      apply Eventually.of_forall
      intro x
      rw [Real.norm_of_nonneg (Real.exp_nonneg _)]
      exact Real.exp_le_exp.mpr ((le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using hPhiB x))
    have hMom := hopfLax_exponential_integral_le hB hV hp hd ρ hρ hHess hg.neg ‖g‖ hψB
      (1/2:ℝ) (by norm_num)
    have hHalf : ρ*(1/2:ℝ) = a := by dsimp only [a]; ring
    rw [hHalf] at hMom
    change (∫ x,Real.exp (a*Q x) ∂μ) ≤ Real.exp (a*(∫ y,-g y ∂μ)) at hMom
    rw [integral_neg,mul_neg] at hMom
    have hExp : (∫ x,Real.exp (φ x) ∂μ) ≤ 1 := by
      have hPoint (x : E) : Real.exp (φ x) ≤ Real.exp (a*G)*Real.exp (a*Q x) := by
        rw [← Real.exp_add]
        apply Real.exp_le_exp.mpr
        dsimp only [φ]
        nlinarith only [mul_le_mul_of_nonneg_left (hfQ x) ha.le]
      have hh := integral_mono hEφI (hEQI.const_mul (Real.exp (a*G))) hPoint
      rw [integral_const_mul] at hh
      calc
        _ ≤ Real.exp (a*G)*(∫ x,Real.exp (a*Q x) ∂μ) := hh
        _ ≤ Real.exp (a*G)*Real.exp (-(a*G)) := mul_le_mul_of_nonneg_left hMom (Real.exp_nonneg _)
        _ = 1 := by rw [← Real.exp_add,add_neg_cancel,Real.exp_zero]
    have hEnt := (ENNReal.ofReal_le_iff_le_toReal hFin).mp
      (relativeEntropyTest_le_klDiv ν μ hPhiMeas ⟨_,hPhiB⟩)
    have hfI : Integrable (fun x => f x) ν :=
      (integrable_const ‖f‖).mono' f.continuous.aestronglyMeasurable (Eventually.of_forall (f.norm_coe_le_norm))
    have hPhiInt : (∫ x,φ x ∂ν) = a*(∫ x,f x ∂ν)+a*G := by
      have hh := integral_add (hfI.const_mul a) (integrable_const (a*G))
      rw [hh,integral_const_mul,integral_const]
      simp only [measureReal_def,measure_univ,ENNReal.toReal_one,one_smul]
    rw [relativeEntropyTest,hPhiInt] at hEnt
    have hScale : a*((∫ x,f x ∂ν)+(∫ y,g y ∂μ)) ≤ (klDiv ν μ).toReal := by
      change a*((∫ x,f x ∂ν)+G) ≤ _
      linarith
    have he : (klDiv ν μ).toReal/a = (2/ρ)*(klDiv ν μ).toReal := by dsimp only [a]; field_simp
    rw [← he]
    exact (le_div_iff₀ ha).mpr (by nlinarith only [hScale])
  apply hBudget.trans_eq
  rw [ENNReal.ofReal_mul (by positivity : 0 ≤ 2/ρ),ENNReal.ofReal_toReal hFin]

/-- The exact form written in the paper: curvature times actual squared
Wasserstein distance is at most twice actual relative entropy. -/
theorem curvature_mul_squaredWasserstein_le_two_klDiv
    {B : NNReal → Ω → E} {P : Measure Ω} (hB : IsEuclideanBrownian B P)
    {V : E → ℝ} (hV : ContDiff ℝ 2 V)
    (hp : IsProbabilityMeasure (gibbsMeasure volume V)) (hd : 0 < d)
    (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ*‖z‖^2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (ν : Measure E) [IsProbabilityMeasure ν] :
    ENNReal.ofReal ρ*squaredWasserstein ν (gibbsMeasure volume V) ≤
      2*klDiv ν (gibbsMeasure volume V) := by
  have hh := squaredWasserstein_le_two_div_curvature_klDiv hB hV hp hd ρ hρ hHess ν
  have he : ENNReal.ofReal ρ*ENNReal.ofReal (2/ρ) = 2 := by
    rw [← ENNReal.ofReal_mul hρ.le]
    have hr : ρ*(2/ρ) = 2 := by field_simp
    rw [hr]
    norm_num
  have hmul := mul_le_mul' (le_refl (ENNReal.ofReal ρ)) hh
  simpa only [← mul_assoc,he] using hmul

end CutoffRigidity
