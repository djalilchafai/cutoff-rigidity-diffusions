module
public import CutoffRigidity.LangevinMovingGradientContinuity
public import CutoffRigidity.LangevinPointwiseEntropyInterpolation
public import CutoffRigidity.ContinuousPartialChainRule
public import CutoffRigidity.BGLInterpolationAlgebra

/-! # The actual optimized-path logarithmic inequality of BGL01

We differentiate the actual logarithmic interpolation along the written
exponential line segment, use gradient commutation and Young's inequality,
and integrate the exact path energy. No Harnack premise is assumed.
-/
public section
namespace CutoffRigidity
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal
variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

set_option maxHeartbeats 1000000 in
/-- The actual BGL01 optimized-path inequality for positive constant-plus-
compact C² initial data, with its exact action constant. All interpolation
regularity, derivatives, and gradient commutation are proved from source data. -/
theorem langevinKernel_log_harnack_compact_perturbation
    {B : NNReal → Ω → E} {P : Measure Ω} (hB : IsEuclideanBrownian B P)
    {V g : E → ℝ} (hV : ContDiff ℝ 2 V)
    (hp : IsProbabilityMeasure (gibbsMeasure volume V))
    (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g)
    (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (c m : ℝ) (hm : 0 < m) (hpos : ∀ x, m ≤ c + g x)
    (T : ℝ) (hT : 0 < T) (x y : E) :
    (∫ z, Real.log (langevinPositiveProfile V g B P c T z)
      ∂langevinKernel V B P T.toNNReal x) ≤
      Real.log (langevinPositiveProfile V g B P c (2 * T) y) +
        ρ * ‖x - y‖ ^ 2 / (2 * (Real.exp (2 * ρ * T) - 1)) := by
  let Ψ := langevinLogInterpolation V g B P c T
  let D := langevinMovingLogScoreAverage (V := V) (g := g) (B := B) (P := P) c T
  let L := fun s z => fderiv ℝ (Ψ s) z
  let den := Real.exp (2 * ρ * T) - 1
  let k := fun s : ℝ => (Real.exp (2 * ρ * s) - 1) / den
  let kd := fun s : ℝ => 2 * ρ * Real.exp (2 * ρ * s) / den
  let γ := fun s : ℝ => y + k s • (x - y)
  let v := fun s : ℝ => kd s • (x - y)
  let H := fun s : ℝ => D s (γ s) + L s (γ s) (v s)
  let A := fun s : ℝ => Real.exp (-2 * ρ * s) * ‖v s‖ ^ 2 / 4
  have hden : den ≠ 0 := ne_of_gt (sub_pos.mpr (Real.one_lt_exp_iff.mpr (by positivity)))
  have hk : Continuous k := by dsimp [k]; fun_prop
  have hkd : Continuous kd := by dsimp [kd]; fun_prop
  have hγ : Continuous γ := continuous_const.add (hk.smul continuous_const)
  have hv : Continuous v := hkd.smul continuous_const
  have hγd (s : ℝ) : HasDerivAt γ (v s) s := by
    exact ((hasDerivAt_bgl_path_parameter ρ T s).smul_const (x - y)).const_add y
  have hDc : Continuous (Function.uncurry D) :=
    continuous_langevinMovingLogScoreAverage hB hV hg hgc ρ hρ.le hHess c m hm hpos T
  have hLc : Continuous (Function.uncurry L) :=
    continuous_fderiv_langevin_log_interpolation hB hV hg hgc ρ hρ.le hHess c m hm hpos T
  have hΨc : Continuous (Function.uncurry Ψ) :=
    continuous_langevinLogInterpolation hB hV hg hgc ρ hρ hHess c m hm hpos T
  have hHd : ∀ s ∈ Ioo 0 T, HasDerivAt (fun r => Ψ r (γ r)) (H s) s := by
    intro s hs
    exact hasDerivAt_along_path_of_continuous_partials Ψ D L hs
      (fun r hr z => hasDerivAt_langevin_log_interpolation_pointwise
        hB hV hp hg hgc ρ hρ hHess c m hm hpos T r hr.1 hr.2 z)
      (fun r z => (contDiff_one_langevin_log_interpolation hB hV hg hgc ρ hρ.le hHess
        c m hm hpos T r).differentiable one_ne_zero z |>.hasFDerivAt)
      hDc hLc γ (v s) (hγd s)
  have hHc : Continuous H := (hDc.comp (continuous_id.prodMk hγ)).add
    ((hLc.comp (continuous_id.prodMk hγ)).clm_apply hv)
  have hAc : Continuous A := by dsimp only [A]; fun_prop
  have hBound (s : ℝ) (hs : 0 ≤ s) : H s ≤ A s := by
    let a := -D s (γ s)
    have ha : 0 ≤ a := by
      change 0 ≤ -(-∫ z, langevinLogScore V g B P c (2 * T - s) z ∂langevinKernel V B P s.toNNReal (γ s))
      rw [neg_neg]
      exact integral_nonneg (fun z => sq_nonneg _)
    have hgrad := langevin_log_interpolation_gradient_sq_le hB hV hg hgc ρ hρ.le hHess
      c m hm hpos T s (γ s)
    rw [Real.coe_toNNReal _ hs] at hgrad
    change ‖gradient (Ψ s) (γ s)‖ ^ 2 ≤ Real.exp (-2 * ρ * s) * a at hgrad
    have he : Real.exp (-ρ * s) ^ 2 = Real.exp (-2 * ρ * s) := by
      rw [pow_two, ← Real.exp_add]
      congr 1
      ring
    have hYoung := bgl_gradient_young_bound (gradient (Ψ s) (γ s)) (v s) a
      (Real.exp (-ρ * s)) ha (Real.exp_nonneg _) (by simpa only [he] using hgrad)
    change D s (γ s) + fderiv ℝ (Ψ s) (γ s) (v s) ≤ _
    rw [← inner_gradient_left]
    simpa only [a, neg_neg, he, A] using hYoung
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hT.le
    (hΨc.comp (continuous_id.prodMk hγ)).continuousOn hHd (hHc.intervalIntegrable 0 T)
  have hInt : (∫ s in (0 : ℝ)..T, H s) ≤ ∫ s in (0 : ℝ)..T, A s :=
    intervalIntegral.integral_mono_on hT.le (hHc.intervalIntegrable 0 T)
    (hAc.intervalIntegrable 0 T) (fun s hs => hBound s hs.1)
  change (∫ s in (0 : ℝ)..T, H s) = Ψ T (γ T) - Ψ 0 (γ 0) at hFTC
  have hEnergy : (∫ s in (0 : ℝ)..T, A s) =
      ρ * ‖x - y‖ ^ 2 / (2 * den) := by
    have he (s : ℝ) : A s = ‖x - y‖ ^ 2 *
        ((2 * ρ * Real.exp (2 * ρ * s) / den) ^ 2 * Real.exp (-2 * ρ * s) / 4) := by
      dsimp only [A, v, kd]
      rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
      ring
    rw [intervalIntegral.integral_congr (fun s _ => he s), intervalIntegral.integral_const_mul,
      bgl_optimal_path_energy ρ T hρ hT]
    dsimp only [den]
    ring
  have hγ0 : γ 0 = y := by simp [γ, k]
  have hγT : γ T = x := by
    change y + (den / den) • (x - y) = x
    rw [div_self hden, one_smul]
    abel
  have hΨ0 : Ψ 0 y = Real.log (langevinPositiveProfile V g B P c (2 * T) y) := by
    change (∫ z, Real.log (langevinPositiveProfile V g B P c (2 * T - 0) z)
      ∂langevinKernel V B P (0 : ℝ).toNNReal y) = _
    rw [Real.toNNReal_zero, langevinKernel_zero hB hV ρ hρ.le hHess,
      Kernel.id_apply, integral_dirac, sub_zero]
  have hΨT : Ψ T x = ∫ z, Real.log (langevinPositiveProfile V g B P c T z)
      ∂langevinKernel V B P T.toNNReal x := by
    change (∫ z, Real.log (langevinPositiveProfile V g B P c (2 * T - T) z)
      ∂langevinKernel V B P T.toNNReal x) = _
    rw [show 2 * T - T = T by ring]
  rw [hFTC, hEnergy, hγT, hγ0, hΨ0, hΨT] at hInt
  linarith

end CutoffRigidity
