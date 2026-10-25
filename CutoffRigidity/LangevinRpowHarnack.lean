module
public import CutoffRigidity.LangevinRpowInterpolation
public import CutoffRigidity.LangevinPowerHarnack

/-! # Genuine power-α Harnack (Wang) from the actual real-power interpolation

The real-power interpolation derivative and its weighted gradient estimate
are combined along the exponential path, exactly as for α = 2. Taking the
logarithm and integrating Young's bound gives the dimension-free inequality
(P_T f)^α(x) ≤ P_T f^α(y) exp(αρ|x-y|²/(2(α-1)(e^{2ρT}-1))) for every α > 1.
-/
public section
namespace CutoffRigidity
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal
variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

set_option maxHeartbeats 1200000 in
/-- Actual power-α Harnack on positive constant-plus-compact C² tests.
All partial derivatives and bounds come from the genuine diffusion; no
Harnack, density smoothness, or operator-domain premise is assumed. -/
theorem langevinKernel_rpow_harnack_compact_perturbation
    {B : NNReal → Ω → E} {P : Measure Ω} (hB : IsEuclideanBrownian B P)
    {V g : E → ℝ} (hV : ContDiff ℝ 2 V)
    (hp : IsProbabilityMeasure (gibbsMeasure volume V))
    (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g)
    (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (c m : ℝ) (hm : 0 < m) (hpos : ∀ x, m ≤ c + g x) (α : ℝ) (hα : 1 < α)
    (T : ℝ) (hT : 0 < T) (x y : E) :
    (langevinPositiveProfile V g B P c T x) ^ α ≤
      (∫ z, (c + g z) ^ α ∂langevinKernel V B P T.toNNReal y) *
        Real.exp (α * ρ * ‖x - y‖ ^ 2 / (2 * (α - 1) * (Real.exp (2 * ρ * T) - 1))) := by
  let F := langevinRpowInterpolation V g B P c α T
  let D := langevinRpowCarreAverage V g B P c α T
  have hα0 : 0 < α := zero_lt_one.trans hα
  have hα1 : 0 < α - 1 := by linarith
  let κ := α / (α - 1)
  have hκ : 0 < κ := div_pos hα0 hα1
  let f := fun s z => Real.log (F s z)
  let d := fun s z => D s z / F s z
  let L := fun s z => fderiv ℝ (f s) z
  have hFPos (s : ℝ) (z : E) : 0 < F s z :=
    (Real.rpow_pos_of_pos hm α).trans_le
      (langevinRpowInterpolation_lower hB hV hg hgc ρ hρ hHess c m hm hpos α hα0.le T s z)
  have hF1 (s : ℝ) : ContDiff ℝ 1 (F s) :=
    contDiff_one_langevinRpowInterpolation hB hV hg hgc ρ hρ hHess c m hm hpos α T s
  have hf1 (s : ℝ) : ContDiff ℝ 1 (f s) := (hF1 s).log (fun z => (hFPos s z).ne')
  have hFc : Continuous (Function.uncurry F) :=
    continuous_langevinRpowInterpolation hB hV hg hgc ρ hρ hHess c m hm hpos α T
  have hDc : Continuous (Function.uncurry D) :=
    continuous_langevinRpowCarreAverage hB hV hg hgc ρ hρ hHess c m hm hpos α T
  have hdc : Continuous (Function.uncurry d) := hDc.div hFc (fun p => (hFPos p.1 p.2).ne')
  have hfc : Continuous (Function.uncurry f) := hFc.log (fun p => (hFPos p.1 p.2).ne')
  have hLc : Continuous (Function.uncurry L) := by
    have hc := (hFc.inv₀ (fun p => (hFPos p.1 p.2).ne')).smul
      (continuous_fderiv_langevinRpowInterpolation hB hV hg hgc ρ hρ hHess c m hm hpos α T)
    apply hc.congr
    intro p
    change (F p.1 p.2)⁻¹ • fderiv ℝ (F p.1) p.2 = fderiv ℝ (f p.1) p.2
    exact (fderiv.log ((hF1 p.1).differentiable one_ne_zero p.2) (hFPos p.1 p.2).ne').symm
  have hTime (s : ℝ) (hs : s ∈ Ioo 0 T) (z : E) : HasDerivAt (fun r => f r z) (d s z) s :=
    (hasDerivAt_langevinRpowInterpolation hB hV hg hgc ρ hρ hHess c m hm hpos α hp T s hs.1 hs.2 z).log
      (hFPos s z).ne'
  let den := Real.exp (2 * ρ * T) - 1
  have hden : den ≠ 0 := ne_of_gt (sub_pos.mpr (Real.one_lt_exp_iff.mpr (by positivity)))
  let k := fun s : ℝ => (Real.exp (2 * ρ * s) - 1) / den
  let kd := fun s : ℝ => 2 * ρ * Real.exp (2 * ρ * s) / den
  let γ := fun s : ℝ => x + k s • (y - x)
  let v := fun s : ℝ => kd s • (y - x)
  let H := fun s : ℝ => d s (γ s) + L s (γ s) (v s)
  let A := fun s : ℝ => κ * Real.exp (-2 * ρ * s) * ‖v s‖ ^ 2 / 4
  have hk : Continuous k := by dsimp [k]; fun_prop
  have hkd : Continuous kd := by dsimp [kd]; fun_prop
  have hγ : Continuous γ := continuous_const.add (hk.smul continuous_const)
  have hv : Continuous v := hkd.smul continuous_const
  have hγd (s : ℝ) : HasDerivAt γ (v s) s :=
    ((hasDerivAt_bgl_path_parameter ρ T s).smul_const (y - x)).const_add x
  have hHd : ∀ s ∈ Ioo 0 T, HasDerivAt (fun r => f r (γ r)) (H s) s := by
    intro s hs
    exact hasDerivAt_along_path_of_continuous_partials f d L hs hTime
      (fun r z => ((hf1 r).differentiable one_ne_zero z).hasFDerivAt) hdc hLc γ (v s) (hγd s)
  have hHc : Continuous H := (hdc.comp (continuous_id.prodMk hγ)).add
    ((hLc.comp (continuous_id.prodMk hγ)).clm_apply hv)
  have hAc : Continuous A := by dsimp only [A]; fun_prop
  have hBound (s : ℝ) (hs : 0 ≤ s) : -A s ≤ H s := by
    let a := d s (γ s)
    have hDPos : 0 ≤ D s (γ s) := integral_nonneg fun z => by
      unfold langevinRpowGradientProfile
      exact mul_nonneg (mul_nonneg (mul_pos hα0 hα1).le (Real.rpow_nonneg (hm.trans_le
        (langevinPositiveProfile_lower hB hV hg hgc ρ hρ.le hHess c m hpos _ z)).le _)) (sq_nonneg _)
    have ha : 0 ≤ a := div_nonneg hDPos (hFPos _ _).le
    have hw := langevinRpowInterpolation_weighted_gradient hB hV hg hgc ρ hρ hHess c m hm hpos α hα T s (γ s)
    rw [Real.coe_toNNReal _ hs] at hw
    have hgrad : ‖gradient (f s) (γ s)‖ ^ 2 ≤ κ * Real.exp (-2 * ρ * s) * a := by
      rw [norm_gradient_log_sq_of_c1 (hF1 s) (fun z => hFPos s z)]
      calc
        _ = (‖gradient (F s) (γ s)‖ ^ 2 / F s (γ s)) / F s (γ s) := by field_simp
        _ ≤ (Real.exp (-2 * ρ * s) * κ * D s (γ s)) / F s (γ s) :=
          div_le_div_of_nonneg_right hw (hFPos _ _).le
        _ = _ := by dsimp only [a, d]; ring
    have hKsq : (Real.sqrt κ * Real.exp (-ρ * s)) ^ 2 = κ * Real.exp (-2 * ρ * s) := by
      have he : Real.exp (-ρ * s) ^ 2 = Real.exp (-2 * ρ * s) := by
        rw [pow_two, ← Real.exp_add]
        congr 1
        ring
      rw [mul_pow, Real.sq_sqrt hκ.le, he]
    have hy := bgl_gradient_young_bound (-gradient (f s) (γ s)) (v s) a
      (Real.sqrt κ * Real.exp (-ρ * s)) ha (by positivity)
      (by simpa only [norm_neg, hKsq] using hgrad)
    rw [inner_neg_left, hKsq] at hy
    change -(κ * Real.exp (-2 * ρ * s) * ‖v s‖ ^ 2 / 4) ≤ d s (γ s) + fderiv ℝ (f s) (γ s) (v s)
    rw [← inner_gradient_left]
    dsimp only [a] at hy
    linarith only [hy]
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hT.le
    (hfc.comp (continuous_id.prodMk hγ)).continuousOn hHd (hHc.intervalIntegrable 0 T)
  change (∫ s in (0 : ℝ)..T, H s) = f T (γ T) - f 0 (γ 0) at hFTC
  have hInt : (∫ s in (0 : ℝ)..T, -A s) ≤ ∫ s in (0 : ℝ)..T, H s :=
    intervalIntegral.integral_mono_on hT.le (hAc.intervalIntegrable 0 T).neg
    (hHc.intervalIntegrable 0 T) (fun s hs => hBound s hs.1)
  rw [intervalIntegral.integral_neg] at hInt
  have hEnergy : (∫ s in (0 : ℝ)..T, A s) = α * ρ * ‖x - y‖ ^ 2 / (2 * (α - 1) * den) := by
    have he (s : ℝ) : A s = (κ * ‖y - x‖ ^ 2) *
        ((2 * ρ * Real.exp (2 * ρ * s) / den) ^ 2 * Real.exp (-2 * ρ * s) / 4) := by
      dsimp only [A, v, kd]
      rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
      ring
    rw [intervalIntegral.integral_congr (fun s _ => he s), intervalIntegral.integral_const_mul,
      bgl_optimal_path_energy ρ T hρ hT, norm_sub_rev x y]
    dsimp only [den, κ]
    field_simp [hden, hα1.ne']
  have hγ0 : γ 0 = x := by simp [γ, k]
  have hγT : γ T = y := by
    change x + (den / den) • (y - x) = y
    rw [div_self hden, one_smul]
    abel
  rw [hEnergy, hFTC, hγ0, hγT] at hInt
  have hLog : Real.log (F 0 x) ≤ Real.log (F T y) + α * ρ * ‖x - y‖ ^ 2 / (2 * (α - 1) * den) := by
    change -(α * ρ * ‖x - y‖ ^ 2 / (2 * (α - 1) * den)) ≤ Real.log (F T y) - Real.log (F 0 x) at hInt
    linarith only [hInt]
  have hExp := Real.exp_le_exp.mpr hLog
  rw [Real.exp_log (hFPos 0 x), Real.exp_add, Real.exp_log (hFPos T y)] at hExp
  have hF0 : F 0 x = (langevinPositiveProfile V g B P c T x) ^ α := by
    change (∫ z, (langevinPositiveProfile V g B P c (T-0) z) ^ α ∂langevinKernel V B P (0 : ℝ).toNNReal x) = _
    rw [Real.toNNReal_zero, langevinKernel_zero hB hV ρ hρ.le hHess, Kernel.id_apply, integral_dirac, sub_zero]
  have hFT : F T y = ∫ z, (c + g z) ^ α ∂langevinKernel V B P T.toNNReal y := by
    have hq0 (z : E) : langevinPositiveProfile V g B P c 0 z = c + g z := by
      change c + (∫ w, g w ∂langevinKernel V B P (0 : ℝ).toNNReal z) = _
      rw [Real.toNNReal_zero, langevinKernel_zero hB hV ρ hρ.le hHess, Kernel.id_apply, integral_dirac]
    change (∫ z, (langevinPositiveProfile V g B P c (T-T) z) ^ α ∂langevinKernel V B P T.toNNReal y) = _
    rw [sub_self]
    simp_rw [hq0]
  rw [hF0, hFT] at hExp
  exact hExp

end CutoffRigidity
