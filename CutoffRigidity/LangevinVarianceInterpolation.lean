module

public import CutoffRigidity.LangevinDynkin
public import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction

/-! # Actual moving-test differentiation for variance interpolation

Salez's local Poincaré proof interpolates the square of a backward heat test
under the actual forward kernel. The moving-test differentiation below is
proved from actual kernel generator consistency and uniform Banach-space
differentiation of bounded continuous tests. It is a preparatory domain
component, not a local Poincaré or backward-heat regularity assertion.
-/

public section

namespace CutoffRigidity

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal BoundedContinuousFunction

/-- Uniformly converging bounded continuous tests may vary together with
probability laws. Only the fixed limiting test needs weak convergence. -/
theorem tendsto_integral_varying_bounded_test
    {X J : Type*} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    {l : Filter J} {ν : J → Measure X} (hν : ∀ i, IsProbabilityMeasure (ν i))
    {f : J → X →ᵇ ℝ} {g : X →ᵇ ℝ} {v : ℝ}
    (hf : Tendsto f l (𝓝 g)) (hg : Tendsto (fun i => ∫ x, g x ∂ν i) l (𝓝 v)) :
    Tendsto (fun i => ∫ x, f i x ∂ν i) l (𝓝 v) := by
  have hnorm : Tendsto (fun i => ‖f i - g‖) l (𝓝 0) :=
    tendsto_iff_norm_sub_tendsto_zero.mp hf
  have hdiff : Tendsto (fun i => (∫ x, f i x ∂ν i) - ∫ x, g x ∂ν i) l (𝓝 0) := by
    apply squeeze_zero_norm (fun i => ?_) hnorm
    let := hν i
    rw [← integral_sub ((f i).integrable (ν i)) (g.integrable (ν i))]
    exact (f i - g).norm_integral_le_norm (ν i)
  simpa only [sub_add_cancel, zero_add] using hdiff.add hg

variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

/-- Actual weak kernel continuity also accommodates a strongly varying
bounded continuous test, the ingredient needed for space-time Dynkin. -/
theorem tendsto_langevinKernel_integral_varying_bounded_test
    {B : ℝ≥0 → Ω → E} {P : Measure Ω} (hB : IsEuclideanBrownian B P)
    {V : E → ℝ} (hV : ContDiff ℝ 2 V) (κ : ℝ) (hκ : 0 ≤ κ)
    (hHess : ∀ x z : E, κ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    {J : Type*} {l : Filter J} {f : J → E →ᵇ ℝ} {g : E →ᵇ ℝ}
    {t : J → ℝ≥0} {t₀ : ℝ≥0} (hf : Tendsto f l (𝓝 g))
    (ht : Tendsto t l (𝓝 t₀)) (x : E) :
    Tendsto (fun i => ∫ y, f i y ∂langevinKernel V B P (t i) x) l
      (𝓝 (∫ y, g y ∂langevinKernel V B P t₀ x)) := by
  apply tendsto_integral_varying_bounded_test
    (fun i => by let := langevinKernel_isMarkovKernel hB hV κ hκ hHess (t i); infer_instance) hf
  exact ((continuous_langevinKernel_integral_of_bounded_continuous hB hV g.continuous
    ⟨‖g‖, g.norm_coe_le_norm⟩ κ hκ hHess x).tendsto t₀).comp ht

/-- Genuine space-time generator differentiation for a uniformly
differentiable bounded-continuous test curve whose frozen spatial test is
compact C². No time-dependent Dynkin identity is assumed. -/
theorem hasDerivWithinAt_langevinKernel_moving_test_right
    {B : ℝ≥0 → Ω → E} {P : Measure Ω} (hB : IsEuclideanBrownian B P)
    {V : E → ℝ} (hV : ContDiff ℝ 2 V) (κ : ℝ) (hκ : 0 ≤ κ)
    (hHess : ∀ x z : E, κ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (q : ℝ → E →ᵇ ℝ) {q' : E →ᵇ ℝ} {s : ℝ} (hs : 0 ≤ s)
    (hq : HasDerivAt q q' s) (hqs : ContDiff ℝ 2 (q s))
    (hqsc : HasCompactSupport (q s)) (x : E) :
    HasDerivWithinAt (fun t : ℝ => ∫ y, q t y ∂langevinKernel V B P t.toNNReal x)
      ((∫ y, q' y ∂langevinKernel V B P s.toNNReal x) +
        ∫ y, langevinDifferentialOperator V (q s) y ∂langevinKernel V B P s.toNNReal x)
      (Ioi s) s := by
  have htime : Tendsto (fun t : ℝ => t.toNNReal) (𝓝[>] s) (𝓝 s.toNNReal) :=
    (continuous_real_toNNReal.tendsto s).mono_left nhdsWithin_le_nhds
  have hqSlope : Tendsto (slope q s) (𝓝[>] s) (𝓝 q') :=
    hq.tendsto_slope.mono_left (nhdsGT_le_nhdsNE s)
  have hA := tendsto_langevinKernel_integral_varying_bounded_test hB hV κ hκ hHess
    hqSlope htime x
  have hBfixed := hasDerivWithinAt_langevinKernel_integral_right hB hV hqs hqsc κ hκ hHess x hs
  rw [hasDerivWithinAt_iff_tendsto_slope' (by simp : s ∉ Ioi s)] at hBfixed ⊢
  apply (hA.add hBfixed).congr'
  filter_upwards with t
  let := langevinKernel_isMarkovKernel hB hV κ hκ hHess t.toNNReal
  simp only [slope_def_field, slope_def_module]
  rw [show (fun y => ((t - s)⁻¹ • (q t - q s)) y) =
      (fun y => (t - s)⁻¹ * (q t y - q s y)) by rfl,
    integral_const_mul, integral_sub ((q t).integrable _) ((q s).integrable _)]
  ring

/-- Actual space-time Dynkin identity for uniformly differentiable
bounded-continuous test curves with compact C² spatial slices. This is the
localized moving-test ingredient of the variance-interpolation proof. -/
theorem langevinKernel_spacetime_dynkin_identity
    {B : ℝ≥0 → Ω → E} {P : Measure Ω} (hB : IsEuclideanBrownian B P)
    {V : E → ℝ} (hV : ContDiff ℝ 2 V) (κ : ℝ) (hκ : 0 ≤ κ)
    (hHess : ∀ x z : E, κ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (q q' : ℝ → E →ᵇ ℝ) (x : E) {T : ℝ} (hT : 0 ≤ T)
    (hqcont : ContinuousOn q (Icc 0 T))
    (hq : ∀ s ∈ Ioo 0 T, HasDerivAt q (q' s) s)
    (hqs : ∀ s ∈ Ioo 0 T, ContDiff ℝ 2 (q s))
    (hqsc : ∀ s ∈ Ioo 0 T, HasCompactSupport (q s))
    (hsource : IntervalIntegrable (fun s =>
      (∫ y, q' s y ∂langevinKernel V B P s.toNNReal x) +
      ∫ y, langevinDifferentialOperator V (q s) y ∂langevinKernel V B P s.toNNReal x)
      volume 0 T) :
    (∫ y, q T y ∂langevinKernel V B P T.toNNReal x) = q 0 x +
      ∫ s in 0..T, ((∫ y, q' s y ∂langevinKernel V B P s.toNNReal x) +
        ∫ y, langevinDifferentialOperator V (q s) y ∂langevinKernel V B P s.toNNReal x) := by
  have hc : ContinuousOn (fun s : ℝ => ∫ y, q s y ∂langevinKernel V B P s.toNNReal x) (Icc 0 T) := by
    intro s hs
    apply tendsto_langevinKernel_integral_varying_bounded_test hB hV κ hκ hHess
      (hqcont s hs)
    exact (continuous_real_toNNReal.tendsto s).mono_left nhdsWithin_le_nhds
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le hT hc
    (fun s hs => hasDerivWithinAt_langevinKernel_moving_test_right hB hV κ hκ hHess
      q hs.1.le (hq s hs) (hqs s hs) (hqsc s hs) x) hsource
  have hz : (∫ y, q 0 y ∂langevinKernel V B P (0 : ℝ).toNNReal x) = q 0 x := by
    rw [Real.toNNReal_zero, langevinKernel_zero hB hV κ hκ hHess, Kernel.id_apply]
    exact integral_dirac (q 0) x
  rw [hz] at hFTC
  linarith

end CutoffRigidity
