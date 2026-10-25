module

public import CutoffRigidity.GibbsStationarity
public import CutoffRigidity.GaussianMoments
public import CutoffRigidity.GaussianTransport
public import CutoffRigidity.Brownian
public import CutoffRigidity.GaussianBilinearMoments
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.Calculus.LHopital
public import Mathlib.Analysis.Normed.Operator.Basic
public import Mathlib.Analysis.Normed.Operator.Bilinear
public import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic

/-! # Differentiating genuine Gaussian averages

The Brownian part of generator consistency is obtained by differentiating
actual Gaussian averages. Compact C² tests provide all dominating functions
through actual bounds on their derivatives; no stochastic generator formula
or differentiation-under-integral premise is assumed.
-/

public section

namespace CutoffRigidity

open MeasureTheory ProbabilityTheory Set
open scoped Topology NNReal

variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

/-- Uniform norm bound for any continuous compactly supported normed-valued map. -/
theorem compact_continuous_norm_bound {F : Type*} [NormedAddCommGroup F]
    {G : E → F} (hG : Continuous G) (hGc : HasCompactSupport G) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x, ‖G x‖ ≤ C := by
  obtain ⟨C, hC⟩ := hGc.exists_bound_of_continuousOn hG.continuousOn
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro x
  by_cases hx : x ∈ tsupport G
  · exact (hC x hx).trans (le_max_left _ _)
  · have hzero : G x = 0 := Function.notMem_support.mp (fun hs => hx (subset_tsupport G hs))
    simpa only [hzero, norm_zero] using le_max_right C 0

/-- The actual Gaussian average at spatial point `x` and noise scale `r`. -/
@[expose] noncomputable def gaussianAverage (f : E → ℝ) (x : E) (r : ℝ) : ℝ :=
  ∫ z, f (x + r • z) ∂stdGaussian E

/-- The actual first-derivative integral of the Gaussian average. -/
@[expose] noncomputable def gaussianAverageDerivative (f : E → ℝ) (x : E) (r : ℝ) : ℝ :=
  ∫ z, fderiv ℝ f (x + r • z) z ∂stdGaussian E

/-- Genuine Gaussian averaging can be differentiated once, with every
integrability and domination hypothesis proved from a compact C² test. -/
theorem hasDerivAt_gaussianAverage {f : E → ℝ} (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) (x : E) (r : ℝ) :
    HasDerivAt (gaussianAverage f x) (gaussianAverageDerivative f x r) r := by
  have hDf : ContDiff ℝ 1 (fderiv ℝ f) := hf.fderiv_right (by norm_num)
  have hx (r : ℝ) : Continuous (fun z : E => x + r • z) := by fun_prop
  have hDc (r : ℝ) : Continuous (fun z : E => fderiv ℝ f (x + r • z) z) :=
    (hDf.continuous.comp (hx r)).clm_apply continuous_id
  obtain ⟨M, hM0, hM⟩ := compact_continuous_norm_bound hf.continuous hfc
  obtain ⟨C, hC0, hC⟩ := compact_continuous_norm_bound hDf.continuous (hfc.fderiv ℝ)
  have hfi : Integrable (fun z : E => f (x + r • z)) (stdGaussian E) :=
    Integrable.mono' (integrable_const M) (hf.continuous.comp (hx r)).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun z => hM _))
  have hz : Integrable (fun z : E => C * ‖z‖) (stdGaussian E) :=
    (IsGaussian.integrable_id (μ := stdGaussian E)).norm.const_mul C
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := stdGaussian E) (F := fun r z => f (x + r • z))
    (F' := fun r z => fderiv ℝ f (x + r • z) z) (s := univ) (bound := fun z => C * ‖z‖)
    (x₀ := r) (by simp) (Filter.Eventually.of_forall (fun r => (hf.continuous.comp (hx r)).aestronglyMeasurable)) hfi
    (hDc r).aestronglyMeasurable (Filter.Eventually.of_forall (fun z r _ => ?_)) hz
    (Filter.Eventually.of_forall (fun z r _ => ?_))
  · exact h.2
  · exact (ContinuousLinearMap.le_opNorm _ _).trans
      (mul_le_mul_of_nonneg_right (hC _) (norm_nonneg z))
  · have hd := (hf.differentiable (by norm_num) (x + r • z)).hasFDerivAt.comp_hasDerivAt r
      (((hasDerivAt_id r).smul_const z).const_add x)
    convert! hd using 1
    simp only [one_smul]

/-- Compact C² tests have a uniform genuine Hessian diagonal bound.
The constant is derived from finitely many compactly supported scalar Hessian entries. -/
theorem compact_test_hessian_diagonal_bound {f : E → ℝ} (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ y z : E, ‖fderiv ℝ (fderiv ℝ f) y z z‖ ≤ K * ‖z‖ ^ 2 := by
  have hDf : ContDiff ℝ 1 (fderiv ℝ f) := hf.fderiv_right (by norm_num)
  have hH : Continuous (fderiv ℝ (fderiv ℝ f)) :=
    (hDf.fderiv_right (m := 0) (by norm_num)).continuous
  have hHc : HasCompactSupport (fderiv ℝ (fderiv ℝ f)) := (hfc.fderiv ℝ).fderiv ℝ
  have hentry (i j : Fin d) : ∃ C : ℝ, 0 ≤ C ∧ ∀ y : E,
      ‖fderiv ℝ (fderiv ℝ f) y (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)‖ ≤ C := by
    apply compact_continuous_norm_bound
      (((hH.clm_apply continuous_const).clm_apply continuous_const))
    exact hHc.comp_left (g := fun H => H (EuclideanSpace.single i 1) (EuclideanSpace.single j 1))
      (by simp)
  choose Kentry hKentry0 hKentry using hentry
  let K : ℝ := ∑ i : Fin d, ∑ j : Fin d, Kentry i j
  have hK0 : 0 ≤ K := Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => hKentry0 i j))
  have hK (y z : E) : ‖fderiv ℝ (fderiv ℝ f) y z z‖ ≤ K * ‖z‖ ^ 2 := by
    rw [bilinear_euclidean_coordinate_expansion]
    calc
      _ ≤ ∑ i : Fin d, ∑ j : Fin d,
          ‖z i * z j * fderiv ℝ (fderiv ℝ f) y (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)‖ := by
        exact (norm_sum_le _ _).trans (Finset.sum_le_sum (fun i _ => norm_sum_le _ _))
      _ ≤ ∑ i : Fin d, ∑ j : Fin d, Kentry i j * ‖z‖ ^ 2 := by
        apply Finset.sum_le_sum
        intro i _
        apply Finset.sum_le_sum
        intro j _
        rw [norm_mul, norm_mul]
        calc
          _ ≤ ‖z‖ * ‖z‖ * Kentry i j := by
            gcongr
            · exact PiLp.norm_apply_le z i
            · exact PiLp.norm_apply_le z j
            · exact hKentry i j y
          _ = _ := by ring
      _ = K * ‖z‖ ^ 2 := by simp only [K, Finset.sum_mul]
  exact ⟨K, hK0, hK⟩

set_option maxHeartbeats 300000 in
/-- The derivative integral can itself be differentiated once. Its dominating
function is the actual Hessian bound times the Gaussian squared norm. -/
theorem hasDerivAt_gaussianAverageDerivative {f : E → ℝ} (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) (x : E) (r : ℝ) :
    HasDerivAt (gaussianAverageDerivative f x)
      (∫ z, fderiv ℝ (fderiv ℝ f) (x + r • z) z z ∂stdGaussian E) r := by
  have hDf : ContDiff ℝ 1 (fderiv ℝ f) := hf.fderiv_right (by norm_num)
  have hx (r : ℝ) : Continuous (fun z : E => x + r • z) := by fun_prop
  have hDc (r : ℝ) : Continuous (fun z : E => fderiv ℝ f (x + r • z) z) :=
    (hDf.continuous.comp (hx r)).clm_apply continuous_id
  have hH : Continuous (fderiv ℝ (fderiv ℝ f)) :=
    (hDf.fderiv_right (m := 0) (by norm_num)).continuous
  obtain ⟨C, hC0, hC⟩ := compact_continuous_norm_bound hDf.continuous (hfc.fderiv ℝ)
  obtain ⟨K, hK0, hK⟩ := compact_test_hessian_diagonal_bound hf hfc
  have hfi : Integrable (fun z : E => fderiv ℝ f (x + r • z) z) (stdGaussian E) := by
    apply Integrable.mono' ((IsGaussian.integrable_id (μ := stdGaussian E)).norm.const_mul C)
      (hDc r).aestronglyMeasurable
    exact Filter.Eventually.of_forall (fun z => (ContinuousLinearMap.le_opNorm _ _).trans
      (mul_le_mul_of_nonneg_right (hC _) (norm_nonneg z)))
  have hbound : Integrable (fun z : E => K * ‖z‖ ^ 2) (stdGaussian E) :=
    (IsGaussian.memLp_two_id (μ := stdGaussian E)).norm.integrable_sq.const_mul K
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := stdGaussian E) (F := fun r z => fderiv ℝ f (x + r • z) z)
    (F' := fun r z => fderiv ℝ (fderiv ℝ f) (x + r • z) z z)
    (s := univ) (bound := fun z => K * ‖z‖ ^ 2) (x₀ := r) (by simp)
    (Filter.Eventually.of_forall (fun r => (hDc r).aestronglyMeasurable)) hfi
    (((hH.comp (hx r)).clm_apply continuous_id).clm_apply continuous_id).aestronglyMeasurable
    (Filter.Eventually.of_forall (fun z r _ => ?_)) hbound
    (Filter.Eventually.of_forall (fun z r _ => ?_))
  · exact h.2
  · exact hK (x + r • z) z
  · have hd := (hDf.differentiable (by norm_num) (x + r • z)).hasFDerivAt.comp_hasDerivAt r
      (((hasDerivAt_id r).smul_const z).const_add x)
    have hh := hd.clm_apply (hasDerivAt_const r z)
    convert! hh using 1
    simp only [Function.comp_def, id_eq, one_smul, add_zero, map_zero]

/-- Centering of the actual standard Gaussian kills the linear Taylor term. -/
theorem gaussianAverageDerivative_zero (f : E → ℝ) (x : E) :
    gaussianAverageDerivative f x 0 = 0 := by
  unfold gaussianAverageDerivative
  simp only [zero_smul, add_zero]
  have h := (fderiv ℝ f x).integral_comp_comm (IsGaussian.integrable_id (μ := stdGaussian E))
  dsimp only [id_eq] at h
  rw [integral_id_stdGaussian, map_zero] at h
  exact h

/-- The quadratic Taylor coefficient of actual Gaussian averaging is the
actual Euclidean Laplacian, obtained by tracing the Hessian covariance. -/
theorem hasDerivAt_gaussianAverageDerivative_zero {f : E → ℝ} (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) (x : E) :
    HasDerivAt (gaussianAverageDerivative f x) (euclideanLaplacian f x) 0 := by
  have h := hasDerivAt_gaussianAverageDerivative hf hfc x 0
  simp only [zero_smul, add_zero] at h
  rw [integral_bilinear_diagonal_stdGaussian] at h
  rw [euclideanLaplacian_eq_second_fderiv_trace
    ((hf.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num) x)]
  exact h

/-- The Gaussian-average value at zero noise is the original test value. -/
theorem gaussianAverage_zero (f : E → ℝ) (x : E) : gaussianAverage f x 0 = f x := by
  simp [gaussianAverage]

/-- The genuine second-order Gaussian Taylor quotient, before converting
noise amplitude into Brownian time. -/
theorem gaussianAverage_quadratic_quotient_tendsto {f : E → ℝ} (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) (x : E) :
    Filter.Tendsto (fun r : ℝ => (gaussianAverage f x r - f x) / r ^ 2)
      (𝓝[≠] 0) (𝓝 (euclideanLaplacian f x / 2)) := by
  have hs := (hasDerivAt_gaussianAverageDerivative_zero hf hfc x).tendsto_slope
  have hs' : Filter.Tendsto (fun r : ℝ => gaussianAverageDerivative f x r / r)
      (𝓝[≠] 0) (𝓝 (euclideanLaplacian f x)) := by
    simpa only [slope_fun_def_field, gaussianAverageDerivative_zero, sub_zero] using hs
  have hdiv : Filter.Tendsto (fun r : ℝ => gaussianAverageDerivative f x r / (2 * r))
      (𝓝[≠] 0) (𝓝 (euclideanLaplacian f x / 2)) := by
    convert hs'.div_const 2 using 1
    funext r
    ring
  have hpow (r : ℝ) : HasDerivAt (fun r : ℝ => r ^ 2) (2 * r) r := by
    convert! (hasDerivAt_id r).pow 2 using 1
    simp
  have hnzero : ∀ᶠ r : ℝ in 𝓝[≠] 0, 2 * r ≠ 0 := by
    filter_upwards [self_mem_nhdsWithin] with r hr
    exact mul_ne_zero (by norm_num) hr
  have hnum : Filter.Tendsto (fun r => gaussianAverage f x r - f x) (𝓝[≠] 0) (𝓝 0) := by
    have hc := (hasDerivAt_gaussianAverage hf hfc x 0).continuousAt.tendsto.sub_const (f x)
    simpa only [gaussianAverage_zero, sub_self] using hc.mono_left nhdsWithin_le_nhds
  have hden : Filter.Tendsto (fun r : ℝ => r ^ 2) (𝓝[≠] 0) (𝓝 0) := by
    have h : Filter.Tendsto (fun r : ℝ => r ^ 2) (𝓝 (0 : ℝ)) (𝓝 ((0 : ℝ) ^ 2)) :=
      (continuous_pow 2).tendsto 0
    simpa only [zero_pow (by norm_num : (2 : ℕ) ≠ 0)] using h.mono_left nhdsWithin_le_nhds
  exact HasDerivAt.lhopital_zero_nhdsNE
    (Filter.Eventually.of_forall (fun r => (hasDerivAt_gaussianAverage hf hfc x r).sub_const (f x)))
    (Filter.Eventually.of_forall hpow) hnzero hnum hden hdiv

/-- Genuine small-time heat-generator consistency for compact C² tests.
The Brownian `sqrt 2` normalization produces exactly the Euclidean Laplacian. -/
theorem gaussianAverage_heat_generator_tendsto {f : E → ℝ} (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) (x : E) :
    Filter.Tendsto (fun t : ℝ => (gaussianAverage f x (Real.sqrt (2 * t)) - f x) / t)
      (𝓝[>] 0) (𝓝 (euclideanLaplacian f x)) := by
  have hroot : Filter.Tendsto (fun t : ℝ => Real.sqrt (2 * t)) (𝓝[>] 0) (𝓝[≠] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · have h : ContinuousAt (fun t : ℝ => Real.sqrt (2 * t)) 0 := by fun_prop
      simpa only [mul_zero, Real.sqrt_zero] using h.tendsto.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with t ht
      exact (Real.sqrt_pos.mpr (mul_pos (by norm_num) ht)).ne'
  have h := (gaussianAverage_quadratic_quotient_tendsto hf hfc x).comp hroot
  have h2 := h.const_mul 2
  have htarget : 2 * (euclideanLaplacian f x / 2) = euclideanLaplacian f x := by ring
  rw [htarget] at h2
  apply h2.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  have ht0 : 0 < t := ht
  dsimp only [Function.comp_apply]
  rw [Real.sq_sqrt (by positivity : 0 ≤ 2 * t)]
  field_simp

/-- Brownian Gaussian averaging is the actual scaled standard Gaussian
average, derived from the driver's genuine finite-dimensional law. -/
theorem integral_brownian_heat_eq_gaussianAverage
    {Ω : Type*} [MeasurableSpace Ω]
    {B : ℝ≥0 → Ω → E} {P : Measure Ω} (hB : IsEuclideanBrownian B P)
    {f : E → ℝ} (hf : Continuous f) (x : E) {t : ℝ} (ht : 0 ≤ t) :
    (∫ ω, f (x + Real.sqrt 2 • B t.toNNReal ω) ∂P) =
      gaussianAverage f x (Real.sqrt (2 * t)) := by
  have hBint := (hB.hasLaw_eval t.toNNReal).integral_comp
    (f := fun y : E => f (x + Real.sqrt 2 • y)) (by fun_prop)
  have hscale := affineGaussian_eq_multivariateGaussian (0 : E) (Real.sqrt t) (Real.sqrt_nonneg t)
  rw [Real.sq_sqrt ht] at hscale
  have hmap : (stdGaussian E).map (fun z : E => Real.sqrt t • z) =
      multivariateGaussian (0 : E) (t • (1 : Matrix (Fin d) (Fin d) ℝ)) := by
    simpa only [affineGaussian, zero_add] using hscale
  rw [Real.coe_toNNReal _ ht, ← hmap] at hBint
  rw [integral_map (by fun_prop) (by fun_prop)] at hBint
  unfold gaussianAverage
  calc
    _ = ∫ z : E, f (x + Real.sqrt 2 • (Real.sqrt t • z)) ∂stdGaussian E := hBint
    _ = _ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun z => by
        change f (x + Real.sqrt 2 • (Real.sqrt t • z)) = f (x + Real.sqrt (2 * t) • z)
        rw [smul_smul, ← Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)])

/-- The genuine Brownian transition expectation has the actual Laplacian
as its small-time generator on compact C² tests, with no Itô premise. -/
theorem brownian_heat_generator_tendsto
    {Ω : Type*} [MeasurableSpace Ω]
    {B : ℝ≥0 → Ω → E} {P : Measure Ω} (hB : IsEuclideanBrownian B P)
    {f : E → ℝ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) (x : E) :
    Filter.Tendsto (fun t : ℝ =>
      ((∫ ω, f (x + Real.sqrt 2 • B t.toNNReal ω) ∂P) - f x) / t)
      (𝓝[>] 0) (𝓝 (euclideanLaplacian f x)) := by
  apply (gaussianAverage_heat_generator_tendsto hf hfc x).congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  rw [integral_brownian_heat_eq_gaussianAverage hB hf.continuous x (show 0 ≤ t from le_of_lt ht)]

end CutoffRigidity
