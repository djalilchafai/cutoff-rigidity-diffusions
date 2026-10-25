module

public import CutoffRigidity.LangevinWeakDriftGenerator
public import CutoffRigidity.GaussianHeatWeakGenerator

/-! # Actual spatially tested semigroup generator

The actual compact-test time generator transfers through the genuine
semigroup and is integrated against compact Lebesgue tests with its proved
uniform bound. The Gaussian weak generator is a separate ingredient in the
subsequent distributional backward equation.
-/

public section

namespace CutoffRigidity

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal

variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

/-- Genuine spatial testing of the actual semigroup time-generator limit. -/
theorem weak_langevinKernel_time_generator_tendsto
    {B : ℝ≥0 → Ω → E} {P : Measure Ω} (hB : IsEuclideanBrownian B P)
    {V g ψ : E → ℝ} (hV : ContDiff ℝ 2 V) (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g)
    (κ : ℝ) (hκ : 0 ≤ κ)
    (hHess : ∀ x z, κ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (hψ : Continuous ψ) (hψc : HasCompactSupport ψ) (s : ℝ≥0) :
    Tendsto (fun h : ℝ => ∫ x, ψ x *
      (((∫ z, g z ∂langevinKernel V B P (s + h.toNNReal) x) -
        ∫ z, g z ∂langevinKernel V B P s x) / h))
      (𝓝[>] 0) (𝓝 (∫ x, ψ x *
        (∫ y, langevinDifferentialOperator V g y ∂langevinKernel V B P s x))) := by
  obtain ⟨M, hM0, hM⟩ := exists_uniform_langevinKernel_generator_quotient_bound hB hV hg hgc κ hκ hHess
  let := langevinKernel_isMarkovKernel hB hV κ hκ hHess s
  have hTimeBound : ∀ᶠ h : ℝ in 𝓝[>] 0, ∀ x : E,
      |((∫ z, g z ∂langevinKernel V B P (s + h.toNNReal) x) -
        ∫ z, g z ∂langevinKernel V B P s x) / h| ≤ M := by
    filter_upwards [hM] with h hh
    intro x
    rw [langevinKernel_time_quotient_eq_integral hB hV hg.continuous hgc κ hκ hHess]
    have hb := norm_integral_le_of_norm_le_const (μ := langevinKernel V B P s x)
      (f := fun y => ((∫ z, g z ∂langevinKernel V B P h.toNNReal y) - g y) / h) (C := M)
      (Eventually.of_forall (fun y => by simpa only [Real.norm_eq_abs] using hh y))
    simpa only [Real.norm_eq_abs, measureReal_def, measure_univ, ENNReal.toReal_one, mul_one] using hb
  have hDom : Integrable (fun x : E => M * ‖ψ x‖) volume :=
    (hψ.integrable_of_hasCompactSupport hψc).norm.const_mul M
  apply tendsto_integral_filter_of_dominated_convergence (fun x : E => M * ‖ψ x‖) ?_ ?_ hDom ?_
  · apply Eventually.of_forall
    intro h
    have hma : StronglyMeasurable (fun x => ∫ z, g z ∂langevinKernel V B P (s + h.toNNReal) x) :=
      hg.continuous.measurable.stronglyMeasurable.integral_kernel
    have hmb : StronglyMeasurable (fun x => ∫ z, g z ∂langevinKernel V B P s x) :=
      hg.continuous.measurable.stronglyMeasurable.integral_kernel
    exact (hψ.measurable.mul ((hma.measurable.sub hmb.measurable).div_const h)).aestronglyMeasurable
  · filter_upwards [hTimeBound] with h hh
    apply Eventually.of_forall
    intro x
    rw [norm_mul, Real.norm_eq_abs (_ / h)]
    exact (mul_le_mul_of_nonneg_left (hh x) (norm_nonneg _)).trans_eq (mul_comm _ _)
  · apply Eventually.of_forall
    intro x
    exact (tendsto_const_nhds (x := ψ x)).mul
      (langevinKernel_time_generator_tendsto hB hV hg hgc κ hκ hHess s x)

/-- The actual compact-test semigroup law in expectation form. -/
theorem langevinKernel_integral_semigroup_compact_test
    {B : ℝ≥0 → Ω → E} {P : Measure Ω} (hB : IsEuclideanBrownian B P)
    {V g : E → ℝ} (hV : ContDiff ℝ 2 V) (hg : Continuous g) (hgc : HasCompactSupport g)
    (κ : ℝ) (hκ : 0 ≤ κ)
    (hHess : ∀ x z, κ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (s t : ℝ≥0) (x : E) :
    (∫ y, (∫ z, g z ∂langevinKernel V B P t y) ∂langevinKernel V B P s x) =
      ∫ z, g z ∂langevinKernel V B P (s + t) x := by
  let := langevinKernel_isMarkovKernel hB hV κ hκ hHess s
  let := langevinKernel_isMarkovKernel hB hV κ hκ hHess t
  have hi : Integrable g ((langevinKernel V B P t ∘ₖ langevinKernel V B P s) x) := by
    rw [langevinKernel_comp hB hV κ hκ hHess]
    let := langevinKernel_isMarkovKernel hB hV κ hκ hHess (s + t)
    exact integrable_compact_test_comp hg hgc aemeasurable_id
  rw [← langevinKernel_comp hB hV κ hκ hHess]
  exact (Kernel.integral_comp hi).symm

/-- The actual backward heat test has its spatially tested generator limit
prescribed by K_t(Lg), without any C² premise on that heat test. -/
theorem weak_langevinKernel_backward_generator_tendsto
    {B : ℝ≥0 → Ω → E} {P : Measure Ω} (hB : IsEuclideanBrownian B P)
    {V g ψ : E → ℝ} (hV : ContDiff ℝ 2 V) (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g)
    (κ : ℝ) (hκ : 0 ≤ κ)
    (hHess : ∀ x z, κ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (hψ : Continuous ψ) (hψc : HasCompactSupport ψ) (t : ℝ≥0) :
    let q := fun y => ∫ z, g z ∂langevinKernel V B P t y
    Tendsto (fun h : ℝ => ∫ x, ψ x *
      (((∫ y, q y ∂langevinKernel V B P h.toNNReal x) - q x) / h))
      (𝓝[>] 0) (𝓝 (∫ x, ψ x *
        (∫ y, langevinDifferentialOperator V g y ∂langevinKernel V B P t x))) := by
  apply (weak_langevinKernel_time_generator_tendsto hB hV hg hgc κ hκ hHess hψ hψc t).congr'
  apply Eventually.of_forall
  intro h
  apply integral_congr_ae
  apply Eventually.of_forall
  intro x
  dsimp only
  rw [langevinKernel_integral_semigroup_compact_test hB hV hg.continuous hgc κ hκ hHess,
    add_comm t h.toNNReal]

private theorem integrable_compact_coefficient_bounded {f ψ : E → ℝ}
    (hψ : Continuous ψ) (hψc : HasCompactSupport ψ) (hfm : Measurable f)
    {M : ℝ} (hM : ∀ x, ‖f x‖ ≤ M) : Integrable (fun x => ψ x * f x) volume := by
  apply ((hψ.integrable_of_hasCompactSupport hψc).norm.const_mul M).mono'
    (hψ.measurable.mul hfm).aestronglyMeasurable
  filter_upwards with x
  rw [Pi.mul_apply, norm_mul]
  exact (mul_le_mul_of_nonneg_left (hM x) (norm_nonneg _)).trans_eq (mul_comm _ _)

/-- The actual spatially tested kernel quotient splits into its genuine
drift and Gaussian parts, with every required spatial integrability proved
from boundedness and compactness of the testing coefficient. -/
theorem weak_langevinKernel_generator_split_c1
    {B : ℝ≥0 → Ω → E} {P : Measure Ω} (hB : IsEuclideanBrownian B P)
    {V f ψ : E → ℝ} (hV : ContDiff ℝ 2 V) (hf : ContDiff ℝ 1 f)
    (hBound : ∃ M : ℝ, 0 ≤ M ∧ ∀ x, ‖f x‖ ≤ M)
    (κ : ℝ) (hκ : 0 ≤ κ)
    (hHess : ∀ x z, κ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (hψ : Continuous ψ) (hψc : HasCompactSupport ψ) {h : ℝ} (hh : 0 < h) :
    (∫ x, ψ x * (((∫ y, f y ∂langevinKernel V B P h.toNNReal x) - f x) / h)) =
      (∫ x, ψ x * (∫ ω, langevinDriftQuotient V f B x h ω ∂P)) +
        ∫ x, ψ x * ((gaussianAverage f x (Real.sqrt (2 * h)) - f x) / h) := by
  let := hB.isProbabilityMeasure
  obtain ⟨M, hM0, hM⟩ := hBound
  have hDM := measurable_langevinDriftQuotient_integral_c1 hB hV hf ⟨M, hM0, hM⟩ κ hκ hHess hh.le
  have hDnorm (x : E) : ‖∫ ω, langevinDriftQuotient V f B x h ω ∂P‖ ≤ 2 * M / h := by
    have hpoint (ω : Ω) : ‖langevinDriftQuotient V f B x h ω‖ ≤ 2 * M / h := by
      change ‖(_ - _) / h‖ ≤ _
      rw [norm_div, Real.norm_eq_abs h, abs_of_pos hh]
      apply div_le_div_of_nonneg_right _ hh.le
      have h1 := hM (langevinSolution V (brownianDrivingPath B ω) x h)
      have h2 := hM (x + Real.sqrt 2 • B h.toNNReal ω)
      exact (norm_sub_le _ _).trans (by linarith)
    simpa using norm_integral_le_of_norm_le_const (μ := P) (Eventually.of_forall hpoint)
  have hiD := integrable_compact_coefficient_bounded hψ hψc hDM hDnorm
  have hGM : StronglyMeasurable (fun x => gaussianAverage f x (Real.sqrt (2 * h))) := by
    have hc : Continuous (fun p : E × E => f (p.1 + Real.sqrt (2 * h) • p.2)) := by fun_prop
    exact hc.stronglyMeasurable.integral_prod_right
  have hGnorm (x : E) : ‖gaussianAverage f x (Real.sqrt (2 * h))‖ ≤ M := by
    simpa only [gaussianAverage, measureReal_def, measure_univ, ENNReal.toReal_one, mul_one] using
      (norm_integral_le_of_norm_le_const (μ := stdGaussian E)
        (f := fun z => f (x + Real.sqrt (2 * h) • z)) (C := M)
        (Eventually.of_forall (fun z => hM _)))
  have hHeatM : Measurable (fun x => (gaussianAverage f x (Real.sqrt (2 * h)) - f x) / h) :=
    (hGM.measurable.sub hf.continuous.measurable).div_const h
  have hHeatN (x : E) : ‖(gaussianAverage f x (Real.sqrt (2 * h)) - f x) / h‖ ≤ 2 * M / h := by
    rw [norm_div, Real.norm_eq_abs h, abs_of_pos hh]
    apply div_le_div_of_nonneg_right _ hh.le
    exact (norm_sub_le _ _).trans (by linarith [hGnorm x, hM x])
  have hiHeat := integrable_compact_coefficient_bounded hψ hψc hHeatM hHeatN
  calc
    _ = ∫ x, (ψ x * (∫ ω, langevinDriftQuotient V f B x h ω ∂P) +
        ψ x * ((gaussianAverage f x (Real.sqrt (2 * h)) - f x) / h)) := by
      apply integral_congr_ae
      apply Eventually.of_forall
      intro x
      dsimp only
      rw [langevinKernel_generator_quotient_eq_drift_add_heat_c1 hB hV hf ⟨M, hM0, hM⟩ κ hκ hHess x hh.le,
        mul_add]
    _ = _ := integral_add hiD hiHeat

/-- The genuine backward transition of a compact C² test satisfies the
ordinary distributional backward equation. The transition itself is only
proved C¹ here; its Laplacian is obtained distributionally, without any
assumed C² heat regularity. -/
theorem langevinKernel_weak_backward_equation
    {B : ℝ≥0 → Ω → E} {P : Measure Ω} (hB : IsEuclideanBrownian B P)
    {V g ψ : E → ℝ} (hV : ContDiff ℝ 2 V) (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g)
    (κ : ℝ) (hκ : 0 ≤ κ)
    (hHess : ∀ x z, κ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (hψ : ContDiff ℝ 2 ψ) (hψc : HasCompactSupport ψ) (t : ℝ≥0) :
    let q := fun x => ∫ y, g y ∂langevinKernel V B P t x
    (∫ x, q x * euclideanLaplacian ψ x) =
      ∫ x, ψ x * ((∫ y, langevinDifferentialOperator V g y ∂langevinKernel V B P t x) +
        inner ℝ (gradient V x) (gradient q x)) := by
  let q := fun x => ∫ y, g y ∂langevinKernel V B P t x
  have hq : ContDiff ℝ 1 q := contDiff_one_langevinKernel_integral hB hV κ hκ hHess
    (hg.of_le (by norm_num)) hgc t
  obtain ⟨M, hM0, hMg⟩ := compact_continuous_norm_bound hg.continuous hgc
  have hM (x : E) : ‖q x‖ ≤ M :=
    langevinKernel_integral_compact_test_norm_le hB hV κ hκ hHess hMg t x
  obtain ⟨L, hgLip⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hgc hg (by norm_num)
  have hL := lipschitzWith_langevinKernel_integral hB hV κ hκ hHess
    (hg.of_le (by norm_num)) hgc hgLip t
  have hd := weak_langevin_drift_integral_tendsto hB hV hq ⟨M, hM0, hM⟩ hL κ hκ hHess hψ.continuous hψc
  have hh := gaussianAverage_lebesgue_generator_tendsto hψ hψc hq.continuous.measurable M hM0 hM
  have hs := hd.add hh
  have ht := weak_langevinKernel_backward_generator_tendsto hB hV hg hgc κ hκ hHess hψ.continuous hψc t
  have hs' := hs.congr' (show
      (fun h : ℝ => (∫ x, ψ x * (∫ ω, langevinDriftQuotient V q B x h ω ∂P)) +
        ∫ x, ψ x * ((gaussianAverage q x (Real.sqrt (2 * h)) - q x) / h)) =ᶠ[𝓝[>] 0]
      (fun h => ∫ x, ψ x * (((∫ y, q y ∂langevinKernel V B P h.toNNReal x) - q x) / h)) by
    filter_upwards [self_mem_nhdsWithin] with h hhpos
    exact (weak_langevinKernel_generator_split_c1 hB hV hq ⟨M, hM0, hM⟩ κ hκ hHess
      hψ.continuous hψc hhpos).symm)
  have heq := tendsto_nhds_unique ht hs'
  have hiDrift : Integrable (fun x => ψ x * inner ℝ (gradient V x) (gradient q x)) volume := by
    have hcV : Continuous (gradient V) := (InnerProductSpace.toDual ℝ E).symm.continuous.comp
      ((hV.of_le (by norm_num) : ContDiff ℝ 1 V).continuous_fderiv one_ne_zero)
    have hcq : Continuous (gradient q) := (InnerProductSpace.toDual ℝ E).symm.continuous.comp (hq.continuous_fderiv one_ne_zero)
    exact ((hψ.continuous.mul (hcV.inner hcq)).integrable_of_hasCompactSupport
      (hψc.mul_right))
  have hiK : Integrable (fun x => ψ x * (∫ y, langevinDifferentialOperator V g y ∂langevinKernel V B P t x)) volume := by
    obtain ⟨N, _, hN⟩ := compact_continuous_norm_bound
      (continuous_langevinDifferentialOperator hV hg) (hasCompactSupport_langevinDifferentialOperator V hgc)
    exact integrable_compact_coefficient_bounded hψ.continuous hψc
      ((continuous_langevinDifferentialOperator hV hg).measurable.stronglyMeasurable.integral_kernel.measurable)
      (fun x => langevinKernel_integral_compact_test_norm_le hB hV κ hκ hHess hN t x)
  have hneg : (∫ x, ψ x * (-inner ℝ (gradient V x) (gradient q x))) =
      -(∫ x, ψ x * inner ℝ (gradient V x) (gradient q x)) := by
    simp only [mul_neg, integral_neg]
  change (∫ x, q x * euclideanLaplacian ψ x) = _
  simp only [mul_add]
  rw [integral_add hiK hiDrift]
  rw [hneg] at heq
  linarith

end CutoffRigidity
