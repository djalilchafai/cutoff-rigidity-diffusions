module

public import CutoffRigidity.C1FisherInformation
public import CutoffRigidity.WeightedGradientEstimate
public import CutoffRigidity.LangevinC1DriftGenerator
public import CutoffRigidity.LangevinGibbsInvariance

/-! # Genuine Fisher contraction for positive compact perturbations

The actual weighted transition-gradient inequality and the proved stochastic
Gibbs invariance yield decay of the canonical closed-gradient Fisher
functional. Normalization is an explicit integral of the initial density;
normalization of the evolved density is derived from actual invariance.
-/

public section
namespace CutoffRigidity
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

private theorem integral_kernel_invariant {μ : Measure E} [IsProbabilityMeasure μ]
    {K : Kernel E E} [IsMarkovKernel K] (hInv : K ∘ₘ μ = μ)
    {f : E → ℝ} (hi : Integrable f μ) :
    (∫ x, (∫ y, f y ∂K x) ∂μ) = ∫ y, f y ∂μ := by
  have hi' : Integrable f (K ∘ₘ μ) := by rw [hInv]; exact hi
  rw [Measure.comp_eq_comp_const_apply] at hi'
  have hh := Kernel.integral_comp hi'
  simpa only [← Measure.comp_eq_comp_const_apply, hInv, Kernel.const_apply] using hh.symm

private theorem probability_withDensity_of_integral_one {μ : Measure E} [IsProbabilityMeasure μ]
    {f : E → ℝ} (hf : Integrable f μ) (hn : ∀ x, 0 ≤ f x) (hInt : ∫ x, f x ∂μ = 1) :
    IsProbabilityMeasure (μ.withDensity (fun x => ENNReal.ofReal (f x))) := by
  constructor
  rw [withDensity_apply _ MeasurableSet.univ, setLIntegral_univ,
    ← ofReal_integral_eq_lintegral_ofReal hf (Eventually.of_forall hn), hInt]
  norm_num

private theorem gradient_const_add (g : E → ℝ) (c : ℝ) :
    gradient (fun x => c + g x) = gradient g := by
  funext x
  change (InnerProductSpace.toDual ℝ E).symm (fderiv ℝ (fun y => c + g y) x) = _
  rw [fderiv_const_add]
  rfl

/-- Canonical Fisher information decays at the source curvature rate for
the genuine density K_t(c+g) relative to the genuine invariant Gibbs law.
No smooth-score formula, stochastic invariance, or information estimate
is supplied as a premise. -/
theorem langevinKernel_relativeFisherInformation_le
    {Ω : Type*} [MeasurableSpace Ω] {B : ℝ≥0 → Ω → E} {P : Measure Ω}
    (hB : IsEuclideanBrownian B P) {V g : E → ℝ}
    (hV : ContDiff ℝ 2 V) (hp : IsProbabilityMeasure (gibbsMeasure volume V))
    (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (hg : ContDiff ℝ 1 g) (hgc : HasCompactSupport g)
    (c m : ℝ) (hm : 0 < m) (hpos : ∀ x, m ≤ c + g x)
    (hNorm : ∫ x, (c + g x) ∂gibbsMeasure volume V = 1) (t : ℝ≥0) :
    let μ := gibbsMeasure volume V
    let f := fun x => c + g x
    let q := fun x => ∫ y, f y ∂langevinKernel V B P t x
    ∃ (hν : IsProbabilityMeasure (μ.withDensity (fun x => ENNReal.ofReal (f x))))
      (hνt : IsProbabilityMeasure (μ.withDensity (fun x => ENNReal.ofReal (q x)))),
      letI := hν
      letI := hνt
      relativeFisherInformation hV hp (μ.withDensity (fun x => ENNReal.ofReal (q x))) ≤
        ENNReal.ofReal (Real.exp (-2 * ρ * t)) *
          relativeFisherInformation hV hp (μ.withDensity (fun x => ENNReal.ofReal (f x))) := by
  let := hp
  let μ := gibbsMeasure volume V
  let K := langevinKernel V B P t
  let := langevinKernel_isMarkovKernel hB hV ρ hρ.le hHess t
  let f := fun x => c + g x
  let q := fun x => ∫ y, f y ∂K x
  have hf : ContDiff ℝ 1 f := contDiff_const.add hg
  obtain ⟨L, hLip⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hgc hg (by norm_num)
  obtain ⟨M, hM⟩ := hgc.exists_bound_of_continuous hg.continuous
  have hfBound (x : E) : ‖f x‖ ≤ |c| + M :=
    (norm_add_le _ _).trans (add_le_add (by simp) (hM _))
  have hfI (ν : Measure E) [IsProbabilityMeasure ν] : Integrable f ν :=
    (integrable_const (|c| + M)).mono' hf.continuous.aestronglyMeasurable (Eventually.of_forall hfBound)
  have hqeq : q = fun x => c + ∫ y, g y ∂K x := by
    funext x
    have hgI : Integrable g (K x) := (integrable_const M).mono' hg.continuous.aestronglyMeasurable
      (Eventually.of_forall hM)
    change (∫ y, c + g y ∂K x) = _
    rw [integral_add (integrable_const c) hgI]
    simp
  have hq : ContDiff ℝ 1 q := by
    rw [hqeq]
    exact contDiff_const.add (contDiff_one_langevinKernel_integral hB hV ρ hρ.le hHess hg hgc t)
  have hqpos (x : E) : m ≤ q x := by
    have hh := integral_mono (integrable_const m) (hfI (K x)) hpos
    simpa only [integral_const, measureReal_def, measure_univ, ENNReal.toReal_one, one_smul] using hh
  have hqBound (x : E) : ‖q x‖ ≤ |c| + M := by
    simpa only [measureReal_def, measure_univ, ENNReal.toReal_one, mul_one] using
      norm_integral_le_of_norm_le_const (μ := K x) (Eventually.of_forall hfBound)
  have hqI : Integrable q μ := (integrable_const (|c| + M)).mono' hq.continuous.aestronglyMeasurable
    (Eventually.of_forall hqBound)
  have hInv : K ∘ₘ μ = μ := langevinKernel_gibbs_invariant hB hV hp ρ hρ hHess t
  have hqNorm : ∫ x, q x ∂μ = 1 := (integral_kernel_invariant hInv (hfI μ)).trans hNorm
  have hν := probability_withDensity_of_integral_one (hfI μ) (fun x => (hm.trans_le (hpos x)).le) hNorm
  have hνt := probability_withDensity_of_integral_one hqI (fun x => (hm.trans_le (hqpos x)).le) hqNorm
  refine ⟨hν, hνt, ?_⟩
  let := hν
  let := hνt
  have hggrad (x : E) : ‖gradient g x‖ ≤ L := by
    change ‖(InnerProductSpace.toDual ℝ E).symm (fderiv ℝ g x)‖ ≤ _
    rw [(InnerProductSpace.toDual ℝ E).symm.norm_map]
    exact norm_fderiv_le_of_lipschitz ℝ hLip
  have hfgrad : MemLp (gradient f) 2 μ := by
    rw [show gradient f = gradient g from gradient_const_add g c]
    exact MemLp.of_bound (continuous_gradient_of_c1 hg).aestronglyMeasurable L
      (Eventually.of_forall hggrad)
  have hqLip := (lipschitzWith_langevinKernel_integral hB hV ρ hρ.le hHess hg hgc hLip t)
  have hqgrad : MemLp (gradient q) 2 μ := by
    apply MemLp.of_bound (continuous_gradient_of_c1 hq).aestronglyMeasurable
      (Real.exp (-ρ * t) * L)
    apply Eventually.of_forall
    intro x
    change ‖(InnerProductSpace.toDual ℝ E).symm (fderiv ℝ q x)‖ ≤ _
    rw [(InnerProductSpace.toDual ℝ E).symm.norm_map]
    rw [hqeq, fderiv_const_add]
    exact norm_fderiv_le_of_lipschitz ℝ hqLip
  let score := fun x => ‖gradient f x‖ ^ 2 / f x
  have hscore := integrable_weighted_gradient_of_memLp hf hm hpos hfgrad
  have hscoreq := integrable_weighted_gradient_of_memLp hq hm hqpos hqgrad
  have hsBound (x : E) : ‖score x‖ ≤ (L : ℝ) ^ 2 / m := by
    change ‖‖gradient f x‖ ^ 2 / f x‖ ≤ _
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (sq_nonneg _) (hm.trans_le (hpos x)).le)]
    have hh : ‖gradient f x‖ ≤ L := by simpa only [f, gradient_const_add] using hggrad x
    exact div_le_div₀ (sq_nonneg _) ((sq_le_sq₀ (norm_nonneg _) L.coe_nonneg).mpr hh) hm (hpos x)
  have hKs : Integrable (fun x => ∫ y, score y ∂K x) μ := by
    have hsM : Measurable score := ((continuous_gradient_of_c1 hf).norm.pow 2).measurable.div hf.continuous.measurable
    apply (integrable_const ((L : ℝ) ^ 2 / m)).mono' hsM.stronglyMeasurable.integral_kernel.aestronglyMeasurable
    apply Eventually.of_forall
    intro x
    simpa using norm_integral_le_of_norm_le_const (μ := K x) (Eventually.of_forall hsBound)
  have hIntegrated := integral_mono hscoreq (hKs.const_mul (Real.exp (-2 * ρ * t)))
    (fun x => langevinKernel_weighted_gradient_le hB hV ρ hρ.le hHess hg hgc c m hm hpos t x)
  rw [integral_const_mul, integral_kernel_invariant hInv hscore] at hIntegrated
  rw [relativeFisherInformation_withDensity_c1_of_memLp hV hp ρ hρ hHess hq m hm hqpos hνt hqgrad,
    relativeFisherInformation_withDensity_c1_of_memLp hV hp ρ hρ hHess hf m hm hpos hν hfgrad,
    ← ENNReal.ofReal_mul (Real.exp_nonneg _)]
  exact ENNReal.ofReal_le_ofReal hIntegrated

end CutoffRigidity
