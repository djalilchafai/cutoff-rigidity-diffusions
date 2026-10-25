module
public import CutoffRigidity.LangevinDensityEvolution
public import CutoffRigidity.EntropyL2Bound

/-! # Actual evolved entropy tends to zero

The genuine compact-data density error lies in the mean-zero operator
domain. Actual form heat decay, full stochastic L² identification, and the
proved KL/χ² inequality give the entropy limit used in the paper's LSI
argument. No entropy convergence premise is introduced.
-/
public section
namespace CutoffRigidity
open MeasureTheory ProbabilityTheory InformationTheory Set Filter
open scoped Topology NNReal ENNReal
variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

/-- Genuine quantitative entropy decay for actual stochastic evolution
of a normalized positive constant-plus-compact C² density. -/
theorem langevinKernel_klDiv_toReal_le_exp_L2_error
    {Ω : Type*} [MeasurableSpace Ω] {B : ℝ≥0 → Ω → E} {P : Measure Ω}
    (hB : IsEuclideanBrownian B P) {V g : E → ℝ}
    (hV : ContDiff ℝ 2 V) (hp : IsProbabilityMeasure (gibbsMeasure volume V))
    (hd : 0 < d) (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g)
    (c m : ℝ) (hm : 0 < m) (hpos : ∀ x, m ≤ c + g x)
    (hNorm : ∫ x, c + g x ∂gibbsMeasure volume V = 1) {T : ℝ} (hT : 0 ≤ T) :
    (klDiv (langevinKernel V B P T.toNNReal ∘ₘ
      ((gibbsMeasure volume V).withDensity (fun x => ENNReal.ofReal (c + g x))))
      (gibbsMeasure volume V)).toReal ≤
      Real.exp (-2 * ρ * T) * ∫ x, (c + g x - 1) ^ 2 ∂gibbsMeasure volume V := by
  let := hp
  let μ := gibbsMeasure volume V
  let K := langevinKernel V B P T.toNNReal
  let := langevinKernel_isMarkovKernel hB hV ρ hρ.le hHess T.toNNReal
  let f := fun x => c + g x
  let q := fun x => ∫ y, f y ∂K x
  obtain ⟨hν, hνt, _⟩ := langevinKernel_relativeFisherInformation_le hB hV hp ρ hρ hHess
    (hg.of_le (by norm_num)) hgc c m hm hpos hNorm T.toNNReal
  let := hν
  let := hνt
  have hfM : Measurable f := measurable_const.add hg.continuous.measurable
  obtain ⟨M, hM⟩ := hgc.exists_bound_of_continuous hg.continuous
  have hfBound (x : E) : ‖f x‖ ≤ |c| + M := (norm_add_le _ _).trans (add_le_add (by simp) (hM _))
  have hfI : Integrable f μ := (integrable_const (|c| + M)).mono' hfM.aestronglyMeasurable (Eventually.of_forall hfBound)
  have hqB (x : E) : ‖q x‖ ≤ |c| + M := by
    simpa only [measureReal_def, measure_univ, ENNReal.toReal_one, mul_one] using
      norm_integral_le_of_norm_le_const (μ := K x) (Eventually.of_forall hfBound)
  have hqM : Measurable q := hfM.stronglyMeasurable.integral_kernel.measurable
  have hqLp : MemLp q 2 μ := MemLp.of_bound hqM.aestronglyMeasurable (|c| + M) (Eventually.of_forall hqB)
  have hqn (x : E) : 0 ≤ q x := integral_nonneg (fun y => (hm.trans_le (hpos y)).le)
  have hLaw := langevinKernel_withDensity_eq hB hV hp ρ hρ hHess hfM
    (fun x => (hm.trans_le (hpos x)).le) ⟨|c| + M, hfBound⟩ hν T.toNNReal
  have hKL := toReal_klDiv_withDensity_le_L2_error hqM hqLp hqn hνt
  change (klDiv (μ.withDensity (fun x => ENNReal.ofReal (q x))) μ).toReal ≤ _ at hKL
  have hgLp : MemLp g 2 μ := hg.continuous.memLp_of_hasCompactSupport hgc
  let u := gibbsConstantLp hp (c - 1) + hgLp.toLp g
  let H := -langevinCompactTestLp hB hV ρ hρ.le hHess
    (continuous_langevinDifferentialOperator hV hg) (hasCompactSupport_langevinDifferentialOperator V hgc) μ 0
  have hgraph : (u, H) ∈ (gibbsPositiveGenerator hV hp).graph := by
    have hh := langevinCompactTestLp_mem_operatorGraph hB hV hp ρ hρ hHess hg hgc 0
    rw [langevinCompactTestLp_zero hB hV hg hgc ρ hρ.le hHess μ] at hh
    have hs := (gibbsPositiveGenerator hV hp).graph.add_mem
      (gibbsConstantLp_graph_mem hV hp (c - 1)) hh
    simpa only [Prod.mk_add_mk, zero_add] using hs
  have hurep : u =ᵐ[μ] fun x => f x - 1 := by
    filter_upwards [Lp.coeFn_add (gibbsConstantLp hp (c - 1)) (hgLp.toLp g),
      (memLp_const (c - 1) : MemLp (fun _ : E => c - 1) 2 μ).coeFn_toLp, hgLp.coeFn_toLp] with x hadd hc hx
    have hc' : (gibbsConstantLp hp (c - 1) : E → ℝ) x = c - 1 := by convert! hc using 1
    rw [hadd, Pi.add_apply, hc', hx]
    dsimp only [f]
    ring
  have hmean : u ∈ gibbsMeanZeroSpace hp := by
    rw [gibbsMeanZeroSpace, Submodule.mem_orthogonal_singleton_iff_inner_left, L2.inner_def]
    have hEq : (∫ x, inner ℝ (u x) (gibbsConstantLp hp 1 x) ∂μ) = ∫ x, (f x - 1) ∂μ := by
      apply integral_congr_ae
      filter_upwards [hurep, (memLp_const (1 : ℝ) : MemLp (fun _ : E => (1 : ℝ)) 2 μ).coeFn_toLp] with x hx hc
      have hc' : (gibbsConstantLp hp 1 : E → ℝ) x = 1 := by convert! hc using 1
      rw [hx, hc', Real.inner_apply, mul_one]
    rw [hEq, integral_sub hfI (integrable_const 1), hNorm]
    simp
  have hInv : K ∘ₘ μ = μ := langevinKernel_gibbs_invariant hB hV hp ρ hρ hHess T.toNNReal
  have hKurep : langevinL2Operator hB hV hp ρ hρ hHess T.toNNReal u =ᵐ[μ] fun x => q x - 1 := by
    have hh := (langevinL2Operator_coeFn hB hV hp ρ hρ hHess T.toNNReal u).trans
      (invariantKernel_integral_congr_ae K hInv hurep)
    filter_upwards [hh] with x hx
    rw [hx, integral_sub (by
      exact (integrable_const (|c| + M)).mono' hfM.aestronglyMeasurable (Eventually.of_forall hfBound)) (integrable_const 1)]
    simp only [integral_const, measureReal_def, measure_univ, ENNReal.toReal_one, one_smul]
    rfl
  have hnormSq : ‖langevinL2Operator hB hV hp ρ hρ hHess T.toNNReal u‖ ^ 2 =
      ∫ x, (q x - 1) ^ 2 ∂μ := by
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hKurep] with x hx
    rw [hx, real_inner_self_eq_norm_sq, Real.norm_eq_abs, sq_abs]
  have hinitialSq : ‖u‖ ^ 2 = ∫ x, (f x - 1) ^ 2 ∂μ := by
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hurep] with x hx
    rw [hx, real_inner_self_eq_norm_sq, Real.norm_eq_abs, sq_abs]
  have hdecay := gibbsHeatSemigroup_norm_le_exp_meanZero hV hp hd ρ hρ hHess u H hgraph hmean hT
  rw [← langevinL2Operator_eq_gibbsHeatSemigroup hB hV hp ρ hρ hHess T.toNNReal] at hdecay
  have hsq := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.exp_nonneg _) (norm_nonneg _))).mpr hdecay
  have he : Real.exp (-ρ * T) ^ 2 = Real.exp (-2 * ρ * T) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  rw [hnormSq, mul_pow, he, hinitialSq] at hsq
  have hh := hKL.trans hsq
  change (klDiv (K ∘ₘ μ.withDensity (fun x => ENNReal.ofReal (f x))) μ).toReal ≤
    Real.exp (-2 * ρ * T) * ∫ x, (f x - 1) ^ 2 ∂μ
  change K ∘ₘ μ.withDensity (fun x => ENNReal.ofReal (f x)) =
    μ.withDensity (fun x => ENNReal.ofReal (q x)) at hLaw
  rw [hLaw]
  exact hh

/-- Actual entropy is finite for bounded nonnegative initial probability
densities. This explicitly rules out infinite-value truncation by `toReal`. -/
theorem langevinKernel_klDiv_ne_top_of_bounded_density
    {Ω : Type*} [MeasurableSpace Ω] {B : ℝ≥0 → Ω → E} {P : Measure Ω}
    (hB : IsEuclideanBrownian B P) {V : E → ℝ}
    (hV : ContDiff ℝ 2 V) (hp : IsProbabilityMeasure (gibbsMeasure volume V))
    (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    {f : E → ℝ} (hf : Measurable f) (hn : ∀ x, 0 ≤ f x)
    (hBound : ∃ M : ℝ, ∀ x, ‖f x‖ ≤ M)
    (hν : IsProbabilityMeasure ((gibbsMeasure volume V).withDensity (fun x => ENNReal.ofReal (f x))))
    (t : ℝ≥0) :
    klDiv (langevinKernel V B P t ∘ₘ
      ((gibbsMeasure volume V).withDensity (fun x => ENNReal.ofReal (f x))))
      (gibbsMeasure volume V) ≠ ⊤ := by
  let := hp
  let := hν
  let μ := gibbsMeasure volume V
  let K := langevinKernel V B P t
  let := langevinKernel_isMarkovKernel hB hV ρ hρ.le hHess t
  let q := fun x => ∫ y, f y ∂K x
  have hLaw := langevinKernel_withDensity_eq hB hV hp ρ hρ hHess hf hn hBound hν t
  change K ∘ₘ μ.withDensity (fun x => ENNReal.ofReal (f x)) =
    μ.withDensity (fun x => ENNReal.ofReal (q x)) at hLaw
  have hqprob : IsProbabilityMeasure (μ.withDensity (fun x => ENNReal.ofReal (q x))) := by
    rw [← hLaw]
    infer_instance
  have hqM : Measurable q := hf.stronglyMeasurable.integral_kernel.measurable
  obtain ⟨M, hM⟩ := hBound
  have hqLp : MemLp q 2 μ := by
    apply MemLp.of_bound hqM.aestronglyMeasurable M
    apply Eventually.of_forall
    intro x
    simpa only [measureReal_def, measure_univ, ENNReal.toReal_one, mul_one] using
      norm_integral_le_of_norm_le_const (μ := K x) (Eventually.of_forall hM)
  have hh := klDiv_withDensity_ne_top_of_memLp_two hqM hqLp (fun x => integral_nonneg hn) hqprob
  change klDiv (K ∘ₘ μ.withDensity (fun x => ENNReal.ofReal (f x))) μ ≠ ⊤
  rw [hLaw]
  exact hh

/-- The actual evolved entropy tends to zero at infinite time, obtained
from true L² decay and the actual KL/χ² estimate. -/
theorem tendsto_klDiv_langevinKernel_toReal_zero
    {Ω : Type*} [MeasurableSpace Ω] {B : ℝ≥0 → Ω → E} {P : Measure Ω}
    (hB : IsEuclideanBrownian B P) {V g : E → ℝ}
    (hV : ContDiff ℝ 2 V) (hp : IsProbabilityMeasure (gibbsMeasure volume V))
    (hd : 0 < d) (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g)
    (c m : ℝ) (hm : 0 < m) (hpos : ∀ x, m ≤ c + g x)
    (hNorm : ∫ x, c + g x ∂gibbsMeasure volume V = 1) :
    Tendsto (fun T : ℝ =>
      (klDiv (langevinKernel V B P T.toNNReal ∘ₘ
        ((gibbsMeasure volume V).withDensity (fun x => ENNReal.ofReal (c + g x))))
        (gibbsMeasure volume V)).toReal) atTop (𝓝 0) := by
  have he : Tendsto (fun T : ℝ => Real.exp (-2 * ρ * T)) atTop (𝓝 0) := by
    have hh := Real.tendsto_exp_neg_atTop_nhds_zero.comp
      (tendsto_id.const_mul_atTop (show 0 < 2 * ρ by positivity))
    simpa only [Function.comp_def, id_eq, neg_mul] using hh
  have hbound := he.mul_const (∫ x, (c + g x - 1) ^ 2 ∂gibbsMeasure volume V)
  simp only [zero_mul] at hbound
  apply squeeze_zero' (Eventually.of_forall (fun T => ENNReal.toReal_nonneg)) ?_ hbound
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with T hT
  exact langevinKernel_klDiv_toReal_le_exp_L2_error hB hV hp hd ρ hρ hHess hg hgc c m hm hpos hNorm hT

end CutoffRigidity
