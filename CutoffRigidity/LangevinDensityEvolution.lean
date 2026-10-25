module

public import CutoffRigidity.LangevinL2Operator
public import CutoffRigidity.LangevinFisherContraction

/-! # Actual reversible density evolution

Symmetry is derived from the actual stochastic/form L² identification.
Testing actual evolved measures then proves that the density evolves by
that same kernel, rather than assuming a reversibility or density formula.
-/
public section
namespace CutoffRigidity
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

/-- Genuine stochastic evolution of every bounded nonnegative normalized
measurable density is its actual kernel evolution relative to Gibbs. -/
theorem langevinKernel_withDensity_eq
    {Ω : Type*} [MeasurableSpace Ω] {B : ℝ≥0 → Ω → E} {P : Measure Ω}
    (hB : IsEuclideanBrownian B P) {V : E → ℝ}
    (hV : ContDiff ℝ 2 V) (hp : IsProbabilityMeasure (gibbsMeasure volume V))
    (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    {f : E → ℝ} (hf : Measurable f) (hn : ∀ x, 0 ≤ f x)
    (hBound : ∃ M : ℝ, ∀ x, ‖f x‖ ≤ M)
    (hν : IsProbabilityMeasure ((gibbsMeasure volume V).withDensity (fun x => ENNReal.ofReal (f x))))
    (t : ℝ≥0) :
    langevinKernel V B P t ∘ₘ
        ((gibbsMeasure volume V).withDensity (fun x => ENNReal.ofReal (f x))) =
      (gibbsMeasure volume V).withDensity
        (fun x => ENNReal.ofReal (∫ y, f y ∂langevinKernel V B P t x)) := by
  let := hp
  let := hν
  let μ := gibbsMeasure volume V
  let K := langevinKernel V B P t
  let ν := μ.withDensity (fun x => ENNReal.ofReal (f x))
  let q := fun x => ∫ y, f y ∂K x
  let := langevinKernel_isMarkovKernel hB hV ρ hρ.le hHess t
  have hInv : K ∘ₘ μ = μ := langevinKernel_gibbs_invariant hB hV hp ρ hρ hHess t
  obtain ⟨M, hM⟩ := hBound
  have hfLp : MemLp f 2 μ := MemLp.of_bound hf.aestronglyMeasurable M (Eventually.of_forall hM)
  have hqM : StronglyMeasurable q := hf.stronglyMeasurable.integral_kernel
  have hqB (x : E) : ‖q x‖ ≤ M := by
    simpa only [measureReal_def, measure_univ, ENNReal.toReal_one, mul_one] using
      norm_integral_le_of_norm_le_const (μ := K x) (Eventually.of_forall hM)
  have hqI : Integrable q μ := (integrable_const M).mono' hqM.aestronglyMeasurable (Eventually.of_forall hqB)
  have hqn (x : E) : 0 ≤ q x := integral_nonneg hn
  have hFinite : IsFiniteMeasure (μ.withDensity (fun x => ENNReal.ofReal (q x))) := by
    apply isFiniteMeasure_withDensity
    rw [← ofReal_integral_eq_lintegral_ofReal hqI (Eventually.of_forall hqn)]
    exact ENNReal.ofReal_ne_top
  let := hFinite
  apply measure_eq_of_compact_c2_integrals
  intro ψ hψ hψc
  have hψLp : MemLp ψ 2 μ := hψ.continuous.memLp_of_hasCompactSupport hψc
  have hKF : langevinL2Operator hB hV hp ρ hρ hHess t (hfLp.toLp f) =ᵐ[μ] q :=
    (langevinL2Operator_coeFn hB hV hp ρ hρ hHess t _).trans
      (invariantKernel_integral_congr_ae K hInv hfLp.coeFn_toLp)
  have hKψ : langevinL2Operator hB hV hp ρ hρ hHess t (hψLp.toLp ψ) =ᵐ[μ]
      fun x => ∫ y, ψ y ∂K x :=
    (langevinL2Operator_coeFn hB hV hp ρ hρ hHess t _).trans
      (invariantKernel_integral_congr_ae K hInv hψLp.coeFn_toLp)
  have hs := langevinL2Operator_symmetric hB hV hp ρ hρ hHess t (hfLp.toLp f) (hψLp.toLp ψ)
  have hleft : inner ℝ (langevinL2Operator hB hV hp ρ hρ hHess t (hfLp.toLp f)) (hψLp.toLp ψ) =
      ∫ x, q x * ψ x ∂μ := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hKF, hψLp.coeFn_toLp] with x hx hxψ
    simp only [hx, hxψ, RCLike.inner_apply, conj_trivial, mul_comm]
  have hright : inner ℝ (hfLp.toLp f) (langevinL2Operator hB hV hp ρ hρ hHess t (hψLp.toLp ψ)) =
      ∫ x, f x * (∫ y, ψ y ∂K x) ∂μ := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hfLp.coeFn_toLp, hKψ] with x hxf hxψ
    simp only [hxf, hxψ, RCLike.inner_apply, conj_trivial, mul_comm]
  rw [hleft, hright] at hs
  have hiψ : Integrable ψ (K ∘ₘ ν) := integrable_compact_test_comp hψ.continuous hψc aemeasurable_id
  have hcomp : (∫ y, ψ y ∂(K ∘ₘ ν)) = ∫ x, (∫ y, ψ y ∂K x) ∂ν := by
    rw [Measure.comp_eq_comp_const_apply] at hiψ ⊢
    exact Kernel.integral_comp hiψ
  change (∫ y, ψ y ∂(K ∘ₘ ν)) = ∫ x, ψ x ∂μ.withDensity (fun x => ENNReal.ofReal (q x))
  rw [hcomp, integral_withDensity_eq_integral_toReal_smul hf.ennreal_ofReal (by simp),
    integral_withDensity_eq_integral_toReal_smul hqM.measurable.ennreal_ofReal (by simp)]
  simp only [ENNReal.toReal_ofReal (hn _), ENNReal.toReal_ofReal (hqn _), smul_eq_mul]
  exact hs.symm

/-- Source Fisher contraction stated for the actual evolved probability
measure, using the derived density symmetry bridge rather than a density
formula or invariance premise. -/
theorem langevinKernel_evolved_relativeFisherInformation_le
    {Ω : Type*} [MeasurableSpace Ω] {B : ℝ≥0 → Ω → E} {P : Measure Ω}
    (hB : IsEuclideanBrownian B P) {V g : E → ℝ}
    (hV : ContDiff ℝ 2 V) (hp : IsProbabilityMeasure (gibbsMeasure volume V))
    (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (hg : ContDiff ℝ 1 g) (hgc : HasCompactSupport g)
    (c m : ℝ) (hm : 0 < m) (hpos : ∀ x, m ≤ c + g x)
    (hNorm : ∫ x, (c + g x) ∂gibbsMeasure volume V = 1) (t : ℝ≥0) :
    let ν := (gibbsMeasure volume V).withDensity (fun x => ENNReal.ofReal (c + g x))
    ∃ hν : IsProbabilityMeasure ν,
      letI := hν
      letI := langevinKernel_isMarkovKernel hB hV ρ hρ.le hHess t
      relativeFisherInformation hV hp (langevinKernel V B P t ∘ₘ ν) ≤
        ENNReal.ofReal (Real.exp (-2 * ρ * t)) * relativeFisherInformation hV hp ν := by
  obtain ⟨hν, hνt, hFI⟩ := langevinKernel_relativeFisherInformation_le
    hB hV hp ρ hρ hHess hg hgc c m hm hpos hNorm t
  refine ⟨hν, ?_⟩
  let := hν
  let := hνt
  let := langevinKernel_isMarkovKernel hB hV ρ hρ.le hHess t
  obtain ⟨M, hM⟩ := hgc.exists_bound_of_continuous hg.continuous
  have hBound : ∃ N : ℝ, ∀ x, ‖c + g x‖ ≤ N := by
    refine ⟨|c| + M, fun x => ?_⟩
    exact (norm_add_le _ _).trans (add_le_add (by simp) (hM _))
  have hf : Measurable (fun x => c + g x) := measurable_const.add hg.continuous.measurable
  have heq := langevinKernel_withDensity_eq hB hV hp ρ hρ hHess
    hf (fun x => (hm.trans_le (hpos x)).le) hBound hν t
  simpa only [heq] using hFI

end CutoffRigidity
