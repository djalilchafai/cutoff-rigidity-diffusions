module
public import CutoffRigidity.LangevinLogHarnack
public import CutoffRigidity.LangevinPositiveProfileFacts
public import CutoffRigidity.CouplingIntegralBound
public import CutoffRigidity.EntropyL2Bound

/-! # Actual entropy-cost regularization for the source core densities

The cited BGL optimized-path inequality is integrated against genuine
couplings. Actual stochastic reversibility identifies its left side with
relative entropy; normalization and log u ≤ u−1 bound its other marginal.
-/
public section
namespace CutoffRigidity
open MeasureTheory ProbabilityTheory InformationTheory Filter
open scoped Topology NNReal ENNReal
variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

set_option maxHeartbeats 800000 in
theorem klDiv_langevinKernel_compact_density_le_cost
    {B : NNReal → Ω → E} {P : Measure Ω} (hB : IsEuclideanBrownian B P)
    {V g : E → ℝ} (hV : ContDiff ℝ 2 V) (hp : IsProbabilityMeasure (gibbsMeasure volume V))
    (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g)
    (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (c m : ℝ) (hm : 0 < m) (hpos : ∀ x, m ≤ c + g x)
    (hNorm : ∫ x, (c + g x) ∂gibbsMeasure volume V = 1)
    (T : ℝ) (hT : 0 < T) :
    let μ := gibbsMeasure volume V
    let ν := μ.withDensity (fun x => ENNReal.ofReal (c + g x))
    klDiv (langevinKernel V B P T.toNNReal ∘ₘ ν) μ ≤
      ENNReal.ofReal (ρ / (2 * (Real.exp (2 * ρ * T) - 1))) * squaredWasserstein ν μ := by
  let := hp
  let μ := gibbsMeasure volume V
  let f := fun x : E => c + g x
  let ν := μ.withDensity (fun x => ENNReal.ofReal (f x))
  let K := langevinKernel V B P T.toNNReal
  let := langevinKernel_isMarkovKernel hB hV ρ hρ.le hHess T.toNNReal
  let q := langevinPositiveProfile V g B P c T
  let Q := langevinPositiveProfile V g B P c (2 * T)
  let A := fun x : E => ∫ y, Real.log (q y) ∂K x
  let B0 := fun x : E => Real.log (Q x)
  let C := ρ / (2 * (Real.exp (2 * ρ * T) - 1))
  obtain ⟨M,hM⟩ := hgc.exists_bound_of_continuous hg.continuous
  have hfC : Continuous f := continuous_const.add hg.continuous
  have hfb (x : E) : ‖f x‖ ≤ |c|+M :=
    (norm_add_le _ _).trans (add_le_add (by simp) (hM x))
  have hfI : Integrable f μ := (integrable_const (|c|+M)).mono' hfC.aestronglyMeasurable
    (Eventually.of_forall hfb)
  have hfn (x : E) : 0 ≤ f x := (hm.trans_le (hpos x)).le
  have hν : IsProbabilityMeasure ν := by
    constructor
    rw [withDensity_apply _ MeasurableSet.univ, setLIntegral_univ,
      ← ofReal_integral_eq_lintegral_ofReal hfI (Eventually.of_forall hfn), hNorm]
    norm_num
  let := hν
  have hqProb := langevinPositiveProfile_probability hB hV hp hg hgc ρ hρ hHess c m hm hpos hNorm T
  have hqC : Continuous q := continuous_const.add
    (contDiff_one_langevinKernel_integral hB hV ρ hρ.le hHess (hg.of_le (by norm_num)) hgc T.toNNReal).continuous
  have hQC : Continuous Q := continuous_const.add
    (contDiff_one_langevinKernel_integral hB hV ρ hρ.le hHess (hg.of_le (by norm_num)) hgc (2*T).toNNReal).continuous
  have hqpos (x : E) : 0 < q x := hm.trans_le
    (langevinPositiveProfile_lower hB hV hg hgc ρ hρ.le hHess c m hpos T x)
  have hQpos (x : E) : 0 < Q x := hm.trans_le
    (langevinPositiveProfile_lower hB hV hg hgc ρ hρ.le hHess c m hpos (2*T) x)
  obtain ⟨N, L, hlogC, hlogB, hlogLip⟩ :=
    langevinLogProfile_bounded_c1_lipschitz hB hV hg hgc ρ hρ.le hHess c m hm hpos T
  obtain ⟨N2,L2,hlogC2,hlogB2,hlogLip2⟩ :=
    langevinLogProfile_bounded_c1_lipschitz hB hV hg hgc ρ hρ.le hHess c m hm hpos (2*T)
  have hAC : Continuous A := continuous_langevinKernel_integral_initial hB hV hlogC.continuous
    ⟨N,hlogB⟩ ρ hρ.le hHess T.toNNReal
  have hAb (x : E) : ‖A x‖ ≤ N := by
    simpa [A] using norm_integral_le_of_norm_le_const (μ := K x) (Eventually.of_forall hlogB)
  have hqi : MemLp q 2 μ := by
    apply MemLp.of_bound hqC.aestronglyMeasurable (|c|+M)
    exact Eventually.of_forall fun x => (norm_add_le _ _).trans (add_le_add (by simp)
      (langevinKernel_integral_compact_test_norm_le hB hV ρ hρ.le hHess hM T.toNNReal x))
  have hQi : Integrable Q μ := by
    apply (integrable_const (|c|+M)).mono' hQC.aestronglyMeasurable
    exact Eventually.of_forall fun x => (norm_add_le _ _).trans (add_le_add (by simp)
      (langevinKernel_integral_compact_test_norm_le hB hV ρ hρ.le hHess hM (2*T).toNNReal x))
  have hBmean : ∫ x, B0 x ∂μ ≤ 0 := by
    have hBi : Integrable B0 μ := (integrable_const N2).mono' hlogC2.continuous.aestronglyMeasurable
      (Eventually.of_forall hlogB2)
    have hi := integral_mono hBi (hQi.sub (integrable_const 1))
      (fun x => Real.log_le_sub_one_of_pos (hQpos x))
    simp only [Pi.sub_apply] at hi
    rw [integral_sub hQi (integrable_const 1), integral_langevinPositiveProfile hB hV hp
      hg.continuous hgc ρ hρ hHess c (2*T), hNorm] at hi
    simpa using hi
  have hEq : K ∘ₘ ν = μ.withDensity (fun x => ENNReal.ofReal (q x)) := by
    have he := langevinKernel_withDensity_eq hB hV hp ρ hρ hHess hfC.measurable hfn ⟨_,hfb⟩ hν T.toNNReal
    convert! he using 1
    congr 1
    funext x
    exact congrArg ENNReal.ofReal (langevinPositiveProfile_eq_kernel_integral hB hV hg.continuous hgc ρ hρ.le hHess c T x)
  have hH : (klDiv (K ∘ₘ ν) μ).toReal = ∫ x, A x ∂ν := by
    rw [hEq, klDiv_toReal_withDensity_eq_density_entropy hqC.measurable (fun x => (hqpos x).le) hqProb]
    rw [integral_withDensity_eq_integral_toReal_smul hfC.measurable.ennreal_ofReal (by simp)]
    simp only [ENNReal.toReal_ofReal (hfn _), smul_eq_mul]
    have hs := langevinKernel_integral_mul_comm_bounded hB hV hp ρ hρ hHess
      hfC.measurable hlogC.continuous.measurable ⟨_,hfb⟩ ⟨N,hlogB⟩ T.toNNReal
    have hqK (x : E) : (∫ y, f y ∂langevinKernel V B P T.toNNReal x) = q x :=
      (langevinPositiveProfile_eq_kernel_integral hB hV hg.continuous hgc ρ hρ.le hHess c T x).symm
    simp_rw [hqK] at hs
    exact hs.symm
  have hC : 0 < C := div_pos hρ (mul_pos (by norm_num)
    (sub_pos.mpr (Real.one_lt_exp_iff.mpr (by positivity))))
  have hfin : klDiv (K ∘ₘ ν) μ ≠ ⊤ := by
    rw [hEq]
    exact klDiv_withDensity_ne_top_of_memLp_two hqC.measurable hqi (fun x => (hqpos x).le) hqProb
  have hh := ofReal_le_mul_squaredWasserstein_of_pointwise ν μ A B0 hAC hlogC2.continuous
    ⟨N,hAb⟩ ⟨N2,hlogB2⟩ C (klDiv (K ∘ₘ ν) μ).toReal hC hH hBmean (fun x y => ?_)
  · simpa only [ENNReal.ofReal_toReal hfin] using hh
  · have he := langevinKernel_log_harnack_compact_perturbation hB hV hp hg hgc ρ hρ hHess
      c m hm hpos T hT x y
    convert! he using 1 <;> dsimp only [C] <;> ring

end CutoffRigidity
