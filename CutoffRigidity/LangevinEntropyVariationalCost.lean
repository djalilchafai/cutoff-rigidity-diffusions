module
public import CutoffRigidity.LangevinStandardLogHarnack
public import CutoffRigidity.LangevinPositiveProfileFacts
public import CutoffRigidity.CouplingIntegralBound

/-! # Entropy variational budgets for every actual initial probability law

Applying the source interpolation to exp φ, with compact C² φ, gives a
quadratic transport bound for the genuine entropy test budget. This includes
Dirac initial laws and requires no initial density or Fisher domain premise.
-/
public section
namespace CutoffRigidity
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal
variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

set_option maxHeartbeats 800000 in
theorem langevinKernel_compact_entropy_test_le_cost
    {B : NNReal → Ω → E} {P : Measure Ω} (hB : IsEuclideanBrownian B P)
    {V : E → ℝ} (hV : ContDiff ℝ 2 V) (hp : IsProbabilityMeasure (gibbsMeasure volume V))
    (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (ν : Measure E) [IsProbabilityMeasure ν]
    (φ : E → ℝ) (hφ : ContDiff ℝ 2 φ) (hφc : HasCompactSupport φ)
    (T : ℝ) (hT : 0 < T) :
    ENNReal.ofReal ((∫ x, φ x ∂(langevinKernel V B P T.toNNReal ∘ₘ ν)) -
      (∫ x, Real.exp (φ x) ∂gibbsMeasure volume V) + 1) ≤
      ENNReal.ofReal (ρ / (2 * (Real.exp (2 * ρ * T) - 1))) *
        squaredWasserstein ν (gibbsMeasure volume V) := by
  let := hp
  let μ := gibbsMeasure volume V
  let K := langevinKernel V B P T.toNNReal
  let := langevinKernel_isMarkovKernel hB hV ρ hρ.le hHess T.toNNReal
  let g := fun x : E => Real.exp (φ x) - 1
  have hg : ContDiff ℝ 2 g := hφ.exp.sub contDiff_const
  have hgc : HasCompactSupport g := by
    apply HasCompactSupport.of_support_subset_isCompact hφc
    intro x hx
    by_contra hn
    have hz := image_eq_zero_of_notMem_tsupport hn
    simpa [g, hz] using hx
  obtain ⟨M,hM0,hM⟩ := compact_continuous_norm_bound hφ.continuous hφc
  let m := Real.exp (-M)
  have hm : 0 < m := Real.exp_pos _
  have hpos (x : E) : m ≤ 1 + g x := by
    have hh := hM x
    rw [Real.norm_eq_abs] at hh
    have hb := (abs_le.mp hh).1
    simpa only [g, add_sub_cancel] using Real.exp_le_exp.mpr hb
  let q := langevinPositiveProfile V g B P 1 T
  let J := ∫ x, Real.exp (φ x) ∂μ
  let A := fun x : E => (∫ y, φ y ∂K x) - J + 1
  let B0 := fun x : E => Real.log (q x) - J + 1
  let C := ρ / (2 * (Real.exp (2 * ρ * T) - 1))
  have hAC : Continuous A := ((continuous_langevinKernel_integral_initial hB hV hφ.continuous
    ⟨M,hM⟩ ρ hρ.le hHess T.toNNReal).sub continuous_const).add continuous_const
  have hAcoreB (x : E) : ‖∫ y, φ y ∂K x‖ ≤ M := by
    simpa using norm_integral_le_of_norm_le_const (μ := K x) (Eventually.of_forall hM)
  have hAb (x : E) : ‖A x‖ ≤ M + |J| + 1 :=
    (norm_add_le _ _).trans (add_le_add ((norm_sub_le _ _).trans
      (add_le_add (hAcoreB x) (by simp))) (by simp))
  obtain ⟨N,L,hlogC,hlogB,hlogLip⟩ :=
    langevinLogProfile_bounded_c1_lipschitz hB hV hg hgc ρ hρ.le hHess 1 m hm hpos T
  have hBC : Continuous B0 := (hlogC.continuous.sub continuous_const).add continuous_const
  have hBb (x : E) : ‖B0 x‖ ≤ N + |J| + 1 :=
    (norm_add_le _ _).trans (add_le_add ((norm_sub_le _ _).trans
      (add_le_add (hlogB x) (by simp))) (by simp))
  have hqC : Continuous q := continuous_const.add
    (contDiff_one_langevinKernel_integral hB hV ρ hρ.le hHess (hg.of_le (by norm_num)) hgc T.toNNReal).continuous
  obtain ⟨Ng,hNg⟩ := hgc.exists_bound_of_continuous hg.continuous
  have hqi : Integrable q μ := by
    apply (integrable_const (1+Ng)).mono' hqC.aestronglyMeasurable
    exact Eventually.of_forall fun x => (norm_add_le _ _).trans (add_le_add (by norm_num)
      (langevinKernel_integral_compact_test_norm_le hB hV ρ hρ.le hHess hNg T.toNNReal x))
  have hqJ : ∫ x, q x ∂μ = J := by
    rw [integral_langevinPositiveProfile hB hV hp hg.continuous hgc ρ hρ hHess 1 T]
    apply integral_congr_ae
    exact Eventually.of_forall fun x => by dsimp [g]; ring
  have hlogi : Integrable (fun x => Real.log (q x)) μ :=
    (integrable_const N).mono' hlogC.continuous.aestronglyMeasurable (Eventually.of_forall hlogB)
  have hBmean : ∫ x, B0 x ∂μ ≤ 0 := by
    have hi := integral_mono hlogi (hqi.sub (integrable_const 1)) (fun x =>
      Real.log_le_sub_one_of_pos (hm.trans_le
        (langevinPositiveProfile_lower hB hV hg hgc ρ hρ.le hHess 1 m hpos T x)))
    simp only [Pi.sub_apply] at hi
    rw [integral_sub hqi (integrable_const 1), hqJ] at hi
    change (∫ x, Real.log (q x) - J + 1 ∂μ) ≤ 0
    have he := integral_add (hlogi.sub (integrable_const J)) (integrable_const (1 : ℝ))
    simp only [Pi.sub_apply] at he
    rw [he, integral_sub hlogi (integrable_const J)]
    simp only [integral_const, measureReal_def, measure_univ, ENNReal.toReal_one, one_smul] at hi ⊢
    linarith
  have hφi : Integrable φ (K ∘ₘ ν) := (integrable_const M).mono' hφ.continuous.aestronglyMeasurable
    (Eventually.of_forall hM)
  have hcomp : ∫ x, φ x ∂(K ∘ₘ ν) = ∫ x, (∫ y, φ y ∂K x) ∂ν := by
    rw [Measure.comp_eq_comp_const_apply] at hφi ⊢
    exact Kernel.integral_comp hφi
  have hAi : Integrable (fun x => ∫ y, φ y ∂K x) ν :=
    (integrable_const M).mono' hφ.continuous.measurable.stronglyMeasurable.integral_kernel.aestronglyMeasurable
      (Eventually.of_forall hAcoreB)
  have hH : (∫ x, φ x ∂(K ∘ₘ ν)) - J + 1 = ∫ x, A x ∂ν := by
    rw [hcomp]
    dsimp only [A]
    have he := integral_add (hAi.sub (integrable_const J)) (integrable_const (1 : ℝ))
    simp only [Pi.sub_apply] at he
    rw [he, integral_sub hAi (integrable_const J)]
    simp
  have hC : 0 < C := div_pos hρ (mul_pos (by norm_num)
    (sub_pos.mpr (Real.one_lt_exp_iff.mpr (by positivity))))
  apply ofReal_le_mul_squaredWasserstein_of_pointwise ν μ A B0 hAC hBC ⟨_,hAb⟩ ⟨_,hBb⟩ C _ hC hH hBmean
  intro x y
  have he := langevinKernel_standard_log_harnack_compact_perturbation hB hV hp hg hgc
    ρ hρ hHess 1 m hm hpos T hT x y
  have hlog (z : E) : Real.log (1 + g z) = φ z := by
    dsimp [g]
    rw [add_sub_cancel, Real.log_exp]
  simp_rw [hlog] at he
  change (∫ z, φ z ∂K x) - J + 1 ≤ Real.log (q y) - J + 1 + C * ‖x-y‖ ^ 2
  have hh : (∫ z, φ z ∂K x) ≤ Real.log (q y) + C * ‖x-y‖ ^ 2 := by
    convert! he using 1
    dsimp only [C]
    ring
  linarith

end CutoffRigidity
