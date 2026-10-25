module
public import CutoffRigidity.KLScalarVariational

/-! # Genuine measure variational criterion for relative entropy

Bounded measurable exponential tests are bounded by actual KL. Conversely,
null-set tests force absolute continuity and actual clipped-log RN tests
recover the full nonnegative KL integrand through Fatou, including infinite
entropy. No variational representation is assumed.
-/
public section
namespace CutoffRigidity
open MeasureTheory InformationTheory Filter Set
open scoped ENNReal Topology

@[expose] noncomputable def relativeEntropyTest {X : Type*} [MeasurableSpace X]
    (ν μ : Measure X) (φ : X → ℝ) : ℝ :=
  (∫ x, φ x ∂ν) - (∫ x, Real.exp (φ x) ∂μ) + 1

private theorem integrable_bounded_real {X : Type*} [MeasurableSpace X]
    {μ : Measure X} [IsProbabilityMeasure μ] {φ : X → ℝ} (hφ : Measurable φ)
    {M : ℝ} (hM : ∀ x, ‖φ x‖ ≤ M) : Integrable φ μ :=
  (integrable_const M).mono' hφ.aestronglyMeasurable (Eventually.of_forall hM)

private theorem integrable_exp_bounded_real {X : Type*} [MeasurableSpace X]
    {μ : Measure X} [IsProbabilityMeasure μ] {φ : X → ℝ} (hφ : Measurable φ)
    {M : ℝ} (hM : ∀ x, ‖φ x‖ ≤ M) : Integrable (fun x => Real.exp (φ x)) μ := by
  apply (integrable_const (Real.exp M)).mono' hφ.exp.aestronglyMeasurable
  apply Eventually.of_forall
  intro x
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact Real.exp_le_exp.mpr ((le_abs_self _).trans (hM x))

/-- Every actual bounded measurable exponential test is below genuine KL. -/
theorem relativeEntropyTest_le_klDiv
    {X : Type*} [MeasurableSpace X] (ν μ : Measure X) [IsProbabilityMeasure ν] [IsProbabilityMeasure μ]
    {φ : X → ℝ} (hφ : Measurable φ) (hBound : ∃ M : ℝ, ∀ x, ‖φ x‖ ≤ M) :
    ENNReal.ofReal (relativeEntropyTest ν μ φ) ≤ klDiv ν μ := by
  by_cases hfin : klDiv ν μ = ⊤
  · rw [hfin]
    exact le_top
  · obtain ⟨hAC, hLLR⟩ := klDiv_ne_top_iff.mp hfin
    obtain ⟨M, hM⟩ := hBound
    have hφI := integrable_bounded_real (μ := ν) hφ hM
    have hExp := integrable_exp_bounded_real (μ := μ) hφ hM
    have hrφ := integrable_toReal_rnDeriv_mul_iff hAC |>.mpr hφI
    have hG := (hrφ.sub hExp).add (integrable_const 1)
    have hKL := (integrable_klFun_rnDeriv_iff hAC).mpr hLLR
    have hh := integral_mono hG hKL (fun x => klFun_exponential_young ENNReal.toReal_nonneg (φ x))
    simp only [Pi.add_apply, Pi.sub_apply] at hh
    have ha := integral_add (hrφ.sub hExp) (integrable_const (1 : ℝ))
    have hs := integral_sub hrφ hExp
    simp only [Pi.sub_apply] at ha hs
    rw [ha, hs, integral_toReal_rnDeriv_mul hAC] at hh
    simp only [integral_const, measureReal_def, measure_univ, ENNReal.toReal_one, one_smul] at hh
    rw [← toReal_klDiv_eq_integral_klFun hAC] at hh
    exact (ENNReal.ofReal_le_ofReal hh).trans_eq (ENNReal.ofReal_toReal hfin)

/-- A universal actual bounded-measurable test bound controls full KL.
Both absolute continuity and the nonnegative Fatou limit are derived. -/
theorem klDiv_le_of_bounded_measurable_tests
    {X : Type*} [MeasurableSpace X] (ν μ : Measure X) [IsProbabilityMeasure ν] [IsProbabilityMeasure μ]
    (C : ENNReal)
    (hTest : ∀ φ : X → ℝ, Measurable φ → (∃ M : ℝ, ∀ x, ‖φ x‖ ≤ M) →
      ENNReal.ofReal (relativeEntropyTest ν μ φ) ≤ C) : klDiv ν μ ≤ C := by
  classical
  by_cases hC : C = ⊤
  · rw [hC]
    exact le_top
  have hAC : ν ≪ μ := Measure.AbsolutelyContinuous.mk (by
    intro A hA hμA
    by_contra hνA
    have ha : 0 < (ν A).toReal := ENNReal.toReal_pos hνA (measure_ne_top ν A)
    let M := (C.toReal + 1) / (ν A).toReal
    let φ := A.indicator (fun _ : X => M)
    have hφM : Measurable φ := measurable_const.indicator hA
    have hφB : ∃ N : ℝ, ∀ x, ‖φ x‖ ≤ N := by
      refine ⟨|M|, fun x => ?_⟩
      by_cases hx : x ∈ A <;> simp [φ, hx]
    have hφAE : φ =ᵐ[μ] fun _ => (0 : ℝ) := by
      filter_upwards [measure_eq_zero_iff_ae_notMem.mp hμA] with x hx
      simp [φ, hx]
    have hExp : (∫ x, Real.exp (φ x) ∂μ) = 1 := by
      have he : (fun x => Real.exp (φ x)) =ᵐ[μ] fun _ => (1 : ℝ) := by
        filter_upwards [hφAE] with x hx
        rw [hx, Real.exp_zero]
      rw [integral_congr_ae he]
      simp
    have hbudget : relativeEntropyTest ν μ φ = C.toReal + 1 := by
      rw [relativeEntropyTest, hExp]
      have hi : (∫ x, φ x ∂ν) = (ν A).toReal * M := by
        rw [show φ = A.indicator (fun _ : X => M) from rfl, integral_indicator hA, setIntegral_const]
        rfl
      rw [hi]
      dsimp only [M]
      field_simp [ha.ne']
      ring
    have hh := hTest φ hφM hφB
    rw [hbudget] at hh
    have ht := ENNReal.toReal_mono hC hh
    rw [ENNReal.toReal_ofReal (by positivity)] at ht
    linarith)
  let r := fun x => (ν.rnDeriv μ x).toReal
  let φ := fun n x => klLogWitness n (r x)
  let F := fun n x => r x * φ n x - Real.exp (φ n x) + 1
  have hrM : Measurable r := (Measure.measurable_rnDeriv ν μ).ennreal_toReal
  have hφM (n : ℕ) : Measurable (φ n) := (measurable_klLogWitness n).comp hrM
  have hφB (n : ℕ) (x : X) : ‖φ n x‖ ≤ n := abs_klLogWitness_le n (r x)
  have hFM (n : ℕ) : Measurable (F n) :=
    ((hrM.mul (hφM n)).sub (hφM n).exp).add measurable_const
  have hF0 (n : ℕ) (x : X) : 0 ≤ F n x := klLogWitness_integrand_nonneg n ENNReal.toReal_nonneg
  have hFI (n : ℕ) : Integrable (F n) μ := by
    have hφI := integrable_bounded_real (μ := ν) (hφM n) (hφB n)
    exact (((integrable_toReal_rnDeriv_mul_iff hAC).mpr hφI).sub
      (integrable_exp_bounded_real (μ := μ) (hφM n) (hφB n))).add (integrable_const 1)
  have hInt (n : ℕ) : (∫ x, F n x ∂μ) = relativeEntropyTest ν μ (φ n) := by
    have hφI := integrable_bounded_real (μ := ν) (hφM n) (hφB n)
    have hrφ := (integrable_toReal_rnDeriv_mul_iff hAC).mpr hφI
    have hExp := integrable_exp_bounded_real (μ := μ) (hφM n) (hφB n)
    change (∫ x, (ν.rnDeriv μ x).toReal * φ n x - Real.exp (φ n x) + 1 ∂μ) = _
    have ha := integral_add (hrφ.sub hExp) (integrable_const (1 : ℝ))
    have hs := integral_sub hrφ hExp
    simp only [Pi.sub_apply] at ha hs
    rw [ha, hs, integral_toReal_rnDeriv_mul hAC]
    simp [relativeEntropyTest]
  have hbound (n : ℕ) : (∫⁻ x, ENNReal.ofReal (F n x) ∂μ) ≤ C := by
    rw [← ofReal_integral_eq_lintegral_ofReal (hFI n) (Eventually.of_forall (hF0 n)), hInt n]
    exact hTest (φ n) (hφM n) ⟨n, hφB n⟩
  have hpoint : ∀ x, liminf (fun n => ENNReal.ofReal (F n x)) atTop = ENNReal.ofReal (klFun (r x)) := by
    intro x
    exact (ENNReal.continuous_ofReal.continuousAt.tendsto.comp
      (tendsto_klLogWitness_integrand (r := r x) ENNReal.toReal_nonneg)).liminf_eq
  have hFatou := lintegral_liminf_le (μ := μ) (f := fun n x => ENNReal.ofReal (F n x))
    (u := atTop) (fun n => (hFM n).ennreal_ofReal)
  simp only [hpoint] at hFatou
  have hh : liminf (fun n => ∫⁻ x, ENNReal.ofReal (F n x) ∂μ) atTop ≤ C := by
    have ht : liminf (fun n => ∫⁻ x, ENNReal.ofReal (F n x) ∂μ) atTop ≤
        liminf (fun _ : ℕ => C) atTop := liminf_le_liminf (Eventually.of_forall hbound)
    simpa using ht
  rw [klDiv_eq_lintegral_klFun_of_ac hAC]
  exact hFatou.trans hh

end CutoffRigidity
