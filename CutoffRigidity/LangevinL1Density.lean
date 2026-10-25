module
public import CutoffRigidity.LangevinL1Duality
public import CutoffRigidity.LangevinDensityEvolution
public import CutoffRigidity.HellingerL2Convergence

/-! # Actual density evolution on the full absolutely continuous probability domain -/
public section
namespace CutoffRigidity
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

/-- The actual reversible density identity on the full nonnegative L¹
probability-density domain, derived from genuine L¹ duality. -/
theorem langevinKernel_withDensity_eq_of_integrable
    {Ω : Type*} [MeasurableSpace Ω] {B : ℝ≥0 → Ω → E} {P : Measure Ω}
    (hB : IsEuclideanBrownian B P) {V : E → ℝ}
    (hV : ContDiff ℝ 2 V) (hp : IsProbabilityMeasure (gibbsMeasure volume V))
    (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    {f : E → ℝ} (hf : Measurable f) (hn : ∀ x, 0 ≤ f x)
    (hfI : Integrable f (gibbsMeasure volume V))
    (hν : IsProbabilityMeasure ((gibbsMeasure volume V).withDensity (fun x => ENNReal.ofReal (f x))))
    (t : ℝ≥0) :
    langevinKernel V B P t ∘ₘ ((gibbsMeasure volume V).withDensity (fun x => ENNReal.ofReal (f x))) =
      (gibbsMeasure volume V).withDensity (fun x => ENNReal.ofReal (∫ y, f y ∂langevinKernel V B P t x)) := by
  let := hp
  let := hν
  let μ := gibbsMeasure volume V
  let ν := μ.withDensity (fun x => ENNReal.ofReal (f x))
  let K := langevinKernel V B P t
  let := langevinKernel_isMarkovKernel hB hV ρ hρ.le hHess t
  let q := fun x => ∫ y, f y ∂K x
  have hInv : K ∘ₘ μ = μ := langevinKernel_gibbs_invariant hB hV hp ρ hρ hHess t
  have hqI := invariantKernel_integral_integrable K hInv hf hfI
  have hqM : Measurable q := hf.stronglyMeasurable.integral_kernel.measurable
  have hqn (x : E) : 0 ≤ q x := integral_nonneg hn
  have hFinite : IsFiniteMeasure (μ.withDensity (fun x => ENNReal.ofReal (q x))) := by
    apply isFiniteMeasure_withDensity
    rw [← ofReal_integral_eq_lintegral_ofReal hqI (Eventually.of_forall hqn)]
    exact ENNReal.ofReal_ne_top
  let := hFinite
  apply measure_eq_of_compact_c2_integrals
  intro ψ hψ hψc
  obtain ⟨M, hM⟩ := hψc.exists_bound_of_continuous hψ.continuous
  have hdual := langevinKernel_integral_mul_comm_integrable hB hV hp ρ hρ hHess hf hn hfI
    hψ.continuous.measurable ⟨M, hM⟩ t
  have hiψ : Integrable ψ (K ∘ₘ ν) := integrable_compact_test_comp hψ.continuous hψc aemeasurable_id
  have hcomp : (∫ y, ψ y ∂(K ∘ₘ ν)) = ∫ x, (∫ y, ψ y ∂K x) ∂ν := by
    rw [Measure.comp_eq_comp_const_apply] at hiψ ⊢
    exact Kernel.integral_comp hiψ
  change (∫ y, ψ y ∂(K ∘ₘ ν)) = ∫ x, ψ x ∂μ.withDensity (fun x => ENNReal.ofReal (q x))
  rw [hcomp, integral_withDensity_eq_integral_toReal_smul hf.ennreal_ofReal (by simp),
    integral_withDensity_eq_integral_toReal_smul hqM.ennreal_ofReal (by simp)]
  simp only [ENNReal.toReal_ofReal (hn _), ENNReal.toReal_ofReal (hqn _), smul_eq_mul]
  exact hdual

/-- Actual finite absolutely continuous measures are reconstructed from
their genuine real RN density, including the null set of infinite representatives. -/
theorem withDensity_ofReal_toReal_rnDeriv_eq {X : Type*} [MeasurableSpace X]
    (ν μ : Measure X) [IsFiniteMeasure ν] [SigmaFinite μ] (hAC : ν ≪ μ) :
    μ.withDensity (fun x => ENNReal.ofReal ((ν.rnDeriv μ x).toReal)) = ν := by
  calc
    _ = μ.withDensity (ν.rnDeriv μ) := by
      apply withDensity_congr_ae
      filter_upwards [Measure.rnDeriv_ne_top ν μ] with x hx
      exact ENNReal.ofReal_toReal hx
    _ = ν := Measure.withDensity_rnDeriv_eq ν μ hAC

/-- Every actual absolutely continuous initial probability remains
absolutely continuous under the actual Langevin transition. -/
theorem langevinKernel_comp_absolutelyContinuous
    {Ω : Type*} [MeasurableSpace Ω] {B : ℝ≥0 → Ω → E} {P : Measure Ω}
    (hB : IsEuclideanBrownian B P) {V : E → ℝ}
    (hV : ContDiff ℝ 2 V) (hp : IsProbabilityMeasure (gibbsMeasure volume V))
    (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (ν : Measure E) [IsProbabilityMeasure ν] (hAC : ν ≪ gibbsMeasure volume V) (t : ℝ≥0) :
    langevinKernel V B P t ∘ₘ ν ≪ gibbsMeasure volume V := by
  let := hp
  let μ := gibbsMeasure volume V
  let f := fun x => (ν.rnDeriv μ x).toReal
  have hrec := withDensity_ofReal_toReal_rnDeriv_eq ν μ hAC
  have hν : IsProbabilityMeasure (μ.withDensity (fun x => ENNReal.ofReal (f x))) := by rw [hrec]; infer_instance
  have hfM : Measurable f := (Measure.measurable_rnDeriv ν μ).ennreal_toReal
  have hLaw := langevinKernel_withDensity_eq_of_integrable hB hV hp ρ hρ hHess hfM
    (fun x => ENNReal.toReal_nonneg) (integrable_toReal_rnDeriv_finite ν μ) hν t
  rw [hrec] at hLaw
  rw [hLaw]
  exact withDensity_absolutelyContinuous _ _

/-- The actual RN density after transition equals actual averaging of the
initial real RN density almost everywhere, on the full probability domain. -/
theorem langevinKernel_rnDeriv_toReal
    {Ω : Type*} [MeasurableSpace Ω] {B : ℝ≥0 → Ω → E} {P : Measure Ω}
    (hB : IsEuclideanBrownian B P) {V : E → ℝ}
    (hV : ContDiff ℝ 2 V) (hp : IsProbabilityMeasure (gibbsMeasure volume V))
    (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (ν : Measure E) [IsProbabilityMeasure ν] (hAC : ν ≪ gibbsMeasure volume V) (t : ℝ≥0) :
    (fun x => ((langevinKernel V B P t ∘ₘ ν).rnDeriv (gibbsMeasure volume V) x).toReal) =ᵐ[gibbsMeasure volume V]
      fun x => ∫ y, (ν.rnDeriv (gibbsMeasure volume V) y).toReal ∂langevinKernel V B P t x := by
  let := hp
  let μ := gibbsMeasure volume V
  let f := fun x => (ν.rnDeriv μ x).toReal
  have hrec := withDensity_ofReal_toReal_rnDeriv_eq ν μ hAC
  have hν : IsProbabilityMeasure (μ.withDensity (fun x => ENNReal.ofReal (f x))) := by rw [hrec]; infer_instance
  have hfM : Measurable f := (Measure.measurable_rnDeriv ν μ).ennreal_toReal
  have hn (x : E) : 0 ≤ f x := ENNReal.toReal_nonneg
  have hLaw := langevinKernel_withDensity_eq_of_integrable hB hV hp ρ hρ hHess hfM hn
    (integrable_toReal_rnDeriv_finite ν μ) hν t
  rw [hrec] at hLaw
  have hqM : Measurable (fun x => ∫ y, f y ∂langevinKernel V B P t x) :=
    hfM.stronglyMeasurable.integral_kernel.measurable
  have hRN := Measure.rnDeriv_withDensity μ hqM.ennreal_ofReal
  rw [← hLaw] at hRN
  filter_upwards [hRN] with x hx
  rw [hx, ENNReal.toReal_ofReal (integral_nonneg hn)]

end CutoffRigidity
