module
public import CutoffRigidity.HopfLax
public import CutoffRigidity.TransportWeakDuality

/-! # The actual Hopf–Lax dual functional and primal quadratic transport -/
public section
namespace CutoffRigidity
open MeasureTheory
open scoped ENNReal NNReal
variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E]
  [BorelSpace E] [SecondCountableTopology E]

/-- The actual Hopf–Lax dual value is below the actual coupling infimum.
The reverse inequality remains the separate strong-duality obligation. -/
theorem hopfLax_transport_weak_duality
    (μ ν : Measure E) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {t M : ℝ} (ht : 0 < t) {f : E → ℝ} (hf : ∀ x, |f x| ≤ M)
    {L : NNReal} (hL : LipschitzWith L f) :
    ENNReal.ofReal (2*t*((∫ x,hopfLax t f x ∂ν)-(∫ y,f y ∂μ))) ≤ squaredWasserstein ν μ := by
  have hfμ : Integrable f μ := (integrable_const M).mono' hL.continuous.aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs] using hf x)
  have hQCont := (lipschitzWith_hopfLax ht.le hf hL).continuous
  have hQν : Integrable (hopfLax t f) ν := by
    apply (integrable_const M).mono' hQCont.aestronglyMeasurable
    apply Filter.Eventually.of_forall
    intro x
    have hb := hopfLax_bounds ht.le hf x
    rw [Real.norm_eq_abs,abs_le]
    exact ⟨hb.1,hb.2.trans (abs_le.mp (hf x)).2⟩
  have hdual (x y : E) : 2*t*hopfLax t f x + -(2*t*f y) ≤ ‖x-y‖^2 := by
    have hh := hopfLax_le_cost ht (fun z => (abs_le.mp (hf z)).1) x y
    have hh' : hopfLax t f x-f y ≤ ‖x-y‖^2/(2*t) := by linarith
    have hh'' := (le_div_iff₀ (by positivity : 0 < 2*t)).mp hh'
    nlinarith only [hh'']
  have hh := quadratic_transport_weak_duality ν μ
    (fun x => 2*t*hopfLax t f x) (fun y => -(2*t*f y))
    (hQν.const_mul (2*t)) (hfμ.const_mul (2*t)).neg hdual
  rw [integral_const_mul,integral_neg,integral_const_mul] at hh
  convert hh using 1
  congr 1
  ring

end CutoffRigidity
