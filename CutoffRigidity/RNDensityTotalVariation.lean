module
public import CutoffRigidity.RNDensityWeakConvergence
public import CutoffRigidity.TotalVariation

/-! # Actual RN-density L¹ control of genuine total variation -/
public section
namespace CutoffRigidity
open MeasureTheory Filter

 theorem abs_integral_sub_le_L1_rnDeriv
    {X : Type*} [MeasurableSpace X] (ν η μ : Measure X)
    [IsFiniteMeasure ν] [IsFiniteMeasure η] [SigmaFinite μ]
    (hν : ν ≪ μ) (hη : η ≪ μ) {φ : X → ℝ} (hφ : Measurable φ)
    (hφb : ∀ x, ‖φ x‖ ≤ 1) :
    |(∫ x, φ x ∂ν) - ∫ x, φ x ∂η| ≤
      ∫ x, |(ν.rnDeriv μ x).toReal - (η.rnDeriv μ x).toReal| ∂μ := by
  let f := fun x => (ν.rnDeriv μ x).toReal
  let g := fun x => (η.rnDeriv μ x).toReal
  have hf := integrable_toReal_rnDeriv_finite ν μ
  have hg := integrable_toReal_rnDeriv_finite η μ
  have hfi := hf.mul_bdd hφ.aestronglyMeasurable (Eventually.of_forall hφb)
  have hgi := hg.mul_bdd hφ.aestronglyMeasurable (Eventually.of_forall hφb)
  rw [integral_eq_integral_toReal_rnDeriv_mul ν μ hν hφ,
    integral_eq_integral_toReal_rnDeriv_mul η μ hη hφ,
    ← integral_sub hfi hgi, ← Real.norm_eq_abs]
  apply (norm_integral_le_integral_norm _).trans
  apply integral_mono_ae (hfi.sub hgi).norm (hf.sub hg).abs
  apply Eventually.of_forall
  intro x
  simp only [Pi.sub_apply]
  rw [← sub_mul, norm_mul, Real.norm_eq_abs (f x - g x)]
  exact mul_le_of_le_one_right (abs_nonneg _) (hφb x)

theorem totalVariationDistance_le_L1_rnDeriv
    {X : Type*} [MeasurableSpace X] (ν η μ : Measure X)
    [IsProbabilityMeasure ν] [IsProbabilityMeasure η] [SigmaFinite μ]
    (hν : ν ≪ μ) (hη : η ≪ μ) :
    totalVariationDistance ν η ≤ ∫ x, |(ν.rnDeriv μ x).toReal - (η.rnDeriv μ x).toReal| ∂μ := by
  apply csSup_le (show {r : ℝ | ∃ A : Set X, MeasurableSet A ∧ r = |ν.real A - η.real A|}.Nonempty from
    ⟨0,∅,MeasurableSet.empty,by simp⟩)
  rintro r ⟨A,hA,rfl⟩
  let φ := A.indicator (fun _ : X => (1 : ℝ))
  have hφ : Measurable φ := measurable_const.indicator hA
  have hb (x : X) : ‖φ x‖ ≤ 1 := by by_cases hx : x ∈ A <;> simp [φ,hx]
  have he (ζ : Measure X) : (∫ x, φ x ∂ζ) = ζ.real A := by simp [φ,integral_indicator hA]
  have hh := abs_integral_sub_le_L1_rnDeriv ν η μ hν hη hφ hb
  rw [he ν,he η] at hh
  exact hh

end CutoffRigidity
