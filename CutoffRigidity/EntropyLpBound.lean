module
public import CutoffRigidity.RelativeLpDistance
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! # Actual entropy control by every relative Lᵖ distance above one

The elementary logarithm/power comparison is integrated against the actual
RN density. Infinite and singular branches are kept in the extended reals.
-/
public section
namespace CutoffRigidity
open MeasureTheory InformationTheory Filter
open scoped Topology ENNReal NNReal

theorem klFun_le_rpow_add_one {r p : ℝ} (hr : 0 ≤ r) (hp : 1 < p) :
    klFun r ≤ (1/(p-1))*r^p+1 := by
  have hlog := Real.log_le_rpow_div hr (sub_pos.mpr hp)
  have hm := mul_le_mul_of_nonneg_left hlog hr
  by_cases hz : r = 0
  · subst r
    simp [klFun,Real.zero_rpow (zero_lt_one.trans hp).ne']
  have hrp : 0 < r := lt_of_le_of_ne hr (Ne.symm hz)
  have he : r*r^(p-1) = r^p := by
    calc
      _ = r^(1:ℝ)*r^(p-1) := by rw [Real.rpow_one]
      _ = r^(1+(p-1)) := (Real.rpow_add hrp _ _).symm
      _ = r^p := by congr 1; ring
  unfold klFun
  rw [← mul_div_assoc,he] at hm
  have hm' : r*Real.log r ≤ (1/(p-1))*r^p := by
    convert! hm using 1 <;> ring
  linarith

/-- Genuine entropy bound in terms of the actual density Lᵖ seminorm. -/
theorem klDiv_le_rnDeriv_eLpNorm_rpow
    {α : Type*} [MeasurableSpace α] (ν μ : Measure α)
    [IsProbabilityMeasure ν] [IsProbabilityMeasure μ] (hAC : ν ≪ μ)
    {p : ℝ} (hp : 1 < p) :
    klDiv ν μ ≤ ENNReal.ofReal (1/(p-1)) *
      eLpNorm (fun x => (ν.rnDeriv μ x).toReal) (ENNReal.ofReal p) μ ^ p + 1 := by
  let r := fun x => (ν.rnDeriv μ x).toReal
  have hp0 : 0 < p := zero_lt_one.trans hp
  have hm : Measurable r := (Measure.measurable_rnDeriv ν μ).ennreal_toReal
  have hPower : (∫⁻ x,ENNReal.ofReal (r x^p) ∂μ) =
      eLpNorm r (ENNReal.ofReal p) μ ^ p := by
    have he (x : α) : ENNReal.ofReal (r x^p) = ‖r x‖ₑ^p := by
      rw [← ENNReal.ofReal_rpow_of_nonneg (show 0 ≤ r x from ENNReal.toReal_nonneg) hp0.le,
        Real.enorm_eq_ofReal_abs,abs_of_nonneg (show 0 ≤ r x from ENNReal.toReal_nonneg)]
    simp_rw [he]
    rw [lintegral_rpow_enorm_eq_rpow_eLpNorm' hp0,
      eLpNorm_eq_eLpNorm' (ENNReal.ofReal_ne_zero_iff.mpr hp0) ENNReal.ofReal_ne_top hm.aestronglyMeasurable,
      ENNReal.toReal_ofReal hp0.le]
  rw [klDiv_eq_lintegral_klFun_of_ac hAC]
  calc
    _ ≤ ∫⁻ x,ENNReal.ofReal ((1/(p-1))*r x^p+1) ∂μ :=
      lintegral_mono (fun x => ENNReal.ofReal_le_ofReal (klFun_le_rpow_add_one ENNReal.toReal_nonneg hp))
    _ = ENNReal.ofReal (1/(p-1))*(∫⁻ x,ENNReal.ofReal (r x^p) ∂μ)+1 := by
      simp_rw [ENNReal.ofReal_add (by positivity : (0:ℝ) ≤ 1/(p-1)*r _^p) zero_le_one,
        ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ 1/(p-1)),ENNReal.ofReal_one]
      rw [lintegral_add_right _ measurable_const,lintegral_const_mul _ (hm.pow_const p).ennreal_ofReal]
      simp
    _ = _ := by rw [hPower]

/-- Every actual relative Lᵖ distance with p>1 controls entropy. This
includes singular laws and infinite seminorms, with no moment premise. -/
theorem klDiv_le_relativeLpDistance_rpow_add
    {α : Type*} [MeasurableSpace α] (ν μ : Measure α)
    [IsProbabilityMeasure ν] [IsProbabilityMeasure μ] {p : ℝ} (hp : 1 < p) :
    klDiv ν μ ≤ ENNReal.ofReal (1/(p-1)) *
      (relativeLpDistance ν μ (ENNReal.ofReal p)+1)^p + 1 := by
  have hp0 : 0 < p := zero_lt_one.trans hp
  have hC : ENNReal.ofReal (1/(p-1)) ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr (by positivity)
  by_cases hAC : ν ≪ μ
  · apply (klDiv_le_rnDeriv_eLpNorm_rpow ν μ hAC hp).trans
    apply add_le_add _ le_rfl
    apply mul_le_mul' le_rfl
    apply ENNReal.rpow_le_rpow _ hp0.le
    let r := fun x => (ν.rnDeriv μ x).toReal
    have he : r = (fun x => r x-1)+(fun _ => (1:ℝ)) := by funext x; simp
    rw [relativeLpDistance_eq_eLpNorm ν μ hAC]
    change eLpNorm r (ENNReal.ofReal p) μ ≤ _
    calc
      _ = eLpNorm ((fun x => r x-1)+(fun _ => (1:ℝ))) (ENNReal.ofReal p) μ := by rw [← he]
      _ ≤ eLpNorm (fun x => r x-1) (ENNReal.ofReal p) μ+
          eLpNorm (fun _ : α => (1:ℝ)) (ENNReal.ofReal p) μ :=
        eLpNorm_add_le (by simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hp.le)
      _ = _ := by
        rw [eLpNorm_const' _ (ENNReal.ofReal_ne_zero_iff.mpr hp0) ENNReal.ofReal_ne_top]
        simp only [enorm_one,measure_univ,ENNReal.one_rpow,mul_one,add_right_inj]
        rfl
  · simp only [relativeLpDistance,hAC,↓reduceIte,top_add,
      ENNReal.top_rpow_of_pos hp0,ENNReal.mul_top hC,le_top]

end CutoffRigidity
