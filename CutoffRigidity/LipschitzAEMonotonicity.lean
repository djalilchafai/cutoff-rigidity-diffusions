module
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun

/-! # The genuine absolutely-continuous monotonicity step -/
public section
namespace CutoffRigidity
open MeasureTheory Set
open scoped NNReal

theorem lipschitzOnWith_le_left_of_deriv_nonpos_ae
    {F : ℝ → ℝ} {a b : ℝ} {C : ℝ≥0} (hab : a ≤ b)
    (hLip : LipschitzOnWith C F (uIcc a b))
    (hd : ∀ᵐ t ∂volume.restrict (Ioc a b), deriv F t ≤ 0) : F b ≤ F a := by
  have hFTC := hLip.absolutelyContinuousOnInterval.integral_deriv_eq_sub
  have hInt : (∫ t in a..b, deriv F t) ≤ 0 := by
    rw [intervalIntegral.integral_of_le hab]
    exact integral_nonpos_of_ae hd
  rw [hFTC] at hInt
  linarith

theorem absolutelyContinuousOnInterval_le_left_of_deriv_nonpos_ae
    {F : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hAC : AbsolutelyContinuousOnInterval F a b)
    (hd : ∀ᵐ t ∂volume.restrict (Ioc a b), deriv F t ≤ 0) : F b ≤ F a := by
  have hFTC := hAC.integral_deriv_eq_sub
  have hInt : (∫ t in a..b, deriv F t) ≤ 0 := by
    rw [intervalIntegral.integral_of_le hab]
    exact integral_nonpos_of_ae hd
  rw [hFTC] at hInt
  linarith

end CutoffRigidity
