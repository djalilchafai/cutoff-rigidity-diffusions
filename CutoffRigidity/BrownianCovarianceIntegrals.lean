module

public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Tactic

/-!
# Integrating the Brownian covariance kernel

These are the actual interval integrals of `min(s,t)` with the exponential
weights in the continuous-noise linear Langevin response. They supply the
variance calculation in the proof of the Mehler law.
-/

public section

open MeasureTheory Set

namespace CutoffRigidity

theorem integral_exp_mul_real (ρ a b : ℝ) (hρ : ρ ≠ 0) :
    (∫ u in a..b, Real.exp (ρ * u)) = (Real.exp (ρ * b) - Real.exp (ρ * a)) / ρ := by
  rw [intervalIntegral.integral_comp_mul_left Real.exp hρ, integral_exp]
  simp only [smul_eq_mul, div_eq_mul_inv]
  ring

theorem integral_time_mul_exp (ρ T : ℝ) (hρ : ρ ≠ 0) :
    (∫ u in 0..T, u * Real.exp (ρ * u)) =
      T * Real.exp (ρ * T) / ρ - (Real.exp (ρ * T) - 1) / ρ ^ 2 := by
  let F : ℝ → ℝ := fun u => u * Real.exp (ρ * u) / ρ - Real.exp (ρ * u) / ρ ^ 2
  have hF (u : ℝ) : HasDerivAt F (u * Real.exp (ρ * u)) u := by
    have he := ((hasDerivAt_id u).const_mul ρ).exp
    have hd := (((hasDerivAt_id u).mul he).div_const ρ).sub (he.div_const (ρ ^ 2))
    convert hd using 1
    · rfl
    · dsimp
      field_simp [hρ]
      ring
  have hc : Continuous (fun u : ℝ => u * Real.exp (ρ * u)) := by fun_prop
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ => hF u)
    (hc.intervalIntegrable 0 T)
  rw [hi]
  simp only [F, mul_zero, zero_mul, zero_div, Real.exp_zero]
  ring

theorem integral_exp_mul_min (ρ s T : ℝ) (hρ : ρ ≠ 0) (hs : 0 ≤ s) (hsT : s ≤ T) :
    (∫ u in 0..T, Real.exp (ρ * u) * min s u) =
      s * Real.exp (ρ * T) / ρ - (Real.exp (ρ * s) - 1) / ρ ^ 2 := by
  have hc : Continuous (fun u => Real.exp (ρ * u) * min s u) := by fun_prop
  have hi : (∫ u in 0..s, Real.exp (ρ * u) * min s u) +
      (∫ u in s..T, Real.exp (ρ * u) * min s u) =
      ∫ u in 0..T, Real.exp (ρ * u) * min s u :=
    intervalIntegral.integral_add_adjacent_intervals
      (hc.intervalIntegrable 0 s) (hc.intervalIntegrable s T)
  have hleft : (∫ u in 0..s, Real.exp (ρ * u) * min s u) =
      ∫ u in 0..s, u * Real.exp (ρ * u) := by
    apply intervalIntegral.integral_congr
    intro u hu
    have hus : u ≤ s := hu.2.trans (le_of_eq (max_eq_right hs))
    change Real.exp (ρ * u) * min s u = u * Real.exp (ρ * u)
    rw [min_eq_right hus, mul_comm]
  have hright : (∫ u in s..T, Real.exp (ρ * u) * min s u) =
      s * ∫ u in s..T, Real.exp (ρ * u) := by
    calc
      _ = ∫ u in s..T, s * Real.exp (ρ * u) := by
        apply intervalIntegral.integral_congr
        intro u hu
        have hsu : s ≤ u := (le_of_eq (min_eq_left hsT).symm).trans hu.1
        change Real.exp (ρ * u) * min s u = s * Real.exp (ρ * u)
        rw [min_eq_left hsu, mul_comm]
      _ = _ := intervalIntegral.integral_const_mul _ _
  rw [← hi, hleft, hright, integral_time_mul_exp ρ s hρ, integral_exp_mul_real ρ s T hρ]
  field_simp
  ring

/-- The actual double integral occurring in the variance of the weighted
Brownian time integral. -/
theorem integral_exp_mul_min_double (ρ T : ℝ) (hρ : ρ ≠ 0) (hT : 0 ≤ T) :
    (∫ s in 0..T, Real.exp (ρ * s) * ∫ u in 0..T, Real.exp (ρ * u) * min s u) =
      Real.exp (ρ * T) / ρ *
          (T * Real.exp (ρ * T) / ρ - (Real.exp (ρ * T) - 1) / ρ ^ 2) -
        ((Real.exp ((2 * ρ) * T) - 1) / (2 * ρ) -
          (Real.exp (ρ * T) - 1) / ρ) / ρ ^ 2 := by
  have hfun (s : ℝ) : Real.exp (ρ * s) *
      (s * Real.exp (ρ * T) / ρ - (Real.exp (ρ * s) - 1) / ρ ^ 2) =
      (Real.exp (ρ * T) / ρ) * (s * Real.exp (ρ * s)) -
        (Real.exp ((2 * ρ) * s) - Real.exp (ρ * s)) / ρ ^ 2 := by
    have he : Real.exp ((2 * ρ) * s) = Real.exp (ρ * s) ^ 2 := by
      rw [pow_two, ← Real.exp_add]
      congr 1
      ring
    rw [he]
    ring
  have heq : (∫ s in 0..T, Real.exp (ρ * s) * ∫ u in 0..T, Real.exp (ρ * u) * min s u) =
      ∫ s in 0..T, (Real.exp (ρ * T) / ρ) * (s * Real.exp (ρ * s)) -
        (Real.exp ((2 * ρ) * s) - Real.exp (ρ * s)) / ρ ^ 2 := by
    apply intervalIntegral.integral_congr
    intro s hs
    have hs0 : 0 ≤ s := (le_of_eq (min_eq_left hT).symm).trans hs.1
    have hsT : s ≤ T := hs.2.trans (le_of_eq (max_eq_right hT))
    change Real.exp (ρ * s) * (∫ u in 0..T, Real.exp (ρ * u) * min s u) =
      (Real.exp (ρ * T) / ρ) * (s * Real.exp (ρ * s)) -
        (Real.exp ((2 * ρ) * s) - Real.exp (ρ * s)) / ρ ^ 2
    rw [integral_exp_mul_min ρ s T hρ hs0 hsT]
    exact hfun s
  rw [heq]
  have hc1 : Continuous (fun s => (Real.exp (ρ * T) / ρ) * (s * Real.exp (ρ * s))) := by fun_prop
  have hc2 : Continuous (fun s => (Real.exp ((2 * ρ) * s) - Real.exp (ρ * s)) / ρ ^ 2) := by fun_prop
  rw [intervalIntegral.integral_sub (hc1.intervalIntegrable 0 T) (hc2.intervalIntegrable 0 T),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_div,
    intervalIntegral.integral_sub
      ((by fun_prop : Continuous (fun s => Real.exp ((2 * ρ) * s))).intervalIntegrable 0 T)
      ((by fun_prop : Continuous (fun s => Real.exp (ρ * s))).intervalIntegrable 0 T),
    integral_time_mul_exp ρ T hρ, integral_exp_mul_real (2 * ρ) 0 T (mul_ne_zero (by norm_num) hρ),
    integral_exp_mul_real ρ 0 T hρ]
  simp only [mul_zero, Real.exp_zero]

/-- The actual covariance integrals reduce the linear Brownian response to
the Mehler variance, without assuming a stochastic distribution formula. -/
theorem brownian_linear_response_variance_integral
    (ρ T : ℝ) (hρ : ρ ≠ 0) (hT : 0 ≤ T) :
    T - 2 * (ρ * Real.exp (-ρ * T)) * (∫ s in 0..T, Real.exp (ρ * s) * s) +
      (ρ * Real.exp (-ρ * T)) ^ 2 *
        (∫ s in 0..T, Real.exp (ρ * s) *
          (∫ u in 0..T, Real.exp (ρ * u) * min s u)) =
      (1 - Real.exp (-2 * ρ * T)) / (2 * ρ) := by
  have hK : (∫ s in 0..T, Real.exp (ρ * s) * s) =
      T * Real.exp (ρ * T) / ρ - (Real.exp (ρ * T) - 1) / ρ ^ 2 := by
    calc
      _ = ∫ s in 0..T, s * Real.exp (ρ * s) := by
        apply intervalIntegral.integral_congr
        intro s _
        exact mul_comm _ _
      _ = _ := integral_time_mul_exp ρ T hρ
  have hdouble : Real.exp ((2 * ρ) * T) = Real.exp (ρ * T) ^ 2 := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  have hnegative : Real.exp (-ρ * T) = (Real.exp (ρ * T))⁻¹ := by
    rw [show -ρ * T = -(ρ * T) by ring, Real.exp_neg]
  have hnegative2 : Real.exp (-2 * ρ * T) = (Real.exp (ρ * T) ^ 2)⁻¹ := by
    rw [show -2 * ρ * T = -((2 * ρ) * T) by ring, Real.exp_neg, hdouble]
  rw [hK, integral_exp_mul_min_double ρ T hρ hT, hnegative, hnegative2, hdouble]
  field_simp [hρ, Real.exp_ne_zero]
  ring

end CutoffRigidity
