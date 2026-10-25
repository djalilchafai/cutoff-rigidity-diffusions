module
public import Mathlib.InformationTheory.KullbackLeibler.Basic

/-! # Scalar variational witnesses for the genuine KL integrand -/
public section
namespace CutoffRigidity
open InformationTheory Filter Set
open scoped Topology

/-- The actual exponential Young inequality for the KL integrand. -/
theorem klFun_exponential_young {r : ℝ} (hr : 0 ≤ r) (s : ℝ) :
    r * s - Real.exp s + 1 ≤ klFun r := by
  rcases eq_or_lt_of_le hr with hz | hp
  · rw [← hz, klFun_zero]
    nlinarith [Real.exp_nonneg s]
  · have hh := mul_le_mul_of_nonneg_left (Real.add_one_le_exp (s - Real.log r)) hp.le
    have heq : r * Real.exp (s - Real.log r) = Real.exp s := by
      rw [Real.exp_sub, Real.exp_log hp]
      field_simp
    rw [heq] at hh
    unfold klFun
    nlinarith

private theorem exponential_test_nonneg_of_sign {r s : ℝ}
    (hs : 0 ≤ s * (r - Real.exp s)) : 0 ≤ r * s - Real.exp s + 1 := by
  have hh := mul_le_mul_of_nonneg_right (Real.add_one_le_exp (-s)) (Real.exp_nonneg s)
  have heq : Real.exp (-s) * Real.exp s = 1 := by rw [← Real.exp_add]; simp
  rw [heq] at hh
  nlinarith

/-- A bounded actual measurable log-density witness; at a zero density
its value decreases to minus infinity rather than using `log 0 = 0`. -/
@[expose] noncomputable def klLogWitness (n : ℕ) (r : ℝ) : ℝ :=
  if r ≤ 0 then -(n : ℝ) else max (-(n : ℝ)) (min (n : ℝ) (Real.log r))

theorem measurable_klLogWitness (n : ℕ) : Measurable (klLogWitness n) := by
  unfold klLogWitness
  exact Measurable.ite measurableSet_Iic measurable_const
    (measurable_const.max (measurable_const.min Real.measurable_log))

theorem abs_klLogWitness_le (n : ℕ) (r : ℝ) : |klLogWitness n r| ≤ n := by
  by_cases hr : r ≤ 0
  · simp only [klLogWitness, hr, ite_true, abs_neg, abs_of_nonneg (Nat.cast_nonneg (α := ℝ) n), le_refl]
  · rw [klLogWitness, ite_eq_right hr, abs_le]
    constructor
    · exact le_max_left _ _
    · exact max_le (by linarith [Nat.cast_nonneg (α := ℝ) n]) (min_le_left _ _)

/-- The actual clipped log witnesses have nonnegative variational
integrands, allowing genuine nonnegative Fatou without domination. -/
theorem klLogWitness_integrand_nonneg (n : ℕ) {r : ℝ} (hr : 0 ≤ r) :
    0 ≤ r * klLogWitness n r - Real.exp (klLogWitness n r) + 1 := by
  by_cases hz : r = 0
  · rw [hz, klLogWitness, ite_eq_left (by simp)]
    apply exponential_test_nonneg_of_sign
    exact mul_nonneg_of_nonpos_of_nonpos (by linarith [Nat.cast_nonneg (α := ℝ) n]) (by linarith [Real.exp_nonneg (-(n : ℝ))])
  · have hp : 0 < r := lt_of_le_of_ne hr (Ne.symm hz)
    rw [klLogWitness, ite_eq_right hp.not_ge]
    by_cases hlo : Real.log r ≤ -(n : ℝ)
    · rw [min_eq_right (hlo.trans (by linarith [Nat.cast_nonneg (α := ℝ) n])), max_eq_left hlo]
      apply exponential_test_nonneg_of_sign
      have he : r ≤ Real.exp (-(n : ℝ)) := (Real.log_le_iff_le_exp hp).mp hlo
      exact mul_nonneg_of_nonpos_of_nonpos (by linarith [Nat.cast_nonneg (α := ℝ) n]) (by linarith)
    · by_cases hhi : (n : ℝ) ≤ Real.log r
      · rw [min_eq_left hhi, max_eq_right (by linarith [Nat.cast_nonneg (α := ℝ) n])]
        apply exponential_test_nonneg_of_sign
        have he : Real.exp (n : ℝ) ≤ r := (Real.le_log_iff_exp_le hp).mp hhi
        exact mul_nonneg (Nat.cast_nonneg n) (by linarith)
      · rw [min_eq_right (le_of_not_ge hhi), max_eq_right (le_of_not_ge hlo), Real.exp_log hp]
        convert! klFun_nonneg hr using 1
        unfold klFun
        ring

/-- These actual bounded witnesses recover the genuine KL integrand,
including at zero density. -/
theorem tendsto_klLogWitness_integrand {r : ℝ} (hr : 0 ≤ r) :
    Tendsto (fun n : ℕ => r * klLogWitness n r - Real.exp (klLogWitness n r) + 1)
      atTop (𝓝 (klFun r)) := by
  by_cases hz : r = 0
  · subst r
    have hh := Real.tendsto_exp_neg_atTop_nhds_zero.comp tendsto_natCast_atTop_atTop
    have hlim := ((tendsto_const_nhds (x := (0 : ℝ))).sub hh).add_const 1
    simpa only [klLogWitness, le_refl, ite_true, zero_mul, zero_sub, neg_zero, zero_add, klFun_zero, Function.comp_def] using hlim
  · have hp : 0 < r := lt_of_le_of_ne hr (Ne.symm hz)
    apply tendsto_const_nhds.congr'
    filter_upwards [tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop |Real.log r|)] with n hn
    have h1 : Real.log r ≤ (n : ℝ) := (le_abs_self _).trans hn
    have h2 : -(n : ℝ) ≤ Real.log r := by have hh := neg_abs_le (Real.log r); linarith
    rw [klLogWitness, ite_eq_right hp.not_ge, min_eq_right h1, max_eq_right h2, Real.exp_log hp]
    unfold klFun
    ring

end CutoffRigidity
