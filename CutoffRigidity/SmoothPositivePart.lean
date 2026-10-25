module
public import CutoffRigidity.SobolevScalarChain
public import Mathlib.Analysis.SpecialFunctions.Sqrt

/-! # Actual smooth normal contractions approximating the positive part -/
public section
namespace CutoffRigidity
open Filter Topology

@[expose] noncomputable def smoothPositivePart (ε r : ℝ) : ℝ :=
  (r + Real.sqrt (r ^ 2 + ε ^ 2) - ε) / 2

theorem smoothPositivePart_zero {ε : ℝ} (hε : 0 < ε) : smoothPositivePart ε 0 = 0 := by
  simp [smoothPositivePart, Real.sqrt_sq hε.le]

theorem contDiff_smoothPositivePart {ε : ℝ} (hε : 0 < ε) :
    ContDiff ℝ 2 (smoothPositivePart ε) := by
  unfold smoothPositivePart
  apply ContDiff.div_const
  apply ContDiff.sub _ contDiff_const
  apply contDiff_id.add
  apply ContDiff.sqrt ((contDiff_id.pow 2).add contDiff_const)
  intro r
  positivity

theorem deriv_smoothPositivePart {ε : ℝ} (hε : 0 < ε) (r : ℝ) :
    deriv (smoothPositivePart ε) r = (1 + r / Real.sqrt (r ^ 2 + ε ^ 2)) / 2 := by
  have hp : 0 < r ^ 2 + ε ^ 2 := by positivity
  have hs : Real.sqrt (r ^ 2 + ε ^ 2) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hp)
  have hds := ((((hasDerivAt_id r).pow 2).add_const (ε ^ 2)).sqrt (by simpa using ne_of_gt hp))
  have hd := (((hasDerivAt_id r).add hds).sub_const ε).div_const 2
  have hd' : HasDerivAt (smoothPositivePart ε)
      ((1 + 2 * r / (2 * Real.sqrt (r ^ 2 + ε ^ 2))) / 2) r := by
    convert hd using 1 <;> first | rfl | simp
  rw [hd'.deriv]
  field_simp

theorem abs_deriv_smoothPositivePart_le {ε : ℝ} (hε : 0 < ε) (r : ℝ) :
    |deriv (smoothPositivePart ε) r| ≤ 1 := by
  rw [deriv_smoothPositivePart hε]
  have hp : 0 < r ^ 2 + ε ^ 2 := by positivity
  have hs : 0 < Real.sqrt (r ^ 2 + ε ^ 2) := Real.sqrt_pos.mpr hp
  have hs2 := Real.sq_sqrt hp.le
  have hl : -Real.sqrt (r ^ 2 + ε ^ 2) ≤ r := by nlinarith
  have hu : r ≤ Real.sqrt (r ^ 2 + ε ^ 2) := by nlinarith
  apply abs_le.mpr
  constructor
  · have hh : -1 ≤ r / Real.sqrt (r ^ 2 + ε ^ 2) := (le_div_iff₀ hs).mpr (by simpa using hl)
    linarith
  · have hh : r / Real.sqrt (r ^ 2 + ε ^ 2) ≤ 1 := (div_le_iff₀ hs).mpr (by simpa using hu)
    linarith

@[expose] noncomputable def positivePartSlope (r : ℝ) : ℝ :=
  if r = 0 then 1 / 2 else if 0 < r then 1 else 0

theorem positivePartSlope_nonneg (r : ℝ) : 0 ≤ positivePartSlope r := by
  unfold positivePartSlope
  split_ifs <;> norm_num

theorem abs_positivePartSlope_le (r : ℝ) : |positivePartSlope r| ≤ 1 := by
  unfold positivePartSlope
  split_ifs <;> norm_num

theorem smoothPositivePart_tendsto {ε : ℕ → ℝ}
    (hε : Tendsto ε atTop (𝓝 0)) (r : ℝ) :
    Tendsto (fun n => smoothPositivePart (ε n) r) atTop (𝓝 (max r 0)) := by
  have hh : Tendsto (fun n => (r + Real.sqrt (r ^ 2 + ε n ^ 2) - ε n) / 2) atTop
      (𝓝 ((r + Real.sqrt (r ^ 2 + 0 ^ 2) - 0) / 2)) := ((tendsto_const_nhds.add
    (Real.continuous_sqrt.continuousAt.tendsto.comp (tendsto_const_nhds.add (hε.pow 2)))).sub hε).div_const 2
  have hid : (r + Real.sqrt (r ^ 2 + 0 ^ 2) - 0) / 2 = max r 0 := by
    rw [zero_pow (by norm_num : 2 ≠ 0), add_zero, Real.sqrt_sq_eq_abs, sub_zero]
    by_cases hr : 0 ≤ r
    · rw [abs_of_nonneg hr, max_eq_left hr]; ring
    · rw [abs_of_neg (lt_of_not_ge hr), max_eq_right (le_of_not_ge hr)]; ring
  rw [hid] at hh
  exact hh

theorem deriv_smoothPositivePart_tendsto {ε : ℕ → ℝ}
    (hpos : ∀ n, 0 < ε n) (hε : Tendsto ε atTop (𝓝 0)) (r : ℝ) :
    Tendsto (fun n => deriv (smoothPositivePart (ε n)) r) atTop (𝓝 (positivePartSlope r)) := by
  simp_rw [deriv_smoothPositivePart (hpos _)]
  by_cases hr : r = 0
  · subst r
    simp [positivePartSlope]
  · have hs : Real.sqrt (r ^ 2 + 0 ^ 2) ≠ 0 := by simpa only [zero_pow (by norm_num : 2 ≠ 0), add_zero, Real.sqrt_sq_eq_abs] using (abs_ne_zero.mpr hr)
    have hh : Tendsto (fun n => (1 + r / Real.sqrt (r ^ 2 + ε n ^ 2)) / 2) atTop
        (𝓝 ((1 + r / Real.sqrt (r ^ 2 + 0 ^ 2)) / 2)) := (tendsto_const_nhds.add (tendsto_const_nhds.div
      (Real.continuous_sqrt.continuousAt.tendsto.comp (tendsto_const_nhds.add (hε.pow 2))) hs)).div_const 2
    have hid : (1 + r / Real.sqrt (r ^ 2 + 0 ^ 2)) / 2 = positivePartSlope r := by
      simp only [zero_pow (by norm_num : 2 ≠ 0), add_zero, Real.sqrt_sq_eq_abs, positivePartSlope, ite_eq_right hr]
      by_cases hp : 0 < r
      · rw [ite_eq_left hp, abs_of_pos hp, div_self hr]; norm_num
      · rw [ite_eq_right hp, abs_of_neg (lt_of_le_of_ne (le_of_not_gt hp) hr)]
        field_simp
        ring
    rw [hid] at hh
    exact hh

end CutoffRigidity
