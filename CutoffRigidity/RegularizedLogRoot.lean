module
public import CutoffRigidity.PoincareIntegrableDomain
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-! # The actual regularized logarithmic RN-root test

The scalar chain bounds give the exact factor four in Fisher information.
These are the regularizations used to justify the written local Poincare
application, including its integrability and limit at positive density.
-/
public section
namespace CutoffRigidity
open Filter
open scoped Topology

@[expose] noncomputable def regularizedLogRoot (ε r : ℝ) : ℝ :=
  Real.log (ε+r^2)-Real.log ε

theorem regularizedLogRoot_zero (ε : ℝ) : regularizedLogRoot ε 0=0 := by
  simp [regularizedLogRoot]

theorem contDiff_regularizedLogRoot {ε : ℝ} (hε : 0 < ε) :
    ContDiff ℝ 2 (regularizedLogRoot ε) := by
  have hh : ContDiff ℝ 2 (fun r : ℝ => ε+r^2) := contDiff_const.add (contDiff_id.pow 2)
  exact (hh.log (fun r => ne_of_gt (by positivity))).sub contDiff_const

theorem hasDerivAt_regularizedLogRoot {ε : ℝ} (hε : 0 < ε) (r : ℝ) :
    HasDerivAt (regularizedLogRoot ε) (2*r/(ε+r^2)) r := by
  have hh := (((hasDerivAt_const r ε).add ((hasDerivAt_id r).pow 2)).log (by positivity : ε+r^2 ≠ 0)).sub_const (Real.log ε)
  convert! hh using 1
  norm_num

theorem deriv_regularizedLogRoot {ε : ℝ} (hε : 0 < ε) (r : ℝ) :
    deriv (regularizedLogRoot ε) r=2*r/(ε+r^2) := (hasDerivAt_regularizedLogRoot hε r).deriv

theorem deriv_regularizedLogRoot_abs_bound {ε : ℝ} (hε : 0 < ε) (r : ℝ) :
    |deriv (regularizedLogRoot ε) r| ≤ (1+ε)/ε := by
  rw [deriv_regularizedLogRoot hε,abs_div,abs_of_pos (by positivity : 0 < ε+r^2),abs_mul,
    abs_of_pos (by norm_num : (0:ℝ)<2)]
  apply (div_le_div_iff₀ (by positivity : 0 < ε+r^2) hε).mpr
  nlinarith [sq_nonneg (|r|-1),sq_abs r,sq_nonneg ε,mul_nonneg hε.le (sq_nonneg r)]

theorem regularizedLogRoot_score_bound {ε : ℝ} (hε : 0 < ε) (r : ℝ) :
    r^2*(deriv (regularizedLogRoot ε) r)^2 ≤ 4 := by
  have hh : |r| *|deriv (regularizedLogRoot ε) r| ≤ 2 := by
    rw [deriv_regularizedLogRoot hε,abs_div,abs_of_pos (by positivity : 0 < ε+r^2),abs_mul,
      abs_of_pos (by norm_num : (0:ℝ)<2),← mul_div_assoc]
    apply (div_le_iff₀ (by positivity : 0 < ε+r^2)).mpr
    nlinarith [sq_abs r]
  have hs := pow_le_pow_left₀ (mul_nonneg (abs_nonneg r) (abs_nonneg _)) hh 2
  simpa only [mul_pow,sq_abs,show (2 : ℝ)^2=4 by norm_num] using hs

/-- A uniform logarithmic domination, valid also at small positive RN density. -/
theorem abs_log_add_sq_le {ε r : ℝ} (hε : 0 < ε) (hr : r ≠ 0) :
    |Real.log (ε+r^2)| ≤ |Real.log (r^2)|+Real.log (ε+1) := by
  have hr2 : 0 < r^2 := sq_pos_of_ne_zero hr
  have hlog0 : 0 ≤ Real.log (ε+1) := Real.log_nonneg (by linarith)
  have hlower := Real.log_le_log hr2 (by linarith : r^2 ≤ ε+r^2)
  have hupper : Real.log (ε+r^2) ≤ |Real.log (r^2)|+Real.log (ε+1) := by
    by_cases hs : r^2 ≤ 1
    · have hh := Real.log_le_log (by positivity : 0 < ε+r^2) (by linarith : ε+r^2 ≤ ε+1)
      linarith [abs_nonneg (Real.log (r^2))]
    · have hs' : 1 ≤ r^2 := (lt_of_not_ge hs).le
      have hh := Real.log_le_log (by positivity : 0 < ε+r^2)
        (by nlinarith : ε+r^2 ≤ (ε+1)*r^2)
      rw [Real.log_mul (by positivity : ε+1 ≠ 0) hr2.ne'] at hh
      linarith [le_abs_self (Real.log (r^2))]
  rw [abs_le]
  exact ⟨by linarith [neg_abs_le (Real.log (r^2))],hupper⟩

theorem abs_regularizedLogRoot_le {ε r : ℝ} (hε : 0 < ε) (hr : r ≠ 0) :
    |regularizedLogRoot ε r| ≤ |Real.log (r^2)|+Real.log (ε+1)+|Real.log ε| := by
  exact (abs_sub _ _).trans (add_le_add (abs_log_add_sq_le hε hr) (le_refl _))

end CutoffRigidity
