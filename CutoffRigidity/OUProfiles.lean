module

public import CutoffRigidity.Asymptotics
public import Mathlib.Analysis.Real.Sqrt

/-!
# Scalar Ornstein–Uhlenbeck profiles

The expressions below are the Gaussian squared Wasserstein and Fisher formulas
for rate equal to dimension and initial point of norm `sqrt dimension`.
Their identification with probability distances is not formalized here.
-/

public section

open Filter Topology

namespace CutoffRigidity

/-- Scalar candidate for the squared Wasserstein distance. -/
@[expose] noncomputable def ouW2Squared (d q : ℝ) : ℝ :=
  d * q + (1 - Real.sqrt (1 - q)) ^ 2

/-- Scalar candidate for relative Fisher information. -/
@[expose] noncomputable def ouFisher (d q : ℝ) : ℝ :=
  d ^ 2 * q ^ 2 / (1 - q) + d ^ 3 * q

/-- Elementary bound for the Gaussian variance correction. -/
theorem gaussian_variance_correction_le {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    (1 - Real.sqrt (1 - q)) ^ 2 ≤ q := by
  have hs := Real.sq_sqrt (show 0 ≤ 1 - q by linarith)
  have hsn := Real.sqrt_nonneg (1 - q)
  have hsu : Real.sqrt (1 - q) ≤ 1 := by
    apply (Real.sqrt_le_left (by norm_num : (0 : ℝ) ≤ 1)).2
    nlinarith
  nlinarith

/-- Positivity and a simple upper bound for the scalar squared-distance profile. -/
theorem ouW2Squared_bounds {d q : ℝ} (hd : 0 ≤ d) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    0 ≤ ouW2Squared d q ∧ ouW2Squared d q ≤ (d + 1) * q := by
  have hcor := gaussian_variance_correction_le hq0 hq1
  unfold ouW2Squared
  constructor
  · positivity
  · nlinarith

/-- The scalar Fisher profile is at least its squared-mean contribution. -/
theorem ouFisher_lower {d q : ℝ} (_hd : 0 ≤ d) (_hq0 : 0 ≤ q) (hq1 : q < 1) :
    d ^ 3 * q ≤ ouFisher d q := by
  unfold ouFisher
  have : 0 ≤ d ^ 2 * q ^ 2 / (1 - q) := by positivity
  linarith

/-- The scalar W2 profile vanishes at `q = d^(-3/2)`. -/
theorem ouW2Squared_three_quarters :
    Tendsto (fun n : ℕ => ouW2Squared n ((n : ℝ) ^ (-(3 / 2 : ℝ)) ))
      atTop (𝓝 0) := by
  apply upper_bound_transfer (C := 2) (ε := 1 / 2) (by norm_num)
  · filter_upwards [eventually_ge_atTop 1] with n hn
    exact (ouW2Squared_bounds (by positivity) (Real.rpow_nonneg (by positivity) _)
      (Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hn) (by norm_num))).1
  · filter_upwards [eventually_ge_atTop 1] with n hn
    have hd : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hp : (0 : ℝ) < n := by linarith
    have hq : (n : ℝ) ^ (-(3 / 2 : ℝ)) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hd (by norm_num)
    have hb := (ouW2Squared_bounds hp.le (Real.rpow_nonneg hp.le _) hq).2
    have heq : (n : ℝ) * (n : ℝ) ^ (-(3 / 2 : ℝ)) = (n : ℝ) ^ (-(1 / 2 : ℝ)) := by
      nth_rw 1 [← Real.rpow_one (n : ℝ)]
      rw [← Real.rpow_add hp]
      norm_num
    calc
      _ ≤ ((n : ℝ) + 1) * (n : ℝ) ^ (-(3 / 2 : ℝ)) := hb
      _ ≤ (2 * (n : ℝ)) * (n : ℝ) ^ (-(3 / 2 : ℝ)) := by gcongr; linarith
      _ = 2 * (n : ℝ) ^ (-(1 / 2 : ℝ)) := by rw [mul_assoc, heq]

/-- The scalar Fisher profile diverges at `q = d^(-5/2)`. -/
theorem ouFisher_five_quarters :
    Tendsto (fun n : ℕ => ouFisher n ((n : ℝ) ^ (-(5 / 2 : ℝ))))
      atTop atTop := by
  apply lower_bound_transfer (c := 1) (ε := 1 / 2) (by norm_num) (by norm_num)
  filter_upwards [eventually_ge_atTop 2] with n hn
  have hd : (1 : ℝ) < n := by exact_mod_cast (show 1 < n by omega)
  have hq : (n : ℝ) ^ (-(5 / 2 : ℝ)) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg hd (by norm_num)
  have hb := ouFisher_lower (by positivity : (0 : ℝ) ≤ n)
    (Real.rpow_nonneg (by positivity : (0 : ℝ) ≤ n) _) hq
  have heq : (n : ℝ) ^ 3 * (n : ℝ) ^ (-(5 / 2 : ℝ)) = (n : ℝ) ^ (1 / 2 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add (by linarith : (0 : ℝ) < n)]
    norm_num
  simpa only [heq, one_mul] using hb

end CutoffRigidity
