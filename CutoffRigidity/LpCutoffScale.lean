module
public import CutoffRigidity.SublogarithmicRates

/-! # The genuine Harnack chi-square exponent at the cutoff scale -/
public section
namespace CutoffRigidity
open Filter Topology

/-- The factor involving the curvature in power-two Harnack is absorbed
by exactly the same fixed-time shift used in the written information proof. -/
theorem chiSquare_exponent_tendsto_zero
    (rate : ℕ → ℝ) (hRate : ∀ n, 0 < rate n) (c : ℝ)
    {ε : ℝ} (hε : 0 < ε)
    (hsub : Tendsto (fun n : ℕ => rate n / Real.log (n : ℝ)) atTop (𝓝 0)) :
    Tendsto (fun n : ℕ =>
      rate n / (Real.exp (2 * rate n * ((1+ε)*criticalTime n (rate n))) - 1) *
        ((c^2 + (rate n)⁻¹) * n)) atTop (𝓝 0) := by
  have hlim := (shifted_dimension_decay_tendsto_zero (Eventually.of_forall hRate)
    hε (by norm_num : (0:ℝ) ≤ 1) hsub).const_mul (2*(c^2+1))
  simp only [mul_zero] at hlim
  apply squeeze_zero' _ _ hlim
  · filter_upwards [eventually_ge_atTop 2] with n hn
    have hr := hRate n
    have hlog : 0 < Real.log (n:ℝ) := Real.log_pos (by exact_mod_cast (show 1<n by omega))
    have ht : 0 < (1+ε)*criticalTime n (rate n) := by unfold criticalTime; positivity
    exact mul_nonneg (div_nonneg (hRate n).le
      (sub_nonneg.mpr (Real.one_le_exp_iff.mpr (by positivity)))) (by positivity)
  · filter_upwards [eventually_ge_atTop 2] with n hn
    have hr := hRate n
    have hnreal : (2:ℝ) ≤ n := by exact_mod_cast hn
    have hnp : (0:ℝ) < n := by positivity
    have hlog : 0 ≤ Real.log (n:ℝ) := Real.log_nonneg (by linarith)
    let t := (1+ε)*criticalTime n (rate n)
    have he : 2*rate n*t = (1+ε)*Real.log (n:ℝ) := by
      dsimp only [t,criticalTime]
      field_simp [ne_of_gt (hRate n)]
    have hE : (2:ℝ) ≤ Real.exp (2*rate n*t) := by
      calc
        _ ≤ (n:ℝ) := hnreal
        _ = Real.exp (Real.log (n:ℝ)) := (Real.exp_log hnp).symm
        _ ≤ _ := Real.exp_le_exp.mpr (by rw [he]; nlinarith)
    have hDen : 0 < Real.exp (2*rate n*t)-1 := by linarith
    have hrExp : rate n ≤ Real.exp (2*rate n) := by
      have hh := Real.add_one_le_exp (2*rate n)
      linarith [hRate n]
    have hExpOne : 1 ≤ Real.exp (2*rate n) := Real.one_le_exp_iff.mpr (by positivity)
    have hcoeff : c^2*rate n+1 ≤ (c^2+1)*Real.exp (2*rate n) := by
      nlinarith [mul_le_mul_of_nonneg_left hrExp (sq_nonneg c)]
    have hId : rate n*((c^2+(rate n)⁻¹)*(n:ℝ)) = (c^2*rate n+1)*n := by
      field_simp [ne_of_gt (hRate n)]
    change rate n / (Real.exp (2*rate n*t)-1)*((c^2+(rate n)⁻¹)*n) ≤ _
    calc
      _ = ((c^2*rate n+1)*n)/(Real.exp (2*rate n*t)-1) := by rw [div_mul_eq_mul_div,hId]
      _ ≤ 2*((c^2*rate n+1)*n)/Real.exp (2*rate n*t) := by
        apply (div_le_div_iff₀ hDen (Real.exp_pos _)).mpr
        nlinarith [mul_nonneg (by positivity : 0 ≤ (c^2*rate n+1)*(n:ℝ)) (by linarith : 0 ≤ Real.exp (2*rate n*t)-2)]
      _ ≤ 2*(((c^2+1)*Real.exp (2*rate n))*n)/Real.exp (2*rate n*t) := by gcongr
      _ = 2*(c^2+1)*((n:ℝ)*Real.exp (-2*rate n*(t-1))) := by
        rw [div_eq_mul_inv, ← Real.exp_neg, ← mul_assoc]
        have hex : Real.exp (2*rate n)*Real.exp (-(2*rate n*t)) = Real.exp (-2*rate n*(t-1)) := by
          rw [← Real.exp_add]; congr 1; ring
        calc
          _ = 2*(c^2+1)*(n:ℝ)*(Real.exp (2*rate n)*Real.exp (-(2*rate n*t))) := by ring
          _ = _ := by rw [hex]; ring

end CutoffRigidity
