module
public import CutoffRigidity.LangevinPositivePowerPairing
public import CutoffRigidity.PositivePowerLogSobolev

/-! # The genuine variable-exponent power curve in Gross's proof -/
public section
namespace CutoffRigidity
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

@[expose] noncomputable def grossExponent (ρ t : ℝ) : ℝ := 1+Real.exp (2*ρ*t)

theorem hasDerivAt_grossExponent (ρ t : ℝ) :
    HasDerivAt (grossExponent ρ) (2*ρ*(grossExponent ρ t-1)) t := by
  have hh := (((hasDerivAt_id t).const_mul (2*ρ)).exp).const_add 1
  convert hh using 1
  · funext s; simp only [grossExponent,id_eq]
  · simp only [grossExponent,id_eq]; ring

/-- Actual differentiation of a positive base with a moving real power. -/
theorem hasDerivAt_positive_rpow_variable
    {q p : ℝ → ℝ} {t D J : ℝ} (hpos : ∀ r,0 < q r)
    (hq : HasDerivAt q D t) (hp : HasDerivAt p J t) :
    HasDerivAt (fun r => q r^p r)
      (q t^p t*(J*Real.log (q t)+p t*D/q t)) t := by
  have hh := (hp.mul (hq.log (hpos t).ne')).exp
  have he (r : ℝ) : q r^p r = Real.exp (p r*Real.log (q r)) := by
    rw [Real.rpow_def_of_pos (hpos r)]
    congr 1
    ring
  convert hh using 1
  · exact funext he
  · rw [he]
    simp only [Pi.mul_apply]
    ring

/-- Uniform bounds on a positive base and on a nonnegative exponent give
an actual integrable constant bound for its true real power. -/
theorem positive_rpow_uniform_bound {q m M p P : ℝ}
    (hm : 0 < m) (hlo : m ≤ q) (hup : q ≤ M) (hp : 0 ≤ p) (hpP : p ≤ P) :
    ‖q^p‖ ≤ (1+M)^P := by
  have hq : 0 < q := hm.trans_le hlo
  have hM : 0 < M := hq.trans_le hup
  rw [Real.norm_of_nonneg (Real.rpow_nonneg hq.le _)]
  exact (Real.rpow_le_rpow hq.le (by linarith : q ≤ 1+M) hp).trans
    (Real.rpow_le_rpow_of_exponent_le (by linarith : 1 ≤ 1+M) hpP)

/-- The actual variable-power derivative has a derived constant bound on
each bounded positive rectangle, providing genuine dominated differentiation. -/
theorem norm_positive_rpow_variable_derivative_le {q D m M N p P J K C : ℝ}
    (hm : 0 < m) (hlo : m ≤ q) (hup : q ≤ M)
    (hN : ‖D‖ ≤ N) (hp : 0 ≤ p) (hpP : p ≤ P)
    (hJ : ‖J‖ ≤ K) (hLog : ‖Real.log q‖ ≤ C) :
    ‖q^p*(J*Real.log q+p*D/q)‖ ≤ (1+M)^P*(K*C+P*(N/m)) := by
  have hq : 0 < q := hm.trans_le hlo
  have hM : 0 < M := hq.trans_le hup
  have hN0 : 0 ≤ N := (norm_nonneg _).trans hN
  have hK0 : 0 ≤ K := (norm_nonneg _).trans hJ
  have hC0 : 0 ≤ C := (norm_nonneg _).trans hLog
  have hP0 : 0 ≤ P := hp.trans hpP
  have hDiv : ‖D/q‖ ≤ N/m := by
    rw [norm_div,Real.norm_of_nonneg hq.le]
    exact (div_le_div_of_nonneg_right hN hq.le).trans (div_le_div_of_nonneg_left hN0 hm hlo)
  rw [norm_mul]
  apply mul_le_mul (positive_rpow_uniform_bound hm hlo hup hp hpP) _ (norm_nonneg _) (by positivity)
  calc
    _ ≤ ‖J*Real.log q‖+‖p*D/q‖ := norm_add_le _ _
    _ = ‖J‖*‖Real.log q‖+p*‖D/q‖ := by
      rw [norm_mul,show p*D/q = p*(D/q) by ring,norm_mul,Real.norm_of_nonneg hp]
    _ ≤ K*C+P*(N/m) := add_le_add (mul_le_mul hJ hLog (norm_nonneg _) hK0)
      (mul_le_mul hpP hDiv (norm_nonneg _) hP0)

end CutoffRigidity
