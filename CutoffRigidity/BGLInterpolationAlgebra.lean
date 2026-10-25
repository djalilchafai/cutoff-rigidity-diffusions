module
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.InnerProductSpace.Basic

/-! # The scalar optimization in the cited BGL interpolation proof

Young's inequality and the exponentially parametrized line segment give
the exact action integral used by the entropy-cost regularization argument.
-/
public section
namespace CutoffRigidity
open MeasureTheory Set

theorem bgl_young_bound {a b : ℝ} (ha : 0 ≤ a) : -a + b * Real.sqrt a ≤ b ^ 2 / 4 := by
  have hs := sq_nonneg (Real.sqrt a - b / 2)
  have he := Real.sq_sqrt ha
  nlinarith

theorem bgl_gradient_young_bound
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (v z : E) (a K : ℝ) (ha : 0 ≤ a) (hK : 0 ≤ K)
    (hv : ‖v‖ ^ 2 ≤ K ^ 2 * a) :
    -a + inner ℝ v z ≤ K ^ 2 * ‖z‖ ^ 2 / 4 := by
  have hn : ‖v‖ ≤ K * Real.sqrt a := by
    apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hK (Real.sqrt_nonneg _))).mp
    simpa only [mul_pow, Real.sq_sqrt ha] using hv
  have hinner : inner ℝ v z ≤ (K * ‖z‖) * Real.sqrt a :=
    (real_inner_le_norm _ _).trans ((mul_le_mul_of_nonneg_right hn (norm_nonneg _)).trans_eq (by ring))
  have hy := bgl_young_bound (b := K * ‖z‖) ha
  nlinarith

theorem hasDerivAt_bgl_path_parameter (ρ T s : ℝ) :
    HasDerivAt (fun r : ℝ => (Real.exp (2 * ρ * r) - 1) / (Real.exp (2 * ρ * T) - 1))
      (2 * ρ * Real.exp (2 * ρ * s) / (Real.exp (2 * ρ * T) - 1)) s := by
  have hd := ((((hasDerivAt_id s).const_mul (2 * ρ)).exp).sub_const 1).div_const
    (Real.exp (2 * ρ * T) - 1)
  simp only [id_eq, mul_one] at hd
  convert! hd using 1 <;> ring

theorem bgl_optimal_path_energy (ρ T : ℝ) (hρ : 0 < ρ) (hT : 0 < T) :
    (∫ s in (0 : ℝ)..T,
      (2 * ρ * Real.exp (2 * ρ * s) / (Real.exp (2 * ρ * T) - 1)) ^ 2 *
        Real.exp (-2 * ρ * s) / 4) = ρ / (2 * (Real.exp (2 * ρ * T) - 1)) := by
  let D := Real.exp (2 * ρ * T) - 1
  have hD : D ≠ 0 := ne_of_gt (sub_pos.mpr (Real.one_lt_exp_iff.mpr (by positivity)))
  let A := fun s : ℝ => ρ * Real.exp (2 * ρ * s) / (2 * D ^ 2)
  let F := fun s : ℝ =>
    (2 * ρ * Real.exp (2 * ρ * s) / D) ^ 2 * Real.exp (-2 * ρ * s) / 4
  have hd (s : ℝ) : HasDerivAt A (F s) s := by
    have hh := (((hasDerivAt_id s).const_mul (2 * ρ)).exp.const_mul ρ).div_const (2 * D ^ 2)
    simp only [id_eq, mul_one] at hh
    convert! hh using 1
    dsimp only [F]
    have he : Real.exp (2 * ρ * s) * Real.exp (-2 * ρ * s) = 1 := by
      rw [← Real.exp_add]
      convert! Real.exp_zero using 1 <;> ring
    rw [show -2 * ρ * s = -(2 * ρ * s) by ring] at he
    field_simp
    nlinarith [congrArg (fun z : ℝ => z * Real.exp (2 * ρ * s)) he]
  have hc : Continuous F := by dsimp [F]; fun_prop
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hd s)
    (hc.intervalIntegrable 0 T)
  change (∫ s in (0 : ℝ)..T, F s) = _
  rw [hi]
  dsimp [A, D]
  simp only [mul_zero, Real.exp_zero]
  field_simp [show Real.exp (2 * ρ * T) - 1 ≠ 0 from hD]

end CutoffRigidity
