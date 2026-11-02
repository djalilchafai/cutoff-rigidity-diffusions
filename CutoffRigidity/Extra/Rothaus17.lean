module

public import Mathlib
public import CutoffRigidity.Extra.Rothaus16

/-! # Rothaus remark (stage 17): the two-point example with `C_LSI > 2 C_PI` -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology

namespace CutoffRigidity.Rothaus

namespace TwoPoint

/-- The mass `p = e^{-3}` of `true`. -/
noncomputable def p : ℝ := Real.exp (-3)

theorem p_pos : 0 < p := Real.exp_pos _
theorem p_lt_one : p < 1 := by
  have := Real.exp_lt_exp.2 (show (-3 : ℝ) < 0 by norm_num)
  simp [p]

noncomputable def μ : Measure Bool := twoPoint p

instance : IsProbabilityMeasure μ := twoPoint_prob p_pos.le p_lt_one.le

theorem real_true : μ.real {true} = p := twoPoint_real_true p_pos.le
theorem real_false : μ.real {false} = 1 - p := twoPoint_real_false p_pos.le p_lt_one.le

/-- Weights: the form is `E f = p (1-p) (f true - f false)²`. -/
noncomputable def w (x y : Bool) : ℝ := if x = y then 0 else p * (1 - p) / 2

theorem w_nonneg (x y : Bool) : 0 ≤ w x y := by
  unfold w
  split_ifs
  · exact le_rfl
  · have := p_pos; have := p_lt_one
    positivity

theorem E_eq (f : Bool → ℝ) :
    ∑ x, ∑ y, w x y * (f x - f y) ^ 2 = p * (1 - p) * (f true - f false) ^ 2 := by
  simp only [Fintype.sum_bool, w]
  simp
  ring

noncomputable def F : Form μ := finiteForm μ w w_nonneg

theorem F_E (f : Bool → ℝ) : F.E f = p * (1 - p) * (f true - f false) ^ 2 := by
  show ∑ x, ∑ y, w x y * (f x - f y) ^ 2 = _
  exact E_eq f

theorem variance_eq (f : Bool → ℝ) : variance f μ = p * (1 - p) * (f true - f false) ^ 2 := by
  rw [variance_finite, Fintype.sum_bool, Fintype.sum_bool, real_true, real_false]
  ring

theorem hπ : ∀ x, 0 < μ.real {x} := by
  intro x
  have := p_pos; have := p_lt_one
  cases x
  · rw [real_false]; linarith
  · rw [real_true]; exact p_pos

theorem hconn : ∀ f : Bool → ℝ, ∑ x, ∑ y, w x y * (f x - f y) ^ 2 = 0 → ∀ x y, f x = f y := by
  intro f hf x y
  rw [E_eq] at hf
  have := p_pos; have := p_lt_one
  have h1 : (f true - f false) ^ 2 = 0 := by
    rcases mul_eq_zero.1 hf with h | h
    · exfalso; have : 0 < p * (1 - p) := by positivity
      linarith
    · exact h
  have h2 : f true = f false := by nlinarith [sq_nonneg (f true - f false)]
  cases x <;> cases y <;> simp [h2]

/-- `Ent(f²) ≤ (f true - f false)²`: a log-Sobolev inequality with constant `1/(p(1-p))`. -/
theorem lsi_const (f : Bool → ℝ) :
    CutCur.entropyOf μ (fun x => f x ^ 2) ≤ (f true - f false) ^ 2 := by
  have hp := p_pos; have hq := p_lt_one
  set s := f true
  set t := f false
  have hM : ∑ x, μ.real {x} * (f x ^ 2) = p * s ^ 2 + (1 - p) * t ^ 2 := by
    rw [Fintype.sum_bool, real_true, real_false]
  rcases (show 0 ≤ p * s ^ 2 + (1 - p) * t ^ 2 by positivity).eq_or_lt with h0 | hpos
  · have hs : s = 0 := by
      have : p * s ^ 2 = 0 := by nlinarith [mul_nonneg hp.le (sq_nonneg s), mul_nonneg (by linarith : (0:ℝ) ≤ 1 - p) (sq_nonneg t)]
      rcases mul_eq_zero.1 this with h | h
      · exact absurd h hp.ne'
      · exact pow_eq_zero_iff (by norm_num) |>.1 h
    have ht : t = 0 := by
      have : (1 - p) * t ^ 2 = 0 := by nlinarith [mul_nonneg hp.le (sq_nonneg s), mul_nonneg (by linarith : (0:ℝ) ≤ 1 - p) (sq_nonneg t)]
      rcases mul_eq_zero.1 this with h | h
      · exfalso; linarith
      · exact pow_eq_zero_iff (by norm_num) |>.1 h
    rw [entropy_finite, Fintype.sum_bool, Fintype.sum_bool, real_true, real_false]
    have hs' : f true = 0 := hs
    have ht' : f false = 0 := ht
    simp [hs', ht']
    positivity
  · have key := entropy_finite_le μ (g := fun x => f x ^ 2) (fun x => sq_nonneg _) (by rw [hM]; exact hpos)
    refine key.trans ?_
    simp only [Fintype.sum_bool, real_true, real_false] at key ⊢
    rw [div_le_iff₀ (by simpa using hpos)]
    have h4 : ((s ^ 2) ^ 2 * p + (t ^ 2) ^ 2 * (1 - p)) = p * s ^ 4 + (1 - p) * t ^ 4 := by ring
    nlinarith [mul_nonneg (sq_nonneg (s - t)) (sq_nonneg (p * s - (1 - p) * t))]

theorem optPI_le : F.optPI ≤ 1 := by
  refine csInf_le ⟨0, fun _ h => h.1⟩ ⟨zero_le_one, fun f _ => ?_⟩
  rw [variance_eq, F_E]; simp

theorem three_le_optLSI : 3 ≤ F.optLSI := by
  have hp := p_pos; have hq := p_lt_one
  have hne : {C : ℝ | 0 ≤ C ∧ ∀ f ∈ F.Q, CutCur.entropyOf μ (fun x => f x ^ 2) ≤ C * F.E f}.Nonempty := by
    have hne1 : (1 - p) ≠ 0 := by linarith
    refine ⟨1 / (p * (1 - p)), by positivity, fun f _ => ?_⟩
    rw [F_E]
    have : 1 / (p * (1 - p)) * (p * (1 - p) * (f true - f false) ^ 2) = (f true - f false) ^ 2 := by
      field_simp
    rw [this]; exact lsi_const f
  refine le_csInf hne fun c ⟨hc0, hc⟩ => ?_
  have h := hc (fun b => if b then 1 else 0) trivial
  rw [F_E] at h
  rw [entropy_finite, Fintype.sum_bool, Fintype.sum_bool, real_true, real_false] at h
  simp only [ite_true, Bool.false_eq_true, ite_false] at h
  have hlog : Real.log p = -3 := Real.log_exp _
  simp [hlog] at h
  have : 3 * p ≤ c * (p * (1 - p)) := by linarith
  have h2 : 3 * p ≤ c * p := by
    have : c * (p * (1 - p)) ≤ c * p := by nlinarith [mul_nonneg hc0 hp.le]
    linarith
  nlinarith

end TwoPoint

/-- **Discrete Rothaus on the two-point space, no hypotheses left.** On `Bool` with `μ{true} = e^{-3}` and the form
`E f = p(1-p)(f true - f false)²`, `C_LSI > 2 C_PI`, and there is an LSI extremal function. -/
theorem twoPoint_rothaus :
    2 * TwoPoint.F.optPI < TwoPoint.F.optLSI ∧
    ∃ f : Bool → ℝ, 0 < TwoPoint.F.E f ∧
      CutCur.entropyOf TwoPoint.μ (fun x => f x ^ 2) = TwoPoint.F.optLSI * TwoPoint.F.E f := by
  have hgt : 2 * TwoPoint.F.optPI < TwoPoint.F.optLSI := by
    have := TwoPoint.optPI_le; have := TwoPoint.three_le_optLSI; linarith
  refine ⟨hgt, ?_⟩
  obtain ⟨f, h1, h2⟩ := finite_rothaus TwoPoint.μ TwoPoint.w TwoPoint.w_nonneg TwoPoint.hπ TwoPoint.hconn hgt
  exact ⟨f, h1, h2⟩

end CutoffRigidity.Rothaus
