module

public import CutoffRigidity.Extra.GaussIso11
public import CutoffRigidity.Statements

/-! # The quadratic Gibbs measure is `N(0, ρ⁻¹ I)` (stage 6b), via characteristic functions -/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal

set_option linter.unusedSectionVars false

namespace CutoffRigidity.GaussIso

variable {d : ℕ}

lemma charFun_gaussρ {ρ : ℝ} (hρ : 0 < ρ) (t : EuclideanSpace ℝ (Fin d)) :
    charFun (gaussρ d ρ) t = Complex.exp (-(‖t‖ ^ 2 / (2 * ρ) : ℝ)) := by
  unfold gaussρ
  rw [charFun_map_smul, charFun_stdGaussian]
  congr 1
  have h : ‖(Real.sqrt ρ)⁻¹ • t‖ ^ 2 = ‖t‖ ^ 2 / ρ := by
    rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, inv_pow, Real.sq_sqrt hρ.le]; ring
  have hc : ((‖(Real.sqrt ρ)⁻¹ • t‖ : ℝ) : ℂ) ^ 2 = ((‖t‖ ^ 2 / ρ : ℝ) : ℂ) := by exact_mod_cast h
  rw [hc]
  have hρc : (ρ : ℂ) ≠ 0 := by exact_mod_cast hρ.ne'
  push_cast
  field_simp


/-- Characteristic function of the quadratic Gibbs measure (unnormalised constant made explicit). -/
lemma charFun_gibbs_quadratic {ρ : ℝ} (hρ : 0 < ρ) (c : ℝ) (t : EuclideanSpace ℝ (Fin d)) :
    charFun (CutCur.gibbs fun x : EuclideanSpace ℝ (Fin d) => ρ / 2 * ‖x‖ ^ 2 + c) t =
      (Complex.exp (-(c : ℂ)) * (Real.pi / (((ρ / 2 : ℝ)) : ℂ)) ^ ((d : ℂ) / 2)) *
        Complex.exp (-(‖t‖ ^ 2 / (2 * ρ) : ℝ)) := by
  unfold CutCur.gibbs
  rw [charFun_apply, integral_withDensity_eq_integral_toReal_smul (by fun_prop)
    (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  have hb : 0 < ((((ρ / 2 : ℝ)) : ℂ)).re := by simpa using hρ
  have key := GaussianFourier.integral_cexp_neg_mul_sq_norm_add_of_euclideanSpace (ι := Fin d) hb Complex.I t
  have e : ∀ x : EuclideanSpace ℝ (Fin d),
      (ENNReal.ofReal (Real.exp (-(ρ / 2 * ‖x‖ ^ 2 + c)))).toReal •
        Complex.exp (((inner ℝ x t : ℝ) : ℂ) * Complex.I) =
      Complex.exp (-(c : ℂ)) * Complex.exp (-(((ρ / 2 : ℝ)) : ℂ) * (‖x‖ : ℂ) ^ 2 +
        Complex.I * ((inner ℝ t x : ℝ) : ℂ)) := by
    intro x
    rw [ENNReal.toReal_ofReal (Real.exp_pos _).le, Complex.real_smul, Complex.ofReal_exp,
      ← Complex.exp_add, ← Complex.exp_add]
    congr 1
    rw [real_inner_comm]
    push_cast
    ring
  simp_rw [e]
  rw [integral_const_mul, key]
  simp only [Fintype.card_fin]
  have hρc : (ρ : ℂ) ≠ 0 := by exact_mod_cast hρ.ne'
  have h2 : Complex.I ^ 2 * (‖t‖ : ℂ) ^ 2 / (4 * (((ρ / 2 : ℝ)) : ℂ)) =
      -(((‖t‖ ^ 2 / (2 * ρ) : ℝ)) : ℂ) := by
    push_cast
    rw [Complex.I_sq]
    field_simp
    ring
  rw [h2]
  ring


/-- A probability Gibbs measure with quadratic potential `ρ|x|²/2 + c` is the Gaussian `N(0, ρ⁻¹ I)`. -/
theorem gibbs_quadratic_eq_gaussρ {ρ : ℝ} (hρ : 0 < ρ) (c : ℝ)
    (hp : IsProbabilityMeasure (CutCur.gibbs fun x : EuclideanSpace ℝ (Fin d) => ρ / 2 * ‖x‖ ^ 2 + c)) :
    CutCur.gibbs (fun x : EuclideanSpace ℝ (Fin d) => ρ / 2 * ‖x‖ ^ 2 + c) = gaussρ d ρ := by
  set K : ℂ := Complex.exp (-(c : ℂ)) * (Real.pi / (((ρ / 2 : ℝ)) : ℂ)) ^ ((d : ℂ) / 2) with hK
  have h0 := charFun_gibbs_quadratic (d := d) hρ c 0
  have hK1 : K = 1 := by
    have h1 : charFun (CutCur.gibbs fun x : EuclideanSpace ℝ (Fin d) => ρ / 2 * ‖x‖ ^ 2 + c) 0 = 1 := by
      rw [charFun_zero]; simp
    rw [h1] at h0
    have h2 := h0.symm
    simp only [norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_div, neg_zero,
      Complex.ofReal_zero, Complex.exp_zero, mul_one] at h2
    exact h2
  refine Measure.ext_of_charFun ?_
  funext t
  rw [charFun_gibbs_quadratic hρ c t, charFun_gaussρ hρ t, ← hK, hK1, one_mul]

end CutoffRigidity.GaussIso
