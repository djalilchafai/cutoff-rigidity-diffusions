module

public import CutoffRigidity.Riemann.WitnessBochner

/-! # Witness (part 3): the quadratic potential and `CD(ρ)` on `ℝ^k` -/

@[expose] public section

open Bundle MeasureTheory
open scoped Manifold ContDiff ENNReal NNReal Topology

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

namespace CutoffRigidity.Riemann.Witness

open CutCur CutoffRigidity

variable {k : ℕ}

/-- The Gaussian potential `V x = ρ‖x‖²/2 + (k/2) log (2π/ρ)`: `e^{-V}` is the density of
`N(0, ρ⁻¹ I)`. -/
noncomputable def gaussPot (k : ℕ) (ρ : ℝ) : Rd k → ℝ :=
  fun x => ρ / 2 * ‖x‖ ^ 2 + (k : ℝ) / 2 * Real.log (2 * Real.pi / ρ)

theorem fderiv_gaussPot (ρ : ℝ) (x : Rd k) :
    fderiv ℝ (gaussPot k ρ) x = ρ • innerSL ℝ x := by
  have h : HasFDerivAt (fun y : Rd k => ‖y‖ ^ 2) (2 • innerSL ℝ x) x :=
    (hasStrictFDerivAt_norm_sq x).hasFDerivAt
  have h2 := ((h.const_mul (ρ / 2)).add_const ((k : ℝ) / 2 * Real.log (2 * Real.pi / ρ)))
  rw [show gaussPot k ρ = fun y => ρ / 2 * ‖y‖ ^ 2 + (k : ℝ) / 2 * Real.log (2 * Real.pi / ρ) from rfl,
    h2.fderiv]
  ext z
  simp
  ring

theorem contDiff_gaussPot (ρ : ℝ) : ContDiff ℝ ∞ (gaussPot k ρ) := by
  unfold gaussPot
  exact (contDiff_const.mul (contDiff_norm_sq ℝ)).add contDiff_const

theorem gradient_gaussPot (ρ : ℝ) (x : Rd k) : gradient (gaussPot k ρ) x = ρ • x := by
  unfold gradient
  rw [fderiv_gaussPot]
  apply (InnerProductSpace.toDual ℝ (Rd k)).injective
  ext z
  simp [InnerProductSpace.toDual_apply_apply]

theorem hessian_gaussPot (ρ : ℝ) (x z : Rd k) :
    fderiv ℝ (fderiv ℝ (gaussPot k ρ)) x z z = ρ * ‖z‖ ^ 2 := by
  have : fderiv ℝ (gaussPot k ρ) = fun y => ρ • innerSL ℝ y := funext (fderiv_gaussPot ρ)
  rw [this]
  have h : HasFDerivAt (fun y : Rd k => ρ • innerSL ℝ y) (ρ • innerSL ℝ) x :=
    ((innerSL ℝ : Rd k →L[ℝ] Rd k →L[ℝ] ℝ).hasFDerivAt).const_smul ρ
  rw [h.fderiv]
  simp only [smul_apply, smul_eq_mul]
  rw [show (innerSL ℝ z) z = ‖z‖ ^ 2 by rw [innerSL_apply_apply, real_inner_self_eq_norm_sq]]

/-- `CD(ρ,∞)` holds for the Gaussian potential on flat `ℝ^k`. -/
theorem cd_gaussPot (ρ : ℝ) : CD (Rd k) ρ (gaussPot k ρ) := by
  intro f hf x
  have hf' : ContDiff ℝ ∞ f := contMDiff_iff_contDiff.1 hf
  rw [carre2_rd hf', gamma2_euclid (contDiff_gaussPot ρ) hf', hessian_gaussPot, carre_rd,
    real_inner_self_eq_norm_sq]
  have : 0 ≤ ∑ i, ∑ j, coordinateDerivative j (coordinateDerivative i f) x ^ 2 := by positivity
  linarith

theorem exp_neg_gaussPot (ρ : ℝ) (hρ : 0 < ρ) (x : Rd k) :
    Real.exp (-gaussPot k ρ x) =
      (2 * Real.pi / ρ) ^ (-(k : ℝ) / 2) * Real.exp (-(ρ / 2) * ‖x‖ ^ 2) := by
  unfold gaussPot
  have hpos : 0 < 2 * Real.pi / ρ := by positivity
  rw [show -(ρ / 2 * ‖x‖ ^ 2 + (k : ℝ) / 2 * Real.log (2 * Real.pi / ρ)) =
      -(ρ / 2) * ‖x‖ ^ 2 + (-(k : ℝ) / 2) * Real.log (2 * Real.pi / ρ) by ring, Real.exp_add,
    mul_comm, Real.rpow_def_of_pos hpos, mul_comm (Real.log _)]

theorem integral_rexp_gauss (ρ : ℝ) (hρ : 0 < ρ) :
    ∫ x : Rd k, Real.exp (-(ρ / 2) * ‖x‖ ^ 2) = (2 * Real.pi / ρ) ^ ((k : ℝ) / 2) := by
  have := GaussianFourier.integral_rexp_neg_mul_sq_norm (V := Rd k) (b := ρ / 2) (by positivity)
  rw [this]
  simp only [finrank_euclideanSpace, Fintype.card_fin]
  congr 1
  field_simp

theorem integrable_rexp_gauss (ρ : ℝ) (hρ : 0 < ρ) :
    Integrable (fun x : Rd k => Real.exp (-(ρ / 2) * ‖x‖ ^ 2)) := by
  by_contra h
  have h0 := integral_rexp_gauss (k := k) ρ hρ
  rw [integral_undef h] at h0
  have : 0 < (2 * Real.pi / ρ) ^ ((k : ℝ) / 2) := by positivity
  linarith

theorem integral_exp_neg_gaussPot (ρ : ℝ) (hρ : 0 < ρ) :
    ∫ x : Rd k, Real.exp (-gaussPot k ρ x) = 1 := by
  simp_rw [exp_neg_gaussPot ρ hρ]
  rw [integral_const_mul, integral_rexp_gauss ρ hρ, ← Real.rpow_add (by positivity)]
  rw [show -(k : ℝ) / 2 + (k : ℝ) / 2 = 0 by ring, Real.rpow_zero]

theorem integrable_exp_neg_gaussPot (ρ : ℝ) (hρ : 0 < ρ) :
    Integrable (fun x : Rd k => Real.exp (-gaussPot k ρ x)) := by
  simp_rw [exp_neg_gaussPot ρ hρ]
  exact (integrable_rexp_gauss ρ hρ).const_mul _

theorem isProbabilityMeasure_gibbs_gaussPot (ρ : ℝ) (hρ : 0 < ρ) :
    IsProbabilityMeasure (gibbs (gaussPot k ρ)) := by
  refine ⟨?_⟩
  rw [gibbs, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal (integrable_exp_neg_gaussPot ρ hρ)
      (Filter.Eventually.of_forall fun x => (Real.exp_pos _).le), integral_exp_neg_gaussPot ρ hρ]
  simp

end CutoffRigidity.Riemann.Witness
