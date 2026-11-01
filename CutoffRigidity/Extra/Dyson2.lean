module

public import CutoffRigidity.Extra.Dyson
public import CutoffRigidity.Extra.Dyson1D
public import CutoffRigidity.Extra.PairwiseInteraction
public import CutoffRigidity.Extra.OptimalConstants

/-! # Regularised Dyson--OU potentials `V_ε` on `ℝ^d` (smooth, `ρ`-convex) and their exact Poincaré /
integration-by-parts identities -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ContDiff

namespace CutoffRigidity.Dyson

variable {d : ℕ}

/-- Regularised interaction `W_ε(x) = ∑_{i<j} G_ε(x_i - x_j)`. -/
noncomputable def Weps (d : ℕ) (β ε : ℝ) (x : CutCur.Rd d) : ℝ :=
  ∑ i, ∑ j with i < j, Ge ε β (x i - x j)

/-- Regularised density `e^{-V_ε}`, `V_ε = ρ/2 |x|² + W_ε`. -/
noncomputable def Dens (d : ℕ) (ρ β ε : ℝ) (x : CutCur.Rd d) : ℝ :=
  Real.exp (-(ρ / 2) * ‖x‖ ^ 2) * ∏ i, ∏ j with i < j, qe ε β (x i - x j)

theorem alg_aux {Z ρ A B C : ℝ} (hZ : 0 < Z)
    (h : Z⁻¹ * A - (Z⁻¹ * B) ^ 2 ≤ ρ⁻¹ * (Z⁻¹ * C)) : Z * A - B ^ 2 ≤ ρ⁻¹ * Z * C := by
  have := mul_le_mul_of_nonneg_left h (sq_nonneg Z)
  have e1 : Z ^ 2 * (Z⁻¹ * A - (Z⁻¹ * B) ^ 2) = Z * A - B ^ 2 := by field_simp
  have e2 : Z ^ 2 * (ρ⁻¹ * (Z⁻¹ * C)) = ρ⁻¹ * Z * C := by field_simp
  rwa [e1, e2] at this

section Reg
variable {ε : ℝ} (hε : 0 < ε) (β : ℝ)
include hε

theorem Weps_props {β : ℝ} (hβ : 0 ≤ β) :
    ConvexOn ℝ Set.univ (Weps d β ε) ∧ (∀ x (s : ℝ), Weps d β ε (x + s • CutCur.diagonal d) = Weps d β ε x) ∧
      ContDiff ℝ 2 (Weps d β ε) := by
  have := CutoffRigidity.Paper.pairwise_interaction (d := d) (convexOn_Ge hε hβ)
  have h2 : ContDiff ℝ 2 (Ge ε β) := (contDiff_Ge hε β).of_le (by exact_mod_cast le_top)
  exact ⟨this.1, this.2.1, this.2.2 h2⟩

theorem exp_neg_V_eps (ρ : ℝ) (x : CutCur.Rd d) :
    Real.exp (-(ρ / 2 * ‖x‖ ^ 2 + Weps d β ε x)) = Dens d ρ β ε x := by
  unfold Dens Weps
  rw [neg_add, Real.exp_add]
  congr 1
  · congr 1; ring
  · rw [← Finset.sum_neg_distrib, Real.exp_sum]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [← Finset.sum_neg_distrib, Real.exp_sum]
    exact Finset.prod_congr rfl fun j _ => exp_neg_Ge hε β _

theorem Dens_integrable {ρ : ℝ} (hρ : 0 < ρ) {β : ℝ} (hβ : 0 ≤ β) :
    Integrable (Dens d ρ β ε) volume ∧ 0 < ∫ x, Dens d ρ β ε x := by
  obtain ⟨hconv, hinv, hW⟩ := Weps_props hε hβ
  have hV : ContDiff ℝ 2 (fun x : CutCur.Rd d => ρ / 2 * ‖x‖ ^ 2 + Weps d β ε x) :=
    (contDiff_const.mul (contDiff_norm_sq ℝ)).add hW
  have := gibbs_partition_finite_positive hV ρ hρ
    (CutoffRigidity.hessian_quadratic_add_convex_lower hW hconv ρ)
  have e : (fun x : CutCur.Rd d => Real.exp (-(ρ / 2 * ‖x‖ ^ 2 + Weps d β ε x))) = Dens d ρ β ε :=
    funext fun x => exp_neg_V_eps hε β ρ x
  simpa only [e] using this

/-- The normalised regularised measure is a probability measure; integrals against it. -/
theorem eps_normalised {ρ : ℝ} (hρ : 0 < ρ) {β : ℝ} (hβ : 0 ≤ β) :
    let Z := ∫ x, Dens d ρ β ε x
    let W' := fun x : CutCur.Rd d => Weps d β ε x + Real.log Z
    let V' := fun x : CutCur.Rd d => ρ / 2 * ‖x‖ ^ 2 + W' x
    IsProbabilityMeasure (CutCur.gibbs V') ∧ ContDiff ℝ 2 W' ∧ ConvexOn ℝ Set.univ W' ∧
      (∀ x (s : ℝ), W' (x + s • CutCur.diagonal d) = W' x) ∧
      ∀ F : CutCur.Rd d → ℝ, ∫ x, F x ∂CutCur.gibbs V' = Z⁻¹ * ∫ x, Dens d ρ β ε x * F x := by
  intro Z W' V'
  obtain ⟨hconv, hinv, hW⟩ := Weps_props hε hβ
  obtain ⟨hint, hpos⟩ := Dens_integrable hε hρ hβ
  have hV : ContDiff ℝ 2 (fun x : CutCur.Rd d => ρ / 2 * ‖x‖ ^ 2 + Weps d β ε x) :=
    (contDiff_const.mul (contDiff_norm_sq ℝ)).add hW
  have e : (fun x : CutCur.Rd d => Real.exp (-(ρ / 2 * ‖x‖ ^ 2 + Weps d β ε x))) = Dens d ρ β ε :=
    funext fun x => exp_neg_V_eps hε β ρ x
  have hint' : Integrable (fun x : CutCur.Rd d => Real.exp (-(ρ / 2 * ‖x‖ ^ 2 + Weps d β ε x))) volume := by
    rw [e]; exact hint
  have hpos' : 0 < ∫ x : CutCur.Rd d, Real.exp (-(ρ / 2 * ‖x‖ ^ 2 + Weps d β ε x)) := by
    rw [e]; exact hpos
  have hp := gibbsMeasure_normalize_potential (volume : Measure (CutCur.Rd d)) _ hint' hpos'
  have hZ : (∫ x : CutCur.Rd d, Real.exp (-(ρ / 2 * ‖x‖ ^ 2 + Weps d β ε x))) = Z := by rw [e]
  rw [hZ] at hp
  have hV'eq : V' = fun x => ρ / 2 * ‖x‖ ^ 2 + Weps d β ε x + Real.log Z := by
    funext x; simp only [V', W']; ring
  have hZpos : 0 < Z := hpos
  refine ⟨?_, hW.add contDiff_const, hconv.add_const _, fun x s => ?_, fun F => ?_⟩
  · show IsProbabilityMeasure (gibbsMeasure volume V')
    rw [hV'eq]; exact hp
  · simp only [W']; rw [hinv x s]
  · have hVm : Measurable V' := by
      have : ContDiff ℝ 2 V' := (contDiff_const.mul (contDiff_norm_sq ℝ)).add (hW.add contDiff_const)
      exact this.continuous.measurable
    show ∫ x, F x ∂gibbsMeasure volume V' = _
    rw [integral_gibbsMeasure volume hVm, ← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [smul_eq_mul, V', W']
    have : Real.exp (-(ρ / 2 * ‖x‖ ^ 2 + (Weps d β ε x + Real.log Z))) = Z⁻¹ * Dens d ρ β ε x := by
      rw [← exp_neg_V_eps hε β ρ x, ← add_assoc, neg_add, Real.exp_add, Real.exp_neg (Real.log Z),
        Real.exp_log hZpos]
      ring
    rw [this]; ring

/-- Exact Poincaré inequality (constant `1/ρ`) for the regularised law, in unnormalised form. -/
theorem eps_poincare (hd : 0 < d) {ρ : ℝ} (hρ : 0 < ρ) {β : ℝ} (hβ : 0 ≤ β)
    {f : CutCur.Rd d → ℝ} (hf : CutCur.IsTestFunction f) :
    let Z := ∫ x, Dens d ρ β ε x
    Z * (∫ x, Dens d ρ β ε x * f x ^ 2) - (∫ x, Dens d ρ β ε x * f x) ^ 2 ≤
      ρ⁻¹ * Z * (∫ x, Dens d ρ β ε x * ‖gradient f x‖ ^ 2) := by
  intro Z
  obtain ⟨hp, hW, hconv, hinv, hI⟩ := eps_normalised hε hρ hβ
  obtain ⟨-, hpos⟩ := Dens_integrable hε hρ hβ
  have hZpos : 0 < Z := hpos
  set W' := fun x : CutCur.Rd d => Weps d β ε x + Real.log Z with hW'
  set V' := fun x : CutCur.Rd d => ρ / 2 * ‖x‖ ^ 2 + W' x with hV'
  have hVc : ContDiff ℝ 2 V' := (contDiff_const.mul (contDiff_norm_sq ℝ)).add hW
  obtain ⟨⟨hgap, -⟩, -, hR⟩ := CutoffRigidity.Paper.convex_interaction hd hρ hW hconv hinv hp
  have hPI := CutoffRigidity.Paper.pi_valid hVc hp hR hf
  rw [hgap] at hPI
  have hfm : MemLp f 2 (CutCur.gibbs V') := by
    obtain ⟨M, hM⟩ := hf.2.1
    exact memLp_of_bounded (a := -M) (b := M) (Eventually.of_forall fun x => by
      rw [Set.mem_Icc, ← abs_le]; exact hM x) hf.1.continuous.aestronglyMeasurable 2
  rw [variance_eq_sub hfm] at hPI
  simp only [Pi.pow_apply] at hPI
  rw [hI (fun x => f x ^ 2), hI f, hI (fun x => ‖gradient f x‖ ^ 2)] at hPI
  have hZ0 : Z ≠ 0 := hZpos.ne'
  have hZdef : (∫ x, Dens d ρ β ε x) = Z := rfl
  rw [hZdef] at hPI
  exact alg_aux hZpos hPI

omit hε in
theorem fderiv_V_diag {W : CutCur.Rd d → ℝ} {ρ : ℝ} {x : CutCur.Rd d} (hW : DifferentiableAt ℝ W x)
    (hinv : ∀ u : ℝ, W (x + u • CutoffRigidity.diagonalDirection d) = W x) :
    fderiv ℝ (fun y => ρ / 2 * ‖y‖ ^ 2 + W y) x (CutoffRigidity.diagonalDirection d) = ρ * ∑ i, x i := by
  have hnorm := (hasStrictFDerivAt_norm_sq x).hasFDerivAt.differentiableAt
  have hquad := hnorm.const_mul (ρ / 2)
  have hdir := CutoffRigidity.fderiv_apply_eq_zero_of_translation_invariant hW hinv
  rw [fderiv_fun_add hquad hW, fderiv_const_mul hnorm, fderiv_norm_sq_apply]
  simp only [add_apply, smul_apply, smul_eq_mul, hdir, add_zero]
  rw [show innerSL ℝ x (CutoffRigidity.diagonalDirection d) = ∑ i, x i by
    change inner ℝ x (CutoffRigidity.diagonalDirection d) = ∑ i, x i
    rw [real_inner_comm]; exact CutoffRigidity.inner_diagonalDirection x]
  ring

/-- Exact weak Neumann eigenfunction identity for the regularised law (unnormalised form):
`∫ D_ε ∂_{(1,..,1)} φ = ρ ∫ D_ε h φ`. -/
theorem eps_ibp (hd : 0 < d) {ρ : ℝ} (hρ : 0 < ρ) {β : ℝ} (hβ : 0 ≤ β)
    {φ : CutCur.Rd d → ℝ} (hφ : CutCur.IsTestFunction φ) :
    (∫ x, Dens d ρ β ε x * fderiv ℝ φ x (CutoffRigidity.diagonalDirection d)) =
      ρ * ∫ x, Dens d ρ β ε x * ((∑ i, x i) * φ x) := by
  obtain ⟨hp, hW, hconv, hinv, hI⟩ := eps_normalised hε hρ hβ
  obtain ⟨-, hpos⟩ := Dens_integrable hε hρ hβ
  have hZpos : 0 < ∫ x, Dens d ρ β ε x := hpos
  set Z := ∫ x, Dens d ρ β ε x with hZ
  set W' := fun x : CutCur.Rd d => Weps d β ε x + Real.log Z with hW'
  set V' := fun x : CutCur.Rd d => ρ / 2 * ‖x‖ ^ 2 + W' x with hV'
  have hVc : ContDiff ℝ 2 V' := (contDiff_const.mul (contDiff_norm_sq ℝ)).add hW
  have hVd : Differentiable ℝ V' := hVc.differentiable (by norm_num)
  have hWd : Differentiable ℝ W' := hW.differentiable (by norm_num)
  have hφd : Differentiable ℝ φ := (hφ.1.differentiable (by simp))
  have hfV (x : CutCur.Rd d) : fderiv ℝ V' x (CutoffRigidity.diagonalDirection d) = ρ * ∑ i, x i :=
    fderiv_V_diag (hWd x) (fun u => hinv x u)
  -- integrability
  obtain ⟨M, hM⟩ := hφ.2.1
  obtain ⟨L, hL0, hL⟩ := hφ.gradient_bound
  have hφc : Continuous φ := hφ.1.continuous
  have hp' : IsProbabilityMeasure (gibbsMeasure volume V') := hp
  have h1' : Integrable φ (CutCur.gibbs V') := by
    simpa using hφ.integrable_of_bounded (CutCur.gibbs V') (F := id) continuous_id
  have h1 : Integrable (fun x => (1 : ℝ) * φ x) (gibbsMeasure volume V') := by
    simp only [one_mul]; exact h1'
  have hderφ : Continuous fun x => fderiv ℝ φ x (CutoffRigidity.diagonalDirection d) :=
    ((hφ.1.continuous_fderiv (by simp)).clm_apply continuous_const)
  have h2 : Integrable (fun x => (1 : ℝ) * fderiv ℝ φ x (CutoffRigidity.diagonalDirection d))
      (gibbsMeasure volume V') := by
    refine Integrable.of_bound (C := L * ‖CutoffRigidity.diagonalDirection d‖) (by simpa using hderφ.aestronglyMeasurable)
      (Eventually.of_forall fun x => ?_)
    have : fderiv ℝ φ x (CutoffRigidity.diagonalDirection d) =
        inner ℝ (gradient φ x) (CutoffRigidity.diagonalDirection d) := by
      rw [← inner_gradient_left]
    simp only [one_mul, this, Real.norm_eq_abs]
    exact (abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right (hL x) (norm_nonneg _))
  have hsumL2 : MemLp (CutoffRigidity.coordinateSum : CutCur.Rd d → ℝ) 2 (gibbsMeasure volume V') :=
    CutoffRigidity.coordinateSum_memLp_gibbs hWd hρ (fun x u => hinv x u) hp
  have hsum1 : Integrable (fun x : CutCur.Rd d => ∑ i, x i) (gibbsMeasure volume V') :=
    (hsumL2.integrable one_le_two)
  have hc : ∀ x : CutCur.Rd d, fderiv ℝ (fun _ : CutCur.Rd d => (1 : ℝ)) x = 0 := fun x => fderiv_const_apply 1
  have h3 : Integrable (fun x => (fderiv ℝ (fun _ : CutCur.Rd d => (1 : ℝ)) x (CutoffRigidity.diagonalDirection d) -
      (1 : ℝ) * fderiv ℝ V' x (CutoffRigidity.diagonalDirection d)) * φ x) (gibbsMeasure volume V') := by
    have : Integrable (fun x => -(ρ * ((∑ i, x i) * φ x))) (gibbsMeasure volume V') := by
      refine Integrable.neg (Integrable.const_mul ?_ ρ)
      refine Integrable.mono' (hsum1.norm.mul_const M) ?_ (Eventually.of_forall fun x => ?_)
      · exact (hsum1.aestronglyMeasurable.mul hφc.aestronglyMeasurable)
      · rw [norm_mul]; exact mul_le_mul_of_nonneg_left (by simpa using hM x) (norm_nonneg _)
    refine this.congr (Eventually.of_forall fun x => ?_)
    simp only [hc, zero_apply, one_mul, hfV, zero_sub]
    ring
  have hibp := integral_mul_fderiv_gibbs_eq_neg (volume : Measure (CutCur.Rd d)) (f := fun _ => (1 : ℝ)) hVd
    (differentiable_const (1 : ℝ)) hφd (CutoffRigidity.diagonalDirection d) h1 h2 h3
  have e3 : (fun x => ((fderiv ℝ (fun _ : CutCur.Rd d => (1 : ℝ)) x (CutoffRigidity.diagonalDirection d) -
      (1 : ℝ) * fderiv ℝ V' x (CutoffRigidity.diagonalDirection d)) * φ x)) =
      fun x => -(ρ * ((∑ i, x i) * φ x)) := by
    funext x
    simp only [hc, zero_apply, one_mul, hfV, zero_sub]
    ring
  rw [e3] at hibp
  have hg : CutCur.gibbs V' = gibbsMeasure volume V' := rfl
  have eR : ∫ x, -(ρ * ((∑ i, x i) * φ x)) ∂gibbsMeasure volume V' =
      -(ρ * ∫ x, (∑ i, x i) * φ x ∂gibbsMeasure volume V') := by
    rw [integral_neg, integral_const_mul]
  have eL : ∫ x, (1 : ℝ) * fderiv ℝ φ x (CutoffRigidity.diagonalDirection d) ∂gibbsMeasure volume V' =
      ∫ x, fderiv ℝ φ x (CutoffRigidity.diagonalDirection d) ∂gibbsMeasure volume V' := by
    simp only [one_mul]
  rw [eR, eL] at hibp
  have l1 := hI (fun x => fderiv ℝ φ x (CutoffRigidity.diagonalDirection d))
  have l2 := hI (fun x => (∑ i, x i) * φ x)
  rw [hg] at l1 l2
  rw [l1, l2] at hibp
  simp only [neg_neg] at hibp
  have hZ0 : Z ≠ 0 := hZpos.ne'
  apply mul_left_cancel₀ (inv_ne_zero hZ0)
  linarith

end Reg

end CutoffRigidity.Dyson
