module

public import CutoffRigidity.Extra.Dyson4

/-! # Dyson--OU on the Weyl chamber: Poincaré inequality, eigenfunction identity -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ContDiff ENNReal

namespace CutoffRigidity.Dyson

variable {d : ℕ}

/-- The normalised Dyson--OU Gibbs probability measure on the chamber. -/
noncomputable def dysonProb (d : ℕ) (ρ β : ℝ) : Measure (CutCur.Rd d) :=
  (dysonMeasure d ρ β Set.univ)⁻¹ • dysonMeasure d ρ β

theorem dysonZ_pos (hd : 0 < d) {ρ : ℝ} (hρ : 0 < ρ) {β : ℝ} (hβ : 0 ≤ β) :
    0 < ∫ x, Dlim d ρ β x := by
  have := dysonMeasure_pos (d := d) ρ β nonempty_chamber
  rw [dysonMeasure_univ hρ hβ, ENNReal.ofReal_pos] at this
  exact this

theorem isProbabilityMeasure_dysonProb (hd : 0 < d) {ρ : ℝ} (hρ : 0 < ρ) {β : ℝ} (hβ : 0 ≤ β) :
    IsProbabilityMeasure (dysonProb d ρ β) := by
  have h0 := (dysonMeasure_pos (d := d) ρ β nonempty_chamber).ne'
  have h1 : dysonMeasure d ρ β Set.univ ≠ ⊤ := by
    rw [dysonMeasure_univ hρ hβ]; exact ENNReal.ofReal_ne_top
  refine ⟨?_⟩
  simp only [dysonProb, Measure.smul_apply, smul_eq_mul]
  exact ENNReal.inv_mul_cancel h0 h1

theorem integral_dysonProb (hd : 0 < d) {ρ : ℝ} (hρ : 0 < ρ) {β : ℝ} (hβ : 0 ≤ β) (F : CutCur.Rd d → ℝ) :
    ∫ x, F x ∂dysonProb d ρ β = (∫ x, Dlim d ρ β x)⁻¹ * ∫ x, Dlim d ρ β x * F x := by
  have hZ := dysonZ_pos hd hρ hβ
  unfold dysonProb
  rw [integral_smul_measure, integral_dysonMeasure, dysonMeasure_univ hρ hβ, ENNReal.toReal_inv,
    ENNReal.toReal_ofReal hZ.le, smul_eq_mul]

theorem bdd_poly {F : CutCur.Rd d → ℝ} {C : ℝ} (hC : ∀ x, |F x| ≤ C) :
    ∀ x, |F x| ≤ C * (1 + ‖x‖) ^ 2 := by
  intro x
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC 0)
  calc |F x| ≤ C := hC x
    _ = C * 1 := (mul_one C).symm
    _ ≤ C * (1 + ‖x‖) ^ 2 := by
      apply mul_le_mul_of_nonneg_left _ hC0
      nlinarith [norm_nonneg x]


/-- **Poincaré inequality with constant `1/ρ`** for the Dyson--OU Gibbs measure on the Weyl chamber,
on the test functions of the manuscript's optimal-constant discussion. -/
theorem dyson_poincare (hd : 0 < d) {ρ : ℝ} (hρ : 0 < ρ) {β : ℝ} (hβ : 0 ≤ β)
    {f : CutCur.Rd d → ℝ} (hf : CutCur.IsTestFunction f) :
    variance f (dysonProb d ρ β) ≤ ρ⁻¹ * ∫ x, ‖gradient f x‖ ^ 2 ∂dysonProb d ρ β := by
  have := isProbabilityMeasure_dysonProb hd hρ hβ
  obtain ⟨M, hM⟩ := hf.2.1
  obtain ⟨L, hL0, hL⟩ := hf.gradient_bound
  have hfc : Continuous f := hf.1.continuous
  have hgc : Continuous fun x => ‖gradient f x‖ ^ 2 :=
    (continuous_gradient_of_c1 (hf.1.of_le (by simp))).norm.pow 2
  set Z := ∫ x, Dlim d ρ β x with hZ
  have hZpos : 0 < Z := dysonZ_pos hd hρ hβ
  have tZ := tendsto_integral_Dens (d := d) hρ hβ (F := fun _ => (1 : ℝ)) measurable_const (M := 1)
    (bdd_poly (F := fun _ => (1 : ℝ)) (C := 1) fun x => by simp)
  have tA := tendsto_integral_Dens hρ hβ (F := fun x => f x ^ 2) (hfc.pow 2).measurable (M := M ^ 2)
    (bdd_poly (C := M ^ 2) fun x => by
      rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hM x) 2)
  have tB := tendsto_integral_Dens hρ hβ (F := f) hfc.measurable (M := M) (bdd_poly (C := M) hM)
  have tC := tendsto_integral_Dens hρ hβ (F := fun x => ‖gradient f x‖ ^ 2) hgc.measurable (M := L ^ 2)
    (bdd_poly (C := L ^ 2) fun x => by
      rw [abs_of_nonneg (by positivity)]; exact pow_le_pow_left₀ (norm_nonneg _) (hL x) 2)
  simp only [mul_one] at tZ
  have hlim := le_of_tendsto_of_tendsto
    ((tZ.mul tA).sub (tB.pow 2)) ((tZ.const_mul ρ⁻¹).mul tC) (by
      filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
      have := eps_poincare (d := d) hε hd hρ hβ hf
      simpa [mul_assoc] using this)
  have hfm : MemLp f 2 (dysonProb d ρ β) :=
    memLp_of_bounded (a := -M) (b := M) (Eventually.of_forall fun x => by
      rw [Set.mem_Icc, ← abs_le]; exact hM x) hfc.aestronglyMeasurable 2
  rw [variance_eq_sub hfm]
  simp only [Pi.pow_apply]
  rw [integral_dysonProb hd hρ hβ (fun x => f x ^ 2), integral_dysonProb hd hρ hβ f,
    integral_dysonProb hd hρ hβ (fun x => ‖gradient f x‖ ^ 2)]
  generalize (∫ x, Dlim d ρ β x * f x ^ 2) = A at hlim ⊢
  generalize (∫ x, Dlim d ρ β x * f x) = B at hlim ⊢
  generalize (∫ x, Dlim d ρ β x * ‖gradient f x‖ ^ 2) = C at hlim ⊢
  have e1 : Z⁻¹ * A - (Z⁻¹ * B) ^ 2 = (Z⁻¹) ^ 2 * (Z * A - B ^ 2) := by field_simp
  have e2 : ρ⁻¹ * (Z⁻¹ * C) = (Z⁻¹) ^ 2 * (ρ⁻¹ * Z * C) := by field_simp
  rw [e1, e2]
  exact mul_le_mul_of_nonneg_left hlim (sq_nonneg _)


theorem abs_sum_le (x : CutCur.Rd d) : |∑ i, x i| ≤ d * ‖x‖ := by
  calc |∑ i, x i| ≤ ∑ i, |x i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin d, ‖x‖ := Finset.sum_le_sum fun i _ => norm_coord_le x i
    _ = d * ‖x‖ := by simp

/-- **Weak Neumann eigenfunction identity.** The function `h = x_1 + ⋯ + x_d` satisfies
`∫ ⟨∇h, ∇φ⟩ dμ = ρ ∫ h φ dμ` for every test function `φ` (no boundary term on the walls of the
chamber): this is the weak form of `L h = -ρ h` with Neumann boundary conditions. -/
theorem dyson_neumann (hd : 0 < d) {ρ : ℝ} (hρ : 0 < ρ) {β : ℝ} (hβ : 0 ≤ β)
    {φ : CutCur.Rd d → ℝ} (hφ : CutCur.IsTestFunction φ) :
    ∫ x, inner ℝ (gradient (fun y : CutCur.Rd d => ∑ i, y i) x) (gradient φ x) ∂dysonProb d ρ β =
      ρ * ∫ x, (∑ i, x i) * φ x ∂dysonProb d ρ β := by
  have := isProbabilityMeasure_dysonProb hd hρ hβ
  obtain ⟨M, hM⟩ := hφ.2.1
  obtain ⟨L, hL0, hL⟩ := hφ.gradient_bound
  have hφc : Continuous φ := hφ.1.continuous
  have hderφ : Continuous fun x => fderiv ℝ φ x (CutoffRigidity.diagonalDirection d) :=
    ((hφ.1.continuous_fderiv (by simp)).clm_apply continuous_const)
  have hsc : Continuous fun x : CutCur.Rd d => ∑ i, x i := continuous_finsetSum _ fun i _ => by fun_prop
  have t1 := tendsto_integral_Dens hρ hβ (F := fun x => fderiv ℝ φ x (CutoffRigidity.diagonalDirection d))
    hderφ.measurable (M := L * ‖CutoffRigidity.diagonalDirection d‖)
    (bdd_poly (C := L * ‖CutoffRigidity.diagonalDirection d‖) fun x => by
      have : fderiv ℝ φ x (CutoffRigidity.diagonalDirection d) =
          inner ℝ (gradient φ x) (CutoffRigidity.diagonalDirection d) := by
        rw [← inner_gradient_left]
      rw [this]
      exact (abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right (hL x) (norm_nonneg _)))
  have t2 := tendsto_integral_Dens hρ hβ (F := fun x => (∑ i, x i) * φ x)
    (hsc.mul hφc).measurable (M := d * M) (fun x => by
      rw [abs_mul]
      have h1 := abs_sum_le x
      have h2 := hM x
      have hx : ‖x‖ ≤ (1 + ‖x‖) ^ 2 := by nlinarith [norm_nonneg x]
      have hM0 : 0 ≤ M := (abs_nonneg _).trans h2
      calc |∑ i, x i| * |φ x| ≤ (d * ‖x‖) * M := mul_le_mul h1 h2 (abs_nonneg _) (by positivity)
        _ = (d * M) * ‖x‖ := by ring
        _ ≤ (d * M) * (1 + ‖x‖) ^ 2 := mul_le_mul_of_nonneg_left hx (by positivity))
  have heq := tendsto_nhds_unique t1 ((t2.const_mul ρ).congr' (by
    filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
    have := eps_ibp (d := d) hε hd hρ hβ hφ
    exact this.symm))
  rw [integral_dysonProb hd hρ hβ, integral_dysonProb hd hρ hβ]
  have hg : ∀ x, inner ℝ (gradient (fun y : CutCur.Rd d => ∑ i, y i) x) (gradient φ x) =
      fderiv ℝ φ x (CutoffRigidity.diagonalDirection d) := by
    intro x
    rw [Paper.gradient_sum, real_inner_comm, inner_gradient_left]
    rfl
  simp only [hg]
  rw [heq, mul_left_comm]

end CutoffRigidity.Dyson
