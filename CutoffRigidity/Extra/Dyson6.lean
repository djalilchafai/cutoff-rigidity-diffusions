module

public import CutoffRigidity.Extra.Dyson5
public import CutoffRigidity.PoincareIntegrableDomain

/-! # Dyson--OU on the Weyl chamber: extremality of `x_1 + ... + x_d` and the optimal Poincaré constant -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ContDiff ENNReal NNReal

namespace CutoffRigidity.Dyson

variable {d : ℕ}

/-- `h(x) = x_1 + ⋯ + x_d`. -/
noncomputable def hsum (d : ℕ) (x : CutCur.Rd d) : ℝ := ∑ i, x i

theorem hsum_eq_inner (x : CutCur.Rd d) : hsum d x = inner ℝ (CutCur.diagonal d) x :=
  (CutoffRigidity.inner_diagonalDirection x).symm

theorem hasFDerivAt_hsum (x : CutCur.Rd d) :
    HasFDerivAt (hsum d) (innerSL ℝ (CutCur.diagonal d)) x := by
  have : hsum d = innerSL ℝ (CutCur.diagonal d) := funext fun y => hsum_eq_inner y
  rw [this]; exact (innerSL ℝ (CutCur.diagonal d)).hasFDerivAt

theorem contDiff_S (n : ℕ) : ContDiff ℝ ∞ (CutoffRigidity.smoothNormalTruncation n) := by
  unfold CutoffRigidity.smoothNormalTruncation
  exact contDiff_const.mul (Real.contDiff_arctan.comp (contDiff_id.div_const _))

/-- the truncated functions `S_n ∘ h` are test functions -/
theorem isTestFunction_S_hsum (n : ℕ) :
    CutCur.IsTestFunction (fun x : CutCur.Rd d => CutoffRigidity.smoothNormalTruncation n (hsum d x)) := by
  have hh : ContDiff ℝ ∞ (hsum d) := by
    have : hsum d = innerSL ℝ (CutCur.diagonal d) := funext fun y => hsum_eq_inner y
    rw [this]; exact (innerSL ℝ (CutCur.diagonal d)).contDiff
  refine ⟨(contDiff_S n).comp hh, ⟨((n : ℝ) + 1) * (Real.pi / 2), fun x =>
    CutoffRigidity.smoothNormalTruncation_abs_le_bound n _⟩, ?_⟩
  have hS : LipschitzWith 1 (CutoffRigidity.smoothNormalTruncation n) :=
    CutoffRigidity.scalar_normal_contraction_lipschitz
      ((contDiff_S n).differentiable (by simp))
      (CutoffRigidity.deriv_smoothNormalTruncation_abs_le_one n)
  have hl : LipschitzWith ‖innerSL ℝ (CutCur.diagonal d)‖₊ (hsum d) := by
    have : hsum d = innerSL ℝ (CutCur.diagonal d) := funext fun y => hsum_eq_inner y
    rw [this]; exact (innerSL ℝ (CutCur.diagonal d)).lipschitzWith
  exact ⟨_, hS.comp hl⟩

theorem fderiv_S_hsum (n : ℕ) (x : CutCur.Rd d) :
    fderiv ℝ (fun y : CutCur.Rd d => CutoffRigidity.smoothNormalTruncation n (hsum d y)) x =
      (1 / (1 + (hsum d x / ((n : ℝ) + 1)) ^ 2)) • innerSL ℝ (CutCur.diagonal d) := by
  have := (CutoffRigidity.hasDerivAt_smoothNormalTruncation n (hsum d x)).comp_hasFDerivAt x
    (hasFDerivAt_hsum x)
  exact this.fderiv

theorem gradient_S_hsum (n : ℕ) (x : CutCur.Rd d) :
    gradient (fun y : CutCur.Rd d => CutoffRigidity.smoothNormalTruncation n (hsum d y)) x =
      (1 / (1 + (hsum d x / ((n : ℝ) + 1)) ^ 2)) • CutCur.diagonal d := by
  apply ext_inner_right ℝ
  intro z
  rw [inner_gradient_left, fderiv_S_hsum, real_inner_smul_left]
  simp [real_inner_comm]


theorem integrable_dysonProb (hd : 0 < d) {ρ : ℝ} (hρ : 0 < ρ) {β : ℝ} (hβ : 0 ≤ β)
    {F : CutCur.Rd d → ℝ} (hFm : Measurable F) {M : ℝ} (hF : ∀ x, |F x| ≤ M * (1 + ‖x‖) ^ 2) :
    Integrable F (dysonProb d ρ β) := by
  have h0 := (dysonMeasure_pos (d := d) ρ β nonempty_chamber).ne'
  unfold dysonProb
  refine Integrable.smul_measure ?_ (ENNReal.inv_ne_top.2 h0)
  rw [dysonMeasure_eq, integrable_withDensity_iff_integrable_smul'
    (f := fun x => ENNReal.ofReal (Dlim d ρ β x)) (ENNReal.measurable_ofReal.comp (measurable_Dlim ρ β))
    (Eventually.of_forall fun x => ENNReal.ofReal_lt_top)]
  simpa [ENNReal.toReal_ofReal (Dlim_nonneg ρ β _)] using integrable_Dlim_mul hρ hβ hFm hF

theorem hsum_continuous : Continuous (hsum d) := by
  unfold hsum; exact continuous_finsetSum _ fun i _ => by fun_prop

theorem hsum_bound (x : CutCur.Rd d) : |hsum d x| ≤ d * (1 + ‖x‖) ^ 2 := by
  have := abs_sum_le x
  have hx : ‖x‖ ≤ (1 + ‖x‖) ^ 2 := by nlinarith [norm_nonneg x]
  calc |hsum d x| ≤ d * ‖x‖ := this
    _ ≤ d * (1 + ‖x‖) ^ 2 := mul_le_mul_of_nonneg_left hx (by positivity)

theorem hsum_sq_bound (x : CutCur.Rd d) : |hsum d x ^ 2| ≤ (d * d) * (1 + ‖x‖) ^ 2 := by
  have h1 := abs_sum_le x
  have hx : ‖x‖ ^ 2 ≤ (1 + ‖x‖) ^ 2 := by nlinarith [norm_nonneg x]
  rw [abs_pow]
  calc |hsum d x| ^ 2 ≤ (d * ‖x‖) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h1 2
    _ = (d * d) * ‖x‖ ^ 2 := by ring
    _ ≤ (d * d) * (1 + ‖x‖) ^ 2 := mul_le_mul_of_nonneg_left hx (by positivity)

section Main
variable (hd : 0 < d) {ρ : ℝ} (hρ : 0 < ρ) {β : ℝ} (hβ : 0 ≤ β)
include hd hρ hβ

theorem hsum_integrable : Integrable (hsum d) (dysonProb d ρ β) :=
  integrable_dysonProb hd hρ hβ hsum_continuous.measurable hsum_bound

theorem hsum_sq_integrable : Integrable (fun x => hsum d x ^ 2) (dysonProb d ρ β) :=
  integrable_dysonProb hd hρ hβ (hsum_continuous.pow 2).measurable hsum_sq_bound

theorem hsum_memLp : MemLp (hsum d) 2 (dysonProb d ρ β) := by
  have := isProbabilityMeasure_dysonProb hd hρ hβ
  exact (memLp_two_iff_integrable_sq hsum_continuous.aestronglyMeasurable).2
    (hsum_sq_integrable hd hρ hβ)

/-- The first moment of `h` vanishes. -/
theorem hsum_mean : ∫ x, hsum d x ∂dysonProb d ρ β = 0 := by
  have hφ : CutCur.IsTestFunction (fun _ : CutCur.Rd d => (1 : ℝ)) :=
    ⟨contDiff_const, ⟨1, fun x => by simp⟩, ⟨0, LipschitzWith.const 1⟩⟩
  have := dyson_neumann hd hρ hβ hφ
  simp only [gradient_fun_const, inner_zero_right, integral_zero, mul_one] at this
  have hρ0 : ρ ≠ 0 := hρ.ne'
  have h2 : ∫ x, ∑ i, x i ∂dysonProb d ρ β = 0 := by
    rcases mul_eq_zero.1 this.symm with h | h
    · exact absurd h hρ0
    · exact h
  exact h2

omit hd hρ hβ in
theorem tendsto_dS (r : ℝ) :
    Tendsto (fun n : ℕ => 1 / (1 + (r / ((n : ℝ) + 1)) ^ 2)) atTop (𝓝 1) := by
  have h0 : Tendsto (fun n : ℕ => r / ((n : ℝ) + 1)) atTop (𝓝 0) := by
    simpa [div_eq_mul_inv] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul r |>.congr fun n => by
        simp [div_eq_mul_inv]
  have := ((h0.pow 2).const_add 1).inv₀ (by norm_num)
  simpa [one_div] using this

/-- `ρ ∫ h² dμ = d`: the Rayleigh quotient of `h` is exactly `ρ`. -/
theorem hsum_second_moment :
    ρ * ∫ x, hsum d x ^ 2 ∂dysonProb d ρ β = d := by
  have := isProbabilityMeasure_dysonProb hd hρ hβ
  have hN (n : ℕ) := dyson_neumann hd hρ hβ (isTestFunction_S_hsum (d := d) n)
  have hgradh : ∀ x : CutCur.Rd d, gradient (fun y : CutCur.Rd d => ∑ i, y i) x = CutCur.diagonal d := Paper.gradient_sum
  have hLHS (n : ℕ) : ∫ x, inner ℝ (gradient (fun y : CutCur.Rd d => ∑ i, y i) x)
      (gradient (fun x : CutCur.Rd d => CutoffRigidity.smoothNormalTruncation n (hsum d x)) x) ∂dysonProb d ρ β =
      ∫ x, (d : ℝ) * (1 / (1 + (hsum d x / ((n : ℝ) + 1)) ^ 2)) ∂dysonProb d ρ β := by
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [hgradh, gradient_S_hsum, real_inner_smul_right]
    have : inner ℝ (CutCur.diagonal d) (CutCur.diagonal d) = (d : ℝ) := by
      rw [real_inner_self_eq_norm_sq, Paper.norm_sq_diagonal]
    rw [this]; ring
  -- left limit
  have tL : Tendsto (fun n : ℕ => ∫ x, (d : ℝ) * (1 / (1 + (hsum d x / ((n : ℝ) + 1)) ^ 2)) ∂dysonProb d ρ β)
      atTop (𝓝 (∫ x, (d : ℝ) * 1 ∂dysonProb d ρ β)) := by
    refine tendsto_integral_of_dominated_convergence (fun _ => (d : ℝ)) (fun n => ?_)
      (integrable_const _) (fun n => Eventually.of_forall fun x => ?_)
      (Eventually.of_forall fun x => (tendsto_dS (hsum d x)).const_mul (d : ℝ))
    · refine (Measurable.const_mul ?_ _).aestronglyMeasurable
      have : Continuous fun x : CutCur.Rd d => 1 / (1 + (hsum d x / ((n : ℝ) + 1)) ^ 2) :=
        continuous_const.div (continuous_const.add ((hsum_continuous.div_const _).pow 2))
          fun x => by positivity
      exact this.measurable
    · have h1 : 0 ≤ 1 / (1 + (hsum d x / ((n : ℝ) + 1)) ^ 2) := by positivity
      have h2 : 1 / (1 + (hsum d x / ((n : ℝ) + 1)) ^ 2) ≤ 1 := by
        rw [div_le_one (by positivity)]; nlinarith [sq_nonneg (hsum d x / ((n : ℝ) + 1))]
      rw [norm_mul, Real.norm_of_nonneg h1, Real.norm_of_nonneg (by positivity : (0 : ℝ) ≤ d)]
      calc (d : ℝ) * (1 / (1 + (hsum d x / ((n : ℝ) + 1)) ^ 2)) ≤ d * 1 := by gcongr
        _ = d := mul_one _
  -- right limit
  have tR : Tendsto (fun n : ℕ => ρ * ∫ x, (∑ i, x i) * CutoffRigidity.smoothNormalTruncation n (hsum d x) ∂dysonProb d ρ β)
      atTop (𝓝 (ρ * ∫ x, hsum d x ^ 2 ∂dysonProb d ρ β)) := by
    refine Tendsto.const_mul ρ (tendsto_integral_of_dominated_convergence (fun x => hsum d x ^ 2) (fun n => ?_)
      (hsum_sq_integrable hd hρ hβ) (fun n => Eventually.of_forall fun x => ?_)
      (Eventually.of_forall fun x => ?_))
    · exact (hsum_continuous.mul ((contDiff_S n).continuous.comp hsum_continuous)).aestronglyMeasurable
    · have h1 := CutoffRigidity.smoothNormalTruncation_abs_le n (hsum d x)
      rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, sq]
      show |hsum d x| * _ ≤ _
      exact (mul_le_mul_of_nonneg_left h1 (abs_nonneg _)).trans (le_of_eq (abs_mul_abs_self _))
    · have := (CutoffRigidity.tendsto_smoothNormalTruncation (hsum d x)).const_mul (hsum d x)
      rw [← sq] at this
      exact this
  have heq : ∀ n : ℕ, ∫ x, (d : ℝ) * (1 / (1 + (hsum d x / ((n : ℝ) + 1)) ^ 2)) ∂dysonProb d ρ β =
      ρ * ∫ x, (∑ i, x i) * CutoffRigidity.smoothNormalTruncation n (hsum d x) ∂dysonProb d ρ β := by
    intro n
    rw [← hLHS n]
    exact hN n
  have := tendsto_nhds_unique tL (tR.congr fun n => (heq n).symm)
  simpa using this.symm

theorem hsum_variance : variance (hsum d) (dysonProb d ρ β) = d / ρ := by
  have := isProbabilityMeasure_dysonProb hd hρ hβ
  rw [variance_eq_sub (hsum_memLp hd hρ hβ)]
  simp only [Pi.pow_apply]
  rw [hsum_mean hd hρ hβ]
  have := hsum_second_moment hd hρ hβ
  field_simp
  linarith

omit hd hρ hβ in
theorem gradient_hsum_sq (x : CutCur.Rd d) : ‖gradient (hsum d) x‖ ^ 2 = d := by
  have : gradient (hsum d) x = CutCur.diagonal d := Paper.gradient_sum x
  rw [this, Paper.norm_sq_diagonal]

/-- Every valid Poincaré constant on test functions is at least `1/ρ`. -/
theorem inv_le_of_poincare {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ f : CutCur.Rd d → ℝ, CutCur.IsTestFunction f →
      variance f (dysonProb d ρ β) ≤ C * ∫ x, ‖gradient f x‖ ^ 2 ∂dysonProb d ρ β) :
    ρ⁻¹ ≤ C := by
  have := isProbabilityMeasure_dysonProb hd hρ hβ
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  set S := fun n : ℕ => fun x : CutCur.Rd d => CutoffRigidity.smoothNormalTruncation n (hsum d x) with hS
  have hSc (n : ℕ) : Continuous (S n) := (contDiff_S n).continuous.comp hsum_continuous
  -- variance of the truncations
  have hvar (n : ℕ) : variance (S n) (dysonProb d ρ β) =
      (∫ x, S n x ^ 2 ∂dysonProb d ρ β) - (∫ x, S n x ∂dysonProb d ρ β) ^ 2 := by
    obtain ⟨M, hM⟩ := (isTestFunction_S_hsum (d := d) n).2.1
    have hm : MemLp (S n) 2 (dysonProb d ρ β) :=
      memLp_of_bounded (a := -M) (b := M) (Eventually.of_forall fun x => by
        rw [Set.mem_Icc, ← abs_le]; exact hM x) (hSc n).aestronglyMeasurable 2
    rw [variance_eq_sub hm]; rfl
  have t2 : Tendsto (fun n => ∫ x, S n x ^ 2 ∂dysonProb d ρ β) atTop
      (𝓝 (∫ x, hsum d x ^ 2 ∂dysonProb d ρ β)) := by
    refine tendsto_integral_of_dominated_convergence (fun x => hsum d x ^ 2) (fun n => ?_)
      (hsum_sq_integrable hd hρ hβ) (fun n => Eventually.of_forall fun x => ?_)
      (Eventually.of_forall fun x => ?_)
    · exact ((hSc n).pow 2).aestronglyMeasurable
    · have h1 := CutoffRigidity.smoothNormalTruncation_abs_le n (hsum d x)
      rw [Real.norm_eq_abs, abs_pow]
      calc |S n x| ^ 2 ≤ |hsum d x| ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h1 2
        _ = hsum d x ^ 2 := sq_abs _
    · exact (CutoffRigidity.tendsto_smoothNormalTruncation (hsum d x)).pow 2
  have t1 : Tendsto (fun n => ∫ x, S n x ∂dysonProb d ρ β) atTop (𝓝 (∫ x, hsum d x ∂dysonProb d ρ β)) := by
    refine tendsto_integral_of_dominated_convergence (fun x => |hsum d x|) (fun n => (hSc n).aestronglyMeasurable)
      (hsum_integrable hd hρ hβ).abs (fun n => Eventually.of_forall fun x => ?_)
      (Eventually.of_forall fun x => CutoffRigidity.tendsto_smoothNormalTruncation (hsum d x))
    rw [Real.norm_eq_abs]
    exact CutoffRigidity.smoothNormalTruncation_abs_le n (hsum d x)
  have tv : Tendsto (fun n => variance (S n) (dysonProb d ρ β)) atTop (𝓝 (d / ρ)) := by
    have := t2.sub (t1.pow 2)
    rw [hsum_mean hd hρ hβ] at this
    have e := hsum_second_moment hd hρ hβ
    have e2 : ∫ x, hsum d x ^ 2 ∂dysonProb d ρ β = d / ρ := by field_simp; linarith
    rw [e2] at this
    simpa [hvar] using this
  have hbound (n : ℕ) : variance (S n) (dysonProb d ρ β) ≤ C * d := by
    refine (hC _ (isTestFunction_S_hsum n)).trans ?_
    refine mul_le_mul_of_nonneg_left ?_ ?_
    · calc ∫ x, ‖gradient (S n) x‖ ^ 2 ∂dysonProb d ρ β ≤ ∫ _x, (d : ℝ) ∂dysonProb d ρ β := by
            refine integral_mono ((isTestFunction_S_hsum (d := d) n).integrable_gradient_sq _)
              (integrable_const _) fun x => ?_
            show ‖gradient (fun x => CutoffRigidity.smoothNormalTruncation n (hsum d x)) x‖ ^ 2 ≤ d
            rw [gradient_S_hsum, norm_smul, mul_pow]
            have h1 : 0 ≤ 1 / (1 + (hsum d x / ((n : ℝ) + 1)) ^ 2) := by positivity
            have h2 : 1 / (1 + (hsum d x / ((n : ℝ) + 1)) ^ 2) ≤ 1 := by
              rw [div_le_one (by positivity)]; nlinarith [sq_nonneg (hsum d x / ((n : ℝ) + 1))]
            have h3 : ‖(1 / (1 + (hsum d x / ((n : ℝ) + 1)) ^ 2))‖ ^ 2 ≤ 1 := by
              rw [Real.norm_of_nonneg h1]; nlinarith
            have h4 : ‖CutCur.diagonal d‖ ^ 2 = d := Paper.norm_sq_diagonal
            rw [h4]; nlinarith
        _ = d := by simp
    · exact hC0
  have hlim := le_of_tendsto' tv hbound
  have : (d : ℝ) / ρ ≤ C * d := hlim
  rw [div_le_iff₀ hρ] at this
  rw [inv_eq_one_div, div_le_iff₀ hρ]
  nlinarith

end Main

end CutoffRigidity.Dyson
