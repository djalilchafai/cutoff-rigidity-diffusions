module

public import CutoffRigidity.LangevinFlow
public import CutoffRigidity.CurvatureMonotonicity

/-! # Actual finite-difference variational equations for Langevin paths

C² potentials supply a continuous spatial linearization. The actual
fixed-noise solution increments solve the exact integral equation with the
averaged Hessian along their segment. Linearized trajectories satisfy the
source exponential bound. No differentiability of the solution map is a
hypothesis or a conclusion of this preparatory module.
-/

public section

namespace CutoffRigidity

open MeasureTheory Set Filter
open scoped Topology NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The actual gradient of a C² potential is C¹. -/
theorem contDiff_one_gradient_of_contDiff_two {V : E → ℝ} (hV : ContDiff ℝ 2 V) :
    ContDiff ℝ 1 (gradient V) := by
  let R : (E →L[ℝ] ℝ) →L[ℝ] E :=
    (InnerProductSpace.toDual ℝ E).symm.toContinuousLinearEquiv.toContinuousLinearMap
  exact R.contDiff.comp (hV.fderiv_right (m := 1) (by norm_num))

/-- The exact averaged Hessian acting on initial-point differences. -/
@[expose] noncomputable def averagedGradientDerivative (V : E → ℝ) (a b : E) : E →L[ℝ] E :=
  ∫ θ : ℝ in 0..1, fderiv ℝ (gradient V) (a + θ • (b - a))

/-- The gradient finite increment is the actual averaged Hessian applied
to the increment, by the fundamental theorem of calculus along its segment. -/
theorem gradient_sub_eq_averagedGradientDerivative {V : E → ℝ}
    (hV : ContDiff ℝ 2 V) (a b : E) :
    gradient V b - gradient V a = averagedGradientDerivative V a b (b - a) := by
  have hG := contDiff_one_gradient_of_contDiff_two hV
  have hc : Continuous (fun θ : ℝ => fderiv ℝ (gradient V) (a + θ • (b - a))) :=
    (hG.continuous_fderiv one_ne_zero).comp (continuous_const.add (continuous_id.smul continuous_const))
  have hd (θ : ℝ) : HasDerivAt (fun r : ℝ => gradient V (a + r • (b - a)))
      (fderiv ℝ (gradient V) (a + θ • (b - a)) (b - a)) θ := by
    simpa only [Function.comp_def, id_eq, one_smul] using
      (hG.differentiable one_ne_zero (a + θ • (b - a))).hasFDerivAt.comp_hasDerivAt θ
        (((hasDerivAt_id θ).smul_const (b - a)).const_add a)
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun θ _ => hd θ)
    ((hc.clm_apply continuous_const).intervalIntegrable 0 1)
  rw [averagedGradientDerivative, ContinuousLinearMap.intervalIntegral_apply (hc.intervalIntegrable 0 1)]
  simpa only [one_smul, zero_smul, add_zero, add_sub_cancel] using hi.symm

/-- The actual continuous-noise solution increment satisfies an exact
linear equation with the averaged spatial derivative, without any assumed
initial-point derivative of the solution map. -/
theorem langevinSolution_initial_increment_variational_integral [FiniteDimensional ℝ E]
    {V : E → ℝ} (hV : ContDiff ℝ 2 V) (ρ : ℝ) (hρ : 0 ≤ ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    {w : ℝ → E} (hw : Continuous w) (x h : E) {t : ℝ} (ht : 0 ≤ t) :
    langevinSolution V w (x + h) t - langevinSolution V w x t = h -
      ∫ s in 0..t, averagedGradientDerivative V (langevinSolution V w x s)
        (langevinSolution V w (x + h) s)
        (langevinSolution V w (x + h) s - langevinSolution V w x s) := by
  have hX := langevinSolution_isLangevinPathOn hV ρ hρ hHess hw (x + h) ht
  have hY := langevinSolution_isLangevinPathOn hV ρ hρ hHess hw x ht
  have hh := langevin_same_noise_difference hV hX hY ⟨ht, le_rfl⟩
  rw [add_sub_cancel_left] at hh
  rw [hh]
  congr 1
  apply intervalIntegral.integral_congr
  intro s _
  exact gradient_sub_eq_averagedGradientDerivative hV _ _

/-- Hessian curvature controls every true linearized trajectory. This
estimate concerns the actual variational equation, not a supplied norm bound. -/
theorem linearized_langevin_norm_bound {V : E → ℝ} (hV : ContDiff ℝ 2 V)
    (ρ : ℝ) (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (X Z : ℝ → E) {t : ℝ} (ht : 0 ≤ t)
    (hc : ContinuousOn Z (Icc 0 t))
    (hD : ∀ s ∈ Ioo 0 t, HasDerivAt Z (-fderiv ℝ (gradient V) (X s) (Z s)) s) :
    ‖Z t‖ ≤ Real.exp (-ρ * t) * ‖Z 0‖ := by
  apply norm_contraction_of_dissipative_derivative ht hc hD
  intro s _
  have hh := hHess (X s) (Z s)
  have hDV := (hV.fderiv_right (m := 1) (by norm_num)).differentiable one_ne_zero
  rw [← inner_fderiv_gradient_apply (hDV (X s))] at hh
  rw [inner_neg_right, real_inner_comm]
  linarith

/-- The actual shifted drift has the actual Hessian as its spatial
linearization for every fixed driving path and time. -/
theorem hasFDerivAt_shifted_langevin_drift {V : E → ℝ} (hV : ContDiff ℝ 2 V)
    (w : ℝ → E) (t : ℝ) (y : E) :
    HasFDerivAt (fun z => -gradient V (z + (w t - w 0)))
      (-fderiv ℝ (gradient V) (y + (w t - w 0))) y := by
  have hh := ((differentiable_gradient_of_contDiff_two hV) (y + (w t - w 0))).hasFDerivAt.comp y
    ((hasFDerivAt_id (𝕜 := ℝ) y).add_const (w t - w 0))
  convert! hh.neg using 1

/-- The genuine spatial linearization along the actual fixed-noise path
is continuous in time on each finite interval. -/
theorem continuousOn_langevinSolution_linearization [FiniteDimensional ℝ E]
    {V : E → ℝ} (hV : ContDiff ℝ 2 V) (ρ : ℝ) (hρ : 0 ≤ ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    {w : ℝ → E} (hw : Continuous w) (x : E) {T : ℝ} (hT : 0 ≤ T) :
    ContinuousOn (fun t => fderiv ℝ (gradient V) (langevinSolution V w x t)) (Icc 0 T) :=
  ((contDiff_one_gradient_of_contDiff_two hV).continuous_fderiv one_ne_zero).comp_continuousOn
    (langevinSolution_isLangevinPathOn hV ρ hρ hHess hw x hT).1

/-- The actual operator-valued variational equation has the source
exponential operator-norm bound, derived from the Hessian lower bound. -/
theorem linearized_langevin_operator_norm_bound {V : E → ℝ} (hV : ContDiff ℝ 2 V)
    (ρ : ℝ) (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (X : ℝ → E) (J : ℝ → E →L[ℝ] E) {t : ℝ} (ht : 0 ≤ t)
    (hJ0 : J 0 = ContinuousLinearMap.id ℝ E)
    (hc : ContinuousOn J (Icc 0 t))
    (hD : ∀ s ∈ Ioo 0 t, HasDerivAt J
      (-(fderiv ℝ (gradient V) (X s)).comp (J s)) s) :
    ‖J t‖ ≤ Real.exp (-ρ * t) := by
  apply ContinuousLinearMap.opNorm_le_bound _ (Real.exp_nonneg _)
  intro z
  have hcont : ContinuousOn (fun s => J s z) (Icc 0 t) := hc.clm_apply continuousOn_const
  have hd (s : ℝ) (hs : s ∈ Ioo 0 t) :
      HasDerivAt (fun r => J r z) (-fderiv ℝ (gradient V) (X s) (J s z)) s := by
    have hh := (hD s hs).clm_apply (hasDerivAt_const s z)
    simpa only [neg_apply, ContinuousLinearMap.comp_apply, map_zero, add_zero] using hh
  have hh := linearized_langevin_norm_bound hV ρ hHess X (fun s => J s z) ht hcont hd
  simpa only [hJ0, ContinuousLinearMap.id_apply] using hh

/-- A continuous actual spatial linearization has a genuine local
operator-valued variational solution, constructed by Picard--Lindelöf.
No solution of the linearized equation is assumed. -/
theorem exists_local_linear_variational_solution
    (A : ℝ → E →L[ℝ] E) {T₀ : ℝ} (hT₀ : 0 < T₀)
    (hA : ContinuousOn A (Icc 0 T₀)) :
    ∃ T : ℝ, 0 < T ∧ T ≤ T₀ ∧ ∃ J : ℝ → E →L[ℝ] E,
      J 0 = ContinuousLinearMap.id ℝ E ∧
      ∀ t ∈ Icc 0 T, HasDerivWithinAt J (-(A t).comp (J t)) (Icc 0 T) t := by
  obtain ⟨K₀, hK₀⟩ := isCompact_Icc.exists_bound_of_continuousOn hA
  let K : ℝ≥0 := ⟨max K₀ 0 + 1, by positivity⟩
  let L : ℝ≥0 := 2 * K
  let T := min T₀ (1 / ((L : ℝ) + 1))
  have hT : 0 < T := lt_min hT₀ (one_div_pos.mpr (by positivity))
  have hTT : T ≤ T₀ := min_le_left _ _
  have hAK (t : ℝ) (ht : t ∈ Icc 0 T) : ‖A t‖ ≤ K := by
    have hh := hK₀ t ⟨ht.1, ht.2.trans hTT⟩
    change ‖A t‖ ≤ max K₀ 0 + 1
    linarith [le_max_left K₀ 0]
  have hPicard : IsPicardLindelof (fun (t : ℝ) (J : E →L[ℝ] E) => -(A t).comp J)
      (tmin := 0) (tmax := T) ⟨0, ⟨le_rfl, hT.le⟩⟩
      (ContinuousLinearMap.id ℝ E) 1 0 L K := by
    constructor
    · intro t ht
      apply LipschitzOnWith.of_dist_le_mul
      intro J _ Q _
      rw [dist_eq_norm, dist_eq_norm]
      calc
        _ = ‖(A t).comp (J - Q)‖ := by
          rw [ContinuousLinearMap.comp_sub, neg_sub_neg, norm_sub_rev]
        _ ≤ ‖A t‖ * ‖J - Q‖ := ContinuousLinearMap.opNorm_comp_le _ _
        _ ≤ (K : ℝ) * ‖J - Q‖ := mul_le_mul_of_nonneg_right (hAK t ht) (norm_nonneg _)
    · intro J _
      exact ((hA.mono (fun t ht => ⟨ht.1, ht.2.trans hTT⟩)).clm_comp continuousOn_const).neg
    · intro t ht J hJ
      have hJdist : ‖J - ContinuousLinearMap.id ℝ E‖ ≤ 1 := by
        simpa only [Metric.mem_closedBall, dist_eq_norm, NNReal.coe_one] using hJ
      have hJn : ‖J‖ ≤ 2 := by
        have hh := norm_le_norm_sub_add J (ContinuousLinearMap.id ℝ E)
        have hid := ContinuousLinearMap.norm_id_le (𝕜 := ℝ) (E := E)
        linarith
      change ‖-(A t).comp J‖ ≤ (L : ℝ)
      rw [norm_neg]
      calc
        _ ≤ ‖A t‖ * ‖J‖ := ContinuousLinearMap.opNorm_comp_le _ _
        _ ≤ (K : ℝ) * 2 := mul_le_mul (hAK t ht) hJn (norm_nonneg _) K.coe_nonneg
        _ = (L : ℝ) := by simp only [L, NNReal.coe_mul, NNReal.coe_ofNat]; ring
    · simp only [sub_zero, max_eq_left hT.le, NNReal.coe_zero, NNReal.coe_one]
      have hh := (le_div_iff₀ (by positivity : (0 : ℝ) < L + 1)).mp (min_le_right T₀ (1 / ((L : ℝ) + 1)))
      change (L : ℝ) * T ≤ 1
      change T * ((L : ℝ) + 1) ≤ 1 at hh
      nlinarith [L.coe_nonneg]
  obtain ⟨J, hJ0, hJD⟩ := hPicard.exists_eq_forall_mem_Icc_hasDerivWithinAt₀
  exact ⟨T, hT, hTT, J, hJ0, hJD⟩

/-- The actual fixed-noise Langevin path admits a genuine local linear
variational evolution, with its operator norm bounded from source curvature.
This constructs the candidate derivative; identifying it as the initial-
point Fréchet derivative still requires the nonlinear remainder argument. -/
theorem exists_langevinSolution_local_linear_variation [FiniteDimensional ℝ E]
    {V : E → ℝ} (hV : ContDiff ℝ 2 V) (ρ : ℝ) (hρ : 0 ≤ ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    {w : ℝ → E} (hw : Continuous w) (x : E) :
    ∃ T : ℝ, 0 < T ∧ ∃ J : ℝ → E →L[ℝ] E,
      J 0 = ContinuousLinearMap.id ℝ E ∧
      (∀ t ∈ Icc 0 T, HasDerivWithinAt J
        (-(fderiv ℝ (gradient V) (langevinSolution V w x t)).comp (J t)) (Icc 0 T) t) ∧
      ∀ t ∈ Icc 0 T, ‖J t‖ ≤ Real.exp (-ρ * t) := by
  let A := fun t => fderiv ℝ (gradient V) (langevinSolution V w x t)
  have hA : ContinuousOn A (Icc 0 1) :=
    continuousOn_langevinSolution_linearization hV ρ hρ hHess hw x (by norm_num)
  obtain ⟨T, hT, _, J, hJ0, hJD⟩ := exists_local_linear_variational_solution A (by norm_num) hA
  refine ⟨T, hT, J, hJ0, hJD, ?_⟩
  have hJC : ContinuousOn J (Icc 0 T) := fun s hs => (hJD s hs).continuousWithinAt
  intro t ht
  apply linearized_langevin_operator_norm_bound hV ρ hHess
    (fun s => langevinSolution V w x s) J ht.1 hJ0
    (hJC.mono (fun s hs => ⟨hs.1, hs.2.trans ht.2⟩))
  intro s hs
  exact (hJD s ⟨hs.1.le, hs.2.le.trans ht.2⟩).hasDerivAt
    (Icc_mem_nhds hs.1 (hs.2.trans_le ht.2))

/-- The true linear variational ODE is equivalent to its required integral
identity on each finite forward interval. -/
theorem linear_variational_integral_eq
    (A : ℝ → E →L[ℝ] E) (J : ℝ → E →L[ℝ] E) {T t : ℝ}
    (hA : ContinuousOn A (Icc 0 T)) (hJ : ContinuousOn J (Icc 0 T))
    (hD : ∀ s ∈ Icc 0 T, HasDerivWithinAt J (-(A s).comp (J s)) (Icc 0 T) s)
    (ht : t ∈ Icc 0 T) :
    J t = J 0 - ∫ s in 0..t, (A s).comp (J s) := by
  have hsub : Icc 0 t ⊆ Icc 0 T := fun s hs => ⟨hs.1, hs.2.trans ht.2⟩
  have hcomp : ContinuousOn (fun s => (A s).comp (J s)) (Icc 0 t) :=
    (hA.mono hsub).clm_comp (hJ.mono hsub)
  have hh := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ht.1 (hJ.mono hsub)
    (fun s hs => (hD s ⟨hs.1.le, hs.2.le.trans ht.2⟩).hasDerivAt
      (Icc_mem_nhds hs.1 (hs.2.trans_le ht.2)))
    (hcomp.neg.intervalIntegrable_of_Icc ht.1)
  rw [intervalIntegral.integral_neg] at hh
  have he := (eq_sub_iff_add_eq.mp hh).symm
  simpa only [sub_eq_add_neg, add_comm] using he

end CutoffRigidity
