module
public import CutoffRigidity.LangevinSquareEvolution
public import CutoffRigidity.LangevinEntropyInterpolation
public import CutoffRigidity.L2PointwiseEvolution

/-! # Genuine variance interpolation for the Langevin transition

The backward square lies in the actual generator graph. Its time derivative
cancels the backward generator part, leaving twice the heat-averaged gradient
energy. No twice differentiable transition density is assumed.
-/
public section
namespace CutoffRigidity
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal
variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}

set_option maxHeartbeats 700000 in
theorem hasDerivAt_langevin_square_interpolation
    {B : NNReal → Ω → (EuclideanSpace ℝ (Fin d))} {P : Measure Ω} (hB : IsEuclideanBrownian B P)
    {V g : (EuclideanSpace ℝ (Fin d)) → ℝ} (hV : ContDiff ℝ 2 V)
    (hp : IsProbabilityMeasure (gibbsMeasure volume V))
    (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g)
    (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : (EuclideanSpace ℝ (Fin d)), ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (T s : ℝ) (hs : 0 < s) (hsT : s < T) :
    letI := hp
    HasDerivAt (fun r : ℝ =>
      langevinL2Operator hB hV hp ρ hρ hHess r.toNNReal
        (langevinSquareProfileLp hB hV hg hgc ρ hρ hHess (gibbsMeasure volume V) (T-r)))
      ((2 : ℝ) • langevinL2Operator hB hV hp ρ hρ hHess s.toNNReal
        (langevinGradientSqProfileLp hB hV hg hgc ρ hρ hHess (gibbsMeasure volume V) (T-s))) s := by
  let := hp
  let μ := gibbsMeasure volume V
  let S := fun r : ℝ => langevinL2Operator hB hV hp ρ hρ hHess r.toNNReal
  let v := fun r : ℝ => langevinSquareProfileLp hB hV hg hgc ρ hρ hHess μ (T-r)
  let D := langevinSquareProfileDerivativeLp hB hV hg hgc ρ hρ hHess μ (T-s)
  let I := langevinGradientSqProfileLp hB hV hg hgc ρ hρ hHess μ (T-s)
  have hv : HasDerivAt v (-D) s := by
    have hh := (hasDerivAt_langevinSquareProfileLp hB hV hg hgc ρ hρ hHess μ (sub_pos.mpr hsT)).scomp s
      ((hasDerivAt_id s).const_sub T)
    simpa only [Function.comp_def, neg_smul, one_smul] using hh
  have hgraph : (v s, -(D + (2 : ℝ) • I)) ∈ (gibbsPositiveGenerator hV hp).graph :=
    langevinSquareProfileLp_mem_operatorGraph hB hV hg hgc ρ hρ hHess hp (T-s)
  have hw : HasDerivAt (fun r => S r (v s)) (-S s (-(D + (2 : ℝ) • I))) s := by
    simpa only [S, langevinL2Operator_eq_gibbsHeatSemigroup] using
      gibbsHeatSemigroup_hasDerivAt_operatorGraph hV hp ρ hρ hHess s hs (v s) (-(D + (2 : ℝ) • I)) hgraph
  have hh := hasDerivAt_strongOperator_apply_moving S 1
    (fun w => (continuous_langevinL2Operator_apply hB hV hp ρ hρ hHess w).comp continuous_real_toNNReal)
    (fun r => norm_langevinL2Operator_le_one hB hV hp ρ hρ hHess r.toNNReal)
    v (-D) (-S s (-(D + (2 : ℝ) • I))) s hv hw
  have hcancel : S s (-D) + -S s (-(D + (2 : ℝ) • I)) = (2 : ℝ) • S s I := by
    simp only [map_neg, map_add, map_smul, neg_neg]
    abel
  rw [hcancel] at hh
  exact hh

@[expose] noncomputable def langevinSquareInterpolation (V g : (EuclideanSpace ℝ (Fin d)) → ℝ)
    (B : NNReal → Ω → (EuclideanSpace ℝ (Fin d))) (P : Measure Ω) (T s : ℝ) (x : (EuclideanSpace ℝ (Fin d))) : ℝ :=
  ∫ y, langevinSquareProfile V g B P (T-s) y ∂langevinKernel V B P s.toNNReal x

@[expose] noncomputable def langevinMovingGradientSqAverage (V g : (EuclideanSpace ℝ (Fin d)) → ℝ)
    (B : NNReal → Ω → (EuclideanSpace ℝ (Fin d))) (P : Measure Ω) (T s : ℝ) (x : (EuclideanSpace ℝ (Fin d))) : ℝ :=
  2 * ∫ y, langevinGradientSqProfile V g B P (T-s) y ∂langevinKernel V B P s.toNNReal x


section Continuity
variable {B : NNReal → Ω → (EuclideanSpace ℝ (Fin d))} {P : Measure Ω} (hB : IsEuclideanBrownian B P)
    {V g : (EuclideanSpace ℝ (Fin d)) → ℝ} (hV : ContDiff ℝ 2 V)
    (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g)
    (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : (EuclideanSpace ℝ (Fin d)), ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)

include hB hV hg hgc hρ hHess in
theorem langevinGradientSqProfile_uniform_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r x, ‖langevinGradientSqProfile V g B P r x‖ ≤ C := by
  obtain ⟨L,hLip⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hgc hg (by norm_num)
  refine ⟨(L : ℝ)^2, sq_nonneg _, ?_⟩
  intro r x
  have hl := lipschitzWith_langevinKernel_integral hB hV ρ hρ.le hHess
    (hg.of_le (by norm_num)) hgc hLip r.toNNReal
  change ‖‖gradient (fun z => ∫ y, g y ∂langevinKernel V B P r.toNNReal z) x‖^2‖ ≤ _
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  apply pow_le_pow_left₀ (norm_nonneg _) _ 2
  rw [show ‖gradient (fun z => ∫ y, g y ∂langevinKernel V B P r.toNNReal z) x‖ =
    ‖fderiv ℝ (fun z => ∫ y, g y ∂langevinKernel V B P r.toNNReal z) x‖ from
      (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin d))).symm.norm_map _]
  exact (norm_fderiv_le_of_lipschitz ℝ hl).trans
    (mul_le_of_le_one_left L.coe_nonneg (Real.exp_le_one_iff.mpr
      (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hρ.le) r.toNNReal.property)))

include hB hV hg hgc hρ hHess in
theorem continuous_langevinSquareInterpolation (T : ℝ) :
    Continuous (fun p : ℝ × (EuclideanSpace ℝ (Fin d)) => langevinSquareInterpolation V g B P T p.1 p.2) := by
  obtain ⟨M,hM0,hM⟩ := compact_continuous_norm_bound hg.continuous hgc
  have hq := (continuous_langevinKernel_integral_time_initial hB hV hg.continuous
    ⟨M,hM⟩ ρ hρ.le hHess).comp
      ((continuous_real_toNNReal.comp continuous_fst).prodMk continuous_snd)
  have hsq : Continuous (Function.uncurry (langevinSquareProfile V g B P)) := hq.pow 2
  have hb (r : ℝ) (x : (EuclideanSpace ℝ (Fin d))) : ‖langevinSquareProfile V g B P r x‖ ≤ M^2 := by
    change ‖(∫ y, g y ∂langevinKernel V B P r.toNNReal x)^2‖ ≤ _
    rw [norm_pow]
    exact pow_le_pow_left₀ (norm_nonneg _)
      (langevinKernel_integral_compact_test_norm_le hB hV ρ hρ.le hHess hM r.toNNReal x) 2
  exact (continuous_langevinKernel_integral_moving_bounded hB hV ρ hρ.le hHess
    _ hsq (M^2) hb).comp
      ((continuous_const.sub continuous_fst).prodMk
        ((continuous_real_toNNReal.comp continuous_fst).prodMk continuous_snd))

include hB hV hg hgc hρ hHess in
theorem continuous_langevinMovingGradientSqAverage (T : ℝ) :
    Continuous (fun p : ℝ × (EuclideanSpace ℝ (Fin d)) => langevinMovingGradientSqAverage V g B P T p.1 p.2) := by
  have hgJoint : Continuous (Function.uncurry (langevinGradientSqProfile V g B P)) :=
    ((continuous_gradient_langevinKernel_integral_time_initial hB hV ρ hρ.le hHess
      (hg.of_le (by norm_num)) hgc).comp
      ((continuous_real_toNNReal.comp continuous_fst).prodMk continuous_snd)).norm.pow 2
  obtain ⟨C,hC0,hC⟩ := langevinGradientSqProfile_uniform_bound hB hV hg hgc ρ hρ hHess
  exact ((continuous_langevinKernel_integral_moving_bounded hB hV ρ hρ.le hHess
    _ hgJoint C hC).comp
      ((continuous_const.sub continuous_fst).prodMk
        ((continuous_real_toNNReal.comp continuous_fst).prodMk continuous_snd))).const_mul 2

include hB hV hg hgc hρ hHess in
theorem langevinMovingGradientSqAverage_uniform_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T s x, ‖langevinMovingGradientSqAverage V g B P T s x‖ ≤ C := by
  obtain ⟨C,hC0,hC⟩ := langevinGradientSqProfile_uniform_bound hB hV hg hgc ρ hρ hHess
  refine ⟨2*C, by positivity, ?_⟩
  intro T s x
  change ‖2 * ∫ y, langevinGradientSqProfile V g B P (T-s) y ∂langevinKernel V B P s.toNNReal x‖ ≤ _
  rw [norm_mul, Real.norm_of_nonneg (by norm_num : 0 ≤ (2 : ℝ))]
  exact mul_le_mul_of_nonneg_left
    (langevinKernel_integral_compact_test_norm_le hB hV ρ hρ.le hHess (hC (T-s)) s.toNNReal x) (by norm_num)
end Continuity


set_option maxHeartbeats 900000 in
/-- The actual variance interpolation identity holds at every initial point,
not merely as an almost-everywhere Hilbert-space statement. -/
theorem hasDerivAt_langevin_square_interpolation_pointwise
    {B : NNReal → Ω → (EuclideanSpace ℝ (Fin d))} {P : Measure Ω} (hB : IsEuclideanBrownian B P)
    {V g : (EuclideanSpace ℝ (Fin d)) → ℝ} (hV : ContDiff ℝ 2 V)
    (hp : IsProbabilityMeasure (gibbsMeasure volume V))
    (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g)
    (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : (EuclideanSpace ℝ (Fin d)), ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (T s : ℝ) (hs : 0 < s) (hsT : s < T) (x : (EuclideanSpace ℝ (Fin d))) :
    HasDerivAt (fun r => langevinSquareInterpolation V g B P T r x)
      (langevinMovingGradientSqAverage V g B P T s x) s := by
  let := hp
  let μ := gibbsMeasure volume V
  let : μ.IsOpenPosMeasure := gibbsMeasure_isOpenPosMeasure volume hV.continuous.measurable
  let U := fun r : ℝ => langevinL2Operator hB hV hp ρ hρ hHess r.toNNReal
    (langevinSquareProfileLp hB hV hg hgc ρ hρ hHess μ (T-r))
  let D := fun r : ℝ => (2 : ℝ) • langevinL2Operator hB hV hp ρ hρ hHess r.toNNReal
    (langevinGradientSqProfileLp hB hV hg hgc ρ hρ hHess μ (T-r))
  let F := langevinSquareInterpolation V g B P T
  let G := langevinMovingGradientSqAverage V g B P T
  have hU (r : ℝ) : U r =ᵐ[μ] F r := by
    have hmem := langevinSquareProfile_memLp hB hV hg hgc ρ hρ hHess μ (T-r)
    exact (langevinL2Operator_coeFn hB hV hp ρ hρ hHess r.toNNReal (hmem.toLp _)).trans
      (invariantKernel_integral_congr_ae (langevinKernel V B P r.toNNReal)
        (langevinKernel_gibbs_invariant hB hV hp ρ hρ hHess r.toNNReal) hmem.coeFn_toLp)
  have hD (r : ℝ) : D r =ᵐ[μ] G r := by
    have hmem := langevinGradientSqProfile_memLp hB hV hg hgc ρ hρ hHess μ (T-r)
    have he := (langevinL2Operator_coeFn hB hV hp ρ hρ hHess r.toNNReal (hmem.toLp _)).trans
      (invariantKernel_integral_congr_ae (langevinKernel V B P r.toNNReal)
        (langevinKernel_gibbs_invariant hB hV hp ρ hρ hHess r.toNNReal) hmem.coeFn_toLp)
    filter_upwards [Lp.coeFn_smul (2 : ℝ) (langevinL2Operator hB hV hp ρ hρ hHess r.toNNReal (hmem.toLp _)), he]
      with y hsm he
    change (((2 : ℝ) • langevinL2Operator hB hV hp ρ hρ hHess r.toNNReal (hmem.toLp _)) : (EuclideanSpace ℝ (Fin d)) →₂[μ] ℝ) y = _
    rw [hsm, Pi.smul_apply, smul_eq_mul, he]
    rfl
  have hGjoint : Continuous (Function.uncurry G) :=
    continuous_langevinMovingGradientSqAverage hB hV hg hgc ρ hρ hHess T
  obtain ⟨C,hC0,hC⟩ := langevinMovingGradientSqAverage_uniform_bound hB hV hg hgc ρ hρ hHess
  have hGc (r : ℝ) : Continuous (G r) := hGjoint.comp (continuous_const.prodMk continuous_id)
  have hGt (y : (EuclideanSpace ℝ (Fin d))) : Continuous (fun r => G r y) := hGjoint.comp (continuous_id.prodMk continuous_const)
  have hDc : Continuous D := continuous_L2_of_bounded_representatives μ D G hGc hGt hD C hC0 (hC T)
  have hFjoint : Continuous (Function.uncurry F) :=
    continuous_langevinSquareInterpolation hB hV hg hgc ρ hρ hHess T
  exact hasDerivAt_of_L2_deriv_continuous_representatives μ U D F G ⟨hs,hsT⟩
    (fun r hr => hasDerivAt_langevin_square_interpolation hB hV hp hg hgc ρ hρ hHess T r hr.1 hr.2)
    hDc (fun r => hFjoint.comp (continuous_const.prodMk continuous_id)) hGc hGt
    hGjoint.stronglyMeasurable hU hD C hC0 (hC T) x

end CutoffRigidity
