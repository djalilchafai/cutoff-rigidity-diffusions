module
public import CutoffRigidity.LangevinJointGradientContinuity
public import CutoffRigidity.LangevinEntropyInterpolation

/-! # Joint continuity and bounds for the actual BGL01 score interpolation

Actual variational-flow derivatives and dominated probability integration
supply joint time/state gradient continuity. The positive logarithmic
profile and its moving heat-averaged score consequently have the true
continuous bounded representatives needed for the pointwise FTC upgrade.
-/
public section
namespace CutoffRigidity
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal
variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

set_option maxHeartbeats 650000 in
/-- Actual compact C¹ transition derivatives are jointly continuous in
nonnegative time and initial point, under any continuous-noise probability. -/
theorem continuous_fderiv_langevinNoiseAverage_time_initial
    {V g : E → ℝ} (hV : ContDiff ℝ 2 V) (ρ : ℝ) (hρ : 0 ≤ ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (hg : ContDiff ℝ 1 g) (hgc : HasCompactSupport g)
    (μ : Measure C(ℝ, E)) [IsProbabilityMeasure μ] :
    Continuous (fun p : NNReal × E =>
      fderiv ℝ (fun y => ∫ w : C(ℝ, E), g (langevinSolution V w y p.1) ∂μ) p.2) := by
  let D (p : NNReal × E) (w : C(ℝ, E)) :=
    fderiv ℝ (fun z => g (langevinSolution V w z p.1)) p.2
  have hDI (p : NNReal × E) : Integrable (D p) μ ∧
      HasFDerivAt (fun y => ∫ w : C(ℝ, E), g (langevinSolution V w y p.1) ∂μ)
        (∫ w, D p w ∂μ) p.2 :=
    hasFDerivAt_langevinNoiseAverage hV ρ hρ hHess hg hgc μ p.1 p.2
  have hDcont (w : C(ℝ, E)) : Continuous (fun p => D p w) := by
    have he (p : NNReal × E) : D p w =
        (fderiv ℝ g (langevinSolution V w p.2 p.1)).comp
          (fderiv ℝ (fun y => langevinSolution V w y p.1) p.2) := by
      exact ((hg.differentiable one_ne_zero _).hasFDerivAt.comp p.2
        (differentiable_langevinSolution_initial_point hV ρ hρ hHess w.continuous p.1.property p.2).hasFDerivAt).fderiv
    simp_rw [he]
    exact ((hg.continuous_fderiv one_ne_zero).comp
      (continuous_langevinSolution_time_initial hV ρ hρ hHess w)).clm_comp
        (continuous_fderiv_langevinSolution_time_initial hV ρ hρ hHess w)
  obtain ⟨L, hLip⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hgc hg (by norm_num)
  have hDB (p : NNReal × E) (w : C(ℝ, E)) : ‖D p w‖ ≤ L := by
    have hh := norm_fderiv_le_of_lipschitz ℝ (x₀ := p.2)
      (hLip.comp (langevinSolution_initial_point_lipschitz hV ρ hρ hHess w.continuous p.1.property))
    apply hh.trans
    change (L : ℝ) * Real.exp (-ρ * p.1) ≤ L
    exact mul_le_of_le_one_right L.coe_nonneg (Real.exp_le_one_iff.mpr
      (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hρ) p.1.property))
  have he : (fun p : NNReal × E =>
      fderiv ℝ (fun y => ∫ w : C(ℝ, E), g (langevinSolution V w y p.1) ∂μ) p.2) =
      fun p => ∫ w, D p w ∂μ := funext (fun p => (hDI p).2.fderiv)
  rw [he]
  apply continuous_iff_continuousAt.mpr
  intro p
  exact tendsto_integral_filter_of_dominated_convergence (fun _ : C(ℝ, E) => (L : ℝ))
    (Eventually.of_forall (fun q => (hDI q).1.aestronglyMeasurable))
    (Eventually.of_forall (fun q => Eventually.of_forall (hDB q))) (integrable_const _)
    (Eventually.of_forall (fun w => (hDcont w).tendsto p))


/-- Actual kernel gradients inherit joint continuity from the genuine
Brownian noise-law derivative representation. -/
theorem continuous_gradient_langevinKernel_integral_time_initial
    {Ω : Type*} [MeasurableSpace Ω] {B : NNReal → Ω → E} {P : Measure Ω}
    (hB : IsEuclideanBrownian B P)
    {V g : E → ℝ} (hV : ContDiff ℝ 2 V) (ρ : ℝ) (hρ : 0 ≤ ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (hg : ContDiff ℝ 1 g) (hgc : HasCompactSupport g) :
    Continuous (fun p : NNReal × E =>
      gradient (fun y => ∫ z, g z ∂langevinKernel V B P p.1 y) p.2) := by
  let := brownianNoiseLaw_isProbabilityMeasure hB
  have he (t : NNReal) : (fun y => ∫ z, g z ∂langevinKernel V B P t y) =
      (fun y => ∫ w : C(ℝ, E), g (langevinSolution V w y t) ∂brownianNoiseLaw B P) := by
    funext y
    rw [langevinKernel_apply_noiseLaw hB hV ρ hρ hHess]
    exact integral_map (((langevinSolution_evaluation_continuous hV ρ hρ hHess t.property).comp
      (continuous_const.prodMk continuous_id)).measurable.aemeasurable)
      hg.continuous.measurable.aestronglyMeasurable
  simp_rw [he]
  exact (InnerProductSpace.toDual ℝ E).symm.continuous.comp
    (continuous_fderiv_langevinNoiseAverage_time_initial hV ρ hρ hHess hg hgc (brownianNoiseLaw B P))

/-- A jointly continuous uniformly bounded moving integrand has jointly
continuous actual Langevin expectations, including at time zero. -/
theorem continuous_langevinKernel_integral_moving_bounded
    {Ω : Type*} [MeasurableSpace Ω] {B : NNReal → Ω → E} {P : Measure Ω}
    (hB : IsEuclideanBrownian B P)
    {V : E → ℝ} (hV : ContDiff ℝ 2 V) (ρ : ℝ) (hρ : 0 ≤ ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (F : ℝ → E → ℝ) (hF : Continuous (Function.uncurry F))
    (M : ℝ) (hM : ∀ a x, ‖F a x‖ ≤ M) :
    Continuous (fun p : ℝ × (NNReal × E) =>
      ∫ y, F p.1 y ∂langevinKernel V B P p.2.1 p.2.2) := by
  let := brownianNoiseLaw_isProbabilityMeasure hB
  have hFa (a : ℝ) : Continuous (F a) := hF.comp (continuous_const.prodMk continuous_id)
  have he (p : ℝ × (NNReal × E)) :
      (∫ y, F p.1 y ∂langevinKernel V B P p.2.1 p.2.2) =
      ∫ w : C(ℝ, E), F p.1 (langevinSolution V w p.2.2 p.2.1) ∂brownianNoiseLaw B P := by
    rw [langevinKernel_apply_noiseLaw hB hV ρ hρ hHess]
    exact integral_map (((langevinSolution_evaluation_continuous hV ρ hρ hHess p.2.1.property).comp
      (continuous_const.prodMk continuous_id)).measurable.aemeasurable)
      (hFa p.1).measurable.aestronglyMeasurable
  simp_rw [he]
  apply continuous_iff_continuousAt.mpr
  intro p
  apply tendsto_integral_filter_of_dominated_convergence (fun _ : C(ℝ, E) => M)
  · exact Eventually.of_forall fun q =>
      ((hFa q.1).comp ((langevinEvaluation_continuous hV ρ hρ hHess q.2.1).comp
        (continuous_const.prodMk continuous_id))).measurable.aestronglyMeasurable
  · exact Eventually.of_forall fun q => Eventually.of_forall fun w => hM _ _
  · exact integrable_const M
  · exact Eventually.of_forall fun w =>
      (hF.comp (continuous_fst.prodMk
        ((continuous_langevinSolution_time_initial hV ρ hρ hHess w).comp continuous_snd))).tendsto p


variable {Ω : Type*} [MeasurableSpace Ω]

@[expose] noncomputable def langevinLogScore (V g : E → ℝ)
    (B : NNReal → Ω → E) (P : Measure Ω) (c r : ℝ) (x : E) : ℝ :=
  ‖gradient (fun y => Real.log (langevinPositiveProfile V g B P c r y)) x‖ ^ 2

section Score
variable {d : ℕ}
variable {B : NNReal → Ω → EuclideanSpace ℝ (Fin d)} {P : Measure Ω} (hB : IsEuclideanBrownian B P)
    {V g : EuclideanSpace ℝ (Fin d) → ℝ} (hV : ContDiff ℝ 2 V)
    (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g)
    (ρ : ℝ) (hρ : 0 ≤ ρ)
    (hHess : ∀ x z : EuclideanSpace ℝ (Fin d), ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (c m : ℝ) (hm : 0 < m) (hpos : ∀ x, m ≤ c + g x)

include hB hV hg hgc hρ hHess in
/-- Uniform actual gradient control at every real time parameter (which
uses its nonnegative part in the actual transition kernel). -/
theorem langevinPositiveProfile_uniform_gradient_bound :
    ∃ G : ℝ, 0 ≤ G ∧ ∀ r x, ‖gradient (langevinPositiveProfile V g B P c r) x‖ ≤ G := by
  obtain ⟨L, hLip⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hgc hg (by norm_num)
  refine ⟨L, L.coe_nonneg, ?_⟩
  intro r x
  have hqLip := lipschitzWith_langevinKernel_integral hB hV ρ hρ hHess
    (hg.of_le (by norm_num)) hgc hLip r.toNNReal
  have hn : ‖gradient (langevinPositiveProfile V g B P c r) x‖ =
      ‖fderiv ℝ (fun y => ∫ z, g z ∂langevinKernel V B P r.toNNReal y) x‖ := by
    change ‖gradient (fun y => c + ∫ z, g z ∂langevinKernel V B P r.toNNReal y) x‖ = _
    rw [gradient, fderiv_const_add]
    exact (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin d))).symm.norm_map _
  rw [hn]
  apply (norm_fderiv_le_of_lipschitz ℝ hqLip).trans
  exact mul_le_of_le_one_left L.coe_nonneg (Real.exp_le_one_iff.mpr
    (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hρ) r.toNNReal.property))

include hB hV hg hgc hρ hHess hm hpos in
/-- The genuine logarithmic score is jointly continuous, with no C²
regularity premise on the evolved profile. -/
theorem continuous_langevinLogScore :
    Continuous (fun p : ℝ × EuclideanSpace ℝ (Fin d) => langevinLogScore V g B P c p.1 p.2) := by
  have hq (r : ℝ) : ContDiff ℝ 1 (langevinPositiveProfile V g B P c r) :=
    contDiff_const.add (contDiff_one_langevinKernel_integral hB hV ρ hρ hHess
      (hg.of_le (by norm_num)) hgc r.toNNReal)
  have hlower := langevinPositiveProfile_lower hB hV hg hgc ρ hρ hHess c m hpos
  have hqJoint : Continuous (fun p : ℝ × EuclideanSpace ℝ (Fin d) => langevinPositiveProfile V g B P c p.1 p.2) := by
    obtain ⟨M, hM⟩ := hgc.exists_bound_of_continuous hg.continuous
    exact continuous_const.add ((continuous_langevinKernel_integral_time_initial hB hV hg.continuous
      ⟨M, hM⟩ ρ hρ hHess).comp ((continuous_real_toNNReal.comp continuous_fst).prodMk continuous_snd))
  have hGradJoint : Continuous (fun p : ℝ × EuclideanSpace ℝ (Fin d) =>
      gradient (langevinPositiveProfile V g B P c p.1) p.2) := by
    have hc := (continuous_gradient_langevinKernel_integral_time_initial hB hV ρ hρ hHess
      (hg.of_le (by norm_num)) hgc).comp ((continuous_real_toNNReal.comp continuous_fst).prodMk continuous_snd)
    apply hc.congr
    intro p
    change gradient (fun y => ∫ z, g z ∂langevinKernel V B P p.1.toNNReal y) p.2 =
      gradient (fun y => c + ∫ z, g z ∂langevinKernel V B P p.1.toNNReal y) p.2
    simp only [gradient, fderiv_const_add]
  have hInv := hqJoint.inv₀ (fun p => (hm.trans_le (hlower p.1 p.2)).ne')
  have hc := (hInv.smul hGradJoint).norm.pow 2
  apply hc.congr
  intro p
  dsimp only [langevinLogScore]
  rw [gradient_log_of_c1 (hq p.1) (fun y => hm.trans_le (hlower p.1 y))]
  simp only [Pi.pow_apply, Pi.smul_apply', Pi.inv_apply]

include hB hV hg hgc hρ hHess hm hpos in
/-- One finite score bound holds uniformly in both time and state. -/
theorem langevinLogScore_uniform_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r x, ‖langevinLogScore V g B P c r x‖ ≤ C := by
  obtain ⟨G, hG, hGrad⟩ := langevinPositiveProfile_uniform_gradient_bound hB hV hg hgc ρ hρ hHess c
  refine ⟨(G / m) ^ 2, sq_nonneg _, ?_⟩
  intro r x
  have hq : ContDiff ℝ 1 (langevinPositiveProfile V g B P c r) :=
    contDiff_const.add (contDiff_one_langevinKernel_integral hB hV ρ hρ hHess
      (hg.of_le (by norm_num)) hgc r.toNNReal)
  have hlower := langevinPositiveProfile_lower hB hV hg hgc ρ hρ hHess c m hpos r
  change ‖‖gradient (fun y => Real.log (langevinPositiveProfile V g B P c r y)) x‖ ^ 2‖ ≤ _
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), norm_gradient_log_sq_of_c1 hq
    (fun y => hm.trans_le (hlower y)), div_pow]
  gcongr
  · exact hGrad r x
  · exact hlower x

/-- Actual pointwise derivative representative in the BGL interpolation. -/
@[expose] noncomputable def langevinMovingLogScoreAverage (T s : ℝ) (x : EuclideanSpace ℝ (Fin d)) : ℝ :=
  -(∫ y, langevinLogScore V g B P c (2 * T - s) y ∂langevinKernel V B P s.toNNReal x)

include hB hV hg hgc hρ hHess hm hpos in
/-- The actual moving-score heat average has a jointly continuous
representative on all real time parameters, including the endpoints. -/
theorem continuous_langevinMovingLogScoreAverage (T : ℝ) :
    Continuous (fun p : ℝ × EuclideanSpace ℝ (Fin d) =>
      langevinMovingLogScoreAverage (V := V) (g := g) (B := B) (P := P) c T p.1 p.2) := by
  obtain ⟨C, _hC, hC⟩ := langevinLogScore_uniform_bound hB hV hg hgc ρ hρ hHess c m hm hpos
  have hc := continuous_langevinKernel_integral_moving_bounded hB hV ρ hρ hHess
    (langevinLogScore V g B P c) (continuous_langevinLogScore hB hV hg hgc ρ hρ hHess c m hm hpos) C hC
  exact (hc.comp (((continuous_const.mul continuous_const).sub continuous_fst).prodMk
    ((continuous_real_toNNReal.comp continuous_fst).prodMk continuous_snd))).neg

include hB hV hg hgc hρ hHess hm hpos in
/-- The moving-score average is uniformly bounded in time and state by
an actual finite source-derived constant. -/
theorem langevinMovingLogScoreAverage_uniform_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T s x,
      ‖langevinMovingLogScoreAverage (V := V) (g := g) (B := B) (P := P) c T s x‖ ≤ C := by
  obtain ⟨C, hC0, hC⟩ := langevinLogScore_uniform_bound hB hV hg hgc ρ hρ hHess c m hm hpos
  refine ⟨C, hC0, ?_⟩
  intro T s x
  let := langevinKernel_isMarkovKernel hB hV ρ hρ hHess s.toNNReal
  change ‖-(∫ y, langevinLogScore V g B P c (2 * T - s) y ∂langevinKernel V B P s.toNNReal x)‖ ≤ C
  rw [norm_neg]
  simpa only [measureReal_def, measure_univ, ENNReal.toReal_one, mul_one] using
    (norm_integral_le_of_norm_le_const
      (μ := langevinKernel V B P s.toNNReal x) (Eventually.of_forall (hC (2 * T - s))))

end Score
end CutoffRigidity
