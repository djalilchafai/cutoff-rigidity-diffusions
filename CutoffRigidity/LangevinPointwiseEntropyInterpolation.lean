module
public import CutoffRigidity.LangevinJointScoreContinuity
public import CutoffRigidity.L2PointwiseEvolution
public import CutoffRigidity.LangevinDomainDynkin

/-! # Pointwise BGL logarithmic interpolation for the actual diffusion

The actual strong L² evolution is upgraded by full support to the pointwise
classical time derivative, using the proved jointly continuous score.
-/
public section
namespace CutoffRigidity
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal
variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

@[expose] noncomputable def langevinLogInterpolation (V g : E → ℝ)
    (B : NNReal → Ω → E) (P : Measure Ω) (c T s : ℝ) (x : E) : ℝ :=
  ∫ y, Real.log (langevinPositiveProfile V g B P c (2 * T - s) y)
    ∂langevinKernel V B P s.toNNReal x

theorem continuous_langevinLogInterpolation
    {B : NNReal → Ω → E} {P : Measure Ω} (hB : IsEuclideanBrownian B P)
    {V g : E → ℝ} (hV : ContDiff ℝ 2 V)
    (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g)
    (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (c m : ℝ) (hm : 0 < m) (hpos : ∀ x, m ≤ c + g x) (T : ℝ) :
    Continuous (fun p : ℝ × E => langevinLogInterpolation V g B P c T p.1 p.2) := by
  obtain ⟨M, hM⟩ := hgc.exists_bound_of_continuous hg.continuous
  let q := langevinPositiveProfile V g B P c
  have hlower := langevinPositiveProfile_lower hB hV hg hgc ρ hρ.le hHess c m hpos
  have hqjoint : Continuous (fun p : ℝ × E => q p.1 p.2) := by
    exact continuous_const.add ((continuous_langevinKernel_integral_time_initial hB hV hg.continuous
      ⟨M, hM⟩ ρ hρ.le hHess).comp ((continuous_real_toNNReal.comp continuous_fst).prodMk continuous_snd))
  have hlogjoint : Continuous (fun p : ℝ × E => Real.log (q p.1 p.2)) :=
    hqjoint.log (fun p => (hm.trans_le (hlower p.1 p.2)).ne')
  have hUpper (r : ℝ) (y : E) : q r y ≤ |c| + M := by
    exact (le_abs_self _).trans ((abs_add_le _ _).trans (add_le_add (le_refl _)
      (by simpa only [Real.norm_eq_abs] using
        langevinKernel_integral_compact_test_norm_le hB hV ρ hρ.le hHess hM r.toNNReal y)))
  have hlogB (r : ℝ) (y : E) : ‖Real.log (q r y)‖ ≤ |Real.log m| + |Real.log (|c| + M)| := by
    rw [Real.norm_eq_abs, abs_le]
    have hlo := Real.log_le_log hm (hlower r y)
    have hhi := Real.log_le_log (hm.trans_le (hlower r y)) (hUpper r y)
    constructor <;> linarith [neg_abs_le (Real.log m), le_abs_self (Real.log (|c| + M)),
      abs_nonneg (Real.log m), abs_nonneg (Real.log (|c| + M))]
  have hFjoint : Continuous (fun p : ℝ × E => langevinLogInterpolation V g B P c T p.1 p.2) := by
    have hc := continuous_langevinKernel_integral_moving_bounded hB hV ρ hρ.le hHess
      (fun r y => Real.log (q r y)) hlogjoint _ hlogB
    exact hc.comp (((continuous_const.mul continuous_const).sub continuous_fst).prodMk
      ((continuous_real_toNNReal.comp continuous_fst).prodMk continuous_snd))
  exact hFjoint

set_option maxHeartbeats 800000 in
theorem hasDerivAt_langevin_log_interpolation_pointwise_of_lt_twice
    {B : NNReal → Ω → E} {P : Measure Ω} (hB : IsEuclideanBrownian B P)
    {V g : E → ℝ} (hV : ContDiff ℝ 2 V)
    (hp : IsProbabilityMeasure (gibbsMeasure volume V))
    (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g)
    (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (c m : ℝ) (hm : 0 < m) (hpos : ∀ x, m ≤ c + g x)
    (T s : ℝ) (hs : 0 < s) (hsT : s < 2 * T) (x : E) :
    HasDerivAt (fun r => langevinLogInterpolation V g B P c T r x)
      (langevinMovingLogScoreAverage (V := V) (g := g) (B := B) (P := P) c T s x) s := by
  let := hp
  let μ := gibbsMeasure volume V
  let : μ.IsOpenPosMeasure := gibbsMeasure_isOpenPosMeasure volume hV.continuous.measurable
  let U := fun r : ℝ => langevinL2Operator hB hV hp ρ hρ hHess r.toNNReal
    (langevinLogProfileLp hB hV hg hgc ρ hρ.le hHess c m hm hpos μ (2 * T - r))
  let D := fun r : ℝ => -langevinL2Operator hB hV hp ρ hρ hHess r.toNNReal
    (langevinLogGradientSqLp hB hV hg hgc ρ hρ hHess c m hm hpos μ (2 * T - r))
  let F := langevinLogInterpolation V g B P c T
  let G := langevinMovingLogScoreAverage (V := V) (g := g) (B := B) (P := P) c T
  have hU (r : ℝ) : U r =ᵐ[μ] F r := by
    have hmem := langevinLogProfile_memLp hB hV hg hgc ρ hρ.le hHess c m hm hpos μ (2 * T - r)
    exact (langevinL2Operator_coeFn hB hV hp ρ hρ hHess r.toNNReal (hmem.toLp _)).trans
      (invariantKernel_integral_congr_ae (langevinKernel V B P r.toNNReal)
        (langevinKernel_gibbs_invariant hB hV hp ρ hρ hHess r.toNNReal) hmem.coeFn_toLp)
  have hD (r : ℝ) : D r =ᵐ[μ] G r := by
    have hmem := langevinLogGradientSq_memLp hB hV hg hgc ρ hρ hHess c m hm hpos μ (2 * T - r)
    have he := (langevinL2Operator_coeFn hB hV hp ρ hρ hHess r.toNNReal (hmem.toLp _)).trans
      (invariantKernel_integral_congr_ae (langevinKernel V B P r.toNNReal)
        (langevinKernel_gibbs_invariant hB hV hp ρ hρ hHess r.toNNReal) hmem.coeFn_toLp)
    filter_upwards [Lp.coeFn_neg (langevinL2Operator hB hV hp ρ hρ hHess r.toNNReal (hmem.toLp _)), he]
      with y hn he
    change ((-langevinL2Operator hB hV hp ρ hρ hHess r.toNNReal (hmem.toLp _)) : E →₂[μ] ℝ) y = _
    rw [hn, Pi.neg_apply, he]
    rfl
  have hGjoint : Continuous (Function.uncurry G) :=
    continuous_langevinMovingLogScoreAverage hB hV hg hgc ρ hρ.le hHess c m hm hpos T
  obtain ⟨C, hC0, hC⟩ := langevinMovingLogScoreAverage_uniform_bound hB hV hg hgc ρ hρ.le hHess c m hm hpos
  have hGc (r : ℝ) : Continuous (G r) := hGjoint.comp (continuous_const.prodMk continuous_id)
  have hGt (y : E) : Continuous (fun r => G r y) := hGjoint.comp (continuous_id.prodMk continuous_const)
  have hDc : Continuous D := continuous_L2_of_bounded_representatives μ D G hGc hGt hD C hC0 (hC T)
  have hFjoint : Continuous (Function.uncurry F) :=
    continuous_langevinLogInterpolation hB hV hg hgc ρ hρ hHess c m hm hpos T
  exact hasDerivAt_of_L2_deriv_continuous_representatives μ U D F G ⟨hs, hsT⟩
    (fun r hr => hasDerivAt_langevin_log_interpolation_of_lt_twice hB hV hp hg hgc ρ hρ hHess c m hm hpos T r hr.1 hr.2)
    hDc (fun r => hFjoint.comp (continuous_const.prodMk continuous_id)) hGc hGt
    hGjoint.stronglyMeasurable hU hD C hC0 (hC T) x


set_option maxHeartbeats 800000 in
theorem hasDerivAt_langevin_log_interpolation_pointwise
    {B : NNReal → Ω → E} {P : Measure Ω} (hB : IsEuclideanBrownian B P)
    {V g : E → ℝ} (hV : ContDiff ℝ 2 V)
    (hp : IsProbabilityMeasure (gibbsMeasure volume V))
    (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g)
    (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (c m : ℝ) (hm : 0 < m) (hpos : ∀ x, m ≤ c + g x)
    (T s : ℝ) (hs : 0 < s) (hsT : s < T) (x : E) :
    HasDerivAt (fun r => langevinLogInterpolation V g B P c T r x)
      (langevinMovingLogScoreAverage (V := V) (g := g) (B := B) (P := P) c T s x) s := by
  let := hp
  let μ := gibbsMeasure volume V
  let : μ.IsOpenPosMeasure := gibbsMeasure_isOpenPosMeasure volume hV.continuous.measurable
  let U := fun r : ℝ => langevinL2Operator hB hV hp ρ hρ hHess r.toNNReal
    (langevinLogProfileLp hB hV hg hgc ρ hρ.le hHess c m hm hpos μ (2 * T - r))
  let D := fun r : ℝ => -langevinL2Operator hB hV hp ρ hρ hHess r.toNNReal
    (langevinLogGradientSqLp hB hV hg hgc ρ hρ hHess c m hm hpos μ (2 * T - r))
  let F := langevinLogInterpolation V g B P c T
  let G := langevinMovingLogScoreAverage (V := V) (g := g) (B := B) (P := P) c T
  have hU (r : ℝ) : U r =ᵐ[μ] F r := by
    have hmem := langevinLogProfile_memLp hB hV hg hgc ρ hρ.le hHess c m hm hpos μ (2 * T - r)
    exact (langevinL2Operator_coeFn hB hV hp ρ hρ hHess r.toNNReal (hmem.toLp _)).trans
      (invariantKernel_integral_congr_ae (langevinKernel V B P r.toNNReal)
        (langevinKernel_gibbs_invariant hB hV hp ρ hρ hHess r.toNNReal) hmem.coeFn_toLp)
  have hD (r : ℝ) : D r =ᵐ[μ] G r := by
    have hmem := langevinLogGradientSq_memLp hB hV hg hgc ρ hρ hHess c m hm hpos μ (2 * T - r)
    have he := (langevinL2Operator_coeFn hB hV hp ρ hρ hHess r.toNNReal (hmem.toLp _)).trans
      (invariantKernel_integral_congr_ae (langevinKernel V B P r.toNNReal)
        (langevinKernel_gibbs_invariant hB hV hp ρ hρ hHess r.toNNReal) hmem.coeFn_toLp)
    filter_upwards [Lp.coeFn_neg (langevinL2Operator hB hV hp ρ hρ hHess r.toNNReal (hmem.toLp _)), he]
      with y hn he
    change ((-langevinL2Operator hB hV hp ρ hρ hHess r.toNNReal (hmem.toLp _)) : E →₂[μ] ℝ) y = _
    rw [hn, Pi.neg_apply, he]
    rfl
  have hGjoint : Continuous (Function.uncurry G) :=
    continuous_langevinMovingLogScoreAverage hB hV hg hgc ρ hρ.le hHess c m hm hpos T
  obtain ⟨C, hC0, hC⟩ := langevinMovingLogScoreAverage_uniform_bound hB hV hg hgc ρ hρ.le hHess c m hm hpos
  have hGc (r : ℝ) : Continuous (G r) := hGjoint.comp (continuous_const.prodMk continuous_id)
  have hGt (y : E) : Continuous (fun r => G r y) := hGjoint.comp (continuous_id.prodMk continuous_const)
  have hDc : Continuous D := continuous_L2_of_bounded_representatives μ D G hGc hGt hD C hC0 (hC T)
  have hFjoint : Continuous (Function.uncurry F) :=
    continuous_langevinLogInterpolation hB hV hg hgc ρ hρ hHess c m hm hpos T
  exact hasDerivAt_of_L2_deriv_continuous_representatives μ U D F G ⟨hs, hsT⟩
    (fun r hr => hasDerivAt_langevin_log_interpolation hB hV hp hg hgc ρ hρ hHess c m hm hpos T r hr.1 hr.2)
    hDc (fun r => hFjoint.comp (continuous_const.prodMk continuous_id)) hGc hGt
    hGjoint.stronglyMeasurable hU hD C hC0 (hC T) x

end CutoffRigidity
