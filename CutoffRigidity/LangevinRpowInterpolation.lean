module
public import CutoffRigidity.LangevinRpowEvolution
public import CutoffRigidity.LangevinSquareInterpolation

/-! # Actual pointwise real-power interpolation for power Harnack

The interpolation F(s,x) = P_s(Q_{T-s}^α)(x) of the positive backward
profile is differentiated at every point, from the strong L² identity and
continuous representatives. The genuine weighted gradient estimate then
gives |∇F|²/F ≤ e^(-2ρs) α/(α-1) ∂ₛF for every α > 1.
-/
public section
namespace CutoffRigidity
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal
variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

@[expose] noncomputable def langevinRpowInterpolation (V g : E → ℝ)
    (B : NNReal → Ω → E) (P : Measure Ω) (c α T s : ℝ) (x : E) : ℝ :=
  ∫ y, langevinPositiveProfile V g B P c (T - s) y ^ α ∂langevinKernel V B P s.toNNReal x

@[expose] noncomputable def langevinRpowCarreAverage (V g : E → ℝ)
    (B : NNReal → Ω → E) (P : Measure Ω) (c α T s : ℝ) (x : E) : ℝ :=
  ∫ y, langevinRpowGradientProfile V g B P c α (T - s) y ∂langevinKernel V B P s.toNNReal x

section Source
variable {d : ℕ}
variable {B : NNReal → Ω → (EuclideanSpace ℝ (Fin d))} {P : Measure Ω} (hB : IsEuclideanBrownian B P)
    {V g : (EuclideanSpace ℝ (Fin d)) → ℝ} (hV : ContDiff ℝ 2 V)
    (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g)
    (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : (EuclideanSpace ℝ (Fin d)), ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (c m : ℝ) (hm : 0 < m) (hpos : ∀ x, m ≤ c + g x) (α : ℝ)

include hB hV hg hgc hρ hHess hm hpos in
set_option maxHeartbeats 600000 in
/-- The real-power profile family is a uniformly bounded, uniformly
Lipschitz C¹ family with jointly continuous derivative. -/
theorem langevinRpowProfile_testData :
    ∃ (A : ℝ) (L : NNReal),
      (∀ r, ContDiff ℝ 1 (fun x => langevinPositiveProfile V g B P c r x ^ α)) ∧
      Continuous (fun p : ℝ × (EuclideanSpace ℝ (Fin d)) => langevinPositiveProfile V g B P c p.1 p.2 ^ α) ∧
      Continuous (fun p : ℝ × (EuclideanSpace ℝ (Fin d)) =>
        fderiv ℝ (fun x => langevinPositiveProfile V g B P c p.1 x ^ α) p.2) ∧
      (∀ r x, ‖langevinPositiveProfile V g B P c r x ^ α‖ ≤ A) ∧
      (∀ r x, ‖fderiv ℝ (fun y => langevinPositiveProfile V g B P c r y ^ α) x‖ ≤ L) := by
  obtain ⟨A, G, N, hA, hG, hN, hC, hlo, hup, hGrad, -, -⟩ :=
    langevinPositiveProfile_rpow_data hB hV hg hgc ρ hρ hHess c m hm hpos
  let q := langevinPositiveProfile V g B P c
  have hqpos (r : ℝ) (x : (EuclideanSpace ℝ (Fin d))) : 0 < q r x := hm.trans_le (hlo r x)
  have hJ := continuous_langevinPositiveProfile_time_initial hB hV hg hgc ρ hρ hHess c
  have hJD := continuous_fderiv_langevinPositiveProfile_time_initial hB hV hg hgc ρ hρ hHess c
  have hfd (r : ℝ) (x : (EuclideanSpace ℝ (Fin d))) : fderiv ℝ (fun y => q r y ^ α) x = (α * q r x ^ (α - 1)) • fderiv ℝ (q r) x :=
    (((hC r).differentiable one_ne_zero x).hasFDerivAt.rpow_const (p := α) (Or.inl (hqpos r x).ne')).fderiv
  have hnorm (r : ℝ) (x : (EuclideanSpace ℝ (Fin d))) : ‖fderiv ℝ (q r) x‖ = ‖gradient (q r) x‖ :=
    ((InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin d))).symm.norm_map _).symm
  have hPn (q' : ℝ) : 0 ≤ m ^ q' + A ^ q' := add_nonneg (Real.rpow_nonneg hm.le _) (Real.rpow_nonneg hA.le _)
  refine ⟨m ^ α + A ^ α, Real.toNNReal (|α| * (m ^ (α - 1) + A ^ (α - 1)) * G),
    fun r => (hC r).rpow_const_of_ne (fun x => (hqpos r x).ne'),
    hJ.rpow_const (fun p => Or.inl (hqpos p.1 p.2).ne'), ?_, ?_, ?_⟩
  · have hc := ((hJ.rpow_const (p := α - 1) (fun p => Or.inl (hqpos p.1 p.2).ne')).const_mul α).smul hJD
    exact hc.congr (fun p => (hfd p.1 p.2).symm)
  · intro r x
    rw [Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos (hqpos r x) _)]
    exact rpow_le_add_of_mem_Icc hm (hlo r x) (hup r x) α
  · intro r x
    rw [Real.coe_toNNReal _ (mul_nonneg (mul_nonneg (abs_nonneg _) (hPn _)) hG), hfd, norm_smul,
      hnorm, Real.norm_eq_abs, abs_mul, abs_of_pos (Real.rpow_pos_of_pos (hqpos r x) _)]
    exact mul_le_mul (mul_le_mul_of_nonneg_left (rpow_le_add_of_mem_Icc hm (hlo r x) (hup r x) _)
      (abs_nonneg _)) (hGrad r x) (norm_nonneg _) (mul_nonneg (abs_nonneg _) (hPn _))

include hB hV hg hgc hρ hHess hm hpos in
theorem continuous_langevinRpowGradientProfile :
    Continuous (fun p : ℝ × (EuclideanSpace ℝ (Fin d)) => langevinRpowGradientProfile V g B P c α p.1 p.2) := by
  obtain ⟨A, G, N, hA, hG, hN, hC, hlo, hup, hGrad, -, -⟩ :=
    langevinPositiveProfile_rpow_data hB hV hg hgc ρ hρ hHess c m hm hpos
  have hJ := continuous_langevinPositiveProfile_time_initial hB hV hg hgc ρ hρ hHess c
  have hJD := continuous_fderiv_langevinPositiveProfile_time_initial hB hV hg hgc ρ hρ hHess c
  have hc := ((hJ.rpow_const (p := α - 2) (fun p => Or.inl (hm.trans_le (hlo p.1 p.2)).ne')).const_mul
    (α * (α - 1))).mul (hJD.norm.pow 2)
  apply hc.congr
  intro p
  show α * (α - 1) * langevinPositiveProfile V g B P c p.1 p.2 ^ (α - 2) *
      ‖fderiv ℝ (langevinPositiveProfile V g B P c p.1) p.2‖ ^ 2 =
    langevinRpowGradientProfile V g B P c α p.1 p.2
  rw [show ‖fderiv ℝ (langevinPositiveProfile V g B P c p.1) p.2‖ =
    ‖gradient (langevinPositiveProfile V g B P c p.1) p.2‖ from
      ((InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin d))).symm.norm_map _).symm]
  rfl

include hB hV hg hgc hρ hHess hm hpos in
theorem continuous_langevinRpowInterpolation (T : ℝ) :
    Continuous (fun p : ℝ × (EuclideanSpace ℝ (Fin d)) => langevinRpowInterpolation V g B P c α T p.1 p.2) := by
  obtain ⟨A, L, -, hJ, -, hBound, -⟩ :=
    langevinRpowProfile_testData hB hV hg hgc ρ hρ hHess c m hm hpos α
  exact (continuous_langevinKernel_integral_moving_bounded hB hV ρ hρ.le hHess
    (fun r x => langevinPositiveProfile V g B P c r x ^ α) hJ A hBound).comp
    ((continuous_const.sub continuous_fst).prodMk
      ((continuous_real_toNNReal.comp continuous_fst).prodMk continuous_snd))

include hB hV hg hgc hρ hHess hm hpos in
theorem continuous_langevinRpowCarreAverage (T : ℝ) :
    Continuous (fun p : ℝ × (EuclideanSpace ℝ (Fin d)) => langevinRpowCarreAverage V g B P c α T p.1 p.2) := by
  obtain ⟨K, hK, hKb⟩ := langevinRpowGradientProfile_uniform_bound hB hV hg hgc ρ hρ hHess c m hm hpos α
  exact (continuous_langevinKernel_integral_moving_bounded hB hV ρ hρ.le hHess
    (fun r x => langevinRpowGradientProfile V g B P c α r x)
    (continuous_langevinRpowGradientProfile hB hV hg hgc ρ hρ hHess c m hm hpos α) K
    (fun r x => by rw [Real.norm_eq_abs]; exact hKb r x)).comp
    ((continuous_const.sub continuous_fst).prodMk
      ((continuous_real_toNNReal.comp continuous_fst).prodMk continuous_snd))

include hB hV hg hgc hρ hHess hm hpos in
theorem langevinRpowCarreAverage_uniform_bound :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ T s x, ‖langevinRpowCarreAverage V g B P c α T s x‖ ≤ K := by
  obtain ⟨K, hK, hKb⟩ := langevinRpowGradientProfile_uniform_bound hB hV hg hgc ρ hρ hHess c m hm hpos α
  refine ⟨K, hK, fun T s x => ?_⟩
  exact langevinKernel_integral_compact_test_norm_le hB hV ρ hρ.le hHess
    (fun y => by rw [Real.norm_eq_abs]; exact hKb (T - s) y) s.toNNReal x

include hB hV hg hgc hρ hHess hm hpos in
theorem langevinRpowInterpolation_lower (hα : 0 ≤ α) (T s : ℝ) (x : (EuclideanSpace ℝ (Fin d))) :
    m ^ α ≤ langevinRpowInterpolation V g B P c α T s x := by
  let := langevinKernel_isMarkovKernel hB hV ρ hρ.le hHess s.toNNReal
  obtain ⟨A, L, hC1, hJ, -, hBound, -⟩ :=
    langevinRpowProfile_testData hB hV hg hgc ρ hρ hHess c m hm hpos α
  have hi : Integrable (fun y => langevinPositiveProfile V g B P c (T - s) y ^ α)
      (langevinKernel V B P s.toNNReal x) :=
    (integrable_const A).mono' (hC1 (T - s)).continuous.aestronglyMeasurable
      (Eventually.of_forall (hBound (T - s)))
  have hh := integral_mono (integrable_const (m ^ α)) hi (fun y =>
    Real.rpow_le_rpow hm.le (langevinPositiveProfile_lower hB hV hg hgc ρ hρ.le hHess c m hpos (T - s) y) hα)
  simpa only [langevinRpowInterpolation, integral_const, measureReal_def, measure_univ,
    ENNReal.toReal_one, one_smul] using hh

include hB hV hg hgc hρ hHess hm hpos in
theorem contDiff_one_langevinRpowInterpolation (T s : ℝ) :
    ContDiff ℝ 1 (langevinRpowInterpolation V g B P c α T s) := by
  obtain ⟨A, L, hC1, -, -, hBound, hLipBound⟩ :=
    langevinRpowProfile_testData hB hV hg hgc ρ hρ hHess c m hm hpos α
  have hLip : LipschitzWith L (fun x => langevinPositiveProfile V g B P c (T - s) x ^ α) :=
    lipschitzWith_of_nnnorm_fderiv_le ((hC1 _).differentiable one_ne_zero)
      (fun x => by exact_mod_cast hLipBound _ x)
  exact contDiff_one_langevinKernel_integral_bounded_c1 hB hV ρ hρ.le hHess (hC1 _) A (hBound _) L hLip
    s.toNNReal

include hB hV hg hgc hρ hHess hm hpos in
theorem continuous_fderiv_langevinRpowInterpolation (T : ℝ) :
    Continuous (fun p : ℝ × (EuclideanSpace ℝ (Fin d)) => fderiv ℝ (langevinRpowInterpolation V g B P c α T p.1) p.2) := by
  obtain ⟨A, L, hC1, -, hFD, hBound, hLipBound⟩ :=
    langevinRpowProfile_testData hB hV hg hgc ρ hρ hHess c m hm hpos α
  have hc := continuous_fderiv_langevinKernel_integral_moving_bounded_c1 hB hV ρ hρ.le hHess
    (fun r x => langevinPositiveProfile V g B P c r x ^ α) hC1 hFD A hBound L hLipBound
  exact hc.comp ((continuous_const.sub continuous_fst).prodMk
    ((continuous_real_toNNReal.comp continuous_fst).prodMk continuous_snd))

include hB hV hg hgc hρ hHess hm hpos in
set_option maxHeartbeats 900000 in
/-- The actual real-power interpolation identity at every initial point. -/
theorem hasDerivAt_langevinRpowInterpolation (hp : IsProbabilityMeasure (gibbsMeasure volume V))
    (T s : ℝ) (hs : 0 < s) (hsT : s < T) (x : (EuclideanSpace ℝ (Fin d))) :
    HasDerivAt (fun r => langevinRpowInterpolation V g B P c α T r x)
      (langevinRpowCarreAverage V g B P c α T s x) s := by
  let := hp
  let μ := gibbsMeasure volume V
  let : μ.IsOpenPosMeasure := gibbsMeasure_isOpenPosMeasure volume hV.continuous.measurable
  let U := fun r : ℝ => langevinL2Operator hB hV hp ρ hρ hHess r.toNNReal
    (langevinRpowProfileLp hB hV hg hgc ρ hρ hHess c m hm hpos α μ (T - r))
  let D := fun r : ℝ => langevinL2Operator hB hV hp ρ hρ hHess r.toNNReal
    (langevinRpowGradientProfileLp hB hV hg hgc ρ hρ hHess c m hm hpos α μ (T - r))
  let F := langevinRpowInterpolation V g B P c α T
  let G := langevinRpowCarreAverage V g B P c α T
  have hU (r : ℝ) : U r =ᵐ[μ] F r := by
    have hmem := langevinRpowProfile_memLp hB hV hg hgc ρ hρ hHess c m hm hpos α μ (T - r)
    exact (langevinL2Operator_coeFn hB hV hp ρ hρ hHess r.toNNReal (hmem.toLp _)).trans
      (invariantKernel_integral_congr_ae (langevinKernel V B P r.toNNReal)
        (langevinKernel_gibbs_invariant hB hV hp ρ hρ hHess r.toNNReal) hmem.coeFn_toLp)
  have hD (r : ℝ) : D r =ᵐ[μ] G r := by
    have hmem := langevinRpowGradientProfile_memLp hB hV hg hgc ρ hρ hHess c m hm hpos α μ (T - r)
    exact (langevinL2Operator_coeFn hB hV hp ρ hρ hHess r.toNNReal (hmem.toLp _)).trans
      (invariantKernel_integral_congr_ae (langevinKernel V B P r.toNNReal)
        (langevinKernel_gibbs_invariant hB hV hp ρ hρ hHess r.toNNReal) hmem.coeFn_toLp)
  have hGjoint : Continuous (Function.uncurry G) :=
    continuous_langevinRpowCarreAverage hB hV hg hgc ρ hρ hHess c m hm hpos α T
  obtain ⟨C, hC0, hC⟩ := langevinRpowCarreAverage_uniform_bound hB hV hg hgc ρ hρ hHess c m hm hpos α
  have hGc (r : ℝ) : Continuous (G r) := hGjoint.comp (continuous_const.prodMk continuous_id)
  have hGt (y : (EuclideanSpace ℝ (Fin d))) : Continuous (fun r => G r y) := hGjoint.comp (continuous_id.prodMk continuous_const)
  have hDc : Continuous D := continuous_L2_of_bounded_representatives μ D G hGc hGt hD C hC0 (hC T)
  have hFjoint : Continuous (Function.uncurry F) :=
    continuous_langevinRpowInterpolation hB hV hg hgc ρ hρ hHess c m hm hpos α T
  exact hasDerivAt_of_L2_deriv_continuous_representatives μ U D F G ⟨hs, hsT⟩
    (fun r hr => hasDerivAt_langevin_rpow_interpolation hB hV hp hg hgc ρ hρ hHess c m hm hpos α T r hr.1 hr.2)
    hDc (fun r => hFjoint.comp (continuous_const.prodMk continuous_id)) hGc hGt
    hGjoint.stronglyMeasurable hU hD C hC0 (hC T) x

include hB hV hg hgc hρ hHess hm hpos in
set_option maxHeartbeats 900000 in
/-- The genuine weighted flow gradient estimate for the real-power
interpolation, with the Wang constant α/(α-1). -/
theorem langevinRpowInterpolation_weighted_gradient (hα : 1 < α) (T s : ℝ) (x : (EuclideanSpace ℝ (Fin d))) :
    ‖gradient (langevinRpowInterpolation V g B P c α T s) x‖ ^ 2 /
      langevinRpowInterpolation V g B P c α T s x ≤
      Real.exp (-2 * ρ * s.toNNReal) * (α / (α - 1)) * langevinRpowCarreAverage V g B P c α T s x := by
  obtain ⟨A, L, hC1, -, -, hBound, hLipBound⟩ :=
    langevinRpowProfile_testData hB hV hg hgc ρ hρ hHess c m hm hpos α
  obtain ⟨A', G, N, hA', hG, hN, hC, hlo, hup, hGrad, -, -⟩ :=
    langevinPositiveProfile_rpow_data hB hV hg hgc ρ hρ hHess c m hm hpos
  let q := langevinPositiveProfile V g B P c (T - s)
  have hqpos (y : (EuclideanSpace ℝ (Fin d))) : 0 < q y := hm.trans_le (hlo _ y)
  have hLip : LipschitzWith L (fun y => q y ^ α) :=
    lipschitzWith_of_nnnorm_fderiv_le ((hC1 _).differentiable one_ne_zero)
      (fun y => by exact_mod_cast hLipBound _ y)
  have hFloor (y : (EuclideanSpace ℝ (Fin d))) : m ^ α ≤ 0 + q y ^ α := by
    rw [zero_add]
    exact Real.rpow_le_rpow hm.le (hlo _ y) (zero_le_one.trans hα.le)
  have hw := langevinKernel_weighted_gradient_le_bounded_c1 hB hV ρ hρ.le hHess
    (hC1 (T - s)) A (hBound (T - s)) L hLip 0 (m ^ α) (Real.rpow_pos_of_pos hm α) hFloor s.toNNReal x
  dsimp only at hw
  simp only [zero_add] at hw
  change ‖gradient (langevinRpowInterpolation V g B P c α T s) x‖ ^ 2 /
      langevinRpowInterpolation V g B P c α T s x ≤
      Real.exp (-2 * ρ * s.toNNReal) *
        ∫ y, ‖gradient (fun z => q z ^ α) y‖ ^ 2 / q y ^ α ∂langevinKernel V B P s.toNNReal x at hw
  have hα1 : 0 < α - 1 := by linarith
  have he (y : (EuclideanSpace ℝ (Fin d))) : ‖gradient (fun z => q z ^ α) y‖ ^ 2 / q y ^ α =
      (α / (α - 1)) * langevinRpowGradientProfile V g B P c α (T - s) y := by
    rw [norm_gradient_rpow_of_c1 (hC _) hqpos]
    have h1 : q y ^ (α - 1) = q y ^ (α - 2) * q y := by
      rw [← Real.rpow_add_one (hqpos y).ne']
      ring_nf
    have h2 : q y ^ α = q y ^ (α - 2) * q y ^ 2 := by
      rw [← Real.rpow_natCast, ← Real.rpow_add (hqpos y)]
      ring_nf
    have hP := Real.rpow_pos_of_pos (hqpos y) (α - 2)
    change (|α| * q y ^ (α - 1) * ‖gradient q y‖) ^ 2 / q y ^ α =
      α / (α - 1) * (α * (α - 1) * q y ^ (α - 2) * ‖gradient q y‖ ^ 2)
    rw [h1, h2, abs_of_pos (by linarith : (0 : ℝ) < α)]
    have hq0 := (hqpos y).ne'
    field_simp
  rw [integral_congr_ae (Eventually.of_forall he), integral_const_mul] at hw
  calc
    _ ≤ _ := hw
    _ = _ := by rw [langevinRpowCarreAverage]; ring

end Source
end CutoffRigidity
