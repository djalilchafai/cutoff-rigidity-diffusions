module
public import CutoffRigidity.LangevinSquareInterpolation
public import CutoffRigidity.LangevinBoundedWeightedGradient
public import CutoffRigidity.LangevinMovingGradientContinuity

/-! # Actual positive square interpolation for the power-two Harnack bound

Adding a constant to the actual compact-test heat curve gives a positive
profile. Its squared interpolation expands into the already checked
variance interpolation and two time-independent genuine semigroup terms.
-/
public section
namespace CutoffRigidity
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal
variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

@[expose] noncomputable def langevinPositiveSquareInterpolation (V g : E → ℝ)
    (B : NNReal → Ω → E) (P : Measure Ω) (c T s : ℝ) (x : E) : ℝ :=
  ∫ y, (langevinPositiveProfile V g B P c (T - s) y) ^ 2 ∂langevinKernel V B P s.toNNReal x

theorem bounded_c1_square_lipschitz {q : E → ℝ} (hq : ContDiff ℝ 1 q)
    (A G : ℝ) (hA : 0 ≤ A) (hG : 0 ≤ G)
    (hBound : ∀ x, ‖q x‖ ≤ A) (hGrad : ∀ x, ‖gradient q x‖ ≤ G) :
    LipschitzWith (Real.toNNReal (2 * A * G)) (fun x => q x ^ 2) := by
  apply lipschitzWith_of_nnnorm_fderiv_le ((hq.pow 2).differentiable one_ne_zero)
  intro x
  change ‖fderiv ℝ (fun y => q y ^ 2) x‖ ≤ (Real.toNNReal (2 * A * G) : ℝ)
  rw [Real.coe_toNNReal _ (by positivity)]
  have he : ‖fderiv ℝ (fun y => q y ^ 2) x‖ = ‖gradient (fun y => q y ^ 2) x‖ :=
    ((InnerProductSpace.toDual ℝ E).symm.norm_map _).symm
  rw [he, gradient_square_of_c1 hq, norm_smul, norm_mul, Real.norm_ofNat]
  exact mul_le_mul (mul_le_mul_of_nonneg_left (hBound x) (by norm_num)) (hGrad x)
    (norm_nonneg _) (by positivity)

section Source
variable {d : ℕ}
variable {B : NNReal → Ω → EuclideanSpace ℝ (Fin d)} {P : Measure Ω} (hB : IsEuclideanBrownian B P)
    {V g : EuclideanSpace ℝ (Fin d) → ℝ} (hV : ContDiff ℝ 2 V)
    (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g)
    (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : EuclideanSpace ℝ (Fin d), ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (c m : ℝ) (hm : 0 < m) (hpos : ∀ x, m ≤ c + g x)

include hB hV hg hgc hρ hHess in
theorem langevinPositiveProfile_uniform_norm_bound :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ r x, ‖langevinPositiveProfile V g B P c r x‖ ≤ A := by
  obtain ⟨M, hM0, hM⟩ := compact_continuous_norm_bound hg.continuous hgc
  refine ⟨|c| + M, add_nonneg (abs_nonneg _) hM0, ?_⟩
  intro r x
  exact (norm_add_le _ _).trans (add_le_add (by simp)
    (langevinKernel_integral_compact_test_norm_le hB hV ρ hρ.le hHess hM r.toNNReal x))

include hB hV hg hgc hρ hHess in
theorem continuous_langevinPositiveProfile_time_initial :
    Continuous (fun p : ℝ × EuclideanSpace ℝ (Fin d) => langevinPositiveProfile V g B P c p.1 p.2) := by
  obtain ⟨M, hM⟩ := hgc.exists_bound_of_continuous hg.continuous
  exact continuous_const.add ((continuous_langevinKernel_integral_time_initial hB hV hg.continuous
    ⟨M, hM⟩ ρ hρ.le hHess).comp ((continuous_real_toNNReal.comp continuous_fst).prodMk continuous_snd))

include hB hV hg hgc hρ hHess in
theorem continuous_fderiv_langevinPositiveProfile_time_initial :
    Continuous (fun p : ℝ × EuclideanSpace ℝ (Fin d) =>
      fderiv ℝ (langevinPositiveProfile V g B P c p.1) p.2) := by
  have hGrad : Continuous (fun p : ℝ × EuclideanSpace ℝ (Fin d) =>
      gradient (langevinPositiveProfile V g B P c p.1) p.2) := by
    have hc := (continuous_gradient_langevinKernel_integral_time_initial hB hV ρ hρ.le hHess
      (hg.of_le (by norm_num)) hgc).comp ((continuous_real_toNNReal.comp continuous_fst).prodMk continuous_snd)
    apply hc.congr
    intro p
    change gradient (fun y => ∫ z, g z ∂langevinKernel V B P p.1.toNNReal y) p.2 =
      gradient (fun y => c + ∫ z, g z ∂langevinKernel V B P p.1.toNNReal y) p.2
    simp only [gradient, fderiv_const_add]
  have hc := (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin d))).continuous.comp hGrad
  simpa only [Function.comp_def, gradient, LinearIsometryEquiv.apply_symm_apply] using hc

include hB hV hg hgc hρ hHess in
theorem continuous_langevinPositiveSquareInterpolation (T : ℝ) :
    Continuous (fun p : ℝ × EuclideanSpace ℝ (Fin d) =>
      langevinPositiveSquareInterpolation V g B P c T p.1 p.2) := by
  obtain ⟨A, hA, hBound⟩ := langevinPositiveProfile_uniform_norm_bound hB hV hg hgc ρ hρ hHess c
  have hF : Continuous (Function.uncurry (fun r x => (langevinPositiveProfile V g B P c r x) ^ 2)) :=
    (continuous_langevinPositiveProfile_time_initial hB hV hg hgc ρ hρ hHess c).pow 2
  have hBnd (r : ℝ) (x : EuclideanSpace ℝ (Fin d)) : ‖(langevinPositiveProfile V g B P c r x) ^ 2‖ ≤ A ^ 2 := by
    rw [norm_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) (hBound r x) 2
  exact (continuous_langevinKernel_integral_moving_bounded hB hV ρ hρ.le hHess _ hF (A ^ 2) hBnd).comp
    ((continuous_const.sub continuous_fst).prodMk ((continuous_real_toNNReal.comp continuous_fst).prodMk continuous_snd))

include hB hV hg hgc hρ hHess hm hpos in
theorem langevinPositiveSquareInterpolation_lower (T s : ℝ) (x : EuclideanSpace ℝ (Fin d)) :
    m ^ 2 ≤ langevinPositiveSquareInterpolation V g B P c T s x := by
  let := langevinKernel_isMarkovKernel hB hV ρ hρ.le hHess s.toNNReal
  obtain ⟨A, hA, hBound⟩ := langevinPositiveProfile_uniform_norm_bound hB hV hg hgc ρ hρ hHess c
  have hq : ContDiff ℝ 1 (langevinPositiveProfile V g B P c (T - s)) := contDiff_const.add
    (contDiff_one_langevinKernel_integral hB hV ρ hρ.le hHess (hg.of_le (by norm_num)) hgc (T - s).toNNReal)
  have hi : Integrable (fun y => (langevinPositiveProfile V g B P c (T - s) y) ^ 2)
      (langevinKernel V B P s.toNNReal x) := (integrable_const (A ^ 2)).mono'
    (hq.continuous.pow 2).aestronglyMeasurable (Eventually.of_forall fun y => by
      rw [norm_pow]; exact pow_le_pow_left₀ (norm_nonneg _) (hBound _ y) 2)
  have hh := integral_mono (integrable_const (m ^ 2)) hi (fun y =>
    pow_le_pow_left₀ hm.le (langevinPositiveProfile_lower hB hV hg hgc ρ hρ.le hHess c m hpos (T-s) y) 2)
  change m ^ 2 ≤ ∫ y, (langevinPositiveProfile V g B P c (T-s) y) ^ 2 ∂langevinKernel V B P s.toNNReal x
  simpa only [integral_const, measureReal_def, measure_univ, ENNReal.toReal_one, one_smul] using hh



include hB hV hg hgc hρ hHess in
private theorem positiveSquareTestData :
    ∃ (A : ℝ) (L : NNReal),
      (∀ r, ContDiff ℝ 1 (fun x => (langevinPositiveProfile V g B P c r x) ^ 2)) ∧
      Continuous (fun p : ℝ × EuclideanSpace ℝ (Fin d) =>
        fderiv ℝ (fun x => (langevinPositiveProfile V g B P c p.1 x) ^ 2) p.2) ∧
      (∀ r x, ‖(langevinPositiveProfile V g B P c r x) ^ 2‖ ≤ A) ∧
      (∀ r x, ‖fderiv ℝ (fun y => (langevinPositiveProfile V g B P c r y) ^ 2) x‖ ≤ L) := by
  let q := langevinPositiveProfile V g B P c
  have hq (r : ℝ) : ContDiff ℝ 1 (q r) := contDiff_const.add
    (contDiff_one_langevinKernel_integral hB hV ρ hρ.le hHess (hg.of_le (by norm_num)) hgc r.toNNReal)
  obtain ⟨A, hA, hBound⟩ := langevinPositiveProfile_uniform_norm_bound hB hV hg hgc ρ hρ hHess c
  obtain ⟨G, hG, hGrad⟩ := langevinPositiveProfile_uniform_gradient_bound hB hV hg hgc ρ hρ.le hHess c
  refine ⟨A ^ 2, Real.toNNReal (2 * A * G), (fun r => (hq r).pow 2), ?_, ?_, ?_⟩
  · have hc := ((continuous_langevinPositiveProfile_time_initial hB hV hg hgc ρ hρ hHess c).const_mul 2).smul
      (continuous_fderiv_langevinPositiveProfile_time_initial hB hV hg hgc ρ hρ hHess c)
    apply hc.congr
    intro p
    change (2 * q p.1 p.2) • fderiv ℝ (q p.1) p.2 = fderiv ℝ (fun y => q p.1 y ^ 2) p.2
    simp only [fderiv_fun_pow 2 ((hq p.1).differentiable one_ne_zero p.2), Nat.reduceSub, pow_one, two_smul, two_mul]
  · intro r x
    rw [norm_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) (hBound r x) 2
  · intro r x
    exact norm_fderiv_le_of_lipschitz ℝ
      (bounded_c1_square_lipschitz (hq r) A G hA hG (hBound r) (hGrad r))

include hB hV hg hgc hρ hHess in
theorem contDiff_one_langevinPositiveSquareInterpolation (T s : ℝ) :
    ContDiff ℝ 1 (langevinPositiveSquareInterpolation V g B P c T s) := by
  obtain ⟨A, L, hSq, _hFD, hBound, hLipBound⟩ := positiveSquareTestData hB hV hg hgc ρ hρ hHess c
  have hLip : LipschitzWith L (fun x => (langevinPositiveProfile V g B P c (T-s) x) ^ 2) :=
    lipschitzWith_of_nnnorm_fderiv_le ((hSq _).differentiable one_ne_zero) (fun x => by exact_mod_cast hLipBound _ x)
  exact contDiff_one_langevinKernel_integral_bounded_c1 hB hV ρ hρ.le hHess (hSq _) A (hBound _) L hLip s.toNNReal

include hB hV hg hgc hρ hHess in
theorem continuous_fderiv_langevinPositiveSquareInterpolation (T : ℝ) :
    Continuous (fun p : ℝ × EuclideanSpace ℝ (Fin d) =>
      fderiv ℝ (langevinPositiveSquareInterpolation V g B P c T p.1) p.2) := by
  obtain ⟨A, L, hSq, hFD, hBound, hLipBound⟩ := positiveSquareTestData hB hV hg hgc ρ hρ hHess c
  have hc := continuous_fderiv_langevinKernel_integral_moving_bounded_c1 hB hV ρ hρ.le hHess
    (fun r x => (langevinPositiveProfile V g B P c r x) ^ 2) hSq hFD A hBound L hLipBound
  exact hc.comp ((continuous_const.sub continuous_fst).prodMk
    ((continuous_real_toNNReal.comp continuous_fst).prodMk continuous_snd))

include hB hV hg hgc hρ hHess in
set_option maxHeartbeats 700000 in
/-- The actual positive-square interpolation is exactly the genuine square
interpolation plus constant semigroup terms on its written time interval. -/
theorem langevinPositiveSquareInterpolation_eq_expansion (T s : ℝ)
    (hs : 0 ≤ s) (hsT : s ≤ T) (x : EuclideanSpace ℝ (Fin d)) :
    langevinPositiveSquareInterpolation V g B P c T s x =
      (c ^ 2 + 2 * c * ∫ y, g y ∂langevinKernel V B P T.toNNReal x) +
        langevinSquareInterpolation V g B P T s x := by
  let := langevinKernel_isMarkovKernel hB hV ρ hρ.le hHess s.toNNReal
  let q := fun y => ∫ z, g z ∂langevinKernel V B P (T-s).toNNReal y
  obtain ⟨M, hM0, hM⟩ := compact_continuous_norm_bound hg.continuous hgc
  have hqM : Measurable q := hg.continuous.measurable.stronglyMeasurable.integral_kernel.measurable
  have hqBound (y : EuclideanSpace ℝ (Fin d)) : ‖q y‖ ≤ M :=
    langevinKernel_integral_compact_test_norm_le hB hV ρ hρ.le hHess hM (T-s).toNNReal y
  have hqI : Integrable q (langevinKernel V B P s.toNNReal x) :=
    (integrable_const M).mono' hqM.aestronglyMeasurable (Eventually.of_forall hqBound)
  have hq2I : Integrable (fun y => q y ^ 2) (langevinKernel V B P s.toNNReal x) :=
    (MemLp.of_bound hqM.aestronglyMeasurable M (Eventually.of_forall hqBound) :
      MemLp q 2 (langevinKernel V B P s.toNNReal x)).integrable_sq
  have hsum : s.toNNReal + (T-s).toNNReal = T.toNNReal := by
    apply NNReal.eq
    simp only [NNReal.coe_add, Real.coe_toNNReal _ hs, Real.coe_toNNReal _ (sub_nonneg.mpr hsT),
      Real.coe_toNNReal _ (hs.trans hsT)]
    ring
  have hsem := langevinKernel_integral_semigroup_compact_test hB hV hg.continuous hgc ρ hρ.le hHess
    s.toNNReal (T-s).toNNReal x
  rw [hsum] at hsem
  have he (y : EuclideanSpace ℝ (Fin d)) : (c + q y) ^ 2 = (c ^ 2 + 2 * c * q y) + q y ^ 2 := by ring
  have hAdd := integral_add ((integrable_const (c ^ 2)).add (hqI.const_mul (2 * c))) hq2I
  have hAdd' := integral_add (integrable_const (c ^ 2)) (hqI.const_mul (2 * c))
  simp only [Pi.add_apply] at hAdd hAdd'
  change (∫ y, (c + q y) ^ 2 ∂langevinKernel V B P s.toNNReal x) = _
  rw [integral_congr_ae (Eventually.of_forall he), hAdd, hAdd', integral_const, integral_const_mul]
  simp only [measureReal_def, measure_univ, ENNReal.toReal_one, one_smul]
  rw [hsem]
  rfl

include hB hV hg hgc hρ hHess in
theorem hasDerivAt_langevinPositiveSquareInterpolation (hp : IsProbabilityMeasure (gibbsMeasure volume V))
    (T s : ℝ) (hs : 0 < s) (hsT : s < T) (x : EuclideanSpace ℝ (Fin d)) :
    HasDerivAt (fun r => langevinPositiveSquareInterpolation V g B P c T r x)
      (langevinMovingGradientSqAverage V g B P T s x) s := by
  have hh := (hasDerivAt_langevin_square_interpolation_pointwise hB hV hp hg hgc ρ hρ hHess T s hs hsT x).const_add
    (c ^ 2 + 2 * c * ∫ y, g y ∂langevinKernel V B P T.toNNReal x)
  apply hh.congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds hs hsT] with r hr
  exact langevinPositiveSquareInterpolation_eq_expansion hB hV hg hgc ρ hρ hHess c T r hr.1.le hr.2.le x



include hB hV hg hgc hρ hHess hm hpos in
set_option maxHeartbeats 750000 in
/-- The weighted genuine flow gradient estimate specialized to the square
of the positive backward profile. -/
theorem langevinPositiveSquareInterpolation_weighted_gradient (T s : ℝ) (x : EuclideanSpace ℝ (Fin d)) :
    ‖gradient (langevinPositiveSquareInterpolation V g B P c T s) x‖ ^ 2 /
      langevinPositiveSquareInterpolation V g B P c T s x ≤
      2 * Real.exp (-2 * ρ * s.toNNReal) * langevinMovingGradientSqAverage V g B P T s x := by
  obtain ⟨A, L, hSq, _hFD, hBound, hLipBound⟩ := positiveSquareTestData hB hV hg hgc ρ hρ hHess c
  let q := langevinPositiveProfile V g B P c (T-s)
  have hq : ContDiff ℝ 1 q := contDiff_const.add
    (contDiff_one_langevinKernel_integral hB hV ρ hρ.le hHess (hg.of_le (by norm_num)) hgc (T-s).toNNReal)
  have hlower := langevinPositiveProfile_lower hB hV hg hgc ρ hρ.le hHess c m hpos (T-s)
  have hLip : LipschitzWith L (fun y => q y ^ 2) :=
    lipschitzWith_of_nnnorm_fderiv_le ((hSq _).differentiable one_ne_zero) (fun y => by exact_mod_cast hLipBound _ y)
  have hFloor (y : EuclideanSpace ℝ (Fin d)) : m ^ 2 ≤ 0 + q y ^ 2 :=
    (pow_le_pow_left₀ hm.le (hlower y) 2).trans_eq (by ring)
  have hw := langevinKernel_weighted_gradient_le_bounded_c1 hB hV ρ hρ.le hHess
    (hSq (T-s)) A (hBound (T-s)) L hLip 0 (m ^ 2) (sq_pos_of_pos hm) hFloor s.toNNReal x
  dsimp only at hw
  simp only [zero_add] at hw
  change ‖gradient (langevinPositiveSquareInterpolation V g B P c T s) x‖ ^ 2 /
      langevinPositiveSquareInterpolation V g B P c T s x ≤
      Real.exp (-2 * ρ * s.toNNReal) *
        ∫ y, ‖gradient (fun z => q z ^ 2) y‖ ^ 2 / q y ^ 2 ∂langevinKernel V B P s.toNNReal x at hw
  have he (y : EuclideanSpace ℝ (Fin d)) : ‖gradient (fun z => q z ^ 2) y‖ ^ 2 / q y ^ 2 =
      4 * langevinGradientSqProfile V g B P (T-s) y := by
    have hqGrad : gradient q y = gradient (fun z => ∫ w, g w ∂langevinKernel V B P (T-s).toNNReal z) y := by
      change gradient (fun z => c + ∫ w, g w ∂langevinKernel V B P (T-s).toNNReal z) y = _
      simp only [gradient, fderiv_const_add]
    rw [gradient_square_of_c1 hq, norm_smul, norm_mul, Real.norm_ofNat, Real.norm_eq_abs,
      abs_of_pos (hm.trans_le (hlower y)), mul_pow, hqGrad]
    change ((2 * q y) ^ 2 * ‖gradient (fun z => ∫ w, g w ∂langevinKernel V B P (T-s).toNNReal z) y‖ ^ 2) / q y ^ 2 =
      4 * ‖gradient (fun z => ∫ w, g w ∂langevinKernel V B P (T-s).toNNReal z) y‖ ^ 2
    have hqNE : q y ≠ 0 := (hm.trans_le (hlower y)).ne'
    field_simp [hqNE]
    ring
  rw [integral_congr_ae (Eventually.of_forall he), integral_const_mul] at hw
  convert hw using 1
  change 2 * Real.exp (-2 * ρ * s.toNNReal) *
    (2 * ∫ y, langevinGradientSqProfile V g B P (T-s) y ∂langevinKernel V B P s.toNNReal x) = _
  ring

end Source
end CutoffRigidity
