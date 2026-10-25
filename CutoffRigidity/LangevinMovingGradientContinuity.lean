module
public import CutoffRigidity.LangevinLogInterpolationGradient

/-! # Joint spatial derivative continuity of the actual BGL interpolation

The genuine initial-state variational derivative, joint continuity of the
moving test derivative, and a uniform derivative bound justify another
probability DCT. No extra heat regularity is assumed.
-/
public section
namespace CutoffRigidity
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal
variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

set_option maxHeartbeats 700000 in
theorem continuous_fderiv_langevinNoiseAverage_moving_bounded_c1
    {V : E → ℝ} (hV : ContDiff ℝ 2 V) (ρ : ℝ) (hρ : 0 ≤ ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (F : ℝ → E → ℝ) (hF : ∀ a, ContDiff ℝ 1 (F a))
    (hFD : Continuous (fun p : ℝ × E => fderiv ℝ (F p.1) p.2))
    (M : ℝ) (hBound : ∀ a x, ‖F a x‖ ≤ M)
    (L : NNReal) (hL : ∀ a x, ‖fderiv ℝ (F a) x‖ ≤ L)
    (μ : Measure C(ℝ, E)) [IsProbabilityMeasure μ] :
    Continuous (fun p : ℝ × (NNReal × E) =>
      fderiv ℝ (fun y => ∫ w : C(ℝ, E), F p.1 (langevinSolution V w y p.2.1) ∂μ) p.2.2) := by
  have hLip (a : ℝ) : LipschitzWith L (F a) :=
    lipschitzWith_of_nnnorm_fderiv_le ((hF a).differentiable one_ne_zero)
      (fun x => by exact_mod_cast hL a x)
  let D (p : ℝ × (NNReal × E)) (w : C(ℝ, E)) :=
    fderiv ℝ (fun z => F p.1 (langevinSolution V w z p.2.1)) p.2.2
  have hDI (p : ℝ × (NNReal × E)) : Integrable (D p) μ ∧
      HasFDerivAt (fun y => ∫ w : C(ℝ, E), F p.1 (langevinSolution V w y p.2.1) ∂μ)
        (∫ w, D p w ∂μ) p.2.2 :=
    hasFDerivAt_langevinNoiseAverage_bounded_c1 hV ρ hρ hHess
      (hF p.1) M (hBound p.1) L (hLip p.1) μ p.2.1 p.2.2
  have hDcont (w : C(ℝ, E)) : Continuous (fun p => D p w) := by
    have he (p : ℝ × (NNReal × E)) : D p w =
        (fderiv ℝ (F p.1) (langevinSolution V w p.2.2 p.2.1)).comp
          (fderiv ℝ (fun y => langevinSolution V w y p.2.1) p.2.2) := by
      exact (((hF p.1).differentiable one_ne_zero _).hasFDerivAt.comp p.2.2
        (differentiable_langevinSolution_initial_point hV ρ hρ hHess w.continuous p.2.1.property p.2.2).hasFDerivAt).fderiv
    simp_rw [he]
    exact (hFD.comp (continuous_fst.prodMk
      ((continuous_langevinSolution_time_initial hV ρ hρ hHess w).comp continuous_snd))).clm_comp
        ((continuous_fderiv_langevinSolution_time_initial hV ρ hρ hHess w).comp continuous_snd)
  have hDB (p : ℝ × (NNReal × E)) (w : C(ℝ, E)) : ‖D p w‖ ≤ L := by
    have hh := norm_fderiv_le_of_lipschitz ℝ (x₀ := p.2.2)
      ((hLip p.1).comp (langevinSolution_initial_point_lipschitz hV ρ hρ hHess w.continuous p.2.1.property))
    apply hh.trans
    change (L : ℝ) * Real.exp (-ρ * p.2.1) ≤ L
    exact mul_le_of_le_one_right L.coe_nonneg (Real.exp_le_one_iff.mpr
      (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hρ) p.2.1.property))
  have he : (fun p : ℝ × (NNReal × E) =>
      fderiv ℝ (fun y => ∫ w : C(ℝ, E), F p.1 (langevinSolution V w y p.2.1) ∂μ) p.2.2) =
      fun p => ∫ w, D p w ∂μ := funext (fun p => (hDI p).2.fderiv)
  rw [he]
  apply continuous_iff_continuousAt.mpr
  intro p
  exact tendsto_integral_filter_of_dominated_convergence (fun _ : C(ℝ, E) => (L : ℝ))
    (Eventually.of_forall (fun q => (hDI q).1.aestronglyMeasurable))
    (Eventually.of_forall (fun q => Eventually.of_forall (hDB q))) (integrable_const _)
    (Eventually.of_forall (fun w => (hDcont w).tendsto p))

/-- Actual moving bounded C¹ kernel tests retain joint derivative
continuity by their genuine noise-law representation. -/
theorem continuous_fderiv_langevinKernel_integral_moving_bounded_c1
    {Ω : Type*} [MeasurableSpace Ω] {B : NNReal → Ω → E} {P : Measure Ω}
    (hB : IsEuclideanBrownian B P)
    {V : E → ℝ} (hV : ContDiff ℝ 2 V) (ρ : ℝ) (hρ : 0 ≤ ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (F : ℝ → E → ℝ) (hF : ∀ a, ContDiff ℝ 1 (F a))
    (hFD : Continuous (fun p : ℝ × E => fderiv ℝ (F p.1) p.2))
    (M : ℝ) (hBound : ∀ a x, ‖F a x‖ ≤ M)
    (L : NNReal) (hL : ∀ a x, ‖fderiv ℝ (F a) x‖ ≤ L) :
    Continuous (fun p : ℝ × (NNReal × E) =>
      fderiv ℝ (fun y => ∫ z, F p.1 z ∂langevinKernel V B P p.2.1 y) p.2.2) := by
  let := brownianNoiseLaw_isProbabilityMeasure hB
  have he (a : ℝ) (t : NNReal) : (fun y => ∫ z, F a z ∂langevinKernel V B P t y) =
      (fun y => ∫ w : C(ℝ, E), F a (langevinSolution V w y t) ∂brownianNoiseLaw B P) := by
    funext y
    rw [langevinKernel_apply_noiseLaw hB hV ρ hρ hHess]
    exact integral_map (((langevinSolution_evaluation_continuous hV ρ hρ hHess t.property).comp
      (continuous_const.prodMk continuous_id)).measurable.aemeasurable)
      (hF a).continuous.measurable.aestronglyMeasurable
  simp_rw [he]
  exact continuous_fderiv_langevinNoiseAverage_moving_bounded_c1 hV ρ hρ hHess
    F hF hFD M hBound L hL (brownianNoiseLaw B P)


section LogInterpolation
variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
variable {B : NNReal → Ω → EuclideanSpace ℝ (Fin d)} {P : Measure Ω} (hB : IsEuclideanBrownian B P)
    {V g : EuclideanSpace ℝ (Fin d) → ℝ} (hV : ContDiff ℝ 2 V)
    (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g)
    (ρ : ℝ) (hρ : 0 ≤ ρ)
    (hHess : ∀ x z : EuclideanSpace ℝ (Fin d), ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (c m : ℝ) (hm : 0 < m) (hpos : ∀ x, m ≤ c + g x)

include hB hV hg hgc hρ hHess hm hpos in
/-- The actual logarithmic profile derivative is jointly continuous in
its genuine time parameter and spatial point. -/
theorem continuous_fderiv_langevinLogProfile_time_initial :
    Continuous (fun p : ℝ × EuclideanSpace ℝ (Fin d) =>
      fderiv ℝ (fun y => Real.log (langevinPositiveProfile V g B P c p.1 y)) p.2) := by
  let q := langevinPositiveProfile V g B P c
  have hq (r : ℝ) : ContDiff ℝ 1 (q r) :=
    contDiff_const.add (contDiff_one_langevinKernel_integral hB hV ρ hρ hHess
      (hg.of_le (by norm_num)) hgc r.toNNReal)
  have hlower := langevinPositiveProfile_lower hB hV hg hgc ρ hρ hHess c m hpos
  obtain ⟨A, hA⟩ := hgc.exists_bound_of_continuous hg.continuous
  have hqJoint : Continuous (fun p : ℝ × EuclideanSpace ℝ (Fin d) => q p.1 p.2) :=
    continuous_const.add ((continuous_langevinKernel_integral_time_initial hB hV hg.continuous
      ⟨A, hA⟩ ρ hρ hHess).comp ((continuous_real_toNNReal.comp continuous_fst).prodMk continuous_snd))
  have hGradJoint : Continuous (fun p : ℝ × EuclideanSpace ℝ (Fin d) => gradient (q p.1) p.2) := by
    have hc := (continuous_gradient_langevinKernel_integral_time_initial hB hV ρ hρ hHess
      (hg.of_le (by norm_num)) hgc).comp ((continuous_real_toNNReal.comp continuous_fst).prodMk continuous_snd)
    apply hc.congr
    intro p
    change gradient (fun y => ∫ z, g z ∂langevinKernel V B P p.1.toNNReal y) p.2 =
      gradient (fun y => c + ∫ z, g z ∂langevinKernel V B P p.1.toNNReal y) p.2
    simp only [gradient, fderiv_const_add]
  have hFDJoint : Continuous (fun p : ℝ × EuclideanSpace ℝ (Fin d) => fderiv ℝ (q p.1) p.2) := by
    have hc := (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin d))).continuous.comp hGradJoint
    simpa only [Function.comp_def, gradient, LinearIsometryEquiv.apply_symm_apply] using hc
  have hInv := hqJoint.inv₀ (fun p => (hm.trans_le (hlower p.1 p.2)).ne')
  have hc := hInv.smul hFDJoint
  apply hc.congr
  intro p
  change (q p.1 p.2)⁻¹ • fderiv ℝ (q p.1) p.2 = _
  exact (fderiv.log ((hq p.1).differentiable one_ne_zero p.2)
    (hm.trans_le (hlower p.1 p.2)).ne').symm

include hB hV hg hgc hρ hHess hm hpos in
set_option maxHeartbeats 700000 in
/-- The true BGL01 interpolation has a spatial derivative jointly
continuous in interpolation time and state. All moving test bounds and
logarithmic derivative continuity follow from the source initial data. -/
theorem continuous_fderiv_langevin_log_interpolation (T : ℝ) :
    Continuous (fun p : ℝ × EuclideanSpace ℝ (Fin d) =>
      fderiv ℝ (fun z => ∫ y,
        Real.log (langevinPositiveProfile V g B P c (2 * T - p.1) y)
          ∂langevinKernel V B P p.1.toNNReal z) p.2) := by
  let q := langevinPositiveProfile V g B P c
  let F := fun r x => Real.log (q r x)
  have hq (r : ℝ) : ContDiff ℝ 1 (q r) :=
    contDiff_const.add (contDiff_one_langevinKernel_integral hB hV ρ hρ hHess
      (hg.of_le (by norm_num)) hgc r.toNNReal)
  have hlower := langevinPositiveProfile_lower hB hV hg hgc ρ hρ hHess c m hpos
  have hF (r : ℝ) : ContDiff ℝ 1 (F r) := (hq r).log (fun x => (hm.trans_le (hlower r x)).ne')
  obtain ⟨A, hA⟩ := hgc.exists_bound_of_continuous hg.continuous
  have hUpper (r : ℝ) (x : EuclideanSpace ℝ (Fin d)) : q r x ≤ |c| + A := by
    exact (le_abs_self _).trans ((abs_add_le _ _).trans
      (add_le_add (le_refl _) (by simpa only [Real.norm_eq_abs] using
        langevinKernel_integral_compact_test_norm_le hB hV ρ hρ hHess hA r.toNNReal x)))
  have hFBound (r : ℝ) (x : EuclideanSpace ℝ (Fin d)) :
      ‖F r x‖ ≤ |Real.log m| + |Real.log (|c| + A)| := by
    rw [Real.norm_eq_abs]
    apply abs_le.mpr
    have hl := Real.log_le_log hm (hlower r x)
    have hu := Real.log_le_log (hm.trans_le (hlower r x)) (hUpper r x)
    constructor
    · linarith [neg_abs_le (Real.log m), abs_nonneg (Real.log (|c| + A))]
    · linarith [le_abs_self (Real.log (|c| + A)), abs_nonneg (Real.log m)]
  obtain ⟨G, hG, hGrad⟩ := langevinPositiveProfile_uniform_gradient_bound hB hV hg hgc ρ hρ hHess c
  let L := Real.toNNReal (G / m)
  have hL (r : ℝ) (x : EuclideanSpace ℝ (Fin d)) : ‖fderiv ℝ (F r) x‖ ≤ L :=
    norm_fderiv_le_of_lipschitz ℝ
      (lipschitzWith_log_of_c1 (hq r) m G hm (hlower r) hG (hGrad r))
  have hc := continuous_fderiv_langevinKernel_integral_moving_bounded_c1 hB hV ρ hρ hHess F hF
    (continuous_fderiv_langevinLogProfile_time_initial hB hV hg hgc ρ hρ hHess c m hm hpos)
    _ hFBound L hL
  exact hc.comp (((continuous_const.mul continuous_const).sub continuous_fst).prodMk
    ((continuous_real_toNNReal.comp continuous_fst).prodMk continuous_snd))

include hB hV hg hgc hρ hHess hm hpos in
theorem continuous_gradient_langevin_log_interpolation (T : ℝ) :
    Continuous (fun p : ℝ × EuclideanSpace ℝ (Fin d) =>
      gradient (fun z => ∫ y,
        Real.log (langevinPositiveProfile V g B P c (2 * T - p.1) y)
          ∂langevinKernel V B P p.1.toNNReal z) p.2) :=
  (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin d))).symm.continuous.comp
    (continuous_fderiv_langevin_log_interpolation hB hV hg hgc ρ hρ hHess c m hm hpos T)

end LogInterpolation
end CutoffRigidity
