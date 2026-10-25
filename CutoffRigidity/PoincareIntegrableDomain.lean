module
public import CutoffRigidity.LangevinLocalSmoothPoincare
public import CutoffRigidity.L2FatouBounds
public import CutoffRigidity.SobolevScalarChain
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv

/-! # Removing an L² premise from the smooth Poincare domain

Bounded smooth normal contractions and Fatou derive the second moment of
an integrable C¹ function from its finite actual gradient energy. This
removes an integrability premise in the log-likelihood application; it does
not assert classical regularity of arbitrary transition log densities.
-/
public section
namespace CutoffRigidity
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal
variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

@[expose] noncomputable def smoothNormalTruncation (n : ℕ) (r : ℝ) : ℝ :=
  ((n : ℝ)+1) * Real.arctan (r / ((n : ℝ)+1))

theorem hasDerivAt_smoothNormalTruncation (n : ℕ) (r : ℝ) :
    HasDerivAt (smoothNormalTruncation n)
      (1 / (1+(r/((n : ℝ)+1))^2)) r := by
  have hh := ((Real.hasDerivAt_arctan (r / ((n : ℝ)+1))).comp r
    ((hasDerivAt_id r).mul_const (((n : ℝ)+1)⁻¹))).const_mul ((n : ℝ)+1)
  convert! hh using 1
  field_simp

theorem contDiff_smoothNormalTruncation (n : ℕ) : ContDiff ℝ 1 (smoothNormalTruncation n) := by
  have hh : ContDiff ℝ 1 (fun r : ℝ => Real.arctan (r / ((n : ℝ)+1))) :=
    (Real.contDiff_arctan : ContDiff ℝ 1 Real.arctan).comp (contDiff_id.div_const ((n : ℝ)+1))
  exact contDiff_const.mul hh

theorem deriv_smoothNormalTruncation_abs_le_one (n : ℕ) (r : ℝ) :
    |deriv (smoothNormalTruncation n) r| ≤ 1 := by
  rw [(hasDerivAt_smoothNormalTruncation n r).deriv,
    abs_of_nonneg (by positivity : 0 ≤ 1 / (1+(r/((n : ℝ)+1))^2))]
  exact (div_le_one (by positivity)).mpr (by nlinarith [sq_nonneg (r/((n : ℝ)+1))])

theorem smoothNormalTruncation_abs_le (n : ℕ) (r : ℝ) :
    |smoothNormalTruncation n r| ≤ |r| := by
  have hl := scalar_normal_contraction_lipschitz
    ((contDiff_smoothNormalTruncation n).differentiable one_ne_zero) (deriv_smoothNormalTruncation_abs_le_one n)
  have hh := hl.dist_le_mul r 0
  simpa only [smoothNormalTruncation,zero_div,Real.arctan_zero,mul_zero,
    Real.dist_eq,sub_zero,NNReal.coe_one,one_mul] using hh

theorem smoothNormalTruncation_abs_le_bound (n : ℕ) (r : ℝ) :
    |smoothNormalTruncation n r| ≤ ((n : ℝ)+1)*(Real.pi/2) := by
  rw [smoothNormalTruncation,abs_mul,abs_of_pos (by positivity : 0 < (n : ℝ)+1)]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  rw [abs_le]
  exact ⟨(Real.neg_pi_div_two_lt_arctan _).le,(Real.arctan_lt_pi_div_two _).le⟩

theorem tendsto_smoothNormalTruncation (r : ℝ) :
    Tendsto (fun n => smoothNormalTruncation n r) atTop (𝓝 r) := by
  by_cases hr : r=0
  · subst r
    simp only [smoothNormalTruncation,zero_div,Real.arctan_zero,mul_zero]
    exact tendsto_const_nhds
  have ht : Tendsto (fun n : ℕ => r / ((n : ℝ)+1)) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv,mul_zero,one_mul] using
      (tendsto_one_div_add_atTop_nhds_zero_nat).const_mul r
  have htNE : Tendsto (fun n : ℕ => r / ((n : ℝ)+1)) atTop (𝓝[≠] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨ht,Eventually.of_forall (fun n => by
      simpa only [mem_compl_iff,mem_singleton_iff] using div_ne_zero hr (by positivity : (n : ℝ)+1 ≠ 0))⟩
  have hh := ((Real.hasDerivAt_arctan 0).tendsto_slope.comp htNE).const_mul r
  convert! hh using 1
  · ext n
    simp only [smoothNormalTruncation,Function.comp_def,slope_def_field,Real.arctan_zero,sub_zero]
    field_simp [hr]
  · norm_num

set_option maxHeartbeats 700000 in
/-- The L² domain follows from actual L¹ integrability and finite gradient
energy; it is not a premise on the test function. -/
theorem memLp_two_and_poincare_of_integrable_c1
    (ν : Measure E) [IsProbabilityMeasure ν] (C : ℝ)
    (hP : HasLocalSmoothPoincare ν C) (hC : 0 ≤ C)
    {f : E → ℝ} (hf : ContDiff ℝ 1 f) (hInt : Integrable f ν)
    (hGI : Integrable (fun x => ‖gradient f x‖^2) ν) :
    MemLp f 2 ν ∧ variance f ν ≤ C * ∫ x, ‖gradient f x‖^2 ∂ν := by
  let fn := fun n : ℕ => smoothNormalTruncation n ∘ f
  have hfn (n : ℕ) : ContDiff ℝ 1 (fn n) := (contDiff_smoothNormalTruncation n).comp hf
  have hfnLp (n : ℕ) : MemLp (fn n) 2 ν :=
    MemLp.of_bound (hfn n).continuous.aestronglyMeasurable (((n : ℝ)+1)*(Real.pi/2))
      (Eventually.of_forall (fun x => smoothNormalTruncation_abs_le_bound n (f x)))
  have hgradBound (n : ℕ) (x : E) : ‖gradient (fn n) x‖ ≤ ‖gradient f x‖ :=
    norm_gradient_scalar_normal_comp_le
      ((contDiff_smoothNormalTruncation n).differentiable one_ne_zero) (hf.differentiable one_ne_zero)
      (deriv_smoothNormalTruncation_abs_le_one n) x
  have hgradSqBound (n : ℕ) (x : E) : ‖gradient (fn n) x‖^2 ≤ ‖gradient f x‖^2 :=
    pow_le_pow_left₀ (norm_nonneg _) (hgradBound n x) 2
  have hfnGI (n : ℕ) : Integrable (fun x => ‖gradient (fn n) x‖^2) ν := by
    apply hGI.mono' ((continuous_gradient_of_c1 (hfn n)).norm.pow 2).aestronglyMeasurable
    exact Eventually.of_forall (fun x => by
      change ‖‖gradient (fn n) x‖^2‖ ≤ _
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      exact hgradSqBound n x)
  have hMean : Tendsto (fun n => ∫ x, fn n x ∂ν) atTop (𝓝 (∫ x, f x ∂ν)) := by
    apply tendsto_integral_of_dominated_convergence (fun x => ‖f x‖)
      (fun n => (hfn n).continuous.aestronglyMeasurable) hInt.norm
      (fun n => Eventually.of_forall (fun x => smoothNormalTruncation_abs_le n (f x)))
      (Eventually.of_forall (fun x => tendsto_smoothNormalTruncation (f x)))
  let centered := fun n : ℕ => fun x : E => fn n x - ∫ y, fn n y ∂ν
  have hcenterLp (n : ℕ) : MemLp (centered n) 2 ν := (hfnLp n).sub (memLp_const _)
  have hcenterLim : ∀ᵐ x ∂ν, Tendsto (fun n => centered n x) atTop
      (𝓝 (f x - ∫ y, f y ∂ν)) :=
    Eventually.of_forall (fun x => (tendsto_smoothNormalTruncation (f x)).sub hMean)
  have hcenterBound (n : ℕ) : (∫ x, ‖centered n x‖^2 ∂ν) ≤ C * ∫ x, ‖gradient f x‖^2 ∂ν := by
    have hp := hP (fn n) (hfn n) (hfnLp n) (hfnGI n)
    have he := (integral_mono (hfnGI n) hGI (hgradSqBound n))
    have hv : (∫ x, ‖centered n x‖^2 ∂ν) = variance (fn n) ν := by
      rw [variance_eq_integral (hfn n).continuous.aemeasurable]
      simp only [centered,Real.norm_eq_abs,sq_abs]
    rw [hv]
    exact hp.trans (mul_le_mul_of_nonneg_left he hC)
  obtain ⟨hcenter,hbound⟩ := memLp_two_and_second_moment_le_of_ae_tendsto hcenterLp
    (hf.continuous.sub continuous_const).aestronglyMeasurable hcenterLim hcenterBound
  have hfLp : MemLp f 2 ν := by
    have hh := hcenter.add (memLp_const (∫ y, f y ∂ν))
    simpa only [Pi.add_apply,sub_add_cancel] using hh
  refine ⟨hfLp, ?_⟩
  rw [variance_eq_integral hf.continuous.aemeasurable]
  simpa only [Pi.sub_apply,Real.norm_eq_abs,sq_abs] using hbound

end CutoffRigidity
