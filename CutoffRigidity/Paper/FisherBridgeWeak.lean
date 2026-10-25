module

public import CutoffRigidity.GibbsCompactWeakH1
public import CutoffRigidity.EigenfunctionCaccioppoli

/-!
# Smooth-test weak gradients lie in the closed Gibbs gradient graph

A Gibbs L² function whose distributional gradient, tested only against
smooth compactly supported functions, is a Gibbs L² vector field belongs to
the actual closed Gibbs gradient graph. Smooth cutoffs localize; the compact
localizations are mollified, and strong Lebesgue graph limits are transferred.
-/

public section

namespace CutoffRigidity

open MeasureTheory Filter Topology ContinuousLinearMap
open scoped Convolution ContDiff

variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

/-! ## Mollification with smooth tests only -/

/-- Weak first derivatives tested against smooth compact functions commute
with smooth compact convolution. -/
theorem coordinateDerivative_bumpMollification_of_smooth_weak_derivative
    (φ : ContDiffBump (0 : E)) {g H : E → ℝ} (hg : LocallyIntegrable g volume) (j : Fin d)
    (hweak : ∀ ψ : E → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      (∫ y, g y * coordinateDerivative j ψ y) = -(∫ y, H y * ψ y)) (x : E) :
    coordinateDerivative j (bumpMollification φ g) x = bumpMollification φ H x := by
  let k := φ.normed volume
  have hk : ContDiff ℝ ∞ k := φ.contDiff_normed
  have hkc : HasCompactSupport k := φ.hasCompactSupport_normed
  unfold bumpMollification
  rw [coordinateDerivative_convolution_kernel (hk.of_le (by simp)) hkc hg,
    scalar_convolution_eq_shifted_kernel, scalar_convolution_eq_shifted_kernel]
  let ψ (y : E) := k (x - y)
  have hψ : ContDiff ℝ ∞ ψ := hk.comp (contDiff_const.sub contDiff_id)
  have hψc : HasCompactSupport ψ := hkc.comp_homeomorph (Homeomorph.subLeft x)
  have hh := hweak ψ hψ hψc
  have hp (y : E) : coordinateDerivative j ψ y = -coordinateDerivative j k (x - y) :=
    coordinateDerivative_reflect (hk.differentiable (by simp)) x j y
  simp_rw [hp] at hh
  simp only [mul_neg, integral_neg] at hh
  have he := neg_inj.mp hh
  simpa only [ψ, mul_comm] using he

theorem project_mollifiedGradientLp_of_smooth_weak_derivative (φ : ContDiffBump (0 : E))
    {g : E → ℝ} (hg : LocallyIntegrable g volume) (hgc : HasCompactSupport g)
    (H : E →₂[volume] ℝ) (j : Fin d)
    (hweak : ∀ ψ : E → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      (∫ y, g y * coordinateDerivative j ψ y) = -(∫ y, H y * ψ y)) :
    (EuclideanSpace.proj j : E →L[ℝ] ℝ).compLp (mollifiedGradientLp φ g hg hgc) =
      bumpMollificationLp φ (fun x => H x) (Lp.stronglyMeasurable H).measurable (Lp.memLp H) := by
  apply Lp.ext
  filter_upwards [(EuclideanSpace.proj j : E →L[ℝ] ℝ).coeFn_compLp (mollifiedGradientLp φ g hg hgc),
    (mollifiedGradient_memLp φ hg hgc).coeFn_toLp,
    (bumpMollification_L2_contraction φ (Lp.stronglyMeasurable H).measurable (Lp.memLp H)).1.coeFn_toLp]
    with x hp hgrad hH
  rw [hp]
  unfold mollifiedGradientLp bumpMollificationLp
  rw [hgrad, hH]
  change (gradient (bumpMollification φ g) x) j = bumpMollification φ (fun y => H y) x
  rw [← fderiv_single_eq_gradient_coordinate]
  exact coordinateDerivative_bumpMollification_of_smooth_weak_derivative φ hg j hweak x

theorem mollifiedGradientLp_tendsto_of_smooth_weak_derivatives
    (φ : ℕ → ContDiffBump (0 : E)) (hφ : Tendsto (fun n => (φ n).rOut) atTop (𝓝 0))
    {g : E → ℝ} (hg : LocallyIntegrable g volume) (hgc : HasCompactSupport g)
    (H : Fin d → E →₂[volume] ℝ)
    (hweak : ∀ j : Fin d, ∀ ψ : E → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      (∫ y, g y * coordinateDerivative j ψ y) = -(∫ y, H j y * ψ y)) :
    Tendsto (fun n => mollifiedGradientLp (φ n) g hg hgc) atTop (𝓝 (euclideanL2Assemble H)) := by
  apply tendsto_euclideanL2_of_coordinate_tendsto
  intro j
  simp_rw [project_mollifiedGradientLp_of_smooth_weak_derivative _ hg hgc (H j) j (hweak j)]
  rw [euclideanL2_project_assemble]
  have hh := bumpMollificationLp_tendsto φ hφ (fun x => H j x)
    (Lp.stronglyMeasurable (H j)).measurable (Lp.memLp (H j))
  simpa only [Lp.toLp_coeFn] using hh

/-- Compact Lebesgue L² functions with Lebesgue L² weak derivatives, tested
against smooth compact functions only, lift to the closed Gibbs graph. -/
theorem exists_gibbsSobolev_of_compact_smooth_weak_derivatives {V g : E → ℝ}
    (hV : ContDiff ℝ 2 V) (hprob : IsProbabilityMeasure (gibbsMeasure volume V))
    (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (hgm : Measurable g) (hg : MemLp g 2 volume) (hgc : HasCompactSupport g)
    (H : Fin d → E →₂[volume] ℝ)
    (hweak : ∀ j : Fin d, ∀ ψ : E → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      (∫ y, g y * coordinateDerivative j ψ y) = -(∫ y, H j y * ψ y)) :
    ∃ v : gibbsSobolevGraph hV hprob,
      gibbsSobolevInclusion hV hprob v = volumeToGibbsL2 hV ρ hρ hHess (hg.toLp g) ∧
      gibbsSobolevDerivative hV hprob v =
        volumeToGibbsL2Vector hV ρ hρ hHess (euclideanL2Assemble H) := by
  let ε : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hε (n : ℕ) : 0 < ε n := by dsimp [ε]; positivity
  let φ (n : ℕ) : ContDiffBump (0 : E) := euclideanMollifierBump (ε n) (hε n)
  have hφ : Tendsto (fun n => (φ n).rOut) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  let f (n : ℕ) := bumpMollification (φ n) g
  have hf (n : ℕ) : ContDiff ℝ 2 (f n) :=
    (bumpMollification_contDiff (φ n) (hg.locallyIntegrable (by norm_num))).of_le (by norm_num)
  have hfc (n : ℕ) : HasCompactSupport (f n) := bumpMollification_hasCompactSupport (φ n) hgc
  have hlimf : Tendsto (fun n => compactC2VolumeLp (f n) (hf n) (hfc n)) atTop (𝓝 (hg.toLp g)) :=
    bumpMollificationLp_tendsto φ hφ g hgm hg
  have hlimG : Tendsto (fun n => compactC2VolumeGradientLp (f n) (hf n) (hfc n))
      atTop (𝓝 (euclideanL2Assemble H)) :=
    mollifiedGradientLp_tendsto_of_smooth_weak_derivatives φ hφ
      (hg.locallyIntegrable (by norm_num)) hgc H hweak
  exact exists_gibbsSobolev_of_volume_L2_graph_limit hV hprob ρ hρ hHess f hf hfc
    (hg.toLp g) (euclideanL2Assemble H) hlimf hlimG

/-! ## Local Lebesgue integrability of Gibbs L² functions -/

/-- Gibbs L² functions are locally Lebesgue integrable, since the Gibbs
density is continuous and positive. -/
theorem locallyIntegrable_volume_of_memLp_gibbs {V : E → ℝ} (hV : Continuous V)
    (hprob : IsProbabilityMeasure (gibbsMeasure volume V))
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → F}
    (hf : MemLp f 2 (gibbsMeasure volume V)) : LocallyIntegrable f volume := by
  have hi : Integrable f (gibbsMeasure volume V) := hf.integrable (by norm_num)
  have hv := (integrable_gibbsMeasure_iff volume hV.measurable f).mp hi
  have hl := hv.locallyIntegrable.continuous_smul (g := fun x => Real.exp (V x)) (by fun_prop)
  refine hl.congr (Eventually.of_forall fun x => ?_)
  change Real.exp (V x) • Real.exp (-V x) • f x = f x
  rw [smul_smul, ← Real.exp_add, add_neg_cancel, Real.exp_zero, one_smul]

/-- A compact continuous cutoff of a Gibbs L² function lies in Lebesgue L². -/
theorem memLp_volume_of_cutoff_mul_gibbs {V χ f : E → ℝ} (hV : Continuous V)
    (hprob : IsProbabilityMeasure (gibbsMeasure volume V))
    (hχ : Continuous χ) (hχc : HasCompactSupport χ) (hf : MemLp f 2 (gibbsMeasure volume V)) :
    MemLp (fun x => χ x * f x) 2 volume := by
  have h := compact_cutoff_gibbsLp_memLp_volume hV hprob hχ hχc (hf.toLp f)
  refine (memLp_congr_ae ?_).mp h
  filter_upwards [(gibbsMeasure_ae_eq_iff volume hV.measurable).mp hf.coeFn_toLp] with x hx
  rw [hx]

theorem integrable_compact_mul_of_locallyIntegrable {c f : E → ℝ} (hc : Continuous c)
    (hcc : HasCompactSupport c) (hf : LocallyIntegrable f volume) :
    Integrable (fun x => c x * f x) volume := by
  simpa only [smul_eq_mul] using hf.integrable_smul_left_of_hasCompactSupport hc hcc

theorem gradient_hasCompactSupport {φ : E → ℝ} (hφc : HasCompactSupport φ) :
    HasCompactSupport (gradient φ) :=
  (hφc.fderiv ℝ).comp_left (g := (InnerProductSpace.toDual ℝ E).symm) (by simp)

theorem coordinateDerivative_hasCompactSupport {φ : E → ℝ} (hφc : HasCompactSupport φ)
    (j : Fin d) : HasCompactSupport (coordinateDerivative j φ) :=
  hφc.fderiv_apply ℝ (EuclideanSpace.single j 1)

/-- The coordinate of an integrable Euclidean vector integral. -/
theorem integral_euclidean_apply {F : E → E} (hF : Integrable F volume) (j : Fin d) :
    (∫ x, F x) j = ∫ x, F x j := by
  have h := (EuclideanSpace.proj j : E →L[ℝ] ℝ).integral_comp_comm hF
  simpa using h.symm

/-- The vector weak-gradient identity gives the coordinate identities. -/
theorem coordinate_weak_derivative_of_weak_gradient {u : E → ℝ} {G : E → E}
    (hu : LocallyIntegrable u volume) (hG : LocallyIntegrable G volume)
    {φ : E → ℝ} (hφ : ContDiff ℝ 1 φ) (hφc : HasCompactSupport φ)
    (hweak : ∫ x, u x • gradient φ x = -∫ x, φ x • G x) (j : Fin d) :
    (∫ x, u x * coordinateDerivative j φ x) = -(∫ x, φ x * G x j) := by
  have h1 : Integrable (fun x => u x • gradient φ x) volume :=
    hu.integrable_smul_right_of_hasCompactSupport (continuous_gradient_of_c1 hφ)
      (gradient_hasCompactSupport hφc)
  have h2 : Integrable (fun x => φ x • G x) volume :=
    hG.integrable_smul_left_of_hasCompactSupport hφ.continuous hφc
  have h := congrArg (fun v : E => v j) hweak
  simp only [PiLp.neg_apply, integral_euclidean_apply h1, integral_euclidean_apply h2] at h
  simpa only [PiLp.smul_apply, smul_eq_mul, coordinateDerivative,
    fderiv_single_eq_gradient_coordinate] using h

/-! ## Smooth cutoff exhaustion -/

/-- Smooth compact cutoffs tending pointwise eventually to one, whose
gradients have an inverse-radius bound. -/
theorem exists_smooth_cutoff_exhaustion_infty :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ χ : ℕ → E → ℝ,
      (∀ n, ContDiff ℝ ∞ (χ n)) ∧ (∀ n, HasCompactSupport (χ n)) ∧
      (∀ n x, 0 ≤ χ n x ∧ χ n x ≤ 1) ∧
      (∀ x, ∀ᶠ n : ℕ in Filter.atTop, χ n x = 1) ∧
      (∀ n x, ‖gradient (χ n) x‖ ≤ C / ((n : ℝ) + 1)) := by
  let φ : ContDiffBump (0 : E) := ⟨1, 2, by norm_num, by norm_num⟩
  have hφ : ContDiff ℝ 2 (φ : E → ℝ) := φ.contDiff
  have hGφ : Continuous (gradient (φ : E → ℝ)) :=
    (differentiable_gradient_of_contDiff_two hφ).continuous
  obtain ⟨C, hC0, hC⟩ := exists_nonneg_bound_of_continuous_compactSupport hGφ
    (gradient_hasCompactSupport φ.hasCompactSupport)
  let ψ (n : ℕ) : ContDiffBump (0 : E) :=
    ⟨(n : ℝ) + 1, 2 * ((n : ℝ) + 1), by positivity, by nlinarith [Nat.cast_nonneg (α := ℝ) n]⟩
  let χ : ℕ → E → ℝ := fun n x => ψ n x
  have hscale (n : ℕ) : χ n = fun x => φ ((((n : ℝ) + 1)⁻¹) • x) := by
    funext x
    dsimp only [χ]
    rw [(ψ n).apply, φ.apply]
    have hn : (n : ℝ) + 1 ≠ 0 := by positivity
    simp [ψ, φ, hn]
  refine ⟨C, hC0, χ, (fun n => (ψ n).contDiff), (fun n => (ψ n).hasCompactSupport),
    (fun n x => ⟨(ψ n).nonneg, (ψ n).le_one⟩), ?_, ?_⟩
  · intro x
    have hevent : ∀ᶠ n : ℕ in Filter.atTop, ‖x‖ ≤ (n : ℝ) + 1 :=
      (tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop ‖x‖)).mono
        (fun n hn => by linarith)
    filter_upwards [hevent] with n hn
    exact (ψ n).one_of_mem_closedBall (by simpa [ψ, Metric.mem_closedBall, dist_zero_right] using hn)
  · intro n x
    rw [hscale n, gradient_comp_scalar (hφ.differentiable (by norm_num))]
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos (by positivity : (0 : ℝ) < n + 1)]
    calc
      _ ≤ ((n : ℝ) + 1)⁻¹ * C := mul_le_mul_of_nonneg_left (hC _) (by positivity)
      _ = _ := by ring

/-! ## Localized lifts and the global graph limit -/

/-- The product rule for coordinate derivatives. -/
theorem coordinateDerivative_mul {χ ψ : E → ℝ} (hχ : Differentiable ℝ χ)
    (hψ : Differentiable ℝ ψ) (j : Fin d) (x : E) :
    coordinateDerivative j (fun y => χ y * ψ y) x =
      χ x * coordinateDerivative j ψ x + ψ x * coordinateDerivative j χ x := by
  simp only [coordinateDerivative]
  rw [fderiv_fun_mul (hχ x) (hψ x)]
  simp only [add_apply, smul_apply, smul_eq_mul]

/-- A smooth compact cutoff of a smooth-test weak gradient pair lifts to the
closed Gibbs graph, with the product-rule gradient. -/
theorem exists_gibbsSobolev_cutoff_of_smooth_weak_gradient {V χ u : E → ℝ} {G : E → E}
    (hV : ContDiff ℝ 2 V) (hprob : IsProbabilityMeasure (gibbsMeasure volume V))
    (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ)
    (hum : Measurable u) (hu : MemLp u 2 (gibbsMeasure volume V))
    (hG : MemLp G 2 (gibbsMeasure volume V))
    (hweak : ∀ j : Fin d, ∀ φ : E → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      (∫ x, u x * coordinateDerivative j φ x) = -(∫ x, φ x * G x j)) :
    ∃ v : gibbsSobolevGraph hV hprob,
      (gibbsSobolevInclusion hV hprob v : E → ℝ) =ᵐ[gibbsMeasure volume V]
        (fun x => χ x * u x) ∧
      (gibbsSobolevDerivative hV hprob v : E → E) =ᵐ[gibbsMeasure volume V]
        (fun x => χ x • G x + u x • gradient χ x) := by
  have hVc := hV.continuous
  have hχ1 : ContDiff ℝ 1 χ := hχ.of_le (by simp)
  have hχ2 : ContDiff ℝ 2 χ := hχ.of_le (by simp)
  have hGj (j : Fin d) : MemLp (fun x => G x j) 2 (gibbsMeasure volume V) := by
    have hm : AEStronglyMeasurable (fun x => G x j) (gibbsMeasure volume V) :=
      (EuclideanSpace.proj j : E →L[ℝ] ℝ).continuous.comp_aestronglyMeasurable
        hG.aestronglyMeasurable
    apply hG.of_le_mul (c := 1) hm
    filter_upwards with x
    simpa only [one_mul] using (PiLp.norm_apply_le (G x) j)
  have hul := locallyIntegrable_volume_of_memLp_gibbs hVc hprob hu
  have hGl (j : Fin d) := locallyIntegrable_volume_of_memLp_gibbs hVc hprob (hGj j)
  let g : E → ℝ := fun x => χ x * u x
  have hgm : Measurable g := hχ.continuous.measurable.mul hum
  have hgL : MemLp g 2 volume := memLp_volume_of_cutoff_mul_gibbs hVc hprob hχ.continuous hχc hu
  have hgc : HasCompactSupport g := by
    simpa only [g, Pi.mul_def] using hχc.mul_right (f' := u)
  have hDχ (j : Fin d) : Continuous (coordinateDerivative j χ) :=
    (c1_coordinateDerivative_of_c2 hχ2 j).continuous
  have hHL (j : Fin d) : MemLp (fun x => χ x * G x j + coordinateDerivative j χ x * u x) 2 volume :=
    (memLp_volume_of_cutoff_mul_gibbs hVc hprob hχ.continuous hχc (hGj j)).add
      (memLp_volume_of_cutoff_mul_gibbs hVc hprob (hDχ j)
        (coordinateDerivative_hasCompactSupport hχc j) hu)
  let H : Fin d → E →₂[volume] ℝ := fun j => (hHL j).toLp _
  have hweakg : ∀ j : Fin d, ∀ ψ : E → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      (∫ y, g y * coordinateDerivative j ψ y) = -(∫ y, H j y * ψ y) := by
    intro j ψ hψ hψc
    have hψ1 : ContDiff ℝ 1 ψ := hψ.of_le (by simp)
    have hψ2 : ContDiff ℝ 2 ψ := hψ.of_le (by simp)
    have hp := hweak j (fun y => χ y * ψ y) (hχ.mul hψ) (by
      simpa only [Pi.mul_def] using hψc.mul_left (f := χ))
    have hprod (x : E) := coordinateDerivative_mul (hχ1.differentiable (by simp))
      (hψ1.differentiable (by simp)) j x
    have hχψc : HasCompactSupport (fun y => χ y * ψ y) := by
      simpa only [Pi.mul_def] using hψc.mul_left (f := χ)
    have hDψ : Continuous (coordinateDerivative j ψ) :=
      (c1_coordinateDerivative_of_c2 hψ2 j).continuous
    have i1 : Integrable (fun x => (χ x * coordinateDerivative j ψ x) * u x) volume :=
      integrable_compact_mul_of_locallyIntegrable (hχ.continuous.mul hDψ)
        (by simpa only [Pi.mul_def] using hχc.mul_right (f' := coordinateDerivative j ψ)) hul
    have i2 : Integrable (fun x => (ψ x * coordinateDerivative j χ x) * u x) volume :=
      integrable_compact_mul_of_locallyIntegrable (hψ.continuous.mul (hDχ j))
        (by simpa only [Pi.mul_def] using hψc.mul_right (f' := coordinateDerivative j χ)) hul
    have i3 : Integrable (fun x => (χ x * ψ x) * G x j) volume :=
      integrable_compact_mul_of_locallyIntegrable (hχ.continuous.mul hψ.continuous) hχψc (hGl j)
    have e0 : (∫ y, H j y * ψ y) =
        ∫ y, (χ y * G y j + coordinateDerivative j χ y * u y) * ψ y := by
      apply integral_congr_ae
      filter_upwards [(hHL j).coeFn_toLp] with y hy
      rw [hy]
    have e1 : (∫ y, g y * coordinateDerivative j ψ y) =
        (∫ y, u y * coordinateDerivative j (fun z => χ z * ψ z) y) -
          ∫ y, (ψ y * coordinateDerivative j χ y) * u y := by
      rw [← integral_sub (i1.add i2 |>.congr (Eventually.of_forall fun x => by
        simp only [Pi.add_apply]; rw [hprod x]; ring)) i2]
      apply integral_congr_ae
      filter_upwards with y
      rw [hprod y]
      simp only [g]
      ring
    have e2 : (∫ y, (χ y * G y j + coordinateDerivative j χ y * u y) * ψ y) =
        (∫ y, (χ y * ψ y) * G y j) + ∫ y, (ψ y * coordinateDerivative j χ y) * u y := by
      rw [← integral_add i3 i2]
      apply integral_congr_ae
      filter_upwards with y
      ring
    rw [e0, e1, e2, hp]
    ring
  obtain ⟨v, hv1, hv2⟩ := exists_gibbsSobolev_of_compact_smooth_weak_derivatives hV hprob ρ hρ hHess
    hgm hgL hgc H hweakg
  refine ⟨v, ?_, ?_⟩
  · rw [hv1]
    exact (volumeToGibbsL2_coeFn hV ρ hρ hHess _).trans
      ((gibbsMeasure_absolutelyContinuous volume V).ae_eq hgL.coeFn_toLp)
  · rw [hv2]
    refine (volumeToGibbsL2Vector_coeFn hV ρ hρ hHess _).trans
      ((gibbsMeasure_absolutelyContinuous volume V).ae_eq ?_)
    have hcoord : ∀ᵐ x ∂(volume : Measure E), ∀ j : Fin d,
        (euclideanL2Assemble H x) j = χ x * G x j + coordinateDerivative j χ x * u x := by
      apply ae_all_iff.mpr
      intro j
      have hp := euclideanL2_project_assemble H j
      filter_upwards [(EuclideanSpace.proj j : E →L[ℝ] ℝ).coeFn_compLp (euclideanL2Assemble H),
        (hHL j).coeFn_toLp] with x h1 h2
      have h3 : ((EuclideanSpace.proj j : E →L[ℝ] ℝ).compLp (euclideanL2Assemble H) : E → ℝ) x =
          H j x := by rw [hp]
      rw [h1] at h3
      change (EuclideanSpace.proj j : E →L[ℝ] ℝ) (euclideanL2Assemble H x) = _ at h3
      rw [← h2]
      simpa using h3
    filter_upwards [hcoord] with x hx
    apply PiLp.ext
    intro j
    rw [hx j]
    simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, coordinateDerivative,
      fderiv_single_eq_gradient_coordinate]
    ring

/-- **Weak gradients lie in the closed domain.** A Gibbs L² function whose
smooth-test distributional gradient is a Gibbs L² field belongs to the actual
closed Gibbs gradient graph, with that field as closed gradient. -/
theorem smooth_weak_gradient_mem_closedGibbsGradient_graph {V u : E → ℝ} {G : E → E}
    (hV : ContDiff ℝ 2 V) (hprob : IsProbabilityMeasure (gibbsMeasure volume V))
    (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (hum : Measurable u) (hu : MemLp u 2 (gibbsMeasure volume V))
    (hG : MemLp G 2 (gibbsMeasure volume V))
    (hweak : ∀ φ : E → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      ∫ x, u x • gradient φ x = -∫ x, φ x • G x) :
    (hu.toLp u, hG.toLp G) ∈ (closedGibbsGradient hV hprob).graph := by
  let μ := gibbsMeasure volume V
  have hVc := hV.continuous
  have hul := locallyIntegrable_volume_of_memLp_gibbs hVc hprob hu
  have hGl := locallyIntegrable_volume_of_memLp_gibbs hVc hprob hG
  have hweakc : ∀ j : Fin d, ∀ φ : E → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      (∫ x, u x * coordinateDerivative j φ x) = -(∫ x, φ x * G x j) :=
    fun j φ hφ hφc => coordinate_weak_derivative_of_weak_gradient hul hGl
      (hφ.of_le (by simp)) hφc (hweak φ hφ hφc) j
  obtain ⟨C, hC0, χ, hχ, hχc, hχbounds, hχone, hχgrad⟩ := exists_smooth_cutoff_exhaustion_infty (d := d)
  let fn (n : ℕ) (x : E) : ℝ := χ n x * u x
  let Gn (n : ℕ) (x : E) : E := χ n x • G x + u x • gradient (χ n) x
  have hlift (n : ℕ) := exists_gibbsSobolev_cutoff_of_smooth_weak_gradient hV hprob ρ hρ hHess
    (hχ n) (hχc n) hum hu hG hweakc
  choose v hv1 hv2 using hlift
  have hfnLp (n : ℕ) : MemLp (fn n) 2 μ :=
    (memLp_congr_ae (hv1 n)).mp (Lp.memLp _)
  have hGnLp (n : ℕ) : MemLp (Gn n) 2 μ :=
    (memLp_congr_ae (hv2 n)).mp (Lp.memLp _)
  have hGχbound (n : ℕ) (x : E) : ‖gradient (χ n) x‖ ≤ C := by
    apply (hχgrad n x).trans
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < n + 1)).mpr
    nlinarith [Nat.cast_nonneg (α := ℝ) n]
  have hcLim : Tendsto (fun n : ℕ => C / ((n : ℝ) + 1)) atTop (𝓝 0) := by
    have hden : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
      tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
    simpa only [div_eq_mul_inv, mul_zero, Function.comp_apply] using
      (tendsto_inv_atTop_zero.comp hden).const_mul C
  have hGχlim (x : E) : Tendsto (fun n => gradient (χ n) x) atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    exact squeeze_zero (fun n => norm_nonneg _) (fun n => hχgrad n x) hcLim
  have hχlim (x : E) : Tendsto (fun n => χ n x) atTop (𝓝 1) :=
    tendsto_const_nhds.congr' ((hχone x).mono (fun n hn => hn.symm))
  have hflim : Tendsto (fun n => (hfnLp n).toLp (fn n)) atTop (𝓝 (hu.toLp u)) := by
    apply tendsto_toL2_of_dominated_sq hu hfnLp (fun x => ‖u x‖ ^ 2) hu.norm.integrable_sq
    · intro n
      filter_upwards with x
      have hb := hχbounds n x
      dsimp only [fn]
      rw [Real.norm_eq_abs, Real.norm_eq_abs]
      have heq : χ n x * u x - u x = (χ n x - 1) * u x := by ring
      rw [heq, abs_mul, mul_pow, sq_abs, sq_abs]
      have hcoef : (χ n x - 1) ^ 2 ≤ 1 := by nlinarith
      nlinarith [sq_nonneg (u x)]
    · filter_upwards with x
      simpa only [fn, one_mul] using (hχlim x).mul_const (u x)
  have hglim : Tendsto (fun n => (hGnLp n).toLp (Gn n)) atTop (𝓝 (hG.toLp G)) := by
    let bound (x : E) := 2 * ‖G x‖ ^ 2 + 2 * C ^ 2 * ‖u x‖ ^ 2
    have hboundInt : Integrable bound μ :=
      (hG.norm.integrable_sq.const_mul 2).add (hu.norm.integrable_sq.const_mul (2 * C ^ 2))
    apply tendsto_toL2_of_dominated_sq hG hGnLp bound hboundInt
    · intro n
      filter_upwards with x
      have hb := hχbounds n x
      have hA : |χ n x - 1| ≤ 1 := by rw [abs_of_nonpos (by linarith)]; linarith
      have heq : Gn n x - G x = (χ n x - 1) • G x + u x • gradient (χ n) x := by
        simp only [Gn]
        module
      have hn : ‖Gn n x - G x‖ ≤ ‖G x‖ + C * ‖u x‖ := by
        rw [heq]
        calc
          _ ≤ ‖(χ n x - 1) • G x‖ + ‖u x • gradient (χ n) x‖ := norm_add_le _ _
          _ = |χ n x - 1| * ‖G x‖ + ‖u x‖ * ‖gradient (χ n) x‖ := by
            rw [norm_smul, norm_smul, Real.norm_eq_abs]
          _ ≤ 1 * ‖G x‖ + ‖u x‖ * C := by
            gcongr
            exact hGχbound n x
          _ = _ := by ring
      have hu0 := norm_nonneg (u x)
      have hg0 := norm_nonneg (G x)
      have hn0 := norm_nonneg (Gn n x - G x)
      dsimp only [bound]
      nlinarith [sq_nonneg (‖G x‖ - C * ‖u x‖)]
    · filter_upwards with x
      have hh := ((hχlim x).smul (tendsto_const_nhds (x := G x))).add
        ((tendsto_const_nhds (x := u x)).smul (hGχlim x))
      simpa only [Gn, one_smul, smul_zero, add_zero] using hh
  have hpairlim := hflim.prodMk_nhds hglim
  apply (closedGibbsGradient_isClosed hV hprob).mem_of_tendsto hpairlim
  refine Eventually.of_forall (fun n => ?_)
  have heV : gibbsSobolevInclusion hV hprob (v n) = (hfnLp n).toLp (fn n) :=
    Lp.ext ((hv1 n).trans (hfnLp n).coeFn_toLp.symm)
  have heD : gibbsSobolevDerivative hV hprob (v n) = (hGnLp n).toLp (Gn n) :=
    Lp.ext ((hv2 n).trans (hGnLp n).coeFn_toLp.symm)
  rw [← heV, ← heD]
  exact (v n).property

end CutoffRigidity
