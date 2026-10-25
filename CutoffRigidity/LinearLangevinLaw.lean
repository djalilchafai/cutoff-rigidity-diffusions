module

public import CutoffRigidity.LangevinBrownian
public import CutoffRigidity.OUKernel
public import CutoffRigidity.GaussianL2Closure
public import CutoffRigidity.BrownianCovarianceIntegrals
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Basic
public import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousMap
public import Mathlib.Topology.ContinuousMap.SecondCountableSpace

/-!
# Explicit linear Langevin response

The pathwise formula below is derived from the actual additive-noise integral
equation by an integrating factor and the fundamental theorem of calculus.
It applies to continuous driving paths, without differentiating the noise.
For actual Brownian drivers, Gaussianity and the covariance quadratures are
derived through jointly Gaussian L² spans, genuine Fubini, and Brownian moments.
The exponential quadratures are evaluated to obtain the exact scalar Mehler
law for the actual canonical Langevin solution with any Brownian noise scale.
-/

public section

namespace CutoffRigidity

open Set MeasureTheory ProbabilityTheory
open scoped Topology NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Removing the whole driving path, rather than only its increment, gives
the ordinary differentiable part needed for the integrating factor. -/
theorem langevin_sub_noise_hasDerivAt {V : E → ℝ} (hV : ContDiff ℝ 2 V)
    {w X : ℝ → E} {x₀ : E} {T t : ℝ}
    (hX : IsLangevinPathOn V w x₀ X T) (ht : t ∈ Ioo 0 T) :
    HasDerivAt (fun s => X s - w s) (-gradient V (X t)) t := by
  have h := (langevin_compensated_hasDerivAt hV hX ht).sub_const (w 0)
  convert h using 1
  ext s
  abel

/-- The actual integrating-factor derivative for a linear potential drift. -/
theorem linear_langevin_integrating_factor_derivative
    {V : E → ℝ} (hV : ContDiff ℝ 2 V) (ρ : ℝ)
    (hgrad : ∀ x : E, gradient V x = ρ • x)
    {w X : ℝ → E} {x₀ : E} {T t : ℝ}
    (hX : IsLangevinPathOn V w x₀ X T) (ht : t ∈ Ioo 0 T) :
    HasDerivAt (fun s => Real.exp (ρ * s) • (X s - w s))
      ((-ρ * Real.exp (ρ * t)) • w t) t := by
  have hY := langevin_sub_noise_hasDerivAt hV hX ht
  rw [hgrad] at hY
  have he : HasDerivAt (fun s : ℝ => Real.exp (ρ * s))
      (ρ * Real.exp (ρ * t)) t := by
    simpa only [id_eq, mul_one, mul_comm] using ((hasDerivAt_id t).const_mul ρ).exp
  have h := he.smul hY
  convert h using 1
  simp only [smul_sub]
  module

/-- Every actual linear Langevin path has the explicit continuous-noise
response formula. This is an identity of trajectories, not a candidate law. -/
theorem linear_langevin_path_response
    {V : E → ℝ} (hV : ContDiff ℝ 2 V) (ρ : ℝ)
    (hgrad : ∀ x : E, gradient V x = ρ • x)
    {w X : ℝ → E} (hw : Continuous w) {x₀ : E} {T : ℝ}
    (hX : IsLangevinPathOn V w x₀ X T) (hT : 0 ≤ T) :
    X T = Real.exp (-ρ * T) • x₀ + w T - Real.exp (-ρ * T) • w 0 -
      (ρ * Real.exp (-ρ * T)) • (∫ s in 0..T, Real.exp (ρ * s) • w s) := by
  have hcont : ContinuousOn (fun s => Real.exp (ρ * s) • (X s - w s)) (Icc 0 T) :=
    (Real.continuous_exp.comp (continuous_const.mul continuous_id)).continuousOn.smul
      (hX.1.sub hw.continuousOn)
  have hsource : Continuous (fun s => (-ρ * Real.exp (ρ * s)) • w s) := by fun_prop
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hT hcont
    (fun t ht => linear_langevin_integrating_factor_derivative hV ρ hgrad hX ht)
    (hsource.intervalIntegrable 0 T)
  simp only [mul_zero, Real.exp_zero, one_smul, hX.initial hT] at hFTC
  have hfun : (fun s => (-ρ * Real.exp (ρ * s)) • w s) =
      fun s => -ρ • (Real.exp (ρ * s) • w s) := by
    funext s
    rw [smul_smul]
  rw [hfun, intervalIntegral.integral_smul] at hFTC
  have hexp : Real.exp (-ρ * T) * Real.exp (ρ * T) = 1 := by
    rw [← Real.exp_add]
    have he : -ρ * T + ρ * T = 0 := by ring
    rw [he, Real.exp_zero]
  have hs := congrArg (fun z => Real.exp (-ρ * T) • z) hFTC
  simp only [smul_sub, smul_smul, hexp, one_smul, neg_smul] at hs
  calc
    X T = (X T - w T - (Real.exp (-ρ * T) • x₀ - Real.exp (-ρ * T) • w 0)) +
        (Real.exp (-ρ * T) • x₀ + w T - Real.exp (-ρ * T) • w 0) := by abel
    _ = _ := by
      rw [← hs]
      simp only [smul_neg, smul_smul]
      module

/-- The paper's actual quadratic potential. Additive normalization constants
do not change any of the pathwise statements below. -/
@[expose] noncomputable def quadraticLangevinPotential (ρ : ℝ) (x : E) : ℝ :=
  ρ / 2 * ‖x‖ ^ 2

/-- Actual gradient of the quadratic potential. -/
theorem gradient_quadraticLangevinPotential (ρ : ℝ) (x : E) :
    gradient (quadraticLangevinPotential ρ) x = ρ • x := by
  have hd := ((hasStrictFDerivAt_norm_sq x).hasFDerivAt).const_mul (ρ / 2)
  simp only [two_smul] at hd
  apply ext_inner_right ℝ
  intro z
  rw [inner_gradient_left]
  unfold quadraticLangevinPotential
  rw [hd.fderiv, real_inner_smul_left]
  simp only [smul_apply, add_apply, smul_eq_mul]
  change ρ / 2 * (inner ℝ x z + inner ℝ x z) = ρ * inner ℝ x z
  ring

/-- The actual derivative functional of the quadratic potential. -/
theorem fderiv_quadraticLangevinPotential (ρ : ℝ) (x : E) :
    fderiv ℝ (quadraticLangevinPotential ρ) x = ρ • innerSL ℝ x := by
  ext z
  rw [← inner_gradient_left, gradient_quadraticLangevinPotential, real_inner_smul_left]
  rfl

/-- Its actual Hessian is exactly the curvature quadratic form. -/
theorem hessian_quadraticLangevinPotential (ρ : ℝ) (x z : E) :
    fderiv ℝ (fderiv ℝ (quadraticLangevinPotential ρ)) x z z = ρ * ‖z‖ ^ 2 := by
  have hfun : fderiv ℝ (quadraticLangevinPotential (E := E) ρ) =
      fun x : E => ρ • innerSL ℝ x :=
    by
      funext x
      exact fderiv_quadraticLangevinPotential ρ x
  have hd := ((innerSL ℝ : E →L[ℝ] E →L[ℝ] ℝ).hasFDerivAt (x := x)).const_smul ρ
  have hd' : HasFDerivAt (fun y : E => ρ • innerSL ℝ y) (ρ • innerSL ℝ) x := by
    convert! hd using 1
  rw [hfun, hd'.fderiv]
  simp only [smul_apply, smul_eq_mul]
  change ρ * inner ℝ z z = _
  rw [real_inner_self_eq_norm_sq]

omit [CompleteSpace E] in
/-- Smoothness of the actual quadratic potential. -/
theorem contDiff_quadraticLangevinPotential (ρ : ℝ) :
    ContDiff ℝ 2 (quadraticLangevinPotential (E := E) ρ) := by
  unfold quadraticLangevinPotential
  have hn : ContDiff ℝ 2 (fun x : E => ‖x‖ ^ 2) := contDiff_norm_sq ℝ
  exact (contDiff_const (c := ρ / 2)).mul hn

/-- The canonical selected solution has the exact linear response, derived
from its proved integral equation rather than from an assumed Gaussian law. -/
theorem quadratic_langevinSolution_response [FiniteDimensional ℝ E]
    (ρ : ℝ) (hρ : 0 ≤ ρ) {w : ℝ → E} (hw : Continuous w) (x₀ : E) {t : ℝ} (ht : 0 ≤ t) :
    langevinSolution (quadraticLangevinPotential ρ) w x₀ t =
      Real.exp (-ρ * t) • x₀ + w t - Real.exp (-ρ * t) • w 0 -
        (ρ * Real.exp (-ρ * t)) • (∫ s in 0..t, Real.exp (ρ * s) • w s) := by
  exact linear_langevin_path_response (contDiff_quadraticLangevinPotential ρ) ρ
    (gradient_quadraticLangevinPotential ρ) hw
    (langevinSolution_isLangevinPathOn (contDiff_quadraticLangevinPotential ρ) ρ hρ
      (fun x z => (hessian_quadraticLangevinPotential ρ x z).ge) hw x₀ ht) ht

/-- Almost surely the actual Brownian-driven quadratic Langevin process has
the explicit linear-response trajectory at every forward time. -/
theorem quadratic_langevinProcess_response_ae
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] [DecidableEq ι]
    {B : ℝ≥0 → Ω → EuclideanSpace ℝ ι} {P : Measure Ω}
    (hB : IsEuclideanBrownian B P) (ρ : ℝ) (hρ : 0 ≤ ρ)
    (x₀ : EuclideanSpace ℝ ι) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      langevinProcess (quadraticLangevinPotential ρ) B x₀ t ω =
        Real.exp (-ρ * (t : ℝ)) • x₀ + Real.sqrt 2 • B t ω -
          (ρ * Real.exp (-ρ * (t : ℝ))) •
            (∫ s in 0..(t : ℝ), Real.exp (ρ * s) • (Real.sqrt 2 • B s.toNNReal ω)) := by
  filter_upwards [brownianDrivingPath_continuous_ae hB,
    brownianDrivingPath_initial_zero_ae hB] with ω hcont hzero
  intro t
  have h := quadratic_langevinSolution_response ρ hρ hcont x₀ t.property
  rw [hzero, smul_zero, sub_zero] at h
  simp only [brownianDrivingPath] at h
  convert! h using 1
  congr 3
  exact congrArg (fun s : ℝ≥0 => B s ω) (Real.toNNReal_coe (r := t)).symm

section ScalarBrownianL2

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

/-- The actual continuous Brownian realization is jointly a.e. measurable,
proved through a measurable modification taking values in continuous paths. -/
theorem brownian_joint_aestronglyMeasurable (hB : IsBrownianReal B P)
    (μ : Measure ℝ) :
    AEStronglyMeasurable (fun p : ℝ × Ω => B p.1.toNNReal p.2) (μ.prod P) := by
  have : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  classical
  let g : Ω → C(ℝ, ℝ) := fun ω =>
    if h : Continuous (fun t => B t ω) then
      ⟨fun t => B t.toNNReal ω, h.comp continuous_real_toNNReal⟩ else 0
  have heval (t : ℝ) : AEMeasurable (fun ω => g ω t) P := by
    apply (hB.aemeasurable t.toNNReal).congr
    filter_upwards [hB.cont] with ω hω
    simp [g, hω]
  have hgm : Measurable (fun ω : NullMeasurableSpace Ω P => g ω) := by
    apply ContinuousMap.measurable_iff_eval.mpr
    exact fun t => (heval t).nullMeasurable.measurable'
  have hgn : AEMeasurable g P := (show NullMeasurable g P from hgm).aemeasurable
  have hmeas : Measurable (fun p : ℝ × Ω => (hgn.mk g p.2) p.1) := by
    change Measurable (Function.uncurry (fun t ω => (hgn.mk g ω) t))
    apply measurable_uncurry_of_continuous_of_measurable
    · exact fun ω => (hgn.mk g ω).continuous
    · exact fun t => (ContinuousMap.measurable_eval t).comp hgn.measurable_mk
  apply hmeas.aestronglyMeasurable.congr
  filter_upwards [Measure.quasiMeasurePreserving_snd.ae hgn.ae_eq_mk,
    Measure.quasiMeasurePreserving_snd.ae hB.cont] with p hmk hcont
  rw [← hmk]
  simp [g, hcont]

/-- Actual scalar Brownian evaluations as elements of the real L² space. -/
@[expose] noncomputable def brownianL2 (hB : IsBrownianReal B P) (t : ℝ≥0) : Ω →₂[P] ℝ :=
  (hB.isGaussianProcess.hasGaussianLaw_eval t).memLp_two.toLp (B t)

/-- Its representative agrees almost surely with the original Brownian evaluation. -/
theorem brownianL2_coeFn (hB : IsBrownianReal B P) (t : ℝ≥0) :
    (brownianL2 hB t : Ω → ℝ) =ᵐ[P] B t :=
  (hB.isGaussianProcess.hasGaussianLaw_eval t).memLp_two.coeFn_toLp

/-- Mean-square Brownian increments are exactly elapsed absolute time. -/
theorem brownianL2_norm_sub_sq (hB : IsBrownianReal B P) (s t : ℝ≥0) :
    ‖brownianL2 hB s - brownianL2 hB t‖ ^ 2 = dist s t := by
  have : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  rw [← l2_integral_sq_eq_norm_sq]
  have hrep : (fun ω => ((brownianL2 hB s - brownianL2 hB t) ω) ^ 2) =ᵐ[P]
      (fun ω => (B s ω - B t ω) ^ 2) := by
    filter_upwards [Lp.coeFn_sub (brownianL2 hB s) (brownianL2 hB t),
      brownianL2_coeFn hB s, brownianL2_coeFn hB t] with ω hsub hs ht
    simp only [hsub, Pi.sub_apply, hs, ht]
  rw [integral_congr_ae hrep]
  have hMem : MemLp (B s - B t) 2 P :=
    (hB.isGaussianProcess.hasGaussianLaw_eval s).memLp_two.sub
      (hB.isGaussianProcess.hasGaussianLaw_eval t).memLp_two
  have hvar := variance_eq_sub hMem
  simp only [Pi.pow_apply, Pi.sub_apply] at hvar
  rw [integral_sub (hB.integrable_eval s) (hB.integrable_eval t),
    hB.integral_eval, hB.integral_eval] at hvar
  simp only [sub_zero] at hvar
  rw [(hB.hasLaw_sub s t).variance_eq, variance_id_gaussianReal] at hvar
  convert! hvar.symm using 1
  simp

/-- Exact L² Brownian distance, giving its mean-square continuity. -/
theorem brownianL2_dist (hB : IsBrownianReal B P) (s t : ℝ≥0) :
    dist (brownianL2 hB s) (brownianL2 hB t) = Real.sqrt (dist s t) := by
  rw [dist_eq_norm, ← brownianL2_norm_sub_sq hB s t, Real.sqrt_sq (norm_nonneg _)]

/-- The genuine Brownian process is a continuous curve in L². -/
theorem brownianL2_continuous (hB : IsBrownianReal B P) : Continuous (brownianL2 hB) := by
  apply continuous_iff_continuous_dist.mpr
  simpa only [brownianL2_dist] using (continuous_dist : Continuous
    (fun p : ℝ≥0 × ℝ≥0 => dist p.1 p.2)).sqrt


/-- The genuine L² inner products reproduce Brownian covariance. -/
theorem brownianL2_inner (hB : IsBrownianReal B P) (s t : ℝ≥0) :
    inner ℝ (brownianL2 hB s) (brownianL2 hB t) = min (s : ℝ) (t : ℝ) := by
  rw [L2.inner_def]
  have hrep : (fun ω => inner ℝ (brownianL2 hB s ω) (brownianL2 hB t ω)) =ᵐ[P]
      (fun ω => B s ω * B t ω) := by
    filter_upwards [brownianL2_coeFn hB s, brownianL2_coeFn hB t] with ω hs ht
    simp [hs, ht, mul_comm]
  rw [integral_congr_ae hrep]
  have hcov := hB.covariance_eval s t
  simp only [covariance, hB.integral_eval, sub_zero] at hcov
  exact hcov

/-- The canonical L² Brownian representatives remain jointly Gaussian. -/
theorem brownianL2_isGaussianProcess (hB : IsBrownianReal B P) :
    IsGaussianProcess (fun t ω => brownianL2 hB t ω) P :=
  hB.isGaussianProcess.congr (fun t => (brownianL2_coeFn hB t).symm)

/-- The actual exponentially weighted Brownian integral as an L² random variable. -/
@[expose] noncomputable def integratedBrownianL2 (hB : IsBrownianReal B P)
    (ρ T : ℝ) : Ω →₂[P] ℝ :=
  ∫ s in (0 : ℝ)..T, Real.exp (ρ * s) • brownianL2 hB s.toNNReal

/-- Continuity of the L² integrand follows from mean-square Brownian continuity. -/
theorem continuous_weighted_brownianL2 (hB : IsBrownianReal B P) (ρ : ℝ) :
    Continuous (fun s : ℝ => Real.exp (ρ * s) • brownianL2 hB s.toNNReal) :=
  (Real.continuous_exp.comp (continuous_const.mul continuous_id)).smul
    ((brownianL2_continuous hB).comp continuous_real_toNNReal)

/-- Gaussianity of the actual L² integral is obtained by closed linear spans,
rather than posited as a law of the stochastic solution. -/
theorem hasGaussianLaw_integratedBrownianL2 (hB : IsBrownianReal B P)
    (ρ T : ℝ) (hT : 0 ≤ T) : HasGaussianLaw (integratedBrownianL2 hB ρ T) P := by
  have : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  let f : ℝ → Ω →₂[P] ℝ := fun s => Real.exp (ρ * s) • brownianL2 hB s.toNNReal
  have hG : IsGaussianProcess (fun s ω => f s ω) P := by
    have h := ((brownianL2_isGaussianProcess hB).comp_right Real.toNNReal).smul
      (fun s => Real.exp (ρ * s))
    apply h.congr
    intro s
    exact (Lp.coeFn_smul (Real.exp (ρ * s)) (brownianL2 hB s.toNNReal)).symm
  have hfi : Integrable f (volume.restrict (Ioc 0 T)) :=
    (continuous_weighted_brownianL2 hB ρ).integrableOn_Icc.mono_set Ioc_subset_Icc_self
  simpa only [integratedBrownianL2, intervalIntegral.integral_of_le hT, f] using
    hasGaussianLaw_integral_l2 P (volume.restrict (Ioc 0 T)) f hG hfi


/-- The Brownian endpoint and its time integral are handled jointly, using
the closed Gaussian linear span of the original Brownian process. -/
theorem hasGaussianLaw_linearBrownianL2 (hB : IsBrownianReal B P)
    (ρ T c : ℝ) (hT : 0 ≤ T) :
    HasGaussianLaw (brownianL2 hB T.toNNReal - c • integratedBrownianL2 hB ρ T) P := by
  have : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  let S := Submodule.span ℝ (Set.range (brownianL2 hB))
  have hspan : (S : Set (Ω →₂[P] ℝ)) ⊆ {X | HasGaussianLaw X P} :=
    fun X hX => hasGaussianLaw_mem_span_of_isGaussianProcess P _
      (brownianL2_isGaussianProcess hB) hX
  have hclosure : closure (S : Set (Ω →₂[P] ℝ)) ⊆ {X | HasGaussianLaw X P} :=
    closure_minimal hspan (isClosed_gaussian_l2 P)
  have hIntegral : integratedBrownianL2 hB ρ T ∈ S.topologicalClosure := by
    rw [integratedBrownianL2, intervalIntegral.integral_of_le hT]
    let μ : Measure ℝ := volume.restrict (Ioc 0 T)
    by_cases hμ : μ = 0
    · change (∫ s, _ ∂μ) ∈ _
      simp [hμ]
    have : NeZero μ := ⟨hμ⟩
    have hf : Integrable (fun s : ℝ => Real.exp (ρ * s) • brownianL2 hB s.toNNReal) μ :=
      (continuous_weighted_brownianL2 hB ρ).integrableOn_Icc.mono_set Ioc_subset_Icc_self
    have ha := S.topologicalClosure.convex.average_mem S.isClosed_topologicalClosure
      (Filter.Eventually.of_forall (fun s : ℝ => S.topologicalClosure.smul_mem _
        (S.le_topologicalClosure (Submodule.subset_span ⟨s.toNNReal, rfl⟩)))) hf
    have hb := S.topologicalClosure.smul_mem (μ.real Set.univ) ha
    rwa [measure_smul_average] at hb
  apply hclosure
  change _ ∈ S.topologicalClosure
  exact S.topologicalClosure.sub_mem
    (S.le_topologicalClosure (Submodule.subset_span ⟨T.toNNReal, rfl⟩))
    (S.topologicalClosure.smul_mem c hIntegral)

/-- Identifying an L² Bochner integral with its pointwise representative uses
Fubini and the separating set-integral functionals on L². -/
theorem coeFn_integral_l2 {T : Type*} [MeasurableSpace T] (μ : Measure T)
    [IsFiniteMeasure μ] [IsProbabilityMeasure P]
    (f : T → Ω →₂[P] ℝ) (g : T → Ω → ℝ) (hf : Integrable f μ)
    (hg : Integrable (Function.uncurry g) (μ.prod P))
    (hrep : ∀ t, (f t : Ω → ℝ) =ᵐ[P] g t) :
    ((∫ t, f t ∂μ : Ω →₂[P] ℝ) : Ω → ℝ) =ᵐ[P] (fun ω => ∫ t, g t ω ∂μ) := by
  apply Integrable.ae_eq_of_forall_setIntegral_eq _ _
    ((Lp.memLp (∫ t, f t ∂μ)).integrable (by norm_num)) hg.integral_prod_right
  intro A hA hPA
  let c : Ω →₂[P] ℝ := indicatorConstLp 2 hA hPA.ne (1 : ℝ)
  calc
    (∫ ω in A, (∫ t, f t ∂μ : Ω →₂[P] ℝ) ω ∂P) =
        inner ℝ c (∫ t, f t ∂μ) := (L2.inner_indicatorConstLp_one hA hPA.ne _).symm
    _ = ∫ t, inner ℝ c (f t) ∂μ := (integral_inner hf c).symm
    _ = ∫ t, ∫ ω in A, g t ω ∂P ∂μ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun t => by
        change inner ℝ (indicatorConstLp 2 hA hPA.ne (1 : ℝ)) (f t) = _
        rw [L2.inner_indicatorConstLp_one]
        exact integral_congr_ae (ae_restrict_of_ae (hrep t)))
    _ = ∫ ω in A, ∫ t, g t ω ∂μ ∂P := by
      exact integral_integral_swap (hg.mono_measure
        (Measure.prod_mono le_rfl Measure.restrict_le_self))


/-- The second moment is obtained from the actual Brownian marginal law. -/
theorem integral_sq_brownian (hB : IsBrownianReal B P) (t : ℝ≥0) :
    (∫ ω, (B t ω) ^ 2 ∂P) = (t : ℝ) := by
  have : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  have h := variance_eq_sub (hB.isGaussianProcess.hasGaussianLaw_eval t).memLp_two
  simp only [Pi.pow_apply, hB.integral_eval, zero_pow (by norm_num : (2 : ℕ) ≠ 0),
    sub_zero] at h
  rw [(hB.hasLaw_eval t).variance_eq, variance_id_gaussianReal] at h
  exact h.symm

/-- Brownian first absolute moments have an elementary locally bounded
majorant, avoiding any assumption on the time integral. -/
theorem integral_norm_brownian_le (hB : IsBrownianReal B P) (t : ℝ≥0) :
    (∫ ω, ‖B t ω‖ ∂P) ≤ (t : ℝ) + 1 := by
  have : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  have hs := (hB.isGaussianProcess.hasGaussianLaw_eval t).memLp_two.integrable_sq
  calc
    (∫ ω, ‖B t ω‖ ∂P) ≤ ∫ ω, ((B t ω) ^ 2 + 1) ∂P := by
      apply integral_mono (hB.integrable_eval t).norm (hs.add (integrable_const 1))
      intro ω
      change ‖B t ω‖ ≤ (B t ω) ^ 2 + 1
      rw [Real.norm_eq_abs]
      nlinarith [sq_nonneg (|B t ω| - 1), sq_abs (B t ω)]
    _ = (t : ℝ) + 1 := by rw [integral_add hs (integrable_const 1),
      integral_sq_brownian hB, integral_const]; simp

/-- Joint integrability of the weighted Brownian path on every finite time
interval follows from the Brownian law and a continuous moment majorant. -/
theorem integrable_weighted_brownian_prod (hB : IsBrownianReal B P) (ρ T : ℝ) :
    Integrable (fun p : ℝ × Ω => Real.exp (ρ * p.1) * B p.1.toNNReal p.2)
      ((volume.restrict (Ioc 0 T)).prod P) := by
  have : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  let μ : Measure ℝ := volume.restrict (Ioc 0 T)
  have hm : AEStronglyMeasurable
      (fun p : ℝ × Ω => Real.exp (ρ * p.1) * B p.1.toNNReal p.2) (μ.prod P) :=
    (by fun_prop : StronglyMeasurable (fun p : ℝ × Ω => Real.exp (ρ * p.1))).aestronglyMeasurable.mul
      (brownian_joint_aestronglyMeasurable hB μ)
  apply (integrable_prod_iff hm).mpr
  refine ⟨Filter.Eventually.of_forall (fun s => by
    convert! (hB.integrable_eval s.toNNReal).const_mul (Real.exp (ρ * s)) using 1), ?_⟩
  have hmajor : Integrable
      (fun s : ℝ => Real.exp (ρ * s) * ((s.toNNReal : ℝ) + 1)) μ := by
    have hc : Continuous (fun s : ℝ => Real.exp (ρ * s) * ((s.toNNReal : ℝ) + 1)) := by
      fun_prop
    exact hc.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  apply hmajor.mono' hm.norm.integral_prod_right'
  filter_upwards with s
  simp only [norm_mul, Real.norm_of_nonneg (Real.exp_pos _).le, integral_const_mul]
  rw [Real.norm_of_nonneg (integral_nonneg (fun ω => norm_nonneg _))]
  exact mul_le_mul_of_nonneg_left (integral_norm_brownian_le hB s.toNNReal) (Real.exp_pos _).le

/-- With explicit joint integrability, the genuine pointwise Brownian
integral agrees with the previously constructed Gaussian L² integral. -/
theorem integratedBrownianL2_coeFn (hB : IsBrownianReal B P) (ρ T : ℝ) (hT : 0 ≤ T)
    (hprod : Integrable (fun p : ℝ × Ω => Real.exp (ρ * p.1) * B p.1.toNNReal p.2)
      ((volume.restrict (Ioc 0 T)).prod P)) :
    (integratedBrownianL2 hB ρ T : Ω → ℝ) =ᵐ[P]
      (fun ω => ∫ s in 0..T, Real.exp (ρ * s) * B s.toNNReal ω) := by
  have : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  rw [integratedBrownianL2, intervalIntegral.integral_of_le hT]
  simp_rw [intervalIntegral.integral_of_le hT]
  apply coeFn_integral_l2 (volume.restrict (Ioc 0 T)) _
    (fun s ω => Real.exp (ρ * s) * B s.toNNReal ω)
    ((continuous_weighted_brownianL2 hB ρ).integrableOn_Icc.mono_set Ioc_subset_Icc_self) hprod
  intro s
  filter_upwards [Lp.coeFn_smul (Real.exp (ρ * s)) (brownianL2 hB s.toNNReal),
    brownianL2_coeFn hB s.toNNReal] with ω hsmul hrep
  simp [hsmul, hrep]

/-- The exact L² representative of the Brownian linear response. -/
theorem linearBrownianL2_coeFn (hB : IsBrownianReal B P)
    (ρ T c : ℝ) (hT : 0 ≤ T) :
    ((brownianL2 hB T.toNNReal - c • integratedBrownianL2 hB ρ T : Ω →₂[P] ℝ) : Ω → ℝ) =ᵐ[P]
      (fun ω => B T.toNNReal ω - c *
        (∫ s in 0..T, Real.exp (ρ * s) * B s.toNNReal ω)) := by
  have hprod := integrable_weighted_brownian_prod hB ρ T
  filter_upwards [Lp.coeFn_sub (brownianL2 hB T.toNNReal)
      (c • integratedBrownianL2 hB ρ T),
    Lp.coeFn_smul c (integratedBrownianL2 hB ρ T),
    brownianL2_coeFn hB T.toNNReal, integratedBrownianL2_coeFn hB ρ T hT hprod]
      with ω hsub hsmul hBrep hirep
  have hh : (brownianL2 hB T.toNNReal ω) -
      ((c • integratedBrownianL2 hB ρ T : Ω →₂[P] ℝ) ω) =
      B T.toNNReal ω - c * (∫ s in 0..T, Real.exp (ρ * s) * B s.toNNReal ω) := by
    rw [hsmul]
    simp only [Pi.smul_apply, smul_eq_mul, hBrep, hirep]
  convert! hsub.trans hh using 1


/-- Gaussianity of the actual pointwise Brownian linear response. -/
theorem hasGaussianLaw_brownian_linearResponse (hB : IsBrownianReal B P)
    (ρ T c : ℝ) (hT : 0 ≤ T) :
    HasGaussianLaw (fun ω => B T.toNNReal ω - c *
      (∫ s in 0..T, Real.exp (ρ * s) * B s.toNNReal ω)) P :=
  (hasGaussianLaw_linearBrownianL2 hB ρ T c hT).congr (linearBrownianL2_coeFn hB ρ T c hT)


/-- The explicit Brownian linear response is centered, proved by Fubini. -/
theorem integral_brownian_linearResponse (hB : IsBrownianReal B P)
    (ρ T c : ℝ) (hT : 0 ≤ T)
    (hprod : Integrable (fun p : ℝ × Ω => Real.exp (ρ * p.1) * B p.1.toNNReal p.2)
      ((volume.restrict (Ioc 0 T)).prod P)) :
    (∫ ω, B T.toNNReal ω - c *
      (∫ s in 0..T, Real.exp (ρ * s) * B s.toNNReal ω) ∂P) = 0 := by
  have : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  have hI : Integrable (fun ω => ∫ s in 0..T, Real.exp (ρ * s) * B s.toNNReal ω) P := by
    simpa only [intervalIntegral.integral_of_le hT] using hprod.integral_prod_right
  rw [integral_sub (hB.integrable_eval _) (hI.const_mul c), hB.integral_eval,
    integral_const_mul]
  have hz : (∫ ω, (∫ s in 0..T, Real.exp (ρ * s) * B s.toNNReal ω) ∂P) = 0 := by
    simp_rw [intervalIntegral.integral_of_le hT]
    rw [← integral_integral_swap hprod]
    simp_rw [integral_const_mul, hB.integral_eval, mul_zero]
    simp
  rw [hz]
  ring


/-- Gaussianity of the actual Brownian linear response, with all analytic
integrability discharged from the Brownian hypotheses. -/
theorem _root_.ProbabilityTheory.IsBrownianReal.hasGaussianLaw_linearResponse (hB : IsBrownianReal B P)
    (ρ T c : ℝ) (hT : 0 ≤ T) :
    HasGaussianLaw (fun ω => B T.toNNReal ω - c *
      (∫ s in 0..T, Real.exp (ρ * s) * B s.toNNReal ω)) P :=
  hasGaussianLaw_brownian_linearResponse hB ρ T c hT

/-- The actual Brownian response has mean zero. -/
theorem _root_.ProbabilityTheory.IsBrownianReal.integral_linearResponse (hB : IsBrownianReal B P)
    (ρ T c : ℝ) (hT : 0 ≤ T) :
    (∫ ω, B T.toNNReal ω - c *
      (∫ s in 0..T, Real.exp (ρ * s) * B s.toNNReal ω) ∂P) = 0 :=
  integral_brownian_linearResponse hB ρ T c hT (integrable_weighted_brownian_prod hB ρ T)

/-- Brownian endpoint/time-integral covariance is an actual deterministic
integral of the Brownian minimum covariance kernel. -/
theorem inner_brownianL2_integratedBrownianL2 (hB : IsBrownianReal B P)
    (ρ T : ℝ) (hT : 0 ≤ T) (s : ℝ≥0) :
    inner ℝ (brownianL2 hB s) (integratedBrownianL2 hB ρ T) =
      ∫ u in 0..T, Real.exp (ρ * u) * min (s : ℝ) (u.toNNReal : ℝ) := by
  rw [integratedBrownianL2, intervalIntegral.integral_of_le hT,
    intervalIntegral.integral_of_le hT]
  rw [← integral_inner ((continuous_weighted_brownianL2 hB ρ).integrableOn_Icc.mono_set
    Ioc_subset_Icc_self) (brownianL2 hB s)]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun u => by
    dsimp only
    rw [inner_smul_right, brownianL2_inner])

/-- The second moment of the weighted Brownian integral is the double
integral of the actual minimum covariance kernel. -/
theorem norm_sq_integratedBrownianL2 (hB : IsBrownianReal B P)
    (ρ T : ℝ) (hT : 0 ≤ T) :
    ‖integratedBrownianL2 hB ρ T‖ ^ 2 =
      ∫ s in 0..T, Real.exp (ρ * s) *
        (∫ u in 0..T, Real.exp (ρ * u) * min (s.toNNReal : ℝ) (u.toNNReal : ℝ)) := by
  rw [← real_inner_self_eq_norm_sq]
  conv_lhs => rw [integratedBrownianL2, intervalIntegral.integral_of_le hT]
  rw [real_inner_comm, ← integral_inner
    ((continuous_weighted_brownianL2 hB ρ).integrableOn_Icc.mono_set Ioc_subset_Icc_self)]
  rw [intervalIntegral.integral_of_le hT]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun s => by
    dsimp only
    rw [inner_smul_right, real_inner_comm,
      ← intervalIntegral.integral_of_le hT, ← integratedBrownianL2,
      inner_brownianL2_integratedBrownianL2 hB ρ T hT])


/-- Endpoint covariance, with time coercions removed on the actual interval. -/
theorem inner_endpoint_integratedBrownianL2 (hB : IsBrownianReal B P)
    (ρ T : ℝ) (hT : 0 ≤ T) :
    inner ℝ (brownianL2 hB T.toNNReal) (integratedBrownianL2 hB ρ T) =
      ∫ s in 0..T, Real.exp (ρ * s) * s := by
  rw [inner_brownianL2_integratedBrownianL2 hB ρ T hT]
  apply intervalIntegral.integral_congr
  intro s hs
  rw [uIcc_of_le hT] at hs
  dsimp only
  rw [Real.coe_toNNReal _ hT, Real.coe_toNNReal _ hs.1, min_eq_right hs.2]

/-- The Gaussian Brownian time integral has the double minimum-kernel
second moment used in the explicit Ornstein--Uhlenbeck covariance calculation. -/
theorem norm_sq_integratedBrownianL2_eq_double (hB : IsBrownianReal B P)
    (ρ T : ℝ) (hT : 0 ≤ T) :
    ‖integratedBrownianL2 hB ρ T‖ ^ 2 =
      ∫ s in 0..T, Real.exp (ρ * s) *
        (∫ u in 0..T, Real.exp (ρ * u) * min s u) := by
  rw [norm_sq_integratedBrownianL2 hB ρ T hT]
  apply intervalIntegral.integral_congr
  intro s hs
  rw [uIcc_of_le hT] at hs
  dsimp only
  rw [Real.coe_toNNReal _ hs.1]
  congr 1
  apply intervalIntegral.integral_congr
  intro u hu
  rw [uIcc_of_le hT] at hu
  dsimp only
  rw [Real.coe_toNNReal _ hu.1]

/-- Exact L² response variance expressed through the deterministic Brownian
covariance integrals. No transport or stochastic-law estimate is assumed. -/
theorem norm_sq_linearBrownianL2 (hB : IsBrownianReal B P)
    (ρ T c : ℝ) (hT : 0 ≤ T) :
    ‖brownianL2 hB T.toNNReal - c • integratedBrownianL2 hB ρ T‖ ^ 2 =
      T - 2 * c * (∫ s in 0..T, Real.exp (ρ * s) * s) + c ^ 2 *
        (∫ s in 0..T, Real.exp (ρ * s) *
          (∫ u in 0..T, Real.exp (ρ * u) * min s u)) := by
  rw [norm_sub_sq_real, inner_smul_right, norm_smul, mul_pow,
    Real.norm_eq_abs, sq_abs,
    norm_sq_integratedBrownianL2_eq_double hB ρ T hT,
    inner_endpoint_integratedBrownianL2 hB ρ T hT]
  have hend : ‖brownianL2 hB T.toNNReal‖ ^ 2 = T := by
    rw [← real_inner_self_eq_norm_sq, brownianL2_inner, min_self, Real.coe_toNNReal _ hT]
  rw [hend]
  ring


/-- Exact variance of the actual Brownian response, reduced to the explicit
deterministic covariance integrals. -/
theorem _root_.ProbabilityTheory.IsBrownianReal.variance_linearResponse (hB : IsBrownianReal B P)
    (ρ T c : ℝ) (hT : 0 ≤ T) :
    variance (fun ω => B T.toNNReal ω - c *
      (∫ s in 0..T, Real.exp (ρ * s) * B s.toNNReal ω)) P =
      T - 2 * c * (∫ s in 0..T, Real.exp (ρ * s) * s) + c ^ 2 *
        (∫ s in 0..T, Real.exp (ρ * s) *
          (∫ u in 0..T, Real.exp (ρ * u) * min s u)) := by
  have : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  rw [← variance_congr (linearBrownianL2_coeFn hB ρ T c hT),
    variance_eq_sub (Lp.memLp _)]
  change (∫ ω, ((brownianL2 hB T.toNNReal - c • integratedBrownianL2 hB ρ T) ω) ^ 2 ∂P) -
    (∫ ω, (brownianL2 hB T.toNNReal - c • integratedBrownianL2 hB ρ T) ω ∂P) ^ 2 = _
  rw [l2_integral_sq_eq_norm_sq, integral_congr_ae (linearBrownianL2_coeFn hB ρ T c hT),
    hB.integral_linearResponse ρ T c hT, zero_pow (by norm_num : (2 : ℕ) ≠ 0), sub_zero,
    norm_sq_linearBrownianL2 hB ρ T c hT]


/-- The genuine scalar response law, with covariance reduced to deterministic
minimum-kernel quadratures. The remaining quadrature evaluation yields Mehler. -/
theorem _root_.ProbabilityTheory.IsBrownianReal.hasLaw_linearResponse_covariance_integral
    (hB : IsBrownianReal B P) (ρ T c : ℝ) (hT : 0 ≤ T) :
    HasLaw (fun ω => B T.toNNReal ω - c *
      (∫ s in 0..T, Real.exp (ρ * s) * B s.toNNReal ω))
      (gaussianReal 0 (T - 2 * c * (∫ s in 0..T, Real.exp (ρ * s) * s) + c ^ 2 *
        (∫ s in 0..T, Real.exp (ρ * s) *
          (∫ u in 0..T, Real.exp (ρ * u) * min s u))).toNNReal) P := by
  have hG := hB.hasGaussianLaw_linearResponse ρ T c hT
  refine ⟨hG.aemeasurable, ?_⟩
  rw [hG.map_eq_gaussianReal, hB.integral_linearResponse ρ T c hT,
    hB.variance_linearResponse ρ T c hT]


/-- The actual scalar canonical Langevin solution, with arbitrary noise scale,
is the affine transform of the proved Brownian linear response. -/
theorem quadratic_langevinSolution_scalar_response_ae (hB : IsBrownianReal B P)
    (ρ σ x₀ T : ℝ) (hρ : 0 ≤ ρ) (hT : 0 ≤ T) :
    (fun ω => langevinSolution (quadraticLangevinPotential ρ)
      (fun s : ℝ => σ * B s.toNNReal ω) x₀ T) =ᵐ[P]
      (fun ω => Real.exp (-ρ * T) * x₀ + σ * (B T.toNNReal ω -
        (ρ * Real.exp (-ρ * T)) *
          (∫ s in 0..T, Real.exp (ρ * s) * B s.toNNReal ω))) := by
  filter_upwards [hB.cont, hB.eval_zero_ae_eq_zero] with ω hcont hzero
  have hw : Continuous (fun s : ℝ => σ * B s.toNNReal ω) :=
    continuous_const.mul (hcont.comp continuous_real_toNNReal)
  have h := quadratic_langevinSolution_response ρ hρ hw x₀ hT
  simp only [smul_eq_mul, Real.toNNReal_zero, hzero, mul_zero, sub_zero] at h
  have hI : (∫ s in 0..T, Real.exp (ρ * s) * (σ * B s.toNNReal ω)) =
      σ * (∫ s in 0..T, Real.exp (ρ * s) * B s.toNNReal ω) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro s hs
    ring
  rw [hI] at h
  rw [h]
  ring

/-- Actual canonical scalar Langevin marginal for a quadratic potential,
with the covariance represented by explicit deterministic quadratures. -/
theorem quadratic_langevinSolution_scalar_hasLaw_covariance_integral
    (hB : IsBrownianReal B P) (ρ σ x₀ T : ℝ) (hρ : 0 ≤ ρ) (hT : 0 ≤ T) :
    HasLaw (fun ω => langevinSolution (quadraticLangevinPotential ρ)
      (fun s : ℝ => σ * B s.toNNReal ω) x₀ T)
      (gaussianReal (Real.exp (-ρ * T) * x₀)
        (NNReal.mk (σ ^ 2) (sq_nonneg σ) *
          (T - 2 * (ρ * Real.exp (-ρ * T)) *
            (∫ s in 0..T, Real.exp (ρ * s) * s) + (ρ * Real.exp (-ρ * T)) ^ 2 *
            (∫ s in 0..T, Real.exp (ρ * s) *
              (∫ u in 0..T, Real.exp (ρ * u) * min s u))).toNNReal)) P := by
  have h := gaussianReal_const_add (gaussianReal_const_mul
    (hB.hasLaw_linearResponse_covariance_integral ρ T (ρ * Real.exp (-ρ * T)) hT) σ)
      (Real.exp (-ρ * T) * x₀)
  simp only [mul_zero, zero_add] at h
  exact h.congr (quadratic_langevinSolution_scalar_response_ae hB ρ σ x₀ T hρ hT)


/-- Exact scalar Mehler law for the actual canonical Langevin solution with
quadratic potential and arbitrary Brownian noise scale. -/
theorem quadratic_langevinSolution_scalar_hasLaw (hB : IsBrownianReal B P)
    (ρ σ x₀ T : ℝ) (hρ : 0 < ρ) (hT : 0 ≤ T) :
    HasLaw (fun ω => langevinSolution (quadraticLangevinPotential ρ)
      (fun s : ℝ => σ * B s.toNNReal ω) x₀ T)
      (gaussianReal (Real.exp (-ρ * T) * x₀)
        (σ ^ 2 * (1 - Real.exp (-2 * ρ * T)) / (2 * ρ)).toNNReal) P := by
  have h := quadratic_langevinSolution_scalar_hasLaw_covariance_integral
    hB ρ σ x₀ T hρ.le hT
  rw [brownian_linear_response_variance_integral ρ T hρ.ne' hT] at h
  have hvar : (NNReal.mk (σ ^ 2) (sq_nonneg σ) : ℝ≥0) *
      ((1 - Real.exp (-2 * ρ * T)) / (2 * ρ)).toNNReal =
      (σ ^ 2 * (1 - Real.exp (-2 * ρ * T)) / (2 * ρ)).toNNReal := by
    rw [← Real.toNNReal_of_nonneg (sq_nonneg σ), ← Real.toNNReal_mul (sq_nonneg σ)]
    congr 1
    ring
  rw [hvar] at h
  exact h

end ScalarBrownianL2

end CutoffRigidity
