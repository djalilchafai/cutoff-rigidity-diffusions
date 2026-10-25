module

public import CutoffRigidity.EntropyDissipation
public import CutoffRigidity.EuclideanBochner

/-!
# Smooth Fisher dissipation calculations

These are differential identities for actual positive smooth densities and
actual Langevin differential operators. Integration-domain and time-dominance
obligations remain explicit; no assertion about general Sobolev Fisher
information or arbitrary transition-density regularity is implicit.
-/

public section

namespace CutoffRigidity

open MeasureTheory Filter Topology

variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

/-- Coordinate chain rule for an actual exponential density. -/
theorem coordinateDerivative_exp {u : E → ℝ} (hu : Differentiable ℝ u)
    (i : Fin d) (x : E) :
    coordinateDerivative i (fun y => Real.exp (u y)) x =
      Real.exp (u x) * coordinateDerivative i u x := by
  rw [coordinateDerivative, (hu x).hasFDerivAt.exp.fderiv]
  simp only [smul_apply, smul_eq_mul, coordinateDerivative]

/-- Actual Euclidean gradient of an exponential density. -/
theorem gradient_exp_density {u : E → ℝ} {x : E} (hu : DifferentiableAt ℝ u x) :
    gradient (fun y => Real.exp (u y)) x = Real.exp (u x) • gradient u x := by
  apply ext_inner_right ℝ
  intro z
  rw [inner_gradient_left, hu.hasFDerivAt.exp.fderiv, real_inner_smul_left,
    inner_gradient_left]
  simp only [smul_apply, smul_eq_mul]

/-- The second coordinate chain rule retains the positive gradient-square term. -/
theorem coordinateDerivative_twice_exp {u : E → ℝ} (hu : ContDiff ℝ 2 u)
    (i : Fin d) (x : E) :
    coordinateDerivative i (coordinateDerivative i (fun y => Real.exp (u y))) x =
      Real.exp (u x) * ((coordinateDerivative i u x) ^ 2 +
        coordinateDerivative i (coordinateDerivative i u) x) := by
  have hd : Differentiable ℝ u := hu.differentiable (by norm_num)
  have hDu : Differentiable ℝ (coordinateDerivative i u) := by
    apply (contDiff_coordinateDerivative (n := 1) ?_ i).differentiable (by norm_num)
    convert hu using 1
    norm_num
  have hfun : coordinateDerivative i (fun y => Real.exp (u y)) =
      fun y => Real.exp (u y) * coordinateDerivative i u y :=
    funext (coordinateDerivative_exp hd i)
  rw [hfun]
  change fderiv ℝ (fun y => Real.exp (u y) * coordinateDerivative i u y) x
    (EuclideanSpace.single i 1) = _
  rw [fderiv_fun_mul (hd x).exp (hDu x)]
  simp only [add_apply, smul_apply, smul_eq_mul]
  rw [(hd x).hasFDerivAt.exp.fderiv]
  simp only [smul_apply, smul_eq_mul]
  unfold coordinateDerivative
  ring

/-- The actual exponential diffusion chain rule for the Langevin operator. -/
theorem langevin_exp_density (V : E → ℝ) {u : E → ℝ} (hu : ContDiff ℝ 2 u) (x : E) :
    langevinDifferentialOperator V (fun y => Real.exp (u y)) x =
      Real.exp (u x) * (langevinDifferentialOperator V u x + ‖gradient u x‖ ^ 2) := by
  have hscore : ‖gradient u x‖ ^ 2 = ∑ i : Fin d, (coordinateDerivative i u x) ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    simp only [coordinateDerivative, fderiv_single_eq_gradient_coordinate]
  rw [langevin_eq_coordinate_sum, langevin_eq_coordinate_sum, hscore]
  simp_rw [coordinateDerivative_twice_exp hu,
    coordinateDerivative_exp (hu.differentiable (by norm_num))]
  rw [← Finset.mul_sum, Finset.sum_add_distrib]
  simp_rw [show ∀ i : Fin d, coordinateDerivative i V x *
      (Real.exp (u x) * coordinateDerivative i u x) =
      Real.exp (u x) * (coordinateDerivative i V x * coordinateDerivative i u x) by
    intro i
    ring]
  rw [← Finset.mul_sum]
  ring

/-- The actual log-density gradient is the density score. -/
theorem gradient_log_density {f : E → ℝ} {x : E}
    (hf : DifferentiableAt ℝ f x) (hpos : 0 < f x) :
    gradient (fun y => Real.log (f y)) x = (f x)⁻¹ • gradient f x := by
  apply ext_inner_right ℝ
  intro z
  rw [inner_gradient_left, (hf.hasFDerivAt.log hpos.ne').fderiv,
    real_inner_smul_left, inner_gradient_left]
  simp only [smul_apply, smul_eq_mul]

/-- The pointwise squared-score equality defining smooth relative Fisher information. -/
theorem density_mul_score_norm_sq {f : E → ℝ} {x : E}
    (hf : DifferentiableAt ℝ f x) (hpos : 0 < f x) :
    f x * ‖gradient (fun y => Real.log (f y)) x‖ ^ 2 = ‖gradient f x‖ ^ 2 / f x := by
  rw [gradient_log_density hf hpos, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
  field_simp

/-- The actual diffusion chain rule for a positive C² density's logarithm. -/
theorem langevin_log_density (V : E → ℝ) {f : E → ℝ}
    (hf : ContDiff ℝ 2 f) (hpos : ∀ x, 0 < f x) (x : E) :
    langevinDifferentialOperator V (fun y => Real.log (f y)) x =
      langevinDifferentialOperator V f x / f x - ‖gradient f x‖ ^ 2 / (f x) ^ 2 := by
  have hu : ContDiff ℝ 2 (fun y => Real.log (f y)) := hf.log (fun x => (hpos x).ne')
  have heq : (fun y => Real.exp (Real.log (f y))) = f :=
    funext (fun y => Real.exp_log (hpos y))
  have h := langevin_exp_density V hu x
  rw [heq, Real.exp_log (hpos x), gradient_log_density
    ((hf.differentiable (by norm_num)) x) (hpos x), norm_smul, mul_pow,
    Real.norm_eq_abs, sq_abs] at h
  field_simp [(hpos x).ne'] at h ⊢
  nlinarith

/-- Actual gradient subtraction, used for the density-weighted Gibbs potential. -/
theorem gradient_sub_actual {V u : E → ℝ} {x : E}
    (hV : DifferentiableAt ℝ V x) (hu : DifferentiableAt ℝ u x) :
    gradient (fun y => V y - u y) x = gradient V x - gradient u x := by
  apply ext_inner_right ℝ
  intro z
  rw [inner_gradient_left, fderiv_fun_sub hV hu, inner_sub_left,
    inner_gradient_left, inner_gradient_left]
  rfl

/-- Reweighting by the density changes the actual Langevin drift by its score. -/
theorem langevin_sub_logDensity (V : E → ℝ) {u : E → ℝ}
    (hV : Differentiable ℝ V) (hu : Differentiable ℝ u) (x : E) :
    langevinDifferentialOperator (fun y => V y - u y) u x =
      langevinDifferentialOperator V u x + ‖gradient u x‖ ^ 2 := by
  rw [langevinDifferentialOperator, langevinDifferentialOperator,
    gradient_sub_actual (hV x) (hu x), inner_sub_left, real_inner_self_eq_norm_sq]
  ring

/-- Actual Hessian subtraction for the density-weighted potential. -/
theorem hessian_sub_actual {V u : E → ℝ} (hV : ContDiff ℝ 2 V) (hu : ContDiff ℝ 2 u)
    (x z : E) :
    fderiv ℝ (fderiv ℝ (fun y => V y - u y)) x z z =
      fderiv ℝ (fderiv ℝ V) x z z - fderiv ℝ (fderiv ℝ u) x z z := by
  have hfun : fderiv ℝ (fun y => V y - u y) = fun y => fderiv ℝ V y - fderiv ℝ u y := by
    funext y
    exact fderiv_fun_sub ((hV.differentiable (by norm_num)) y) ((hu.differentiable (by norm_num)) y)
  rw [hfun, fderiv_fun_sub
    (((hV.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)) x)
    (((hu.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)) x)]
  rfl

/-- The cubic score derivative equals twice the Hessian contracted with the score. -/
theorem inner_gradient_score_norm_sq {u : E → ℝ} (hu : ContDiff ℝ 2 u) (x : E) :
    inner ℝ (gradient u x) (gradient (fun y => ‖gradient u y‖ ^ 2) x) =
      2 * fderiv ℝ (fderiv ℝ u) x (gradient u x) (gradient u x) := by
  have hΓ : (fun y => ‖gradient u y‖ ^ 2) = fun y => inner ℝ (gradient u y) (gradient u y) := by
    funext y
    exact (real_inner_self_eq_norm_sq _).symm
  rw [inner_gradient_eq_sum_fderiv_single, hessian_gradient_coordinate_contraction hu u,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  change coordinateDerivative i u x * coordinateDerivative i (fun y => ‖gradient u y‖ ^ 2) x = _
  rw [hΓ, coordinateDerivative_gradient_inner hu hu, Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  ring

/-- The actual Gibbs measure with potential `V-u` is the original Gibbs
measure weighted by the positive density `exp u`, expressed through integration. -/
theorem integral_gibbs_sub_weight {V u : E → ℝ} (hV : Measurable V) (hu : Measurable u)
    (F : E → ℝ) :
    (∫ x, F x ∂gibbsMeasure volume (fun y => V y - u y)) =
      ∫ x, Real.exp (u x) * F x ∂gibbsMeasure volume V := by
  have hsub : Measurable (fun y => V y - u y) := by fun_prop
  rw [integral_gibbsMeasure volume hsub, integral_gibbsMeasure volume hV]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => by
    have he : Real.exp (-(V x - u x)) = Real.exp (-V x) * Real.exp (u x) := by
      rw [neg_sub]
      have ha : u x - V x = -V x + u x := by ring
      rw [ha, Real.exp_add]
    simp only [he, smul_eq_mul]
    ring

/-- The squared score is C² when its log density is C³. -/
theorem contDiff_score_norm_sq {u : E → ℝ} (hu : ContDiff ℝ 3 u) :
    ContDiff ℝ 2 (fun x => ‖gradient u x‖ ^ 2) := by
  have hfun : (fun x => ‖gradient u x‖ ^ 2) =
      fun x => ∑ i : Fin d, (coordinateDerivative i u x) ^ 2 := by
    funext x
    rw [EuclideanSpace.real_norm_sq_eq]
    simp only [coordinateDerivative, fderiv_single_eq_gradient_coordinate]
  rw [hfun]
  apply ContDiff.sum
  intro i hi
  apply ContDiff.pow
  apply contDiff_coordinateDerivative
  convert hu using 1
  norm_num

/-- Explicit smooth integration domain for density-weighted Bochner and
integration by parts. Every field is ordinary integrability of displayed
functions; no Fisher identity or differential inequality is assumed. -/
structure FisherIntegrationDomain (V u : E → ℝ) : Prop where
  bochner : BochnerIntegrationDomain (fun x => V x - u x) u
  test_Dexp : ∀ i : Fin d, Integrable
    (fun x => ‖gradient u x‖ ^ 2 *
      fderiv ℝ (fun y => Real.exp (u y)) x (EuclideanSpace.single i 1)) (gibbsMeasure volume V)
  test_DDexp : ∀ i : Fin d, Integrable
    (fun x => ‖gradient u x‖ ^ 2 * fderiv ℝ
      (fun y => fderiv ℝ (fun z => Real.exp (u z)) y (EuclideanSpace.single i 1)) x
      (EuclideanSpace.single i 1)) (gibbsMeasure volume V)
  Dtest_Dexp : ∀ i : Fin d, Integrable
    (fun x => fderiv ℝ (fun y => ‖gradient u y‖ ^ 2) x (EuclideanSpace.single i 1) *
      fderiv ℝ (fun y => Real.exp (u y)) x (EuclideanSpace.single i 1)) (gibbsMeasure volume V)
  test_drift_Dexp : ∀ i : Fin d, Integrable
    (fun x => ‖gradient u x‖ ^ 2 * fderiv ℝ V x (EuclideanSpace.single i 1) *
      fderiv ℝ (fun y => Real.exp (u y)) x (EuclideanSpace.single i 1)) (gibbsMeasure volume V)
  variation_first : Integrable
    (fun x => langevinDifferentialOperator V (fun y => Real.exp (u y)) x * ‖gradient u x‖ ^ 2)
    (gibbsMeasure volume V)
  weighted_operator : Integrable
    (fun x => Real.exp (u x) * inner ℝ (gradient u x)
      (gradient (langevinDifferentialOperator (fun y => V y - u y) u) x)) (gibbsMeasure volume V)
  weighted_hessian_norm : Integrable
    (fun x => Real.exp (u x) * ∑ i : Fin d, ∑ j : Fin d,
      (coordinateDerivative j (coordinateDerivative i u) x) ^ 2) (gibbsMeasure volume V)
  weighted_hessian_V : Integrable
    (fun x => Real.exp (u x) * fderiv ℝ (fderiv ℝ V) x (gradient u x) (gradient u x))
    (gibbsMeasure volume V)
  weighted_hessian_u : Integrable
    (fun x => Real.exp (u x) * fderiv ℝ (fderiv ℝ u) x (gradient u x) (gradient u x))
    (gibbsMeasure volume V)
  weighted_score : Integrable (fun x => Real.exp (u x) * ‖gradient u x‖ ^ 2) (gibbsMeasure volume V)

/-- The exact static Fisher-variation identity in logarithmic density
coordinates. This is the density-weighted Bochner calculation. -/
theorem integral_fisher_variation_exp_identity {V u : E → ℝ}
    (hV : ContDiff ℝ 2 V) (hu : ContDiff ℝ 3 u) (hdom : FisherIntegrationDomain V u) :
    (∫ x, langevinDifferentialOperator V (fun y => Real.exp (u y)) x * ‖gradient u x‖ ^ 2 +
      2 * (Real.exp (u x) * inner ℝ (gradient u x)
        (gradient (langevinDifferentialOperator (fun y => V y - u y) u) x))
      ∂gibbsMeasure volume V) =
      -2 * (∫ x, Real.exp (u x) * ((∑ i : Fin d, ∑ j : Fin d,
        (coordinateDerivative j (coordinateDerivative i u) x) ^ 2) +
        fderiv ℝ (fderiv ℝ V) x (gradient u x) (gradient u x)) ∂gibbsMeasure volume V) := by
  have hu2 : ContDiff ℝ 2 u := hu.of_le (by norm_num)
  have hVm := hV.continuous.measurable
  have hum := hu.continuous.measurable
  have hb := integrated_bochner_identity (hV.sub hu2) hu hdom.bochner
  rw [integral_gibbs_sub_weight hVm hum, integral_gibbs_sub_weight hVm hum,
    integral_gibbs_sub_weight hVm hum] at hb
  simp_rw [hessian_sub_actual hV hu2, mul_sub] at hb
  rw [integral_sub hdom.weighted_hessian_V hdom.weighted_hessian_u] at hb
  have he := integral_mul_langevin_eq_neg_gradient_inner
    (hV.differentiable (by norm_num))
    ((contDiff_score_norm_sq hu).differentiable (by norm_num)) hu2.exp
    hdom.test_Dexp hdom.test_DDexp hdom.Dtest_Dexp hdom.test_drift_Dexp
  have hinner (x : E) :
      inner ℝ (gradient (fun y => ‖gradient u y‖ ^ 2) x)
          (gradient (fun y => Real.exp (u y)) x) =
        2 * (Real.exp (u x) * fderiv ℝ (fderiv ℝ u) x (gradient u x) (gradient u x)) := by
    rw [gradient_exp_density ((hu.differentiable (by norm_num)) x),
      real_inner_smul_right, real_inner_comm, inner_gradient_score_norm_sq hu2]
    ring
  simp_rw [hinner, mul_comm (‖gradient u _‖ ^ 2)] at he
  rw [integral_const_mul] at he
  rw [integral_add hdom.variation_first (hdom.weighted_operator.const_mul 2), integral_const_mul]
  have hsum := integral_add hdom.weighted_hessian_norm hdom.weighted_hessian_V
  have hpoint (x : E) : Real.exp (u x) *
      ((∑ i : Fin d, ∑ j : Fin d, (coordinateDerivative j (coordinateDerivative i u) x) ^ 2) +
        fderiv ℝ (fderiv ℝ V) x (gradient u x) (gradient u x)) =
      Real.exp (u x) * (∑ i : Fin d, ∑ j : Fin d,
        (coordinateDerivative j (coordinateDerivative i u) x) ^ 2) +
      Real.exp (u x) * fderiv ℝ (fderiv ℝ V) x (gradient u x) (gradient u x) := by ring
  simp_rw [hpoint]
  rw [hsum]
  linarith

/-- Actual curvature dissipativity of the smooth Fisher first variation.
The hypotheses concern the real Hessian and explicit integration domain. -/
theorem integral_fisher_variation_exp_le {V u : E → ℝ}
    (hV : ContDiff ℝ 2 V) (hu : ContDiff ℝ 3 u) (hdom : FisherIntegrationDomain V u)
    (ρ : ℝ) (hcurv : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z) :
    (∫ x, langevinDifferentialOperator V (fun y => Real.exp (u y)) x * ‖gradient u x‖ ^ 2 +
      2 * (Real.exp (u x) * inner ℝ (gradient u x)
        (gradient (langevinDifferentialOperator (fun y => V y - u y) u) x))
      ∂gibbsMeasure volume V) ≤
      -2 * ρ * (∫ x, Real.exp (u x) * ‖gradient u x‖ ^ 2 ∂gibbsMeasure volume V) := by
  rw [integral_fisher_variation_exp_identity hV hu hdom]
  have hR : Integrable (fun x => Real.exp (u x) *
      ((∑ i : Fin d, ∑ j : Fin d, (coordinateDerivative j (coordinateDerivative i u) x) ^ 2) +
        fderiv ℝ (fderiv ℝ V) x (gradient u x) (gradient u x))) (gibbsMeasure volume V) := by
    convert hdom.weighted_hessian_norm.add hdom.weighted_hessian_V using 1
    funext x
    dsimp only [Pi.add_apply]
    ring
  have hi := integral_mono (hdom.weighted_score.const_mul ρ) hR (fun x => by
    have hs : 0 ≤ ∑ i : Fin d, ∑ j : Fin d,
        (coordinateDerivative j (coordinateDerivative i u) x) ^ 2 := by positivity
    calc
      ρ * (Real.exp (u x) * ‖gradient u x‖ ^ 2) =
          Real.exp (u x) * (ρ * ‖gradient u x‖ ^ 2) := by ring
      _ ≤ Real.exp (u x) * fderiv ℝ (fderiv ℝ V) x (gradient u x) (gradient u x) :=
        mul_le_mul_of_nonneg_left (hcurv x (gradient u x)) (Real.exp_pos _).le
      _ ≤ _ := by nlinarith [Real.exp_pos (u x)])
  rw [integral_const_mul] at hi
  linarith

/-- The actual first variation of the smooth Fisher integral in log-density coordinates. -/
@[expose] noncomputable def fisherVariationIntegrand (V u : E → ℝ) (x : E) : ℝ :=
  langevinDifferentialOperator V (fun y => Real.exp (u y)) x * ‖gradient u x‖ ^ 2 +
    2 * (Real.exp (u x) * inner ℝ (gradient u x)
      (gradient (langevinDifferentialOperator (fun y => V y - u y) u) x))

/-- Equality of the actual smooth Fisher integrand in density and log-density form. -/
theorem exp_density_fisher_integrand {u : E → ℝ} {x : E} (hu : DifferentiableAt ℝ u x) :
    ‖gradient (fun y => Real.exp (u y)) x‖ ^ 2 / Real.exp (u x) =
      Real.exp (u x) * ‖gradient u x‖ ^ 2 := by
  rw [gradient_exp_density hu, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
  field_simp

/-- Differentiating an actual positive-density forward equation yields its
log-density equation, before spatial/time derivative commutation is invoked. -/
theorem hasDerivAt_logDensity_from_density_pde
    {V : E → ℝ} (hV : Differentiable ℝ V) (u : ℝ → E → ℝ)
    {t : ℝ} (hu : ContDiff ℝ 2 (u t)) (x : E)
    (hPDE : HasDerivAt (fun s => Real.exp (u s x))
      (langevinDifferentialOperator V (fun y => Real.exp (u t y)) x) t) :
    HasDerivAt (fun s => u s x)
      (langevinDifferentialOperator (fun y => V y - u t y) (u t) x) t := by
  have h := (Real.hasDerivAt_log (Real.exp_pos (u t x)).ne').comp t hPDE
  have hcoeff : (Real.exp (u t x))⁻¹ *
      langevinDifferentialOperator V (fun y => Real.exp (u t y)) x =
      langevinDifferentialOperator (fun y => V y - u t y) (u t) x := by
    rw [langevin_exp_density V hu, langevin_sub_logDensity V hV (hu.differentiable (by norm_num))]
    field_simp
  simpa only [Function.comp_def, Real.log_exp, hcoeff] using h

/-- Dominated time differentiation of the genuine smooth Fisher integral.
The density PDE and the corresponding gradient-in-time identity are explicit;
the latter is the mixed-derivative regularity obligation for a heat flow. -/
theorem hasDerivAt_smooth_fisher_from_density_pde
    (V : E → ℝ) (u : ℝ → E → ℝ) {t₀ : ℝ} {s : Set ℝ} (hs : s ∈ 𝓝 t₀)
    (hspatial : ∀ t ∈ s, ContDiff ℝ 2 (u t))
    (hdensity : ∀ᵐ x ∂gibbsMeasure volume V, ∀ t ∈ s,
      HasDerivAt (fun r => Real.exp (u r x))
        (langevinDifferentialOperator V (fun y => Real.exp (u t y)) x) t)
    (hgradient : ∀ᵐ x ∂gibbsMeasure volume V, ∀ t ∈ s,
      HasDerivAt (fun r => gradient (u r) x)
        (gradient (langevinDifferentialOperator (fun y => V y - u t y) (u t)) x) t)
    (hmeas : ∀ᶠ t in 𝓝 t₀,
      AEStronglyMeasurable (fun x => Real.exp (u t x) * ‖gradient (u t) x‖ ^ 2)
        (gibbsMeasure volume V))
    (hint : Integrable (fun x => Real.exp (u t₀ x) * ‖gradient (u t₀) x‖ ^ 2)
      (gibbsMeasure volume V))
    (hDmeas : AEStronglyMeasurable (fisherVariationIntegrand V (u t₀)) (gibbsMeasure volume V))
    (bound : E → ℝ)
    (hbound : ∀ᵐ x ∂gibbsMeasure volume V, ∀ t ∈ s,
      ‖fisherVariationIntegrand V (u t) x‖ ≤ bound x)
    (hboundInt : Integrable bound (gibbsMeasure volume V)) :
    HasDerivAt (fun t => ∫ x,
      ‖gradient (fun y => Real.exp (u t y)) x‖ ^ 2 / Real.exp (u t x) ∂gibbsMeasure volume V)
      (∫ x, fisherVariationIntegrand V (u t₀) x ∂gibbsMeasure volume V) t₀ := by
  have hdiff : ∀ᵐ x ∂gibbsMeasure volume V, ∀ t ∈ s,
      HasDerivAt (fun r => Real.exp (u r x) * ‖gradient (u r) x‖ ^ 2)
        (fisherVariationIntegrand V (u t) x) t := by
    filter_upwards [hdensity, hgradient] with x hd hg
    intro t ht
    have h := (hd t ht).mul (hg t ht).norm_sq
    convert h using 1
    dsimp [fisherVariationIntegrand]
    ring
  have h := (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := gibbsMeasure volume V)
    (F := fun t x => Real.exp (u t x) * ‖gradient (u t) x‖ ^ 2)
    (F' := fun t x => fisherVariationIntegrand V (u t) x)
    hs hmeas hint hDmeas hbound hboundInt hdiff).2
  apply h.congr_of_eventuallyEq
  filter_upwards [hs] with t ht
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x =>
    exp_density_fisher_integrand (((hspatial t ht).differentiable (by norm_num)) x)

/-- The smooth-domain differential inequality `I' ≤ -2ρ I`, derived from
actual density PDE, dominated differentiation, and the proved weighted
Bochner identity. It makes no unconditional heat-kernel regularity claim. -/
theorem smooth_fisher_dissipation_le
    {V : E → ℝ} (hV : ContDiff ℝ 2 V) (u : ℝ → E → ℝ)
    {t₀ : ℝ} {s : Set ℝ} (hs : s ∈ 𝓝 t₀)
    (hspatial : ∀ t ∈ s, ContDiff ℝ 2 (u t)) (hu₀ : ContDiff ℝ 3 (u t₀))
    (hdom : FisherIntegrationDomain V (u t₀))
    (hdensity : ∀ᵐ x ∂gibbsMeasure volume V, ∀ t ∈ s,
      HasDerivAt (fun r => Real.exp (u r x))
        (langevinDifferentialOperator V (fun y => Real.exp (u t y)) x) t)
    (hgradient : ∀ᵐ x ∂gibbsMeasure volume V, ∀ t ∈ s,
      HasDerivAt (fun r => gradient (u r) x)
        (gradient (langevinDifferentialOperator (fun y => V y - u t y) (u t)) x) t)
    (hmeas : ∀ᶠ t in 𝓝 t₀,
      AEStronglyMeasurable (fun x => Real.exp (u t x) * ‖gradient (u t) x‖ ^ 2)
        (gibbsMeasure volume V))
    (hDmeas : AEStronglyMeasurable (fisherVariationIntegrand V (u t₀)) (gibbsMeasure volume V))
    (bound : E → ℝ)
    (hbound : ∀ᵐ x ∂gibbsMeasure volume V, ∀ t ∈ s,
      ‖fisherVariationIntegrand V (u t) x‖ ≤ bound x)
    (hboundInt : Integrable bound (gibbsMeasure volume V))
    (ρ : ℝ) (hcurv : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z) :
    ∃ I' : ℝ,
      HasDerivAt (fun t => ∫ x,
        ‖gradient (fun y => Real.exp (u t y)) x‖ ^ 2 / Real.exp (u t x) ∂gibbsMeasure volume V) I' t₀ ∧
      I' ≤ -2 * ρ * (∫ x,
        ‖gradient (fun y => Real.exp (u t₀ y)) x‖ ^ 2 / Real.exp (u t₀ x) ∂gibbsMeasure volume V) := by
  refine ⟨∫ x, fisherVariationIntegrand V (u t₀) x ∂gibbsMeasure volume V,
    hasDerivAt_smooth_fisher_from_density_pde V u hs hspatial hdensity hgradient hmeas
      hdom.weighted_score hDmeas bound hbound hboundInt, ?_⟩
  have h := integral_fisher_variation_exp_le hV hu₀ hdom ρ hcurv
  have heq : (fun x => ‖gradient (fun y => Real.exp (u t₀ y)) x‖ ^ 2 / Real.exp (u t₀ x)) =
      fun x => Real.exp (u t₀ x) * ‖gradient (u t₀) x‖ ^ 2 := by
    funext x
    exact exp_density_fisher_integrand ((hu₀.differentiable (by norm_num)) x)
  rw [heq]
  exact h

end CutoffRigidity
