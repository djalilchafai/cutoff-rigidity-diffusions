module

public import CutoffRigidity.Extra.NoBmConvex
public import CutoffRigidity.Extra.NoBmLSI
public import CutoffRigidity.ConvexInteractionCurvature
public import CutoffRigidity.GibbsMoments
public import Mathlib.Analysis.Calculus.BumpFunction.Convolution
public import Mathlib.Analysis.Calculus.BumpFunction.Normed
public import Mathlib.Analysis.Convolution

/-! # Brownian-free LSI for `C²` potentials (step 2): mollification of the potential -/

public section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ContDiff ENNReal NNReal Convolution

namespace CutoffRigidity.NoBm

variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

/-- The `n`-th mollifier bump, of outer radius `1/(n+1)`. -/
@[expose] noncomputable def bump (n : ℕ) : ContDiffBump (0 : E) :=
  ⟨1 / (2 * ((n : ℝ) + 1)), 1 / ((n : ℝ) + 1), by positivity,
    by
      have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
      rw [show 1 / (2 * ((n : ℝ) + 1)) = (1 / ((n : ℝ) + 1)) / 2 by field_simp]
      linarith⟩

/-- The `n`-th normalized mollifier. -/
@[expose] noncomputable def mol (n : ℕ) : E → ℝ := (bump (d := d) n).normed volume

theorem mol_nonneg (n : ℕ) (x : E) : 0 ≤ mol n x := (bump n).nonneg_normed x

theorem mol_integral (n : ℕ) : ∫ x : E, mol (d := d) n x = 1 := (bump n).integral_normed

theorem mol_contDiff (n : ℕ) : ContDiff ℝ ∞ (mol (d := d) n) := (bump n).contDiff_normed

theorem mol_cs (n : ℕ) : HasCompactSupport (mol (d := d) n) := (bump n).hasCompactSupport_normed

theorem mol_support (n : ℕ) {t : E} (ht : mol n t ≠ 0) : ‖t‖ ≤ 1 := by
  have h1 : t ∈ Function.support (mol (d := d) n) := ht
  rw [mol, (bump n).support_normed_eq] at h1
  have h2 : ‖t‖ < 1 / ((n : ℝ) + 1) := by simpa [bump] using h1
  have h3 : 1 / ((n : ℝ) + 1) ≤ 1 := by
    rw [div_le_one (by positivity)]; linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  linarith

theorem mol_integrable (n : ℕ) : Integrable (mol (d := d) n) volume := (bump n).integrable_normed

/-- Mollification `ψ_n ⋆ g` written as an integral. -/
@[expose] noncomputable def molc (n : ℕ) (g : E → ℝ) (x : E) : ℝ := ∫ t, mol n t * g (x - t)

theorem molc_eq (n : ℕ) (g : E → ℝ) : molc n g = (mol n ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) := by
  funext x
  simp [molc, convolution_def]

theorem molc_contDiff (n : ℕ) {g : E → ℝ} (hg : Continuous g) : ContDiff ℝ ∞ (molc n g) := by
  rw [molc_eq]
  exact (mol_cs n).contDiff_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ) (mol_contDiff n)
    (hg.locallyIntegrable)

theorem molc_tendsto {g : E → ℝ} (hg : Continuous g) (x : E) :
    Tendsto (fun n => molc n g x) atTop (𝓝 (g x)) := by
  have := ContDiffBump.convolution_tendsto_right_of_continuous (μ := (volume : Measure E))
    (φ := fun n : ℕ => bump (d := d) n) (l := atTop) (g := g) ?_ hg x
  · simpa [molc_eq, mol] using this
  · simp only [bump]
    exact tendsto_const_nhds.div_atTop (tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop)

theorem molc_integrand_integrable (n : ℕ) {g : E → ℝ} (hg : Continuous g) (x : E) :
    Integrable (fun t => mol n t * g (x - t)) volume := by
  have hc : Continuous fun t => mol n t * g (x - t) :=
    (mol_contDiff n).continuous.mul (hg.comp (continuous_const.sub continuous_id))
  refine hc.integrable_of_hasCompactSupport ?_
  exact (mol_cs n).mul_right

theorem molc_convex (n : ℕ) {g : E → ℝ} (hg : Continuous g) (hc : ConvexOn ℝ univ g) :
    ConvexOn ℝ univ (molc n g) := by
  refine ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩
  have hx := molc_integrand_integrable n hg x
  have hy := molc_integrand_integrable n hg y
  have hpt : ∀ t, mol n t * g ((a • x + b • y) - t) ≤
      a * (mol n t * g (x - t)) + b * (mol n t * g (y - t)) := by
    intro t
    have e : (a • x + b • y) - t = a • (x - t) + b • (y - t) := by
      rw [smul_sub, smul_sub]
      have : t = a • t + b • t := by rw [← add_smul, hab, one_smul]
      conv_lhs => rw [this]
      abel
    rw [e]
    have := hc.2 (mem_univ (x - t)) (mem_univ (y - t)) ha hb hab
    simp only [smul_eq_mul] at this
    nlinarith [mol_nonneg n t]
  have := integral_mono (molc_integrand_integrable n hg (a • x + b • y))
    ((hx.const_mul a).add (hy.const_mul b)) (g := fun t => a * (mol n t * g (x - t)) + b * (mol n t * g (y - t))) hpt
  rw [integral_add (hx.const_mul a) (hy.const_mul b), integral_const_mul, integral_const_mul] at this
  simpa [molc, smul_eq_mul] using this

theorem molc_lower (n : ℕ) {g : E → ℝ} (hg : Continuous g) {L : E → ℝ} (hL : ∀ y, L y ≤ g y)
    (x : E) {c : ℝ} (hcb : ∀ t, ‖t‖ ≤ 1 → L (x - t) ≥ c) : c ≤ molc n g x := by
  have h1 := molc_integrand_integrable n hg x
  have hpt : ∀ t, mol n t * c ≤ mol n t * g (x - t) := by
    intro t
    by_cases ht : mol n t = 0
    · simp [ht]
    · have := hcb t (mol_support n ht)
      exact mul_le_mul_of_nonneg_left (this.trans (hL _)) (mol_nonneg n t)
  have := integral_mono ((mol_integrable n).mul_const c) h1 hpt
  rw [integral_mul_const, mol_integral] at this
  simpa [molc] using this


/-! ### The mollified potentials -/

section Potential

variable {V : EuclideanSpace ℝ (Fin d) → ℝ} (hV : ContDiff ℝ 2 V) {ρ : ℝ} (hρ : 0 < ρ)
  (hH : ∀ x z : EuclideanSpace ℝ (Fin d), ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)

/-- The convex part `U = V - ρ‖x‖²/2` of the potential. -/
@[expose] noncomputable def convPart (ρ : ℝ) (V : E → ℝ) (x : E) : ℝ := V x - ρ / 2 * ‖x‖ ^ 2

include hV in
theorem convPart_contDiff : ContDiff ℝ 2 (convPart ρ V) :=
  hV.sub (contDiff_const.mul (contDiff_norm_sq ℝ))

include hV hH in
theorem convPart_convex : ConvexOn ℝ univ (convPart ρ V) := by
  have hU := convPart_contDiff (ρ := ρ) hV
  refine convexOn_univ_of_hessian_nonneg hU (fun x z => ?_)
  let Q : E → ℝ := quadraticLangevinPotential ρ
  have hQ : ContDiff ℝ 2 Q := contDiff_quadraticLangevinPotential ρ
  have hVeq : V = fun y => Q y + convPart ρ V y := by
    funext y; simp [Q, quadraticLangevinPotential, convPart]
  have hderiv : fderiv ℝ V = fun y => fderiv ℝ Q y + fderiv ℝ (convPart ρ V) y := by
    conv_lhs => rw [hVeq]
    funext y
    exact fderiv_add (hQ.differentiable (by norm_num) y) (hU.differentiable (by norm_num) y)
  have h1 := hH x z
  rw [hderiv, fderiv_fun_add
    (((hQ.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)) x)
    (((hU.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)) x)] at h1
  simp only [ContinuousLinearMap.add_apply] at h1
  have hquad := hessian_quadraticLangevinPotential ρ x z
  change fderiv ℝ (fderiv ℝ Q) x z z = _ at hquad
  rw [hquad] at h1
  linarith

/-- The mollified potentials. -/
@[expose] noncomputable def Vn (ρ : ℝ) (V : E → ℝ) (n : ℕ) (x : E) : ℝ := ρ / 2 * ‖x‖ ^ 2 + molc n (convPart ρ V) x

include hV in
theorem Vn_contDiff (n : ℕ) : ContDiff ℝ ∞ (Vn ρ V n) :=
  (contDiff_const.mul (contDiff_norm_sq ℝ)).add (molc_contDiff n (convPart_contDiff (ρ := ρ) hV).continuous)

include hV hH in
theorem Vn_hessian (n : ℕ) (x z : E) :
    ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ (Vn ρ V n)) x z z := by
  have hc := (convPart_contDiff (ρ := ρ) hV).continuous
  exact hessian_quadratic_add_convex_lower
    ((molc_contDiff n hc).of_le (by norm_cast)) (molc_convex n hc (convPart_convex hV hH)) ρ x z

include hV hρ hH in
theorem Vn_lower (n : ℕ) (x : E) :
    ρ / 8 * ‖x‖ ^ 2 - (3 * ρ / 4 + (‖gradient V 0‖ ^ 2 / ρ - V 0)) ≤ Vn ρ V n x := by
  have hc := (convPart_contDiff (ρ := ρ) hV).continuous
  set K := ‖gradient V 0‖ ^ 2 / ρ - V 0 with hK
  have hlow := potential_gaussian_lower_bound hV ρ hρ hH
  have := molc_lower n hc (L := fun y => -(ρ / 4) * ‖y‖ ^ 2 - K)
    (fun y => by have := hlow y; simp only [convPart]; nlinarith) x
    (c := -(3 * ρ / 8) * ‖x‖ ^ 2 - 3 * ρ / 4 - K) (fun t ht => by
      have h1 : ‖x - t‖ ≤ ‖x‖ + 1 := (norm_sub_le _ _).trans (by linarith)
      have h2 : ‖x - t‖ ^ 2 ≤ 3 / 2 * ‖x‖ ^ 2 + 3 := by
        have : ‖x - t‖ ^ 2 ≤ (‖x‖ + 1) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
        nlinarith [sq_nonneg (‖x‖ - 2)]
      nlinarith)
  simp only [Vn]
  nlinarith

include hV hρ hH in
theorem Vn_exp_le (n : ℕ) (x : E) :
    Real.exp (-Vn ρ V n x) ≤
      Real.exp (3 * ρ / 4 + (‖gradient V 0‖ ^ 2 / ρ - V 0)) * Real.exp (-(ρ / 8) * ‖x‖ ^ 2) := by
  rw [← Real.exp_add, Real.exp_le_exp]
  have := Vn_lower hV hρ hH n x
  linarith

include hV in
theorem Vn_tendsto (x : E) : Tendsto (fun n => Vn ρ V n x) atTop (𝓝 (V x)) := by
  have := (molc_tendsto (convPart_contDiff (ρ := ρ) hV).continuous x).const_add (ρ / 2 * ‖x‖ ^ 2)
  simpa [Vn, convPart] using this


/-! ### Partition functions and convergence of the Gibbs integrals -/

/-- Partition function of the mollified potential. -/
@[expose] noncomputable def Zn (ρ : ℝ) (V : E → ℝ) (n : ℕ) : ℝ := ∫ x, Real.exp (-Vn ρ V n x)

/-- Normalised mollified potential. -/
@[expose] noncomputable def Wn (ρ : ℝ) (V : E → ℝ) (n : ℕ) (x : E) : ℝ := Vn ρ V n x + Real.log (Zn ρ V n)

include hV hρ hH in
theorem integrable_exp_Vn (n : ℕ) : Integrable (fun x => Real.exp (-Vn ρ V n x)) volume := by
  have hg : Integrable (fun x : E => Real.exp (3 * ρ / 4 + (‖gradient V 0‖ ^ 2 / ρ - V 0)) *
      Real.exp (-(ρ / 8) * ‖x‖ ^ 2)) volume :=
    (integrable_exp_neg_mul_norm_sq (ρ / 8) (by positivity)).const_mul _
  refine hg.mono' ?_ (Eventually.of_forall fun x => ?_)
  · exact (Real.continuous_exp.comp (Vn_contDiff hV n).continuous.neg).aestronglyMeasurable
  · rw [Real.norm_of_nonneg (Real.exp_nonneg _)]
    exact Vn_exp_le hV hρ hH n x

include hV hρ hH in
theorem integrable_exp_V : Integrable (fun x => Real.exp (-V x)) volume := by
  have hg : Integrable (fun x : E => Real.exp (‖gradient V 0‖ ^ 2 / ρ - V 0) *
      Real.exp (-(ρ / 4) * ‖x‖ ^ 2)) volume :=
    (integrable_exp_neg_mul_norm_sq (ρ / 4) (by positivity)).const_mul _
  refine hg.mono' ?_ (Eventually.of_forall fun x => ?_)
  · exact (Real.continuous_exp.comp hV.continuous.neg).aestronglyMeasurable
  · rw [Real.norm_of_nonneg (Real.exp_nonneg _)]
    exact gibbs_density_gaussian_domination hV ρ hρ hH x

include hV in
theorem integral_exp_V_eq_one (hp : IsProbabilityMeasure (CutCur.gibbs V)) :
    ∫ x, Real.exp (-V x) = 1 := by
  have h := integral_gibbsMeasure volume (V := V) hV.continuous.measurable (fun _ => (1 : ℝ))
  change ∫ x, (1 : ℝ) ∂CutCur.gibbs V = _ at h
  simpa using h.symm

include hV hρ hH in
theorem tendsto_integral_exp_mul {G : E → ℝ} (hG : Continuous G) {B : ℝ} (hB : ∀ x, |G x| ≤ B) :
    Tendsto (fun n => ∫ x, Real.exp (-Vn ρ V n x) * G x) atTop
      (𝓝 (∫ x, Real.exp (-V x) * G x)) := by
  have hbound : Integrable (fun x : E => (B * Real.exp (3 * ρ / 4 + (‖gradient V 0‖ ^ 2 / ρ - V 0))) *
      Real.exp (-(ρ / 8) * ‖x‖ ^ 2)) volume :=
    (integrable_exp_neg_mul_norm_sq (ρ / 8) (by positivity)).const_mul _
  refine tendsto_integral_of_dominated_convergence _ (fun n => ?_) hbound (fun n => ?_) ?_
  · exact ((Real.continuous_exp.comp (Vn_contDiff hV n).continuous.neg).mul hG).aestronglyMeasurable
  · refine Eventually.of_forall fun x => ?_
    rw [norm_mul, Real.norm_of_nonneg (Real.exp_nonneg _), Real.norm_eq_abs]
    calc Real.exp (-Vn ρ V n x) * |G x|
        ≤ (Real.exp (3 * ρ / 4 + (‖gradient V 0‖ ^ 2 / ρ - V 0)) * Real.exp (-(ρ / 8) * ‖x‖ ^ 2)) * B :=
          mul_le_mul (Vn_exp_le hV hρ hH n x) (hB x) (abs_nonneg _) (by positivity)
      _ = _ := by ring
  · refine Eventually.of_forall fun x => ?_
    exact ((Real.continuous_exp.tendsto _).comp (Vn_tendsto hV x).neg).mul_const _

include hV hρ hH in
theorem tendsto_Zn (hp : IsProbabilityMeasure (CutCur.gibbs V)) :
    Tendsto (Zn ρ V) atTop (𝓝 1) := by
  have h := tendsto_integral_exp_mul hV hρ hH (G := fun _ => (1 : ℝ)) continuous_const (B := 1)
    (fun x => by simp)
  simp only [mul_one] at h
  rw [integral_exp_V_eq_one hV hp] at h
  exact h

include hV hρ hH in
theorem gibbs_Wn_integral (n : ℕ) (hZ : 0 < Zn ρ V n) (G : E → ℝ) :
    ∫ x, G x ∂CutCur.gibbs (Wn ρ V n) = (Zn ρ V n)⁻¹ * ∫ x, Real.exp (-Vn ρ V n x) * G x := by
  have hmeas : Measurable (Wn ρ V n) :=
    (((Vn_contDiff hV n).continuous).add continuous_const).measurable
  have h := integral_gibbsMeasure volume (V := Wn ρ V n) hmeas G
  change ∫ x, G x ∂gibbsMeasure volume (Wn ρ V n) = _ at h
  rw [show CutCur.gibbs (Wn ρ V n) = gibbsMeasure volume (Wn ρ V n) from rfl, h, ← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only [Wn, smul_eq_mul, neg_add, Real.exp_add, Real.exp_neg (Real.log _), Real.exp_log hZ]
  ring

include hV hρ hH in
theorem tendsto_gibbs_Wn (hp : IsProbabilityMeasure (CutCur.gibbs V)) {G : E → ℝ}
    (hG : Continuous G) {B : ℝ} (hB : ∀ x, |G x| ≤ B) :
    Tendsto (fun n => ∫ x, G x ∂CutCur.gibbs (Wn ρ V n)) atTop (𝓝 (∫ x, G x ∂CutCur.gibbs V)) := by
  have h1 := tendsto_Zn hV hρ hH hp
  have h2 := tendsto_integral_exp_mul hV hρ hH hG hB
  have h3 := (h1.inv₀ one_ne_zero).mul h2
  have e : ∫ x, G x ∂CutCur.gibbs V = (1 : ℝ)⁻¹ * ∫ x, Real.exp (-V x) * G x := by
    have := integral_gibbsMeasure volume (V := V) hV.continuous.measurable G
    change ∫ x, G x ∂gibbsMeasure volume V = _ at this
    rw [show CutCur.gibbs V = gibbsMeasure volume V from rfl, this]
    simp
  rw [e]
  refine h3.congr' ?_
  filter_upwards [h1.eventually (lt_mem_nhds (show (0 : ℝ) < 1 by norm_num))] with n hn
  rw [gibbs_Wn_integral hV hρ hH n hn]

end Potential


theorem norm_gradient_eq' (f : E → ℝ) (x : E) : ‖gradient f x‖ = ‖fderiv ℝ f x‖ := by
  unfold gradient
  exact LinearIsometryEquiv.norm_map _ _

/-- Continuous functions with compact support are bounded. -/
theorem exists_abs_bound {G : E → ℝ} (hG : Continuous G) (hc : HasCompactSupport G) :
    ∃ B : ℝ, ∀ x, |G x| ≤ B := by
  obtain ⟨M, hM⟩ := hG.bounded_above_of_compact_support hc
  exact ⟨M, fun x => by simpa [Real.norm_eq_abs] using hM x⟩

theorem cont_sqlog {f : E → ℝ} (hf : Continuous f) :
    Continuous fun x => f x ^ 2 * Real.log (f x ^ 2) :=
  Real.continuous_mul_log.comp (hf.pow 2)

theorem cs_sqlog {f : E → ℝ} (hfc : HasCompactSupport f) :
    HasCompactSupport fun x => f x ^ 2 * Real.log (f x ^ 2) :=
  hfc.comp_left (g := fun t : ℝ => t ^ 2 * Real.log (t ^ 2)) (by simp)

theorem cs_sq {f : E → ℝ} (hfc : HasCompactSupport f) : HasCompactSupport fun x => f x ^ 2 :=
  hfc.comp_left (g := fun t : ℝ => t ^ 2) (by simp)

theorem cont_gradsq {f : E → ℝ} (hf : ContDiff ℝ 1 f) : Continuous fun x => ‖gradient f x‖ ^ 2 := by
  simp_rw [norm_gradient_eq']
  exact (hf.continuous_fderiv one_ne_zero).norm.pow 2

theorem cs_gradsq {f : E → ℝ} (hfc : HasCompactSupport f) :
    HasCompactSupport fun x => ‖gradient f x‖ ^ 2 := by
  simp_rw [norm_gradient_eq']
  exact (hfc.fderiv ℝ).comp_left (g := fun A : E →L[ℝ] ℝ => ‖A‖ ^ 2) (by simp)

section Main

variable {V : EuclideanSpace ℝ (Fin d) → ℝ} (hV : ContDiff ℝ 2 V) {ρ : ℝ} (hρ : 0 < ρ)
  (hH : ∀ x z : EuclideanSpace ℝ (Fin d), ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)

include hV hρ hH in
theorem lsi_C2_smooth_compact (hp : IsProbabilityMeasure (CutCur.gibbs V))
    {f : E → ℝ} (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f) :
    CutCur.entropyOf (CutCur.gibbs V) (fun x => f x ^ 2) ≤
      2 / ρ * ∫ x, ‖gradient f x‖ ^ 2 ∂CutCur.gibbs V := by
  have hf2 : Continuous fun x => f x ^ 2 := hf.continuous.pow 2
  obtain ⟨B1, hB1⟩ := exists_abs_bound (cont_sqlog hf.continuous) (cs_sqlog hfc)
  obtain ⟨B2, hB2⟩ := exists_abs_bound hf2 (cs_sq hfc)
  have hf1 : ContDiff ℝ 1 f := hf.of_le (by norm_cast)
  obtain ⟨B3, hB3⟩ := exists_abs_bound (cont_gradsq hf1) (cs_gradsq hfc)
  have t1 := tendsto_gibbs_Wn hV hρ hH hp (cont_sqlog hf.continuous) hB1
  have t2 := tendsto_gibbs_Wn hV hρ hH hp hf2 hB2
  have t3 := tendsto_gibbs_Wn hV hρ hH hp (cont_gradsq hf1) hB3
  have hlhs : Tendsto (fun n => CutCur.entropyOf (CutCur.gibbs (Wn ρ V n)) (fun x => f x ^ 2)) atTop
      (𝓝 (CutCur.entropyOf (CutCur.gibbs V) (fun x => f x ^ 2))) := by
    unfold CutCur.entropyOf
    have t4 := (Real.continuous_mul_log.tendsto _).comp t2
    refine t1.sub ?_
    simpa [Function.comp_def, mul_comm] using t4
  have hev : ∀ᶠ n in atTop, CutCur.entropyOf (CutCur.gibbs (Wn ρ V n)) (fun x => f x ^ 2) ≤
      2 / ρ * ∫ x, ‖gradient f x‖ ^ 2 ∂CutCur.gibbs (Wn ρ V n) := by
    filter_upwards [(tendsto_Zn hV hρ hH hp).eventually (lt_mem_nhds (show (0 : ℝ) < 1 by norm_num))]
      with n hn
    have hprob : IsProbabilityMeasure (CutCur.gibbs (Wn ρ V n)) :=
      gibbsMeasure_normalize_potential volume (Vn ρ V n) (integrable_exp_Vn hV hρ hH n) hn
    have hWd : ContDiff ℝ ∞ (Wn ρ V n) := (Vn_contDiff hV n).add contDiff_const
    refine lsi_smooth_compact hWd hprob hρ (fun x z => ?_) hf hfc
    have : fderiv ℝ (Wn ρ V n) = fderiv ℝ (Vn ρ V n) := by
      funext y; exact fderiv_add_const (f := Vn ρ V n) (Real.log (Zn ρ V n))
    rw [this]
    exact Vn_hessian hV hH n x z
  exact le_of_tendsto_of_tendsto hlhs (t3.const_mul _) hev

end Main

end CutoffRigidity.NoBm
