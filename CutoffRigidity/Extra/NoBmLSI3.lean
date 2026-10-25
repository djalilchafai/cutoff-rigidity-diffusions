module

public import CutoffRigidity.Extra.NoBmLSI2

/-! # Brownian-free LSI for `C²` potentials (step 4): bounded `C²` tests with bounded gradient -/

public section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ContDiff ENNReal NNReal

namespace CutoffRigidity.NoBm

variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

/-- Passage to the limit in the LSI along a bounded sequence converging in `C¹`-pointwise sense. -/
theorem lsi_of_approx {μ : Measure E} [IsProbabilityMeasure μ] {c : ℝ} {f : E → ℝ}
    (fn : ℕ → E → ℝ) (hfn : ∀ n, ContDiff ℝ 1 (fn n))
    {M G : ℝ} (hM : ∀ n x, |fn n x| ≤ M) (hG : ∀ n x, ‖fderiv ℝ (fn n) x‖ ≤ G)
    (hx : ∀ x, Tendsto (fun n => fn n x) atTop (𝓝 (f x)))
    (hgx : ∀ x, Tendsto (fun n => ‖fderiv ℝ (fn n) x‖) atTop (𝓝 ‖fderiv ℝ f x‖))
    (hL : ∀ n, CutCur.entropyOf μ (fun x => fn n x ^ 2) ≤ c * ∫ x, ‖gradient (fn n) x‖ ^ 2 ∂μ) :
    CutCur.entropyOf μ (fun x => f x ^ 2) ≤ c * ∫ x, ‖gradient f x‖ ^ 2 ∂μ := by
  obtain ⟨B1, hB1⟩ := (isCompact_Icc (a := -M) (b := M)).exists_bound_of_continuousOn
    (Real.continuous_mul_log.comp (continuous_pow 2)).continuousOn
  have hfc : ∀ n, Continuous (fn n) := fun n => (hfn n).continuous
  have t1 : Tendsto (fun n => ∫ x, fn n x ^ 2 * Real.log (fn n x ^ 2) ∂μ) atTop
      (𝓝 (∫ x, f x ^ 2 * Real.log (f x ^ 2) ∂μ)) := by
    refine tendsto_integral_of_dominated_convergence (fun _ => B1) (fun n => ?_) (integrable_const _)
      (fun n => Eventually.of_forall fun x => ?_) (Eventually.of_forall fun x => ?_)
    · exact (cont_sqlog (hfc n)).aestronglyMeasurable
    · exact hB1 _ (abs_le.mp (hM n x))
    · exact (Real.continuous_mul_log.comp (continuous_pow 2)).continuousAt.tendsto.comp (hx x)
  have t2 : Tendsto (fun n => ∫ x, fn n x ^ 2 ∂μ) atTop (𝓝 (∫ x, f x ^ 2 ∂μ)) := by
    refine tendsto_integral_of_dominated_convergence (fun _ => M ^ 2) (fun n => ?_) (integrable_const _)
      (fun n => Eventually.of_forall fun x => ?_) (Eventually.of_forall fun x => ?_)
    · exact ((hfc n).pow 2).aestronglyMeasurable
    · have := hM n x
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact (sq_le_sq' (abs_le.mp this).1 (abs_le.mp this).2)
    · exact ((continuous_pow 2).tendsto _).comp (hx x)
  have t3 : Tendsto (fun n => ∫ x, ‖gradient (fn n) x‖ ^ 2 ∂μ) atTop
      (𝓝 (∫ x, ‖gradient f x‖ ^ 2 ∂μ)) := by
    refine tendsto_integral_of_dominated_convergence (fun _ => G ^ 2) (fun n => ?_) (integrable_const _)
      (fun n => Eventually.of_forall fun x => ?_) (Eventually.of_forall fun x => ?_)
    · exact (cont_gradsq (hfn n)).aestronglyMeasurable
    · rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), norm_gradient_eq']
      exact pow_le_pow_left₀ (norm_nonneg _) (hG n x) 2
    · simp_rw [norm_gradient_eq']
      exact (hgx x).pow 2
  have hlhs : Tendsto (fun n => CutCur.entropyOf μ (fun x => fn n x ^ 2)) atTop
      (𝓝 (CutCur.entropyOf μ (fun x => f x ^ 2))) := by
    unfold CutCur.entropyOf
    have t4 := (Real.continuous_mul_log.tendsto _).comp t2
    refine t1.sub ?_
    simpa [Function.comp_def, mul_comm] using t4
  exact le_of_tendsto_of_tendsto' hlhs (t3.const_mul _) hL


/-- The fixed cutoff profile: equal to `1` on the unit ball, supported in the ball of radius `2`. -/
noncomputable def cutProfile : ContDiffBump (0 : E) := ⟨1, 2, one_pos, one_lt_two⟩

/-- The rescaled cutoff `χ_R(x) = χ(x/R)`. -/
noncomputable def cutoff (R : ℝ) (x : E) : ℝ := cutProfile (R⁻¹ • x)

theorem cutoff_contDiff (R : ℝ) : ContDiff ℝ ∞ (cutoff (d := d) R) :=
  (cutProfile (d := d)).contDiff.comp (contDiff_id.const_smul R⁻¹ : ContDiff ℝ ∞ fun x : E => R⁻¹ • x)

theorem cutoff_nonneg (R : ℝ) (x : E) : 0 ≤ cutoff R x := (cutProfile (d := d)).nonneg

theorem cutoff_le_one (R : ℝ) (x : E) : cutoff R x ≤ 1 := (cutProfile (d := d)).le_one

theorem cutoff_eq_one {R : ℝ} (hR : 0 < R) {x : E} (hx : ‖x‖ ≤ R) : cutoff R x = 1 := by
  apply (cutProfile (d := d)).one_of_mem_closedBall
  rw [mem_closedBall_zero_iff, norm_smul, norm_inv, Real.norm_of_nonneg hR.le]
  show R⁻¹ * ‖x‖ ≤ 1
  rw [inv_mul_le_iff₀ hR]; simpa using hx

theorem cutoff_eq_zero {R : ℝ} (hR : 0 < R) {x : E} (hx : 2 * R ≤ ‖x‖) : cutoff R x = 0 := by
  apply (cutProfile (d := d)).zero_of_le_dist
  rw [dist_zero_right, norm_smul, norm_inv, Real.norm_of_nonneg hR.le]
  show 2 ≤ R⁻¹ * ‖x‖
  rw [le_inv_mul_iff₀ hR]; simpa [mul_comm] using hx

theorem exists_cutoff_grad_bound : ∃ L : ℝ, 0 ≤ L ∧ ∀ y : E, ‖fderiv ℝ (cutProfile (d := d)) y‖ ≤ L := by
  obtain ⟨L, hL⟩ := exists_abs_bound (G := fun y => ‖fderiv ℝ (cutProfile (d := d)) y‖)
    (((cutProfile (d := d)).contDiff (n := 1)).continuous_fderiv one_ne_zero).norm
    ((cutProfile (d := d)).hasCompactSupport.fderiv ℝ).norm
  exact ⟨max L 0, le_max_right _ _, fun y => by have h := hL y; rw [abs_norm] at h; exact h.trans (le_max_left _ _)⟩

theorem norm_fderiv_cutoff_le {L : ℝ} (hL : ∀ y : E, ‖fderiv ℝ (cutProfile (d := d)) y‖ ≤ L)
    {R : ℝ} (hR : 0 < R) (x : E) : ‖fderiv ℝ (cutoff R) x‖ ≤ L * R⁻¹ := by
  have h1 : HasFDerivAt (cutoff (d := d) R)
      ((fderiv ℝ (cutProfile (d := d)) (R⁻¹ • x)).comp (R⁻¹ • ContinuousLinearMap.id ℝ E)) x := by
    have h2 : HasFDerivAt (fun y : E => R⁻¹ • y) (R⁻¹ • ContinuousLinearMap.id ℝ E) x :=
      (hasFDerivAt_id x).const_smul R⁻¹
    exact (((cutProfile (d := d)).contDiff (n := 1)).differentiable one_ne_zero _).hasFDerivAt.comp x h2
  rw [h1.fderiv]
  refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
  have : ‖R⁻¹ • ContinuousLinearMap.id ℝ E‖ ≤ R⁻¹ := by
    refine (norm_smul_le R⁻¹ (ContinuousLinearMap.id ℝ E)).trans ?_
    rw [Real.norm_of_nonneg (inv_nonneg.mpr hR.le)]
    exact mul_le_of_le_one_right (inv_nonneg.mpr hR.le) (ContinuousLinearMap.norm_id_le)
  exact mul_le_mul (hL _) this (norm_nonneg _) ((norm_nonneg _).trans (hL 0))


section Main

variable {V : EuclideanSpace ℝ (Fin d) → ℝ} (hV : ContDiff ℝ 2 V) {ρ : ℝ} (hρ : 0 < ρ)
  (hH : ∀ x z : EuclideanSpace ℝ (Fin d), ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)

include hV hρ hH in
/-- LSI for bounded `C²` functions with bounded gradient (cutoff argument). -/
theorem lsi_C2_bounded (hp : IsProbabilityMeasure (CutCur.gibbs V))
    {h : E → ℝ} (hh : ContDiff ℝ 2 h) {M G : ℝ} (hM : ∀ x, |h x| ≤ M)
    (hG : ∀ x, ‖fderiv ℝ h x‖ ≤ G) :
    CutCur.entropyOf (CutCur.gibbs V) (fun x => h x ^ 2) ≤
      2 / ρ * ∫ x, ‖gradient h x‖ ^ 2 ∂CutCur.gibbs V := by
  have := hp
  obtain ⟨L, hL0, hL⟩ := exists_cutoff_grad_bound (d := d)
  have hh1 : ContDiff ℝ 1 h := hh.of_le (by norm_cast)
  have hR : ∀ n : ℕ, (0 : ℝ) < (n : ℝ) + 1 := fun n => by positivity
  set fn : ℕ → E → ℝ := fun n x => cutoff ((n : ℝ) + 1) x * h x with hfn
  have hfn2 : ∀ n, ContDiff ℝ 2 (fn n) := fun n =>
    ((cutoff_contDiff ((n : ℝ) + 1)).of_le (by norm_cast)).mul hh
  have hfn1 : ∀ n, ContDiff ℝ 1 (fn n) := fun n => (hfn2 n).of_le (by norm_cast)
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  have hfeq : ∀ (n : ℕ) (y : E), ‖y‖ ≤ (n : ℝ) + 1 → fn n y = h y := by
    intro n y hy
    simp only [hfn]
    rw [cutoff_eq_one (hR n) hy, one_mul]
  refine lsi_of_approx (G := G + M * L) (M := M) fn hfn1 (fun n x => ?_) (fun n x => ?_) (fun x => ?_)
    (fun x => ?_) (fun n => ?_)
  · simp only [hfn]
    rw [abs_mul, abs_of_nonneg (cutoff_nonneg _ _)]
    calc cutoff _ x * |h x| ≤ 1 * M :=
          mul_le_mul (cutoff_le_one _ _) (hM x) (abs_nonneg _) zero_le_one
      _ = M := one_mul M
  · have hu : DifferentiableAt ℝ (cutoff ((n : ℝ) + 1)) x :=
      ((cutoff_contDiff _).differentiable (by norm_num) _)
    have hhd : DifferentiableAt ℝ h x := hh1.differentiable one_ne_zero x
    simp only [hfn]
    rw [fderiv_fun_mul hu hhd]
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul, norm_smul, Real.norm_of_nonneg (cutoff_nonneg _ _), Real.norm_eq_abs]
    have h1 : cutoff ((n : ℝ) + 1) x * ‖fderiv ℝ h x‖ ≤ G :=
      (mul_le_mul (cutoff_le_one _ _) (hG x) (norm_nonneg _) zero_le_one).trans_eq (one_mul G)
    have hinv : ((n : ℝ) + 1)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)])
    have h2 : |h x| * ‖fderiv ℝ (cutoff ((n : ℝ) + 1)) x‖ ≤ M * L :=
      mul_le_mul (hM x) ((norm_fderiv_cutoff_le hL (hR n) x).trans (by nlinarith)) (norm_nonneg _) hM0
    linarith
  · refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_gt_atTop ⌈‖x‖⌉₊] with n hn
    have : ‖x‖ ≤ (n : ℝ) + 1 := by
      have := Nat.le_ceil ‖x‖
      have h2 : (⌈‖x‖⌉₊ : ℝ) < n := by exact_mod_cast hn
      linarith
    exact (hfeq n x this).symm
  · refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_gt_atTop ⌈‖x‖⌉₊] with n hn
    have hlt : ‖x‖ < (n : ℝ) + 1 := by
      have := Nat.le_ceil ‖x‖
      have h2 : (⌈‖x‖⌉₊ : ℝ) < n := by exact_mod_cast hn
      linarith
    have heq : fn n =ᶠ[𝓝 x] h := by
      have hmem : Metric.ball (0 : E) ((n : ℝ) + 1) ∈ 𝓝 x :=
        Metric.isOpen_ball.mem_nhds (by simpa using hlt)
      filter_upwards [hmem] with y hy
      exact hfeq n y (by simpa using (Metric.mem_ball.mp hy).le)
    rw [heq.fderiv_eq]
  · refine lsi_C2_compact hV hρ hH hp (hfn2 n) ?_
    refine HasCompactSupport.intro (isCompact_closedBall (0 : E) (2 * ((n : ℝ) + 1))) (fun x hx => ?_)
    simp only [hfn]
    rw [cutoff_eq_zero (hR n) (not_le.mp (mem_closedBall_zero_iff.not.mp hx)).le, zero_mul]


include hV hρ hH in
/-- The regularised-square entropy bound used by the closed-domain argument, with no Brownian motion. -/
theorem logSobolev_regularized_compact_square_nobm
    (hp : IsProbabilityMeasure (gibbsMeasure volume V))
    {f : E → ℝ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) (ε : ℝ) (hε : 0 < ε) :
    let μ := gibbsMeasure volume V
    let a := ∫ x, f x ^ 2 ∂μ
    (∫⁻ x, ENNReal.ofReal (InformationTheory.klFun ((f x ^ 2 + ε) / (a + ε))) ∂μ) ≤
      ENNReal.ofReal ((2 / ρ) / (a + ε) * ∫ x, ‖gradient f x‖ ^ 2 ∂μ) := by
  intro μ a
  have hp' : IsProbabilityMeasure (CutCur.gibbs V) := hp
  have := hp
  have hf1 : ContDiff ℝ 1 f := hf.of_le (by norm_cast)
  obtain ⟨M, hM⟩ := exists_abs_bound hf.continuous hfc
  obtain ⟨Gf, hGf⟩ : ∃ G : ℝ, ∀ y, ‖fderiv ℝ f y‖ ≤ G := by
    obtain ⟨G, hG⟩ := exists_abs_bound (G := fun y => ‖fderiv ℝ f y‖)
      (hf1.continuous_fderiv one_ne_zero).norm (hfc.fderiv ℝ).norm
    exact ⟨G, fun y => by simpa using hG y⟩
  set h : E → ℝ := fun x => Real.sqrt (f x ^ 2 + ε) with hh
  have hpos : ∀ x, 0 < f x ^ 2 + ε := fun x => by positivity
  have hsq : ∀ x, h x ^ 2 = f x ^ 2 + ε := fun x => Real.sq_sqrt (hpos x).le
  have hh2 : ContDiff ℝ 2 h := ((hf.pow 2).add contDiff_const).sqrt (fun x => (hpos x).ne')
  have hhM : ∀ x, |h x| ≤ Real.sqrt (M ^ 2 + ε) := by
    intro x
    rw [abs_of_nonneg (Real.sqrt_nonneg _)]
    exact Real.sqrt_le_sqrt (by
      have := sq_le_sq' (abs_le.mp (hM x)).1 (abs_le.mp (hM x)).2
      linarith)
  have hgrad : ∀ x, ‖fderiv ℝ h x‖ ≤ ‖fderiv ℝ f x‖ := by
    intro x
    have hd : HasFDerivAt f (fderiv ℝ f x) x := (hf1.differentiable one_ne_zero x).hasFDerivAt
    have h1 := ((hd.mul hd).add_const ε).sqrt (by simpa [sq] using (hpos x).ne')
    have heq : h = fun y => Real.sqrt ((f * f) y + ε) := by
      funext y; simp [hh, sq]
    have h2 := h1.fderiv
    rw [← heq] at h2
    simp only [Pi.mul_apply] at h2
    rw [h2, norm_smul]
    have : ‖f x • fderiv ℝ f x + f x • fderiv ℝ f x‖ = 2 * |f x| * ‖fderiv ℝ f x‖ := by
      rw [← two_smul ℝ (f x • fderiv ℝ f x), smul_smul, norm_smul, Real.norm_eq_abs, abs_mul]
      norm_num
    rw [this]
    have hfx : |f x| ≤ Real.sqrt (f x * f x + ε) := by
      rw [← Real.sqrt_sq_eq_abs]
      exact Real.sqrt_le_sqrt (by nlinarith)
    have hs : 0 < Real.sqrt (f x * f x + ε) := Real.sqrt_pos.mpr (by nlinarith [hpos x, sq (f x)])
    rw [Real.norm_eq_abs, abs_of_pos (by positivity : 0 < 1 / (2 * Real.sqrt (f x * f x + ε)))]
    calc 1 / (2 * Real.sqrt (f x * f x + ε)) * (2 * |f x| * ‖fderiv ℝ f x‖)
        = (|f x| / Real.sqrt (f x * f x + ε)) * ‖fderiv ℝ f x‖ := by field_simp
      _ ≤ 1 * ‖fderiv ℝ f x‖ := by
          gcongr
          rw [div_le_one hs]; exact hfx
      _ = _ := one_mul _
  have hLSI := lsi_C2_bounded hV hρ hH hp' hh2 hhM (fun x => (hgrad x).trans (hGf x))
  -- gradient comparison
  have hh1 : ContDiff ℝ 1 h := hh2.of_le (by norm_cast)
  have hint_gf : Integrable (fun x => ‖gradient f x‖ ^ 2) μ := by
    refine Integrable.of_bound (C := Gf ^ 2) (cont_gradsq hf1).aestronglyMeasurable
      (Eventually.of_forall fun x => ?_)
    rw [Real.norm_of_nonneg (sq_nonneg _), norm_gradient_eq']
    exact pow_le_pow_left₀ (norm_nonneg _) (hGf x) 2
  have hint_gh : Integrable (fun x => ‖gradient h x‖ ^ 2) μ := by
    refine Integrable.of_bound (C := Gf ^ 2) (cont_gradsq hh1).aestronglyMeasurable
      (Eventually.of_forall fun x => ?_)
    rw [Real.norm_of_nonneg (sq_nonneg _), norm_gradient_eq']
    exact pow_le_pow_left₀ (norm_nonneg _) ((hgrad x).trans (hGf x)) 2
  have hgle : ∫ x, ‖gradient h x‖ ^ 2 ∂μ ≤ ∫ x, ‖gradient f x‖ ^ 2 ∂μ := by
    refine integral_mono hint_gh hint_gf fun x => ?_
    simp only [norm_gradient_eq']
    exact pow_le_pow_left₀ (norm_nonneg _) (hgrad x) 2
  -- entropy of `w = f² + ε`
  set w : E → ℝ := fun x => f x ^ 2 + ε with hw
  have hwpos : ∀ x, 0 < w x := hpos
  have hf2I : Integrable (fun x => f x ^ 2) μ := by
    refine Integrable.of_bound (C := M ^ 2) (hf.continuous.pow 2).aestronglyMeasurable
      (Eventually.of_forall fun x => ?_)
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    exact sq_le_sq' (abs_le.mp (hM x)).1 (abs_le.mp (hM x)).2
  have hwI : Integrable w μ := hf2I.add (integrable_const ε)
  have hwlI : Integrable (fun x => w x * Real.log (w x)) μ := by
    obtain ⟨B2, hB2⟩ := (isCompact_Icc (a := 0) (b := M ^ 2 + ε)).exists_bound_of_continuousOn
      Real.continuous_mul_log.continuousOn
    refine Integrable.of_bound (C := B2)
      (Real.continuous_mul_log.comp ((hf.continuous.pow 2).add continuous_const)).aestronglyMeasurable
      (Eventually.of_forall fun x => hB2 _ ⟨(hwpos x).le, ?_⟩)
    have := sq_le_sq' (abs_le.mp (hM x)).1 (abs_le.mp (hM x)).2
    simp only [hw]; linarith
  have hD : ∫ x, w x ∂μ = a + ε := by
    simp only [hw]
    rw [integral_add hf2I (integrable_const ε)]
    simp [a]
  have hDpos : 0 < a + ε := by
    have : 0 ≤ a := integral_nonneg fun x => sq_nonneg _
    linarith
  have hent : CutCur.entropyOf μ w = (∫ x, w x * Real.log (w x) ∂μ) - (a + ε) * Real.log (a + ε) := by
    unfold CutCur.entropyOf
    rw [hD]
  have hpt : ∀ x, InformationTheory.klFun (w x / (a + ε)) =
      (a + ε)⁻¹ * (w x * Real.log (w x)) - ((a + ε)⁻¹ * Real.log (a + ε)) * w x
        - (a + ε)⁻¹ * w x + 1 := by
    intro x
    rw [InformationTheory.klFun_apply, Real.log_div (hwpos x).ne' hDpos.ne']
    field_simp
    ring
  set c : ℝ := (a + ε)⁻¹ with hc
  set k : ℝ := (a + ε)⁻¹ * Real.log (a + ε) with hk
  have hA : Integrable (fun x => c * (w x * Real.log (w x))) μ := hwlI.const_mul c
  have hB : Integrable (fun x => k * w x) μ := hwI.const_mul k
  have hC : Integrable (fun x => c * w x) μ := hwI.const_mul c
  have hAB : Integrable (fun x => c * (w x * Real.log (w x)) - k * w x) μ := hA.sub hB
  have hABC : Integrable (fun x => c * (w x * Real.log (w x)) - k * w x - c * w x) μ := hAB.sub hC
  have hklI : Integrable (fun x => InformationTheory.klFun (w x / (a + ε))) μ := by
    have := hABC.add (integrable_const (1 : ℝ))
    exact this.congr (Eventually.of_forall fun x => (hpt x).symm)
  have hklint : ∫ x, InformationTheory.klFun (w x / (a + ε)) ∂μ = (a + ε)⁻¹ * CutCur.entropyOf μ w := by
    simp_rw [hpt]
    rw [integral_add hABC (integrable_const _), integral_sub hAB hC, integral_sub hA hB,
      integral_const_mul, integral_const_mul, integral_const_mul, hD, hent]
    simp only [integral_const, measureReal_def, measure_univ, ENNReal.toReal_one, one_smul, hc, hk]
    field_simp
    ring
  have hnn : ∀ x, 0 ≤ InformationTheory.klFun (w x / (a + ε)) := fun x =>
    InformationTheory.klFun_nonneg (div_nonneg (hwpos x).le hDpos.le)
  show (∫⁻ x, ENNReal.ofReal (InformationTheory.klFun (w x / (a + ε))) ∂μ) ≤ _
  rw [← ofReal_integral_eq_lintegral_ofReal hklI (Eventually.of_forall hnn), hklint]
  refine ENNReal.ofReal_le_ofReal ?_
  have hLSI' : CutCur.entropyOf μ w ≤ 2 / ρ * ∫ x, ‖gradient f x‖ ^ 2 ∂μ := by
    have e : CutCur.entropyOf μ w = CutCur.entropyOf μ (fun x => h x ^ 2) := by
      simp only [CutCur.entropyOf, hsq, hw]
    rw [e]
    refine hLSI.trans ?_
    exact mul_le_mul_of_nonneg_left hgle (by positivity)
  calc (a + ε)⁻¹ * CutCur.entropyOf μ w ≤ (a + ε)⁻¹ * (2 / ρ * ∫ x, ‖gradient f x‖ ^ 2 ∂μ) :=
        mul_le_mul_of_nonneg_left hLSI' (inv_nonneg.mpr hDpos.le)
    _ = _ := by ring

end Main

end CutoffRigidity.NoBm
