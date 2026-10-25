module
public import CutoffRigidity.PositiveCoreDensityApproximation

/-! # Actual bounded positive truncation of finite-entropy densities

Clipping toward one decreases the genuine KL integrand. Actual mass
normalization and its exact entropy identity yield L¹ and KL convergence,
preparing the smooth compact core approximation.
-/
public section
namespace CutoffRigidity
open MeasureTheory ProbabilityTheory InformationTheory Filter Set
open scoped Topology ENNReal NNReal

@[expose] noncomputable def entropyDensityClip (ε N z : ℝ) : ℝ := max ε (min N z)

theorem klFun_entropyDensityClip_le {ε N z : ℝ}
    (hz : 0 ≤ z) (hε : ε ≤ 1) (hN : 1 ≤ N) :
    klFun (entropyDensityClip ε N z) ≤ klFun z := by
  by_cases hze : z ≤ ε
  · rw [entropyDensityClip, min_eq_right (hze.trans (hε.trans hN)), max_eq_left hze]
    have hh := convexOn_klFun.le_on_segment hz (by norm_num : (0 : ℝ) ≤ 1)
      (by rw [segment_eq_Icc (hze.trans hε)]; exact ⟨hze, hε⟩)
    simpa only [klFun_one, max_eq_left (klFun_nonneg hz)] using hh
  · by_cases hnz : N ≤ z
    · rw [entropyDensityClip, min_eq_left hnz, max_eq_right (hε.trans hN)]
      have hh := convexOn_klFun.le_on_segment (by norm_num : (0 : ℝ) ≤ 1) hz
        (by rw [segment_eq_Icc (hN.trans hnz)]; exact ⟨hN, hnz⟩)
      simpa only [klFun_one, max_eq_right (klFun_nonneg hz)] using hh
    · rw [entropyDensityClip, min_eq_right (le_of_not_ge hnz), max_eq_right (le_of_not_ge hze)]

theorem entropyDensityClip_tendsto {z : ℝ} (hz : 0 ≤ z) :
    Tendsto (fun n : ℕ => entropyDensityClip (differenceStep n) ((n : ℝ) + 1) z) atTop (𝓝 z) := by
  have htop : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
  have hmin : Tendsto (fun n : ℕ => min ((n : ℝ) + 1) z) atTop (𝓝 z) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [htop.eventually_ge_atTop z] with n hn
    exact (min_eq_right hn).symm
  simpa only [entropyDensityClip, max_eq_right hz] using differenceStep_tendsto_zero.max hmin

/-- Exact normalization identity for the genuine KL integrand. -/
theorem klFun_div_positive {u A : ℝ} (hu : 0 < u) (hA : 0 < A) :
    klFun (u / A) = klFun u / A - (u / A) * Real.log A + (1 - 1 / A) := by
  rw [klFun_apply, klFun_apply, Real.log_div hu.ne' hA.ne']
  field_simp
  ring


set_option maxHeartbeats 700000 in
/-- Genuine truncation convergence follows from dominated convergence
against f+1 and the actual integrable KL density; clipping does not
increase the KL integrand. -/
theorem entropyDensityClip_L1_entropy_tendsto
    {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsProbabilityMeasure μ]
    {f : X → ℝ} (hf : Measurable f) (hfI : Integrable f μ) (hf0 : ∀ x, 0 ≤ f x)
    (hKL : Integrable (fun x => klFun (f x)) μ) :
    let u := fun n x => entropyDensityClip (differenceStep n) ((n : ℝ) + 1) (f x)
    Tendsto (fun n => ∫ x, ‖u n x - f x‖ ∂μ) atTop (𝓝 0) ∧
      Tendsto (fun n => ∫ x, klFun (u n x) ∂μ) atTop (𝓝 (∫ x, klFun (f x) ∂μ)) := by
  let u := fun n x => entropyDensityClip (differenceStep n) ((n : ℝ) + 1) (f x)
  have huMeas (n : ℕ) : Measurable (u n) := measurable_const.max (measurable_const.min hf)
  have huPos (n : ℕ) (x : X) : 0 < u n x :=
    (differenceStep_pos n).trans_le (le_max_left _ _)
  have huLe (n : ℕ) (x : X) : u n x ≤ f x + 1 := by
    apply (max_le_max (differenceStep_le_one n) (min_le_right _ _)).trans
    exact max_le (by linarith [hf0 x]) (by linarith)
  have hpoint (x : X) : Tendsto (fun n => u n x) atTop (𝓝 (f x)) := entropyDensityClip_tendsto (hf0 x)
  constructor
  · have hh := tendsto_integral_filter_of_dominated_convergence
      (F := fun n x => ‖u n x - f x‖) (f := fun _ => (0 : ℝ)) (fun x => 2 * f x + 1)
      (Eventually.of_forall (fun n => ((huMeas n).aestronglyMeasurable.sub hf.aestronglyMeasurable).norm))
      (Eventually.of_forall (fun n => Eventually.of_forall (fun x => ?_)))
      ((hfI.const_mul 2).add (integrable_const 1))
      (Eventually.of_forall (fun x => by simpa only [sub_self, norm_zero, Pi.sub_apply] using
        ((hpoint x).sub_const (f x)).norm))
    · simpa only [integral_zero, Pi.sub_apply] using hh
    · rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
      have hb := norm_sub_le (u n x) (f x)
      simp only [Real.norm_eq_abs, abs_of_pos (huPos n x), abs_of_nonneg (hf0 x)] at hb
      exact hb.trans (by linarith [huLe n x])
  · apply tendsto_integral_filter_of_dominated_convergence (fun x => klFun (f x))
      (Eventually.of_forall (fun n => (measurable_klFun.comp (huMeas n)).aestronglyMeasurable))
      (Eventually.of_forall (fun n => Eventually.of_forall (fun x => ?_))) hKL
      (Eventually.of_forall (fun x => continuous_klFun.continuousAt.tendsto.comp (hpoint x)))
    simp only [Real.norm_eq_abs, Function.comp_def, abs_of_nonneg (klFun_nonneg (huPos n x).le)]
    exact klFun_entropyDensityClip_le (N := (n : ℝ) + 1) (hf0 x) (differenceStep_le_one n) (by linarith [show 0 ≤ (n : ℝ) from Nat.cast_nonneg n])

/-- Integration of the exact normalization identity; all integrability
is inherited from the actual integrable density and its KL integrand. -/
theorem integral_klFun_div_mass
    {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsProbabilityMeasure μ]
    {u : X → ℝ} (hu : Integrable u μ) (hupos : ∀ x, 0 < u x)
    (hKL : Integrable (fun x => klFun (u x)) μ) (hMass : 0 < ∫ x, u x ∂μ) :
    (∫ x, klFun (u x / (∫ y, u y ∂μ)) ∂μ) =
      (∫ x, klFun (u x) ∂μ) / (∫ x, u x ∂μ) -
        Real.log (∫ x, u x ∂μ) + (1 - 1 / (∫ x, u x ∂μ)) := by
  let A := ∫ x, u x ∂μ
  have he (x : X) : klFun (u x / A) = klFun (u x) / A - (u x / A) * Real.log A + (1 - 1 / A) :=
    klFun_div_positive (hupos x) hMass
  have hAdd := integral_add
    ((hKL.div_const A).sub ((hu.div_const A).mul_const (Real.log A))) (integrable_const (1 - 1 / A))
  have hSub := integral_sub (hKL.div_const A) ((hu.div_const A).mul_const (Real.log A))
  simp only [Pi.sub_apply] at hAdd hSub
  rw [integral_congr_ae (Eventually.of_forall he), hAdd, hSub,
    integral_div, integral_mul_const, integral_div, integral_const]
  dsimp only [A]
  simp only [measureReal_def, measure_univ, ENNReal.toReal_one, one_smul, div_self hMass.ne', one_mul]


/-- Actual KL-integral equality for a normalized density whose genuine
KL integrand is integrable; no boundedness hypothesis is needed. -/
theorem klDiv_withDensity_eq_integral_of_klFun_integrable
    {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsProbabilityMeasure μ]
    {f : X → ℝ} (hf : Measurable f) (hfI : Integrable f μ) (hf0 : ∀ x, 0 ≤ f x)
    (hMass : ∫ x, f x ∂μ = 1) (hKL : Integrable (fun x => klFun (f x)) μ) :
    klDiv (μ.withDensity (fun x => ENNReal.ofReal (f x))) μ = ENNReal.ofReal (∫ x, klFun (f x) ∂μ) := by
  let := isProbabilityMeasure_withDensity_ofReal_integral_one hfI hf0 hMass
  rw [klDiv_eq_lintegral_klFun_of_ac (withDensity_absolutelyContinuous _ _),
    ofReal_integral_eq_lintegral_ofReal hKL (Eventually.of_forall (fun x => klFun_nonneg (hf0 x)))]
  apply lintegral_congr_ae
  filter_upwards [Measure.rnDeriv_withDensity μ hf.ennreal_ofReal] with x hx
  rw [hx, ENNReal.toReal_ofReal (hf0 x)]

set_option maxHeartbeats 850000 in
/-- Every actual finite-entropy probability density has bounded uniformly
positive normalized approximants, with genuine L¹ and KL convergence.
The bounds may depend on the approximation index and are constructed. -/
theorem exists_bounded_positive_density_L1_KL_approx
    {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsProbabilityMeasure μ]
    {f : X → ℝ} (hf : Measurable f) (hfI : Integrable f μ) (hf0 : ∀ x, 0 ≤ f x)
    (hMass : ∫ x, f x ∂μ = 1) (hKL : Integrable (fun x => klFun (f x)) μ) :
    ∃ r : ℕ → X → ℝ,
      (∀ n, Measurable (r n)) ∧
      (∀ n, ∃ a b : ℝ, 0 < a ∧ ∀ x, r n x ∈ Icc a b) ∧
      (∀ n, ∫ x, r n x ∂μ = 1) ∧
      Tendsto (fun n => ∫ x, ‖r n x - f x‖ ∂μ) atTop (𝓝 0) ∧
      Tendsto (fun n => klDiv (μ.withDensity (fun x => ENNReal.ofReal (r n x))) μ)
        atTop (𝓝 (klDiv (μ.withDensity (fun x => ENNReal.ofReal (f x))) μ)) := by
  let u := fun n x => entropyDensityClip (differenceStep n) ((n : ℝ) + 1) (f x)
  have huMeas (n : ℕ) : Measurable (u n) := measurable_const.max (measurable_const.min hf)
  have huLower (n : ℕ) (x : X) : differenceStep n ≤ u n x := le_max_left _ _
  have huUpper (n : ℕ) (x : X) : u n x ≤ (n : ℝ) + 1 :=
    max_le ((differenceStep_le_one n).trans (by linarith [show 0 ≤ (n : ℝ) from Nat.cast_nonneg n])) (min_le_left _ _)
  have huPos (n : ℕ) (x : X) : 0 < u n x := (differenceStep_pos n).trans_le (huLower n x)
  have huI (n : ℕ) : Integrable (u n) μ := (integrable_const ((n : ℝ) + 1)).mono'
    (huMeas n).aestronglyMeasurable (Eventually.of_forall (fun x => by
      rw [Real.norm_eq_abs, abs_of_pos (huPos n x)]; exact huUpper n x))
  have huKL (n : ℕ) : Integrable (fun x => klFun (u n x)) μ := hKL.mono'
    (measurable_klFun.comp (huMeas n)).aestronglyMeasurable (Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (klFun_nonneg (huPos n x).le)]
      exact klFun_entropyDensityClip_le (N := (n : ℝ) + 1) (hf0 x) (differenceStep_le_one n)
        (by linarith [show 0 ≤ (n : ℝ) from Nat.cast_nonneg n]))
  obtain ⟨hL1, hEntropy⟩ := entropyDensityClip_L1_entropy_tendsto μ hf hfI hf0 hKL
  let mass := fun n => ∫ x, u n x ∂μ
  have hmassPos (n : ℕ) : 0 < mass n := by
    have hh := integral_mono (integrable_const (differenceStep n)) (huI n) (huLower n)
    have hl : differenceStep n ≤ mass n := by simpa only [integral_const, measureReal_def,
      measure_univ, ENNReal.toReal_one, one_smul] using hh
    exact (differenceStep_pos n).trans_le hl
  have hmassLim : Tendsto mass atTop (𝓝 1) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    apply squeeze_zero (fun n => norm_nonneg _) _ hL1
    intro n
    have he : mass n - 1 = ∫ x, u n x - f x ∂μ := by
      rw [integral_sub (huI n) hfI, hMass]
    change ‖mass n - 1‖ ≤ ∫ x, ‖u n x - f x‖ ∂μ
    rw [he]
    exact norm_integral_le_integral_norm (fun x => u n x - f x)
  let r := fun n x => u n x / mass n
  have hrMeas (n : ℕ) : Measurable (r n) := (huMeas n).div_const _
  have hrLower (n : ℕ) (x : X) : differenceStep n / mass n ≤ r n x :=
    div_le_div_of_nonneg_right (huLower n x) (hmassPos n).le
  have hrUpper (n : ℕ) (x : X) : r n x ≤ ((n : ℝ) + 1) / mass n :=
    div_le_div_of_nonneg_right (huUpper n x) (hmassPos n).le
  have hrMass (n : ℕ) : ∫ x, r n x ∂μ = 1 := by
    rw [show (∫ x, r n x ∂μ) = mass n / mass n by exact integral_div _ _]
    exact div_self (hmassPos n).ne'
  have hL1norm : Tendsto (fun n => ∫ x, ‖r n x - f x‖ ∂μ) atTop (𝓝 0) :=
    normalized_density_L1_tendsto μ f u hfI huI hf0 hMass (fun n x => (huPos n x).le) hmassPos hL1
  have hklEq (n : ℕ) : klDiv (μ.withDensity (fun x => ENNReal.ofReal (r n x))) μ =
      ENNReal.ofReal ((∫ x, klFun (u n x) ∂μ) / mass n - Real.log (mass n) + (1 - 1 / mass n)) := by
    rw [klDiv_bounded_positive_density_eq_integral (hrMeas n) (((n : ℝ) + 1) / mass n)
      (fun x => div_nonneg (huPos n x).le (hmassPos n).le) (hrUpper n) (hrMass n)]
    congr 1
    exact integral_klFun_div_mass μ (huI n) (huPos n) (huKL n) (hmassPos n)
  have hscalar : Tendsto (fun n => (∫ x, klFun (u n x) ∂μ) / mass n -
      Real.log (mass n) + (1 - 1 / mass n)) atTop (𝓝 (∫ x, klFun (f x) ∂μ)) := by
    have hc1 : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
    have hh := ((hEntropy.div hmassLim (by norm_num)).sub (hmassLim.log (by norm_num))).add
      (hc1.sub (hc1.div hmassLim (by norm_num)))
    simpa only [Pi.div_apply, div_one, Real.log_one, sub_zero, sub_self, add_zero] using hh
  refine ⟨r, hrMeas, ?_, hrMass, hL1norm, ?_⟩
  · intro n
    exact ⟨differenceStep n / mass n, ((n : ℝ) + 1) / mass n,
      div_pos (differenceStep_pos n) (hmassPos n), fun x => ⟨hrLower n x, hrUpper n x⟩⟩
  · have hh := ENNReal.continuous_ofReal.continuousAt.tendsto.comp hscalar
    simpa only [Function.comp_def, hklEq,
      klDiv_withDensity_eq_integral_of_klFun_integrable hf hfI hf0 hMass hKL] using hh

end CutoffRigidity
