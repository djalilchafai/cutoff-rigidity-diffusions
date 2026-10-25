module
public import CutoffRigidity.LangevinRNLp
public import CutoffRigidity.BarycenterLpLowerCutoffs

/-! # Genuine Lᵖ cutoff of the relative density for every finite p ≥ 1

This is display (1.25) of the paper under the hypotheses of Corollary 1.4.
After cutoff and for p > 2, the Cauchy–Schwarz interpolation
‖u‖_p^p ≤ ‖u‖₂ ‖u‖_{2p-2}^{p-1} combines the proved L² decay with the
uniform L^{2p-2} density bound derived from the actual power-α Harnack
inequality, α = (2p-2)/(2p-3). Before cutoff, p = 1 is twice the actual
total variation and p > 1 follows from the entropy lower cutoff.
The value p = ∞ is not covered (and is false in general).
-/
public section
namespace CutoffRigidity
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal NNReal
variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

/-- Cauchy–Schwarz interpolation of the Lᵠ norm between L² and L^(2q-2). -/
theorem eLpNorm_rpow_le_eLpNorm_two_mul_interp {X : Type*} [MeasurableSpace X] (μ : Measure X)
    {u : X → ℝ} (hu : AEStronglyMeasurable u μ) {q : ℝ} (hq : 2 < q) :
    eLpNorm u (ENNReal.ofReal q) μ ^ q ≤
      eLpNorm u 2 μ * eLpNorm u (ENNReal.ofReal (2 * q - 2)) μ ^ (q - 1) := by
  have hq0 : 0 < q := by linarith
  have hr0 : 0 < 2 * q - 2 := by linarith
  have hq1 : q - 1 ≠ 0 := by linarith
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by simpa using hq0) ENNReal.ofReal_ne_top hu,
    eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num) hu,
    eLpNorm_eq_lintegral_rpow_enorm_toReal (by simpa using hr0) ENNReal.ofReal_ne_top hu,
    ENNReal.toReal_ofReal hq0.le, ENNReal.toReal_ofReal hr0.le, ← ENNReal.rpow_mul,
    ← ENNReal.rpow_mul, show 1 / q * q = 1 by field_simp, ENNReal.rpow_one,
    show 1 / (2 * q - 2) * (q - 1) = 1 / 2 by
      rw [show 2 * q - 2 = 2 * (q - 1) by ring]; field_simp, ENNReal.toReal_ofNat]
  have hm : AEMeasurable (fun x => ‖u x‖ₑ) μ := hu.enorm
  have hH := ENNReal.lintegral_mul_le_Lp_mul_Lq μ Real.HolderConjugate.two_two hm
    (hm.pow_const (q - 1))
  have he1 : (fun x => ‖u x‖ₑ ^ q) = (fun x => ‖u x‖ₑ) * fun x => ‖u x‖ₑ ^ (q - 1) := by
    funext x
    rw [Pi.mul_apply, show q = 1 + (q - 1) by ring, ENNReal.rpow_add_of_nonneg _ _ zero_le_one
      (by linarith), ENNReal.rpow_one]
    ring_nf
  have he2 (x : X) : (‖u x‖ₑ ^ (q - 1)) ^ (2 : ℝ) = ‖u x‖ₑ ^ (2 * q - 2) := by
    rw [← ENNReal.rpow_mul]
    ring_nf
  simp_rw [he2] at hH
  rw [he1]
  exact hH

/-- The actual uniform Lᵠ density profile on a mean ball is controlled by
the actual L² profile and the integrated power-α Harnack bound. -/
theorem meanBallLp_rpow_upper (D : SpectralInformationLowerData Ω d) (hd : 0 < d)
    {c : ℝ} (hc : 0 ≤ c) {t : ℝ} (ht : 0 < t) {q : ℝ} (hq : 2 < q) :
    meanBallLp D c (ENNReal.ofReal q) t ^ q ≤ meanBallLp D c 2 t *
      (ENNReal.ofReal (Real.exp ((2 * q - 3) / 2 *
        (D.rate / (Real.exp (2 * D.rate * t) - 1) * ((c ^ 2 + D.rate⁻¹) * d)))) + 1) ^ (q - 1) := by
  let := D.probability
  let μ := gibbsMeasure volume D.potential
  let S := Metric.closedBall (∫ y, y ∂gibbsMeasure volume D.potential) (c * Real.sqrt d)
  let R := meanBallLp D c 2 t *
      (ENNReal.ofReal (Real.exp ((2 * q - 3) / 2 *
        (D.rate / (Real.exp (2 * D.rate * t) - 1) * ((c ^ 2 + D.rate⁻¹) * d)))) + 1) ^ (q - 1)
  have hq0 : 0 < q := by linarith
  have hρ := D.rate_pos
  have hden : 0 < Real.exp (2 * D.rate * t) - 1 :=
    sub_pos.mpr (Real.one_lt_exp_iff.mpr (by positivity))
  have hx : ∀ x : S, relativeLpDistance (langevinKernel D.potential D.driver D.noiseLaw t.toNNReal x)
      μ (ENNReal.ofReal q) ^ q ≤ R := by
    intro x
    let ν := langevinKernel D.potential D.driver D.noiseLaw t.toNNReal x
    let := langevinKernel_isMarkovKernel D.brownian D.smooth D.rate D.rate_pos.le D.hessian t.toNNReal
    have hAC : ν ≪ μ := langevinKernel_absolutelyContinuous_gibbs D.brownian D.smooth D.probability
      D.rate D.rate_pos D.hessian x t ht
    let h := fun y => (ν.rnDeriv μ y).toReal
    have hhM : Measurable h := (Measure.measurable_rnDeriv ν μ).ennreal_toReal
    rw [relativeLpDistance_eq_eLpNorm ν μ hAC]
    have hI := eLpNorm_rpow_le_eLpNorm_two_mul_interp μ (hhM.sub_const 1).aestronglyMeasurable hq
    have h2 : eLpNorm (fun y => h y - 1) 2 μ ≤ meanBallLp D c 2 t := by
      rw [← relativeLpDistance_eq_eLpNorm ν μ hAC]
      exact le_iSup (fun y : S => relativeLpDistance
        (langevinKernel D.potential D.driver D.noiseLaw t.toNNReal y) μ 2) x
    let α := (2 * q - 2) / (2 * q - 3)
    have h23 : 0 < 2 * q - 3 := by linarith
    have hα : 1 < α := (one_lt_div h23).mpr (by linarith)
    have hα2 : α ≤ 2 := (div_le_iff₀ h23).mpr (by linarith)
    have hα1 : α - 1 = 1 / (2 * q - 3) := by dsimp only [α]; field_simp; ring
    have hαr : α / (α - 1) = 2 * q - 2 := by rw [hα1]; dsimp only [α]; field_simp
    have hRN := langevinKernel_rnDeriv_eLpNorm_le D.brownian D.smooth D.probability D.rate D.rate_pos
      D.hessian α hα hα2 t ht x
    rw [hαr] at hRN
    have hcost := spectral_mean_ball_initial_transport_bound D hd hc x x.property
    rw [squaredWasserstein_dirac_eq_ofReal _ (gibbs_memLp_two_id_of_hessian_bound
      D.smooth D.rate D.rate_pos D.hessian)] at hcost
    have hmom := (ENNReal.ofReal_le_ofReal_iff (by positivity : 0 ≤ (c^2+D.rate⁻¹)*(d:ℝ))).mp hcost
    have hexp : D.rate / (2 * (α - 1) * (Real.exp (2 * D.rate * t) - 1)) *
        ∫ y, ‖(x : E) - y‖ ^ 2 ∂μ ≤ (2 * q - 3) / 2 *
          (D.rate / (Real.exp (2 * D.rate * t) - 1) * ((c ^ 2 + D.rate⁻¹) * d)) := by
      have hcoef : D.rate / (2 * (α - 1) * (Real.exp (2 * D.rate * t) - 1)) =
          (2 * q - 3) / 2 * (D.rate / (Real.exp (2 * D.rate * t) - 1)) := by
        rw [hα1]; field_simp
      rw [hcoef, mul_assoc]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      calc
        _ = ∫ y, ‖y - (x : E)‖ ^ 2 ∂μ := by simp only [norm_sub_rev]
        _ ≤ _ := hmom
    have hr1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (2 * q - 2) := by
      rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal (by linarith)
    have hconst : eLpNorm (fun _ : E => (1 : ℝ)) (ENNReal.ofReal (2 * q - 2)) μ = 1 := by
      rw [eLpNorm_const _ (by simpa using (by linarith : (0:ℝ) < 2 * q - 2))
        (IsProbabilityMeasure.ne_zero μ), measure_univ, ENNReal.one_rpow, enorm_one, one_mul]
    have htri : eLpNorm (fun y => h y - 1) (ENNReal.ofReal (2 * q - 2)) μ ≤
        ENNReal.ofReal (Real.exp ((2 * q - 3) / 2 *
          (D.rate / (Real.exp (2 * D.rate * t) - 1) * ((c ^ 2 + D.rate⁻¹) * d)))) + 1 := by
      calc
        _ = eLpNorm (h - fun _ : E => (1 : ℝ)) (ENNReal.ofReal (2 * q - 2)) μ := rfl
        _ ≤ eLpNorm h (ENNReal.ofReal (2 * q - 2)) μ +
            eLpNorm (fun _ : E => (1 : ℝ)) (ENNReal.ofReal (2 * q - 2)) μ := eLpNorm_sub_le hr1
        _ ≤ _ := by
          rw [hconst]
          exact add_le_add (hRN.trans (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr hexp))) le_rfl
    exact hI.trans (mul_le_mul' h2 (ENNReal.rpow_le_rpow htri (by linarith)))
  have hsup : meanBallLp D c (ENNReal.ofReal q) t ≤ R ^ (1 / q) := by
    apply iSup_le
    intro x
    have hh := ENNReal.rpow_le_rpow (hx x) (by positivity : (0:ℝ) ≤ 1 / q)
    rwa [← ENNReal.rpow_mul, mul_one_div_cancel hq0.ne', ENNReal.rpow_one] at hh
  calc
    _ ≤ (R ^ (1 / q)) ^ q := ENNReal.rpow_le_rpow hsup hq0.le
    _ = R := by rw [← ENNReal.rpow_mul, one_div_mul_cancel hq0.ne', ENNReal.rpow_one]

/-- After cutoff, every finite exponent above two has vanishing actual
mean-ball density error. -/
theorem meanBall_Lp_after_cutoff_gt_two_of_harnack
    (D : ∀ n : ℕ, SpectralInformationLowerData Ω n) {c ε : ℝ}
    (hc : 0 ≤ c) (hε : 0 < ε)
    (hsub : (fun n => (D n).rate) =o[atTop] (fun n : ℕ => Real.log (n:ℝ)))
    {q : ℝ} (hq : 2 < q) :
    Tendsto (fun n : ℕ => meanBallLp (D n) c (ENNReal.ofReal q)
      ((1+ε)*criticalTime n (D n).rate)) atTop (𝓝 0) := by
  have hq0 : 0 < q := by linarith
  have hE := chiSquare_exponent_tendsto_zero (fun n => (D n).rate)
    (fun n => (D n).rate_pos) c hε hsub.tendsto_div_nhds_zero
  have hF : Tendsto (fun n : ℕ => (ENNReal.ofReal (Real.exp ((2 * q - 3) / 2 *
      ((D n).rate / (Real.exp (2 * (D n).rate * ((1+ε)*criticalTime n (D n).rate)) - 1) *
        ((c ^ 2 + (D n).rate⁻¹) * n)))) + 1) ^ (q - 1)) atTop
      (𝓝 ((ENNReal.ofReal (Real.exp ((2 * q - 3) / 2 * 0)) + 1) ^ (q - 1))) := by
    have h1 := ((ENNReal.continuous_ofReal.comp Real.continuous_exp).tendsto _).comp
      (hE.const_mul ((2 * q - 3) / 2))
    have h2 := (ENNReal.continuous_rpow_const (y := q - 1)).continuousAt.tendsto.comp
      (h1.add (tendsto_const_nhds (x := (1 : ℝ≥0∞))))
    exact h2
  have hlim := ENNReal.Tendsto.mul (meanBall_L2_after_cutoff D hc hε hsub) (Or.inr (by
      simp only [mul_zero, Real.exp_zero, ENNReal.ofReal_one]
      exact ENNReal.rpow_ne_top_of_nonneg (by linarith) (by norm_num))) hF (Or.inr ENNReal.zero_ne_top)
  rw [zero_mul] at hlim
  have hroot := (ENNReal.continuous_rpow_const (y := 1 / q)).continuousAt.tendsto.comp hlim
  rw [Function.comp_def, ENNReal.zero_rpow_of_pos (by positivity)] at hroot
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hroot
    (Eventually.of_forall (fun n => bot_le))
  filter_upwards [eventually_ge_atTop 2] with n hn
  have hnpos : 0 < n := by omega
  have hlog : 0 < Real.log (n:ℝ) := Real.log_pos (by exact_mod_cast (show 1 < n by omega))
  have hr := (D n).rate_pos
  have ht : 0 < (1+ε)*criticalTime n (D n).rate := by unfold criticalTime; positivity
  have hh := ENNReal.rpow_le_rpow (meanBallLp_rpow_upper (D n) hnpos hc ht hq)
    (by positivity : (0:ℝ) ≤ 1 / q)
  rwa [← ENNReal.rpow_mul, mul_one_div_cancel hq0.ne', ENNReal.rpow_one] at hh

/-- After cutoff, every finite exponent has vanishing actual mean-ball
density error. -/
theorem meanBall_Lp_after_cutoff_of_ne_top
    (D : ∀ n : ℕ, SpectralInformationLowerData Ω n) {c ε : ℝ}
    (hc : 0 ≤ c) (hε : 0 < ε)
    (hsub : (fun n => (D n).rate) =o[atTop] (fun n : ℕ => Real.log (n:ℝ)))
    {p : ℝ≥0∞} (hpt : p ≠ ⊤) :
    Tendsto (fun n : ℕ => meanBallLp (D n) c p
      ((1+ε)*criticalTime n (D n).rate)) atTop (𝓝 0) := by
  rcases le_or_gt p 2 with hp | hp
  · exact meanBall_Lp_after_cutoff_le_two D hc hε hsub hp
  · have hq : 2 < p.toReal := by
      have := (ENNReal.toReal_lt_toReal ENNReal.ofNat_ne_top hpt).mpr hp
      simpa using this
    have h := meanBall_Lp_after_cutoff_gt_two_of_harnack D hc hε hsub hq
    rwa [ENNReal.ofReal_toReal hpt] at h

/-- The actual L¹ density profile is exactly twice the actual total
variation profile at every positive time. -/
theorem spectralSetLp_one_eq_ofReal_two_tv (D : SpectralInformationLowerData Ω d)
    {S : Set E} (hS : S.Nonempty) {t : ℝ} (ht : 0 < t) :
    spectralSetLp D S 1 t = ENNReal.ofReal (2 * projectedSetTV (spectralInformationToAffine D) S t) := by
  let := D.probability
  let := langevinKernel_isMarkovKernel D.brownian D.smooth D.rate D.rate_pos.le D.hessian t.toNNReal
  let tv := fun x => totalVariationDistance (langevinKernel D.potential D.driver D.noiseLaw t.toNNReal x)
    (gibbsMeasure volume D.potential)
  let f := fun a : ℝ => ENNReal.ofReal (2 * a)
  have hf : Monotone f := fun a b hab => ENNReal.ofReal_le_ofReal (by linarith)
  have hfc : Continuous f := ENNReal.continuous_ofReal.comp (continuous_const.mul continuous_id)
  have hEq (x : E) : relativeLpDistance (langevinKernel D.potential D.driver D.noiseLaw t.toNNReal x)
      (gibbsMeasure volume D.potential) 1 = f (tv x) :=
    relativeLpDistance_one_eq_two_tv _ _ (langevinKernel_absolutelyContinuous_gibbs D.brownian
      D.smooth D.probability D.rate D.rate_pos D.hessian x t ht)
  have hcs := hf.map_csSup_of_continuousAt hfc.continuousAt (hS.image tv)
    (projectedSetTV_bddAbove (spectralInformationToAffine D) S t)
  change (⨆ x : S, relativeLpDistance (langevinKernel D.potential D.driver D.noiseLaw t.toNNReal x)
      (gibbsMeasure volume D.potential) 1) = f (sSup (tv '' S))
  rw [hcs, Set.image_image, sSup_image']
  simp only [hEq]

/-- Before cutoff, the actual L¹ density error tends to its maximum two. -/
theorem meanBall_Lp_one_before_cutoff
    (D : ∀ n : ℕ, SpectralInformationLowerData Ω n) {c ε : ℝ}
    (hc : 0 < c) (hε : 0 < ε) (hε1 : ε < 1)
    (hliminf : 0 < liminf (fun n => ENNReal.ofReal (D n).rate) atTop) :
    Tendsto (fun n : ℕ => meanBallLp (D n) c 1
      ((1-ε)*criticalTime n (D n).rate)) atTop (𝓝 2) := by
  have hf : Continuous (fun a : ℝ => ENNReal.ofReal (2 * a)) :=
    ENNReal.continuous_ofReal.comp (continuous_const.mul continuous_id)
  have hh := (hf.tendsto (1 : ℝ)).comp
    (meanBall_totalVariation_before_cutoff D hc hε hε1 hliminf)
  simp only [Function.comp_def, mul_one, ENNReal.ofReal_ofNat] at hh
  apply hh.congr'
  filter_upwards [eventually_ge_atTop 2] with n hn
  have hlog : 0 < Real.log (n:ℝ) := Real.log_pos (by exact_mod_cast (show 1 < n by omega))
  have hr := (D n).rate_pos
  have h1 : 0 < 1 - ε := by linarith
  have ht : 0 < (1-ε)*criticalTime n (D n).rate := by unfold criticalTime; positivity
  exact (spectralSetLp_one_eq_ofReal_two_tv (D n) ⟨_, Metric.mem_closedBall_self (by positivity)⟩ ht).symm

/-- Before cutoff, the actual L¹ cube density error tends to two. -/
theorem convexCube_Lp_one_before_cutoff
    (D : ∀ n : ℕ, ConvexInteractionCubeData Ω n) {c ε : ℝ}
    (hc : 0 < c) (hε : 0 < ε) (hε1 : ε < 1)
    (hliminf : 0 < liminf (fun n => ENNReal.ofReal (D n).rate) atTop) :
    Tendsto (fun n : ℕ => convexCubeLp (D n) c 1
      ((1-ε)*criticalTime n (D n).rate)) atTop (𝓝 2) := by
  have hf : Continuous (fun a : ℝ => ENNReal.ofReal (2 * a)) :=
    ENNReal.continuous_ofReal.comp (continuous_const.mul continuous_id)
  have hh := (hf.tendsto (1 : ℝ)).comp
    (convexCube_totalVariation_before_cutoff D hc hε hε1 hliminf)
  simp only [Function.comp_def, mul_one, ENNReal.ofReal_ofNat] at hh
  apply hh.congr'
  filter_upwards [eventually_ge_atTop 2] with n hn
  have hlog : 0 < Real.log (n:ℝ) := Real.log_pos (by exact_mod_cast (show 1 < n by omega))
  have hr := (D n).rate_pos
  have h1 : 0 < 1 - ε := by linarith
  have ht : 0 < (1-ε)*criticalTime n (D n).rate := by unfold criticalTime; positivity
  have hS : (closedCoordinateCube (∫ y, y ∂gibbsMeasure volume (cubeSpectralData (D n)).potential)
      c).Nonempty :=
    ⟨∫ y, y ∂gibbsMeasure volume (cubeSpectralData (D n)).potential, fun i => by simpa using hc.le⟩
  exact (spectralSetLp_one_eq_ofReal_two_tv (cubeSpectralData (D n)) hS ht).symm

/-- The paper's display (1.25) on actual source mean balls: for every
finite p ≥ 1 the uniform relative density error has cutoff, with limit 2
for p = 1 and +∞ for p > 1 before, and 0 after the critical time. -/
theorem meanBall_Lp_cutoff
    (D : ∀ n : ℕ, SpectralInformationLowerData Ω n) {c ε : ℝ}
    (hc : 0 < c) (hε : 0 < ε) (hε1 : ε < 1)
    (hliminf : 0 < liminf (fun n => ENNReal.ofReal (D n).rate) atTop)
    (hsub : (fun n => (D n).rate) =o[atTop] (fun n : ℕ => Real.log (n : ℝ)))
    {p : ℝ≥0∞} (hp : 1 ≤ p) (hpt : p ≠ ⊤) :
    Tendsto (fun n => meanBallLp (D n) c p ((1 - ε) * criticalTime n (D n).rate)) atTop
      (𝓝 (if p = 1 then 2 else ⊤)) ∧
    Tendsto (fun n => meanBallLp (D n) c p ((1 + ε) * criticalTime n (D n).rate)) atTop (𝓝 0) := by
  refine ⟨?_, meanBall_Lp_after_cutoff_of_ne_top D hc.le hε hsub hpt⟩
  by_cases h1 : p = 1
  · subst h1
    simpa using meanBall_Lp_one_before_cutoff D hc hε hε1 hliminf
  · simp only [h1, ↓reduceIte]
    have hq : 1 < p.toReal := by
      have := (ENNReal.toReal_lt_toReal ENNReal.one_ne_top hpt).mpr (lt_of_le_of_ne hp (Ne.symm h1))
      simpa using this
    have h := meanBall_Lp_before_cutoff_gt_one D hc hε hε1 hq hliminf
    rwa [ENNReal.ofReal_toReal hpt] at h

/-- The paper's display (1.25) on actual normalized convex-interaction
cubes, with the same before/after limits as on mean balls. -/
theorem convexCube_Lp_cutoff
    (D : ∀ n : ℕ, ConvexInteractionCubeData Ω n) {c ε : ℝ}
    (hc : 0 < c) (hε : 0 < ε) (hε1 : ε < 1)
    (hliminf : 0 < liminf (fun n => ENNReal.ofReal (D n).rate) atTop)
    (hsub : (fun n => (D n).rate) =o[atTop] (fun n : ℕ => Real.log (n : ℝ)))
    {p : ℝ≥0∞} (hp : 1 ≤ p) (hpt : p ≠ ⊤) :
    Tendsto (fun n => convexCubeLp (D n) c p ((1 - ε) * criticalTime n (D n).rate)) atTop
      (𝓝 (if p = 1 then 2 else ⊤)) ∧
    Tendsto (fun n => convexCubeLp (D n) c p ((1 + ε) * criticalTime n (D n).rate)) atTop (𝓝 0) := by
  refine ⟨?_, ?_⟩
  · by_cases h1 : p = 1
    · subst h1
      simpa using convexCube_Lp_one_before_cutoff D hc hε hε1 hliminf
    · simp only [h1, ↓reduceIte]
      have hq : 1 < p.toReal := by
        have := (ENNReal.toReal_lt_toReal ENNReal.one_ne_top hpt).mpr (lt_of_le_of_ne hp (Ne.symm h1))
        simpa using this
      have h := convexCube_Lp_before_cutoff_gt_one D hc hε hε1 hq hliminf
      rwa [ENNReal.ofReal_toReal hpt] at h
  · exact tendsto_of_tendsto_of_tendsto_of_le_of_le'
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0:ENNReal)) atTop (𝓝 0))
      (meanBall_Lp_after_cutoff_of_ne_top (fun n => cubeSpectralData (D n)) hc.le hε hsub hpt)
      (Eventually.of_forall (fun n => bot_le))
      (Eventually.of_forall (fun n => spectralSetLp_mono_set (cubeSpectralData (D n))
        (closedCoordinateCube_subset_ball _ hc.le) p _))

end CutoffRigidity
