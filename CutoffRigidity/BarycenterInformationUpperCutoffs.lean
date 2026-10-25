module
public import CutoffRigidity.BarycenterFisherLowerCutoffs
public import CutoffRigidity.SublogarithmicRates
public import CutoffRigidity.Pinsker
public import CutoffRigidity.LangevinEntropyFinite
public import CutoffRigidity.LangevinInformationUpperBounds

/-! # The source information upper cutoffs on actual mean-centered sets

The fixed time-one/time-two regularization shifts in the written proof
are absorbed by the actual sublogarithmic curvature assumption. Initial
costs use the actual Gibbs barycenter and actual variance bound.
-/
public section
namespace CutoffRigidity
open MeasureTheory ProbabilityTheory InformationTheory Filter Set
open scoped Topology ENNReal NNReal
variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

/-- Actual initial Dirac transport cost on a source Gibbs-mean ball. -/
theorem spectral_mean_ball_initial_transport_bound
    (D : SpectralInformationLowerData Ω d) (hd : 0 < d)
    {c : ℝ} (hc : 0 ≤ c) (x : E)
    (hx : x ∈ Metric.closedBall (∫ y, y ∂gibbsMeasure volume D.potential) (c * Real.sqrt d)) :
    squaredWasserstein (Measure.dirac x) (gibbsMeasure volume D.potential) ≤
      ENNReal.ofReal ((c ^ 2 + D.rate⁻¹) * d) := by
  let := D.probability
  have hlp := gibbs_memLp_two_id_of_hessian_bound D.smooth D.rate D.rate_pos D.hessian
  have hvar := gibbs_variance_le_dim_div_gap D.smooth D.probability hd D.rate D.rate_pos D.hessian
  rw [D.spectral hd] at hvar
  rw [squaredWasserstein_dirac_eq_ofReal _ hlp, second_moment_about_mean _ hlp]
  apply ENNReal.ofReal_le_ofReal
  have hxNorm : ‖x - ∫ y, y ∂gibbsMeasure volume D.potential‖ ≤ c * Real.sqrt d :=
    (Metric.mem_closedBall.mp hx)
  have hxSq := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hc (Real.sqrt_nonneg (d : ℝ)))).mpr hxNorm
  rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg d)] at hxSq
  rw [div_eq_mul_inv] at hvar
  nlinarith only [hxSq, hvar]

/-- A genuine TV set profile is nonnegative whenever its initial set is
nonempty; the supremum uses the actual probability distance. -/
theorem projectedSetTV_nonneg (D : AffineProjectedCutoffData Ω d)
    {S : Set E} (hS : S.Nonempty) (t : ℝ) : 0 ≤ projectedSetTV D S t := by
  let := D.probability
  let := langevinKernel_isMarkovKernel D.brownian D.smooth D.curvature D.curvature_nonneg D.hessian t.toNNReal
  obtain ⟨x, hx⟩ := hS
  exact (totalVariationDistance_nonneg _ _).trans
    (le_csSup (projectedSetTV_bddAbove D S t) ⟨x, hx, rfl⟩)

/-- Actual Pinsker transfers an extended finite set entropy bound to the
actual TV supremum, including a supremum that is not attained. -/
theorem projectedSetTV_le_sqrt_KL (D : AffineProjectedCutoffData Ω d)
    {S : Set E} (hS : S.Nonempty) (t : ℝ) (hFin : projectedSetKL D S t ≠ ⊤) :
    projectedSetTV D S t ≤ Real.sqrt ((projectedSetKL D S t).toReal / 2) := by
  let := D.probability
  let := langevinKernel_isMarkovKernel D.brownian D.smooth D.curvature D.curvature_nonneg D.hessian t.toNNReal
  apply csSup_le (hS.image _)
  rintro _ ⟨x, hx, rfl⟩
  have hle : klDiv (langevinKernel D.potential D.driver D.noiseLaw t.toNNReal x)
      (gibbsMeasure volume D.potential) ≤ projectedSetKL D S t :=
    le_iSup (fun y : S => klDiv (langevinKernel D.potential D.driver D.noiseLaw t.toNNReal y)
      (gibbsMeasure volume D.potential)) ⟨x, hx⟩
  have hKL := ne_top_of_le_ne_top hFin hle
  have hpinsker := totalVariationDistance_sq_le_klDiv_toReal
    (langevinKernel D.potential D.driver D.noiseLaw t.toNNReal x) (gibbsMeasure volume D.potential) hKL
  have hleR := ENNReal.toReal_mono hFin hle
  apply (sq_le_sq₀ (totalVariationDistance_nonneg _ _) (Real.sqrt_nonneg _)).mp
  rw [Real.sq_sqrt (div_nonneg ENNReal.toReal_nonneg (by norm_num))]
  linarith

/-- Scalar absorption of the written fixed regularization shift. The
actual-measure upper profiles are instantiated below, not assumed as
source inequalities. -/
theorem shifted_information_upper_cutoff
    (rate : ℕ → ℝ) (hRate : ∀ n, 0 < rate n) (H : ℕ → ENNReal)
    {c ε shift : ℝ} (hε : 0 < ε) (hshift : 0 ≤ shift)
    (hpositive : ∃ r : ℝ, 0 < r ∧ ∀ᶠ n in atTop, r ≤ rate n)
    (hsub : Tendsto (fun n : ℕ => rate n / Real.log (n : ℝ)) atTop (𝓝 0))
    (hUpper : ∀ᶠ n in atTop, H n ≤ ENNReal.ofReal
      (((c ^ 2 + (rate n)⁻¹) / 2) * ((n : ℝ) * Real.exp
        (-2 * rate n * ((1 + ε) * criticalTime n (rate n) - shift))))) :
    Tendsto H atTop (𝓝 0) := by
  obtain ⟨r, hr, hRateLower⟩ := hpositive
  have hscale := shifted_dimension_decay_tendsto_zero
    (Filter.Eventually.of_forall hRate) hε hshift hsub
  have hbound : ∀ᶠ n in atTop, H n ≤ ENNReal.ofReal
      (((c ^ 2 + r⁻¹) / 2) * ((n : ℝ) * Real.exp
        (-2 * rate n * ((1 + ε) * criticalTime n (rate n) - shift)))) := by
    filter_upwards [hRateLower, hUpper] with n hn hH
    apply hH.trans
    apply ENNReal.ofReal_le_ofReal
    gcongr
  have hlim := ENNReal.continuous_ofReal.continuousAt.tendsto.comp (hscale.const_mul ((c ^ 2 + r⁻¹) / 2))
  simp only [mul_zero, ENNReal.ofReal_zero, Function.comp_def] at hlim
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ENNReal)) atTop (𝓝 0)) hlim
    (Filter.Eventually.of_forall fun n => (bot_le : (0 : ENNReal) ≤ H n)) hbound

/-- Actual Pinsker passes vanishing set KL to vanishing set TV. -/
theorem projectedSetTV_tendsto_zero_of_KL
    (D : ∀ n : ℕ, AffineProjectedCutoffData Ω n)
    (S : ∀ n : ℕ, Set (EuclideanSpace ℝ (Fin n)))
    (hS : ∀ n, (S n).Nonempty) (t : ℕ → ℝ)
    (hKL : Tendsto (fun n => projectedSetKL (D n) (S n) (t n)) atTop (𝓝 0)) :
    Tendsto (fun n => projectedSetTV (D n) (S n) (t n)) atTop (𝓝 0) := by
  have hfinite : ∀ᶠ n in atTop, projectedSetKL (D n) (S n) (t n) ≠ ⊤ := by
    have he := hKL.eventually (eventually_lt_nhds (by norm_num : (0 : ENNReal) < 1))
    exact he.mono (fun n hn => ne_top_of_lt hn)
  have hreal := (ENNReal.continuousAt_toReal (by simp : (0 : ENNReal) ≠ ⊤)).tendsto.comp hKL
  have hsqrt := (hreal.div_const 2).sqrt
  simp only [ENNReal.toReal_zero, zero_div, Real.sqrt_zero, Function.comp_def] at hsqrt
  apply squeeze_zero' (Filter.Eventually.of_forall (fun n => projectedSetTV_nonneg (D n) (hS n) (t n))) _ hsqrt
  filter_upwards [hfinite] with n hn
  exact projectedSetTV_le_sqrt_KL (D n) (hS n) (t n) hn


/-- The actual written entropy transport estimate passes to genuine set
suprema, with no information estimate included in the source data. -/
theorem spectralSetKL_upper_of_initial_transport
    (D : SpectralInformationLowerData Ω d) (hd : 0 < d) (S : Set E) (B : ℝ)
    (hCost : ∀ x ∈ S, squaredWasserstein (Measure.dirac x) (gibbsMeasure volume D.potential) ≤ ENNReal.ofReal B)
    {t : ℝ} (ht : 1 ≤ t) :
    projectedSetKL (spectralInformationToAffine D) S t ≤
      ENNReal.ofReal (Real.exp (-2 * D.rate * (t - 1)) / 2 * B) := by
  let := D.probability
  apply iSup_le
  intro x
  have hh := klDiv_langevinKernel_le_exp_transport D.brownian D.smooth D.probability hd D.rate D.rate_pos D.hessian
    (Measure.dirac (x : E)) t.toNNReal (by exact_mod_cast (show (1 : ℝ) ≤ (t.toNNReal : ℝ) by
      rw [Real.coe_toNNReal _ (by linarith : 0 ≤ t)]; exact ht))
  rw [langevinKernel_comp_dirac, Real.coe_toNNReal _ (by linarith : 0 ≤ t)] at hh
  apply hh.trans
  rw [ENNReal.ofReal_mul (by positivity : 0 ≤ Real.exp (-2 * D.rate * (t - 1)) / 2)]
  exact mul_le_mul' le_rfl (hCost x x.property)

/-- The source Fisher time-two estimate passes to the canonical extended
Fisher profile on any actual set. -/
theorem spectralSetFisher_upper_of_initial_transport
    (D : SpectralInformationLowerData Ω d) (S : Set E) (B : ℝ)
    (hCost : ∀ x ∈ S, squaredWasserstein (Measure.dirac x) (gibbsMeasure volume D.potential) ≤ ENNReal.ofReal B)
    {t : ℝ} (ht : 2 ≤ t) :
    spectralSetFisher D S t ≤ ENNReal.ofReal (Real.exp (-2 * D.rate * (t - 2)) / 2 * B) := by
  let := D.probability
  let := langevinKernel_isMarkovKernel D.brownian D.smooth D.rate D.rate_pos.le D.hessian t.toNNReal
  apply iSup_le
  intro x
  have hh := relativeFisherInformation_langevinKernel_le_exp_transport D.brownian D.smooth D.probability
    D.rate D.rate_pos D.hessian (Measure.dirac (x : E)) t.toNNReal
    (by exact_mod_cast (show (2 : ℝ) ≤ (t.toNNReal : ℝ) by
      rw [Real.coe_toNNReal _ (by linarith : 0 ≤ t)]; exact ht))
  simp only [langevinKernel_comp_dirac, Real.coe_toNNReal _ (by linarith : 0 ≤ t)] at hh
  apply hh.trans
  rw [ENNReal.ofReal_mul (by positivity : 0 ≤ Real.exp (-2 * D.rate * (t - 2)) / 2)]
  exact mul_le_mul' le_rfl (hCost x x.property)

theorem meanBallKL_upper (D : SpectralInformationLowerData Ω d) (hd : 0 < d)
    {c t : ℝ} (hc : 0 ≤ c) (ht : 1 ≤ t) :
    meanBallKL D c t ≤ ENNReal.ofReal (((c ^ 2 + D.rate⁻¹) / 2) *
      ((d : ℝ) * Real.exp (-2 * D.rate * (t - 1)))) := by
  have hh := spectralSetKL_upper_of_initial_transport D hd _ ((c ^ 2 + D.rate⁻¹) * d)
    (fun x hx => spectral_mean_ball_initial_transport_bound D hd hc x hx) ht
  change meanBallKL D c t ≤ _ at hh
  convert hh using 1
  congr 1
  ring

theorem meanBallFisher_upper (D : SpectralInformationLowerData Ω d) (hd : 0 < d)
    {c t : ℝ} (hc : 0 ≤ c) (ht : 2 ≤ t) :
    meanBallFisher D c t ≤ ENNReal.ofReal (((c ^ 2 + D.rate⁻¹) / 2) *
      ((d : ℝ) * Real.exp (-2 * D.rate * (t - 2)))) := by
  have hh := spectralSetFisher_upper_of_initial_transport D _ ((c ^ 2 + D.rate⁻¹) * d)
    (fun x hx => spectral_mean_ball_initial_transport_bound D hd hc x hx) ht
  change meanBallFisher D c t ≤ _ at hh
  convert hh using 1
  congr 1
  ring

theorem convexCubeKL_upper (D : ConvexInteractionCubeData Ω d) (hd : 0 < d)
    {c t : ℝ} (hc : 0 ≤ c) (ht : 1 ≤ t) :
    convexCubeKL D c t ≤ ENNReal.ofReal (((c ^ 2 + D.rate⁻¹) / 2) *
      ((d : ℝ) * Real.exp (-2 * D.rate * (t - 1)))) := by
  have hh := spectralSetKL_upper_of_initial_transport (cubeSpectralData D) hd _ ((c ^ 2 + D.rate⁻¹) * d)
    (fun x hx => spectral_mean_ball_initial_transport_bound (cubeSpectralData D) hd hc x
      (closedCoordinateCube_subset_ball _ hc hx)) ht
  change convexCubeKL D c t ≤ ENNReal.ofReal
    (Real.exp (-2 * D.rate * (t - 1)) / 2 * ((c ^ 2 + D.rate⁻¹) * d)) at hh
  convert hh using 1
  congr 1
  ring

theorem convexCubeFisher_upper (D : ConvexInteractionCubeData Ω d) (hd : 0 < d)
    {c t : ℝ} (hc : 0 ≤ c) (ht : 2 ≤ t) :
    convexCubeFisher D c t ≤ ENNReal.ofReal (((c ^ 2 + D.rate⁻¹) / 2) *
      ((d : ℝ) * Real.exp (-2 * D.rate * (t - 2)))) := by
  have hh := spectralSetFisher_upper_of_initial_transport (cubeSpectralData D) _ ((c ^ 2 + D.rate⁻¹) * d)
    (fun x hx => spectral_mean_ball_initial_transport_bound (cubeSpectralData D) hd hc x
      (closedCoordinateCube_subset_ball _ hc hx)) ht
  change convexCubeFisher D c t ≤ ENNReal.ofReal
    (Real.exp (-2 * D.rate * (t - 2)) / 2 * ((c ^ 2 + D.rate⁻¹) * d)) at hh
  convert hh using 1
  congr 1
  ring

/-- The exact source mean-ball entropy after-cutoff conclusion. The
sublogarithmic assumption is used for the written time-one shift. -/
theorem meanBall_entropy_after_cutoff
    (D : ∀ n : ℕ, SpectralInformationLowerData Ω n) {c ε : ℝ}
    (hc : 0 ≤ c) (hε : 0 < ε)
    (hliminf : 0 < liminf (fun n => ENNReal.ofReal (D n).rate) atTop)
    (hsub : Tendsto (fun n : ℕ => (D n).rate / Real.log (n : ℝ)) atTop (𝓝 0)) :
    Tendsto (fun n => meanBallKL (D n) c ((1 + ε) * criticalTime n (D n).rate)) atTop (𝓝 0) := by
  have htime := (criticalTime_tendsto_atTop_of_sublogarithmic
    (Filter.Eventually.of_forall (fun n => (D n).rate_pos)) hsub).const_mul_atTop (by linarith : 0 < 1 + ε)
  apply shifted_information_upper_cutoff (fun n => (D n).rate) (fun n => (D n).rate_pos) _ hε
    (by norm_num : (0 : ℝ) ≤ 1) (spectralInformation_rates_eventually_positive_lower D hliminf) hsub
  filter_upwards [htime.eventually_ge_atTop 1, eventually_ge_atTop 1] with n ht hn
  exact meanBallKL_upper (D n) (by omega) hc ht

/-- The written time-two Fisher estimate yields the actual mean-ball
canonical Fisher after-cutoff conclusion. -/
theorem meanBallFisher_after_cutoff
    (D : ∀ n : ℕ, SpectralInformationLowerData Ω n) {c ε : ℝ}
    (hc : 0 ≤ c) (hε : 0 < ε)
    (hliminf : 0 < liminf (fun n => ENNReal.ofReal (D n).rate) atTop)
    (hsub : Tendsto (fun n : ℕ => (D n).rate / Real.log (n : ℝ)) atTop (𝓝 0)) :
    Tendsto (fun n => meanBallFisher (D n) c ((1 + ε) * criticalTime n (D n).rate)) atTop (𝓝 0) := by
  have htime := (criticalTime_tendsto_atTop_of_sublogarithmic
    (Filter.Eventually.of_forall (fun n => (D n).rate_pos)) hsub).const_mul_atTop (by linarith : 0 < 1 + ε)
  apply shifted_information_upper_cutoff (fun n => (D n).rate) (fun n => (D n).rate_pos) _ hε
    (by norm_num : (0 : ℝ) ≤ 2) (spectralInformation_rates_eventually_positive_lower D hliminf) hsub
  filter_upwards [htime.eventually_ge_atTop 2, eventually_ge_atTop 1] with n ht hn
  exact meanBallFisher_upper (D n) (by omega) hc ht

/-- Actual TV vanishes on the source mean balls by genuine Pinsker. -/
theorem meanBall_totalVariation_after_cutoff
    (D : ∀ n : ℕ, SpectralInformationLowerData Ω n) {c ε : ℝ}
    (hc : 0 ≤ c) (hε : 0 < ε)
    (hliminf : 0 < liminf (fun n => ENNReal.ofReal (D n).rate) atTop)
    (hsub : Tendsto (fun n : ℕ => (D n).rate / Real.log (n : ℝ)) atTop (𝓝 0)) :
    Tendsto (fun n => meanBallTV (D n) c ((1 + ε) * criticalTime n (D n).rate)) atTop (𝓝 0) := by
  apply projectedSetTV_tendsto_zero_of_KL (fun n => spectralInformationToAffine (D n))
    (fun n => Metric.closedBall (∫ y, y ∂gibbsMeasure volume (D n).potential) (c * Real.sqrt n))
    (fun n => ⟨∫ y, y ∂gibbsMeasure volume (D n).potential, by
      rw [Metric.mem_closedBall, dist_self]
      exact mul_nonneg hc (Real.sqrt_nonneg (n : ℝ))⟩)
    (fun n => (1 + ε) * criticalTime n (D n).rate)
  exact meanBall_entropy_after_cutoff D hc hε hliminf hsub

theorem convexCube_entropy_after_cutoff
    (D : ∀ n : ℕ, ConvexInteractionCubeData Ω n) {c ε : ℝ}
    (hc : 0 ≤ c) (hε : 0 < ε)
    (hliminf : 0 < liminf (fun n => ENNReal.ofReal (D n).rate) atTop)
    (hsub : Tendsto (fun n : ℕ => (D n).rate / Real.log (n : ℝ)) atTop (𝓝 0)) :
    Tendsto (fun n => convexCubeKL (D n) c ((1 + ε) * criticalTime n (D n).rate)) atTop (𝓝 0) := by
  have htime := (criticalTime_tendsto_atTop_of_sublogarithmic
    (Filter.Eventually.of_forall (fun n => (D n).rate_pos)) hsub).const_mul_atTop (by linarith : 0 < 1 + ε)
  apply shifted_information_upper_cutoff (fun n => (D n).rate) (fun n => (D n).rate_pos) _ hε
    (by norm_num : (0 : ℝ) ≤ 1)
    (spectralInformation_rates_eventually_positive_lower (fun n => cubeSpectralData (D n)) hliminf) hsub
  filter_upwards [htime.eventually_ge_atTop 1, eventually_ge_atTop 1] with n ht hn
  exact convexCubeKL_upper (D n) (by omega) hc ht

theorem convexCubeFisher_after_cutoff
    (D : ∀ n : ℕ, ConvexInteractionCubeData Ω n) {c ε : ℝ}
    (hc : 0 ≤ c) (hε : 0 < ε)
    (hliminf : 0 < liminf (fun n => ENNReal.ofReal (D n).rate) atTop)
    (hsub : Tendsto (fun n : ℕ => (D n).rate / Real.log (n : ℝ)) atTop (𝓝 0)) :
    Tendsto (fun n => convexCubeFisher (D n) c ((1 + ε) * criticalTime n (D n).rate)) atTop (𝓝 0) := by
  have htime := (criticalTime_tendsto_atTop_of_sublogarithmic
    (Filter.Eventually.of_forall (fun n => (D n).rate_pos)) hsub).const_mul_atTop (by linarith : 0 < 1 + ε)
  apply shifted_information_upper_cutoff (fun n => (D n).rate) (fun n => (D n).rate_pos) _ hε
    (by norm_num : (0 : ℝ) ≤ 2)
    (spectralInformation_rates_eventually_positive_lower (fun n => cubeSpectralData (D n)) hliminf) hsub
  filter_upwards [htime.eventually_ge_atTop 2, eventually_ge_atTop 1] with n ht hn
  exact convexCubeFisher_upper (D n) (by omega) hc ht

theorem convexCube_totalVariation_after_cutoff
    (D : ∀ n : ℕ, ConvexInteractionCubeData Ω n) {c ε : ℝ}
    (hc : 0 ≤ c) (hε : 0 < ε)
    (hliminf : 0 < liminf (fun n => ENNReal.ofReal (D n).rate) atTop)
    (hsub : Tendsto (fun n : ℕ => (D n).rate / Real.log (n : ℝ)) atTop (𝓝 0)) :
    Tendsto (fun n => convexCubeTV (D n) c ((1 + ε) * criticalTime n (D n).rate)) atTop (𝓝 0) := by
  apply projectedSetTV_tendsto_zero_of_KL (fun n => spectralInformationToAffine (cubeSpectralData (D n)))
    (fun n => closedCoordinateCube (∫ y, y ∂gibbsMeasure volume (cubeSpectralData (D n)).potential) c)
    (fun n => ⟨∫ y, y ∂gibbsMeasure volume (cubeSpectralData (D n)).potential, fun i => by simp [hc]⟩) (fun n => (1 + ε) * criticalTime n (D n).rate)
  exact convexCube_entropy_after_cutoff D hc hε hliminf hsub


/-- The source entropy, total-variation and Fisher cutoffs on balls about
actual Gibbs means, with the paper's literal sublogarithmic hypothesis.
All probability, spectral projection and functional bounds are derived. -/
theorem meanBall_information_cutoff
    (D : ∀ n : ℕ, SpectralInformationLowerData Ω n) {c ε : ℝ}
    (hc : 0 < c) (hε : 0 < ε) (hε1 : ε < 1)
    (hliminf : 0 < liminf (fun n => ENNReal.ofReal (D n).rate) atTop)
    (hsub : (fun n => (D n).rate) =o[atTop] (fun n : ℕ => Real.log (n : ℝ))) :
    Tendsto (fun n => meanBallKL (D n) c ((1 - ε) * criticalTime n (D n).rate)) atTop (𝓝 ⊤) ∧
    Tendsto (fun n => meanBallKL (D n) c ((1 + ε) * criticalTime n (D n).rate)) atTop (𝓝 0) ∧
    Tendsto (fun n => meanBallTV (D n) c ((1 - ε) * criticalTime n (D n).rate)) atTop (𝓝 1) ∧
    Tendsto (fun n => meanBallTV (D n) c ((1 + ε) * criticalTime n (D n).rate)) atTop (𝓝 0) ∧
    Tendsto (fun n => meanBallFisher (D n) c ((1 - ε) * criticalTime n (D n).rate)) atTop (𝓝 ⊤) ∧
    Tendsto (fun n => meanBallFisher (D n) c ((1 + ε) * criticalTime n (D n).rate)) atTop (𝓝 0) :=
  ⟨meanBall_entropy_before_cutoff D hc hε hε1 hliminf,
    meanBall_entropy_after_cutoff D hc.le hε hliminf hsub.tendsto_div_nhds_zero,
    meanBall_totalVariation_before_cutoff D hc hε hε1 hliminf,
    meanBall_totalVariation_after_cutoff D hc.le hε hliminf hsub.tendsto_div_nhds_zero,
    meanBallFisher_before_cutoff D hc hε hε1 hliminf,
    meanBallFisher_after_cutoff D hc.le hε hliminf hsub.tendsto_div_nhds_zero⟩

/-- The source normalized convex-interaction cube information cutoffs.
Probability, actual spectral gap and diagonal Gaussian projection are
constructed internally from the convex interaction and Brownian driver. -/
theorem convexCube_information_cutoff
    (D : ∀ n : ℕ, ConvexInteractionCubeData Ω n) {c ε : ℝ}
    (hc : 0 < c) (hε : 0 < ε) (hε1 : ε < 1)
    (hliminf : 0 < liminf (fun n => ENNReal.ofReal (D n).rate) atTop)
    (hsub : (fun n => (D n).rate) =o[atTop] (fun n : ℕ => Real.log (n : ℝ))) :
    Tendsto (fun n => convexCubeKL (D n) c ((1 - ε) * criticalTime n (D n).rate)) atTop (𝓝 ⊤) ∧
    Tendsto (fun n => convexCubeKL (D n) c ((1 + ε) * criticalTime n (D n).rate)) atTop (𝓝 0) ∧
    Tendsto (fun n => convexCubeTV (D n) c ((1 - ε) * criticalTime n (D n).rate)) atTop (𝓝 1) ∧
    Tendsto (fun n => convexCubeTV (D n) c ((1 + ε) * criticalTime n (D n).rate)) atTop (𝓝 0) ∧
    Tendsto (fun n => convexCubeFisher (D n) c ((1 - ε) * criticalTime n (D n).rate)) atTop (𝓝 ⊤) ∧
    Tendsto (fun n => convexCubeFisher (D n) c ((1 + ε) * criticalTime n (D n).rate)) atTop (𝓝 0) :=
  ⟨convexCube_entropy_before_cutoff D hc hε hε1 hliminf,
    convexCube_entropy_after_cutoff D hc.le hε hliminf hsub.tendsto_div_nhds_zero,
    convexCube_totalVariation_before_cutoff D hc hε hε1 hliminf,
    convexCube_totalVariation_after_cutoff D hc.le hε hliminf hsub.tendsto_div_nhds_zero,
    convexCubeFisher_before_cutoff D hc hε hε1 hliminf,
    convexCubeFisher_after_cutoff D hc.le hε hliminf hsub.tendsto_div_nhds_zero⟩

end CutoffRigidity
