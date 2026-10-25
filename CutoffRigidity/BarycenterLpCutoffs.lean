module
public import CutoffRigidity.LangevinChiSquareBound
public import CutoffRigidity.LpCutoffScale
public import CutoffRigidity.BarycenterInformationUpperCutoffs

/-! # Actual relative Lᵖ profiles on the source mean balls and cubes -/
public section
namespace CutoffRigidity
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal NNReal
variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

@[expose] noncomputable def spectralSetLp (D : SpectralInformationLowerData Ω d)
    (S : Set E) (p : ENNReal) (t : ℝ) : ENNReal :=
  ⨆ x : S, relativeLpDistance (langevinKernel D.potential D.driver D.noiseLaw t.toNNReal x)
    (gibbsMeasure volume D.potential) p

@[expose] noncomputable def meanBallLp (D : SpectralInformationLowerData Ω d)
    (c : ℝ) (p : ENNReal) (t : ℝ) : ENNReal := spectralSetLp D
      (Metric.closedBall (∫ y, y ∂gibbsMeasure volume D.potential) (c*Real.sqrt d)) p t

@[expose] noncomputable def convexCubeLp (D : ConvexInteractionCubeData Ω d)
    (c : ℝ) (p : ENNReal) (t : ℝ) : ENNReal := spectralSetLp (cubeSpectralData D)
      (closedCoordinateCube (∫ y, y ∂gibbsMeasure volume (cubeSpectralData D).potential) c) p t

/-- Exponent monotonicity is applied to actual density errors. -/
theorem spectralSetLp_mono (D : SpectralInformationLowerData Ω d)
    (S : Set E) {p q : ENNReal} (hpq : p ≤ q) (t : ℝ) :
    spectralSetLp D S p t ≤ spectralSetLp D S q t := by
  let := D.probability
  exact iSup_mono fun x => relativeLpDistance_mono _ _ hpq

/-- An actual entropy profile is below the square of the L²-error profile. -/
theorem projectedSetKL_le_spectralSetLp_two_sq
    (D : SpectralInformationLowerData Ω d) (S : Set E) (t : ℝ) :
    projectedSetKL (spectralInformationToAffine D) S t ≤ spectralSetLp D S 2 t ^ 2 := by
  let := D.probability
  let := langevinKernel_isMarkovKernel D.brownian D.smooth D.rate D.rate_pos.le D.hessian t.toNNReal
  apply iSup_le
  intro x
  change InformationTheory.klDiv (langevinKernel D.potential D.driver D.noiseLaw t.toNNReal x) (gibbsMeasure volume D.potential) ≤ _
  exact (klDiv_le_relativeLpDistance_two_sq _ _).trans
    (ENNReal.pow_le_pow_left (le_iSup (fun y : S => relativeLpDistance
      (langevinKernel D.potential D.driver D.noiseLaw t.toNNReal y) (gibbsMeasure volume D.potential) 2) x))

/-- The Harnack bound gives a genuine uniform density-error bound on an
actual source mean ball, including the actual variance contribution. -/
theorem meanBallLp_two_sq_upper (D : SpectralInformationLowerData Ω d)
    (hd : 0 < d) {c : ℝ} (hc : 0 ≤ c) {t : ℝ} (ht : 0 < t) :
    meanBallLp D c 2 t ^ 2 ≤ ENNReal.ofReal (Real.exp
      (D.rate / (Real.exp (2*D.rate*t)-1) * ((c^2+D.rate⁻¹)*d)) - 1) := by
  let := D.probability
  have hr := D.rate_pos
  let S := Metric.closedBall (∫ y, y ∂gibbsMeasure volume D.potential) (c*Real.sqrt d)
  have hS : Nonempty S := ⟨⟨_, Metric.mem_closedBall_self (by positivity)⟩⟩
  let := hS
  rw [meanBallLp, spectralSetLp, ENNReal.iSup_pow]
  apply iSup_le
  intro x
  apply (relativeLpDistance_two_sq_langevinKernel_le_exp_moment D.brownian D.smooth D.probability
    D.rate D.rate_pos D.hessian t ht x).trans
  apply ENNReal.ofReal_le_ofReal
  apply sub_le_sub_right
  apply Real.exp_le_exp.mpr
  have ha : 0 ≤ D.rate/(Real.exp (2*D.rate*t)-1) :=
    (div_pos D.rate_pos (sub_pos.mpr (Real.one_lt_exp_iff.mpr (by positivity)))).le
  apply mul_le_mul_of_nonneg_left _ ha
  have hcost := spectral_mean_ball_initial_transport_bound D hd hc x x.property
  rw [squaredWasserstein_dirac_eq_ofReal _ (gibbs_memLp_two_id_of_hessian_bound
    D.smooth D.rate D.rate_pos D.hessian)] at hcost
  have hreal := (ENNReal.ofReal_le_ofReal_iff (by positivity : 0 ≤ (c^2+D.rate⁻¹)*(d:ℝ))).mp hcost
  calc
    _ = ∫ y, ‖y-(x:E)‖^2 ∂gibbsMeasure volume D.potential := by simp only [norm_sub_rev]
    _ ≤ _ := hreal

/-- Squared extended norms determine their actual convergence, with
infinite limits included. -/
theorem tendsto_ennreal_of_sq_tendsto {u : ℕ → ENNReal} {L : ENNReal}
    (h : Tendsto (fun n => u n ^ 2) atTop (𝓝 (L^2))) :
    Tendsto u atTop (𝓝 L) := by
  have hh := (ENNReal.continuous_rpow_const (y := (1/2:ℝ))).continuousAt.tendsto.comp h
  have he (v : ENNReal) : (v^2)^((1/2):ℝ) = v := by
    rw [← ENNReal.rpow_natCast_mul]
    norm_num
  simpa only [Function.comp_def, he] using hh

/-- The actual mean-ball L² density distance vanishes after the source
critical time. No Lᵖ estimate is included in the source data. -/
theorem meanBall_L2_after_cutoff
    (D : ∀ n : ℕ, SpectralInformationLowerData Ω n) {c ε : ℝ}
    (hc : 0 ≤ c) (hε : 0 < ε)
    (hsub : (fun n => (D n).rate) =o[atTop] (fun n : ℕ => Real.log (n:ℝ))) :
    Tendsto (fun n : ℕ => meanBallLp (D n) c 2
      ((1+ε)*criticalTime n (D n).rate)) atTop (𝓝 0) := by
  have he := chiSquare_exponent_tendsto_zero (fun n => (D n).rate)
    (fun n => (D n).rate_pos) c hε hsub.tendsto_div_nhds_zero
  have hlim := ENNReal.continuous_ofReal.continuousAt.tendsto.comp
    ((Real.continuous_exp.continuousAt.tendsto.comp he).sub_const 1)
  simp only [Real.exp_zero, sub_self, ENNReal.ofReal_zero, Function.comp_def] at hlim
  apply tendsto_ennreal_of_sq_tendsto (L := 0)
  simp only [zero_pow (by decide : 2 ≠ 0)]
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0:ENNReal)) atTop (𝓝 0)) hlim
    (Eventually.of_forall (fun n => bot_le))
  filter_upwards [eventually_ge_atTop 2] with n hn
  have hnpos : 0 < n := by omega
  have hlog : 0 < Real.log (n:ℝ) := Real.log_pos (by exact_mod_cast (show 1<n by omega))
  have hr := (D n).rate_pos
  apply meanBallLp_two_sq_upper (D n) hnpos hc
  unfold criticalTime
  positivity

/-- Monotonicity of actual probability Lᵖ norms gives every exponent
between one and two (indeed every p≤2) from the derived L² upper bound. -/
theorem meanBall_Lp_after_cutoff_le_two
    (D : ∀ n : ℕ, SpectralInformationLowerData Ω n) {c ε : ℝ}
    (hc : 0 ≤ c) (hε : 0 < ε)
    (hsub : (fun n => (D n).rate) =o[atTop] (fun n : ℕ => Real.log (n:ℝ)))
    {p : ENNReal} (hp : p ≤ 2) :
    Tendsto (fun n : ℕ => meanBallLp (D n) c p
      ((1+ε)*criticalTime n (D n).rate)) atTop (𝓝 0) := by
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0:ENNReal)) atTop (𝓝 0))
    (meanBall_L2_after_cutoff D hc hε hsub)
    (Eventually.of_forall (fun n => bot_le))
    (Eventually.of_forall (fun n => spectralSetLp_mono (D n) _ hp _))

/-- Entropy divergence forces genuine L² divergence before cutoff. -/
theorem meanBall_L2_before_cutoff
    (D : ∀ n : ℕ, SpectralInformationLowerData Ω n) {c ε : ℝ}
    (hc : 0 < c) (hε : 0 < ε) (hε1 : ε < 1)
    (hliminf : 0 < liminf (fun n => ENNReal.ofReal (D n).rate) atTop) :
    Tendsto (fun n : ℕ => meanBallLp (D n) c 2
      ((1-ε)*criticalTime n (D n).rate)) atTop (𝓝 ⊤) := by
  apply tendsto_ennreal_of_sq_tendsto (L := ⊤)
  simp only [ENNReal.top_pow (by decide : 2 ≠ 0)]
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (meanBall_entropy_before_cutoff D hc hε hε1 hliminf) tendsto_const_nhds
    (Eventually.of_forall (fun n => projectedSetKL_le_spectralSetLp_two_sq (D n) _ _))
    (Eventually.of_forall (fun _n => le_top))

/-- Restriction to an initial subset decreases the genuine Lᵖ profile. -/
theorem spectralSetLp_mono_set (D : SpectralInformationLowerData Ω d)
    {S R : Set E} (hSR : S ⊆ R) (p : ENNReal) (t : ℝ) :
    spectralSetLp D S p t ≤ spectralSetLp D R p t := by
  apply iSup_le
  intro x
  exact le_iSup_of_le ⟨x,hSR x.property⟩ le_rfl

/-- The cube upper cutoff follows from its actual containment in the
mean ball; its lower cutoff below uses the true diagonal eigenfunction. -/
theorem convexCube_Lp_after_cutoff_le_two
    (D : ∀ n : ℕ, ConvexInteractionCubeData Ω n) {c ε : ℝ}
    (hc : 0 ≤ c) (hε : 0 < ε)
    (hsub : (fun n => (D n).rate) =o[atTop] (fun n : ℕ => Real.log (n:ℝ)))
    {p : ENNReal} (hp : p ≤ 2) :
    Tendsto (fun n : ℕ => convexCubeLp (D n) c p
      ((1+ε)*criticalTime n (D n).rate)) atTop (𝓝 0) := by
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0:ENNReal)) atTop (𝓝 0))
    (meanBall_Lp_after_cutoff_le_two (fun n => cubeSpectralData (D n)) hc hε hsub hp)
    (Eventually.of_forall (fun n => bot_le))
    (Eventually.of_forall (fun n => spectralSetLp_mono_set (cubeSpectralData (D n))
      (closedCoordinateCube_subset_ball _ hc) p _))

/-- Genuine cube L² divergence uses the actual diagonal Gaussian lower
bound already derived from the normalized interaction's eigenfunction. -/
theorem convexCube_L2_before_cutoff
    (D : ∀ n : ℕ, ConvexInteractionCubeData Ω n) {c ε : ℝ}
    (hc : 0 < c) (hε : 0 < ε) (hε1 : ε < 1)
    (hliminf : 0 < liminf (fun n => ENNReal.ofReal (D n).rate) atTop) :
    Tendsto (fun n : ℕ => convexCubeLp (D n) c 2
      ((1-ε)*criticalTime n (D n).rate)) atTop (𝓝 ⊤) := by
  apply tendsto_ennreal_of_sq_tendsto (L := ⊤)
  simp only [ENNReal.top_pow (by decide : 2 ≠ 0)]
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (convexCube_entropy_before_cutoff D hc hε hε1 hliminf) tendsto_const_nhds
    (Eventually.of_forall (fun n => projectedSetKL_le_spectralSetLp_two_sq (cubeSpectralData (D n)) _ _))
    (Eventually.of_forall (fun _n => le_top))

/-- Every exponent at least two has the genuine pre-cutoff divergence. -/
theorem meanBall_Lp_before_cutoff_ge_two
    (D : ∀ n : ℕ, SpectralInformationLowerData Ω n) {c ε : ℝ}
    (hc : 0 < c) (hε : 0 < ε) (hε1 : ε < 1)
    (hliminf : 0 < liminf (fun n => ENNReal.ofReal (D n).rate) atTop)
    {p : ENNReal} (hp : 2 ≤ p) :
    Tendsto (fun n : ℕ => meanBallLp (D n) c p
      ((1-ε)*criticalTime n (D n).rate)) atTop (𝓝 ⊤) :=
  tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (meanBall_L2_before_cutoff D hc hε hε1 hliminf) tendsto_const_nhds
    (Eventually.of_forall (fun n => spectralSetLp_mono (D n) _ hp _))
    (Eventually.of_forall (fun _n => le_top))

/-- The same exponent transfer for actual interaction cubes. -/
theorem convexCube_Lp_before_cutoff_ge_two
    (D : ∀ n : ℕ, ConvexInteractionCubeData Ω n) {c ε : ℝ}
    (hc : 0 < c) (hε : 0 < ε) (hε1 : ε < 1)
    (hliminf : 0 < liminf (fun n => ENNReal.ofReal (D n).rate) atTop)
    {p : ENNReal} (hp : 2 ≤ p) :
    Tendsto (fun n : ℕ => convexCubeLp (D n) c p
      ((1-ε)*criticalTime n (D n).rate)) atTop (𝓝 ⊤) :=
  tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (convexCube_L2_before_cutoff D hc hε hε1 hliminf) tendsto_const_nhds
    (Eventually.of_forall (fun n => spectralSetLp_mono (cubeSpectralData (D n)) _ hp _))
    (Eventually.of_forall (fun _n => le_top))

end CutoffRigidity
