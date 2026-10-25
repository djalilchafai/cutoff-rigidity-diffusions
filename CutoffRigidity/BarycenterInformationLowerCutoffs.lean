module
public import CutoffRigidity.ConvexInteractionCubeCutoff

/-! # The actual mean-centered initial sets in the source lower information cutoffs -/
public section
namespace CutoffRigidity
open Set MeasureTheory ProbabilityTheory InformationTheory Filter Topology
open scoped ENNReal NNReal
variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

@[expose] noncomputable def projectedSetKL (D : AffineProjectedCutoffData Ω d) (S : Set E) (t : ℝ) : ℝ≥0∞ :=
  ⨆ x : S, klDiv (langevinKernel D.potential D.driver D.noiseLaw t.toNNReal x) (gibbsMeasure volume D.potential)
@[expose] noncomputable def projectedSetTV (D : AffineProjectedCutoffData Ω d) (S : Set E) (t : ℝ) : ℝ :=
  sSup ((fun x => totalVariationDistance (langevinKernel D.potential D.driver D.noiseLaw t.toNNReal x)
    (gibbsMeasure volume D.potential)) '' S)

theorem projectedSetTV_bddAbove (D : AffineProjectedCutoffData Ω d) (S : Set E) (t : ℝ) :
    BddAbove ((fun x => totalVariationDistance (langevinKernel D.potential D.driver D.noiseLaw t.toNNReal x)
      (gibbsMeasure volume D.potential)) '' S) := by
  let := D.probability
  let := langevinKernel_isMarkovKernel D.brownian D.smooth D.curvature D.curvature_nonneg D.hessian t.toNNReal
  refine ⟨1, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  exact totalVariationDistance_le_one _ _

theorem projectedSetTV_le_one (D : AffineProjectedCutoffData Ω d) {S : Set E} (hS : S.Nonempty) (t : ℝ) :
    projectedSetTV D S t ≤ 1 := by
  apply csSup_le (hS.image _)
  rintro _ ⟨x, hx, rfl⟩
  let := D.probability
  let := langevinKernel_isMarkovKernel D.brownian D.smooth D.curvature D.curvature_nonneg D.hessian t.toNNReal
  exact totalVariationDistance_le_one _ _

theorem projectedSetKL_lower_of_coordinate (D : AffineProjectedCutoffData Ω d) {S : Set E}
    (x : E) (hx : x ∈ S) (j : Fin D.coordinateCount) (L : ℝ)
    (hL : L ≤ (inner ℝ (D.coefficient j) x + D.constant j) ^ 2) {t : ℝ} (ht : 0 < t) :
    ENNReal.ofReal (Real.exp (-2 * D.rate * t) * L / 2) ≤ projectedSetKL D S t := by
  have hnorm : (inner ℝ (D.coefficient j) x + D.constant j) ^ 2 ≤
      ‖affineEigenfunctionMap D.coefficient D.constant x‖ ^ 2 := by
    have hh := sq_le_sq₀ (norm_nonneg ((affineEigenfunctionMap D.coefficient D.constant x) j))
      (norm_nonneg (affineEigenfunctionMap D.coefficient D.constant x)) |>.mpr
        (PiLp.norm_apply_le (affineEigenfunctionMap D.coefficient D.constant x) j)
    simpa only [affineEigenfunctionMap, Real.norm_eq_abs, sq_abs] using hh
  have he := klDiv_langevinKernel_affine_mean_lower D.brownian D.smooth D.curvature D.curvature_nonneg
    D.hessian D.coefficient D.constant D.rate D.rate_pos D.eigenfunction D.probability D.orthonormal x t.toNNReal
    (by simpa only [Real.coe_toNNReal _ ht.le] using ht)
  rw [Real.coe_toNNReal _ ht.le] at he
  apply le_trans _ (he.trans (le_iSup (fun y : S => klDiv
    (langevinKernel D.potential D.driver D.noiseLaw t.toNNReal y) (gibbsMeasure volume D.potential)) ⟨x, hx⟩))
  apply ENNReal.ofReal_le_ofReal
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left (hL.trans hnorm) (Real.exp_pos _).le) (by norm_num)

theorem projectedSetTV_lower_of_coordinate (D : AffineProjectedCutoffData Ω d) {S : Set E}
    (x : E) (hx : x ∈ S) (j : Fin D.coordinateCount)
    (hm : 0 < inner ℝ (D.coefficient j) x + D.constant j) {t : ℝ} (ht : 0 ≤ t) :
    1 - 8 / (Real.exp (-2 * D.rate * t) * (inner ℝ (D.coefficient j) x + D.constant j) ^ 2) ≤
      projectedSetTV D S t := by
  have he := totalVariationDistance_langevinKernel_affine_mean_lower D.brownian D.smooth D.curvature
    D.curvature_nonneg D.hessian D.coefficient D.constant D.rate D.rate_pos D.eigenfunction
    D.probability D.orthonormal x t.toNNReal j hm
  rw [Real.coe_toNNReal _ ht, mul_pow, ← Real.exp_nat_mul] at he
  have hexp : (2 : ℕ) * (-D.rate * t) = -2 * D.rate * t := by push_cast; ring
  rw [hexp] at he
  exact he.trans (le_csSup (projectedSetTV_bddAbove D S t) ⟨x, hx, rfl⟩)

/-- A canonical actual first-eigenfunction row realizes the required
positive Gaussian mean on the sphere about the genuine Gibbs mean. -/
theorem spectralInformation_mean_ball_witness (D : SpectralInformationLowerData Ω d) (hd : 0 < d)
    {c : ℝ} (hc : 0 < c) :
    ∃ (x : E) (j : Fin (Module.finrank ℝ (affineEigenRows D.potential D.rate))),
      x ∈ Metric.closedBall (∫ y, y ∂gibbsMeasure volume D.potential) (c * Real.sqrt d) ∧
      0 < inner ℝ ((spectralInformationToAffine D).coefficient j) x + (spectralInformationToAffine D).constant j ∧
      (inner ℝ ((spectralInformationToAffine D).coefficient j) x + (spectralInformationToAffine D).constant j) ^ 2 =
        D.rate * c ^ 2 * d := by
  let j : Fin (Module.finrank ℝ (affineEigenRows D.potential D.rate)) := ⟨0, spectralInformation_rows_finrank_pos D hd⟩
  let m := ∫ y, y ∂gibbsMeasure volume D.potential
  let R := c * Real.sqrt (d : ℝ)
  let x := m + R • affineEigenBasisRows D.potential D.rate j
  have hR : 0 < R := mul_pos hc (Real.sqrt_pos.mpr (Nat.cast_pos.mpr hd))
  have hx : x ∈ Metric.closedBall m R := by
    simp [x, Metric.mem_closedBall, dist_eq_norm, norm_smul, abs_of_pos hR,
      (affineEigenBasisRows_orthonormal D.potential D.rate).norm_eq_one]
  have he := congrArg (fun z => z j)
    (classicalEvaluationEigenmap_eq_linear_about_mean D.smooth D.rate D.rate_pos D.hessian D.probability x)
  change classicalEigenRepresentative D.potential D.rate
    (classicalEigenOrthonormalBasis D.smooth D.rate D.rate_pos D.hessian D.probability j) x =
      Real.sqrt D.rate * inner ℝ (affineEigenBasisRows D.potential D.rate j) (x - m) at he
  rw [classicalEigenOrthonormalBasis_representative] at he
  have hrow : inner ℝ (affineEigenBasisRows D.potential D.rate j) (affineEigenBasisRows D.potential D.rate j) = 1 :=
    orthonormal_iff_ite.mp (affineEigenBasisRows_orthonormal D.potential D.rate) j j
  dsimp only [x] at he
  rw [add_sub_cancel_left, inner_smul_right, hrow, mul_one] at he
  refine ⟨x, j, hx, ?_, ?_⟩
  · change 0 < affineEigenBasisFunction D.potential D.rate j x
    rw [he]
    exact mul_pos (Real.sqrt_pos.mpr D.rate_pos) hR
  · change (affineEigenBasisFunction D.potential D.rate j x) ^ 2 = _
    rw [he, mul_pow, Real.sq_sqrt D.rate_pos.le]
    dsimp only [R]
    rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg d)]
    ring

@[expose] noncomputable def meanBallKL (D : SpectralInformationLowerData Ω d) (c t : ℝ) : ℝ≥0∞ :=
  projectedSetKL (spectralInformationToAffine D)
    (Metric.closedBall (∫ y, y ∂gibbsMeasure volume D.potential) (c * Real.sqrt d)) t
@[expose] noncomputable def meanBallTV (D : SpectralInformationLowerData Ω d) (c t : ℝ) : ℝ :=
  projectedSetTV (spectralInformationToAffine D)
    (Metric.closedBall (∫ y, y ∂gibbsMeasure volume D.potential) (c * Real.sqrt d)) t

theorem meanBallKL_lower (D : SpectralInformationLowerData Ω d) (hd : 0 < d)
    {c t : ℝ} (hc : 0 ≤ c) (ht : 0 < t) :
    ENNReal.ofReal (D.rate * c ^ 2 / 2 * ((d : ℝ) * Real.exp (-2 * D.rate * t))) ≤ meanBallKL D c t := by
  by_cases hz : c = 0
  · simp only [hz, zero_pow (by decide : 2 ≠ 0), mul_zero, zero_div, zero_mul, ENNReal.ofReal_zero]
    exact bot_le
  obtain ⟨x, j, hx, hm, hs⟩ := spectralInformation_mean_ball_witness D hd (lt_of_le_of_ne hc (Ne.symm hz))
  have h := projectedSetKL_lower_of_coordinate (spectralInformationToAffine D) x hx j
    (D.rate * c ^ 2 * d) hs.ge ht
  change ENNReal.ofReal (Real.exp (-2 * D.rate * t) * (D.rate * c ^ 2 * d) / 2) ≤ meanBallKL D c t at h
  convert h using 1
  congr 1
  ring

theorem meanBallTV_le_one (D : SpectralInformationLowerData Ω d) {c : ℝ} (hc : 0 ≤ c) (t : ℝ) :
    meanBallTV D c t ≤ 1 :=
  projectedSetTV_le_one _ ⟨∫ y, y ∂gibbsMeasure volume D.potential, by simpa using mul_nonneg hc (Real.sqrt_nonneg (d : ℝ))⟩ t

theorem meanBallTV_lower (D : SpectralInformationLowerData Ω d) (hd : 0 < d)
    {c t : ℝ} (hc : 0 < c) (ht : 0 ≤ t) :
    1 - 8 / (D.rate * c ^ 2 * ((d : ℝ) * Real.exp (-2 * D.rate * t))) ≤ meanBallTV D c t := by
  obtain ⟨x, j, hx, hm, hs⟩ := spectralInformation_mean_ball_witness D hd hc
  have h := projectedSetTV_lower_of_coordinate (spectralInformationToAffine D) x hx j hm ht
  rw [hs] at h
  change 1 - 8 / (Real.exp (-2 * D.rate * t) * (D.rate * c ^ 2 * d)) ≤ meanBallTV D c t at h
  convert h using 1
  congr 2
  ring

@[expose] noncomputable def cubeOneRowProjectedData (D : ConvexInteractionCubeData Ω d) (hd : 0 < d) :
    AffineProjectedCutoffData Ω d where
  potential := (cubeSpectralData D).potential
  smooth := (cubeSpectralData D).smooth
  curvature := D.rate
  curvature_nonneg := D.rate_pos.le
  hessian := (cubeSpectralData D).hessian
  probability := (cubeSpectralData D).probability
  rate := D.rate
  rate_pos := D.rate_pos
  driver := D.driver
  noiseLaw := D.noiseLaw
  brownian := D.brownian
  coordinateCount := 1
  row := fun _ => 0
  coefficient := fun _ => normalizedDiagonalCoefficient d D.rate
  constant := fun _ => 0
  eigenfunction := fun _ => cube_normalized_diagonal_eigenfunction D
  orthonormal := by
    intro i j
    have he : i = j := Subsingleton.elim _ _
    simp only [he, ↓reduceIte]
    simpa only [pow_two] using cube_normalized_diagonal_second_moment D hd

@[expose] noncomputable def convexCubeKL (D : ConvexInteractionCubeData Ω d) (c t : ℝ) : ℝ≥0∞ :=
  projectedSetKL (spectralInformationToAffine (cubeSpectralData D))
    (closedCoordinateCube (∫ y, y ∂gibbsMeasure volume (cubeSpectralData D).potential) c) t
@[expose] noncomputable def convexCubeTV (D : ConvexInteractionCubeData Ω d) (c t : ℝ) : ℝ :=
  projectedSetTV (spectralInformationToAffine (cubeSpectralData D))
    (closedCoordinateCube (∫ y, y ∂gibbsMeasure volume (cubeSpectralData D).potential) c) t

theorem convexCubeKL_lower (D : ConvexInteractionCubeData Ω d) (hd : 0 < d)
    {c t : ℝ} (hc : 0 ≤ c) (ht : 0 < t) :
    ENNReal.ofReal (D.rate * c ^ 2 / 2 * ((d : ℝ) * Real.exp (-2 * D.rate * t))) ≤ convexCubeKL D c t := by
  let m := ∫ y, y ∂gibbsMeasure volume (cubeSpectralData D).potential
  have h := projectedSetKL_lower_of_coordinate (cubeOneRowProjectedData D hd)
    (m + c • diagonalDirection d) (cube_diagonal_corner_mem m hc) ⟨0, by change 0 < (1 : ℕ); decide⟩ (D.rate * c ^ 2 * d)
    (cube_normalized_diagonal_corner_sq D hd c).ge ht
  change ENNReal.ofReal (Real.exp (-2 * D.rate * t) * (D.rate * c ^ 2 * d) / 2) ≤ convexCubeKL D c t at h
  convert h using 1
  congr 1
  ring

theorem convexCubeTV_le_one (D : ConvexInteractionCubeData Ω d) {c : ℝ} (hc : 0 ≤ c) (t : ℝ) :
    convexCubeTV D c t ≤ 1 := by
  apply projectedSetTV_le_one
  exact ⟨∫ y, y ∂gibbsMeasure volume (cubeSpectralData D).potential, fun i => by simp [hc]⟩

theorem convexCubeTV_lower (D : ConvexInteractionCubeData Ω d) (hd : 0 < d)
    {c t : ℝ} (hc : 0 < c) (ht : 0 ≤ t) :
    1 - 8 / (D.rate * c ^ 2 * ((d : ℝ) * Real.exp (-2 * D.rate * t))) ≤ convexCubeTV D c t := by
  let m := ∫ y, y ∂gibbsMeasure volume (cubeSpectralData D).potential
  let x := m + c • diagonalDirection d
  have hs := cube_normalized_diagonal_corner_sq D hd c
  have hnonneg : 0 ≤ inner ℝ (normalizedDiagonalCoefficient d D.rate) x + 0 := by
    dsimp only [x, m]
    simp only [normalizedDiagonalCoefficient, real_inner_smul_left, inner_add_right, inner_smul_right,
      inner_diagonalDirection, cube_coordinateSum_mean_zero D hd, add_zero]
    have hdg : coordinateSum (diagonalDirection d) = (d : ℝ) := by simp [coordinateSum, diagonalDirection]
    rw [hdg]
    positivity
  have hpos : 0 < D.rate * c ^ 2 * (d : ℝ) :=
    mul_pos (mul_pos D.rate_pos (sq_pos_of_pos hc)) (Nat.cast_pos.mpr hd)
  have hm : 0 < inner ℝ (normalizedDiagonalCoefficient d D.rate) x + 0 := by nlinarith [hs]
  have h := projectedSetTV_lower_of_coordinate (cubeOneRowProjectedData D hd)
    x (cube_diagonal_corner_mem m hc.le) ⟨0, by change 0 < (1 : ℕ); decide⟩ hm ht
  change 1 - 8 / (Real.exp (-2 * D.rate * t) *
    (inner ℝ (normalizedDiagonalCoefficient d D.rate) x + 0) ^ 2) ≤ _ at h
  rw [hs] at h
  change 1 - 8 / (Real.exp (-2 * D.rate * t) * (D.rate * c ^ 2 * d)) ≤ convexCubeTV D c t at h
  convert h using 1
  congr 2
  ring


private theorem information_early_time_pos {n : ℕ} (hn : 2 ≤ n)
    {rate ε : ℝ} (hrate : 0 < rate) (hε1 : ε < 1) :
    0 < (1 - ε) * criticalTime n rate := by
  apply mul_pos (by linarith)
  unfold criticalTime
  exact div_pos (Real.log_pos (by exact_mod_cast (show 1 < n by omega))) (by positivity)

/-- Scalar asymptotics applied only after proving the actual-measure lower bound. -/
theorem entropy_cutoff_of_actual_set_lower
    (rate : ℕ → ℝ) (hrate : ∀ n, 0 < rate n) (H : ℕ → ℝ → ℝ≥0∞)
    {c ε : ℝ} (hc : 0 < c) (hε : 0 < ε) (hε1 : ε < 1)
    (hlower : ∀ n, 0 < n → ∀ t, 0 < t →
      ENNReal.ofReal (rate n * c ^ 2 / 2 * ((n : ℝ) * Real.exp (-2 * rate n * t))) ≤ H n t)
    (hpositive : ∃ r : ℝ, 0 < r ∧ ∀ᶠ n in atTop, r ≤ rate n) :
    Tendsto (fun n : ℕ => H n ((1 - ε) * criticalTime n (rate n))) atTop (𝓝 ⊤) := by
  obtain ⟨r, hr, hevent⟩ := hpositive
  have hC : 0 < r * c ^ 2 / 2 := by positivity
  have hscale : Tendsto (fun n : ℕ => ENNReal.ofReal (r * c ^ 2 / 2 * (n : ℝ) ^ ε))
      atTop (𝓝 ⊤) := ENNReal.tendsto_ofReal_nhds_top.mpr
        ((power_before_cutoff hε).const_mul_atTop hC)
  apply tendsto_nhds_top_mono hscale
  filter_upwards [hevent, eventually_ge_atTop 2] with n hn hdim
  have h := hlower n (by omega) _ (information_early_time_pos hdim (hrate n) hε1)
  rw [dimension_decay_at_criticalTime n (rate n) (1 - ε)
    (by exact_mod_cast (show 0 < n by omega)) (hrate n).ne'] at h
  simp only [show (1 : ℝ) - (1 - ε) = ε by ring] at h
  apply le_trans _ h
  apply ENNReal.ofReal_le_ofReal
  gcongr

/-- The separating-halfspace lower bound and the probability upper bound
force total variation to one. -/
theorem totalVariation_cutoff_of_actual_set_lower
    (rate : ℕ → ℝ) (hrate : ∀ n, 0 < rate n) (H : ℕ → ℝ → ℝ)
    {c ε : ℝ} (hc : 0 < c) (hε : 0 < ε) (hε1 : ε < 1)
    (hupper : ∀ n t, H n t ≤ 1)
    (hlower : ∀ n, 0 < n → ∀ t, 0 ≤ t →
      1 - 8 / (rate n * c ^ 2 * ((n : ℝ) * Real.exp (-2 * rate n * t))) ≤ H n t)
    (hpositive : ∃ r : ℝ, 0 < r ∧ ∀ᶠ n in atTop, r ≤ rate n) :
    Tendsto (fun n : ℕ => H n ((1 - ε) * criticalTime n (rate n))) atTop (𝓝 1) := by
  obtain ⟨r, hr, hevent⟩ := hpositive
  have hC : 0 < r * c ^ 2 := mul_pos hr (sq_pos_of_pos hc)
  have hscale : Tendsto (fun n : ℕ => 8 / (r * c ^ 2 * (n : ℝ) ^ ε)) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero, Pi.inv_apply] using
      (((power_before_cutoff hε).const_mul_atTop hC).inv_tendsto_atTop.const_mul 8)
  have hdiff : Tendsto (fun n : ℕ => 1 - H n
      ((1 - ε) * criticalTime n (rate n))) atTop (𝓝 0) := by
    apply squeeze_zero' (g := fun n : ℕ => 8 / (r * c ^ 2 * (n : ℝ) ^ ε))
    · exact Filter.Eventually.of_forall (fun n => sub_nonneg.mpr (hupper n _))
    · filter_upwards [hevent, eventually_ge_atTop 2] with n hn hdim
      have ht := information_early_time_pos hdim (hrate n) hε1
      have h := hlower n (by omega) _ ht.le
      rw [dimension_decay_at_criticalTime n (rate n) (1 - ε)
        (by exact_mod_cast (show 0 < n by omega)) (hrate n).ne'] at h
      simp only [show (1 : ℝ) - (1 - ε) = ε by ring] at h
      have hpow : 0 < (n : ℝ) ^ ε := Real.rpow_pos_of_pos
        (by exact_mod_cast (show 0 < n by omega)) _
      have hden : r * c ^ 2 * (n : ℝ) ^ ε ≤ rate n * c ^ 2 * (n : ℝ) ^ ε := by gcongr
      have hdiv := div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 8)
        (mul_pos hC hpow) hden
      linarith
    · exact hscale
  have h := (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)).sub hdiff
  simpa only [sub_sub_cancel, sub_zero] using h

/-- The source entropy lower cutoff on balls about the actual Gibbs barycenter. -/
theorem meanBall_entropy_before_cutoff
    (D : ∀ n : ℕ, SpectralInformationLowerData Ω n) {c ε : ℝ}
    (hc : 0 < c) (hε : 0 < ε) (hε1 : ε < 1)
    (hliminf : 0 < liminf (fun n => ENNReal.ofReal (D n).rate) atTop) :
    Tendsto (fun n : ℕ => meanBallKL (D n) c
      ((1 - ε) * criticalTime n (D n).rate)) atTop (𝓝 ⊤) :=
  entropy_cutoff_of_actual_set_lower (fun n => (D n).rate) (fun n => (D n).rate_pos)
    (fun n t => meanBallKL (D n) c t) hc hε hε1
    (fun n hn _t ht => meanBallKL_lower (D n) hn hc.le ht)
    (spectralInformation_rates_eventually_positive_lower D hliminf)

/-- The source total-variation lower cutoff on the actual barycenter balls. -/
theorem meanBall_totalVariation_before_cutoff
    (D : ∀ n : ℕ, SpectralInformationLowerData Ω n) {c ε : ℝ}
    (hc : 0 < c) (hε : 0 < ε) (hε1 : ε < 1)
    (hliminf : 0 < liminf (fun n => ENNReal.ofReal (D n).rate) atTop) :
    Tendsto (fun n : ℕ => meanBallTV (D n) c
      ((1 - ε) * criticalTime n (D n).rate)) atTop (𝓝 1) :=
  totalVariation_cutoff_of_actual_set_lower (fun n => (D n).rate) (fun n => (D n).rate_pos)
    (fun n t => meanBallTV (D n) c t) hc hε hε1
    (fun n t => meanBallTV_le_one (D n) hc.le t)
    (fun n hn _t ht => meanBallTV_lower (D n) hn hc ht)
    (spectralInformation_rates_eventually_positive_lower D hliminf)

/-- The exact cube entropy lower cutoff, using the normalized diagonal
Gaussian projection and the actual normalized convex-interaction Gibbs law. -/
theorem convexCube_entropy_before_cutoff
    (D : ∀ n : ℕ, ConvexInteractionCubeData Ω n) {c ε : ℝ}
    (hc : 0 < c) (hε : 0 < ε) (hε1 : ε < 1)
    (hliminf : 0 < liminf (fun n => ENNReal.ofReal (D n).rate) atTop) :
    Tendsto (fun n : ℕ => convexCubeKL (D n) c
      ((1 - ε) * criticalTime n (D n).rate)) atTop (𝓝 ⊤) :=
  entropy_cutoff_of_actual_set_lower (fun n => (D n).rate) (fun n => (D n).rate_pos)
    (fun n t => convexCubeKL (D n) c t) hc hε hε1
    (fun n hn _t ht => convexCubeKL_lower (D n) hn hc.le ht)
    (spectralInformation_rates_eventually_positive_lower (fun n => cubeSpectralData (D n)) hliminf)

/-- The exact cube total-variation lower cutoff from the same actual
one-dimensional diagonal projection; no supplied family or law is assumed. -/
theorem convexCube_totalVariation_before_cutoff
    (D : ∀ n : ℕ, ConvexInteractionCubeData Ω n) {c ε : ℝ}
    (hc : 0 < c) (hε : 0 < ε) (hε1 : ε < 1)
    (hliminf : 0 < liminf (fun n => ENNReal.ofReal (D n).rate) atTop) :
    Tendsto (fun n : ℕ => convexCubeTV (D n) c
      ((1 - ε) * criticalTime n (D n).rate)) atTop (𝓝 1) :=
  totalVariation_cutoff_of_actual_set_lower (fun n => (D n).rate) (fun n => (D n).rate_pos)
    (fun n t => convexCubeTV (D n) c t) hc hε hε1
    (fun n t => convexCubeTV_le_one (D n) hc.le t)
    (fun n hn _t ht => convexCubeTV_lower (D n) hn hc ht)
    (spectralInformation_rates_eventually_positive_lower (fun n => cubeSpectralData (D n)) hliminf)

end CutoffRigidity
