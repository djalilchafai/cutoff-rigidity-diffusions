module
public import CutoffRigidity.BarycenterWassersteinCutoff

/-! # The written diagonal-eigenfunction cube proof in Section 3.6 -/
public section
namespace CutoffRigidity
open Set MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal ContDiff
variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

@[expose] def closedCoordinateCube (m : E) (c : ℝ) : Set E := {x | ∀ i, |x i - m i| ≤ c}

theorem closedCoordinateCube_subset_ball (m : E) {c : ℝ} (hc : 0 ≤ c) :
    closedCoordinateCube m c ⊆ Metric.closedBall m (c * Real.sqrt d) := by
  intro x hx
  rw [Metric.mem_closedBall, dist_eq_norm]
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hc (Real.sqrt_nonneg _))).mp
  rw [EuclideanSpace.real_norm_sq_eq, mul_pow, Real.sq_sqrt (Nat.cast_nonneg d)]
  calc
    _ ≤ ∑ _ : Fin d, c ^ 2 := Finset.sum_le_sum (fun i _ => by
      simpa only [PiLp.sub_apply, sq_abs] using (sq_le_sq₀ (abs_nonneg _) hc).mpr (hx i))
    _ = _ := by simp; ring

theorem cube_diagonal_corner_mem (m : E) {c : ℝ} (hc : 0 ≤ c) :
    m + c • diagonalDirection d ∈ closedCoordinateCube m c := by
  intro i
  simp [diagonalDirection, PiLp.add_apply, PiLp.smul_apply, abs_of_nonneg hc]

structure ConvexInteractionCubeData (Ω : Type*) [MeasurableSpace Ω] (d : ℕ) where
  interaction : EuclideanSpace ℝ (Fin d) → ℝ
  smooth : ContDiff ℝ 2 interaction
  convex : ConvexOn ℝ Set.univ interaction
  rate : ℝ
  rate_pos : 0 < rate
  diagonalInvariant : ∀ x (t : ℝ), interaction (x + t • diagonalDirection d) = interaction x
  driver : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d)
  noiseLaw : Measure Ω
  brownian : IsEuclideanBrownian driver noiseLaw

@[expose] noncomputable def cubeSpectralData (D : ConvexInteractionCubeData Ω d) : SpectralInformationLowerData Ω d :=
  normalizedConvexInteractionInformationLowerData D.smooth D.convex D.rate D.rate_pos D.diagonalInvariant D.brownian

theorem cube_coordinateSum_eigenfunction (D : ConvexInteractionCubeData Ω d) (x : E) :
    langevinDifferentialOperator (cubeSpectralData D).potential coordinateSum x = -D.rate * coordinateSum x := by
  change langevinDifferentialOperator
    (fun y : E => D.rate / 2 * ‖y‖ ^ 2 + (D.interaction y + Real.log
      (∫ z : E, Real.exp (-(D.rate / 2 * ‖z‖ ^ 2 + D.interaction z))))) coordinateSum x = _
  apply langevinDifferentialOperator_coordinateSum
  · exact ((D.smooth.add contDiff_const).differentiable (by norm_num)) x
  · intro t
    rw [D.diagonalInvariant]

theorem cube_coordinateSum_mean_zero (D : ConvexInteractionCubeData Ω d) (hd : 0 < d) :
    coordinateSum (∫ x, x ∂gibbsMeasure volume (cubeSpectralData D).potential) = 0 := by
  let S := cubeSpectralData D
  let := S.probability
  have hne : diagonalDirection d ≠ 0 := by
    intro h
    have hn := norm_sq_diagonalDirection d
    rw [h, norm_zero, zero_pow (by decide : 2 ≠ 0)] at hn
    exact (Nat.cast_pos.mpr hd).ne' hn.symm
  have he : ∀ x : E, langevinDifferentialOperator S.potential
      (fun y => inner ℝ (diagonalDirection d) y + 0) x = -D.rate * (inner ℝ (diagonalDirection d) x + 0) := by
    simpa only [inner_diagonalDirection, add_zero] using cube_coordinateSum_eigenfunction D
  have hm := affine_eigenfunction_mean_zero S.potential (S.smooth.differentiable (by norm_num))
    (diagonalDirection d) hne 0 D.rate D.rate_pos he S.probability
  have hi := (gibbs_memLp_two_id_of_hessian_bound S.smooth S.rate S.rate_pos S.hessian).integrable (by norm_num)
  simp only [add_zero] at hm
  rw [integral_inner hi, inner_diagonalDirection] at hm
  exact hm

@[expose] noncomputable def normalizedDiagonalCoefficient (d : ℕ) (rate : ℝ) : EuclideanSpace ℝ (Fin d) :=
  Real.sqrt (rate / d) • diagonalDirection d

theorem normalizedDiagonalCoefficient_norm_sq {rate : ℝ} (hpos : 0 < rate) (hd : 0 < d) :
    ‖normalizedDiagonalCoefficient d rate‖ ^ 2 = rate := by
  have hdR : (0 : ℝ) < d := Nat.cast_pos.mpr hd
  rw [normalizedDiagonalCoefficient, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs,
    Real.sq_sqrt (div_nonneg hpos.le hdR.le), norm_sq_diagonalDirection]
  exact div_mul_cancel₀ rate hdR.ne'

theorem cube_normalized_diagonal_eigenfunction (D : ConvexInteractionCubeData Ω d) (x : E) :
    langevinDifferentialOperator (cubeSpectralData D).potential
      (fun y => inner ℝ (normalizedDiagonalCoefficient d D.rate) y + 0) x =
      -D.rate * (inner ℝ (normalizedDiagonalCoefficient d D.rate) x + 0) := by
  have hsum : ContDiff ℝ 2 (coordinateSum : E → ℝ) := by
    have he : (coordinateSum : E → ℝ) = innerSL ℝ (diagonalDirection d) := funext (fun y => (inner_diagonalDirection y).symm)
    rw [he]
    exact (innerSL ℝ (diagonalDirection d)).contDiff
  have he := langevinDifferentialOperator_smul_classical (cubeSpectralData D).potential hsum
    (Real.sqrt (D.rate / d)) x
  rw [cube_coordinateSum_eigenfunction D] at he
  simpa only [normalizedDiagonalCoefficient, real_inner_smul_left, inner_diagonalDirection, add_zero,
    mul_assoc, mul_comm, mul_left_comm] using he

theorem cube_normalized_diagonal_second_moment (D : ConvexInteractionCubeData Ω d) (hd : 0 < d) :
    (∫ x, (inner ℝ (normalizedDiagonalCoefficient d D.rate) x + 0) ^ 2
      ∂gibbsMeasure volume (cubeSpectralData D).potential) = 1 := by
  have he := affine_eigenfunction_second_moment_all (cubeSpectralData D).potential
    ((cubeSpectralData D).smooth.differentiable (by norm_num)) (normalizedDiagonalCoefficient d D.rate)
    0 D.rate D.rate_pos (cube_normalized_diagonal_eigenfunction D) (cubeSpectralData D).probability
  rwa [normalizedDiagonalCoefficient_norm_sq D.rate_pos hd, div_self D.rate_pos.ne'] at he

theorem cube_normalized_diagonal_corner_sq (D : ConvexInteractionCubeData Ω d) (hd : 0 < d) (c : ℝ) :
    (inner ℝ (normalizedDiagonalCoefficient d D.rate)
      ((∫ x, x ∂gibbsMeasure volume (cubeSpectralData D).potential) + c • diagonalDirection d) + 0) ^ 2 =
      D.rate * c ^ 2 * d := by
  have hdR : (0 : ℝ) < d := Nat.cast_pos.mpr hd
  simp only [normalizedDiagonalCoefficient, real_inner_smul_left, inner_add_right, inner_smul_right,
    inner_diagonalDirection, add_zero]
  rw [cube_coordinateSum_mean_zero D hd]
  have hsum : coordinateSum (diagonalDirection d) = (d : ℝ) := by simp [coordinateSum, diagonalDirection]
  rw [hsum]
  simp only [mul_zero, zero_add, mul_pow, Real.sq_sqrt (div_nonneg D.rate_pos.le hdR.le)]
  field_simp

@[expose] noncomputable def cubeSquaredWasserstein (D : ConvexInteractionCubeData Ω d) (c t : ℝ) : ℝ :=
  (⨆ x : closedCoordinateCube (∫ y, y ∂gibbsMeasure volume (cubeSpectralData D).potential) c,
    squaredWasserstein (langevinKernel (cubeSpectralData D).potential D.driver D.noiseLaw t.toNNReal x)
      (gibbsMeasure volume (cubeSpectralData D).potential)).toReal

set_option maxHeartbeats 800000 in
/-- The written cube sandwich: its lower bound uses the normalized
diagonal eigenfunction at a cube corner, not an inscribed fixed ball. -/
theorem cubeSquaredWasserstein_bounds (D : ConvexInteractionCubeData Ω d) (hd : 0 < d)
    {c t : ℝ} (hc : 0 ≤ c) (ht : 0 ≤ t) :
    c ^ 2 * ((d : ℝ) * Real.exp (-2 * D.rate * t)) ≤ cubeSquaredWasserstein D c t ∧
      cubeSquaredWasserstein D c t ≤
        (c ^ 2 + D.rate⁻¹) * ((d : ℝ) * Real.exp (-2 * D.rate * t)) := by
  let S := cubeSpectralData D
  let m := ∫ y, y ∂gibbsMeasure volume S.potential
  let C := closedCoordinateCube m c
  let W : ℝ≥0∞ := ⨆ x : C, squaredWasserstein
    (langevinKernel S.potential D.driver D.noiseLaw t.toNNReal x) (gibbsMeasure volume S.potential)
  let WB : ℝ≥0∞ := ⨆ x : Metric.closedBall m (c * Real.sqrt d), squaredWasserstein
    (langevinKernel S.potential D.driver D.noiseLaw t.toNNReal x) (gibbsMeasure volume S.potential)
  have hsubset : W ≤ WB := by
    apply iSup_le
    intro x
    exact le_iSup (fun y : Metric.closedBall m (c * Real.sqrt d) => squaredWasserstein
      (langevinKernel S.potential D.driver D.noiseLaw t.toNNReal y) (gibbsMeasure volume S.potential))
      ⟨x, closedCoordinateCube_subset_ball m hc x.property⟩
  have hbfin : WB ≠ ⊤ := by
    change (⨆ x : Metric.closedBall (∫ y, y ∂gibbsMeasure volume S.potential) (c * Real.sqrt d),
      squaredWasserstein (langevinKernel S.potential S.driver S.noiseLaw t.toNNReal x)
        (gibbsMeasure volume S.potential)) ≠ ⊤
    rw [← barycenterBallSquaredWasserstein_ofReal S hd hc t]
    exact ENNReal.ofReal_ne_top
  have hwfin : W ≠ ⊤ := ne_top_of_le_ne_top hbfin hsubset
  have hu := (ENNReal.toReal_mono hbfin hsubset).trans
    (barycenterBallSquaredWasserstein_bounds S hd hc ht).2
  have horth (i j : Fin 1) :
      (∫ x, (inner ℝ (normalizedDiagonalCoefficient d D.rate) x + 0) *
        (inner ℝ (normalizedDiagonalCoefficient d D.rate) x + 0) ∂gibbsMeasure volume S.potential) =
      if i = j then 1 else 0 := by
    have hij : i = j := Subsingleton.elim _ _
    simp only [hij, ↓reduceIte]
    simpa only [pow_two] using cube_normalized_diagonal_second_moment D hd
  let x₀ := m + c • diagonalDirection d
  have hx₀ : x₀ ∈ C := cube_diagonal_corner_mem m hc
  have hl := affine_langevin_wasserstein_lower D.brownian S.smooth D.rate D.rate_pos.le S.hessian
    (fun _ : Fin 1 => normalizedDiagonalCoefficient d D.rate) (fun _ => 0) D.rate D.rate_pos
    (fun _ => cube_normalized_diagonal_eigenfunction D) S.probability horth x₀ t.toNNReal
  have hnorm : ‖WithLp.toLp 2 (fun _ : Fin 1 => inner ℝ (normalizedDiagonalCoefficient d D.rate) x₀ + 0)‖ ^ 2 =
      D.rate * c ^ 2 * d := by
    rw [EuclideanSpace.real_norm_sq_eq]
    simpa only [Fin.sum_univ_one] using cube_normalized_diagonal_corner_sq D hd c
  rw [hnorm, Real.coe_toNNReal _ ht] at hl
  have hcost : squaredWasserstein (langevinKernel S.potential D.driver D.noiseLaw t.toNNReal x₀)
      (gibbsMeasure volume S.potential) ≤ W := le_iSup (fun x : C => squaredWasserstein
        (langevinKernel S.potential D.driver D.noiseLaw t.toNNReal x) (gibbsMeasure volume S.potential)) ⟨x₀, hx₀⟩
  have hh := hl.trans (mul_le_mul_right hcost (ENNReal.ofReal D.rate))
  have hhR := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hwfin) hh
  have hpos := D.rate_pos
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal D.rate_pos.le,
    ENNReal.toReal_ofReal (by positivity)] at hhR
  change _ ≤ D.rate * cubeSquaredWasserstein D c t at hhR
  change cubeSquaredWasserstein D c t ≤ _ at hu
  refine ⟨?_, hu⟩
  have hcorr : 0 ≤ (1 : ℝ) * (1 - Real.sqrt (1 - Real.exp (-2 * D.rate * t))) ^ 2 := by positivity
  nlinarith

theorem cube_squaredWasserstein_before_cutoff
    (D : ∀ n : ℕ, ConvexInteractionCubeData Ω n) {c ε : ℝ}
    (hc : 0 < c) (hε : 0 < ε) (hε1 : ε < 1) :
    Tendsto (fun n : ℕ => cubeSquaredWasserstein (D n) c ((1 - ε) * criticalTime n (D n).rate)) atTop atTop := by
  apply exponential_lower_cutoff (c := c ^ 2) (rate := fun n => (D n).rate)
    (sq_pos_of_pos hc) hε (fun n => (D n).rate_pos.ne')
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hp := (D n).rate_pos
  have ht : 0 ≤ (1 - ε) * criticalTime n (D n).rate := by
    apply mul_nonneg (by linarith)
    unfold criticalTime
    exact div_nonneg (Real.log_nonneg (by exact_mod_cast hn)) (by positivity)
  exact (cubeSquaredWasserstein_bounds (D n) (by omega) hc.le ht).1

theorem cube_squaredWasserstein_after_cutoff
    (D : ∀ n : ℕ, ConvexInteractionCubeData Ω n) {c ε : ℝ}
    (hc : 0 ≤ c) (hε : 0 < ε)
    (hliminf : 0 < liminf (fun n => ENNReal.ofReal (D n).rate) atTop) :
    Tendsto (fun n : ℕ => cubeSquaredWasserstein (D n) c ((1 + ε) * criticalTime n (D n).rate)) atTop (𝓝 0) := by
  obtain ⟨r, hr, hrate⟩ := spectralInformation_rates_eventually_positive_lower (fun n => cubeSpectralData (D n)) hliminf
  apply exponential_upper_cutoff (C := c ^ 2 + r⁻¹) (rate := fun n => (D n).rate)
    hε (fun n => (D n).rate_pos.ne')
  · exact Filter.Eventually.of_forall (fun _ => ENNReal.toReal_nonneg)
  · filter_upwards [hrate, eventually_ge_atTop 1] with n hn hdim
    have hp := (D n).rate_pos
    have ht : 0 ≤ (1 + ε) * criticalTime n (D n).rate := by
      apply mul_nonneg (by linarith)
      unfold criticalTime
      exact div_nonneg (Real.log_nonneg (by exact_mod_cast hdim)) (by positivity)
    exact (cubeSquaredWasserstein_bounds (D n) (by omega) hc ht).2.trans
      (mul_le_mul_of_nonneg_right (add_le_add le_rfl (inv_anti₀ hr hn)) (by positivity))

theorem cubeSquaredWasserstein_ofReal (D : ConvexInteractionCubeData Ω d) (hd : 0 < d)
    {c : ℝ} (hc : 0 ≤ c) (t : ℝ) :
    ENNReal.ofReal (cubeSquaredWasserstein D c t) =
      ⨆ x : closedCoordinateCube (∫ y, y ∂gibbsMeasure volume (cubeSpectralData D).potential) c,
        squaredWasserstein (langevinKernel (cubeSpectralData D).potential D.driver D.noiseLaw t.toNNReal x)
          (gibbsMeasure volume (cubeSpectralData D).potential) := by
  let S := cubeSpectralData D
  let m := ∫ y, y ∂gibbsMeasure volume S.potential
  have hbfin : (⨆ x : Metric.closedBall m (c * Real.sqrt d),
      squaredWasserstein (langevinKernel S.potential D.driver D.noiseLaw t.toNNReal x)
        (gibbsMeasure volume S.potential)) ≠ ⊤ := by
    change (⨆ x : Metric.closedBall (∫ y, y ∂gibbsMeasure volume S.potential) (c * Real.sqrt d),
      squaredWasserstein (langevinKernel S.potential S.driver S.noiseLaw t.toNNReal x)
        (gibbsMeasure volume S.potential)) ≠ ⊤
    rw [← barycenterBallSquaredWasserstein_ofReal S hd hc t]
    exact ENNReal.ofReal_ne_top
  apply ENNReal.ofReal_toReal
  apply ne_top_of_le_ne_top hbfin
  apply iSup_le
  intro x
  exact le_iSup (fun y : Metric.closedBall m (c * Real.sqrt d) =>
    squaredWasserstein (langevinKernel S.potential D.driver D.noiseLaw t.toNNReal y)
      (gibbsMeasure volume S.potential)) ⟨x, closedCoordinateCube_subset_ball m hc x.property⟩

@[expose] noncomputable def cubeWasserstein (D : ConvexInteractionCubeData Ω d) (c t : ℝ) : ℝ :=
  ⨆ x : closedCoordinateCube (∫ y, y ∂gibbsMeasure volume (cubeSpectralData D).potential) c,
    Real.sqrt ((squaredWasserstein (langevinKernel (cubeSpectralData D).potential D.driver D.noiseLaw t.toNNReal x)
      (gibbsMeasure volume (cubeSpectralData D).potential)).toReal)

theorem cubeWasserstein_eq_sqrt
    (D : ConvexInteractionCubeData Ω d) (hd : 0 < d) {c : ℝ} (hc : 0 ≤ c) (t : ℝ) :
    cubeWasserstein D c t = Real.sqrt (cubeSquaredWasserstein D c t) := by
  let S := closedCoordinateCube (∫ y, y ∂gibbsMeasure volume (cubeSpectralData D).potential) c
  let W (x : S) := squaredWasserstein (langevinKernel (cubeSpectralData D).potential D.driver D.noiseLaw t.toNNReal x)
    (gibbsMeasure volume (cubeSpectralData D).potential)
  have hS : S.Nonempty := ⟨∫ y, y ∂gibbsMeasure volume (cubeSpectralData D).potential, fun i => by simp [hc]⟩
  let : Nonempty S := hS.to_subtype
  have hfin : (⨆ x : S, W x) ≠ ⊤ := by
    rw [← cubeSquaredWasserstein_ofReal D hd hc t]
    exact ENNReal.ofReal_ne_top
  have hpoint : ∀ x : S, W x ≠ ⊤ := fun x => ne_top_of_le_ne_top hfin (le_iSup W x)
  have hb : BddAbove (Set.range fun x : S => (W x).toReal) := by
    refine ⟨(⨆ x : S, W x).toReal, ?_⟩
    rintro _ ⟨x, rfl⟩
    exact ENNReal.toReal_mono hfin (le_iSup W x)
  change (⨆ x : S, Real.sqrt ((W x).toReal)) = Real.sqrt ((⨆ x : S, W x).toReal)
  rw [ENNReal.toReal_iSup hpoint]
  exact (Real.sqrt_monotone.map_ciSup_of_continuousAt Real.continuous_sqrt.continuousAt hb).symm

/-- Source Section 3.6 cube branch before cutoff. -/
theorem cube_wasserstein_before_cutoff
    (D : ∀ n : ℕ, ConvexInteractionCubeData Ω n) {c ε : ℝ}
    (hc : 0 < c) (hε : 0 < ε) (hε1 : ε < 1) :
    Tendsto (fun n : ℕ => cubeWasserstein (D n) c
      ((1 - ε) * criticalTime n (D n).rate)) atTop atTop := by
  have h := Real.tendsto_sqrt_atTop.comp (cube_squaredWasserstein_before_cutoff D hc hε hε1)
  apply h.congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  exact (cubeWasserstein_eq_sqrt (D n) (by omega) hc.le _).symm

/-- Source Section 3.6 cube branch after cutoff, without centering premises. -/
theorem cube_wasserstein_after_cutoff
    (D : ∀ n : ℕ, ConvexInteractionCubeData Ω n) {c ε : ℝ}
    (hc : 0 ≤ c) (hε : 0 < ε)
    (hliminf : 0 < liminf (fun n => ENNReal.ofReal (D n).rate) atTop) :
    Tendsto (fun n : ℕ => cubeWasserstein (D n) c
      ((1 + ε) * criticalTime n (D n).rate)) atTop (𝓝 0) := by
  have h := Real.continuous_sqrt.continuousAt.tendsto.comp
    (cube_squaredWasserstein_after_cutoff D hc hε hliminf)
  have hh := h.congr' (show (fun n : ℕ => Real.sqrt (cubeSquaredWasserstein (D n) c
      ((1 + ε) * criticalTime n (D n).rate))) =ᶠ[atTop]
      (fun n => cubeWasserstein (D n) c ((1 + ε) * criticalTime n (D n).rate)) from by
    filter_upwards [eventually_ge_atTop 1] with n hn
    exact (cubeWasserstein_eq_sqrt (D n) (by omega) hc _).symm)
  simpa only [Real.sqrt_zero] using hh


theorem coordinateSum_cube_abs_isGreatest (m : E) (hm : coordinateSum m = 0)
    {c : ℝ} (hc : 0 ≤ c) :
    IsGreatest ((fun x : E => |coordinateSum x|) '' closedCoordinateCube m c) ((d : ℝ) * c) := by
  have hsum (x : E) : coordinateSum x = ∑ i : Fin d, (x i - m i) := by
    rw [Finset.sum_sub_distrib]
    change coordinateSum x = coordinateSum x - coordinateSum m
    rw [hm, sub_zero]
  constructor
  · refine ⟨m + c • diagonalDirection d, cube_diagonal_corner_mem m hc, ?_⟩
    dsimp only
    rw [hsum]
    simp only [PiLp.add_apply, PiLp.smul_apply, diagonalDirection, smul_eq_mul,
      mul_one, add_sub_cancel_left, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    exact abs_of_nonneg (mul_nonneg (Nat.cast_nonneg _) hc)
  · rintro _ ⟨x, hx, rfl⟩
    dsimp only
    rw [hsum]
    calc
      _ ≤ ∑ i : Fin d, |x i - m i| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _ : Fin d, c := Finset.sum_le_sum (fun i _ => hx i)
      _ = _ := by simp

/-- Exact normalized-eigenfunction supremum in the source's cube proof. -/
theorem cube_normalized_diagonal_abs_isGreatest (D : ConvexInteractionCubeData Ω d) (hd : 0 < d)
    {c : ℝ} (hc : 0 ≤ c) :
    IsGreatest ((fun x : E => |inner ℝ (normalizedDiagonalCoefficient d D.rate) x + 0|) ''
      closedCoordinateCube (∫ y, y ∂gibbsMeasure volume (cubeSpectralData D).potential) c)
      (c * Real.sqrt D.rate * Real.sqrt d) := by
  have hg := coordinateSum_cube_abs_isGreatest _ (cube_coordinateSum_mean_zero D hd) hc
  have hp (x : E) : |inner ℝ (normalizedDiagonalCoefficient d D.rate) x + 0| =
      Real.sqrt (D.rate / d) * |coordinateSum x| := by
    simp only [normalizedDiagonalCoefficient, real_inner_smul_left, inner_diagonalDirection,
      add_zero, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
  have hdR : (0 : ℝ) < d := Nat.cast_pos.mpr hd
  have hs : (Real.sqrt (D.rate / d) * ((d : ℝ) * c)) ^ 2 = D.rate * c ^ 2 * d := by
    rw [mul_pow, Real.sq_sqrt (div_nonneg D.rate_pos.le hdR.le)]
    field_simp
  have ht : (c * Real.sqrt D.rate * Real.sqrt (d : ℝ)) ^ 2 = D.rate * c ^ 2 * d := by
    rw [mul_pow, mul_pow, Real.sq_sqrt D.rate_pos.le, Real.sq_sqrt hdR.le]
    ring
  have hscale : Real.sqrt (D.rate / d) * ((d : ℝ) * c) = c * Real.sqrt D.rate * Real.sqrt d := by
    have h1 : 0 ≤ Real.sqrt (D.rate / d) * ((d : ℝ) * c) := by positivity
    have h2 : 0 ≤ c * Real.sqrt D.rate * Real.sqrt d := by positivity
    nlinarith
  constructor
  · obtain ⟨x, hx, he⟩ := hg.1
    exact ⟨x, hx, by dsimp only at he ⊢; rw [hp, he, hscale]⟩
  · rintro _ ⟨x, hx, rfl⟩
    dsimp only
    rw [hp, ← hscale]
    exact mul_le_mul_of_nonneg_left (hg.2 ⟨x, hx, rfl⟩) (Real.sqrt_nonneg _)

theorem cube_normalized_diagonal_abs_sup (D : ConvexInteractionCubeData Ω d) (hd : 0 < d)
    {c : ℝ} (hc : 0 ≤ c) :
    sSup ((fun x : E => |inner ℝ (normalizedDiagonalCoefficient d D.rate) x + 0|) ''
      closedCoordinateCube (∫ y, y ∂gibbsMeasure volume (cubeSpectralData D).potential) c) =
      c * Real.sqrt D.rate * Real.sqrt d :=
  (cube_normalized_diagonal_abs_isGreatest D hd hc).csSup_eq

theorem cube_actual_spectral_gap (D : ConvexInteractionCubeData Ω d) (hd : 0 < d) :
    gibbsSpectralGap (cubeSpectralData D).smooth (cubeSpectralData D).probability = D.rate :=
  (cubeSpectralData D).spectral hd

theorem cube_gibbs_variance_bound (D : ConvexInteractionCubeData Ω d) (hd : 0 < d) :
    (∫ x, ‖x - ∫ y, y ∂gibbsMeasure volume (cubeSpectralData D).potential‖ ^ 2
      ∂gibbsMeasure volume (cubeSpectralData D).potential) ≤ d / D.rate := by
  have h := gibbs_variance_le_dim_div_gap (cubeSpectralData D).smooth (cubeSpectralData D).probability hd
    D.rate D.rate_pos (cubeSpectralData D).hessian
  rwa [cube_actual_spectral_gap D hd] at h

end CutoffRigidity
