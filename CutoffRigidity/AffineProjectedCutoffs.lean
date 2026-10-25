module

public import CutoffRigidity.AffineProjectedDistances
public import CutoffRigidity.AffineWassersteinEstimate
public import CutoffRigidity.Asymptotics

/-! # Early entropy and total-variation cutoff for actual affine eigenmaps

This is the lower-bound projection paragraph of the paper. Actual affine
pointwise eigenfunctions, their Gibbs L² Gram matrix, and the Brownian
Langevin construction imply the distance estimates. A row direction in the
initial ball witnesses the divergence of the projected mean. Identification
with the entire first spectral eigenspace remains separate.
-/

public section

namespace CutoffRigidity

open Set MeasureTheory ProbabilityTheory InformationTheory Filter Topology
open scoped ENNReal NNReal

/-- The separating halfspace works for either sign of the Gaussian mean. -/
theorem totalVariationDistance_affineGaussian_nonzero_lower
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (m : EuclideanSpace ℝ ι) (s : ℝ) (hs : 0 ≤ s) (i : ι) (hm : m i ≠ 0) :
    1 - 4 * (s ^ 2 + 1) / (m i) ^ 2 ≤
      totalVariationDistance (affineGaussian m s) (stdGaussian (EuclideanSpace ℝ ι)) := by
  by_cases hp : 0 < m i
  · exact totalVariationDistance_affineGaussian_lower m s hs i hp
  have hn : 0 < -m i := by rcases lt_or_gt_of_ne hm with h | h <;> linarith
  have hXμ : MemLp (fun x : EuclideanSpace ℝ ι => x i) 2 (affineGaussian m s) := by
    simpa using IsGaussian.memLp_dual (affineGaussian m s) (EuclideanSpace.proj i) 2 (by norm_num)
  have hXν : MemLp (fun x : EuclideanSpace ℝ ι => x i) 2
      (stdGaussian (EuclideanSpace ℝ ι)) := by
    simpa using IsGaussian.memLp_dual (stdGaussian (EuclideanSpace ℝ ι))
      (EuclideanSpace.proj i) 2 (by norm_num)
  have hmeanν : (∫ x : EuclideanSpace ℝ ι, x i ∂stdGaussian (EuclideanSpace ℝ ι)) = 0 := by
    simpa using integral_eval_affineGaussian (0 : EuclideanSpace ℝ ι) 1 (by norm_num) i
  have hvarν : variance (fun x : EuclideanSpace ℝ ι => x i)
      (stdGaussian (EuclideanSpace ℝ ι)) = 1 := by
    simpa using variance_eval_affineGaussian (0 : EuclideanSpace ℝ ι) 1 (by norm_num) i
  have h := totalVariationDistance_ge_mean_separation (affineGaussian m s)
    (stdGaussian (EuclideanSpace ℝ ι)) (fun x => -x i) (by fun_prop)
    hXμ.neg hXν.neg hn
    (by rw [integral_neg, integral_eval_affineGaussian m s hs])
    (by rw [integral_neg, hmeanν, neg_zero])
  simpa only [variance_fun_neg, variance_eval_affineGaussian m s hs i, hvarν, neg_sq] using h

/-- Antipodal points along one unit row make the corresponding affine
coordinate large even when its constant term has arbitrary sign. -/
theorem exists_ball_affine_coordinate_sq_ge {d k : ℕ}
    {v : Fin k → EuclideanSpace ℝ (Fin d)} (hv : Orthonormal ℝ v)
    (b : EuclideanSpace ℝ (Fin k)) {ρ R : ℝ} (hρ : 0 ≤ ρ) (hR : 0 ≤ R) (j : Fin k) :
    ∃ x ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) R,
      ρ * R ^ 2 ≤ ((eigenmapCLM v ρ x + b) j) ^ 2 := by
  let u := R • v j
  have hmem : u ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) R := by
    simp [u, Metric.mem_closedBall, dist_zero_right, norm_smul, hv.norm_eq_one, abs_of_nonneg hR]
  have hcoord : (eigenmapCLM v ρ u) j = Real.sqrt ρ * R := by
    change Real.sqrt ρ * inner ℝ (v j) (R • v j) = _
    rw [inner_smul_right, orthonormal_iff_ite.mp hv j j]
    simp
  have hs : (Real.sqrt ρ * R) ^ 2 = ρ * R ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hρ]
  by_cases hb : 0 ≤ b j
  · refine ⟨u, hmem, ?_⟩
    change ρ * R ^ 2 ≤ ((eigenmapCLM v ρ u) j + b j) ^ 2
    rw [hcoord]
    nlinarith [mul_nonneg (Real.sqrt_nonneg ρ) hR, sq_nonneg (b j)]
  · refine ⟨-u, ?_, ?_⟩
    · simpa only [Metric.mem_closedBall, dist_zero_right, norm_neg] using hmem
    · rw [map_neg]
      change ρ * R ^ 2 ≤ (-(eigenmapCLM v ρ u) j + b j) ^ 2
      rw [hcoord]
      nlinarith [mul_nonneg (Real.sqrt_nonneg ρ) hR, sq_nonneg (b j)]

/-- Actual hypotheses of the affine lower-cutoff argument. No distance
estimate or Gaussian marginal law is stored as a premise. -/
structure AffineProjectedCutoffData (Ω : Type*) [MeasurableSpace Ω] (d : ℕ) where
  potential : EuclideanSpace ℝ (Fin d) → ℝ
  smooth : ContDiff ℝ 2 potential
  curvature : ℝ
  curvature_nonneg : 0 ≤ curvature
  hessian : ∀ x z, curvature * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ potential) x z z
  probability : IsProbabilityMeasure (gibbsMeasure volume potential)
  rate : ℝ
  rate_pos : 0 < rate
  driver : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d)
  noiseLaw : Measure Ω
  brownian : IsEuclideanBrownian driver noiseLaw
  coordinateCount : ℕ
  row : 0 < d → Fin coordinateCount
  coefficient : Fin coordinateCount → EuclideanSpace ℝ (Fin d)
  constant : Fin coordinateCount → ℝ
  eigenfunction : ∀ i x, langevinDifferentialOperator potential
    (fun y => inner ℝ (coefficient i) y + constant i) x =
      -rate * (inner ℝ (coefficient i) x + constant i)
  orthonormal : ∀ i j, ∫ x, (inner ℝ (coefficient i) x + constant i) *
    (inner ℝ (coefficient j) x + constant j) ∂gibbsMeasure volume potential =
      if i = j then 1 else 0

variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}

/-- Actual extended relative-entropy supremum on the source initial ball. -/
@[expose] noncomputable def affineBallKL (D : AffineProjectedCutoffData Ω d) (c t : ℝ) : ℝ≥0∞ :=
  ⨆ x : Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) (c * Real.sqrt d),
    klDiv (langevinKernel D.potential D.driver D.noiseLaw t.toNNReal x)
      (gibbsMeasure volume D.potential)

/-- Actual probability-normalized total-variation supremum on the same ball. -/
@[expose] noncomputable def affineBallTV (D : AffineProjectedCutoffData Ω d) (c t : ℝ) : ℝ :=
  sSup ((fun x => totalVariationDistance
    (langevinKernel D.potential D.driver D.noiseLaw t.toNNReal x)
    (gibbsMeasure volume D.potential)) ''
      Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) (c * Real.sqrt d))

private theorem affineTV_bddAbove (D : AffineProjectedCutoffData Ω d) (c t : ℝ) :
    BddAbove ((fun x => totalVariationDistance
      (langevinKernel D.potential D.driver D.noiseLaw t.toNNReal x)
      (gibbsMeasure volume D.potential)) ''
      Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) (c * Real.sqrt d)) := by
  let := D.probability
  let := langevinKernel_isMarkovKernel D.brownian D.smooth D.curvature D.curvature_nonneg D.hessian t.toNNReal
  refine ⟨1, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  exact totalVariationDistance_le_one _ _

/-- The genuine TV ball supremum is at most one. -/
theorem affineBallTV_le_one (D : AffineProjectedCutoffData Ω d) {c : ℝ} (hc : 0 ≤ c) (t : ℝ) :
    affineBallTV D c t ≤ 1 := by
  apply csSup_le
  · refine ⟨_, 0, ?_, rfl⟩
    simp [Metric.mem_closedBall, mul_nonneg hc (Real.sqrt_nonneg (d : ℝ))]
  · rintro _ ⟨x, hx, rfl⟩
    let := D.probability
    let := langevinKernel_isMarkovKernel D.brownian D.smooth D.curvature D.curvature_nonneg D.hessian t.toNNReal
    exact totalVariationDistance_le_one _ _

/-- The true entropy supremum is bounded below by the projected mean on an
antipodal row point. -/
theorem affineBallKL_lower (D : AffineProjectedCutoffData Ω d) (hd : 0 < d)
    {c t : ℝ} (hc : 0 ≤ c) (ht : 0 < t) :
    ENNReal.ofReal (D.rate * c ^ 2 / 2 * ((d : ℝ) * Real.exp (-2 * D.rate * t))) ≤
      affineBallKL D c t := by
  have hv := affine_eigenfunction_normalized_rows_orthonormal D.potential
    (D.smooth.differentiable (by norm_num)) D.coefficient D.constant D.rate D.rate_pos
    D.eigenfunction D.probability D.orthonormal
  obtain ⟨x, hx, hnorm⟩ := exists_ball_affine_eigenmap_norm_sq_ge hv (WithLp.toLp 2 D.constant)
    D.rate_pos.le (mul_nonneg hc (Real.sqrt_nonneg (d : ℝ))) (D.row hd)
  rw [affine_eigenfunction_eigenmap_representation D.coefficient D.constant D.rate_pos x] at hnorm
  have h := klDiv_langevinKernel_affine_mean_lower D.brownian D.smooth D.curvature
    D.curvature_nonneg D.hessian D.coefficient D.constant D.rate D.rate_pos
    D.eigenfunction D.probability D.orthonormal x t.toNNReal
    (by simpa only [Real.coe_toNNReal _ ht.le] using ht)
  rw [Real.coe_toNNReal _ ht.le] at h
  have hrsq : (c * Real.sqrt (d : ℝ)) ^ 2 = c ^ 2 * d := by
    rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg d)]
  rw [hrsq] at hnorm
  have hl : ENNReal.ofReal (D.rate * c ^ 2 / 2 * ((d : ℝ) * Real.exp (-2 * D.rate * t))) ≤
      ENNReal.ofReal (Real.exp (-2 * D.rate * t) * ‖affineEigenfunctionMap D.coefficient D.constant x‖ ^ 2 / 2) := by
    apply ENNReal.ofReal_le_ofReal
    change _ ≤ Real.exp (-2 * D.rate * t) * ‖WithLp.toLp 2 (fun i =>
      inner ℝ (D.coefficient i) x + D.constant i)‖ ^ 2 / 2
    nlinarith [mul_le_mul_of_nonneg_left hnorm (Real.exp_pos (-2 * D.rate * t)).le]
  exact hl.trans (h.trans (le_iSup (fun y : Metric.closedBall (0 : EuclideanSpace ℝ (Fin d))
    (c * Real.sqrt d) => klDiv (langevinKernel D.potential D.driver D.noiseLaw t.toNNReal y)
      (gibbsMeasure volume D.potential)) ⟨x, hx⟩))

private theorem affineTV_point_nonzero_lower (D : AffineProjectedCutoffData Ω d)
    (x : EuclideanSpace ℝ (Fin d)) (t : ℝ≥0) (j : Fin D.coordinateCount)
    (hm : inner ℝ (D.coefficient j) x + D.constant j ≠ 0) :
    1 - 8 / (Real.exp (-D.rate * (t : ℝ)) *
      (inner ℝ (D.coefficient j) x + D.constant j)) ^ 2 ≤
      totalVariationDistance (langevinKernel D.potential D.driver D.noiseLaw t x)
        (gibbsMeasure volume D.potential) := by
  have hmi : (Real.exp (-D.rate * (t : ℝ)) •
      affineEigenfunctionMap D.coefficient D.constant x) j ≠ 0 := mul_ne_zero (Real.exp_ne_zero _) hm
  have h := totalVariationDistance_affineGaussian_nonzero_lower
    (Real.exp (-D.rate * (t : ℝ)) • affineEigenfunctionMap D.coefficient D.constant x)
    (ouNoise D.rate t) (ouNoise_nonneg D.rate t) j hmi
  rw [ouNoise_sq D.rate_pos.le t.coe_nonneg] at h
  have hc : 4 * ((1 - Real.exp (-2 * D.rate * (t : ℝ))) + 1) ≤ 8 := by
    nlinarith [Real.exp_pos (-2 * D.rate * (t : ℝ))]
  have hg := (sub_le_sub_left (div_le_div_of_nonneg_right hc (sq_nonneg _)) 1).trans h
  have hp := totalVariationDistance_langevinKernel_ge_ouLaw D.brownian D.smooth D.curvature
    D.curvature_nonneg D.hessian D.coefficient D.constant D.rate D.rate_pos
    D.eigenfunction D.probability D.orthonormal x t
  rw [affineGaussian_eq_multivariateGaussian _ _ (ouNoise_nonneg D.rate t),
    ouNoise_sq D.rate_pos.le t.coe_nonneg] at hg
  rw [ouLaw_eq_multivariateGaussian D.rate_pos.le t.coe_nonneg] at hp
  convert! hg.trans hp using 1

/-- The actual TV supremum has the projected antipodal-row lower bound,
without any restriction on the affine constants. -/
theorem affineBallTV_lower (D : AffineProjectedCutoffData Ω d) (hd : 0 < d)
    {c t : ℝ} (hc : 0 < c) (ht : 0 ≤ t) :
    1 - 8 / (D.rate * c ^ 2 * ((d : ℝ) * Real.exp (-2 * D.rate * t))) ≤
      affineBallTV D c t := by
  have hv := affine_eigenfunction_normalized_rows_orthonormal D.potential
    (D.smooth.differentiable (by norm_num)) D.coefficient D.constant D.rate D.rate_pos
    D.eigenfunction D.probability D.orthonormal
  obtain ⟨x, hx, hsq⟩ := exists_ball_affine_coordinate_sq_ge hv (WithLp.toLp 2 D.constant)
    D.rate_pos.le (mul_nonneg hc.le (Real.sqrt_nonneg (d : ℝ))) (D.row hd)
  rw [affine_eigenfunction_eigenmap_representation D.coefficient D.constant D.rate_pos x] at hsq
  change D.rate * (c * Real.sqrt (d : ℝ)) ^ 2 ≤
    (inner ℝ (D.coefficient (D.row hd)) x + D.constant (D.row hd)) ^ 2 at hsq
  have hrsq : (c * Real.sqrt (d : ℝ)) ^ 2 = c ^ 2 * d := by
    rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg d)]
  rw [hrsq] at hsq
  have hbase : 0 < D.rate * c ^ 2 * ((d : ℝ) * Real.exp (-2 * D.rate * t)) := by
    exact mul_pos (mul_pos D.rate_pos (sq_pos_of_pos hc))
      (mul_pos (by exact_mod_cast hd) (Real.exp_pos _))
  have hm : inner ℝ (D.coefficient (D.row hd)) x + D.constant (D.row hd) ≠ 0 := by
    intro hz
    rw [hz, zero_pow (by norm_num : (2 : ℕ) ≠ 0)] at hsq
    have hdim : (0 : ℝ) < d := by exact_mod_cast hd
    have : 0 < D.rate * (c ^ 2 * (d : ℝ)) :=
      mul_pos D.rate_pos (mul_pos (sq_pos_of_pos hc) hdim)
    linarith
  have h := affineTV_point_nonzero_lower D x t.toNNReal (D.row hd) hm
  rw [Real.coe_toNNReal _ ht] at h
  have he : Real.exp (-D.rate * t) ^ 2 = Real.exp (-2 * D.rate * t) := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  have hden : D.rate * c ^ 2 * ((d : ℝ) * Real.exp (-2 * D.rate * t)) ≤
      (Real.exp (-D.rate * t) * (inner ℝ (D.coefficient (D.row hd)) x + D.constant (D.row hd))) ^ 2 := by
    rw [mul_pow, he]
    nlinarith [mul_le_mul_of_nonneg_left hsq (Real.exp_pos (-2 * D.rate * t)).le]
  have hl := sub_le_sub_left (div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 8) hbase hden) 1
  exact (hl.trans h).trans (le_csSup (affineTV_bddAbove D c t) ⟨x, hx, rfl⟩)


/-- The paper's positive lower limit provides a positive eventual rate bound. -/
theorem affineProjected_rates_eventually_positive_lower
    (D : ∀ n : ℕ, AffineProjectedCutoffData Ω n)
    (hliminf : 0 < liminf (fun n => (D n).rate) atTop) :
    ∃ r : ℝ, 0 < r ∧ ∀ᶠ n in atTop, r ≤ (D n).rate := by
  let r := liminf (fun n => (D n).rate) atTop / 2
  have hr : 0 < r := by dsimp [r]; positivity
  have hb : IsBoundedUnder (· ≥ ·) atTop (fun n => (D n).rate) := by
    refine ⟨0, ?_⟩
    change ∀ᶠ n : ℕ in atTop, 0 ≤ (D n).rate
    exact Filter.Eventually.of_forall (fun n => (D n).rate_pos.le)
  have he : ∀ᶠ n in atTop, r < (D n).rate :=
    eventually_lt_of_lt_liminf (show r < liminf (fun n => (D n).rate) atTop by dsimp [r]; linarith) hb
  exact ⟨r, hr, he.mono (fun _ hn => hn.le)⟩

private theorem affineProjected_early_time_pos {n : ℕ} (hn : 2 ≤ n)
    {ρ ε : ℝ} (hρ : 0 < ρ) (hε1 : ε < 1) :
    0 < (1 - ε) * criticalTime n ρ := by
  apply mul_pos (by linarith)
  unfold criticalTime
  exact div_pos (Real.log_pos (by exact_mod_cast (show 1 < n by omega))) (by positivity)

/-- The actual extended entropy supremum diverges before the logarithmic
critical time. This is the affine-eigenmap version of the paper's lower cutoff. -/
theorem affine_entropy_before_cutoff_of_eventual_rate_lower
    (D : ∀ n : ℕ, AffineProjectedCutoffData Ω n) {c ε : ℝ}
    (hc : 0 < c) (hε : 0 < ε) (hε1 : ε < 1)
    (hpositive : ∃ r : ℝ, 0 < r ∧ ∀ᶠ n in atTop, r ≤ (D n).rate) :
    Tendsto (fun n : ℕ => affineBallKL (D n) c
      ((1 - ε) * criticalTime n (D n).rate)) atTop (𝓝 ⊤) := by
  obtain ⟨r, hr, hrate⟩ := hpositive
  have hC : 0 < r * c ^ 2 / 2 := by positivity
  have hscale : Tendsto (fun n : ℕ => ENNReal.ofReal (r * c ^ 2 / 2 * (n : ℝ) ^ ε))
      atTop (𝓝 ⊤) := ENNReal.tendsto_ofReal_nhds_top.mpr
        ((power_before_cutoff hε).const_mul_atTop hC)
  apply tendsto_nhds_top_mono hscale
  filter_upwards [hrate, eventually_ge_atTop 2] with n hn hdim
  have ht := affineProjected_early_time_pos hdim (D n).rate_pos hε1
  have h := affineBallKL_lower (D n) (by omega) hc.le ht
  rw [dimension_decay_at_criticalTime n (D n).rate (1 - ε)
    (by exact_mod_cast (show 0 < n by omega)) (D n).rate_pos.ne'] at h
  simp only [show (1 : ℝ) - (1 - ε) = ε by ring] at h
  apply le_trans _ h
  apply ENNReal.ofReal_le_ofReal
  gcongr

/-- Actual total variation on the initial balls tends to one before the
critical time, by the projected Gaussian separating halfspace. -/
theorem affine_totalVariation_before_cutoff_of_eventual_rate_lower
    (D : ∀ n : ℕ, AffineProjectedCutoffData Ω n) {c ε : ℝ}
    (hc : 0 < c) (hε : 0 < ε) (hε1 : ε < 1)
    (hpositive : ∃ r : ℝ, 0 < r ∧ ∀ᶠ n in atTop, r ≤ (D n).rate) :
    Tendsto (fun n : ℕ => affineBallTV (D n) c
      ((1 - ε) * criticalTime n (D n).rate)) atTop (𝓝 1) := by
  obtain ⟨r, hr, hrate⟩ := hpositive
  have hC : 0 < r * c ^ 2 := mul_pos hr (sq_pos_of_pos hc)
  have hscale : Tendsto (fun n : ℕ => 8 / (r * c ^ 2 * (n : ℝ) ^ ε)) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero, Pi.inv_apply] using
      (((power_before_cutoff hε).const_mul_atTop hC).inv_tendsto_atTop.const_mul 8)
  have hdiff : Tendsto (fun n : ℕ => 1 - affineBallTV (D n) c
      ((1 - ε) * criticalTime n (D n).rate)) atTop (𝓝 0) := by
    apply squeeze_zero' (g := fun n : ℕ => 8 / (r * c ^ 2 * (n : ℝ) ^ ε))
    · exact Filter.Eventually.of_forall (fun n => sub_nonneg.mpr (affineBallTV_le_one (D n) hc.le _))
    · filter_upwards [hrate, eventually_ge_atTop 2] with n hn hdim
      have ht := affineProjected_early_time_pos hdim (D n).rate_pos hε1
      have h := affineBallTV_lower (D n) (by omega) hc ht.le
      rw [dimension_decay_at_criticalTime n (D n).rate (1 - ε)
        (by exact_mod_cast (show 0 < n by omega)) (D n).rate_pos.ne'] at h
      simp only [show (1 : ℝ) - (1 - ε) = ε by ring] at h
      have hpow : 0 < (n : ℝ) ^ ε := Real.rpow_pos_of_pos
        (by exact_mod_cast (show 0 < n by omega)) _
      have hden : r * c ^ 2 * (n : ℝ) ^ ε ≤ (D n).rate * c ^ 2 * (n : ℝ) ^ ε := by gcongr
      have hdiv := div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 8)
        (mul_pos hC hpow) hden
      linarith
    · exact hscale
  have h := (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)).sub hdiff
  simpa only [sub_sub_cancel, sub_zero] using h


/-- Real-liminf formulation of the actual entropy lower cutoff. The stronger
preceding theorem also covers rates diverging to infinity. -/
theorem affine_entropy_before_cutoff
    (D : ∀ n : ℕ, AffineProjectedCutoffData Ω n) {c ε : ℝ}
    (hc : 0 < c) (hε : 0 < ε) (hε1 : ε < 1)
    (hliminf : 0 < liminf (fun n => (D n).rate) atTop) :
    Tendsto (fun n : ℕ => affineBallKL (D n) c
      ((1 - ε) * criticalTime n (D n).rate)) atTop (𝓝 ⊤) :=
  affine_entropy_before_cutoff_of_eventual_rate_lower D hc hε hε1
    (affineProjected_rates_eventually_positive_lower D hliminf)

/-- Real-liminf formulation of the actual total-variation lower cutoff. -/
theorem affine_totalVariation_before_cutoff
    (D : ∀ n : ℕ, AffineProjectedCutoffData Ω n) {c ε : ℝ}
    (hc : 0 < c) (hε : 0 < ε) (hε1 : ε < 1)
    (hliminf : 0 < liminf (fun n => (D n).rate) atTop) :
    Tendsto (fun n : ℕ => affineBallTV (D n) c
      ((1 - ε) * criticalTime n (D n).rate)) atTop (𝓝 1) :=
  affine_totalVariation_before_cutoff_of_eventual_rate_lower D hc hε hε1
    (affineProjected_rates_eventually_positive_lower D hliminf)

end CutoffRigidity
