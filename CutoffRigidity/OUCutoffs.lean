module

public import CutoffRigidity.OUWassersteinCutoff
public import CutoffRigidity.GaussianEntropy
public import CutoffRigidity.Pinsker

/-!
# Entropy and total variation cutoff for the actual unit-rate OU kernel

This proves the pure OU special case on the paper's initial balls of radius
`c sqrt n`, using actual Mehler measures, genuine relative entropy and genuine
total variation. The general curved-diffusion corollary is a separate target.
-/

public section

namespace CutoffRigidity

open MeasureTheory ProbabilityTheory InformationTheory Filter Topology
open scoped ENNReal

/-- The Gaussian covariance contribution to entropy is nonnegative. -/
theorem gaussian_entropy_correction_nonneg {q : ℝ} (hq : q < 1) :
    0 ≤ -q - Real.log (1 - q) := by
  have h := Real.log_le_sub_one_of_pos (sub_pos.mpr hq)
  linarith

/-- A uniform upper bound for the small covariance correction. -/
theorem gaussian_entropy_correction_le {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1 / 2) :
    -q - Real.log (1 - q) ≤ q := by
  have hp : 0 < 1 - q := by linarith
  have hlog := Real.one_sub_inv_le_log_of_pos hp
  have hinv : (1 - q)⁻¹ ≤ 1 + 2 * q := by
    rw [inv_eq_one_div]
    apply (div_le_iff₀ hp).mpr
    nlinarith [mul_nonneg hq0 (show 0 ≤ 1 - 2 * q by linarith)]
  linarith

/-- Exact genuine relative entropy of the unit-rate Mehler law. -/
theorem klDiv_ouLaw {n : ℕ} (x : EuclideanSpace ℝ (Fin n)) {t : ℝ} (ht : 0 < t) :
    klDiv (ouLaw 1 t x) (stdGaussian (EuclideanSpace ℝ (Fin n))) =
      ENNReal.ofReal ((Real.exp (-2 * t) * ‖x‖ ^ 2 +
        n * (-Real.exp (-2 * t) - Real.log (1 - Real.exp (-2 * t)))) / 2) := by
  rw [ouLaw_eq_multivariateGaussian (by norm_num) ht.le]
  simpa only [mul_one] using klDiv_ou_marginal n x 1 t (by norm_num) ht

/-- The Gaussian entropy formula is finite and nonnegative at positive times. -/
theorem klDiv_ouLaw_toReal {n : ℕ} (x : EuclideanSpace ℝ (Fin n)) {t : ℝ} (ht : 0 < t) :
    (klDiv (ouLaw 1 t x) (stdGaussian (EuclideanSpace ℝ (Fin n)))).toReal =
      (Real.exp (-2 * t) * ‖x‖ ^ 2 +
        n * (-Real.exp (-2 * t) - Real.log (1 - Real.exp (-2 * t)))) / 2 := by
  rw [klDiv_ouLaw x ht, ENNReal.toReal_ofReal]
  have hcorr := gaussian_entropy_correction_nonneg
    (Real.exp_lt_one_iff.mpr (show -2 * t < 0 by linarith))
  positivity

/-- The actual relative-entropy supremum over the initial ball. -/
@[expose] noncomputable def ouBallEntropy (n : ℕ) (c t : ℝ) : ℝ :=
  sSup ((fun x : EuclideanSpace ℝ (Fin n) =>
    (klDiv (ouLaw 1 t x) (stdGaussian (EuclideanSpace ℝ (Fin n)))).toReal) ''
      Metric.closedBall 0 (c * Real.sqrt n))

/-- The finite Gaussian entropy supremum is attained on the boundary of the ball. -/
theorem ouBallEntropy_isGreatest {n : ℕ} (hn : 0 < n) {c t : ℝ}
    (hc : 0 ≤ c) (ht : 0 < t) :
    IsGreatest ((fun x : EuclideanSpace ℝ (Fin n) =>
      (klDiv (ouLaw 1 t x) (stdGaussian (EuclideanSpace ℝ (Fin n)))).toReal) ''
        Metric.closedBall 0 (c * Real.sqrt n))
      ((c ^ 2 * n * Real.exp (-2 * t) +
        n * (-Real.exp (-2 * t) - Real.log (1 - Real.exp (-2 * t)))) / 2) := by
  have hR : 0 ≤ c * Real.sqrt (n : ℝ) := mul_nonneg hc (Real.sqrt_nonneg _)
  have hRsq : (c * Real.sqrt (n : ℝ)) ^ 2 = c ^ 2 * n := by
    rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg n)]
  have hnrm : ‖EuclideanSpace.single (⟨0, hn⟩ : Fin n) (c * Real.sqrt n)‖ =
      c * Real.sqrt (n : ℝ) := by
    simp [PiLp.norm_single, abs_of_nonneg hc, abs_of_nonneg (Real.sqrt_nonneg _)]
  constructor
  · refine ⟨EuclideanSpace.single (⟨0, hn⟩ : Fin n) (c * Real.sqrt n), ?_, ?_⟩
    · simpa only [Metric.mem_closedBall, dist_zero_right, hnrm] using
        (le_rfl : c * Real.sqrt (n : ℝ) ≤ c * Real.sqrt (n : ℝ))
    · dsimp only
      rw [klDiv_ouLaw_toReal _ ht, hnrm, hRsq]
      ring
  · rintro _ ⟨x, hx, rfl⟩
    dsimp only
    rw [klDiv_ouLaw_toReal _ ht]
    have hxR : ‖x‖ ≤ c * Real.sqrt (n : ℝ) := by
      simpa only [Metric.mem_closedBall, dist_zero_right] using hx
    have hxSq : ‖x‖ ^ 2 ≤ c ^ 2 * n := by
      rw [← hRsq]
      exact (sq_le_sq₀ (norm_nonneg _) hR).mpr hxR
    nlinarith [Real.exp_pos (-2 * t)]

/-- Exact finite entropy supremum of the genuine Mehler laws. -/
theorem ouBallEntropy_eq {n : ℕ} (hn : 0 < n) {c t : ℝ} (hc : 0 ≤ c) (ht : 0 < t) :
    ouBallEntropy n c t = (c ^ 2 * n * Real.exp (-2 * t) +
      n * (-Real.exp (-2 * t) - Real.log (1 - Real.exp (-2 * t)))) / 2 :=
  (ouBallEntropy_isGreatest hn hc ht).csSup_eq

/-- The mean contribution supplies the pre-cutoff entropy lower bound. -/
theorem ouBallEntropy_lower {n : ℕ} (hn : 0 < n) {c t : ℝ} (hc : 0 ≤ c) (ht : 0 < t) :
    c ^ 2 / 2 * ((n : ℝ) * Real.exp (-2 * t)) ≤ ouBallEntropy n c t := by
  rw [ouBallEntropy_eq hn hc ht]
  have hcorr := gaussian_entropy_correction_nonneg
    (Real.exp_lt_one_iff.mpr (show -2 * t < 0 by linarith))
  nlinarith [Nat.cast_nonneg (α := ℝ) n]

/-- Once the covariance correction is small, entropy has the paper's exponential upper scale. -/
theorem ouBallEntropy_upper {n : ℕ} (hn : 0 < n) {c t : ℝ} (hc : 0 ≤ c) (ht : 0 < t)
    (hq : Real.exp (-2 * t) ≤ 1 / 2) :
    ouBallEntropy n c t ≤ (c ^ 2 + 1) * ((n : ℝ) * Real.exp (-2 * t)) := by
  rw [ouBallEntropy_eq hn hc ht]
  have hcorr := gaussian_entropy_correction_le (Real.exp_pos _).le hq
  have hm := mul_le_mul_of_nonneg_left hcorr (Nat.cast_nonneg (α := ℝ) n)
  have hmean := mul_nonneg (sq_nonneg c)
    (mul_nonneg (Nat.cast_nonneg (α := ℝ) n) (Real.exp_pos (-2 * t)).le)
  have hnq : 0 ≤ (n : ℝ) * Real.exp (-2 * t) := by positivity
  nlinarith

private theorem ou_criticalTime_pos {n : ℕ} (hn : 2 ≤ n) : 0 < criticalTime n 1 := by
  unfold criticalTime
  apply div_pos
  · exact Real.log_pos (by exact_mod_cast (show 1 < n by omega))
  · norm_num

/-- Genuine OU relative entropy diverges before the critical time. -/
theorem ou_entropy_before_cutoff {c ε : ℝ} (hc : 0 < c) (hε : 0 < ε) (hε1 : ε < 1) :
    Tendsto (fun n : ℕ => ouBallEntropy n c ((1 - ε) * criticalTime n 1)) atTop atTop := by
  apply exponential_lower_cutoff (c := c ^ 2 / 2) (rate := fun _ => 1)
    (by positivity) hε (fun _ => one_ne_zero)
  filter_upwards [eventually_ge_atTop 2] with n hn
  simpa only [mul_one] using ouBallEntropy_lower (by omega) hc.le
    (mul_pos (by linarith) (ou_criticalTime_pos hn))

private theorem ou_late_decay_eventually_le_half {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop,
      Real.exp (-2 * ((1 + ε) * criticalTime n 1)) ≤ 1 / 2 := by
  have h : Tendsto (fun n : ℕ => Real.exp (-2 * ((1 + ε) * criticalTime n 1))) atTop (𝓝 0) := by
    apply (power_after_cutoff (ε := 1 + ε) (by linarith)).congr'
    filter_upwards [eventually_ge_atTop 1] with n hn
    symm
    simpa only [mul_one] using decay_at_criticalTime n 1 (1 + ε)
      (by exact_mod_cast (show 0 < n by omega)) one_ne_zero
  filter_upwards [h.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))] with n hn
  exact hn.le

/-- Genuine OU relative entropy vanishes after the critical time. -/
theorem ou_entropy_after_cutoff {c ε : ℝ} (hc : 0 ≤ c) (hε : 0 < ε) :
    Tendsto (fun n : ℕ => ouBallEntropy n c ((1 + ε) * criticalTime n 1)) atTop (𝓝 0) := by
  apply exponential_upper_cutoff (C := c ^ 2 + 1) (rate := fun _ => 1)
    hε (fun _ => one_ne_zero)
  · filter_upwards [eventually_ge_atTop 2] with n hn
    have ht := mul_pos (show 0 < 1 + ε by linarith) (ou_criticalTime_pos hn)
    rw [ouBallEntropy_eq (by omega) hc ht]
    have hcorr := gaussian_entropy_correction_nonneg
      (Real.exp_lt_one_iff.mpr (show -2 * ((1 + ε) * criticalTime n 1) < 0 by linarith))
    positivity
  · filter_upwards [eventually_ge_atTop 2, ou_late_decay_eventually_le_half hε] with n hn hq
    simpa only [mul_one] using ouBallEntropy_upper (by omega) hc
      (mul_pos (by linarith) (ou_criticalTime_pos hn)) hq

/-- The actual total variation supremum over the initial ball. -/
@[expose] noncomputable def ouBallTotalVariation (n : ℕ) (c t : ℝ) : ℝ :=
  sSup ((fun x : EuclideanSpace ℝ (Fin n) =>
    totalVariationDistance (ouLaw 1 t x) (stdGaussian (EuclideanSpace ℝ (Fin n)))) ''
      Metric.closedBall 0 (c * Real.sqrt n))

private theorem ouTV_values_nonempty (n : ℕ) {c : ℝ} (hc : 0 ≤ c) (t : ℝ) :
    ((fun x : EuclideanSpace ℝ (Fin n) =>
      totalVariationDistance (ouLaw 1 t x) (stdGaussian (EuclideanSpace ℝ (Fin n)))) ''
        Metric.closedBall 0 (c * Real.sqrt n)).Nonempty := by
  refine ⟨_, 0, ?_, rfl⟩
  simp only [Metric.mem_closedBall, dist_self]
  positivity

private theorem ouTV_values_bddAbove (n : ℕ) (c t : ℝ) :
    BddAbove ((fun x : EuclideanSpace ℝ (Fin n) =>
      totalVariationDistance (ouLaw 1 t x) (stdGaussian (EuclideanSpace ℝ (Fin n)))) ''
        Metric.closedBall 0 (c * Real.sqrt n)) := by
  refine ⟨1, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  exact totalVariationDistance_le_one _ _

/-- The supremum retains the probability normalization `0 ≤ TV ≤ 1`. -/
theorem ouBallTotalVariation_bounds (n : ℕ) {c : ℝ} (hc : 0 ≤ c) (t : ℝ) :
    0 ≤ ouBallTotalVariation n c t ∧ ouBallTotalVariation n c t ≤ 1 := by
  constructor
  · obtain ⟨r, hr⟩ := ouTV_values_nonempty n hc t
    obtain ⟨x, hx, rfl⟩ := hr
    exact (totalVariationDistance_nonneg _ _).trans
      (le_csSup (ouTV_values_bddAbove n c t) ⟨x, hx, rfl⟩)
  · apply csSup_le (ouTV_values_nonempty n hc t)
    rintro _ ⟨x, hx, rfl⟩
    exact totalVariationDistance_le_one _ _

/-- Pinsker's inequality gives a uniform upper bound on the actual TV supremum. -/
theorem ouBallTotalVariation_le_sqrt_entropy {n : ℕ} (hn : 0 < n) {c t : ℝ}
    (hc : 0 ≤ c) (ht : 0 < t) :
    ouBallTotalVariation n c t ≤ Real.sqrt (ouBallEntropy n c t / 2) := by
  have hH : 0 ≤ ouBallEntropy n c t :=
    (by positivity : 0 ≤ c ^ 2 / 2 * ((n : ℝ) * Real.exp (-2 * t))).trans
      (ouBallEntropy_lower hn hc ht)
  apply csSup_le (ouTV_values_nonempty n hc t)
  rintro _ ⟨x, hx, rfl⟩
  have hKL : klDiv (ouLaw 1 t x) (stdGaussian (EuclideanSpace ℝ (Fin n))) ≠ ∞ := by
    rw [klDiv_ouLaw x ht]
    exact ENNReal.ofReal_ne_top
  have hPinsker := totalVariationDistance_sq_le_klDiv_toReal
    (ouLaw 1 t x) (stdGaussian (EuclideanSpace ℝ (Fin n))) hKL
  have hEnt : (klDiv (ouLaw 1 t x) (stdGaussian (EuclideanSpace ℝ (Fin n)))).toReal ≤
      ouBallEntropy n c t := by
    rw [ouBallEntropy_eq hn hc ht]
    exact (ouBallEntropy_isGreatest hn hc ht).2 ⟨x, hx, rfl⟩
  apply (sq_le_sq₀ (totalVariationDistance_nonneg _ _) (Real.sqrt_nonneg _)).mp
  rw [Real.sq_sqrt (div_nonneg hH (by norm_num))]
  linarith

/-- Genuine OU total variation vanishes after the critical time. -/
theorem ou_totalVariation_after_cutoff {c ε : ℝ} (hc : 0 ≤ c) (hε : 0 < ε) :
    Tendsto (fun n : ℕ => ouBallTotalVariation n c ((1 + ε) * criticalTime n 1))
      atTop (𝓝 0) := by
  apply squeeze_zero'
    (Filter.Eventually.of_forall fun n => (ouBallTotalVariation_bounds n hc _).1)
    (by
      filter_upwards [eventually_ge_atTop 2] with n hn
      exact ouBallTotalVariation_le_sqrt_entropy (by omega) hc
        (mul_pos (by linarith) (ou_criticalTime_pos hn)))
  simpa only [div_zero, zero_div, Real.sqrt_zero] using
    ((ou_entropy_after_cutoff hc hε).div_const 2).sqrt

/-- Coordinate expectation of the actual normalized OU law. -/
theorem integral_eval_ouLaw {n : ℕ} (x : EuclideanSpace ℝ (Fin n)) (t : ℝ) (i : Fin n) :
    ∫ y, y i ∂ouLaw 1 t x = Real.exp (-t) * x i := by
  have : IsGaussian (ouLaw 1 t x) := by unfold ouLaw; infer_instance
  have h := (EuclideanSpace.proj (𝕜 := ℝ) i).integral_comp_comm
    (IsGaussian.integrable_id (μ := ouLaw 1 t x))
  simpa [integral_id_ouLaw] using h

/-- An initial boundary point and its separating coordinate give a genuine TV
lower bound; no lower bound is inferred from entropy. -/
theorem ouBallTotalVariation_lower {n : ℕ} (hn : 0 < n) {c t : ℝ}
    (hc : 0 < c) (ht : 0 < t) :
    1 - 8 / (c ^ 2 * n * Real.exp (-2 * t)) ≤ ouBallTotalVariation n c t := by
  let j : Fin n := ⟨0, hn⟩
  let R : ℝ := c * Real.sqrt n
  let x₀ : EuclideanSpace ℝ (Fin n) := EuclideanSpace.single j R
  let m : ℝ := Real.exp (-t) * R
  have hR : 0 < R := mul_pos hc (Real.sqrt_pos.mpr (by exact_mod_cast hn))
  have hm : 0 < m := mul_pos (Real.exp_pos _) hR
  have hxball : x₀ ∈ Metric.closedBall 0 (c * Real.sqrt n) := by
    simp only [Metric.mem_closedBall, dist_zero_right]
    change ‖EuclideanSpace.single j R‖ ≤ R
    simp [PiLp.norm_single, abs_of_pos hR]
  have hGaussian : IsGaussian (ouLaw 1 t x₀) := by unfold ouLaw; infer_instance
  have hXμ : MemLp (fun y : EuclideanSpace ℝ (Fin n) => y j) 2 (ouLaw 1 t x₀) := by
    simpa using IsGaussian.memLp_dual (ouLaw 1 t x₀) (EuclideanSpace.proj j) 2 (by norm_num)
  have hXν : MemLp (fun y : EuclideanSpace ℝ (Fin n) => y j) 2
      (stdGaussian (EuclideanSpace ℝ (Fin n))) := by
    simpa using IsGaussian.memLp_dual (stdGaussian (EuclideanSpace ℝ (Fin n)))
      (EuclideanSpace.proj j) 2 (by norm_num)
  have hmeanμ : (∫ y, y j ∂ouLaw 1 t x₀) = m := by
    rw [integral_eval_ouLaw]
    simp [x₀, m]
  have hmeanν : (∫ y : EuclideanSpace ℝ (Fin n), y j ∂stdGaussian (EuclideanSpace ℝ (Fin n))) = 0 := by
    simpa using integral_eval_affineGaussian (0 : EuclideanSpace ℝ (Fin n)) 1 (by norm_num) j
  have hvarμ := variance_eval_ouLaw (by norm_num : (0 : ℝ) ≤ 1) ht.le x₀ j
  simp only [mul_one] at hvarμ
  have hvarν : variance (fun y : EuclideanSpace ℝ (Fin n) => y j)
      (stdGaussian (EuclideanSpace ℝ (Fin n))) = 1 := by
    simpa using variance_eval_affineGaussian (0 : EuclideanSpace ℝ (Fin n)) 1 (by norm_num) j
  have hsep := totalVariationDistance_ge_mean_separation (ouLaw 1 t x₀)
    (stdGaussian (EuclideanSpace ℝ (Fin n))) (fun y => y j) (by fun_prop)
    hXμ hXν hm hmeanμ hmeanν
  rw [hvarμ, hvarν] at hsep
  have hcoeff : 4 * ((1 - Real.exp (-2 * t)) + 1) ≤ 8 := by
    linarith [Real.exp_pos (-2 * t)]
  have hfrac := div_le_div_of_nonneg_right hcoeff (sq_nonneg m)
  have hmSq : m ^ 2 = c ^ 2 * n * Real.exp (-2 * t) := by
    dsimp [m, R]
    rw [mul_pow, mul_pow, Real.sq_sqrt (Nat.cast_nonneg n)]
    have he : Real.exp (-t) ^ 2 = Real.exp (-2 * t) := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    rw [he]
    ring
  have hpoint : totalVariationDistance (ouLaw 1 t x₀) (stdGaussian (EuclideanSpace ℝ (Fin n))) ≤
      ouBallTotalVariation n c t :=
    le_csSup (ouTV_values_bddAbove n c t) ⟨x₀, hxball, rfl⟩
  rw [← hmSq]
  linarith

/-- Genuine OU total variation tends to one before the critical time. -/
theorem ou_totalVariation_before_cutoff {c ε : ℝ}
    (hc : 0 < c) (hε : 0 < ε) (hε1 : ε < 1) :
    Tendsto (fun n : ℕ => ouBallTotalVariation n c ((1 - ε) * criticalTime n 1))
      atTop (𝓝 1) := by
  have hscale : Tendsto (fun n : ℕ => 8 / (c ^ 2 * (n : ℝ) ^ ε)) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero, Pi.inv_apply] using
      (((power_before_cutoff hε).const_mul_atTop (sq_pos_of_pos hc)).inv_tendsto_atTop.const_mul 8)
  have hdiff : Tendsto (fun n : ℕ =>
      1 - ouBallTotalVariation n c ((1 - ε) * criticalTime n 1)) atTop (𝓝 0) := by
    apply squeeze_zero' (g := fun n : ℕ => 8 / (c ^ 2 * (n : ℝ) ^ ε))
    · exact Filter.Eventually.of_forall fun n => sub_nonneg.mpr
        (ouBallTotalVariation_bounds n hc.le _).2
    · filter_upwards [eventually_ge_atTop 2] with n hn
      have ht := mul_pos (show 0 < 1 - ε by linarith) (ou_criticalTime_pos hn)
      have h := ouBallTotalVariation_lower (n := n) (by omega) hc ht
      have he : c ^ 2 * (n : ℝ) * Real.exp (-2 * ((1 - ε) * criticalTime n 1)) =
          c ^ 2 * (n : ℝ) ^ ε := by
        rw [mul_assoc]
        have hd := dimension_decay_at_criticalTime n 1 (1 - ε)
          (by exact_mod_cast (show 0 < n by omega)) one_ne_zero
        simp only [mul_one, show (1 : ℝ) - (1 - ε) = ε by ring] at hd
        rw [hd]
      rw [he] at h
      linarith
    · exact hscale
  have h := (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)).sub hdiff
  simpa only [sub_sub_cancel, sub_zero] using h

end CutoffRigidity
