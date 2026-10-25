module

public import CutoffRigidity.OUKernel
public import CutoffRigidity.Asymptotics
public import CutoffRigidity.OUProfiles

/-!
# Wasserstein cutoff for the genuine OU kernels on Euclidean balls

This is the pure Ornstein--Uhlenbeck, unit-rate special case of the paper's
Wasserstein cutoff argument. The quantity being optimized is the actual
coupling infimum for the actual Mehler probability measures. The general
curved-diffusion corollary still requires its analytic and stochastic inputs.
-/

public section

namespace CutoffRigidity

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

/-- The actual squared equilibrium transport cost of the unit-rate OU kernel. -/
theorem squaredWasserstein_ouLaw_toReal {n : ℕ} (t : ℝ)
    (x : EuclideanSpace ℝ (Fin n)) :
    (squaredWasserstein (ouLaw 1 t x) (stdGaussian (EuclideanSpace ℝ (Fin n)))).toReal =
      Real.exp (-2 * t) * ‖x‖ ^ 2 +
        (n : ℝ) * (1 - Real.sqrt (1 - Real.exp (-2 * t))) ^ 2 := by
  rw [squaredWasserstein_ouLaw]
  simp only [mul_one, Fintype.card_fin]
  rw [ENNReal.toReal_ofReal]
  positivity

/-- The real supremum is finite: it is taken over a bounded closed ball, and
its transport costs have the explicit finite Gaussian formula. -/
@[expose] noncomputable def ouBallSquaredWasserstein (n : ℕ) (c t : ℝ) : ℝ :=
  sSup ((fun x : EuclideanSpace ℝ (Fin n) =>
    (squaredWasserstein (ouLaw 1 t x) (stdGaussian (EuclideanSpace ℝ (Fin n)))).toReal) ''
      Metric.closedBall 0 (c * Real.sqrt n))

/-- The exact squared cost supremum is attained along a coordinate direction. -/
theorem ouBallSquaredWasserstein_isGreatest {n : ℕ} (hn : 0 < n)
    {c : ℝ} (hc : 0 ≤ c) (t : ℝ) :
    IsGreatest ((fun x : EuclideanSpace ℝ (Fin n) =>
      (squaredWasserstein (ouLaw 1 t x) (stdGaussian (EuclideanSpace ℝ (Fin n)))).toReal) ''
        Metric.closedBall 0 (c * Real.sqrt n))
      (c ^ 2 * n * Real.exp (-2 * t) +
        n * (1 - Real.sqrt (1 - Real.exp (-2 * t))) ^ 2) := by
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
      rw [squaredWasserstein_ouLaw_toReal, hnrm, hRsq]
      ring
  · rintro _ ⟨x, hx, rfl⟩
    dsimp only
    rw [squaredWasserstein_ouLaw_toReal]
    have hxR : ‖x‖ ≤ c * Real.sqrt (n : ℝ) := by
      simpa only [Metric.mem_closedBall, dist_zero_right] using hx
    have hxSq : ‖x‖ ^ 2 ≤ c ^ 2 * n := by
      rw [← hRsq]
      exact (sq_le_sq₀ (norm_nonneg _) hR).mpr hxR
    nlinarith [Real.exp_pos (-2 * t)]

/-- Exact finite ball supremum for the actual OU equilibrium transport cost. -/
theorem ouBallSquaredWasserstein_eq {n : ℕ} (hn : 0 < n)
    {c : ℝ} (hc : 0 ≤ c) (t : ℝ) :
    ouBallSquaredWasserstein n c t = c ^ 2 * n * Real.exp (-2 * t) +
      n * (1 - Real.sqrt (1 - Real.exp (-2 * t))) ^ 2 :=
  (ouBallSquaredWasserstein_isGreatest hn hc t).csSup_eq

/-- The lower and upper exponential bounds used in the paper's cutoff proof,
now discharged for the genuine unit-rate OU measures. -/
theorem ouBallSquaredWasserstein_bounds {n : ℕ} (hn : 0 < n)
    {c t : ℝ} (hc : 0 ≤ c) (ht : 0 ≤ t) :
    c ^ 2 * ((n : ℝ) * Real.exp (-2 * t)) ≤ ouBallSquaredWasserstein n c t ∧
      ouBallSquaredWasserstein n c t ≤ (c ^ 2 + 1) * ((n : ℝ) * Real.exp (-2 * t)) := by
  rw [ouBallSquaredWasserstein_eq hn hc]
  have hq0 : 0 ≤ Real.exp (-2 * t) := (Real.exp_pos _).le
  have hq1 : Real.exp (-2 * t) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hcor := gaussian_variance_correction_le hq0 hq1
  constructor
  · nlinarith [sq_nonneg (1 - Real.sqrt (1 - Real.exp (-2 * t)))]
  · nlinarith [Nat.cast_nonneg (α := ℝ) n]

/-- Before the critical time, the genuine OU squared Wasserstein supremum diverges. -/
theorem ou_squaredWasserstein_before_cutoff {c ε : ℝ}
    (hc : 0 < c) (hε : 0 < ε) (hε1 : ε < 1) :
    Tendsto (fun n : ℕ =>
      ouBallSquaredWasserstein n c ((1 - ε) * criticalTime n 1)) atTop atTop := by
  apply exponential_lower_cutoff (c := c ^ 2) (rate := fun _ => 1)
    (sq_pos_of_pos hc) hε (fun _ => one_ne_zero)
  filter_upwards [eventually_ge_atTop 1] with n hn
  have ht : 0 ≤ (1 - ε) * criticalTime n 1 := by
    apply mul_nonneg (by linarith)
    unfold criticalTime
    exact div_nonneg (Real.log_nonneg (by exact_mod_cast hn)) (by norm_num)
  simpa only [mul_one] using
    (ouBallSquaredWasserstein_bounds (by omega) hc.le ht).1

/-- After the critical time, the genuine OU squared Wasserstein supremum vanishes. -/
theorem ou_squaredWasserstein_after_cutoff {c ε : ℝ} (hc : 0 ≤ c) (hε : 0 < ε) :
    Tendsto (fun n : ℕ =>
      ouBallSquaredWasserstein n c ((1 + ε) * criticalTime n 1)) atTop (𝓝 0) := by
  apply exponential_upper_cutoff (C := c ^ 2 + 1) (rate := fun _ => 1)
    hε (fun _ => one_ne_zero)
  · filter_upwards [eventually_ge_atTop 1] with n hn
    rw [ouBallSquaredWasserstein_eq (by omega) hc]
    positivity
  · filter_upwards [eventually_ge_atTop 1] with n hn
    have ht : 0 ≤ (1 + ε) * criticalTime n 1 := by
      apply mul_nonneg (by linarith)
      unfold criticalTime
      exact div_nonneg (Real.log_nonneg (by exact_mod_cast hn)) (by norm_num)
    simpa only [mul_one] using
      (ouBallSquaredWasserstein_bounds (by omega) hc ht).2

/-- Supremum of the actual real Wasserstein distances on the same initial ball.
The Gaussian costs are finite, so taking the real square root is unambiguous. -/
@[expose] noncomputable def ouBallWasserstein (n : ℕ) (c t : ℝ) : ℝ :=
  sSup ((fun x : EuclideanSpace ℝ (Fin n) =>
    Real.sqrt ((squaredWasserstein (ouLaw 1 t x)
      (stdGaussian (EuclideanSpace ℝ (Fin n)))).toReal)) ''
        Metric.closedBall 0 (c * Real.sqrt n))

/-- Attainment of the squared supremum justifies moving the square root outside. -/
theorem ouBallWasserstein_eq_sqrt {n : ℕ} (hn : 0 < n)
    {c : ℝ} (hc : 0 ≤ c) (t : ℝ) :
    ouBallWasserstein n c t = Real.sqrt (ouBallSquaredWasserstein n c t) := by
  have hmax := ouBallSquaredWasserstein_isGreatest hn hc t
  have hgreat : IsGreatest ((fun x : EuclideanSpace ℝ (Fin n) =>
      Real.sqrt ((squaredWasserstein (ouLaw 1 t x)
        (stdGaussian (EuclideanSpace ℝ (Fin n)))).toReal)) ''
          Metric.closedBall 0 (c * Real.sqrt n))
      (Real.sqrt (c ^ 2 * n * Real.exp (-2 * t) +
        n * (1 - Real.sqrt (1 - Real.exp (-2 * t))) ^ 2)) := by
    constructor
    · obtain ⟨x, hx, heq⟩ := hmax.1
      exact ⟨x, hx, congrArg Real.sqrt heq⟩
    · rintro _ ⟨x, hx, rfl⟩
      exact Real.sqrt_le_sqrt (hmax.2 ⟨x, hx, rfl⟩)
  rw [ouBallSquaredWasserstein_eq hn hc]
  exact hgreat.csSup_eq

/-- The actual OU Wasserstein supremum diverges before the critical time. -/
theorem ou_wasserstein_before_cutoff {c ε : ℝ}
    (hc : 0 < c) (hε : 0 < ε) (hε1 : ε < 1) :
    Tendsto (fun n : ℕ =>
      ouBallWasserstein n c ((1 - ε) * criticalTime n 1)) atTop atTop := by
  have h := Real.tendsto_sqrt_atTop.comp (ou_squaredWasserstein_before_cutoff hc hε hε1)
  apply h.congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  exact (ouBallWasserstein_eq_sqrt (by omega) hc.le _).symm

/-- The actual OU Wasserstein supremum vanishes after the critical time. -/
theorem ou_wasserstein_after_cutoff {c ε : ℝ} (hc : 0 ≤ c) (hε : 0 < ε) :
    Tendsto (fun n : ℕ =>
      ouBallWasserstein n c ((1 + ε) * criticalTime n 1)) atTop (𝓝 0) := by
  have h : Tendsto (fun n : ℕ => Real.sqrt
      (ouBallSquaredWasserstein n c ((1 + ε) * criticalTime n 1))) atTop (𝓝 0) := by
    simpa only [Function.comp_def, Real.sqrt_zero] using (Real.continuous_sqrt.tendsto 0).comp
      (ou_squaredWasserstein_after_cutoff hc hε)
  apply h.congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  exact (ouBallWasserstein_eq_sqrt (by omega) hc _).symm

end CutoffRigidity
