module

public import CutoffRigidity.AffineWassersteinEstimate
public import CutoffRigidity.Asymptotics

/-! # Classical affine eigenmap and Poincaré Wasserstein cutoff

This follows the proof of Corollary `cor_cutoff_langevin_general`: apply the
actual Poincaré functional inequality to coordinates, use the genuine kernel
ball bounds, and evaluate the resulting powers at the logarithmic time.
The data below describe actual potentials, Brownian drivers, invariant Gibbs
laws and affine PDE eigenfunctions. Matching this classical affine framework
with the full first L² eigenspace and its spectral gap remains separate.
-/

public section

namespace CutoffRigidity

open Set MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

/-- The actual smooth Poincaré functional inequality, with its analytic domain
visible. It is not a scalar moment-bound premise. -/
@[expose] def HasSmoothPoincare {d : ℕ}
    (μ : Measure (EuclideanSpace ℝ (Fin d))) (rate : ℝ) : Prop :=
  ∀ f : EuclideanSpace ℝ (Fin d) → ℝ, ContDiff ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) f → MemLp f 2 μ →
    Integrable (fun x => ‖gradient f x‖ ^ 2) μ → (∫ x, f x ∂μ) = 0 →
    (∫ x, f x ^ 2 ∂μ) ≤ (∫ x, ‖gradient f x‖ ^ 2 ∂μ) / rate

/-- Applying the genuine Poincaré inequality to actual Euclidean coordinates
proves the second-moment bound used in the source corollary. -/
theorem second_moment_le_of_smoothPoincare {d : ℕ}
    (μ : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure μ]
    (rate : ℝ) (hLp : MemLp (fun x => x) 2 μ)
    (hcenter : ∫ x, x ∂μ = 0) (hP : HasSmoothPoincare μ rate) :
    (∫ x, ‖x‖ ^ 2 ∂μ) ≤ d / rate := by
  have hcoord (i : Fin d) : MemLp (fun x : EuclideanSpace ℝ (Fin d) => x i) 2 μ :=
    hLp.of_le_mul (c := 1) (by fun_prop) (Filter.Eventually.of_forall (fun x => by
      simpa only [one_mul] using PiLp.norm_apply_le x i))
  have hmean (i : Fin d) : (∫ x : EuclideanSpace ℝ (Fin d), x i ∂μ) = 0 := by
    have h := (EuclideanSpace.proj (𝕜 := ℝ) i).integral_comp_comm
      (hLp.integrable (by norm_num))
    simpa [hcenter] using h
  have hbound (i : Fin d) : (∫ x : EuclideanSpace ℝ (Fin d), (x i) ^ 2 ∂μ) ≤ 1 / rate := by
    have hgrad (x : EuclideanSpace ℝ (Fin d)) :
        gradient (fun y : EuclideanSpace ℝ (Fin d) => y i) x = EuclideanSpace.single i 1 := by
      simpa only [EuclideanSpace.inner_single_left, map_one, one_mul, add_zero] using
        gradient_inner_add_const (EuclideanSpace.single i 1) 0 x
    have hi : Integrable (fun x : EuclideanSpace ℝ (Fin d) =>
        ‖gradient (fun y : EuclideanSpace ℝ (Fin d) => y i) x‖ ^ 2) μ := by
      simp only [hgrad, PiLp.norm_single, norm_one, one_pow]
      exact integrable_const 1
    have hsm : ContDiff ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞)
        (fun x : EuclideanSpace ℝ (Fin d) => x i) := by
      exact (EuclideanSpace.proj (𝕜 := ℝ) i).contDiff
    have h := hP (fun x => x i) hsm (hcoord i) hi (hmean i)
    simpa only [hgrad, PiLp.norm_single, norm_one, one_pow, integral_const, measureReal_def, measure_univ, ENNReal.toReal_one,
      smul_eq_mul, one_mul] using h
  simp_rw [EuclideanSpace.real_norm_sq_eq]
  rw [integral_finsetSum _ (fun i _ => (hcoord i).integrable_sq)]
  calc
    _ ≤ ∑ _ : Fin d, 1 / rate := Finset.sum_le_sum (fun i _ => hbound i)
    _ = d / rate := by simp [div_eq_mul_inv]

/-- Transparent actual hypotheses for the classical affine version of the
corollary. No Wasserstein estimate or Gaussian law is a field. -/
structure AffineLangevinCutoffData (Ω : Type*) [MeasurableSpace Ω] (d : ℕ) where
  potential : EuclideanSpace ℝ (Fin d) → ℝ
  smooth : ContDiff ℝ 2 potential
  rate : ℝ
  rate_pos : 0 < rate
  hessian : ∀ x z, rate * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ potential) x z z
  probability : IsProbabilityMeasure (gibbsMeasure volume potential)
  centered : ∫ x, x ∂gibbsMeasure volume potential = 0
  poincare : HasSmoothPoincare (gibbsMeasure volume potential) rate
  driver : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d)
  noiseLaw : Measure Ω
  brownian : IsEuclideanBrownian driver noiseLaw
  invariant : ∀ t, (langevinKernel potential driver noiseLaw t) ∘ₘ
    (gibbsMeasure volume potential) = gibbsMeasure volume potential
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

/-- The genuine supremum of squared Wasserstein distances for the actual
nonlinear kernel, on the source's Euclidean starting ball. -/
@[expose] noncomputable def affineBallSquaredWasserstein
    (D : AffineLangevinCutoffData Ω d) (c t : ℝ) : ℝ :=
  (⨆ x : Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) (c * Real.sqrt d),
    squaredWasserstein (langevinKernel D.potential D.driver D.noiseLaw t.toNNReal x)
      (gibbsMeasure volume D.potential)).toReal

/-- The source's two scalar bounds hold for the actual nonlinear transport
supremum; all probabilistic estimates are supplied by the constructed kernel. -/
theorem affineBallSquaredWasserstein_bounds
    (D : AffineLangevinCutoffData Ω d) (hd : 0 < d) {c t : ℝ} (hc : 0 ≤ c) (ht : 0 ≤ t) :
    c ^ 2 * ((d : ℝ) * Real.exp (-2 * D.rate * t)) ≤ affineBallSquaredWasserstein D c t ∧
      affineBallSquaredWasserstein D c t ≤
        (c ^ 2 + D.rate⁻¹) * ((d : ℝ) * Real.exp (-2 * D.rate * t)) := by
  let := D.probability
  have hrate := D.rate_pos
  let W : ℝ≥0∞ := ⨆ x : Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) (c * Real.sqrt d),
    squaredWasserstein (langevinKernel D.potential D.driver D.noiseLaw t.toNNReal x)
      (gibbsMeasure volume D.potential)
  have hLp := gibbs_memLp_two_id_of_hessian_bound D.smooth D.rate D.rate_pos D.hessian
  have hmoment := second_moment_le_of_smoothPoincare _ D.rate hLp D.centered D.poincare
  have hupper := langevin_wasserstein_upper_ball D.brownian D.smooth D.rate D.rate_pos
    D.hessian D.probability D.centered t.toNNReal (D.invariant t.toNNReal) (c * Real.sqrt d)
  have hrsq : (c * Real.sqrt (d : ℝ)) ^ 2 = c ^ 2 * d := by
    rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg d)]
  rw [Real.coe_toNNReal _ ht, hrsq] at hupper
  have hfinite : W ≠ ⊤ := ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top) hupper
  have hureal := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top) hupper
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.exp_pos _).le,
    ENNReal.toReal_ofReal (by positivity)] at hureal
  have hR : 0 ≤ c * Real.sqrt (d : ℝ) := mul_nonneg hc (Real.sqrt_nonneg _)
  have hlower := affine_langevin_wasserstein_lower_ball D.brownian D.smooth D.rate D.rate_pos.le
    D.hessian D.coefficient D.constant D.rate D.rate_pos D.eigenfunction D.probability D.orthonormal
    (c * Real.sqrt d) hR (D.row hd) t.toNNReal
  rw [Real.coe_toNNReal _ ht, hrsq] at hlower
  have hfactor : ENNReal.ofReal D.rate * W ≠ ⊤ := ENNReal.mul_ne_top (by simp) hfinite
  have hlreal := ENNReal.toReal_mono hfactor hlower
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal D.rate_pos.le,
    ENNReal.toReal_ofReal (by positivity)] at hlreal
  change _ ≤ D.rate * affineBallSquaredWasserstein D c t at hlreal
  change affineBallSquaredWasserstein D c t ≤ _ at hureal
  constructor
  · have hnonneg : 0 ≤ (D.coordinateCount : ℝ) *
        (1 - Real.sqrt (1 - Real.exp (-2 * D.rate * t))) ^ 2 := by positivity
    nlinarith [D.rate_pos]
  · calc
      affineBallSquaredWasserstein D c t ≤ Real.exp (-2 * D.rate * t) *
          (c ^ 2 * d + ∫ x, ‖x‖ ^ 2 ∂gibbsMeasure volume D.potential) := hureal
      _ ≤ Real.exp (-2 * D.rate * t) * (c ^ 2 * d + d / D.rate) := by
        gcongr
      _ = _ := by rw [div_eq_mul_inv]; ring

/-- The extended ball supremum is finite; its real representation loses no information. -/
theorem affineBallSquaredWasserstein_ofReal
    (D : AffineLangevinCutoffData Ω d) (c t : ℝ) :
    ENNReal.ofReal (affineBallSquaredWasserstein D c t) =
      ⨆ x : Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) (c * Real.sqrt d),
        squaredWasserstein (langevinKernel D.potential D.driver D.noiseLaw t.toNNReal x)
          (gibbsMeasure volume D.potential) := by
  have hupper := langevin_wasserstein_upper_ball D.brownian D.smooth D.rate D.rate_pos
    D.hessian D.probability D.centered t.toNNReal (D.invariant t.toNNReal) (c * Real.sqrt d)
  exact ENNReal.ofReal_toReal (ne_top_of_le_ne_top
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top) hupper)

/-- Before the critical time the genuine squared Wasserstein ball supremum
diverges, for the classical affine/Poincaré hypotheses. -/
theorem affine_squaredWasserstein_before_cutoff
    (D : ∀ n : ℕ, AffineLangevinCutoffData Ω n) {c ε : ℝ}
    (hc : 0 < c) (hε : 0 < ε) (hε1 : ε < 1) :
    Tendsto (fun n : ℕ => affineBallSquaredWasserstein (D n) c
      ((1 - ε) * criticalTime n (D n).rate)) atTop atTop := by
  apply exponential_lower_cutoff (c := c ^ 2) (rate := fun n => (D n).rate)
    (sq_pos_of_pos hc) hε (fun n => (D n).rate_pos.ne')
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hpos := (D n).rate_pos
  have ht : 0 ≤ (1 - ε) * criticalTime n (D n).rate := by
    apply mul_nonneg (by linarith)
    unfold criticalTime
    exact div_nonneg (Real.log_nonneg (by exact_mod_cast hn)) (by positivity)
  exact (affineBallSquaredWasserstein_bounds (D n) (by omega) hc.le ht).1

/-- A positive lower limit of the rates gives a uniform eventual inverse-rate bound. -/
theorem affine_rates_eventually_bounded_inverse
    (D : ∀ n : ℕ, AffineLangevinCutoffData Ω n)
    (hliminf : 0 < liminf (fun n => (D n).rate) atTop) :
    ∃ r : ℝ, 0 < r ∧ ∀ᶠ n in atTop, (D n).rate⁻¹ ≤ r⁻¹ := by
  let r := liminf (fun n => (D n).rate) atTop / 2
  have hr : 0 < r := by dsimp [r]; positivity
  have hb : IsBoundedUnder (· ≥ ·) atTop (fun n => (D n).rate) :=
    isBoundedUnder_of_eventually_ge (Filter.Eventually.of_forall (fun n : ℕ => (D n).rate_pos.le))
  have hevent : ∀ᶠ n in atTop, r < (D n).rate :=
    eventually_lt_of_lt_liminf (show r < liminf (fun n => (D n).rate) atTop by dsimp [r]; linarith) hb
  refine ⟨r, hr, ?_⟩
  filter_upwards [hevent] with n hn
  exact inv_anti₀ hr hn.le

/-- After the critical time the genuine squared Wasserstein ball supremum
vanishes. The only rate restriction here is the paper's positive lower limit. -/
theorem affine_squaredWasserstein_after_cutoff_of_eventual_inverse_bound
    (D : ∀ n : ℕ, AffineLangevinCutoffData Ω n) {c ε : ℝ}
    (hc : 0 ≤ c) (hε : 0 < ε)
    (r : ℝ) (_hr : 0 < r) (hrate : ∀ᶠ n in atTop, (D n).rate⁻¹ ≤ r⁻¹) :
    Tendsto (fun n : ℕ => affineBallSquaredWasserstein (D n) c
      ((1 + ε) * criticalTime n (D n).rate)) atTop (𝓝 0) := by
  apply exponential_upper_cutoff (C := c ^ 2 + r⁻¹) (rate := fun n => (D n).rate)
    hε (fun n => (D n).rate_pos.ne')
  · exact Filter.Eventually.of_forall (fun _ => ENNReal.toReal_nonneg)
  · filter_upwards [hrate, eventually_ge_atTop 1] with n hn hdim
    have hpos := (D n).rate_pos
    have ht : 0 ≤ (1 + ε) * criticalTime n (D n).rate := by
      apply mul_nonneg (by linarith)
      unfold criticalTime
      exact div_nonneg (Real.log_nonneg (by exact_mod_cast hdim)) (by positivity)
    exact (affineBallSquaredWasserstein_bounds (D n) (by omega) hc ht).2.trans
      (mul_le_mul_of_nonneg_right (add_le_add le_rfl hn) (by positivity))

/-- The source's positive extended lower limit allows both finite rates and
rates diverging to infinity. It supplies precisely the uniform bound needed. -/
theorem affine_rates_eventually_bounded_inverse_of_ennreal_liminf
    (D : ∀ n : ℕ, AffineLangevinCutoffData Ω n)
    (hliminf : 0 < liminf (fun n => ENNReal.ofReal (D n).rate) atTop) :
    ∃ r : ℝ, 0 < r ∧ ∀ᶠ n in atTop, (D n).rate⁻¹ ≤ r⁻¹ := by
  obtain ⟨s, hs0, hs⟩ := exists_between hliminf
  have hsfin : s ≠ ⊤ := ne_of_lt (hs.trans_le le_top)
  have hr : 0 < s.toReal := ENNReal.toReal_pos hs0.ne' hsfin
  have hevent : ∀ᶠ n in atTop, s < ENNReal.ofReal (D n).rate :=
    eventually_lt_of_lt_liminf hs
  refine ⟨s.toReal, hr, ?_⟩
  filter_upwards [hevent] with n hn
  have hreal : s.toReal < (D n).rate := by
    rw [← ENNReal.ofReal_toReal hsfin] at hn
    exact (ENNReal.ofReal_lt_ofReal_iff (D n).rate_pos).mp hn
  exact inv_anti₀ hr hreal.le

/-- The actual squared Wasserstein cutoff after logarithmic time, with
exactly the source's positive lower-limit rate condition, including infinity. -/
theorem affine_squaredWasserstein_after_cutoff
    (D : ∀ n : ℕ, AffineLangevinCutoffData Ω n) {c ε : ℝ}
    (hc : 0 ≤ c) (hε : 0 < ε)
    (hliminf : 0 < liminf (fun n => ENNReal.ofReal (D n).rate) atTop) :
    Tendsto (fun n : ℕ => affineBallSquaredWasserstein (D n) c
      ((1 + ε) * criticalTime n (D n).rate)) atTop (𝓝 0) := by
  obtain ⟨r, hr, hrate⟩ := affine_rates_eventually_bounded_inverse_of_ennreal_liminf D hliminf
  exact affine_squaredWasserstein_after_cutoff_of_eventual_inverse_bound D hc hε r hr hrate

end CutoffRigidity
