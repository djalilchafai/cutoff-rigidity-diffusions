module
public import CutoffRigidity.BarycenterWasserstein

/-! # Corollary 1.2 on balls about the actual barycenters

The source data impose no centering, invariance, Poincaré or eigenfamily
premise. The written translation-to-mean step is discharged by the actual
affine-coordinate and second-moment identities of BarycenterWasserstein.
-/
public section
namespace CutoffRigidity
open Set MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal
variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

@[expose] noncomputable def barycenterBallSquaredWasserstein
    (D : SpectralInformationLowerData Ω d) (c t : ℝ) : ℝ :=
  (⨆ x : Metric.closedBall (∫ y, y ∂gibbsMeasure volume D.potential) (c * Real.sqrt d),
    squaredWasserstein (langevinKernel D.potential D.driver D.noiseLaw t.toNNReal x)
      (gibbsMeasure volume D.potential)).toReal

theorem barycenterBallSquaredWasserstein_bounds
    (D : SpectralInformationLowerData Ω d) (hd : 0 < d) {c t : ℝ} (hc : 0 ≤ c) (ht : 0 ≤ t) :
    c ^ 2 * ((d : ℝ) * Real.exp (-2 * D.rate * t)) ≤ barycenterBallSquaredWasserstein D c t ∧
      barycenterBallSquaredWasserstein D c t ≤
        (c ^ 2 + D.rate⁻¹) * ((d : ℝ) * Real.exp (-2 * D.rate * t)) := by
  have hrate := D.rate_pos
  let W : ℝ≥0∞ := ⨆ x : Metric.closedBall (∫ y, y ∂gibbsMeasure volume D.potential) (c * Real.sqrt d),
    squaredWasserstein (langevinKernel D.potential D.driver D.noiseLaw t.toNNReal x) (gibbsMeasure volume D.potential)
  have hb := euclidean_wasserstein_mean_ball D.brownian D.smooth D.rate D.rate_pos D.hessian
    D.probability (D.spectral hd) hd (c * Real.sqrt d) (mul_nonneg hc (Real.sqrt_nonneg _)) t.toNNReal
  have hrsq : (c * Real.sqrt (d : ℝ)) ^ 2 = c ^ 2 * d := by
    rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg d)]
  rw [Real.coe_toNNReal _ ht, hrsq] at hb
  have hfinite : W ≠ ⊤ := ne_top_of_le_ne_top
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top) hb.2
  have hl := ENNReal.toReal_mono hfinite hb.1
  have hu := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top) hb.2
  rw [ENNReal.toReal_ofReal (by positivity)] at hl
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.exp_pos _).le,
    ENNReal.toReal_ofReal (by positivity)] at hu
  have hm := gibbs_variance_le_dim_div_gap D.smooth D.probability hd D.rate D.rate_pos D.hessian
  rw [D.spectral hd] at hm
  change _ ≤ barycenterBallSquaredWasserstein D c t at hl
  change barycenterBallSquaredWasserstein D c t ≤ _ at hu
  constructor
  · have hk : 0 ≤ (Module.finrank ℝ (gibbsFirstEigenspace D.smooth D.probability) / D.rate) *
        (1 - Real.sqrt (1 - Real.exp (-2 * D.rate * t))) ^ 2 := by positivity
    nlinarith
  · calc
      _ ≤ Real.exp (-2 * D.rate * t) * (c ^ 2 * d +
        ∫ x, ‖x - ∫ y, y ∂gibbsMeasure volume D.potential‖ ^ 2 ∂gibbsMeasure volume D.potential) := hu
      _ ≤ Real.exp (-2 * D.rate * t) * (c ^ 2 * d + d / D.rate) := by gcongr
      _ = _ := by rw [div_eq_mul_inv]; ring

theorem barycenterBallSquaredWasserstein_ofReal
    (D : SpectralInformationLowerData Ω d) (hd : 0 < d) {c : ℝ} (hc : 0 ≤ c) (t : ℝ) :
    ENNReal.ofReal (barycenterBallSquaredWasserstein D c t) =
      ⨆ x : Metric.closedBall (∫ y, y ∂gibbsMeasure volume D.potential) (c * Real.sqrt d),
        squaredWasserstein (langevinKernel D.potential D.driver D.noiseLaw t.toNNReal x) (gibbsMeasure volume D.potential) := by
  have hb := euclidean_wasserstein_mean_ball D.brownian D.smooth D.rate D.rate_pos D.hessian
    D.probability (D.spectral hd) hd (c * Real.sqrt d) (mul_nonneg hc (Real.sqrt_nonneg _)) t.toNNReal
  exact ENNReal.ofReal_toReal (ne_top_of_le_ne_top
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top) hb.2)

theorem barycenter_squaredWasserstein_before_cutoff
    (D : ∀ n : ℕ, SpectralInformationLowerData Ω n) {c ε : ℝ}
    (hc : 0 < c) (hε : 0 < ε) (hε1 : ε < 1) :
    Tendsto (fun n : ℕ => barycenterBallSquaredWasserstein (D n) c
      ((1 - ε) * criticalTime n (D n).rate)) atTop atTop := by
  apply exponential_lower_cutoff (c := c ^ 2) (rate := fun n => (D n).rate)
    (sq_pos_of_pos hc) hε (fun n => (D n).rate_pos.ne')
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hpos := (D n).rate_pos
  have ht : 0 ≤ (1 - ε) * criticalTime n (D n).rate := by
    apply mul_nonneg (by linarith)
    unfold criticalTime
    exact div_nonneg (Real.log_nonneg (by exact_mod_cast hn)) (by positivity)
  exact (barycenterBallSquaredWasserstein_bounds (D n) (by omega) hc.le ht).1

theorem barycenter_squaredWasserstein_after_cutoff
    (D : ∀ n : ℕ, SpectralInformationLowerData Ω n) {c ε : ℝ}
    (hc : 0 ≤ c) (hε : 0 < ε)
    (hliminf : 0 < liminf (fun n => ENNReal.ofReal (D n).rate) atTop) :
    Tendsto (fun n : ℕ => barycenterBallSquaredWasserstein (D n) c
      ((1 + ε) * criticalTime n (D n).rate)) atTop (𝓝 0) := by
  obtain ⟨r, hr, hrate⟩ := spectralInformation_rates_eventually_positive_lower D hliminf
  apply exponential_upper_cutoff (C := c ^ 2 + r⁻¹) (rate := fun n => (D n).rate)
    hε (fun n => (D n).rate_pos.ne')
  · exact Filter.Eventually.of_forall (fun _ => ENNReal.toReal_nonneg)
  · filter_upwards [hrate, eventually_ge_atTop 1] with n hn hdim
    have hpos := (D n).rate_pos
    have ht : 0 ≤ (1 + ε) * criticalTime n (D n).rate := by
      apply mul_nonneg (by linarith)
      unfold criticalTime
      exact div_nonneg (Real.log_nonneg (by exact_mod_cast hdim)) (by positivity)
    exact (barycenterBallSquaredWasserstein_bounds (D n) (by omega) hc ht).2.trans
      (mul_le_mul_of_nonneg_right (add_le_add le_rfl (inv_anti₀ hr hn)) (by positivity))

@[expose] noncomputable def barycenterBallWasserstein (D : SpectralInformationLowerData Ω d) (c t : ℝ) : ℝ :=
  ⨆ x : Metric.closedBall (∫ y, y ∂gibbsMeasure volume D.potential) (c * Real.sqrt d),
    Real.sqrt ((squaredWasserstein (langevinKernel D.potential D.driver D.noiseLaw t.toNNReal x)
      (gibbsMeasure volume D.potential)).toReal)

theorem barycenterBallWasserstein_eq_sqrt
    (D : SpectralInformationLowerData Ω d) (hd : 0 < d) {c : ℝ} (hc : 0 ≤ c) (t : ℝ) :
    barycenterBallWasserstein D c t = Real.sqrt (barycenterBallSquaredWasserstein D c t) := by
  let S := Metric.closedBall (∫ y, y ∂gibbsMeasure volume D.potential) (c * Real.sqrt d)
  let W (x : S) := squaredWasserstein (langevinKernel D.potential D.driver D.noiseLaw t.toNNReal x)
    (gibbsMeasure volume D.potential)
  have hS : S.Nonempty := ⟨∫ y, y ∂gibbsMeasure volume D.potential, by
    simpa [S] using mul_nonneg hc (Real.sqrt_nonneg (d : ℝ))⟩
  let : Nonempty S := hS.to_subtype
  have hfin : (⨆ x : S, W x) ≠ ⊤ := by
    rw [← barycenterBallSquaredWasserstein_ofReal D hd hc t]
    exact ENNReal.ofReal_ne_top
  have hpoint : ∀ x : S, W x ≠ ⊤ := fun x => ne_top_of_le_ne_top hfin (le_iSup W x)
  have hb : BddAbove (Set.range fun x : S => (W x).toReal) := by
    refine ⟨(⨆ x : S, W x).toReal, ?_⟩
    rintro _ ⟨x, rfl⟩
    exact ENNReal.toReal_mono hfin (le_iSup W x)
  change (⨆ x : S, Real.sqrt ((W x).toReal)) = Real.sqrt ((⨆ x : S, W x).toReal)
  rw [ENNReal.toReal_iSup hpoint]
  exact (Real.sqrt_monotone.map_ciSup_of_continuousAt Real.continuous_sqrt.continuousAt hb).symm

/-- Exact source Corollary 1.2 before cutoff on B(m_d,c√d). -/
theorem barycenter_wasserstein_before_cutoff
    (D : ∀ n : ℕ, SpectralInformationLowerData Ω n) {c ε : ℝ}
    (hc : 0 < c) (hε : 0 < ε) (hε1 : ε < 1) :
    Tendsto (fun n : ℕ => barycenterBallWasserstein (D n) c
      ((1 - ε) * criticalTime n (D n).rate)) atTop atTop := by
  have h := Real.tendsto_sqrt_atTop.comp (barycenter_squaredWasserstein_before_cutoff D hc hε hε1)
  apply h.congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  exact (barycenterBallWasserstein_eq_sqrt (D n) (by omega) hc.le _).symm

/-- Exact source Corollary 1.2 after cutoff, with no centering premise. -/
theorem barycenter_wasserstein_after_cutoff
    (D : ∀ n : ℕ, SpectralInformationLowerData Ω n) {c ε : ℝ}
    (hc : 0 ≤ c) (hε : 0 < ε)
    (hliminf : 0 < liminf (fun n => ENNReal.ofReal (D n).rate) atTop) :
    Tendsto (fun n : ℕ => barycenterBallWasserstein (D n) c
      ((1 + ε) * criticalTime n (D n).rate)) atTop (𝓝 0) := by
  have h := Real.continuous_sqrt.continuousAt.tendsto.comp
    (barycenter_squaredWasserstein_after_cutoff D hc hε hliminf)
  have hh := h.congr' (show (fun n : ℕ => Real.sqrt (barycenterBallSquaredWasserstein (D n) c
      ((1 + ε) * criticalTime n (D n).rate))) =ᶠ[atTop]
      (fun n => barycenterBallWasserstein (D n) c ((1 + ε) * criticalTime n (D n).rate)) from by
    filter_upwards [eventually_ge_atTop 1] with n hn
    exact (barycenterBallWasserstein_eq_sqrt (D n) (by omega) hc _).symm)
  simpa only [Real.sqrt_zero] using hh

/-- The normalized convex-interaction specialization has the actual
confinement spectral gap internally, and requires no centering premise. -/
theorem normalized_convexInteraction_wasserstein_before_cutoff
    {W : ∀ n : ℕ, EuclideanSpace ℝ (Fin n) → ℝ}
    (hW : ∀ n, ContDiff ℝ 2 (W n)) (hconv : ∀ n, ConvexOn ℝ Set.univ (W n))
    (rate : ℕ → ℝ) (hpos : ∀ n, 0 < rate n)
    (hinv : ∀ n (x : EuclideanSpace ℝ (Fin n)) (t : ℝ),
      W n (x + t • diagonalDirection n) = W n x)
    {B : ∀ n : ℕ, ℝ≥0 → Ω → EuclideanSpace ℝ (Fin n)} {P : ℕ → Measure Ω}
    (hB : ∀ n, IsEuclideanBrownian (B n) (P n)) {c ε : ℝ}
    (hc : 0 < c) (hε : 0 < ε) (hε1 : ε < 1) :
    Tendsto (fun n : ℕ => barycenterBallWasserstein
      (normalizedConvexInteractionInformationLowerData (hW n) (hconv n) (rate n) (hpos n) (hinv n) (hB n)) c
      ((1 - ε) * criticalTime n (rate n))) atTop atTop :=
  barycenter_wasserstein_before_cutoff
    (fun n => normalizedConvexInteractionInformationLowerData (hW n) (hconv n) (rate n) (hpos n) (hinv n) (hB n))
    hc hε hε1

/-- After-cutoff part of the same source ball specialization, under the
paper's positive lower-limit confinement condition. -/
theorem normalized_convexInteraction_wasserstein_after_cutoff
    {W : ∀ n : ℕ, EuclideanSpace ℝ (Fin n) → ℝ}
    (hW : ∀ n, ContDiff ℝ 2 (W n)) (hconv : ∀ n, ConvexOn ℝ Set.univ (W n))
    (rate : ℕ → ℝ) (hpos : ∀ n, 0 < rate n)
    (hinv : ∀ n (x : EuclideanSpace ℝ (Fin n)) (t : ℝ),
      W n (x + t • diagonalDirection n) = W n x)
    {B : ∀ n : ℕ, ℝ≥0 → Ω → EuclideanSpace ℝ (Fin n)} {P : ℕ → Measure Ω}
    (hB : ∀ n, IsEuclideanBrownian (B n) (P n)) {c ε : ℝ}
    (hc : 0 ≤ c) (hε : 0 < ε)
    (hliminf : 0 < liminf (fun n => ENNReal.ofReal (rate n)) atTop) :
    Tendsto (fun n : ℕ => barycenterBallWasserstein
      (normalizedConvexInteractionInformationLowerData (hW n) (hconv n) (rate n) (hpos n) (hinv n) (hB n)) c
      ((1 + ε) * criticalTime n (rate n))) atTop (𝓝 0) :=
  barycenter_wasserstein_after_cutoff
    (fun n => normalizedConvexInteractionInformationLowerData (hW n) (hconv n) (rate n) (hpos n) (hinv n) (hB n))
    hc hε hliminf

end CutoffRigidity
