module
public import CutoffRigidity.BarycenterInformationLowerCutoffs
public import CutoffRigidity.LogSobolev

/-! # Actual Fisher lower cutoffs on source barycenter balls and cubes

The genuine full-domain LSI transfers the already proved actual entropy
lower cutoff to canonical relative Fisher information. No density or
pointwise smoothness of Dirac-start transition laws is assumed.
-/
public section
namespace CutoffRigidity
open Set MeasureTheory ProbabilityTheory InformationTheory Filter Topology
open scoped ENNReal NNReal
variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

/-- Actual canonical Fisher profile over an actual set of initial points. -/
@[expose] noncomputable def spectralSetFisher
    (D : SpectralInformationLowerData Ω d) (S : Set E) (t : ℝ) : ENNReal := by
  let := D.probability
  let := langevinKernel_isMarkovKernel D.brownian D.smooth D.rate D.rate_pos.le D.hessian t.toNNReal
  exact ⨆ x : S, relativeFisherInformation D.smooth D.probability
    (langevinKernel D.potential D.driver D.noiseLaw t.toNNReal x)

/-- Genuine full LSI gives the pointwise-to-set lower comparison, with
infinite Fisher values included. -/
theorem spectralSetFisher_ge_scaled_entropy
    (D : SpectralInformationLowerData Ω d) (hd : 0 < d) (S : Set E) (t : ℝ) :
    ENNReal.ofReal (2 * D.rate) * projectedSetKL (spectralInformationToAffine D) S t ≤
      spectralSetFisher D S t := by
  let := D.probability
  let := langevinKernel_isMarkovKernel D.brownian D.smooth D.rate D.rate_pos.le D.hessian t.toNNReal
  change ENNReal.ofReal (2 * D.rate) * (⨆ x : S,
    klDiv (langevinKernel D.potential D.driver D.noiseLaw t.toNNReal x) (gibbsMeasure volume D.potential)) ≤
      ⨆ x : S, relativeFisherInformation D.smooth D.probability
        (langevinKernel D.potential D.driver D.noiseLaw t.toNNReal x)
  rw [ENNReal.mul_iSup]
  apply iSup_le
  intro x
  have hLSI := logSobolev_relativeFisherInformation D.brownian D.smooth D.probability hd
    D.rate D.rate_pos D.hessian (langevinKernel D.potential D.driver D.noiseLaw t.toNNReal x)
  have hb0 : ENNReal.ofReal (2 * D.rate) ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr (by have hr := D.rate_pos; positivity)
  have hh := (ENNReal.le_div_iff_mul_le (Or.inl hb0) (Or.inl ENNReal.ofReal_ne_top)).mp hLSI
  have hh' : ENNReal.ofReal (2 * D.rate) *
      klDiv (langevinKernel D.potential D.driver D.noiseLaw t.toNNReal x) (gibbsMeasure volume D.potential) ≤
      relativeFisherInformation D.smooth D.probability
        (langevinKernel D.potential D.driver D.noiseLaw t.toNNReal x) := by
    simpa only [mul_comm] using hh
  exact hh'.trans (le_iSup (fun y : S => relativeFisherInformation D.smooth D.probability
    (langevinKernel D.potential D.driver D.noiseLaw t.toNNReal y)) x)

@[expose] noncomputable def meanBallFisher (D : SpectralInformationLowerData Ω d) (c t : ℝ) : ENNReal :=
  spectralSetFisher D
    (Metric.closedBall (∫ y, y ∂gibbsMeasure volume D.potential) (c * Real.sqrt d)) t

@[expose] noncomputable def convexCubeFisher (D : ConvexInteractionCubeData Ω d) (c t : ℝ) : ENNReal :=
  spectralSetFisher (cubeSpectralData D)
    (closedCoordinateCube (∫ y, y ∂gibbsMeasure volume (cubeSpectralData D).potential) c) t

private theorem fisher_cutoff_of_entropy_cutoff
    (rate : ℕ → ℝ) (H I : ℕ → ENNReal) (hH : Tendsto H atTop (𝓝 ⊤))
    (hpositive : ∃ r : ℝ, 0 < r ∧ ∀ᶠ n in atTop, r ≤ rate n)
    (hBound : ∀ᶠ n in atTop, ENNReal.ofReal (2 * rate n) * H n ≤ I n) :
    Tendsto I atTop (𝓝 ⊤) := by
  obtain ⟨r, hr, hRate⟩ := hpositive
  have hC0 : ENNReal.ofReal (2 * r) ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr (by positivity)
  have hScale : Tendsto (fun n => ENNReal.ofReal (2 * r) * H n) atTop (𝓝 ⊤) := by
    have hh := (ENNReal.continuous_const_mul (a := ENNReal.ofReal (2 * r)) ENNReal.ofReal_ne_top).continuousAt.tendsto.comp hH
    simpa only [Function.comp_def, ENNReal.mul_top hC0] using hh
  apply tendsto_nhds_top_mono hScale
  filter_upwards [hRate, hBound] with n hn hI
  exact (mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal (by linarith : 2 * r ≤ 2 * rate n))
    (show (0 : ENNReal) ≤ H n from bot_le)).trans hI

/-- The source Fisher before-cutoff divergence on actual Gibbs-barycenter
balls, derived directly from actual entropy divergence and genuine LSI. -/
theorem meanBallFisher_before_cutoff
    (D : ∀ n : ℕ, SpectralInformationLowerData Ω n) {c ε : ℝ}
    (hc : 0 < c) (hε : 0 < ε) (hε1 : ε < 1)
    (hliminf : 0 < liminf (fun n => ENNReal.ofReal (D n).rate) atTop) :
    Tendsto (fun n : ℕ => meanBallFisher (D n) c
      ((1 - ε) * criticalTime n (D n).rate)) atTop (𝓝 ⊤) := by
  apply fisher_cutoff_of_entropy_cutoff (fun n => (D n).rate)
    (fun n => meanBallKL (D n) c ((1 - ε) * criticalTime n (D n).rate))
    (fun n => meanBallFisher (D n) c ((1 - ε) * criticalTime n (D n).rate))
    (meanBall_entropy_before_cutoff D hc hε hε1 hliminf)
    (spectralInformation_rates_eventually_positive_lower D hliminf)
  filter_upwards [eventually_ge_atTop 1] with n hn
  exact spectralSetFisher_ge_scaled_entropy (D n) (by omega) _ _

/-- The source Fisher before-cutoff divergence on actual Gibbs-barycenter
coordinate cubes, through the same genuine entropy/LSI comparison. -/
theorem convexCubeFisher_before_cutoff
    (D : ∀ n : ℕ, ConvexInteractionCubeData Ω n) {c ε : ℝ}
    (hc : 0 < c) (hε : 0 < ε) (hε1 : ε < 1)
    (hliminf : 0 < liminf (fun n => ENNReal.ofReal (D n).rate) atTop) :
    Tendsto (fun n : ℕ => convexCubeFisher (D n) c
      ((1 - ε) * criticalTime n (D n).rate)) atTop (𝓝 ⊤) := by
  apply fisher_cutoff_of_entropy_cutoff (fun n => (D n).rate)
    (fun n => convexCubeKL (D n) c ((1 - ε) * criticalTime n (D n).rate))
    (fun n => convexCubeFisher (D n) c ((1 - ε) * criticalTime n (D n).rate))
    (convexCube_entropy_before_cutoff D hc hε hε1 hliminf)
    (spectralInformation_rates_eventually_positive_lower (fun n => cubeSpectralData (D n)) hliminf)
  filter_upwards [eventually_ge_atTop 1] with n hn
  exact spectralSetFisher_ge_scaled_entropy (cubeSpectralData (D n)) (by omega) _ _

end CutoffRigidity
