module

public import CutoffRigidity.OperatorWassersteinTheorem
public import CutoffRigidity.AffineWassersteinCutoff

/-! # Wasserstein cutoff from the actual attained spectral gap

The data contain the paper's potential, noise and actual spectral equality.
Poincaré and the nonempty Gaussian eigenmap are proved internally. As usual
for sequences indexed by naturals, the spectral assertion is only needed
in positive dimension; dimension zero is a harmless padding entry.
-/

public section

namespace CutoffRigidity

open Set MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

/-- Actual source data, without a supplied Poincaré inequality, affine
eigenfamily, Gaussian-law premise or eigenspace regularity premise. -/
structure SpectralLangevinCutoffData (Ω : Type*) [MeasurableSpace Ω] (d : ℕ) where
  potential : EuclideanSpace ℝ (Fin d) → ℝ
  smooth : ContDiff ℝ 2 potential
  rate : ℝ
  rate_pos : 0 < rate
  hessian : ∀ x z, rate * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ potential) x z z
  probability : IsProbabilityMeasure (gibbsMeasure volume potential)
  centered : ∫ x, x ∂gibbsMeasure volume potential = 0
  spectral : 0 < d → gibbsSpectralGap smooth probability = rate
  driver : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d)
  noiseLaw : Measure Ω
  brownian : IsEuclideanBrownian driver noiseLaw
  invariant : ∀ t, (langevinKernel potential driver noiseLaw t) ∘ₘ
    (gibbsMeasure volume potential) = gibbsMeasure volume potential

variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}

/-- The Poincaré premise of the earlier affine estimate is now derived
from the actual canonical spectral gap. -/
theorem spectralCutoff_hasSmoothPoincare (D : SpectralLangevinCutoffData Ω d) :
    HasSmoothPoincare (gibbsMeasure volume D.potential) D.rate := by
  by_cases hd : 0 < d
  · have h := hasSmoothPoincare_gibbsSpectralGap D.smooth D.probability hd D.rate D.rate_pos D.hessian
    rwa [D.spectral hd] at h
  · have hd0 : d = 0 := by omega
    have : Subsingleton (EuclideanSpace ℝ (Fin d)) := by rw [hd0]; infer_instance
    let := D.probability
    intro f hf hfm hgf hmean
    have hc : f = fun _ => f 0 := funext (fun x => congrArg f (Subsingleton.elim x 0))
    have hIc : (∫ x, f x ∂gibbsMeasure volume D.potential) = f 0 := by
      calc
        _ = ∫ _ : EuclideanSpace ℝ (Fin d), f 0 ∂gibbsMeasure volume D.potential :=
          integral_congr_ae (Filter.Eventually.of_forall (fun x => congrFun hc x))
        _ = f 0 := by simp
    have hz : f 0 = 0 := hIc.symm.trans hmean
    have hfzero : f = fun _ => 0 := funext (fun x => (congrFun hc x).trans hz)
    have hleft : (∫ x, f x ^ 2 ∂gibbsMeasure volume D.potential) = 0 := by simp_rw [hfzero]; simp
    rw [hleft]
    exact div_nonneg (integral_nonneg (fun x => sq_nonneg _)) D.rate_pos.le

/-- Positive dimension supplies a genuine first eigenvector, hence an
internally constructed nonempty orthonormal affine family. -/
theorem spectralCutoff_rows_finrank_pos (D : SpectralLangevinCutoffData Ω d) (hd : 0 < d) :
    0 < Module.finrank ℝ (affineEigenRows D.potential D.rate) := by
  have h := firstEigenspace_finrank_pos D.smooth D.probability hd D.rate D.rate_pos D.hessian (D.spectral hd)
  rwa [firstEigenspace_finrank_eq_operator D.smooth D.probability D.rate (D.spectral hd),
    operatorEigenspace_finrank_eq_classical D.smooth D.probability D.rate D.rate_pos D.hessian,
    classicalL2Eigenspace_finrank_eq_rows D.smooth D.rate D.rate_pos D.hessian D.probability] at h

/-- Every old affine/Poincaré field is now constructed from the actual
spectral assumptions; none is an additional source hypothesis. -/
@[expose] noncomputable def spectralCutoffToAffine (D : SpectralLangevinCutoffData Ω d) :
    AffineLangevinCutoffData Ω d where
  potential := D.potential
  smooth := D.smooth
  rate := D.rate
  rate_pos := D.rate_pos
  hessian := D.hessian
  probability := D.probability
  centered := D.centered
  poincare := spectralCutoff_hasSmoothPoincare D
  driver := D.driver
  noiseLaw := D.noiseLaw
  brownian := D.brownian
  invariant := D.invariant
  coordinateCount := Module.finrank ℝ (affineEigenRows D.potential D.rate)
  row := fun hd => ⟨0, spectralCutoff_rows_finrank_pos D hd⟩
  coefficient := fun i => (affineEigenBasisCoefficient D.potential D.rate i : EuclideanSpace ℝ (Fin d))
  constant := fun i => affineEigenConstant D.potential D.rate (affineEigenBasisCoefficient D.potential D.rate i)
  eigenfunction := affineEigenBasisFunction_eigenfunction D.potential D.rate_pos
  orthonormal := affineEigenBasisFunction_integral_mul D.potential
    (D.smooth.differentiable (by norm_num)) D.rate_pos D.probability

/-- The actual nonlinear transport supremum in the source corollary. -/
@[expose] noncomputable def spectralBallSquaredWasserstein
    (D : SpectralLangevinCutoffData Ω d) (c t : ℝ) : ℝ :=
  (⨆ x : Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) (c * Real.sqrt d),
    squaredWasserstein (langevinKernel D.potential D.driver D.noiseLaw t.toNNReal x)
      (gibbsMeasure volume D.potential)).toReal

/-- The source scalar sandwich now holds from actual spectral source data. -/
theorem spectralBallSquaredWasserstein_bounds
    (D : SpectralLangevinCutoffData Ω d) (hd : 0 < d) {c t : ℝ} (hc : 0 ≤ c) (ht : 0 ≤ t) :
    c ^ 2 * ((d : ℝ) * Real.exp (-2 * D.rate * t)) ≤ spectralBallSquaredWasserstein D c t ∧
      spectralBallSquaredWasserstein D c t ≤
        (c ^ 2 + D.rate⁻¹) * ((d : ℝ) * Real.exp (-2 * D.rate * t)) :=
  affineBallSquaredWasserstein_bounds (spectralCutoffToAffine D) hd hc ht

theorem spectralBallSquaredWasserstein_ofReal
    (D : SpectralLangevinCutoffData Ω d) (c t : ℝ) :
    ENNReal.ofReal (spectralBallSquaredWasserstein D c t) =
      ⨆ x : Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) (c * Real.sqrt d),
        squaredWasserstein (langevinKernel D.potential D.driver D.noiseLaw t.toNNReal x)
          (gibbsMeasure volume D.potential) :=
  affineBallSquaredWasserstein_ofReal (spectralCutoffToAffine D) c t

/-- Before logarithmic time the genuine transport supremum diverges,
using the actual first-gap rigidity assumptions of the source. -/
theorem spectral_squaredWasserstein_before_cutoff
    (D : ∀ n : ℕ, SpectralLangevinCutoffData Ω n) {c ε : ℝ}
    (hc : 0 < c) (hε : 0 < ε) (hε1 : ε < 1) :
    Tendsto (fun n : ℕ => spectralBallSquaredWasserstein (D n) c
      ((1 - ε) * criticalTime n (D n).rate)) atTop atTop :=
  affine_squaredWasserstein_before_cutoff (fun n => spectralCutoffToAffine (D n)) hc hε hε1

/-- After logarithmic time the genuine transport supremum vanishes under
exactly the source's positive extended lower limit of the actual rates. -/
theorem spectral_squaredWasserstein_after_cutoff
    (D : ∀ n : ℕ, SpectralLangevinCutoffData Ω n) {c ε : ℝ}
    (hc : 0 ≤ c) (hε : 0 < ε)
    (hliminf : 0 < liminf (fun n => ENNReal.ofReal (D n).rate) atTop) :
    Tendsto (fun n : ℕ => spectralBallSquaredWasserstein (D n) c
      ((1 + ε) * criticalTime n (D n).rate)) atTop (𝓝 0) :=
  affine_squaredWasserstein_after_cutoff (fun n => spectralCutoffToAffine (D n)) hc hε hliminf

/-- The genuine supremum of the real quadratic Wasserstein distances,
defined from the actual coupling transport costs. -/
@[expose] noncomputable def spectralBallWasserstein
    (D : SpectralLangevinCutoffData Ω d) (c t : ℝ) : ℝ :=
  ⨆ x : Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) (c * Real.sqrt d),
    Real.sqrt ((squaredWasserstein (langevinKernel D.potential D.driver D.noiseLaw t.toNNReal x)
      (gibbsMeasure volume D.potential)).toReal)

/-- Finiteness of the actual transport supremum and continuity of the
square root justify passing between the source's W₂ and squared costs. -/
theorem spectralBallWasserstein_eq_sqrt
    (D : SpectralLangevinCutoffData Ω d) {c : ℝ} (hc : 0 ≤ c) (t : ℝ) :
    spectralBallWasserstein D c t = Real.sqrt (spectralBallSquaredWasserstein D c t) := by
  let S := Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) (c * Real.sqrt d)
  let W (x : S) := squaredWasserstein
    (langevinKernel D.potential D.driver D.noiseLaw t.toNNReal x) (gibbsMeasure volume D.potential)
  have hS : S.Nonempty := ⟨0, by simpa [S] using mul_nonneg hc (Real.sqrt_nonneg (d : ℝ))⟩
  let : Nonempty S := hS.to_subtype
  have hfin : (⨆ x : S, W x) ≠ ⊤ := by
    rw [← spectralBallSquaredWasserstein_ofReal D c t]
    exact ENNReal.ofReal_ne_top
  have hpoint : ∀ x : S, W x ≠ ⊤ := fun x => ne_top_of_le_ne_top hfin (le_iSup W x)
  have hbounded : BddAbove (Set.range fun x : S => (W x).toReal) := by
    refine ⟨(⨆ x : S, W x).toReal, ?_⟩
    rintro _ ⟨x, rfl⟩
    exact ENNReal.toReal_mono hfin (le_iSup W x)
  change (⨆ x : S, Real.sqrt ((W x).toReal)) = Real.sqrt ((⨆ x : S, W x).toReal)
  rw [ENNReal.toReal_iSup hpoint]
  exact (Real.sqrt_monotone.map_ciSup_of_continuousAt Real.continuous_sqrt.continuousAt hbounded).symm

/-- The actual W₂ ball supremum diverges before the critical time. -/
theorem spectral_wasserstein_before_cutoff
    (D : ∀ n : ℕ, SpectralLangevinCutoffData Ω n) {c ε : ℝ}
    (hc : 0 < c) (hε : 0 < ε) (hε1 : ε < 1) :
    Tendsto (fun n : ℕ => spectralBallWasserstein (D n) c
      ((1 - ε) * criticalTime n (D n).rate)) atTop atTop := by
  have h := Real.tendsto_sqrt_atTop.comp (spectral_squaredWasserstein_before_cutoff D hc hε hε1)
  apply h.congr'
  exact Filter.Eventually.of_forall (fun n => (spectralBallWasserstein_eq_sqrt (D n) hc.le _).symm)

/-- The actual W₂ ball supremum vanishes after the critical time. -/
theorem spectral_wasserstein_after_cutoff
    (D : ∀ n : ℕ, SpectralLangevinCutoffData Ω n) {c ε : ℝ}
    (hc : 0 ≤ c) (hε : 0 < ε)
    (hliminf : 0 < liminf (fun n => ENNReal.ofReal (D n).rate) atTop) :
    Tendsto (fun n : ℕ => spectralBallWasserstein (D n) c
      ((1 + ε) * criticalTime n (D n).rate)) atTop (𝓝 0) := by
  have h := Real.continuous_sqrt.continuousAt.tendsto.comp
    (spectral_squaredWasserstein_after_cutoff D hc hε hliminf)
  have hh := h.congr' (Filter.Eventually.of_forall
    (fun n => (spectralBallWasserstein_eq_sqrt (D n) hc _).symm))
  simpa only [Real.sqrt_zero] using hh

end CutoffRigidity
