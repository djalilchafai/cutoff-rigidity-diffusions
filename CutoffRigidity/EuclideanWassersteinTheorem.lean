module

public import CutoffRigidity.LangevinGibbsInvariance
public import CutoffRigidity.SpectralWassersteinCutoff
public import CutoffRigidity.SpectralInformationLowerCutoffs

/-! # The source Euclidean Wasserstein theorem and cutoff

The distance is the actual coupling Wasserstein cost, λ₁ the actual attained
self-adjoint first gap, E₁ its actual eigenspace, and Λ the squared continuous
evaluation norm on its unique continuous representatives. Actual stochastic
Gibbs invariance is proved internally, not retained as a source premise.
-/

public section

namespace CutoffRigidity

open Set MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

/-- The actual-first-eigenspace source estimate, with Gibbs invariance derived. -/
theorem euclidean_wasserstein_theorem_of_gap_eq_curvature
    {B : ℝ≥0 → Ω → E} {P : Measure Ω} (hB : IsEuclideanBrownian B P)
    {V : E → ℝ} (hV : ContDiff ℝ 2 V) (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (hprob : IsProbabilityMeasure (gibbsMeasure volume V))
    (hgap : gibbsSpectralGap hV hprob = ρ) (S : Set E) (hS : S.Nonempty) (t : ℝ≥0) :
    (ENNReal.ofReal ρ⁻¹ *
      (ENNReal.ofReal (Real.exp (-2 * ρ * (t : ℝ))) * firstEigenLambda hV hprob ρ hρ hHess hgap S +
        ENNReal.ofReal (Module.finrank ℝ (gibbsFirstEigenspace hV hprob) *
          (1 - Real.sqrt (1 - Real.exp (-2 * ρ * (t : ℝ)))) ^ 2)) ≤
      ⨆ x : S, squaredWasserstein (langevinKernel V B P t (x : E)) (gibbsMeasure volume V)) ∧
    ((⨆ x : S, squaredWasserstein (langevinKernel V B P t (x : E)) (gibbsMeasure volume V)) ≤
      ENNReal.ofReal (Real.exp (-2 * ρ * (t : ℝ))) *
        ⨆ x : S, ENNReal.ofReal (∫ y, ‖y - (x : E)‖ ^ 2 ∂gibbsMeasure volume V)) :=
  first_eigenspace_euclidean_wasserstein_theorem hB hV ρ hρ hHess hprob hgap S hS t
    (langevinKernel_gibbs_invariant hB hV hprob ρ hρ hHess t)

/-- The actual-first-eigenspace source estimate, with Gibbs invariance derived. -/
theorem euclidean_wasserstein_ball_of_gap_eq_curvature
    {B : ℝ≥0 → Ω → E} {P : Measure Ω} (hB : IsEuclideanBrownian B P)
    {V : E → ℝ} (hV : ContDiff ℝ 2 V) (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (hprob : IsProbabilityMeasure (gibbsMeasure volume V))
    (hgap : gibbsSpectralGap hV hprob = ρ)
    (hcenter : ∫ x, x ∂gibbsMeasure volume V = 0)
    (hd : 0 < d) (R : ℝ) (hR : 0 ≤ R) (t : ℝ≥0) :
    (ENNReal.ofReal (Real.exp (-2 * ρ * (t : ℝ)) * R ^ 2 +
      (Module.finrank ℝ (gibbsFirstEigenspace hV hprob) / ρ) *
        (1 - Real.sqrt (1 - Real.exp (-2 * ρ * (t : ℝ)))) ^ 2) ≤
      ⨆ x : Metric.closedBall (0 : E) R,
        squaredWasserstein (langevinKernel V B P t (x : E)) (gibbsMeasure volume V)) ∧
    ((⨆ x : Metric.closedBall (0 : E) R,
      squaredWasserstein (langevinKernel V B P t (x : E)) (gibbsMeasure volume V)) ≤
      ENNReal.ofReal (Real.exp (-2 * ρ * (t : ℝ))) *
        ENNReal.ofReal (R ^ 2 + ∫ x, ‖x‖ ^ 2 ∂gibbsMeasure volume V)) :=
  first_eigenspace_euclidean_wasserstein_ball hB hV ρ hρ hHess hprob hgap hcenter hd R hR t
    (langevinKernel_gibbs_invariant hB hV hprob ρ hρ hHess t)

/-- The source pointwise Λ uses the actual canonical first gap and the
actual first-eigenspace continuous evaluation norm. -/
@[expose] noncomputable def euclideanLambdaPoint {V : E → ℝ}
    (hV : ContDiff ℝ 2 V) (hp : IsProbabilityMeasure (gibbsMeasure volume V))
    (hgap_pos : 0 < gibbsSpectralGap hV hp)
    (hHess : ∀ x z : E, gibbsSpectralGap hV hp * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (x : E) : ℝ :=
  firstEigenLambdaPoint hV hp (gibbsSpectralGap hV hp) hgap_pos hHess rfl x

@[expose] noncomputable def euclideanLambda {V : E → ℝ}
    (hV : ContDiff ℝ 2 V) (hp : IsProbabilityMeasure (gibbsMeasure volume V))
    (hgap_pos : 0 < gibbsSpectralGap hV hp)
    (hHess : ∀ x z : E, gibbsSpectralGap hV hp * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (S : Set E) : ℝ≥0∞ :=
  firstEigenLambda hV hp (gibbsSpectralGap hV hp) hgap_pos hHess rfl S

theorem euclideanLambdaPoint_eq_basis_sum {V : E → ℝ}
    (hV : ContDiff ℝ 2 V) (hp : IsProbabilityMeasure (gibbsMeasure volume V))
    (hgap_pos : 0 < gibbsSpectralGap hV hp)
    (hHess : ∀ x z : E, gibbsSpectralGap hV hp * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ (gibbsFirstEigenspace hV hp)) (x : E) :
    euclideanLambdaPoint hV hp hgap_pos hHess x =
      ∑ i, |firstEigenRepresentative hV hp (gibbsSpectralGap hV hp) hgap_pos hHess rfl (b i) x| ^ 2 :=
  firstEigenLambdaPoint_eq_basis_sum hV hp (gibbsSpectralGap hV hp) hgap_pos hHess rfl b x

theorem euclideanLambda_ball {V : E → ℝ}
    (hV : ContDiff ℝ 2 V) (hp : IsProbabilityMeasure (gibbsMeasure volume V))
    (hgap_pos : 0 < gibbsSpectralGap hV hp)
    (hHess : ∀ x z : E, gibbsSpectralGap hV hp * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (hcenter : ∫ x, x ∂gibbsMeasure volume V = 0) (hd : 0 < d) {R : ℝ} (hR : 0 ≤ R) :
    euclideanLambda hV hp hgap_pos hHess (Metric.closedBall (0 : E) R) =
      ENNReal.ofReal (gibbsSpectralGap hV hp * R ^ 2) :=
  firstEigenLambda_ball hV (gibbsSpectralGap hV hp) hgap_pos hHess hp rfl hcenter hd hR

/-- The source Euclidean theorem, with λ₁ the actual attained first gap,
E₁ the actual self-adjoint eigenspace, and Λ its actual evaluation norm.
All regularity, Gaussian projection and Gibbs invariance bridges are proved. -/
theorem euclidean_wasserstein_theorem
    {B : ℝ≥0 → Ω → E} {P : Measure Ω} (hB : IsEuclideanBrownian B P)
    {V : E → ℝ} (hV : ContDiff ℝ 2 V) (hp : IsProbabilityMeasure (gibbsMeasure volume V))
    (hgap_pos : 0 < gibbsSpectralGap hV hp)
    (hHess : ∀ x z : E, gibbsSpectralGap hV hp * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (S : Set E) (hS : S.Nonempty) (t : ℝ≥0) :
    let rate := gibbsSpectralGap hV hp
    (ENNReal.ofReal rate⁻¹ *
      (ENNReal.ofReal (Real.exp (-2 * rate * (t : ℝ))) * euclideanLambda hV hp hgap_pos hHess S +
        ENNReal.ofReal (Module.finrank ℝ (gibbsFirstEigenspace hV hp) *
          (1 - Real.sqrt (1 - Real.exp (-2 * rate * (t : ℝ)))) ^ 2)) ≤
      ⨆ x : S, squaredWasserstein (langevinKernel V B P t (x : E)) (gibbsMeasure volume V)) ∧
    ((⨆ x : S, squaredWasserstein (langevinKernel V B P t (x : E)) (gibbsMeasure volume V)) ≤
      ENNReal.ofReal (Real.exp (-2 * rate * (t : ℝ))) *
        ⨆ x : S, ENNReal.ofReal (∫ y, ‖y - (x : E)‖ ^ 2 ∂gibbsMeasure volume V)) :=
  euclidean_wasserstein_theorem_of_gap_eq_curvature hB hV (gibbsSpectralGap hV hp) hgap_pos hHess hp rfl S hS t

/-- The source centered-ball formula with the actual first eigenspace
dimension; its positive dimension follows from attained spectral gap. -/
theorem euclidean_wasserstein_ball
    {B : ℝ≥0 → Ω → E} {P : Measure Ω} (hB : IsEuclideanBrownian B P)
    {V : E → ℝ} (hV : ContDiff ℝ 2 V) (hp : IsProbabilityMeasure (gibbsMeasure volume V))
    (hgap_pos : 0 < gibbsSpectralGap hV hp)
    (hHess : ∀ x z : E, gibbsSpectralGap hV hp * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (hcenter : ∫ x, x ∂gibbsMeasure volume V = 0) (hd : 0 < d)
    (R : ℝ) (hR : 0 ≤ R) (t : ℝ≥0) :
    let rate := gibbsSpectralGap hV hp
    (ENNReal.ofReal (Real.exp (-2 * rate * (t : ℝ)) * R ^ 2 +
      (Module.finrank ℝ (gibbsFirstEigenspace hV hp) / rate) *
        (1 - Real.sqrt (1 - Real.exp (-2 * rate * (t : ℝ)))) ^ 2) ≤
      ⨆ x : Metric.closedBall (0 : E) R,
        squaredWasserstein (langevinKernel V B P t (x : E)) (gibbsMeasure volume V)) ∧
    ((⨆ x : Metric.closedBall (0 : E) R,
      squaredWasserstein (langevinKernel V B P t (x : E)) (gibbsMeasure volume V)) ≤
      ENNReal.ofReal (Real.exp (-2 * rate * (t : ℝ))) *
        ENNReal.ofReal (R ^ 2 + ∫ x, ‖x‖ ^ 2 ∂gibbsMeasure volume V)) :=
  euclidean_wasserstein_ball_of_gap_eq_curvature hB hV (gibbsSpectralGap hV hp) hgap_pos hHess hp rfl
    hcenter hd R hR t

/-- Source cutoff data have no invariance, Poincaré, affine-family,
Gaussian-law or eigenspace regularity fields. -/
structure EuclideanLangevinCutoffData (Ω : Type*) [MeasurableSpace Ω] (d : ℕ)
    extends SpectralInformationLowerData Ω d where
  centered : ∫ x, x ∂gibbsMeasure volume potential = 0

/-- The remaining invariance field of the conditional intermediary is
filled by the genuine stochastic Gibbs invariance theorem. -/
@[expose] noncomputable def euclideanCutoffToSpectral
    (D : EuclideanLangevinCutoffData Ω d) : SpectralLangevinCutoffData Ω d where
  potential := D.potential
  smooth := D.smooth
  rate := D.rate
  rate_pos := D.rate_pos
  hessian := D.hessian
  probability := D.probability
  centered := D.centered
  spectral := D.spectral
  driver := D.driver
  noiseLaw := D.noiseLaw
  brownian := D.brownian
  invariant := fun t => langevinKernel_gibbs_invariant D.brownian D.smooth D.probability
    D.rate D.rate_pos D.hessian t

@[expose] noncomputable def euclideanBallSquaredWasserstein
    (D : EuclideanLangevinCutoffData Ω d) (c t : ℝ) : ℝ :=
  spectralBallSquaredWasserstein (euclideanCutoffToSpectral D) c t

@[expose] noncomputable def euclideanBallWasserstein
    (D : EuclideanLangevinCutoffData Ω d) (c t : ℝ) : ℝ :=
  spectralBallWasserstein (euclideanCutoffToSpectral D) c t

theorem euclideanBallSquaredWasserstein_bounds
    (D : EuclideanLangevinCutoffData Ω d) (hd : 0 < d) {c t : ℝ} (hc : 0 ≤ c) (ht : 0 ≤ t) :
    c ^ 2 * ((d : ℝ) * Real.exp (-2 * D.rate * t)) ≤ euclideanBallSquaredWasserstein D c t ∧
      euclideanBallSquaredWasserstein D c t ≤
        (c ^ 2 + D.rate⁻¹) * ((d : ℝ) * Real.exp (-2 * D.rate * t)) :=
  spectralBallSquaredWasserstein_bounds (euclideanCutoffToSpectral D) hd hc ht

theorem euclidean_wasserstein_before_cutoff
    (D : ∀ n : ℕ, EuclideanLangevinCutoffData Ω n) {c ε : ℝ}
    (hc : 0 < c) (hε : 0 < ε) (hε1 : ε < 1) :
    Tendsto (fun n : ℕ => euclideanBallWasserstein (D n) c
      ((1 - ε) * criticalTime n (D n).rate)) atTop atTop :=
  spectral_wasserstein_before_cutoff (fun n => euclideanCutoffToSpectral (D n)) hc hε hε1

theorem euclidean_wasserstein_after_cutoff
    (D : ∀ n : ℕ, EuclideanLangevinCutoffData Ω n) {c ε : ℝ}
    (hc : 0 ≤ c) (hε : 0 < ε)
    (hliminf : 0 < liminf (fun n => ENNReal.ofReal (D n).rate) atTop) :
    Tendsto (fun n : ℕ => euclideanBallWasserstein (D n) c
      ((1 + ε) * criticalTime n (D n).rate)) atTop (𝓝 0) :=
  spectral_wasserstein_after_cutoff (fun n => euclideanCutoffToSpectral (D n)) hc hε hliminf

/-- Applying the proved spectral Poincaré inequality gives the dimension
upper bound used in the cutoff corollary. -/
theorem euclidean_wasserstein_ball_upper_dimension
    {B : ℝ≥0 → Ω → E} {P : Measure Ω} (hB : IsEuclideanBrownian B P)
    {V : E → ℝ} (hV : ContDiff ℝ 2 V) (hp : IsProbabilityMeasure (gibbsMeasure volume V))
    (hgap_pos : 0 < gibbsSpectralGap hV hp)
    (hHess : ∀ x z : E, gibbsSpectralGap hV hp * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (hcenter : ∫ x, x ∂gibbsMeasure volume V = 0) (hd : 0 < d)
    (R : ℝ) (hR : 0 ≤ R) (t : ℝ≥0) :
    (⨆ x : Metric.closedBall (0 : E) R,
      squaredWasserstein (langevinKernel V B P t (x : E)) (gibbsMeasure volume V)) ≤
      ENNReal.ofReal (Real.exp (-2 * gibbsSpectralGap hV hp * (t : ℝ))) *
        ENNReal.ofReal (R ^ 2 + d / gibbsSpectralGap hV hp) := by
  have hb := (euclidean_wasserstein_ball hB hV hp hgap_pos hHess hcenter hd R hR t).2
  have hm := gibbs_second_moment_le_dim_div_spectralGap hV hp hd (gibbsSpectralGap hV hp)
    hgap_pos hHess hcenter
  apply hb.trans
  gcongr

theorem euclideanCutoff_rate_eq_first_gap (D : EuclideanLangevinCutoffData Ω d) (hd : 0 < d) :
    D.rate = gibbsSpectralGap D.smooth D.probability := (D.spectral hd).symm

theorem euclideanBallWasserstein_eq_sqrt
    (D : EuclideanLangevinCutoffData Ω d) {c : ℝ} (hc : 0 ≤ c) (t : ℝ) :
    euclideanBallWasserstein D c t = Real.sqrt (euclideanBallSquaredWasserstein D c t) :=
  spectralBallWasserstein_eq_sqrt (euclideanCutoffToSpectral D) hc t

theorem euclideanBallSquaredWasserstein_ofReal
    (D : EuclideanLangevinCutoffData Ω d) (c t : ℝ) :
    ENNReal.ofReal (euclideanBallSquaredWasserstein D c t) =
      ⨆ x : Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) (c * Real.sqrt d),
        squaredWasserstein (langevinKernel D.potential D.driver D.noiseLaw t.toNNReal x)
          (gibbsMeasure volume D.potential) :=
  spectralBallSquaredWasserstein_ofReal (euclideanCutoffToSpectral D) c t

theorem euclidean_squaredWasserstein_before_cutoff
    (D : ∀ n : ℕ, EuclideanLangevinCutoffData Ω n) {c ε : ℝ}
    (hc : 0 < c) (hε : 0 < ε) (hε1 : ε < 1) :
    Tendsto (fun n : ℕ => euclideanBallSquaredWasserstein (D n) c
      ((1 - ε) * criticalTime n (D n).rate)) atTop atTop :=
  spectral_squaredWasserstein_before_cutoff (fun n => euclideanCutoffToSpectral (D n)) hc hε hε1

theorem euclidean_squaredWasserstein_after_cutoff
    (D : ∀ n : ℕ, EuclideanLangevinCutoffData Ω n) {c ε : ℝ}
    (hc : 0 ≤ c) (hε : 0 < ε)
    (hliminf : 0 < liminf (fun n => ENNReal.ofReal (D n).rate) atTop) :
    Tendsto (fun n : ℕ => euclideanBallSquaredWasserstein (D n) c
      ((1 + ε) * criticalTime n (D n).rate)) atTop (𝓝 0) :=
  spectral_squaredWasserstein_after_cutoff (fun n => euclideanCutoffToSpectral (D n)) hc hε hliminf

theorem euclideanLambdaPoint_eq_evaluation_norm {V : E → ℝ}
    (hV : ContDiff ℝ 2 V) (hp : IsProbabilityMeasure (gibbsMeasure volume V))
    (hgap_pos : 0 < gibbsSpectralGap hV hp)
    (hHess : ∀ x z : E, gibbsSpectralGap hV hp * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (x : E) : euclideanLambdaPoint hV hp hgap_pos hHess x =
      ‖firstEigenEvaluationCLM hV hp (gibbsSpectralGap hV hp) hgap_pos hHess rfl x‖ ^ 2 := rfl

theorem euclideanLambdaPoint_eq_supremum_bases {V : E → ℝ}
    (hV : ContDiff ℝ 2 V) (hp : IsProbabilityMeasure (gibbsMeasure volume V))
    (hgap_pos : 0 < gibbsSpectralGap hV hp)
    (hHess : ∀ x z : E, gibbsSpectralGap hV hp * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (x : E) :
    sSup (Set.range fun b : OrthonormalBasis
      (Fin (Module.finrank ℝ (gibbsFirstEigenspace hV hp))) ℝ (gibbsFirstEigenspace hV hp) =>
        ∑ i, |firstEigenRepresentative hV hp (gibbsSpectralGap hV hp) hgap_pos hHess rfl (b i) x| ^ 2) =
      euclideanLambdaPoint hV hp hgap_pos hHess x :=
  firstEigenLambdaPoint_eq_supremum_bases hV hp (gibbsSpectralGap hV hp) hgap_pos hHess rfl x

end CutoffRigidity
