module

public import Mathlib.Probability.BrownianMotion.Basic
public import CutoffRigidity.GaussianEntropy

/-!
# The standard Euclidean Brownian driver

The paper's standard Brownian motion is represented by independent actual
real Brownian coordinate processes. This uses Mathlib's Brownian predicate,
including its finite-dimensional laws and almost-sure continuity. The
resulting driver has the genuine multivariate Gaussian marginal law.
-/

public section

namespace CutoffRigidity

open MeasureTheory ProbabilityTheory
open scoped NNReal

variable {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]

/-- Standard Euclidean Brownian motion, through independent Brownian coordinates. -/
structure IsEuclideanBrownian (B : ℝ≥0 → Ω → EuclideanSpace ℝ ι) (P : Measure Ω) : Prop where
  coordinate : ∀ i, IsBrownianReal (fun t ω => B t ω i) P
  independent : iIndepFun (fun i ω => fun t : ℝ≥0 => B t ω i) P

theorem IsEuclideanBrownian.continuous_paths
    {B : ℝ≥0 → Ω → EuclideanSpace ℝ ι} {P : Measure Ω}
    (hB : IsEuclideanBrownian B P) : ∀ᵐ ω ∂P, Continuous (fun t => B t ω) := by
  have hc : ∀ᵐ ω ∂P, ∀ i, Continuous (fun t => B t ω i) :=
    ae_all_iff.mpr (fun i => (hB.coordinate i).cont)
  filter_upwards [hc] with ω hω
  exact (PiLp.continuous_toLp 2 (fun _ : ι => ℝ)).comp (continuous_pi_iff.mpr hω)

theorem IsEuclideanBrownian.initial_ae_eq_zero
    {B : ℝ≥0 → Ω → EuclideanSpace ℝ ι} {P : Measure Ω}
    (hB : IsEuclideanBrownian B P) : ∀ᵐ ω ∂P, B 0 ω = 0 := by
  have hzero : ∀ᵐ ω ∂P, ∀ i, B 0 ω i = 0 :=
    ae_all_iff.mpr (fun i => (hB.coordinate i).eval_zero_ae_eq_zero)
  filter_upwards [hzero] with ω hω
  ext i
  exact hω i

omit [Fintype ι] in
theorem IsEuclideanBrownian.independent_eval
    {B : ℝ≥0 → Ω → EuclideanSpace ℝ ι} {P : Measure Ω}
    (hB : IsEuclideanBrownian B P) (t : ℝ≥0) :
    iIndepFun (fun i ω => B t ω i) P := by
  exact hB.independent.comp (fun _ f => f t) (fun _ => measurable_pi_apply t)

variable [DecidableEq ι]

/-- The standard Gaussian marginal with covariance `t I`, derived from the
actual independent Brownian coordinate laws. -/
theorem IsEuclideanBrownian.hasLaw_eval
    {B : ℝ≥0 → Ω → EuclideanSpace ℝ ι} {P : Measure Ω}
    (hB : IsEuclideanBrownian B P) (t : ℝ≥0) :
    HasLaw (B t) (multivariateGaussian (0 : EuclideanSpace ℝ ι)
      ((t : ℝ) • (1 : Matrix ι ι ℝ))) P := by
  have hp : HasLaw (fun ω i => B t ω i) (Measure.pi (fun _ : ι => gaussianReal 0 t)) P :=
    (hB.independent_eval t).hasLaw_pi (fun i => (hB.coordinate i).hasLaw_eval t)
  have hm := hasLaw_map (P := Measure.pi (fun _ : ι => gaussianReal 0 t))
    ((MeasurableEquiv.toLp (p := 2) (ι → ℝ)).measurable.aemeasurable)
  have h := hm.comp hp
  change HasLaw (B t)
    ((Measure.pi (fun _ : ι => gaussianReal 0 t)).map (WithLp.toLp 2)) P at h
  have hgauss : (Measure.pi (fun _ : ι => gaussianReal 0 t)).map (WithLp.toLp 2) =
      multivariateGaussian (0 : EuclideanSpace ℝ ι) (Matrix.diagonal (fun _ : ι => (t : ℝ))) := by
    simpa using gaussian_pi_eq_multivariate (0 : EuclideanSpace ℝ ι) (fun _ => t)
  rw [hgauss] at h
  have hcov : Matrix.diagonal (fun _ : ι => (t : ℝ)) = (t : ℝ) • (1 : Matrix ι ι ℝ) := by
    ext i j
    by_cases hij : i = j <;> simp [hij]
  simpa only [hcov] using h

theorem IsEuclideanBrownian.isProbabilityMeasure
    {B : ℝ≥0 → Ω → EuclideanSpace ℝ ι} {P : Measure Ω}
    (hB : IsEuclideanBrownian B P) : IsProbabilityMeasure P :=
  (hB.hasLaw_eval 0).isProbabilityMeasure

theorem IsEuclideanBrownian.aemeasurable_eval
    {B : ℝ≥0 → Ω → EuclideanSpace ℝ ι} {P : Measure Ω}
    (hB : IsEuclideanBrownian B P) (t : ℝ≥0) : AEMeasurable (B t) P :=
  (hB.hasLaw_eval t).aemeasurable

/-- Genuine Brownian increments have the multivariate Gaussian law with
covariance equal to the elapsed absolute time. -/
theorem IsEuclideanBrownian.hasLaw_sub
    {B : ℝ≥0 → Ω → EuclideanSpace ℝ ι} {P : Measure Ω}
    (hB : IsEuclideanBrownian B P) (s t : ℝ≥0) :
    HasLaw (fun ω => B s ω - B t ω)
      (multivariateGaussian (0 : EuclideanSpace ℝ ι)
        ((nndist (s : ℝ) (t : ℝ) : ℝ) • (1 : Matrix ι ι ℝ))) P := by
  have hi : iIndepFun (fun i ω => B s ω i - B t ω i) P :=
    hB.independent.comp (fun _ f => f s - f t) (fun _ => by fun_prop)
  have hp : HasLaw (fun ω i => B s ω i - B t ω i)
      (Measure.pi (fun _ : ι => gaussianReal 0 (nndist (s : ℝ) (t : ℝ)))) P :=
    hi.hasLaw_pi (fun i => (hB.coordinate i).hasLaw_sub s t)
  have hm := hasLaw_map
    (P := Measure.pi (fun _ : ι => gaussianReal 0 (nndist (s : ℝ) (t : ℝ))))
    ((MeasurableEquiv.toLp (p := 2) (ι → ℝ)).measurable.aemeasurable)
  have h := hm.comp hp
  change HasLaw (fun ω => B s ω - B t ω)
    ((Measure.pi (fun _ : ι => gaussianReal 0 (nndist (s : ℝ) (t : ℝ)))).map (WithLp.toLp 2)) P at h
  have hgauss : (Measure.pi (fun _ : ι => gaussianReal 0 (nndist (s : ℝ) (t : ℝ)))).map
      (WithLp.toLp 2) = multivariateGaussian (0 : EuclideanSpace ℝ ι)
      ((nndist (s : ℝ) (t : ℝ) : ℝ) • (1 : Matrix ι ι ℝ)) := by
    have hg := gaussian_pi_eq_multivariate (0 : EuclideanSpace ℝ ι)
      (fun _ => nndist (s : ℝ) (t : ℝ))
    have hcov : Matrix.diagonal (fun _ : ι => (nndist (s : ℝ) (t : ℝ) : ℝ)) =
        (nndist (s : ℝ) (t : ℝ) : ℝ) • (1 : Matrix ι ι ℝ) := by
      ext i j
      by_cases hij : i = j <;> simp [hij]
    simpa only [PiLp.zero_apply, hcov] using hg
  rwa [hgauss] at h

end CutoffRigidity
