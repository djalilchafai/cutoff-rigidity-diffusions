module

public import CutoffRigidity.Brownian
public import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Independence
public import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Basic
public import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence
public import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic

/-! # Actual orthogonal projections of the Brownian driver

The Brownian noise in the affine eigenmap calculation is projected along
orthonormal rows. Its Brownian property follows from joint Gaussianity and
its computed covariance, including independence of the whole coordinate paths.
-/

public section

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace CutoffRigidity

variable {Ω : Type*} [MeasurableSpace Ω] {d k : ℕ}
  {B : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d)} {P : Measure Ω}

/-- The genuine vector Brownian driver is jointly Gaussian at all finite sets of times. -/
theorem IsEuclideanBrownian.isGaussianProcess (hB : IsEuclideanBrownian B P) :
    IsGaussianProcess B P := by
  classical
  constructor
  intro I
  let L : (Fin d → I → ℝ) →L[ℝ] (I → EuclideanSpace ℝ (Fin d)) :=
    LinearMap.toContinuousLinearMap
      { toFun := fun f t => WithLp.toLp 2 (fun i => f i t)
        map_add' := by intro x y; rfl
        map_smul' := by intro r x; rfl }
  have hi := hB.independent.comp (fun _ f => I.restrict f)
    (fun _ => Finset.measurable_restrict I)
  have hg := iIndepFun.hasGaussianLaw
    (fun i => (hB.coordinate i).isGaussianProcess.hasGaussianLaw I) hi
  exact hg.map L

/-- The actual covariance of two linear projections at arbitrary times. -/
theorem IsEuclideanBrownian.covariance_inner (hB : IsEuclideanBrownian B P)
    (a b : EuclideanSpace ℝ (Fin d)) (s t : ℝ≥0) :
    cov[fun ω => inner ℝ a (B s ω), fun ω => inner ℝ b (B t ω); P] =
      (min s t : ℝ) * inner ℝ a b := by
  let := hB.isProbabilityMeasure
  have hmem (i : Fin d) (u : ℝ≥0) : MemLp (fun ω => B u ω i) 2 P :=
    ((hB.coordinate i).isGaussianProcess.hasGaussianLaw_eval u).memLp_two
  have hcov (i j : Fin d) :
      cov[fun ω => B s ω i, fun ω => B t ω j; P] =
        if i = j then (min s t : ℝ) else 0 := by
    by_cases hij : i = j
    · subst j
      simpa using (hB.coordinate i).covariance_eval s t
    · rw [ite_eq_right hij]
      exact ((hB.independent.indepFun hij).comp
        (measurable_pi_apply s) (measurable_pi_apply t)).covariance_eq_zero
          (hmem i s) (hmem j t)
  simp only [PiLp.inner_apply, Real.inner_apply]
  rw [covariance_fun_sum_fun_sum
    (fun i => (hmem i s).const_mul (a i)) (fun i => (hmem i t).const_mul (b i))]
  simp only [covariance_const_mul_left, covariance_const_mul_right, hcov]
  simp only [mul_ite, mul_zero]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Linear projections remain centered. -/
theorem IsEuclideanBrownian.integral_inner (hB : IsEuclideanBrownian B P)
    (a : EuclideanSpace ℝ (Fin d)) (t : ℝ≥0) :
    (∫ ω, inner ℝ a (B t ω) ∂P) = 0 := by
  simp only [PiLp.inner_apply, Real.inner_apply]
  rw [integral_finsetSum _ (fun i _ => (hB.coordinate i).integrable_eval t |>.const_mul (a i))]
  simp only [integral_const_mul, (hB.coordinate _).integral_eval, mul_zero, Finset.sum_const_zero]

/-- The unscaled orthogonal projection used for the noise in Lemma 3.3. -/
@[expose] noncomputable def orthogonalBrownianProjection
    (v : Fin k → EuclideanSpace ℝ (Fin d))
    (B : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d)) :
    ℝ≥0 → Ω → EuclideanSpace ℝ (Fin k) :=
  fun t ω => WithLp.toLp 2 (fun i => inner ℝ (v i) (B t ω))

/-- Orthonormal projections of an actual standard Brownian driver are actual
standard Brownian motions, with independent full coordinate paths. -/
theorem IsEuclideanBrownian.orthogonalProjection (hB : IsEuclideanBrownian B P)
    {v : Fin k → EuclideanSpace ℝ (Fin d)} (hv : Orthonormal ℝ v) :
    IsEuclideanBrownian (orthogonalBrownianProjection v B) P := by
  have hG : IsGaussianProcess
      (fun (p : (_ : Fin k) × ℝ≥0) ω => inner ℝ (v p.1) (B p.2 ω)) P :=
    (hB.isGaussianProcess.comp_right (fun p : (_ : Fin k) × ℝ≥0 => p.2)).comp_left
      (fun p : (_ : Fin k) × ℝ≥0 => innerSL ℝ (v p.1))
  have hGi (i : Fin k) : IsGaussianProcess (fun t ω => inner ℝ (v i) (B t ω)) P :=
    hG.comp_right (fun t => ⟨i, t⟩)
  constructor
  · intro i
    refine ⟨(hGi i).isPreBrownianReal_of_covariance
      (fun t => hB.integral_inner (v i) t) ?_, ?_⟩
    · intro s t hst
      rw [hB.covariance_inner, orthonormal_iff_ite.mp hv, ite_eq_left rfl, mul_one]
      exact min_eq_left (show (s : ℝ) ≤ t from hst)
    · filter_upwards [hB.continuous_paths] with ω hω
      exact (innerSL ℝ (v i)).continuous.comp hω
  · apply hG.iIndepFun_of_covariance_eq_zero
      (fun i t => (hGi i).aemeasurable t)
    intro i j hij s t
    rw [hB.covariance_inner, orthonormal_iff_ite.mp hv, ite_eq_right hij, mul_zero]

end CutoffRigidity
