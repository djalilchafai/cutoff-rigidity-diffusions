module

public import CutoffRigidity.Eigenmap
public import CutoffRigidity.GaussianTransport

/-!
# Assembling the eigenmap lower bound

This is the last probability-distance step in the proof of Theorem 1.1.
The projected-law equalities remain explicit obligations: this theorem does
not prove spectral splitting or Lemma 3.3's identification of the projected
diffusion. All measures and transport distances here are genuine objects.
-/

public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace CutoffRigidity

theorem eigenmap_transport_lower_bound {d k : ℕ}
    {v : Fin k → EuclideanSpace ℝ (Fin d)} (hv : Orthonormal ℝ v)
    (b : EuclideanSpace ℝ (Fin k)) (ρ t : ℝ) (hρ : 0 ≤ ρ) (ht : 0 ≤ t)
    (x₀ : EuclideanSpace ℝ (Fin d))
    (ν μ : Measure (EuclideanSpace ℝ (Fin d)))
    [IsProbabilityMeasure ν] [IsProbabilityMeasure μ]
    (hlaw : ν.map (fun x => eigenmapLinear v ρ x + b) =
      multivariateGaussian (Real.exp (-ρ * t) • (eigenmapLinear v ρ x₀ + b))
        ((1 - Real.exp (-2 * ρ * t)) • (1 : Matrix (Fin k) (Fin k) ℝ)))
    (hequilibrium : μ.map (fun x => eigenmapLinear v ρ x + b) =
      stdGaussian (EuclideanSpace ℝ (Fin k))) :
    ENNReal.ofReal (Real.exp (-2 * ρ * t) * ‖eigenmapLinear v ρ x₀ + b‖ ^ 2 +
      k * (1 - Real.sqrt (1 - Real.exp (-2 * ρ * t))) ^ 2) ≤
      ENNReal.ofReal ρ * squaredWasserstein ν μ := by
  have h := squaredWasserstein_map_le ν μ (eigenmapAffine_lipschitz hv hρ b)
  rw [hlaw, hequilibrium, squaredWasserstein_ou_marginal _ ρ t hρ ht] at h
  let K : ℝ≥0 := ⟨Real.sqrt ρ, Real.sqrt_nonneg ρ⟩
  have hfactor : (K : ℝ≥0∞) ^ 2 = ENNReal.ofReal ρ := by
    rw [show (K : ℝ≥0∞) = ENNReal.ofReal (Real.sqrt ρ) by
      exact (ENNReal.ofReal_coe_nnreal (p := K)).symm]
    rw [← ENNReal.ofReal_pow (Real.sqrt_nonneg ρ) 2, Real.sq_sqrt hρ]
  change _ ≤ (K : ℝ≥0∞) ^ 2 * squaredWasserstein ν μ at h
  rw [hfactor] at h
  simpa only [Fintype.card_fin] using h

end CutoffRigidity
