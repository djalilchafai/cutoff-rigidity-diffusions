module

public import CutoffRigidity.Riemann.TransportW2

/-! # Transport, step 3: exact `W₂` cost of the rescaled Mehler law against the equilibrium

On `ℝ^k`, with `γ_ρ = N(0, ρ⁻¹ I)` and the Mehler law `N(e^{-ρt} z, ρ⁻¹(1-e^{-2ρt}) I)` of the
Euclidean factor, the rescaled (`√ρ`) laws have squared `W₂` cost
`ρ e^{-2ρt}‖z‖² + k (1 - √(1-e^{-2ρt}))²`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace CutoffRigidity.Riemann

variable {k : ℕ}

theorem cost2_eq_squaredWasserstein (μ ν : Measure (EuclideanSpace ℝ (Fin k))) :
    cost2 μ ν = CutoffRigidity.squaredWasserstein μ ν := by
  unfold cost2 CutoffRigidity.squaredWasserstein
  rw [iInf_subtype']
  rfl

/-- Rescaling an isotropic Gaussian. -/
theorem affineGaussian_map_smul (m : EuclideanSpace ℝ (Fin k)) (s c : ℝ) :
    (CutoffRigidity.affineGaussian m s).map (fun x => c • x) =
      CutoffRigidity.affineGaussian (c • m) (c * s) := by
  unfold CutoffRigidity.affineGaussian
  rw [Measure.map_map (by fun_prop) (by fun_prop)]
  congr 1
  ext x
  simp [smul_add, smul_smul]

/-- The equilibrium Gaussian after rescaling is standard. -/
theorem gaussian_equilibrium_rescaled {ρ : ℝ} (hρ : 0 < ρ) :
    (multivariateGaussian (0 : EuclideanSpace ℝ (Fin k))
        (ρ⁻¹ • (1 : Matrix (Fin k) (Fin k) ℝ))).map (fun x => Real.sqrt ρ • x) =
      stdGaussian (EuclideanSpace ℝ (Fin k)) := by
  have hs : ρ⁻¹ • (1 : Matrix (Fin k) (Fin k) ℝ) =
      (Real.sqrt ρ⁻¹) ^ 2 • (1 : Matrix (Fin k) (Fin k) ℝ) := by
    rw [Real.sq_sqrt (inv_nonneg.2 hρ.le)]
  rw [hs, ← CutoffRigidity.affineGaussian_eq_multivariateGaussian _ _ (Real.sqrt_nonneg _),
    affineGaussian_map_smul]
  have : Real.sqrt ρ * Real.sqrt ρ⁻¹ = 1 := by
    rw [← Real.sqrt_mul hρ.le, mul_inv_cancel₀ hρ.ne', Real.sqrt_one]
  rw [this, smul_zero]
  exact CutoffRigidity.affineGaussian_zero_one

/-- The rescaled Mehler law. -/
theorem mehler_rescaled {ρ t : ℝ} (hρ : 0 < ρ) (ht : 0 ≤ t) (z : EuclideanSpace ℝ (Fin k)) :
    (multivariateGaussian (Real.exp (-ρ * t) • z)
        ((ρ⁻¹ * (1 - Real.exp (-2 * ρ * t))) • (1 : Matrix (Fin k) (Fin k) ℝ))).map
        (fun x => Real.sqrt ρ • x) =
      CutoffRigidity.affineGaussian (Real.sqrt ρ • (Real.exp (-ρ * t) • z))
        (Real.sqrt (1 - Real.exp (-2 * ρ * t))) := by
  have hq : 0 ≤ 1 - Real.exp (-2 * ρ * t) := by
    have : Real.exp (-2 * ρ * t) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith)
    linarith
  have hs : (ρ⁻¹ * (1 - Real.exp (-2 * ρ * t))) • (1 : Matrix (Fin k) (Fin k) ℝ) =
      (Real.sqrt (ρ⁻¹ * (1 - Real.exp (-2 * ρ * t)))) ^ 2 • (1 : Matrix (Fin k) (Fin k) ℝ) := by
    rw [Real.sq_sqrt (mul_nonneg (inv_nonneg.2 hρ.le) hq)]
  rw [hs, ← CutoffRigidity.affineGaussian_eq_multivariateGaussian _ _ (Real.sqrt_nonneg _),
    affineGaussian_map_smul]
  congr 2
  rw [← Real.sqrt_mul hρ.le, ← mul_assoc, mul_inv_cancel₀ hρ.ne', one_mul]

/-- Exact cost of the rescaled Mehler law against the standard Gaussian. -/
theorem cost2_mehler_rescaled {ρ t : ℝ} (hρ : 0 < ρ) (ht : 0 ≤ t)
    (z : EuclideanSpace ℝ (Fin k)) :
    cost2 ((multivariateGaussian (Real.exp (-ρ * t) • z)
        ((ρ⁻¹ * (1 - Real.exp (-2 * ρ * t))) • (1 : Matrix (Fin k) (Fin k) ℝ))).map
        (fun x => Real.sqrt ρ • x))
      ((multivariateGaussian (0 : EuclideanSpace ℝ (Fin k))
        (ρ⁻¹ • (1 : Matrix (Fin k) (Fin k) ℝ))).map (fun x => Real.sqrt ρ • x)) =
      ENNReal.ofReal (ρ * (Real.exp (-2 * ρ * t) * ‖z‖ ^ 2) +
        k * (1 - Real.sqrt (1 - Real.exp (-2 * ρ * t))) ^ 2) := by
  rw [mehler_rescaled hρ ht, gaussian_equilibrium_rescaled hρ, cost2_eq_squaredWasserstein,
    CutoffRigidity.squaredWasserstein_affineGaussian _ _ (Real.sqrt_nonneg _)]
  congr 1
  rw [norm_smul, norm_smul, mul_pow, mul_pow, Real.norm_eq_abs, Real.norm_eq_abs, sq_abs, sq_abs,
    Real.sq_sqrt hρ.le]
  have : (Real.exp (-ρ * t)) ^ 2 = Real.exp (-2 * ρ * t) := by
    rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  rw [this, Fintype.card_fin]
  ring

end CutoffRigidity.Riemann
