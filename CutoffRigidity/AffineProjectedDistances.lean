module

public import CutoffRigidity.VectorMehlerLaw
public import CutoffRigidity.AffineEigenmapGaussian
public import CutoffRigidity.LangevinKernel
public import CutoffRigidity.TotalVariation
public import CutoffRigidity.GaussianEntropy
public import Mathlib.InformationTheory.KullbackLeibler.DataProcessing

/-!
# Actual affine-eigenmap entropy and total-variation lower bounds

This is the projection argument in the entropy/TV lower-bound paragraph of
Section 3. The affine coordinate equations and their genuine Gibbs L² Gram
matrix imply both Gaussian laws. Data processing is then applied to the actual
Brownian Langevin kernel. This treats the affine-eigenmap component; identifying
it with the entire first eigenspace additionally needs spectral rigidity.
-/

public section

namespace CutoffRigidity

open MeasureTheory ProbabilityTheory InformationTheory
open scoped NNReal ENNReal

variable {Ω : Type*} [MeasurableSpace Ω] {d k : ℕ}

/-- The actual tuple of affine pointwise eigenfunctions. -/
@[expose] noncomputable def affineEigenfunctionMap (a : Fin k → (EuclideanSpace ℝ (Fin d))) (b : Fin k → ℝ)
    (x : (EuclideanSpace ℝ (Fin d))) : (EuclideanSpace ℝ (Fin k)) := WithLp.toLp 2 (fun i => inner ℝ (a i) x + b i)

variable {B : ℝ≥0 → Ω → (EuclideanSpace ℝ (Fin d))} {P : Measure Ω} (hB : IsEuclideanBrownian B P)
    {V : (EuclideanSpace ℝ (Fin d)) → ℝ} (hV : ContDiff ℝ 2 V) (κ : ℝ) (hκ : 0 ≤ κ)
    (hHess : ∀ x z : (EuclideanSpace ℝ (Fin d)), κ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (a : Fin k → (EuclideanSpace ℝ (Fin d))) (b : Fin k → ℝ) (ρ : ℝ) (hρ : 0 < ρ)
    (heigen : ∀ i x, langevinDifferentialOperator V (fun y => inner ℝ (a i) y + b i) x =
      -ρ * (inner ℝ (a i) x + b i))
    (hprob : IsProbabilityMeasure (gibbsMeasure volume V))
    (horth : ∀ i j, ∫ x, (inner ℝ (a i) x + b i) * (inner ℝ (a j) x + b j)
      ∂gibbsMeasure volume V = if i = j then 1 else 0)

include hB hV hκ hHess hρ heigen hprob horth

/-- The actual nonlinear transition kernel has the proved OU eigenmap law. -/
theorem langevinKernel_map_affineEigenfunctionMap (x₀ : (EuclideanSpace ℝ (Fin d))) (t : ℝ≥0) :
    (langevinKernel V B P t x₀).map (affineEigenfunctionMap a b) =
      ouLaw ρ t (affineEigenfunctionMap a b x₀) := by
  have hv := affine_eigenfunction_normalized_rows_orthonormal V
    (hV.differentiable (by norm_num)) a b ρ hρ heigen hprob horth
  have hrep (x : EuclideanSpace ℝ (Fin d)) :
      eigenmapCLM (normalizedAffineRows a ρ) ρ x + WithLp.toLp 2 b =
      affineEigenfunctionMap a b x := affine_eigenfunction_eigenmap_representation a b hρ x
  have he : ∀ x i, langevinDifferentialOperator V
      (fun y => (eigenmapCLM (normalizedAffineRows a ρ) ρ y + WithLp.toLp 2 b) i) x =
      -ρ * (eigenmapCLM (normalizedAffineRows a ρ) ρ x + WithLp.toLp 2 b) i := by
    intro x i
    simp_rw [hrep]
    convert! heigen i x using 1
  have hLaw := langevinProcess_eigenmap_hasLaw hB hV κ hκ hHess
    (normalizedAffineRows a ρ) hv (WithLp.toLp 2 b) ρ hρ he x₀ t
  simp_rw [hrep] at hLaw
  rw [langevinKernel_apply_eq_process_law hB hV κ hκ hHess,
    (show Measurable (affineEigenfunctionMap a b) by unfold affineEigenfunctionMap; fun_prop).aemeasurable.map_map_of_aemeasurable
      (langevinProcess_aemeasurable_eval hB hV κ hκ hHess x₀ t),
    ouLaw_eq_multivariateGaussian hρ.le t.coe_nonneg]
  convert! hLaw.map_eq using 1

omit hB κ hκ hHess in
/-- Equilibrium projection follows from the affine equations and L² moments. -/
theorem gibbsMeasure_map_affineEigenfunctionMap :
    (gibbsMeasure volume V).map (affineEigenfunctionMap a b) = stdGaussian (EuclideanSpace ℝ (Fin k)) :=
  (affine_eigenmap_hasLaw_stdGaussian V (hV.differentiable (by norm_num)) a b
    ρ hρ heigen hprob horth).map_eq

/-- The paper's actual total-variation projection inequality. -/
theorem totalVariationDistance_langevinKernel_ge_ouLaw (x₀ : (EuclideanSpace ℝ (Fin d))) (t : ℝ≥0) :
    totalVariationDistance (ouLaw ρ t (affineEigenfunctionMap a b x₀)) (stdGaussian (EuclideanSpace ℝ (Fin k))) ≤
      totalVariationDistance (langevinKernel V B P t x₀) (gibbsMeasure volume V) := by
  let := hprob
  let := langevinKernel_isMarkovKernel hB hV κ hκ hHess t
  have h := totalVariationDistance_map_le (langevinKernel V B P t x₀)
    (gibbsMeasure volume V) (T := affineEigenfunctionMap a b)
    (by unfold affineEigenfunctionMap; fun_prop)
  rwa [langevinKernel_map_affineEigenfunctionMap hB hV κ hκ hHess a b ρ hρ heigen hprob horth,
    gibbsMeasure_map_affineEigenfunctionMap hV a b ρ hρ heigen hprob horth] at h

/-- A concrete projected Gaussian halfspace separates the actual nonlinear
transition law from equilibrium. -/
theorem totalVariationDistance_langevinKernel_affine_halfspace_lower
    (x₀ : (EuclideanSpace ℝ (Fin d))) (t : ℝ≥0) (i : Fin k) (hm : 0 < inner ℝ (a i) x₀ + b i) :
    1 - 4 * (2 - Real.exp (-2 * ρ * (t : ℝ))) /
      (Real.exp (-ρ * (t : ℝ)) * (inner ℝ (a i) x₀ + b i)) ^ 2 ≤
      totalVariationDistance (langevinKernel V B P t x₀) (gibbsMeasure volume V) := by
  have hmean : 0 < (Real.exp (-ρ * (t : ℝ)) • affineEigenfunctionMap a b x₀) i := by
    change 0 < Real.exp (-ρ * (t : ℝ)) * (inner ℝ (a i) x₀ + b i)
    exact mul_pos (Real.exp_pos _) hm
  have h := totalVariationDistance_affineGaussian_lower
    (Real.exp (-ρ * (t : ℝ)) • affineEigenfunctionMap a b x₀)
    (ouNoise ρ t) (ouNoise_nonneg ρ t) i hmean
  rw [ouNoise_sq hρ.le t.coe_nonneg] at h
  have hnorm : (1 - Real.exp (-2 * ρ * (t : ℝ))) + 1 =
      2 - Real.exp (-2 * ρ * (t : ℝ)) := by ring
  rw [hnorm] at h
  have hp := totalVariationDistance_langevinKernel_ge_ouLaw
    hB hV κ hκ hHess a b ρ hρ heigen hprob horth x₀ t
  rw [affineGaussian_eq_multivariateGaussian _ _ (ouNoise_nonneg ρ t),
    ouNoise_sq hρ.le t.coe_nonneg] at h
  rw [ouLaw_eq_multivariateGaussian hρ.le t.coe_nonneg] at hp
  convert! h.trans hp using 1

/-- Genuine relative entropy contracts under the actual affine eigenmap. -/
theorem klDiv_langevinKernel_ge_ouLaw (x₀ : (EuclideanSpace ℝ (Fin d))) (t : ℝ≥0) :
    klDiv (ouLaw ρ t (affineEigenfunctionMap a b x₀)) (stdGaussian (EuclideanSpace ℝ (Fin k))) ≤
      klDiv (langevinKernel V B P t x₀) (gibbsMeasure volume V) := by
  let := hprob
  let := langevinKernel_isMarkovKernel hB hV κ hκ hHess t
  have h := klDiv_map_le (langevinKernel V B P t x₀) (gibbsMeasure volume V)
    (g := affineEigenfunctionMap a b) (by unfold affineEigenfunctionMap; fun_prop)
  rwa [langevinKernel_map_affineEigenfunctionMap hB hV κ hκ hHess a b ρ hρ heigen hprob horth,
    gibbsMeasure_map_affineEigenfunctionMap hV a b ρ hρ heigen hprob horth] at h

/-- The exact projected Gaussian entropy gives a pointwise lower bound for
the actual nonlinear Langevin kernel, as in the paper's mapping argument. -/
theorem klDiv_langevinKernel_affine_lower (x₀ : (EuclideanSpace ℝ (Fin d))) (t : ℝ≥0) (ht : 0 < (t : ℝ)) :
    ENNReal.ofReal ((Real.exp (-2 * ρ * (t : ℝ)) * ‖affineEigenfunctionMap a b x₀‖ ^ 2 +
      k * (-Real.exp (-2 * ρ * (t : ℝ)) - Real.log (1 - Real.exp (-2 * ρ * (t : ℝ))))) / 2) ≤
      klDiv (langevinKernel V B P t x₀) (gibbsMeasure volume V) := by
  have h := klDiv_langevinKernel_ge_ouLaw hB hV κ hκ hHess a b ρ hρ heigen hprob horth x₀ t
  rw [ouLaw_eq_multivariateGaussian hρ.le t.coe_nonneg,
    klDiv_ou_marginal k (affineEigenfunctionMap a b x₀) ρ t hρ ht] at h
  exact h


/-- Dropping the nonnegative Gaussian covariance entropy correction gives
the paper's exponentially decaying mean lower bound for the genuine KL. -/
theorem klDiv_langevinKernel_affine_mean_lower
    (x₀ : EuclideanSpace ℝ (Fin d)) (t : ℝ≥0) (ht : 0 < (t : ℝ)) :
    ENNReal.ofReal (Real.exp (-2 * ρ * (t : ℝ)) * ‖affineEigenfunctionMap a b x₀‖ ^ 2 / 2) ≤
      klDiv (langevinKernel V B P t x₀) (gibbsMeasure volume V) := by
  apply le_trans _ (klDiv_langevinKernel_affine_lower
    hB hV κ hκ hHess a b ρ hρ heigen hprob horth x₀ t ht)
  apply ENNReal.ofReal_le_ofReal
  have hq : Real.exp (-2 * ρ * (t : ℝ)) < 1 :=
    Real.exp_lt_one_iff.mpr (by nlinarith [mul_pos hρ ht])
  have hlog := Real.log_le_sub_one_of_pos (sub_pos.mpr hq)
  have hcorr : 0 ≤ -Real.exp (-2 * ρ * (t : ℝ)) -
      Real.log (1 - Real.exp (-2 * ρ * (t : ℝ))) := by linarith
  have := mul_nonneg (Nat.cast_nonneg k : (0 : ℝ) ≤ k) hcorr
  linarith

/-- A uniform covariance bound gives a simple projected separating-halfspace
estimate for the actual nonlinear kernel. -/
theorem totalVariationDistance_langevinKernel_affine_mean_lower
    (x₀ : EuclideanSpace ℝ (Fin d)) (t : ℝ≥0) (i : Fin k)
    (hm : 0 < inner ℝ (a i) x₀ + b i) :
    1 - 8 / (Real.exp (-ρ * (t : ℝ)) * (inner ℝ (a i) x₀ + b i)) ^ 2 ≤
      totalVariationDistance (langevinKernel V B P t x₀) (gibbsMeasure volume V) := by
  apply le_trans _ (totalVariationDistance_langevinKernel_affine_halfspace_lower
    hB hV κ hκ hHess a b ρ hρ heigen hprob horth x₀ t i hm)
  have hc : 4 * (2 - Real.exp (-2 * ρ * (t : ℝ))) ≤ 8 := by
    nlinarith [Real.exp_pos (-2 * ρ * (t : ℝ))]
  exact sub_le_sub_left (div_le_div_of_nonneg_right hc (sq_nonneg _)) 1

end CutoffRigidity
