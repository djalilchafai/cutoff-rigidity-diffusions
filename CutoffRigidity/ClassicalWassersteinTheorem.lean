module

public import CutoffRigidity.ClassicalEigenspace
public import CutoffRigidity.AffineWassersteinEstimate
public import CutoffRigidity.Evaluation

/-!
# The classical-generator form of the Euclidean Wasserstein theorem

The actual classical Gibbs L² eigenspace supplies its unique continuous
representatives, orthonormal basis, evaluation functional and Gaussian
projection. No affine family or projected-law assumption is supplied.
Identification with the self-adjoint spectral eigenspace remains separate.
-/

public section

namespace CutoffRigidity

open Set MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

/-- The pointwise source Λ is the actual squared operator norm of evaluation. -/
@[expose] noncomputable def classicalLambdaPoint {V : E → ℝ} (hV : ContDiff ℝ 2 V)
    (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z) (x : E) : ℝ :=
  ‖classicalEigenEvaluationCLM hV ρ hρ hHess x‖ ^ 2

/-- The source set supremum is extended-valued, allowing unbounded sets. -/
@[expose] noncomputable def classicalLambda {V : E → ℝ} (hV : ContDiff ℝ 2 V)
    (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z) (S : Set E) : ℝ≥0∞ :=
  ⨆ x : S, ENNReal.ofReal (classicalLambdaPoint hV ρ hρ hHess x)

/-- Parseval proves the defining evaluation sum for every actual ONB. -/
theorem classicalLambdaPoint_eq_basis_sum {V : E → ℝ} (hV : ContDiff ℝ 2 V)
    (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ (classicalL2Eigenspace V ρ)) (x : E) :
    classicalLambdaPoint hV ρ hρ hHess x =
      ∑ i, |classicalEigenRepresentative V ρ (b i) x| ^ 2 := by
  let := classicalL2Eigenspace_finiteDimensional hV ρ hρ hHess
  exact (sum_abs_sq_evaluation_eq_norm_sq (classicalEigenEvaluationCLM hV ρ hρ hHess x) b).symm

/-- The paper's supremum over all orthonormal bases equals the actual
evaluation norm; finite dimensionality is derived from curvature rigidity. -/
theorem classicalLambdaPoint_eq_supremum_bases {V : E → ℝ} (hV : ContDiff ℝ 2 V)
    (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z) (x : E) :
    sSup (Set.range fun b : OrthonormalBasis
      (Fin (Module.finrank ℝ (classicalL2Eigenspace V ρ))) ℝ (classicalL2Eigenspace V ρ) =>
        ∑ i, |classicalEigenRepresentative V ρ (b i) x| ^ 2) =
      classicalLambdaPoint hV ρ hρ hHess x := by
  let := classicalL2Eigenspace_finiteDimensional hV ρ hρ hHess
  exact sSup_sum_abs_sq_evaluation_eq_norm_sq
    (classicalEigenEvaluationCLM hV ρ hρ hHess x)
    (stdOrthonormalBasis ℝ (classicalL2Eigenspace V ρ))

/-- In particular Λ equals the squared norm of the constructed actual eigenmap. -/
theorem classicalLambdaPoint_eq_eigenmap {V : E → ℝ} (hV : ContDiff ℝ 2 V)
    (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (hprob : IsProbabilityMeasure (gibbsMeasure volume V)) (x : E) :
    classicalLambdaPoint hV ρ hρ hHess x =
      ‖classicalEvaluationEigenmap hV ρ hρ hHess hprob x‖ ^ 2 := by
  rw [classicalLambdaPoint_eq_basis_sum hV ρ hρ hHess
    (classicalEigenOrthonormalBasis hV ρ hρ hHess hprob), EuclideanSpace.real_norm_sq_eq]
  simp only [classicalEvaluationEigenmap, sq_abs]

/-- The dimension in the theorem is the actual classical L² dimension. -/
theorem classicalL2Eigenspace_finrank_eq_rows {V : E → ℝ} (hV : ContDiff ℝ 2 V)
    (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (hprob : IsProbabilityMeasure (gibbsMeasure volume V)) :
    Module.finrank ℝ (classicalL2Eigenspace V ρ) = Module.finrank ℝ (affineEigenRows V ρ) :=
  (classicalEigenRowsEquiv hV ρ hρ hHess hprob).finrank_eq

/-- Centering the actual Gibbs equilibrium removes the forced affine constants. -/
theorem affineEigenConstant_eq_zero_of_centered {V : E → ℝ} (hV : ContDiff ℝ 2 V)
    (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (hprob : IsProbabilityMeasure (gibbsMeasure volume V))
    (hcenter : ∫ x, x ∂gibbsMeasure volume V = 0) (a : affineEigenRows V ρ) :
    affineEigenConstant V ρ a = 0 := by
  let := hprob
  by_cases ha : (a : E) = 0
  · simp [affineEigenConstant, ha]
  · have hm := affine_eigenfunction_mean_zero V (hV.differentiable (by norm_num)) a ha
      (affineEigenConstant V ρ a) ρ hρ (affineEigenRows_eigenfunction V hρ a) hprob
    have hi : Integrable (fun x : E => x) (gibbsMeasure volume V) :=
      (gibbs_memLp_two_id_of_hessian_bound hV ρ hρ hHess).integrable (by norm_num)
    rw [integral_add (hi.const_inner (a : E)) (integrable_const _), integral_inner hi,
      hcenter, inner_zero_right, zero_add, integral_const] at hm
    simpa using hm

/-- In the centered case the actual evaluation eigenmap is precisely the
linear eigenmap of the internally constructed orthonormal rows. -/
theorem classicalEvaluationEigenmap_eq_linear_of_centered {V : E → ℝ} (hV : ContDiff ℝ 2 V)
    (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (hprob : IsProbabilityMeasure (gibbsMeasure volume V))
    (hcenter : ∫ x, x ∂gibbsMeasure volume V = 0) (x : E) :
    classicalEvaluationEigenmap hV ρ hρ hHess hprob x =
      eigenmapLinear (affineEigenBasisRows V ρ) ρ x := by
  rw [classicalEvaluationEigenmap_eq_affine]
  apply congrArg (WithLp.toLp 2)
  funext i
  rw [affineEigenBasisFunction_representation,
    affineEigenConstant_eq_zero_of_centered hV ρ hρ hHess hprob hcenter, add_zero]

/-- The exact ball maximum of the actual evaluation norm in the centered
case; positive classical dimension supplies an attaining row direction. -/
theorem classicalLambdaPoint_ball_isGreatest {V : E → ℝ} (hV : ContDiff ℝ 2 V)
    (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (hprob : IsProbabilityMeasure (gibbsMeasure volume V))
    (hcenter : ∫ x, x ∂gibbsMeasure volume V = 0)
    (hk : 0 < Module.finrank ℝ (classicalL2Eigenspace V ρ)) {R : ℝ} (hR : 0 ≤ R) :
    IsGreatest ((classicalLambdaPoint hV ρ hρ hHess) '' Metric.closedBall (0 : E) R) (ρ * R ^ 2) := by
  have hk' : 0 < Module.finrank ℝ (affineEigenRows V ρ) := by
    rwa [classicalL2Eigenspace_finrank_eq_rows hV ρ hρ hHess hprob] at hk
  have hp (x : E) : classicalLambdaPoint hV ρ hρ hHess x =
      ‖eigenmapLinear (affineEigenBasisRows V ρ) ρ x‖ ^ 2 := by
    rw [classicalLambdaPoint_eq_eigenmap hV ρ hρ hHess hprob,
      classicalEvaluationEigenmap_eq_linear_of_centered hV ρ hρ hHess hprob hcenter]
  simpa only [funext hp] using eigenmapLinear_ball_isGreatest
    (affineEigenBasisRows_orthonormal V ρ) hρ.le hR (⟨0, hk'⟩ : Fin _)

/-- The real supremum in the paper's centered ball calculation. -/
theorem classicalLambdaPoint_ball_sup {V : E → ℝ} (hV : ContDiff ℝ 2 V)
    (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (hprob : IsProbabilityMeasure (gibbsMeasure volume V))
    (hcenter : ∫ x, x ∂gibbsMeasure volume V = 0)
    (hk : 0 < Module.finrank ℝ (classicalL2Eigenspace V ρ)) {R : ℝ} (hR : 0 ≤ R) :
    sSup ((classicalLambdaPoint hV ρ hρ hHess) '' Metric.closedBall (0 : E) R) = ρ * R ^ 2 :=
  (classicalLambdaPoint_ball_isGreatest hV ρ hρ hHess hprob hcenter hk hR).csSup_eq

/-- The actual extended-valued Λ has the same exact centered ball value. -/
theorem classicalLambda_ball {V : E → ℝ} (hV : ContDiff ℝ 2 V)
    (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (hprob : IsProbabilityMeasure (gibbsMeasure volume V))
    (hcenter : ∫ x, x ∂gibbsMeasure volume V = 0)
    (hk : 0 < Module.finrank ℝ (classicalL2Eigenspace V ρ)) {R : ℝ} (hR : 0 ≤ R) :
    classicalLambda hV ρ hρ hHess (Metric.closedBall (0 : E) R) = ENNReal.ofReal (ρ * R ^ 2) := by
  have hg := classicalLambdaPoint_ball_isGreatest hV ρ hρ hHess hprob hcenter hk hR
  apply le_antisymm
  · apply iSup_le
    intro x
    exact ENNReal.ofReal_le_ofReal (hg.2 ⟨x, x.property, rfl⟩)
  · obtain ⟨x, hx, heq⟩ := hg.1
    rw [← heq]
    exact le_iSup (fun y : Metric.closedBall (0 : E) R =>
      ENNReal.ofReal (classicalLambdaPoint hV ρ hρ hHess y)) ⟨x, hx⟩

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Pointwise lower estimate for the actual nonlinear Langevin kernel,
with the dimension and Λ of the actual classical L² eigenspace. -/
theorem classical_langevin_wasserstein_lower
    {B : ℝ≥0 → Ω → E} {P : Measure Ω} (hB : IsEuclideanBrownian B P)
    {V : E → ℝ} (hV : ContDiff ℝ 2 V) (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (hprob : IsProbabilityMeasure (gibbsMeasure volume V)) (x₀ : E) (t : ℝ≥0) :
    ENNReal.ofReal (Real.exp (-2 * ρ * (t : ℝ)) * classicalLambdaPoint hV ρ hρ hHess x₀ +
      Module.finrank ℝ (classicalL2Eigenspace V ρ) *
        (1 - Real.sqrt (1 - Real.exp (-2 * ρ * (t : ℝ)))) ^ 2) ≤
      ENNReal.ofReal ρ * squaredWasserstein (langevinKernel V B P t x₀) (gibbsMeasure volume V) := by
  rw [classicalL2Eigenspace_finrank_eq_rows hV ρ hρ hHess hprob,
    classicalLambdaPoint_eq_eigenmap hV ρ hρ hHess hprob, classicalEvaluationEigenmap_eq_affine]
  exact affine_langevin_wasserstein_lower hB hV ρ hρ.le hHess
    (fun i => (affineEigenBasisCoefficient V ρ i : E))
    (fun i => affineEigenConstant V ρ (affineEigenBasisCoefficient V ρ i)) ρ hρ
    (affineEigenBasisFunction_eigenfunction V hρ) hprob
    (affineEigenBasisFunction_integral_mul V (hV.differentiable (by norm_num)) hρ hprob) x₀ t

/-- The source's arbitrary-set lower estimate, with actual Λ and actual
classical eigenspace dimension; no boundedness premise on the starting set. -/
theorem classical_langevin_wasserstein_lower_supremum
    {B : ℝ≥0 → Ω → E} {P : Measure Ω} (hB : IsEuclideanBrownian B P)
    {V : E → ℝ} (hV : ContDiff ℝ 2 V) (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (hprob : IsProbabilityMeasure (gibbsMeasure volume V)) (S : Set E) (hS : S.Nonempty) (t : ℝ≥0) :
    ENNReal.ofReal (Real.exp (-2 * ρ * (t : ℝ))) * classicalLambda hV ρ hρ hHess S +
      ENNReal.ofReal (Module.finrank ℝ (classicalL2Eigenspace V ρ) *
        (1 - Real.sqrt (1 - Real.exp (-2 * ρ * (t : ℝ)))) ^ 2) ≤
      ENNReal.ofReal ρ * ⨆ x : S,
        squaredWasserstein (langevinKernel V B P t (x : E)) (gibbsMeasure volume V) := by
  let : Nonempty S := hS.to_subtype
  rw [classicalLambda, ENNReal.mul_iSup, ENNReal.iSup_add]
  apply iSup_le
  intro x
  have h := classical_langevin_wasserstein_lower hB hV ρ hρ hHess hprob x t
  have hΛ0 : 0 ≤ classicalLambdaPoint hV ρ hρ hHess x := sq_nonneg _
  rw [ENNReal.ofReal_add (mul_nonneg (Real.exp_pos _).le hΛ0) (by positivity),
    ENNReal.ofReal_mul (Real.exp_pos _).le] at h
  exact h.trans (mul_le_mul_right (le_iSup (fun y : S =>
    squaredWasserstein (langevinKernel V B P t (y : E)) (gibbsMeasure volume V)) x) _)

/-- The full arbitrary-starting-set Wasserstein theorem for the actual
classical eigenspace. The upper bound states Gibbs invariance explicitly. -/
theorem classical_euclidean_wasserstein_theorem
    {B : ℝ≥0 → Ω → E} {P : Measure Ω} (hB : IsEuclideanBrownian B P)
    {V : E → ℝ} (hV : ContDiff ℝ 2 V) (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (hprob : IsProbabilityMeasure (gibbsMeasure volume V)) (S : Set E) (hS : S.Nonempty) (t : ℝ≥0)
    (hinvariant : (langevinKernel V B P t) ∘ₘ (gibbsMeasure volume V) = gibbsMeasure volume V) :
    (ENNReal.ofReal ρ⁻¹ *
      (ENNReal.ofReal (Real.exp (-2 * ρ * (t : ℝ))) * classicalLambda hV ρ hρ hHess S +
        ENNReal.ofReal (Module.finrank ℝ (classicalL2Eigenspace V ρ) *
          (1 - Real.sqrt (1 - Real.exp (-2 * ρ * (t : ℝ)))) ^ 2)) ≤
      ⨆ x : S, squaredWasserstein (langevinKernel V B P t (x : E)) (gibbsMeasure volume V)) ∧
    ((⨆ x : S, squaredWasserstein (langevinKernel V B P t (x : E)) (gibbsMeasure volume V)) ≤
      ENNReal.ofReal (Real.exp (-2 * ρ * (t : ℝ))) *
        ⨆ x : S, ENNReal.ofReal (∫ y, ‖y - (x : E)‖ ^ 2 ∂gibbsMeasure volume V)) := by
  constructor
  · have h := classical_langevin_wasserstein_lower_supremum hB hV ρ hρ hHess hprob S hS t
    have hi : ENNReal.ofReal ρ⁻¹ * ENNReal.ofReal ρ = 1 := by
      rw [← ENNReal.ofReal_mul (inv_nonneg.mpr hρ.le), inv_mul_cancel₀ hρ.ne', ENNReal.ofReal_one]
    have hh := mul_le_mul_right h (ENNReal.ofReal ρ⁻¹)
    rwa [← mul_assoc, hi, one_mul] at hh
  · exact langevin_wasserstein_upper_iSup hB hV ρ hρ hHess hprob t hinvariant S

/-- The centered-ball corollary, including the exact Λ value and the genuine
second moment of the actual Gibbs equilibrium. -/
theorem classical_euclidean_wasserstein_ball
    {B : ℝ≥0 → Ω → E} {P : Measure Ω} (hB : IsEuclideanBrownian B P)
    {V : E → ℝ} (hV : ContDiff ℝ 2 V) (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (hprob : IsProbabilityMeasure (gibbsMeasure volume V))
    (hcenter : ∫ x, x ∂gibbsMeasure volume V = 0)
    (hk : 0 < Module.finrank ℝ (classicalL2Eigenspace V ρ)) (R : ℝ) (hR : 0 ≤ R) (t : ℝ≥0)
    (hinvariant : (langevinKernel V B P t) ∘ₘ (gibbsMeasure volume V) = gibbsMeasure volume V) :
    (ENNReal.ofReal (Real.exp (-2 * ρ * (t : ℝ)) * R ^ 2 +
      (Module.finrank ℝ (classicalL2Eigenspace V ρ) / ρ) *
        (1 - Real.sqrt (1 - Real.exp (-2 * ρ * (t : ℝ)))) ^ 2) ≤
      ⨆ x : Metric.closedBall (0 : E) R,
        squaredWasserstein (langevinKernel V B P t (x : E)) (gibbsMeasure volume V)) ∧
    ((⨆ x : Metric.closedBall (0 : E) R,
      squaredWasserstein (langevinKernel V B P t (x : E)) (gibbsMeasure volume V)) ≤
      ENNReal.ofReal (Real.exp (-2 * ρ * (t : ℝ))) *
        ENNReal.ofReal (R ^ 2 + ∫ x, ‖x‖ ^ 2 ∂gibbsMeasure volume V)) := by
  constructor
  · have hS : (Metric.closedBall (0 : E) R).Nonempty := ⟨0, by simpa using hR⟩
    have h := (classical_euclidean_wasserstein_theorem hB hV ρ hρ hHess hprob
      (Metric.closedBall (0 : E) R) hS t hinvariant).1
    rw [classicalLambda_ball hV ρ hρ hHess hprob hcenter hk hR,
      ← ENNReal.ofReal_mul (Real.exp_pos _).le,
      ← ENNReal.ofReal_add (by positivity) (by positivity),
      ← ENNReal.ofReal_mul (inv_nonneg.mpr hρ.le)] at h
    convert h using 1
    congr 1
    field_simp
  · exact langevin_wasserstein_upper_ball hB hV ρ hρ hHess hprob hcenter t hinvariant R

end CutoffRigidity
