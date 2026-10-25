module

public import CutoffRigidity.GibbsOperatorAffineRepresentative
public import CutoffRigidity.ClassicalWassersteinTheorem
public import CutoffRigidity.GibbsOperatorCurvatureGap

/-! # The Wasserstein theorem for the actual self-adjoint operator eigenspace

Weak Bochner rigidity proves that actual curvature-rate operator
eigenclasses have unique continuous affine representatives. Their genuine
continuous evaluation functional supplies the basis-independent source Λ.
The stochastic upper bound retains the explicit Gibbs invariance premise.
-/

public section

namespace CutoffRigidity

open Set MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

/-- The proved identification is an isometry for the actual Gibbs L² norm. -/
@[expose] noncomputable def operatorEigenClassicalIsometry {V : E → ℝ}
    (hV : ContDiff ℝ 2 V) (hp : IsProbabilityMeasure (gibbsMeasure volume V))
    (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z) :
    gibbsOperatorEigenspace hV hp ρ ≃ₗᵢ[ℝ] classicalL2Eigenspace V ρ :=
  LinearIsometryEquiv.ofEq _ _ (gibbsOperatorEigenspace_eq_classicalL2Eigenspace hV hp ρ hρ hHess)

theorem operatorEigenClassicalIsometry_coe {V : E → ℝ}
    (hV : ContDiff ℝ 2 V) (hp : IsProbabilityMeasure (gibbsMeasure volume V))
    (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (u : gibbsOperatorEigenspace hV hp ρ) :
    (operatorEigenClassicalIsometry hV hp ρ hρ hHess u : E →₂[gibbsMeasure volume V] ℝ) = u := rfl

theorem operatorEigenspace_finiteDimensional {V : E → ℝ}
    (hV : ContDiff ℝ 2 V) (hp : IsProbabilityMeasure (gibbsMeasure volume V))
    (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z) :
    FiniteDimensional ℝ (gibbsOperatorEigenspace hV hp ρ) := by
  let := classicalL2Eigenspace_finiteDimensional hV ρ hρ hHess
  exact FiniteDimensional.of_injective
    (operatorEigenClassicalIsometry hV hp ρ hρ hHess).toLinearMap
    (operatorEigenClassicalIsometry hV hp ρ hρ hHess).injective

theorem operatorEigenspace_finrank_eq_classical {V : E → ℝ}
    (hV : ContDiff ℝ 2 V) (hp : IsProbabilityMeasure (gibbsMeasure volume V))
    (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z) :
    Module.finrank ℝ (gibbsOperatorEigenspace hV hp ρ) = Module.finrank ℝ (classicalL2Eigenspace V ρ) :=
  (operatorEigenClassicalIsometry hV hp ρ hρ hHess).toLinearEquiv.finrank_eq

theorem operatorEigenspace_finrank_le {V : E → ℝ}
    (hV : ContDiff ℝ 2 V) (hp : IsProbabilityMeasure (gibbsMeasure volume V))
    (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z) :
    Module.finrank ℝ (gibbsOperatorEigenspace hV hp ρ) ≤ d := by
  rw [operatorEigenspace_finrank_eq_classical hV hp ρ hρ hHess]
  exact classicalL2Eigenspace_finrank_le hV ρ hρ hHess

/-- Evaluation always uses the unique continuous representative of the
actual operator eigenclass, never an arbitrary L² representative. -/
@[expose] noncomputable def operatorEigenRepresentative {V : E → ℝ}
    (hV : ContDiff ℝ 2 V) (hp : IsProbabilityMeasure (gibbsMeasure volume V))
    (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (u : gibbsOperatorEigenspace hV hp ρ) : E → ℝ :=
  classicalEigenRepresentative V ρ (operatorEigenClassicalIsometry hV hp ρ hρ hHess u)

theorem operatorEigenRepresentative_spec {V : E → ℝ}
    (hV : ContDiff ℝ 2 V) (hp : IsProbabilityMeasure (gibbsMeasure volume V))
    (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (u : gibbsOperatorEigenspace hV hp ρ) :
    ContDiff ℝ 2 (operatorEigenRepresentative hV hp ρ hρ hHess u) ∧
    (∀ x, langevinDifferentialOperator V (operatorEigenRepresentative hV hp ρ hρ hHess u) x =
      -ρ * operatorEigenRepresentative hV hp ρ hρ hHess u x) ∧
    operatorEigenRepresentative hV hp ρ hρ hHess u =ᵐ[gibbsMeasure volume V]
      (u : E →₂[gibbsMeasure volume V] ℝ) :=
  classicalEigenRepresentative_spec V ρ (operatorEigenClassicalIsometry hV hp ρ hρ hHess u)

theorem operatorEigenRepresentative_unique {V f : E → ℝ}
    (hV : ContDiff ℝ 2 V) (hp : IsProbabilityMeasure (gibbsMeasure volume V))
    (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (u : gibbsOperatorEigenspace hV hp ρ) (hf : Continuous f)
    (hae : f =ᵐ[gibbsMeasure volume V] (u : E →₂[gibbsMeasure volume V] ℝ)) :
    f = operatorEigenRepresentative hV hp ρ hρ hHess u :=
  classicalEigenRepresentative_unique hV.continuous ρ
    (operatorEigenClassicalIsometry hV hp ρ hρ hHess u) hf hae

@[expose] noncomputable def operatorEigenEvaluationCLM {V : E → ℝ}
    (hV : ContDiff ℝ 2 V) (hp : IsProbabilityMeasure (gibbsMeasure volume V))
    (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (x : E) : gibbsOperatorEigenspace hV hp ρ →L[ℝ] ℝ :=
  (classicalEigenEvaluationCLM hV ρ hρ hHess x).comp
    (operatorEigenClassicalIsometry hV hp ρ hρ hHess).toContinuousLinearEquiv.toContinuousLinearMap

theorem operatorEigenEvaluationCLM_apply {V : E → ℝ}
    (hV : ContDiff ℝ 2 V) (hp : IsProbabilityMeasure (gibbsMeasure volume V))
    (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (x : E) (u : gibbsOperatorEigenspace hV hp ρ) :
    operatorEigenEvaluationCLM hV hp ρ hρ hHess x u = operatorEigenRepresentative hV hp ρ hρ hHess u x := rfl

@[expose] noncomputable def operatorLambdaPoint {V : E → ℝ}
    (hV : ContDiff ℝ 2 V) (hp : IsProbabilityMeasure (gibbsMeasure volume V))
    (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z) (x : E) : ℝ :=
  ‖operatorEigenEvaluationCLM hV hp ρ hρ hHess x‖ ^ 2

@[expose] noncomputable def operatorLambda {V : E → ℝ}
    (hV : ContDiff ℝ 2 V) (hp : IsProbabilityMeasure (gibbsMeasure volume V))
    (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z) (S : Set E) : ℝ≥0∞ :=
  ⨆ x : S, ENNReal.ofReal (operatorLambdaPoint hV hp ρ hρ hHess x)

theorem operatorLambdaPoint_eq_classical {V : E → ℝ}
    (hV : ContDiff ℝ 2 V) (hp : IsProbabilityMeasure (gibbsMeasure volume V))
    (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z) (x : E) :
    operatorLambdaPoint hV hp ρ hρ hHess x = classicalLambdaPoint hV ρ hρ hHess x := by
  unfold operatorLambdaPoint operatorEigenEvaluationCLM classicalLambdaPoint
  rw [ContinuousLinearMap.opNorm_comp_linearIsometryEquiv]

theorem operatorLambda_eq_classical {V : E → ℝ}
    (hV : ContDiff ℝ 2 V) (hp : IsProbabilityMeasure (gibbsMeasure volume V))
    (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z) (S : Set E) :
    operatorLambda hV hp ρ hρ hHess S = classicalLambda hV ρ hρ hHess S := by
  unfold operatorLambda classicalLambda
  simp_rw [operatorLambdaPoint_eq_classical]

@[expose] noncomputable def operatorEigenOrthonormalBasis {V : E → ℝ}
    (hV : ContDiff ℝ 2 V) (hp : IsProbabilityMeasure (gibbsMeasure volume V))
    (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z) :
    OrthonormalBasis (Fin (Module.finrank ℝ (gibbsOperatorEigenspace hV hp ρ))) ℝ
      (gibbsOperatorEigenspace hV hp ρ) := by
  let := operatorEigenspace_finiteDimensional hV hp ρ hρ hHess
  exact stdOrthonormalBasis ℝ _

theorem operatorLambdaPoint_eq_basis_sum {V : E → ℝ}
    (hV : ContDiff ℝ 2 V) (hp : IsProbabilityMeasure (gibbsMeasure volume V))
    (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ (gibbsOperatorEigenspace hV hp ρ)) (x : E) :
    operatorLambdaPoint hV hp ρ hρ hHess x =
      ∑ i, |operatorEigenRepresentative hV hp ρ hρ hHess (b i) x| ^ 2 := by
  let := operatorEigenspace_finiteDimensional hV hp ρ hρ hHess
  exact (sum_abs_sq_evaluation_eq_norm_sq (operatorEigenEvaluationCLM hV hp ρ hρ hHess x) b).symm

theorem operatorLambdaPoint_eq_supremum_bases {V : E → ℝ}
    (hV : ContDiff ℝ 2 V) (hp : IsProbabilityMeasure (gibbsMeasure volume V))
    (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z) (x : E) :
    sSup (Set.range fun b : OrthonormalBasis
      (Fin (Module.finrank ℝ (gibbsOperatorEigenspace hV hp ρ))) ℝ (gibbsOperatorEigenspace hV hp ρ) =>
        ∑ i, |operatorEigenRepresentative hV hp ρ hρ hHess (b i) x| ^ 2) =
      operatorLambdaPoint hV hp ρ hρ hHess x := by
  let := operatorEigenspace_finiteDimensional hV hp ρ hρ hHess
  exact sSup_sum_abs_sq_evaluation_eq_norm_sq (operatorEigenEvaluationCLM hV hp ρ hρ hHess x)
    (operatorEigenOrthonormalBasis hV hp ρ hρ hHess)

@[expose] noncomputable def operatorEvaluationEigenmap {V : E → ℝ}
    (hV : ContDiff ℝ 2 V) (hp : IsProbabilityMeasure (gibbsMeasure volume V))
    (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z) (x : E) :
    EuclideanSpace ℝ (Fin (Module.finrank ℝ (gibbsOperatorEigenspace hV hp ρ))) :=
  WithLp.toLp 2 (fun i => operatorEigenRepresentative hV hp ρ hρ hHess
    (operatorEigenOrthonormalBasis hV hp ρ hρ hHess i) x)

theorem operatorLambdaPoint_eq_eigenmap {V : E → ℝ}
    (hV : ContDiff ℝ 2 V) (hp : IsProbabilityMeasure (gibbsMeasure volume V))
    (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z) (x : E) :
    operatorLambdaPoint hV hp ρ hρ hHess x = ‖operatorEvaluationEigenmap hV hp ρ hρ hHess x‖ ^ 2 := by
  rw [operatorLambdaPoint_eq_basis_sum hV hp ρ hρ hHess
    (operatorEigenOrthonormalBasis hV hp ρ hρ hHess), EuclideanSpace.real_norm_sq_eq]
  simp only [operatorEvaluationEigenmap, sq_abs]

/-- Transfer of the proved source estimate to the actual self-adjoint operator eigenspace. -/
theorem operatorLambdaPoint_ball_isGreatest {V : E → ℝ} (hV : ContDiff ℝ 2 V)
    (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (hprob : IsProbabilityMeasure (gibbsMeasure volume V))
    (hcenter : ∫ x, x ∂gibbsMeasure volume V = 0)
    (hk : 0 < Module.finrank ℝ (gibbsOperatorEigenspace hV hprob ρ)) {R : ℝ} (hR : 0 ≤ R) :
    IsGreatest ((operatorLambdaPoint hV hprob ρ hρ hHess) '' Metric.closedBall (0 : E) R) (ρ * R ^ 2) := by
  have hdim := operatorEigenspace_finrank_eq_classical hV hprob ρ hρ hHess
  have hk' : 0 < Module.finrank ℝ (classicalL2Eigenspace V ρ) := by
    rwa [hdim] at hk
  simpa only [operatorLambdaPoint_eq_classical, operatorLambda_eq_classical, hdim] using
    classicalLambdaPoint_ball_isGreatest hV ρ hρ hHess hprob hcenter hk' hR

/-- Transfer of the proved source estimate to the actual self-adjoint operator eigenspace. -/
theorem operatorLambdaPoint_ball_sup {V : E → ℝ} (hV : ContDiff ℝ 2 V)
    (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (hprob : IsProbabilityMeasure (gibbsMeasure volume V))
    (hcenter : ∫ x, x ∂gibbsMeasure volume V = 0)
    (hk : 0 < Module.finrank ℝ (gibbsOperatorEigenspace hV hprob ρ)) {R : ℝ} (hR : 0 ≤ R) :
    sSup ((operatorLambdaPoint hV hprob ρ hρ hHess) '' Metric.closedBall (0 : E) R) = ρ * R ^ 2 := by
  have hdim := operatorEigenspace_finrank_eq_classical hV hprob ρ hρ hHess
  have hk' : 0 < Module.finrank ℝ (classicalL2Eigenspace V ρ) := by
    rwa [hdim] at hk
  simpa only [operatorLambdaPoint_eq_classical, operatorLambda_eq_classical, hdim] using
    classicalLambdaPoint_ball_sup hV ρ hρ hHess hprob hcenter hk' hR

/-- Transfer of the proved source estimate to the actual self-adjoint operator eigenspace. -/
theorem operatorLambda_ball {V : E → ℝ} (hV : ContDiff ℝ 2 V)
    (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (hprob : IsProbabilityMeasure (gibbsMeasure volume V))
    (hcenter : ∫ x, x ∂gibbsMeasure volume V = 0)
    (hk : 0 < Module.finrank ℝ (gibbsOperatorEigenspace hV hprob ρ)) {R : ℝ} (hR : 0 ≤ R) :
    operatorLambda hV hprob ρ hρ hHess (Metric.closedBall (0 : E) R) = ENNReal.ofReal (ρ * R ^ 2) := by
  have hdim := operatorEigenspace_finrank_eq_classical hV hprob ρ hρ hHess
  have hk' : 0 < Module.finrank ℝ (classicalL2Eigenspace V ρ) := by
    rwa [hdim] at hk
  simpa only [operatorLambdaPoint_eq_classical, operatorLambda_eq_classical, hdim] using
    classicalLambda_ball hV ρ hρ hHess hprob hcenter hk' hR

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Transfer of the proved source estimate to the actual self-adjoint operator eigenspace. -/
theorem operator_langevin_wasserstein_lower
    {B : ℝ≥0 → Ω → E} {P : Measure Ω} (hB : IsEuclideanBrownian B P)
    {V : E → ℝ} (hV : ContDiff ℝ 2 V) (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (hprob : IsProbabilityMeasure (gibbsMeasure volume V)) (x₀ : E) (t : ℝ≥0) :
    ENNReal.ofReal (Real.exp (-2 * ρ * (t : ℝ)) * operatorLambdaPoint hV hprob ρ hρ hHess x₀ +
      Module.finrank ℝ (gibbsOperatorEigenspace hV hprob ρ) *
        (1 - Real.sqrt (1 - Real.exp (-2 * ρ * (t : ℝ)))) ^ 2) ≤
      ENNReal.ofReal ρ * squaredWasserstein (langevinKernel V B P t x₀) (gibbsMeasure volume V) := by
  have hdim := operatorEigenspace_finrank_eq_classical hV hprob ρ hρ hHess
  simpa only [operatorLambdaPoint_eq_classical, operatorLambda_eq_classical, hdim] using
    classical_langevin_wasserstein_lower hB hV ρ hρ hHess hprob x₀ t

/-- Transfer of the proved source estimate to the actual self-adjoint operator eigenspace. -/
theorem operator_langevin_wasserstein_lower_supremum
    {B : ℝ≥0 → Ω → E} {P : Measure Ω} (hB : IsEuclideanBrownian B P)
    {V : E → ℝ} (hV : ContDiff ℝ 2 V) (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (hprob : IsProbabilityMeasure (gibbsMeasure volume V)) (S : Set E) (hS : S.Nonempty) (t : ℝ≥0) :
    ENNReal.ofReal (Real.exp (-2 * ρ * (t : ℝ))) * operatorLambda hV hprob ρ hρ hHess S +
      ENNReal.ofReal (Module.finrank ℝ (gibbsOperatorEigenspace hV hprob ρ) *
        (1 - Real.sqrt (1 - Real.exp (-2 * ρ * (t : ℝ)))) ^ 2) ≤
      ENNReal.ofReal ρ * ⨆ x : S,
        squaredWasserstein (langevinKernel V B P t (x : E)) (gibbsMeasure volume V) := by
  have hdim := operatorEigenspace_finrank_eq_classical hV hprob ρ hρ hHess
  simpa only [operatorLambdaPoint_eq_classical, operatorLambda_eq_classical, hdim] using
    classical_langevin_wasserstein_lower_supremum hB hV ρ hρ hHess hprob S hS t

/-- Transfer of the proved source estimate to the actual self-adjoint operator eigenspace. -/
theorem operator_euclidean_wasserstein_theorem
    {B : ℝ≥0 → Ω → E} {P : Measure Ω} (hB : IsEuclideanBrownian B P)
    {V : E → ℝ} (hV : ContDiff ℝ 2 V) (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (hprob : IsProbabilityMeasure (gibbsMeasure volume V)) (S : Set E) (hS : S.Nonempty) (t : ℝ≥0)
    (hinvariant : (langevinKernel V B P t) ∘ₘ (gibbsMeasure volume V) = gibbsMeasure volume V) :
    (ENNReal.ofReal ρ⁻¹ *
      (ENNReal.ofReal (Real.exp (-2 * ρ * (t : ℝ))) * operatorLambda hV hprob ρ hρ hHess S +
        ENNReal.ofReal (Module.finrank ℝ (gibbsOperatorEigenspace hV hprob ρ) *
          (1 - Real.sqrt (1 - Real.exp (-2 * ρ * (t : ℝ)))) ^ 2)) ≤
      ⨆ x : S, squaredWasserstein (langevinKernel V B P t (x : E)) (gibbsMeasure volume V)) ∧
    ((⨆ x : S, squaredWasserstein (langevinKernel V B P t (x : E)) (gibbsMeasure volume V)) ≤
      ENNReal.ofReal (Real.exp (-2 * ρ * (t : ℝ))) *
        ⨆ x : S, ENNReal.ofReal (∫ y, ‖y - (x : E)‖ ^ 2 ∂gibbsMeasure volume V)) := by
  have hdim := operatorEigenspace_finrank_eq_classical hV hprob ρ hρ hHess
  simpa only [operatorLambdaPoint_eq_classical, operatorLambda_eq_classical, hdim] using
    classical_euclidean_wasserstein_theorem hB hV ρ hρ hHess hprob S hS t hinvariant

/-- Transfer of the proved source estimate to the actual self-adjoint operator eigenspace. -/
theorem operator_euclidean_wasserstein_ball
    {B : ℝ≥0 → Ω → E} {P : Measure Ω} (hB : IsEuclideanBrownian B P)
    {V : E → ℝ} (hV : ContDiff ℝ 2 V) (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (hprob : IsProbabilityMeasure (gibbsMeasure volume V))
    (hcenter : ∫ x, x ∂gibbsMeasure volume V = 0)
    (hk : 0 < Module.finrank ℝ (gibbsOperatorEigenspace hV hprob ρ)) (R : ℝ) (hR : 0 ≤ R) (t : ℝ≥0)
    (hinvariant : (langevinKernel V B P t) ∘ₘ (gibbsMeasure volume V) = gibbsMeasure volume V) :
    (ENNReal.ofReal (Real.exp (-2 * ρ * (t : ℝ)) * R ^ 2 +
      (Module.finrank ℝ (gibbsOperatorEigenspace hV hprob ρ) / ρ) *
        (1 - Real.sqrt (1 - Real.exp (-2 * ρ * (t : ℝ)))) ^ 2) ≤
      ⨆ x : Metric.closedBall (0 : E) R,
        squaredWasserstein (langevinKernel V B P t (x : E)) (gibbsMeasure volume V)) ∧
    ((⨆ x : Metric.closedBall (0 : E) R,
      squaredWasserstein (langevinKernel V B P t (x : E)) (gibbsMeasure volume V)) ≤
      ENNReal.ofReal (Real.exp (-2 * ρ * (t : ℝ))) *
        ENNReal.ofReal (R ^ 2 + ∫ x, ‖x‖ ^ 2 ∂gibbsMeasure volume V)) := by
  have hdim := operatorEigenspace_finrank_eq_classical hV hprob ρ hρ hHess
  have hk' : 0 < Module.finrank ℝ (classicalL2Eigenspace V ρ) := by
    rwa [hdim] at hk
  simpa only [operatorLambdaPoint_eq_classical, operatorLambda_eq_classical, hdim] using
    classical_euclidean_wasserstein_ball hB hV ρ hρ hHess hprob hcenter hk' R hR t hinvariant

/-- The genuine first eigenspace of the self-adjoint Gibbs operator is
taken at its canonical attained positive spectral gap. -/
@[expose] noncomputable def gibbsFirstEigenspace {V : E → ℝ}
    (hV : ContDiff ℝ 2 V) (hp : IsProbabilityMeasure (gibbsMeasure volume V)) :
    Submodule ℝ (E →₂[gibbsMeasure volume V] ℝ) :=
  gibbsOperatorEigenspace hV hp (gibbsSpectralGap hV hp)

@[expose] noncomputable def firstEigenCurvatureIsometry {V : E → ℝ}
    (hV : ContDiff ℝ 2 V) (hp : IsProbabilityMeasure (gibbsMeasure volume V))
    (ρ : ℝ) (hgap : gibbsSpectralGap hV hp = ρ) :
    gibbsFirstEigenspace hV hp ≃ₗᵢ[ℝ] gibbsOperatorEigenspace hV hp ρ :=
  LinearIsometryEquiv.ofEq _ _ (congrArg (gibbsOperatorEigenspace hV hp) hgap)

theorem firstEigenspace_finrank_eq_operator {V : E → ℝ}
    (hV : ContDiff ℝ 2 V) (hp : IsProbabilityMeasure (gibbsMeasure volume V))
    (ρ : ℝ) (hgap : gibbsSpectralGap hV hp = ρ) :
    Module.finrank ℝ (gibbsFirstEigenspace hV hp) =
      Module.finrank ℝ (gibbsOperatorEigenspace hV hp ρ) :=
  (firstEigenCurvatureIsometry hV hp ρ hgap).toLinearEquiv.finrank_eq

theorem firstEigenspace_finiteDimensional {V : E → ℝ}
    (hV : ContDiff ℝ 2 V) (hp : IsProbabilityMeasure (gibbsMeasure volume V))
    (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (hgap : gibbsSpectralGap hV hp = ρ) :
    FiniteDimensional ℝ (gibbsFirstEigenspace hV hp) := by
  let := operatorEigenspace_finiteDimensional hV hp ρ hρ hHess
  exact FiniteDimensional.of_injective (firstEigenCurvatureIsometry hV hp ρ hgap).toLinearMap
    (firstEigenCurvatureIsometry hV hp ρ hgap).injective

theorem firstEigenspace_finrank_pos {V : E → ℝ}
    (hV : ContDiff ℝ 2 V) (hp : IsProbabilityMeasure (gibbsMeasure volume V))
    (hd : 0 < d) (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (hgap : gibbsSpectralGap hV hp = ρ) :
    0 < Module.finrank ℝ (gibbsFirstEigenspace hV hp) := by
  let := firstEigenspace_finiteDimensional hV hp ρ hρ hHess hgap
  exact Module.finrank_pos_iff_exists_ne_zero.mpr
    (gibbsSpectralGap_hasEigenvector hV hp hd ρ hρ hHess)

@[expose] noncomputable def firstEigenRepresentative {V : E → ℝ}
    (hV : ContDiff ℝ 2 V) (hp : IsProbabilityMeasure (gibbsMeasure volume V))
    (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (hgap : gibbsSpectralGap hV hp = ρ) (u : gibbsFirstEigenspace hV hp) : E → ℝ :=
  operatorEigenRepresentative hV hp ρ hρ hHess (firstEigenCurvatureIsometry hV hp ρ hgap u)

@[expose] noncomputable def firstEigenEvaluationCLM {V : E → ℝ}
    (hV : ContDiff ℝ 2 V) (hp : IsProbabilityMeasure (gibbsMeasure volume V))
    (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (hgap : gibbsSpectralGap hV hp = ρ) (x : E) : gibbsFirstEigenspace hV hp →L[ℝ] ℝ :=
  (operatorEigenEvaluationCLM hV hp ρ hρ hHess x).comp
    (firstEigenCurvatureIsometry hV hp ρ hgap).toContinuousLinearEquiv.toContinuousLinearMap

theorem firstEigenEvaluationCLM_apply {V : E → ℝ}
    (hV : ContDiff ℝ 2 V) (hp : IsProbabilityMeasure (gibbsMeasure volume V))
    (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (hgap : gibbsSpectralGap hV hp = ρ) (x : E) (u : gibbsFirstEigenspace hV hp) :
    firstEigenEvaluationCLM hV hp ρ hρ hHess hgap x u =
      firstEigenRepresentative hV hp ρ hρ hHess hgap u x := rfl

@[expose] noncomputable def firstEigenLambdaPoint {V : E → ℝ}
    (hV : ContDiff ℝ 2 V) (hp : IsProbabilityMeasure (gibbsMeasure volume V))
    (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (hgap : gibbsSpectralGap hV hp = ρ) (x : E) : ℝ :=
  ‖firstEigenEvaluationCLM hV hp ρ hρ hHess hgap x‖ ^ 2

@[expose] noncomputable def firstEigenLambda {V : E → ℝ}
    (hV : ContDiff ℝ 2 V) (hp : IsProbabilityMeasure (gibbsMeasure volume V))
    (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (hgap : gibbsSpectralGap hV hp = ρ) (S : Set E) : ℝ≥0∞ :=
  ⨆ x : S, ENNReal.ofReal (firstEigenLambdaPoint hV hp ρ hρ hHess hgap x)

theorem firstEigenLambdaPoint_eq_operator {V : E → ℝ}
    (hV : ContDiff ℝ 2 V) (hp : IsProbabilityMeasure (gibbsMeasure volume V))
    (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (hgap : gibbsSpectralGap hV hp = ρ) (x : E) :
    firstEigenLambdaPoint hV hp ρ hρ hHess hgap x = operatorLambdaPoint hV hp ρ hρ hHess x := by
  unfold firstEigenLambdaPoint firstEigenEvaluationCLM operatorLambdaPoint
  rw [ContinuousLinearMap.opNorm_comp_linearIsometryEquiv]

theorem firstEigenLambda_eq_operator {V : E → ℝ}
    (hV : ContDiff ℝ 2 V) (hp : IsProbabilityMeasure (gibbsMeasure volume V))
    (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (hgap : gibbsSpectralGap hV hp = ρ) (S : Set E) :
    firstEigenLambda hV hp ρ hρ hHess hgap S = operatorLambda hV hp ρ hρ hHess S := by
  unfold firstEigenLambda operatorLambda
  simp_rw [firstEigenLambdaPoint_eq_operator]

@[expose] noncomputable def firstEigenOrthonormalBasis {V : E → ℝ}
    (hV : ContDiff ℝ 2 V) (hp : IsProbabilityMeasure (gibbsMeasure volume V))
    (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (hgap : gibbsSpectralGap hV hp = ρ) :
    OrthonormalBasis (Fin (Module.finrank ℝ (gibbsFirstEigenspace hV hp))) ℝ
      (gibbsFirstEigenspace hV hp) := by
  let := firstEigenspace_finiteDimensional hV hp ρ hρ hHess hgap
  exact stdOrthonormalBasis ℝ _

theorem firstEigenLambdaPoint_eq_basis_sum {V : E → ℝ}
    (hV : ContDiff ℝ 2 V) (hp : IsProbabilityMeasure (gibbsMeasure volume V))
    (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (hgap : gibbsSpectralGap hV hp = ρ)
    {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ (gibbsFirstEigenspace hV hp)) (x : E) :
    firstEigenLambdaPoint hV hp ρ hρ hHess hgap x =
      ∑ i, |firstEigenRepresentative hV hp ρ hρ hHess hgap (b i) x| ^ 2 := by
  let := firstEigenspace_finiteDimensional hV hp ρ hρ hHess hgap
  exact (sum_abs_sq_evaluation_eq_norm_sq (firstEigenEvaluationCLM hV hp ρ hρ hHess hgap x) b).symm

/-- The source estimate for the actual first eigenspace at its actual attained spectral gap. -/
theorem firstEigenLambdaPoint_ball_isGreatest {V : E → ℝ} (hV : ContDiff ℝ 2 V)
    (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (hprob : IsProbabilityMeasure (gibbsMeasure volume V))
    (hgap : gibbsSpectralGap hV hprob = ρ)
    (hcenter : ∫ x, x ∂gibbsMeasure volume V = 0)
    (hd : 0 < d) {R : ℝ} (hR : 0 ≤ R) :
    IsGreatest ((firstEigenLambdaPoint hV hprob ρ hρ hHess hgap) '' Metric.closedBall (0 : E) R) (ρ * R ^ 2) := by
  have hdim := firstEigenspace_finrank_eq_operator hV hprob ρ hgap
  have hk' : 0 < Module.finrank ℝ (gibbsOperatorEigenspace hV hprob ρ) := by
    simpa only [hdim] using firstEigenspace_finrank_pos hV hprob hd ρ hρ hHess hgap
  simpa only [firstEigenLambdaPoint_eq_operator, firstEigenLambda_eq_operator, hdim] using
    operatorLambdaPoint_ball_isGreatest hV ρ hρ hHess hprob hcenter hk' hR

/-- The source estimate for the actual first eigenspace at its actual attained spectral gap. -/
theorem firstEigenLambdaPoint_ball_sup {V : E → ℝ} (hV : ContDiff ℝ 2 V)
    (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (hprob : IsProbabilityMeasure (gibbsMeasure volume V))
    (hgap : gibbsSpectralGap hV hprob = ρ)
    (hcenter : ∫ x, x ∂gibbsMeasure volume V = 0)
    (hd : 0 < d) {R : ℝ} (hR : 0 ≤ R) :
    sSup ((firstEigenLambdaPoint hV hprob ρ hρ hHess hgap) '' Metric.closedBall (0 : E) R) = ρ * R ^ 2 := by
  have hdim := firstEigenspace_finrank_eq_operator hV hprob ρ hgap
  have hk' : 0 < Module.finrank ℝ (gibbsOperatorEigenspace hV hprob ρ) := by
    simpa only [hdim] using firstEigenspace_finrank_pos hV hprob hd ρ hρ hHess hgap
  simpa only [firstEigenLambdaPoint_eq_operator, firstEigenLambda_eq_operator, hdim] using
    operatorLambdaPoint_ball_sup hV ρ hρ hHess hprob hcenter hk' hR

/-- The source estimate for the actual first eigenspace at its actual attained spectral gap. -/
theorem firstEigenLambda_ball {V : E → ℝ} (hV : ContDiff ℝ 2 V)
    (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (hprob : IsProbabilityMeasure (gibbsMeasure volume V))
    (hgap : gibbsSpectralGap hV hprob = ρ)
    (hcenter : ∫ x, x ∂gibbsMeasure volume V = 0)
    (hd : 0 < d) {R : ℝ} (hR : 0 ≤ R) :
    firstEigenLambda hV hprob ρ hρ hHess hgap (Metric.closedBall (0 : E) R) = ENNReal.ofReal (ρ * R ^ 2) := by
  have hdim := firstEigenspace_finrank_eq_operator hV hprob ρ hgap
  have hk' : 0 < Module.finrank ℝ (gibbsOperatorEigenspace hV hprob ρ) := by
    simpa only [hdim] using firstEigenspace_finrank_pos hV hprob hd ρ hρ hHess hgap
  simpa only [firstEigenLambdaPoint_eq_operator, firstEigenLambda_eq_operator, hdim] using
    operatorLambda_ball hV ρ hρ hHess hprob hcenter hk' hR

/-- The source estimate for the actual first eigenspace at its actual attained spectral gap. -/
theorem first_eigenspace_langevin_wasserstein_lower
    {B : ℝ≥0 → Ω → E} {P : Measure Ω} (hB : IsEuclideanBrownian B P)
    {V : E → ℝ} (hV : ContDiff ℝ 2 V) (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (hprob : IsProbabilityMeasure (gibbsMeasure volume V))
    (hgap : gibbsSpectralGap hV hprob = ρ) (x₀ : E) (t : ℝ≥0) :
    ENNReal.ofReal (Real.exp (-2 * ρ * (t : ℝ)) * firstEigenLambdaPoint hV hprob ρ hρ hHess hgap x₀ +
      Module.finrank ℝ (gibbsFirstEigenspace hV hprob) *
        (1 - Real.sqrt (1 - Real.exp (-2 * ρ * (t : ℝ)))) ^ 2) ≤
      ENNReal.ofReal ρ * squaredWasserstein (langevinKernel V B P t x₀) (gibbsMeasure volume V) := by
  have hdim := firstEigenspace_finrank_eq_operator hV hprob ρ hgap
  simpa only [firstEigenLambdaPoint_eq_operator, firstEigenLambda_eq_operator, hdim] using
    operator_langevin_wasserstein_lower hB hV ρ hρ hHess hprob x₀ t

/-- The source estimate for the actual first eigenspace at its actual attained spectral gap. -/
theorem first_eigenspace_langevin_wasserstein_lower_supremum
    {B : ℝ≥0 → Ω → E} {P : Measure Ω} (hB : IsEuclideanBrownian B P)
    {V : E → ℝ} (hV : ContDiff ℝ 2 V) (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (hprob : IsProbabilityMeasure (gibbsMeasure volume V))
    (hgap : gibbsSpectralGap hV hprob = ρ) (S : Set E) (hS : S.Nonempty) (t : ℝ≥0) :
    ENNReal.ofReal (Real.exp (-2 * ρ * (t : ℝ))) * firstEigenLambda hV hprob ρ hρ hHess hgap S +
      ENNReal.ofReal (Module.finrank ℝ (gibbsFirstEigenspace hV hprob) *
        (1 - Real.sqrt (1 - Real.exp (-2 * ρ * (t : ℝ)))) ^ 2) ≤
      ENNReal.ofReal ρ * ⨆ x : S,
        squaredWasserstein (langevinKernel V B P t (x : E)) (gibbsMeasure volume V) := by
  have hdim := firstEigenspace_finrank_eq_operator hV hprob ρ hgap
  simpa only [firstEigenLambdaPoint_eq_operator, firstEigenLambda_eq_operator, hdim] using
    operator_langevin_wasserstein_lower_supremum hB hV ρ hρ hHess hprob S hS t

/-- The source estimate for the actual first eigenspace at its actual attained spectral gap. -/
theorem first_eigenspace_euclidean_wasserstein_theorem
    {B : ℝ≥0 → Ω → E} {P : Measure Ω} (hB : IsEuclideanBrownian B P)
    {V : E → ℝ} (hV : ContDiff ℝ 2 V) (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (hprob : IsProbabilityMeasure (gibbsMeasure volume V))
    (hgap : gibbsSpectralGap hV hprob = ρ) (S : Set E) (hS : S.Nonempty) (t : ℝ≥0)
    (hinvariant : (langevinKernel V B P t) ∘ₘ (gibbsMeasure volume V) = gibbsMeasure volume V) :
    (ENNReal.ofReal ρ⁻¹ *
      (ENNReal.ofReal (Real.exp (-2 * ρ * (t : ℝ))) * firstEigenLambda hV hprob ρ hρ hHess hgap S +
        ENNReal.ofReal (Module.finrank ℝ (gibbsFirstEigenspace hV hprob) *
          (1 - Real.sqrt (1 - Real.exp (-2 * ρ * (t : ℝ)))) ^ 2)) ≤
      ⨆ x : S, squaredWasserstein (langevinKernel V B P t (x : E)) (gibbsMeasure volume V)) ∧
    ((⨆ x : S, squaredWasserstein (langevinKernel V B P t (x : E)) (gibbsMeasure volume V)) ≤
      ENNReal.ofReal (Real.exp (-2 * ρ * (t : ℝ))) *
        ⨆ x : S, ENNReal.ofReal (∫ y, ‖y - (x : E)‖ ^ 2 ∂gibbsMeasure volume V)) := by
  have hdim := firstEigenspace_finrank_eq_operator hV hprob ρ hgap
  simpa only [firstEigenLambdaPoint_eq_operator, firstEigenLambda_eq_operator, hdim] using
    operator_euclidean_wasserstein_theorem hB hV ρ hρ hHess hprob S hS t hinvariant

/-- The source estimate for the actual first eigenspace at its actual attained spectral gap. -/
theorem first_eigenspace_euclidean_wasserstein_ball
    {B : ℝ≥0 → Ω → E} {P : Measure Ω} (hB : IsEuclideanBrownian B P)
    {V : E → ℝ} (hV : ContDiff ℝ 2 V) (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (hprob : IsProbabilityMeasure (gibbsMeasure volume V))
    (hgap : gibbsSpectralGap hV hprob = ρ)
    (hcenter : ∫ x, x ∂gibbsMeasure volume V = 0)
    (hd : 0 < d) (R : ℝ) (hR : 0 ≤ R) (t : ℝ≥0)
    (hinvariant : (langevinKernel V B P t) ∘ₘ (gibbsMeasure volume V) = gibbsMeasure volume V) :
    (ENNReal.ofReal (Real.exp (-2 * ρ * (t : ℝ)) * R ^ 2 +
      (Module.finrank ℝ (gibbsFirstEigenspace hV hprob) / ρ) *
        (1 - Real.sqrt (1 - Real.exp (-2 * ρ * (t : ℝ)))) ^ 2) ≤
      ⨆ x : Metric.closedBall (0 : E) R,
        squaredWasserstein (langevinKernel V B P t (x : E)) (gibbsMeasure volume V)) ∧
    ((⨆ x : Metric.closedBall (0 : E) R,
      squaredWasserstein (langevinKernel V B P t (x : E)) (gibbsMeasure volume V)) ≤
      ENNReal.ofReal (Real.exp (-2 * ρ * (t : ℝ))) *
        ENNReal.ofReal (R ^ 2 + ∫ x, ‖x‖ ^ 2 ∂gibbsMeasure volume V)) := by
  have hdim := firstEigenspace_finrank_eq_operator hV hprob ρ hgap
  have hk' : 0 < Module.finrank ℝ (gibbsOperatorEigenspace hV hprob ρ) := by
    simpa only [hdim] using firstEigenspace_finrank_pos hV hprob hd ρ hρ hHess hgap
  simpa only [firstEigenLambdaPoint_eq_operator, firstEigenLambda_eq_operator, hdim] using
    operator_euclidean_wasserstein_ball hB hV ρ hρ hHess hprob hcenter hk' R hR t hinvariant

theorem firstEigenspace_finrank_le {V : E → ℝ}
    (hV : ContDiff ℝ 2 V) (hp : IsProbabilityMeasure (gibbsMeasure volume V))
    (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (hgap : gibbsSpectralGap hV hp = ρ) :
    Module.finrank ℝ (gibbsFirstEigenspace hV hp) ≤ d := by
  rw [firstEigenspace_finrank_eq_operator hV hp ρ hgap]
  exact operatorEigenspace_finrank_le hV hp ρ hρ hHess

theorem firstEigenLambdaPoint_eq_supremum_bases {V : E → ℝ}
    (hV : ContDiff ℝ 2 V) (hp : IsProbabilityMeasure (gibbsMeasure volume V))
    (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (hgap : gibbsSpectralGap hV hp = ρ) (x : E) :
    sSup (Set.range fun b : OrthonormalBasis
      (Fin (Module.finrank ℝ (gibbsFirstEigenspace hV hp))) ℝ (gibbsFirstEigenspace hV hp) =>
        ∑ i, |firstEigenRepresentative hV hp ρ hρ hHess hgap (b i) x| ^ 2) =
      firstEigenLambdaPoint hV hp ρ hρ hHess hgap x := by
  let := firstEigenspace_finiteDimensional hV hp ρ hρ hHess hgap
  exact sSup_sum_abs_sq_evaluation_eq_norm_sq (firstEigenEvaluationCLM hV hp ρ hρ hHess hgap x)
    (firstEigenOrthonormalBasis hV hp ρ hρ hHess hgap)

end CutoffRigidity
