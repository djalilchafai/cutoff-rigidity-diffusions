module

public import CutoffRigidity.VectorMehlerLaw
public import CutoffRigidity.AffineEigenmapGaussian
public import CutoffRigidity.LangevinKernel
public import CutoffRigidity.EuclideanLowerBound
public import CutoffRigidity.SecondMoment
public import CutoffRigidity.GibbsMoments

/-! # Actual affine eigenmap Wasserstein estimates

These estimates use the constructed nonlinear Langevin kernel, the actual
Gibbs equilibrium, the derived projected Mehler law, and its exact Gaussian
transport cost. They concern actual affine pointwise eigenfunctions. Matching
them with the full first L² eigenspace still requires spectral attainment and
analytic rigidity. The upper bound states invariance of the actual Gibbs law
explicitly; it assumes no transport estimate.
-/

public section

namespace CutoffRigidity

open Set MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

variable {Ω : Type*} [MeasurableSpace Ω] {d k : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

/-- Pointwise lower bound for the actual nonlinear transition kernel, with
all Gaussian pushforward laws derived from actual affine eigenfunctions. -/
theorem affine_langevin_wasserstein_lower
    {B : ℝ≥0 → Ω → E} {P : Measure Ω} (hB : IsEuclideanBrownian B P)
    {V : EuclideanSpace ℝ (Fin d) → ℝ} (hV : ContDiff ℝ 2 V) (κ : ℝ) (hκ : 0 ≤ κ)
    (hHess : ∀ x z, κ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (a : Fin k → EuclideanSpace ℝ (Fin d)) (b : Fin k → ℝ) (ρ : ℝ) (hρ : 0 < ρ)
    (heigen : ∀ i x, langevinDifferentialOperator V (fun y => inner ℝ (a i) y + b i) x =
      -ρ * (inner ℝ (a i) x + b i))
    (hprob : IsProbabilityMeasure (gibbsMeasure volume V))
    (horth : ∀ i j, ∫ x, (inner ℝ (a i) x + b i) * (inner ℝ (a j) x + b j)
      ∂gibbsMeasure volume V = if i = j then 1 else 0)
    (x₀ : E) (t : ℝ≥0) :
    ENNReal.ofReal (Real.exp (-2 * ρ * (t : ℝ)) *
      ‖WithLp.toLp 2 (fun i => inner ℝ (a i) x₀ + b i)‖ ^ 2 +
      k * (1 - Real.sqrt (1 - Real.exp (-2 * ρ * (t : ℝ)))) ^ 2) ≤
      ENNReal.ofReal ρ * squaredWasserstein (langevinKernel V B P t x₀) (gibbsMeasure volume V) := by
  let := hprob
  let := langevinKernel_isMarkovKernel hB hV κ hκ hHess t
  let v := normalizedAffineRows a ρ
  have hv : Orthonormal ℝ v :=
    affine_eigenfunction_normalized_rows_orthonormal V (hV.differentiable (by norm_num))
      a b ρ hρ heigen hprob horth
  have hid (x : E) : eigenmapCLM v ρ x + WithLp.toLp 2 b =
      WithLp.toLp 2 (fun i => inner ℝ (a i) x + b i) :=
    affine_eigenfunction_eigenmap_representation a b hρ x
  have heig : ∀ x i, langevinDifferentialOperator V
      (fun y => (eigenmapCLM v ρ y + WithLp.toLp 2 b) i) x =
        -ρ * (eigenmapCLM v ρ x + WithLp.toLp 2 b) i := by
    intro x i
    simp_rw [hid]
    exact heigen i x
  have hlaw := langevinProcess_eigenmap_hasLaw hB hV κ hκ hHess v hv
    (WithLp.toLp 2 b) ρ hρ heig x₀ t
  have heq := normalized_affine_eigenmap_hasLaw_stdGaussian V
    (hV.differentiable (by norm_num)) a b ρ hρ heigen hprob horth
  have hmap : (langevinKernel V B P t x₀).map (fun x => eigenmapLinear v ρ x + WithLp.toLp 2 b) =
      multivariateGaussian (Real.exp (-ρ * (t : ℝ)) • (eigenmapLinear v ρ x₀ + WithLp.toLp 2 b))
        ((1 - Real.exp (-2 * ρ * (t : ℝ))) • (1 : Matrix (Fin k) (Fin k) ℝ)) := by
    rw [langevinKernel_apply_eq_process_law hB hV κ hκ hHess]
    have hm : Measurable (fun x : E => eigenmapLinear v ρ x + WithLp.toLp 2 b) := by
      exact (eigenmapAffine_lipschitz hv hρ.le (WithLp.toLp 2 b)).continuous.measurable
    rw [hm.aemeasurable.map_map_of_aemeasurable
      (langevinProcess_aemeasurable_eval hB hV κ hκ hHess x₀ t)]
    exact hlaw.map_eq
  have h := eigenmap_transport_lower_bound hv (WithLp.toLp 2 b) ρ t hρ.le t.coe_nonneg x₀
    (langevinKernel V B P t x₀) (gibbsMeasure volume V) hmap heq.map_eq
  rw [← eigenmapCLM_apply, hid] at h
  exact h

/-- A nonzero orthonormal row gives the ball lower bound even with an
arbitrary affine constant: choose one of the two antipodal row directions. -/
theorem exists_ball_affine_eigenmap_norm_sq_ge
    {v : Fin k → E} (hv : Orthonormal ℝ v) (b : EuclideanSpace ℝ (Fin k))
    {ρ R : ℝ} (hρ : 0 ≤ ρ) (hR : 0 ≤ R) (j : Fin k) :
    ∃ x ∈ Metric.closedBall (0 : E) R, ρ * R ^ 2 ≤ ‖eigenmapCLM v ρ x + b‖ ^ 2 := by
  let u : E := R • v j
  have hmem : u ∈ Metric.closedBall (0 : E) R := by
    simp [u, Metric.mem_closedBall, dist_zero_right, norm_smul, hv.norm_eq_one, abs_of_nonneg hR]
  have hnorm : ‖eigenmapCLM v ρ u‖ ^ 2 = ρ * R ^ 2 :=
    eigenmapLinear_norm_sq_smul_row hv hρ R j
  by_cases hi : 0 ≤ inner ℝ (eigenmapCLM v ρ u) b
  · refine ⟨u, hmem, ?_⟩
    rw [norm_add_sq_real, hnorm]
    nlinarith [sq_nonneg ‖b‖]
  · refine ⟨-u, ?_, ?_⟩
    · simpa only [Metric.mem_closedBall, dist_zero_right, norm_neg] using hmem
    · rw [map_neg, norm_add_sq_real, norm_neg, inner_neg_left, hnorm]
      nlinarith [sq_nonneg ‖b‖]

section UniformLower

variable {B : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d)} {P : Measure Ω} (hB : IsEuclideanBrownian B P)
  {V : EuclideanSpace ℝ (Fin d) → ℝ} (hV : ContDiff ℝ 2 V) (κ : ℝ) (hκ : 0 ≤ κ)
  (hHess : ∀ x z, κ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
  (a : Fin k → EuclideanSpace ℝ (Fin d)) (b : Fin k → ℝ) (ρ : ℝ) (hρ : 0 < ρ)
  (heigen : ∀ i x, langevinDifferentialOperator V (fun y => inner ℝ (a i) y + b i) x =
    -ρ * (inner ℝ (a i) x + b i))
  (hprob : IsProbabilityMeasure (gibbsMeasure volume V))
  (horth : ∀ i j, ∫ x, (inner ℝ (a i) x + b i) * (inner ℝ (a j) x + b j)
    ∂gibbsMeasure volume V = if i = j then 1 else 0)

include hB hV κ hκ hHess hρ heigen hprob horth

/-- Extended suprema over arbitrary starting sets require no boundedness assumption. -/
theorem affine_langevin_wasserstein_lower_iSup (S : Set E) (t : ℝ≥0) :
    (⨆ x : S, ENNReal.ofReal (Real.exp (-2 * ρ * (t : ℝ)) *
      ‖WithLp.toLp 2 (fun i => inner ℝ (a i) (x : E) + b i)‖ ^ 2 +
      k * (1 - Real.sqrt (1 - Real.exp (-2 * ρ * (t : ℝ)))) ^ 2)) ≤
      ENNReal.ofReal ρ * ⨆ x : S,
        squaredWasserstein (langevinKernel V B P t (x : E)) (gibbsMeasure volume V) := by
  apply iSup_le
  intro x
  exact (affine_langevin_wasserstein_lower hB hV κ hκ hHess a b ρ hρ heigen hprob horth x t).trans
    (mul_le_mul_right (le_iSup (fun y : S => squaredWasserstein
      (langevinKernel V B P t (y : E)) (gibbsMeasure volume V)) x) _)

/-- The source's extended eigenmap supremum form, for a nonempty starting set. -/
theorem affine_langevin_wasserstein_lower_supremum (S : Set E) (hS : S.Nonempty) (t : ℝ≥0) :
    ENNReal.ofReal (Real.exp (-2 * ρ * (t : ℝ))) *
      (⨆ x : S, ENNReal.ofReal (‖WithLp.toLp 2 (fun i => inner ℝ (a i) (x : E) + b i)‖ ^ 2)) +
      ENNReal.ofReal (k * (1 - Real.sqrt (1 - Real.exp (-2 * ρ * (t : ℝ)))) ^ 2) ≤
      ENNReal.ofReal ρ * ⨆ x : S,
        squaredWasserstein (langevinKernel V B P t (x : E)) (gibbsMeasure volume V) := by
  let : Nonempty S := hS.to_subtype
  rw [ENNReal.mul_iSup, ENNReal.iSup_add]
  have h := affine_langevin_wasserstein_lower_iSup hB hV κ hκ hHess a b ρ hρ heigen hprob horth S t
  convert h using 1
  congr 1
  funext x
  rw [ENNReal.ofReal_add (mul_nonneg (Real.exp_pos _).le (sq_nonneg _)) (by positivity),
    ENNReal.ofReal_mul (Real.exp_pos _).le]

/-- The actual transition laws obey the source ball lower estimate whenever
at least one normalized affine eigenfunction is present. -/
theorem affine_langevin_wasserstein_lower_ball (R : ℝ) (hR : 0 ≤ R) (j : Fin k) (t : ℝ≥0) :
    ENNReal.ofReal (Real.exp (-2 * ρ * (t : ℝ)) * (ρ * R ^ 2) +
      k * (1 - Real.sqrt (1 - Real.exp (-2 * ρ * (t : ℝ)))) ^ 2) ≤
      ENNReal.ofReal ρ * ⨆ x : Metric.closedBall (0 : E) R,
        squaredWasserstein (langevinKernel V B P t (x : E)) (gibbsMeasure volume V) := by
  have hv := affine_eigenfunction_normalized_rows_orthonormal V
    (hV.differentiable (by norm_num)) a b ρ hρ heigen hprob horth
  obtain ⟨x, hx, hnorm⟩ := exists_ball_affine_eigenmap_norm_sq_ge hv
    (WithLp.toLp 2 b) hρ.le hR j
  rw [affine_eigenfunction_eigenmap_representation a b hρ x] at hnorm
  have h := affine_langevin_wasserstein_lower hB hV κ hκ hHess a b ρ hρ heigen hprob horth x t
  have hmono : ENNReal.ofReal (Real.exp (-2 * ρ * (t : ℝ)) * (ρ * R ^ 2) +
      k * (1 - Real.sqrt (1 - Real.exp (-2 * ρ * (t : ℝ)))) ^ 2) ≤
      ENNReal.ofReal (Real.exp (-2 * ρ * (t : ℝ)) *
        ‖WithLp.toLp 2 (fun i => inner ℝ (a i) x + b i)‖ ^ 2 +
        k * (1 - Real.sqrt (1 - Real.exp (-2 * ρ * (t : ℝ)))) ^ 2) := by
    apply ENNReal.ofReal_le_ofReal
    gcongr
  exact hmono.trans (h.trans (mul_le_mul_right (le_iSup
    (fun y : Metric.closedBall (0 : E) R => squaredWasserstein
      (langevinKernel V B P t (y : E)) (gibbsMeasure volume V)) ⟨x, hx⟩) _))

end UniformLower

/-- The actual transition kernel upper bound follows from the proved
synchronous-coupling contraction and explicitly stated Gibbs invariance. -/
theorem langevin_wasserstein_upper
    {B : ℝ≥0 → Ω → E} {P : Measure Ω} (hB : IsEuclideanBrownian B P)
    {V : EuclideanSpace ℝ (Fin d) → ℝ} (hV : ContDiff ℝ 2 V) (κ : ℝ) (hκ : 0 < κ)
    (hHess : ∀ x z, κ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (hprob : IsProbabilityMeasure (gibbsMeasure volume V))
    (t : ℝ≥0) (hinvariant : (langevinKernel V B P t) ∘ₘ (gibbsMeasure volume V) = gibbsMeasure volume V)
    (x₀ : E) :
    squaredWasserstein (langevinKernel V B P t x₀) (gibbsMeasure volume V) ≤
      ENNReal.ofReal (Real.exp (-2 * κ * (t : ℝ))) *
        ENNReal.ofReal (∫ x, ‖x - x₀‖ ^ 2 ∂gibbsMeasure volume V) := by
  let := hprob
  have h := squaredWasserstein_langevinKernel_comp_le hB hV κ hκ.le hHess t
    (Measure.dirac x₀) (gibbsMeasure volume V)
  have hd : (langevinKernel V B P t) ∘ₘ (Measure.dirac x₀) = langevinKernel V B P t x₀ :=
    Measure.dirac_bind (langevinKernel V B P t).measurable x₀
  rw [hd, hinvariant, squaredWasserstein_dirac_eq_ofReal _
    (gibbs_memLp_two_id_of_hessian_bound hV κ hκ hHess)] at h
  exact h

/-- Uniform upper bound over any starting set, with genuine extended suprema. -/
theorem langevin_wasserstein_upper_iSup
    {B : ℝ≥0 → Ω → E} {P : Measure Ω} (hB : IsEuclideanBrownian B P)
    {V : EuclideanSpace ℝ (Fin d) → ℝ} (hV : ContDiff ℝ 2 V) (κ : ℝ) (hκ : 0 < κ)
    (hHess : ∀ x z, κ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (hprob : IsProbabilityMeasure (gibbsMeasure volume V))
    (t : ℝ≥0) (hinvariant : (langevinKernel V B P t) ∘ₘ (gibbsMeasure volume V) = gibbsMeasure volume V)
    (S : Set E) :
    (⨆ x₀ : S, squaredWasserstein (langevinKernel V B P t (x₀ : E)) (gibbsMeasure volume V)) ≤
      ENNReal.ofReal (Real.exp (-2 * κ * (t : ℝ))) *
        ⨆ x₀ : S, ENNReal.ofReal (∫ x, ‖x - (x₀ : E)‖ ^ 2 ∂gibbsMeasure volume V) := by
  apply iSup_le
  intro x₀
  exact (langevin_wasserstein_upper hB hV κ hκ hHess hprob t hinvariant x₀).trans
    (mul_le_mul_right (le_iSup (fun y : S => ENNReal.ofReal
      (∫ x, ‖x - (y : E)‖ ^ 2 ∂gibbsMeasure volume V)) x₀) _)

/-- The centered Gibbs ball upper bound uses its proved finite second moment. -/
theorem langevin_wasserstein_upper_ball
    {B : ℝ≥0 → Ω → E} {P : Measure Ω} (hB : IsEuclideanBrownian B P)
    {V : E → ℝ} (hV : ContDiff ℝ 2 V) (κ : ℝ) (hκ : 0 < κ)
    (hHess : ∀ x z, κ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (hprob : IsProbabilityMeasure (gibbsMeasure volume V))
    (hcenter : ∫ x, x ∂gibbsMeasure volume V = 0)
    (t : ℝ≥0) (hinvariant : (langevinKernel V B P t) ∘ₘ (gibbsMeasure volume V) = gibbsMeasure volume V)
    (R : ℝ) :
    (⨆ x₀ : Metric.closedBall (0 : E) R,
      squaredWasserstein (langevinKernel V B P t (x₀ : E)) (gibbsMeasure volume V)) ≤
      ENNReal.ofReal (Real.exp (-2 * κ * (t : ℝ))) *
        ENNReal.ofReal (R ^ 2 + ∫ x, ‖x‖ ^ 2 ∂gibbsMeasure volume V) := by
  let := hprob
  have hLp := gibbs_memLp_two_id_of_hessian_bound hV κ hκ hHess
  apply iSup_le
  intro x₀
  have h := langevin_wasserstein_upper hB hV κ hκ hHess hprob t hinvariant x₀
  rw [centered_second_moment _ hLp hcenter] at h
  apply h.trans
  apply mul_le_mul_right
  apply ENNReal.ofReal_le_ofReal
  have hn : ‖(x₀ : E)‖ ≤ R := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using x₀.property
  gcongr

end CutoffRigidity
