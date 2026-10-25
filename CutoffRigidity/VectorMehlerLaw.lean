module

public import CutoffRigidity.BrownianProjection
public import CutoffRigidity.ProjectedLangevin
public import CutoffRigidity.LinearLangevinLaw
public import CutoffRigidity.BrownianCovarianceIntegrals

/-! # Actual Euclidean quadratic Langevin marginals

The scalar Brownian response law and evaluated covariance quadrature identify
actual quadratic Langevin solutions. Linear projections are handled using
actual Brownian Gaussian processes and Bochner-integral commutation.
-/

public section

namespace CutoffRigidity

open Set MeasureTheory ProbabilityTheory
open scoped NNReal

variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

/-- A unit Euclidean projection is a genuine scalar Brownian motion. -/
theorem IsEuclideanBrownian.inner_unit
    {B : ℝ≥0 → Ω → E} {P : Measure Ω} (hB : IsEuclideanBrownian B P)
    (u : E) (hu : ‖u‖ = 1) : IsBrownianReal (fun t ω => inner ℝ u (B t ω)) P := by
  have hG := hB.isGaussianProcess.comp_left (fun _ => innerSL ℝ u)
  refine ⟨hG.isPreBrownianReal_of_covariance (hB.integral_inner u) ?_, ?_⟩
  · intro s t hst
    change cov[fun ω => inner ℝ u (B s ω), fun ω => inner ℝ u (B t ω); P] = (s : ℝ)
    rw [hB.covariance_inner, real_inner_self_eq_norm_sq, hu]
    simp [min_eq_left (show (s : ℝ) ≤ t from hst)]
  · filter_upwards [hB.continuous_paths] with ω hω
    exact (innerSL ℝ u).continuous.comp hω

/-- Actual canonical quadratic solutions commute with a real linear functional. -/
theorem quadratic_langevinSolution_inner
    (ρ : ℝ) (hρ : 0 ≤ ρ) {w : ℝ → E} (hw : Continuous w)
    (x₀ c : E) {T : ℝ} (hT : 0 ≤ T) :
    inner ℝ c (langevinSolution (quadraticLangevinPotential ρ) w x₀ T) =
      langevinSolution (quadraticLangevinPotential ρ) (fun s => inner ℝ c (w s))
        (inner ℝ c x₀) T := by
  have hw' : Continuous (fun s => inner ℝ c (w s)) := (innerSL ℝ c).continuous.comp hw
  rw [quadratic_langevinSolution_response ρ hρ hw x₀ hT,
    quadratic_langevinSolution_response ρ hρ hw' (inner ℝ c x₀) hT]
  simp only [inner_add_right, inner_sub_right, inner_smul_right, smul_eq_mul]
  have hi : IntervalIntegrable (fun s => Real.exp (ρ * s) • w s) volume 0 T :=
    (by fun_prop : Continuous (fun s => Real.exp (ρ * s) • w s)).intervalIntegrable 0 T
  have hI := (innerSL ℝ c).intervalIntegral_comp_comm hi
  change (∫ s in 0..T, inner ℝ c (Real.exp (ρ * s) • w s)) =
    inner ℝ c (∫ s in 0..T, Real.exp (ρ * s) • w s) at hI
  simp only [inner_smul_right] at hI
  rw [← hI]

/-- Every actual vector linear projection has the exact scalar Mehler law. -/
theorem quadratic_langevinSolution_inner_hasLaw
    {B : ℝ≥0 → Ω → E} {P : Measure Ω} (hB : IsEuclideanBrownian B P)
    (ρ σ T : ℝ) (hρ : 0 < ρ) (hT : 0 ≤ T) (x₀ c : E) :
    HasLaw (fun ω => inner ℝ c (langevinSolution (quadraticLangevinPotential ρ)
      (fun s : ℝ => σ • B s.toNNReal ω) x₀ T))
      (gaussianReal (Real.exp (-ρ * T) * inner ℝ c x₀)
        (((σ * ‖c‖) ^ 2 * (1 - Real.exp (-2 * ρ * T)) / (2 * ρ)).toNNReal)) P := by
  by_cases hc : c = 0
  · subst c
    let := hB.isProbabilityMeasure
    refine ⟨by simpa only [inner_zero_left] using (aemeasurable_const : AEMeasurable (fun _ : Ω => (0 : ℝ)) P), ?_⟩
    simp [gaussianReal_zero_var]
  · let u : E := ‖c‖⁻¹ • c
    have hn : ‖c‖ ≠ 0 := norm_ne_zero_iff.mpr hc
    have hu : ‖u‖ = 1 := by simp [u, norm_smul, hn]
    have hBu := hB.inner_unit u hu
    have hnoise (ω : Ω) :
        (fun s : ℝ => (σ * ‖c‖) * inner ℝ u (B s.toNNReal ω)) =
          fun s => inner ℝ c (σ • B s.toNNReal ω) := by
      funext s
      simp only [u, real_inner_smul_left, inner_smul_right]
      field_simp
    have hlaw := quadratic_langevinSolution_scalar_hasLaw hBu ρ (σ * ‖c‖)
      (inner ℝ c x₀) T hρ hT
    apply hlaw.congr
    filter_upwards [hB.continuous_paths] with ω hω
    have hw : Continuous (fun s : ℝ => σ • B s.toNNReal ω) :=
      (continuous_const : Continuous (fun _ : ℝ => σ)).smul (hω.comp continuous_real_toNNReal)
    rw [hnoise]
    exact quadratic_langevinSolution_inner ρ hρ.le hw x₀ c hT

/-- The actual vector quadratic Langevin marginal is the multivariate
Mehler Gaussian, with its mean and covariance derived from Brownian response. -/
theorem quadratic_langevinSolution_vector_hasLaw
    {B : ℝ≥0 → Ω → E} {P : Measure Ω} (hB : IsEuclideanBrownian B P)
    (ρ σ T : ℝ) (hρ : 0 < ρ) (hT : 0 ≤ T) (x₀ : E) :
    HasLaw (fun ω => langevinSolution (quadraticLangevinPotential ρ)
      (fun s : ℝ => σ • B s.toNNReal ω) x₀ T)
      (multivariateGaussian (Real.exp (-ρ * T) • x₀)
        ((σ ^ 2 * (1 - Real.exp (-2 * ρ * T)) / (2 * ρ)) • (1 : Matrix (Fin d) (Fin d) ℝ))) P := by
  let := hB.isProbabilityMeasure
  let X := fun ω => langevinSolution (quadraticLangevinPotential ρ)
    (fun s : ℝ => σ • B s.toNNReal ω) x₀ T
  have hmcoord (i : Fin d) : AEMeasurable (fun ω => X ω i) P := by
    have h := (quadratic_langevinSolution_inner_hasLaw hB ρ σ T hρ hT x₀
      (EuclideanSpace.single i 1)).aemeasurable
    simpa only [EuclideanSpace.inner_single_left, map_one, one_mul] using h
  have hm : AEMeasurable X P :=
    (MeasurableEquiv.toLp (p := 2) (Fin d → ℝ)).measurable.comp_aemeasurable
      (AEMeasurable.of_eval hmcoord)
  have hq : 0 ≤ (1 - Real.exp (-2 * ρ * T)) / (2 * ρ) := by
    apply div_nonneg _ (by positivity)
    exact sub_nonneg.mpr (Real.exp_le_one_iff.mpr (by nlinarith))
  have hv : 0 ≤ σ ^ 2 * (1 - Real.exp (-2 * ρ * T)) / (2 * ρ) := by
    rw [mul_div_assoc]
    exact mul_nonneg (sq_nonneg σ) hq
  refine ⟨hm, ?_⟩
  apply Measure.ext_of_charFun
  funext c
  have hlaw := quadratic_langevinSolution_inner_hasLaw hB ρ σ T hρ hT x₀ c
  have hid : (fun ω => inner ℝ (X ω) c) = fun ω => inner ℝ c (X ω) := by
    funext ω
    exact real_inner_comm _ _
  rw [charFun_map_eq_charFun_map_inner_one hm, hid, hlaw.map_eq,
    charFun_gaussianReal, charFun_multivariateGaussian (Matrix.PosSemidef.one.smul hv)]
  have hqc : 0 ≤ (σ * ‖c‖) ^ 2 * (1 - Real.exp (-2 * ρ * T)) / (2 * ρ) := by
    rw [mul_div_assoc]
    exact mul_nonneg (sq_nonneg _) hq
  simp only [Real.toNNReal_of_nonneg hqc, inner_smul_right, Matrix.smul_mulVec, Matrix.one_mulVec,
    dotProduct_smul, smul_eq_mul]
  have hdot : (c.ofLp ⬝ᵥ c.ofLp) = ‖c‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, PiLp.inner_apply]
    simp only [Real.inner_apply, dotProduct]
  rw [hdot]
  congr 1
  push_cast
  ring

/-- The source normalization has invariant standard Gaussian covariance. -/
theorem quadratic_langevinSolution_normalized_hasLaw
    {B : ℝ≥0 → Ω → E} {P : Measure Ω} (hB : IsEuclideanBrownian B P)
    (ρ T : ℝ) (hρ : 0 < ρ) (hT : 0 ≤ T) (x₀ : E) :
    HasLaw (fun ω => langevinSolution (quadraticLangevinPotential ρ)
      (fun s : ℝ => Real.sqrt ρ • brownianDrivingPath B ω s) x₀ T)
      (multivariateGaussian (Real.exp (-ρ * T) • x₀)
        ((1 - Real.exp (-2 * ρ * T)) • (1 : Matrix (Fin d) (Fin d) ℝ))) P := by
  have h := quadratic_langevinSolution_vector_hasLaw hB ρ (Real.sqrt ρ * Real.sqrt 2)
    T hρ hT x₀
  have hs : (Real.sqrt ρ * Real.sqrt 2) ^ 2 = 2 * ρ := by
    rw [mul_pow, Real.sq_sqrt hρ.le, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    ring
  have hv : (Real.sqrt ρ * Real.sqrt 2) ^ 2 * (1 - Real.exp (-2 * ρ * T)) / (2 * ρ) =
      1 - Real.exp (-2 * ρ * T) := by
    rw [hs]
    field_simp
  rw [hv] at h
  simpa only [brownianDrivingPath, smul_smul] using h

/-- Lemma 3.3's actual projected Langevin marginal, obtained from the actual
integral equation, Brownian projection, uniqueness, and the derived Mehler law. -/
theorem langevinProcess_eigenmap_hasLaw
    {k : ℕ} {B : ℝ≥0 → Ω → E} {P : Measure Ω} (hB : IsEuclideanBrownian B P)
    {V : E → ℝ} (hV : ContDiff ℝ 2 V) (κ : ℝ) (hκ : 0 ≤ κ)
    (hHess : ∀ x z, κ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (v : Fin k → E) (hv : Orthonormal ℝ v)
    (b : EuclideanSpace ℝ (Fin k)) (ρ : ℝ) (hρ : 0 < ρ)
    (heigen : ∀ x i, langevinDifferentialOperator V
      (fun y => (eigenmapCLM v ρ y + b) i) x = -ρ * (eigenmapCLM v ρ x + b) i)
    (x₀ : E) (t : ℝ≥0) :
    HasLaw (fun ω => eigenmapCLM v ρ (langevinProcess V B x₀ t ω) + b)
      (multivariateGaussian (Real.exp (-ρ * (t : ℝ)) • (eigenmapCLM v ρ x₀ + b))
        ((1 - Real.exp (-2 * ρ * (t : ℝ))) • (1 : Matrix (Fin k) (Fin k) ℝ))) P := by
  have h := quadratic_langevinSolution_normalized_hasLaw (hB.orthogonalProjection hv)
    ρ t hρ t.coe_nonneg (eigenmapCLM v ρ x₀ + b)
  apply h.congr
  filter_upwards [langevinProcess_eigenmap_projection_ae hB hV κ hκ hHess
    v b ρ hρ.le heigen x₀] with ω hω
  exact hω t

end CutoffRigidity
