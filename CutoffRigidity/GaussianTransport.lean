module

public import CutoffRigidity.Transport
public import CutoffRigidity.GaussianMoments
public import CutoffRigidity.TransportMoments

/-!
# Shared-noise transport for isotropic Gaussian measures

The shared-noise coupling and the matching mean/variance lower bound prove
the isotropic Gaussian transport formula used in Theorem 1.1. The measures
are actual multivariate Gaussian laws, and the distance is an infimum over
actual coupling measures. The final theorem specializes to the Mehler
Gaussian marginal, without assuming its identification with a diffusion.
-/

public section

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace ENNReal
open scoped MatrixOrder

namespace CutoffRigidity

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The isotropic Gaussian law of `m + s Z`, with `Z` standard Gaussian. -/
@[expose] noncomputable def affineGaussian (m : EuclideanSpace ℝ ι) (s : ℝ) :
    Measure (EuclideanSpace ℝ ι) :=
  (stdGaussian (EuclideanSpace ℝ ι)).map (fun x => m + s • x)

instance (m : EuclideanSpace ℝ ι) (s : ℝ) : IsProbabilityMeasure (affineGaussian m s) := by
  unfold affineGaussian
  exact (Measure.isProbabilityMeasure_map_iff (by fun_prop)).2 inferInstance

instance (m : EuclideanSpace ℝ ι) (s : ℝ) : IsGaussian (affineGaussian m s) := by
  have heq : affineGaussian m s =
      ((stdGaussian (EuclideanSpace ℝ ι)).map
        (s • ContinuousLinearMap.id ℝ (EuclideanSpace ℝ ι))).map (fun x => m + x) := by
    rw [Measure.map_map (by fun_prop) (by fun_prop)]
    rfl
  rw [heq]
  infer_instance

omit [DecidableEq ι] in
@[simp] theorem affineGaussian_zero_one :
    affineGaussian (0 : EuclideanSpace ℝ ι) 1 = stdGaussian (EuclideanSpace ℝ ι) := by
  simp [affineGaussian]

/-- For nonnegative scale, the affine-image law is the usual multivariate
Gaussian with covariance `s² I`, including the degenerate scale zero. -/
theorem affineGaussian_eq_multivariateGaussian (m : EuclideanSpace ℝ ι)
    (s : ℝ) (hs : 0 ≤ s) :
    affineGaussian m s = multivariateGaussian m (s ^ 2 • (1 : Matrix ι ι ℝ)) := by
  have hsqrt : CFC.sqrt (s ^ 2 • (1 : Matrix ι ι ℝ)) = s • (1 : Matrix ι ι ℝ) := by
    rw [← show (s • (1 : Matrix ι ι ℝ)) ^ 2 = s ^ 2 • (1 : Matrix ι ι ℝ) by
      simp [pow_two, smul_smul]]
    exact CFC.sqrt_sq _ (Matrix.PosSemidef.one.smul hs).nonneg
  unfold affineGaussian multivariateGaussian
  rw [hsqrt]
  congr 1
  ext x
  simp

/-- Mean of the affine-image Gaussian. -/
theorem integral_id_affineGaussian (m : EuclideanSpace ℝ ι) (s : ℝ) (hs : 0 ≤ s) :
    ∫ x, x ∂affineGaussian m s = m := by
  rw [affineGaussian_eq_multivariateGaussian m s hs]
  exact integral_id_multivariateGaussian

/-- Coordinate means of the affine-image Gaussian. -/
theorem integral_eval_affineGaussian (m : EuclideanSpace ℝ ι)
    (s : ℝ) (hs : 0 ≤ s) (i : ι) :
    ∫ x, x i ∂affineGaussian m s = m i := by
  have h := (EuclideanSpace.proj (𝕜 := ℝ) i).integral_comp_comm
    (IsGaussian.integrable_id (μ := affineGaussian m s))
  simpa only [id_eq, EuclideanSpace.coe_proj, integral_id_affineGaussian m s hs] using h

/-- Each coordinate of the isotropic Gaussian has variance `s²`. -/
theorem variance_eval_affineGaussian (m : EuclideanSpace ℝ ι)
    (s : ℝ) (hs : 0 ≤ s) (i : ι) :
    Var[fun x => x i; affineGaussian m s] = s ^ 2 := by
  rw [affineGaussian_eq_multivariateGaussian m s hs]
  simpa using variance_eval_multivariateGaussian
    (μ := m) (Matrix.PosSemidef.one.smul (sq_nonneg s)) i

/-- Gaussian second moment under a scalar affine transformation. -/
theorem gaussian_affine_second_moment (m : EuclideanSpace ℝ ι) (s : ℝ) :
    ∫ x, ‖m + s • x‖ ^ 2 ∂stdGaussian (EuclideanSpace ℝ ι) =
      ‖m‖ ^ 2 + s ^ 2 * Fintype.card ι := by
  have hi : Integrable (fun x : EuclideanSpace ℝ ι => x)
      (stdGaussian (EuclideanSpace ℝ ι)) := IsGaussian.integrable_id
  have hs : Integrable (fun x : EuclideanSpace ℝ ι => ‖x‖ ^ 2)
      (stdGaussian (EuclideanSpace ℝ ι)) :=
    IsGaussian.memLp_two_id.norm.integrable_sq
  have hc : Integrable (fun x : EuclideanSpace ℝ ι => 2 * s * inner ℝ m x)
      (stdGaussian (EuclideanSpace ℝ ι)) :=
    (hi.const_inner m).const_mul (2 * s)
  have hexp (x : EuclideanSpace ℝ ι) :
      ‖m + s • x‖ ^ 2 = ‖m‖ ^ 2 + 2 * s * inner ℝ m x + s ^ 2 * ‖x‖ ^ 2 := by
    rw [norm_add_sq_real, real_inner_smul_right, norm_smul, mul_pow, Real.norm_eq_abs,
      sq_abs]
    ring
  simp_rw [hexp]
  have ha := integral_add ((integrable_const (‖m‖ ^ 2)).add hc) (hs.const_mul (s ^ 2))
  simp only [Pi.add_apply] at ha
  rw [ha]
  have hb := integral_add (integrable_const (‖m‖ ^ 2)) hc
  rw [hb, integral_const_mul,
    integral_inner hi, integral_id_stdGaussian, inner_zero_right, mul_zero,
    integral_const_mul, standard_gaussian_second_moment]
  simp

/-- A coupling using the same standard Gaussian sample for the two coordinates. -/
noncomputable def affineGaussianCoupling (m : EuclideanSpace ℝ ι) (s : ℝ) :
    Coupling (affineGaussian m s) (stdGaussian (EuclideanSpace ℝ ι)) :=
  ⟨(stdGaussian (EuclideanSpace ℝ ι)).map (fun x => (m + s • x, x)), by
    constructor
    · rw [Measure.map_map (by fun_prop) (by fun_prop)]
      rfl
    · rw [Measure.map_map (by fun_prop) (by fun_prop)]
      change (stdGaussian (EuclideanSpace ℝ ι)).map id = _
      simp⟩

/-- The real-valued quadratic cost of the shared-noise Gaussian coupling. -/
theorem affineGaussianCoupling_integral_cost (m : EuclideanSpace ℝ ι) (s : ℝ) :
    ∫ z, ‖z.1 - z.2‖ ^ 2 ∂(affineGaussianCoupling m s).val =
      ‖m‖ ^ 2 + (s - 1) ^ 2 * Fintype.card ι := by
  rw [affineGaussianCoupling, integral_map (by fun_prop) (by fun_prop)]
  have heq (x : EuclideanSpace ℝ ι) : m + s • x - x = m + (s - 1) • x := by
    rw [sub_smul, one_smul, add_sub_assoc]
  simp_rw [heq]
  exact gaussian_affine_second_moment m (s - 1)

/-- The extended quadratic cost of the shared-noise coupling is finite and exact. -/
theorem affineGaussianCoupling_cost (m : EuclideanSpace ℝ ι) (s : ℝ) :
    (∫⁻ z, edist z.1 z.2 ^ 2 ∂(affineGaussianCoupling m s).val) =
      ENNReal.ofReal (‖m‖ ^ 2 + (s - 1) ^ 2 * Fintype.card ι) := by
  rw [affineGaussianCoupling, lintegral_map (by fun_prop) (by fun_prop)]
  have heq (x : EuclideanSpace ℝ ι) : m + s • x - x = m + (s - 1) • x := by
    rw [sub_smul, one_smul, add_sub_assoc]
  simp only [edist_eq_enorm_sub, heq]
  have hi : Integrable (fun x : EuclideanSpace ℝ ι => ‖m + (s - 1) • x‖ ^ 2)
      (stdGaussian (EuclideanSpace ℝ ι)) := by
    have h : MemLp (fun x : EuclideanSpace ℝ ι => m + (s - 1) • x) 2
        (stdGaussian (EuclideanSpace ℝ ι)) :=
      (memLp_const m).add (IsGaussian.memLp_two_id.const_smul (s - 1))
    exact h.norm.integrable_sq
  have ho := ofReal_integral_eq_lintegral_ofReal hi
    (Filter.Eventually.of_forall (fun x => sq_nonneg ‖m + (s - 1) • x‖))
  rw [gaussian_affine_second_moment] at ho
  rw [ho]
  congr 1
  ext x
  rw [ENNReal.ofReal_pow (norm_nonneg _) 2, ofReal_norm]

/-- An actual Gaussian coupling yields the expected upper bound on squared W₂. -/
theorem squaredWasserstein_affineGaussian_le (m : EuclideanSpace ℝ ι) (s : ℝ) :
    squaredWasserstein (affineGaussian m s) (stdGaussian (EuclideanSpace ℝ ι)) ≤
      ENNReal.ofReal (‖m‖ ^ 2 + (s - 1) ^ 2 * Fintype.card ι) := by
  calc
    _ ≤ _ := squaredWasserstein_le_cost (affineGaussianCoupling m s)
    _ = _ := affineGaussianCoupling_cost m s

/-- Exact squared quadratic transport distance from an isotropic Gaussian to
the standard Gaussian, proved with a shared-noise coupling and the matching
mean/variance lower bound over all couplings. -/
theorem squaredWasserstein_affineGaussian (m : EuclideanSpace ℝ ι)
    (s : ℝ) (hs : 0 ≤ s) :
    squaredWasserstein (affineGaussian m s) (stdGaussian (EuclideanSpace ℝ ι)) =
      ENNReal.ofReal (‖m‖ ^ 2 + (s - 1) ^ 2 * Fintype.card ι) := by
  apply le_antisymm (squaredWasserstein_affineGaussian_le m s)
  have hμ (i : ι) : MemLp (fun x : EuclideanSpace ℝ ι => x i) 2 (affineGaussian m s) := by
    simpa using IsGaussian.memLp_dual (affineGaussian m s) (EuclideanSpace.proj i)
      2 (by norm_num)
  have hν (i : ι) : MemLp (fun x : EuclideanSpace ℝ ι => x i) 2
      (stdGaussian (EuclideanSpace ℝ ι)) := by
    simpa using IsGaussian.memLp_dual (stdGaussian (EuclideanSpace ℝ ι))
      (EuclideanSpace.proj i) 2 (by norm_num)
  have hmeanν (i : ι) :
      ∫ x : EuclideanSpace ℝ ι, x i ∂stdGaussian (EuclideanSpace ℝ ι) = 0 := by
    simpa using integral_eval_affineGaussian (0 : EuclideanSpace ℝ ι) 1 (by norm_num) i
  have hvarν (i : ι) :
      Var[fun x : EuclideanSpace ℝ ι => x i; stdGaussian (EuclideanSpace ℝ ι)] = (1 : ℝ) ^ 2 := by
    simpa using variance_eval_affineGaussian (0 : EuclideanSpace ℝ ι) 1 (by norm_num) i
  have hl := squaredWasserstein_ge_coordinate_moments
    (affineGaussian m s) (stdGaussian (EuclideanSpace ℝ ι)) hμ hν
    (fun i => m i) (fun _ => 0) (fun _ => s) (fun _ => 1)
    (fun _ => hs) (fun _ => by norm_num)
    (integral_eval_affineGaussian m s hs) hmeanν
    (variance_eval_affineGaussian m s hs) hvarν
  simpa [Finset.sum_add_distrib, ← EuclideanSpace.real_norm_sq_eq, mul_comm] using hl

/-- The isotropic case of the multivariate Gaussian W₂ formula cited in the
paper, stated directly for Mathlib's multivariate Gaussian measure. -/
theorem squaredWasserstein_isotropicGaussian (m : EuclideanSpace ℝ ι)
    (s : ℝ) (hs : 0 ≤ s) :
    squaredWasserstein (multivariateGaussian m (s ^ 2 • (1 : Matrix ι ι ℝ)))
        (stdGaussian (EuclideanSpace ℝ ι)) =
      ENNReal.ofReal (‖m‖ ^ 2 + (s - 1) ^ 2 * Fintype.card ι) := by
  rw [← affineGaussian_eq_multivariateGaussian m s hs]
  exact squaredWasserstein_affineGaussian m s hs

/-- The mean and covariance profile used for the projected OU law in the
proof of Theorem 1.1, with `q` its squared mean-decay factor. -/
theorem squaredWasserstein_gaussian_decay (z : EuclideanSpace ℝ ι)
    (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    squaredWasserstein
        (multivariateGaussian (Real.sqrt q • z) ((1 - q) • (1 : Matrix ι ι ℝ)))
        (stdGaussian (EuclideanSpace ℝ ι)) =
      ENNReal.ofReal (q * ‖z‖ ^ 2 + Fintype.card ι * (1 - Real.sqrt (1 - q)) ^ 2) := by
  have hq : 0 ≤ 1 - q := sub_nonneg.mpr hq1
  have hcov : (1 - q) • (1 : Matrix ι ι ℝ) =
      (Real.sqrt (1 - q)) ^ 2 • (1 : Matrix ι ι ℝ) := by rw [Real.sq_sqrt hq]
  rw [hcov, squaredWasserstein_isotropicGaussian _ _ (Real.sqrt_nonneg _)]
  congr 1
  rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, Real.sq_sqrt hq0]
  ring

/-- Exact distance for the Gaussian measure prescribed by the Mehler formula
in the paper. Identification of this measure with a projected diffusion is
a separate stochastic-process obligation. -/
theorem squaredWasserstein_ou_marginal (z : EuclideanSpace ℝ ι)
    (ρ t : ℝ) (hρ : 0 ≤ ρ) (ht : 0 ≤ t) :
    squaredWasserstein
        (multivariateGaussian (Real.exp (-ρ * t) • z)
          ((1 - Real.exp (-2 * ρ * t)) • (1 : Matrix ι ι ℝ)))
        (stdGaussian (EuclideanSpace ℝ ι)) =
      ENNReal.ofReal (Real.exp (-2 * ρ * t) * ‖z‖ ^ 2 +
        Fintype.card ι * (1 - Real.sqrt (1 - Real.exp (-2 * ρ * t))) ^ 2) := by
  have hq0 : 0 ≤ Real.exp (-2 * ρ * t) := (Real.exp_pos _).le
  have hq1 : Real.exp (-2 * ρ * t) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    nlinarith [mul_nonneg hρ ht]
  have hsqrt : Real.sqrt (Real.exp (-2 * ρ * t)) = Real.exp (-ρ * t) := by
    have heq : Real.exp (-2 * ρ * t) = Real.exp (-ρ * t) ^ 2 := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    rw [heq, Real.sqrt_sq (Real.exp_pos _).le]
  simpa only [hsqrt] using squaredWasserstein_gaussian_decay z _ hq0 hq1

end CutoffRigidity
