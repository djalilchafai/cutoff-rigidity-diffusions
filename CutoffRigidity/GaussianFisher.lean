module

public import CutoffRigidity.GaussianEntropy
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.Calculus.Gradient.Basic

/-!
# Gaussian Fisher integrals

The integrals below use the derivative of the logarithm of the canonical
positive Gaussian density ratio. They do not define general Sobolev Fisher
information for arbitrary measures. The Radon--Nikodym interpretation of
these densities is proved in `GaussianEntropy`.
-/

public section

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace CutoffRigidity

/-- Pointwise quadratic formula for the logarithm of the canonical density
ratio. Both Gaussian variances are nondegenerate. -/
theorem gaussian_log_pdf_ratio (m : ℝ) (v : ℝ≥0) (hv : v ≠ 0) (x : ℝ) :
    Real.log (gaussianPDFReal m v x / gaussianPDFReal 0 1 x) =
      -(Real.log v) / 2 - (x - m) ^ 2 / (2 * v) + x ^ 2 / 2 := by
  rw [Real.log_div (gaussianPDFReal_pos m v x hv).ne'
    (gaussianPDFReal_pos 0 1 x (by norm_num)).ne',
    log_gaussianPDFReal m v hv, log_gaussianPDFReal 0 1 (by norm_num)]
  simp
  ring

/-- The score relative to the standard Gaussian, computed from the genuine
smooth density ratio rather than from an almost-everywhere representative. -/
theorem gaussian_deriv_log_pdf_ratio (m : ℝ) (v : ℝ≥0) (hv : v ≠ 0) (x : ℝ) :
    deriv (fun y => Real.log (gaussianPDFReal m v y / gaussianPDFReal 0 1 y)) x =
      x - (x - m) / v := by
  have hfun : (fun y => Real.log (gaussianPDFReal m v y / gaussianPDFReal 0 1 y)) =
      fun y => -(Real.log v) / 2 - (y - m) ^ 2 / (2 * v) + y ^ 2 / 2 :=
    funext (gaussian_log_pdf_ratio m v hv)
  rw [hfun]
  have h := ((hasDerivAt_const x (-(Real.log (v : ℝ)) / 2)).sub
    ((((hasDerivAt_id x).sub_const m).pow 2).div_const (2 * v))).add
      (((hasDerivAt_id x).pow 2).div_const 2)
  have hvreal : (v : ℝ) ≠ 0 := NNReal.coe_ne_zero.mpr hv
  simp only [Pi.add_def, Pi.sub_def, Pi.pow_apply, id_eq] at h
  rw [h.deriv]
  field_simp
  ring

/-- The scalar Gaussian relative Fisher integral equals its squared mean
plus its covariance mismatch contribution. -/
theorem gaussian_fisher_integral_standard (m : ℝ) (v : ℝ≥0) (hv : v ≠ 0) :
    ∫ x, (deriv (fun y => Real.log
        (gaussianPDFReal m v y / gaussianPDFReal 0 1 y)) x) ^ 2 ∂gaussianReal m v =
      m ^ 2 + ((v : ℝ) - 1) ^ 2 / v := by
  have hX : MemLp (fun x : ℝ => x) 2 (gaussianReal m v) := IsGaussian.memLp_two_id
  have hi : Integrable (fun x : ℝ => x - m) (gaussianReal m v) :=
    (hX.sub (memLp_const m)).integrable (by norm_num)
  have hs : Integrable (fun x : ℝ => (x - m) ^ 2) (gaussianReal m v) :=
    (hX.sub (memLp_const m)).integrable_sq
  have hmean : ∫ x : ℝ, (x - m) ∂gaussianReal m v = 0 := by
    rw [integral_sub (hX.integrable (by norm_num)) (integrable_const _)]
    simp
  have hvar : ∫ x : ℝ, (x - m) ^ 2 ∂gaussianReal m v = v := by
    have h := variance_eq_integral (X := fun x : ℝ => x) (μ := gaussianReal m v)
      (by fun_prop)
    simpa using h.symm
  let a : ℝ := ((v : ℝ) - 1) / v
  have hvreal : (v : ℝ) ≠ 0 := NNReal.coe_ne_zero.mpr hv
  have hexp (x : ℝ) : (x - (x - m) / v) ^ 2 =
      m ^ 2 + 2 * m * a * (x - m) + a ^ 2 * (x - m) ^ 2 := by
    dsimp [a]
    field_simp
    ring
  simp_rw [gaussian_deriv_log_pdf_ratio m v hv, hexp]
  have h1 := integral_add ((integrable_const (m ^ 2)).add (hi.const_mul (2 * m * a)))
    (hs.const_mul (a ^ 2))
  simp only [Pi.add_apply] at h1
  rw [h1]
  have h2 := integral_add (integrable_const (m ^ 2)) (hi.const_mul (2 * m * a))
  rw [h2, integral_const_mul, integral_const_mul, hmean, hvar, integral_const]
  simp only [probReal_univ, smul_eq_mul, one_mul, mul_zero, add_zero]
  dsimp [a]
  field_simp

/-- Pointwise differentiability of the canonical scalar log density ratio. -/
theorem gaussian_hasDerivAt_log_pdf_ratio (m : ℝ) (v : ℝ≥0) (hv : v ≠ 0) (x : ℝ) :
    HasDerivAt (fun y => Real.log (gaussianPDFReal m v y / gaussianPDFReal 0 1 y))
      (x - (x - m) / v) x := by
  have hfun : (fun y => Real.log (gaussianPDFReal m v y / gaussianPDFReal 0 1 y)) =
      fun y => -(Real.log v) / 2 - (y - m) ^ 2 / (2 * v) + y ^ 2 / 2 :=
    funext (gaussian_log_pdf_ratio m v hv)
  have hd : DifferentiableAt ℝ
      (fun y => Real.log (gaussianPDFReal m v y / gaussianPDFReal 0 1 y)) x := by
    rw [hfun]
    fun_prop
  simpa only [gaussian_deriv_log_pdf_ratio m v hv x] using hd.hasDerivAt

/-- Logarithm of the ratio of the products of canonical scalar Gaussian
densities, viewed as a smooth function on Euclidean space. -/
@[expose] noncomputable def diagonalGaussianLogDensityRatio {ι : Type*} [Fintype ι]
    (m : EuclideanSpace ℝ ι) (v : ι → ℝ≥0) (x : EuclideanSpace ℝ ι) : ℝ :=
  Real.log ((∏ i, gaussianPDFReal (m i) (v i) (x i)) /
    (∏ i, gaussianPDFReal 0 1 (x i)))

theorem diagonalGaussianLogDensityRatio_eq_sum {ι : Type*} [Fintype ι]
    (m : EuclideanSpace ℝ ι) (v : ι → ℝ≥0) (hv : ∀ i, v i ≠ 0)
    (x : EuclideanSpace ℝ ι) :
    diagonalGaussianLogDensityRatio m v x =
      ∑ i, Real.log (gaussianPDFReal (m i) (v i) (x i) / gaussianPDFReal 0 1 (x i)) := by
  have hp (i : ι) : gaussianPDFReal (m i) (v i) (x i) ≠ 0 :=
    (gaussianPDFReal_pos _ _ _ (hv i)).ne'
  have hq (i : ι) : gaussianPDFReal 0 1 (x i) ≠ 0 :=
    (gaussianPDFReal_pos _ _ _ (by norm_num)).ne'
  unfold diagonalGaussianLogDensityRatio
  rw [Real.log_div (Finset.prod_ne_zero_iff.mpr (fun i _ => hp i))
    (Finset.prod_ne_zero_iff.mpr (fun i _ => hq i)),
    Real.log_prod (fun i _ => hp i), Real.log_prod (fun i _ => hq i),
    ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  exact (Real.log_div (hp i) (hq i)).symm

/-- The actual Euclidean gradient of the canonical product-density ratio is
the vector of coordinate scores. -/
theorem gradient_diagonalGaussianLogDensityRatio {ι : Type*} [Fintype ι]
    (m : EuclideanSpace ℝ ι) (v : ι → ℝ≥0) (hv : ∀ i, v i ≠ 0)
    (x : EuclideanSpace ℝ ι) :
    gradient (diagonalGaussianLogDensityRatio m v) x =
      WithLp.toLp 2 (fun i => x i - (x i - m i) / v i) := by
  have hd (i : ι) : HasFDerivAt
      (fun y : EuclideanSpace ℝ ι => Real.log
        (gaussianPDFReal (m i) (v i) (y i) / gaussianPDFReal 0 1 (y i)))
      ((x i - (x i - m i) / v i) • EuclideanSpace.proj (𝕜 := ℝ) i) x := by
    exact (gaussian_hasDerivAt_log_pdf_ratio (m i) (v i) (hv i) (x i)).comp_hasFDerivAt x
      (EuclideanSpace.proj (𝕜 := ℝ) i).hasFDerivAt
  have hsum := HasFDerivAt.fun_sum (fun i (_ : i ∈ (Finset.univ : Finset ι)) => hd i)
  have hlin : (∑ i, (x i - (x i - m i) / v i) • EuclideanSpace.proj (𝕜 := ℝ) i) =
      InnerProductSpace.toDual ℝ (EuclideanSpace ℝ ι)
        (WithLp.toLp 2 (fun i => x i - (x i - m i) / v i)) := by
    ext y
    simp [InnerProductSpace.toDual_apply_apply, PiLp.inner_apply, mul_comm]
  rw [hlin] at hsum
  have hfun := funext (diagonalGaussianLogDensityRatio_eq_sum m v hv)
  rw [← hfun] at hsum
  exact (hasGradientAt_iff_hasFDerivAt.mpr hsum).gradient

/-- Integral of the squared genuine Euclidean gradient for a positive
diagonal Gaussian. This remains a canonical-density integral rather than a
definition of general Sobolev Fisher information. -/
theorem diagonalGaussian_fisher_integral_standard {ι : Type*} [Fintype ι] [DecidableEq ι]
    (m : EuclideanSpace ℝ ι) (v : ι → ℝ≥0) (hv : ∀ i, v i ≠ 0) :
    ∫ x, ‖gradient (diagonalGaussianLogDensityRatio m v) x‖ ^ 2
      ∂multivariateGaussian m (Matrix.diagonal (fun i => (v i : ℝ))) =
      ‖m‖ ^ 2 + ∑ i, ((v i : ℝ) - 1) ^ 2 / v i := by
  let μ := multivariateGaussian m (Matrix.diagonal (fun i => (v i : ℝ)))
  have hS : (Matrix.diagonal (fun i => (v i : ℝ))).PosSemidef :=
    Matrix.PosSemidef.diagonal (fun i => (v i).coe_nonneg)
  have hcoord (i : ι) :
      ∫ x : EuclideanSpace ℝ ι, (x i - (x i - m i) / v i) ^ 2 ∂μ =
        (m i) ^ 2 + ((v i : ℝ) - 1) ^ 2 / v i := by
    have hmap : μ.map (fun x : EuclideanSpace ℝ ι => x i) = gaussianReal (m i) (v i) := by
      simpa [μ] using (measurePreserving_eval_multivariateGaussian (μ := m) hS (i := i)).map_eq
    calc
      _ = ∫ y : ℝ, (y - (y - m i) / v i) ^ 2 ∂gaussianReal (m i) (v i) := by
        rw [← hmap, integral_map (by fun_prop) (by fun_prop)]
      _ = _ := by
        simpa only [gaussian_deriv_log_pdf_ratio _ _ (hv i)] using
          gaussian_fisher_integral_standard (m i) (v i) (hv i)
  have hint (i : ι) : Integrable
      (fun x : EuclideanSpace ℝ ι => (x i - (x i - m i) / v i) ^ 2) μ := by
    have hX : MemLp (fun x : EuclideanSpace ℝ ι => x i) 2 μ := by
      simpa using IsGaussian.memLp_dual μ (EuclideanSpace.proj i) 2 (by norm_num)
    simpa only [div_eq_inv_mul, Pi.sub_apply] using
      (hX.sub ((hX.sub (memLp_const (m i))).const_mul ((v i : ℝ)⁻¹))).integrable_sq
  simp_rw [gradient_diagonalGaussianLogDensityRatio m v hv, EuclideanSpace.real_norm_sq_eq]
  rw [integral_finsetSum _ (fun i _ => hint i)]
  simp_rw [hcoord]
  rw [Finset.sum_add_distrib, ← EuclideanSpace.real_norm_sq_eq]

/-- Isotropic specialization of the actual squared-gradient integral. -/
theorem isotropicGaussian_fisher_integral_standard {ι : Type*} [Fintype ι] [DecidableEq ι]
    (m : EuclideanSpace ℝ ι) (v : ℝ≥0) (hv : v ≠ 0) :
    ∫ x, ‖gradient (diagonalGaussianLogDensityRatio m (fun _ => v)) x‖ ^ 2
      ∂multivariateGaussian m ((v : ℝ) • (1 : Matrix ι ι ℝ)) =
      ‖m‖ ^ 2 + Fintype.card ι * ((v : ℝ) - 1) ^ 2 / v := by
  have hmat : Matrix.diagonal (fun _ : ι => (v : ℝ)) =
      (v : ℝ) • (1 : Matrix ι ι ℝ) := by
    ext i j
    by_cases hij : i = j <;> simp [hij]
  rw [← hmat]
  simpa [mul_div_assoc] using
    diagonalGaussian_fisher_integral_standard m (fun _ => v) (fun _ => hv)

/-- Fisher gradient integral for the unit-equilibrium Mehler Gaussian. The
initial mean is decayed by `sqrt q` and the covariance is `(1-q)I`. -/
theorem gaussian_decay_fisher_integral {ι : Type*} [Fintype ι] [DecidableEq ι]
    (z : EuclideanSpace ℝ ι) (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1) :
    let v : ℝ≥0 := ⟨1 - q, (sub_pos.mpr hq1).le⟩
    ∫ x, ‖gradient (diagonalGaussianLogDensityRatio (Real.sqrt q • z) (fun _ => v)) x‖ ^ 2
      ∂multivariateGaussian (Real.sqrt q • z) ((1 - q) • (1 : Matrix ι ι ℝ)) =
      q * ‖z‖ ^ 2 + Fintype.card ι * q ^ 2 / (1 - q) := by
  intro v
  have hv : v ≠ 0 := NNReal.coe_ne_zero.mp (sub_pos.mpr hq1).ne'
  have h := isotropicGaussian_fisher_integral_standard (Real.sqrt q • z) v hv
  change (∫ x, ‖gradient (diagonalGaussianLogDensityRatio (Real.sqrt q • z) (fun _ => v)) x‖ ^ 2
      ∂multivariateGaussian (Real.sqrt q • z) ((1 - q) • (1 : Matrix ι ι ℝ))) =
    ‖Real.sqrt q • z‖ ^ 2 + Fintype.card ι * ((1 - q) - 1) ^ 2 / (1 - q) at h
  rw [h, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, Real.sq_sqrt hq0]
  congr 1
  ring

end CutoffRigidity
