module

public import CutoffRigidity.GaussianMoments
public import Mathlib.InformationTheory.KullbackLeibler.Basic
public import Mathlib.InformationTheory.KullbackLeibler.DataProcessing
public import Mathlib.InformationTheory.KullbackLeibler.ChainRule
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.Tactic

/-!
# Relative entropy of a scalar Gaussian

This file evaluates the genuine log-likelihood ratio and Kullback--Leibler
 divergence of Mathlib's Gaussian probability measures. These are Gaussian
inputs to the entropy arguments in Section 3.3 of the paper.
-/

public section

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal NNReal

namespace CutoffRigidity

/-- Relative entropy is invariant under a measurable change of coordinates. -/
theorem klDiv_map_measurableEquiv {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (e : α ≃ᵐ β) (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    klDiv (μ.map e) (ν.map e) = klDiv μ ν := by
  apply le_antisymm (klDiv_map_le μ ν e.measurable)
  have h := klDiv_map_le (μ.map e) (ν.map e) e.symm.measurable
  simpa only [e.map_symm_map] using h

/-- Additivity of relative entropy for independent probability measures. -/
theorem klDiv_prod_probability {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ ν : Measure α) (ξ ζ : Measure β)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    [IsProbabilityMeasure ξ] [IsProbabilityMeasure ζ] :
    klDiv (μ.prod ξ) (ν.prod ζ) = klDiv μ ν + klDiv ξ ζ := by
  have hswap : klDiv (μ.prod ξ) (μ.prod ζ) = klDiv (ξ.prod μ) (ζ.prod μ) := by
    have h := klDiv_map_measurableEquiv
      (MeasurableEquiv.prodComm : α × β ≃ᵐ β × α) (μ.prod ξ) (μ.prod ζ)
    change klDiv ((μ.prod ξ).map Prod.swap) ((μ.prod ζ).map Prod.swap) = _ at h
    rw [Measure.prod_swap, Measure.prod_swap] at h
    exact h.symm
  have hleft : klDiv (ξ.prod μ) (ζ.prod μ) = klDiv ξ ζ := by
    simpa only [Measure.compProd_const] using klDiv_compProd_left ξ ζ (Kernel.const β μ)
  have hchain := klDiv_compProd_eq_add μ ν (Kernel.const α ξ) (Kernel.const α ζ)
  simpa only [Measure.compProd_const, hswap, hleft] using hchain

/-- Finite independent-coordinate additivity of genuine relative entropy. -/
theorem klDiv_pi_fin_probability (n : ℕ) (μ ν : Fin n → Measure ℝ)
    [∀ i, IsProbabilityMeasure (μ i)] [∀ i, IsProbabilityMeasure (ν i)] :
    klDiv (Measure.pi μ) (Measure.pi ν) = ∑ i, klDiv (μ i) (ν i) := by
  induction n with
  | zero =>
    rw [Measure.pi_of_empty μ, Measure.pi_of_empty ν]
    simp
  | succ n ih =>
    let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0
    have hμ := (measurePreserving_piFinSuccAbove μ 0).map_eq
    have hν := (measurePreserving_piFinSuccAbove ν 0).map_eq
    have h := klDiv_map_measurableEquiv e (Measure.pi μ) (Measure.pi ν)
    change klDiv ((Measure.pi μ).map
        (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0))
      ((Measure.pi ν).map
        (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0)) = _ at h
    rw [hμ, hν] at h
    simp only [Fin.succAbove_zero] at h
    rw [← h, klDiv_prod_probability, ih]
    exact (Fin.sum_univ_succ (fun i : Fin (n + 1) => klDiv (μ i) (ν i))).symm

/-- Logarithm of the real Gaussian density, for positive variance. -/
theorem log_gaussianPDFReal (m : ℝ) (v : ℝ≥0) (hv : v ≠ 0) (x : ℝ) :
    Real.log (gaussianPDFReal m v x) =
      -(Real.log (2 * Real.pi) + Real.log v) / 2 - (x - m) ^ 2 / (2 * v) := by
  have hvpos : (0 : ℝ) < v := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hv)
  have hbase : 0 < 2 * Real.pi * (v : ℝ) := by positivity
  rw [gaussianPDFReal, Real.log_mul (inv_ne_zero (Real.sqrt_ne_zero'.mpr hbase))
    (Real.exp_ne_zero _), Real.log_inv, Real.log_sqrt hbase.le,
    Real.log_mul (by positivity : (2 * Real.pi : ℝ) ≠ 0) hvpos.ne', Real.log_exp]
  ring

/-- Radon--Nikodym identification of Gaussian log-likelihood ratio with its
strictly positive density ratio, almost everywhere under the first measure. -/
theorem gaussianReal_llr_eq_log_pdf_ratio (m : ℝ) (v : ℝ≥0) (hv : v ≠ 0) :
    llr (gaussianReal m v) (gaussianReal 0 1) =ᵐ[gaussianReal m v]
      fun x => Real.log (gaussianPDFReal m v x / gaussianPDFReal 0 1 x) := by
  have hr := Measure.rnDeriv_withDensity_right (gaussianReal m v) volume
    (measurable_gaussianPDF 0 1).aemeasurable
    (Filter.Eventually.of_forall fun x => (gaussianPDF_pos 0 (by norm_num) x).ne')
    (Filter.Eventually.of_forall fun x => (gaussianPDF_lt_top (μ := 0) (v := 1) (x := x)).ne)
  rw [← gaussianReal_of_var_ne_zero 0 (by norm_num)] at hr
  have hac := gaussianReal_absolutelyContinuous m hv
  filter_upwards [hac.ae_le hr, hac.ae_le (rnDeriv_gaussianReal m v)] with x hx hpdf
  rw [llr, hx, hpdf, ENNReal.toReal_mul, ENNReal.toReal_inv,
    toReal_gaussianPDF, toReal_gaussianPDF]
  congr 1
  ring

/-- The actual Gaussian log-likelihood ratio is an integrable quadratic. -/
theorem gaussianReal_llr_eq_quadratic (m : ℝ) (v : ℝ≥0) (hv : v ≠ 0) :
    llr (gaussianReal m v) (gaussianReal 0 1) =ᵐ[gaussianReal m v]
      fun x => -(Real.log v) / 2 - (x - m) ^ 2 / (2 * v) + x ^ 2 / 2 := by
  filter_upwards [gaussianReal_llr_eq_log_pdf_ratio m v hv] with x hx
  rw [hx, Real.log_div (gaussianPDFReal_pos m v x hv).ne'
    (gaussianPDFReal_pos 0 1 x (by norm_num)).ne',
    log_gaussianPDFReal m v hv, log_gaussianPDFReal 0 1 (by norm_num)]
  simp
  ring

/-- The true Gaussian log-likelihood ratio has finite integral. -/
theorem integrable_llr_gaussianReal (m : ℝ) (v : ℝ≥0) (hv : v ≠ 0) :
    Integrable (llr (gaussianReal m v) (gaussianReal 0 1)) (gaussianReal m v) := by
  rw [integrable_congr (gaussianReal_llr_eq_quadratic m v hv)]
  have hX : MemLp (fun x : ℝ => x) 2 (gaussianReal m v) := IsGaussian.memLp_two_id
  exact ((integrable_const _).sub
    ((hX.sub (memLp_const m)).integrable_sq.div_const (2 * v))).add
      (hX.integrable_sq.div_const 2)

/-- Evaluation of the genuine log-likelihood ratio integral. -/
theorem integral_llr_gaussianReal (m : ℝ) (v : ℝ≥0) (hv : v ≠ 0) :
    ∫ x, llr (gaussianReal m v) (gaussianReal 0 1) x ∂gaussianReal m v =
      (m ^ 2 + v - 1 - Real.log v) / 2 := by
  have hX : MemLp (fun x : ℝ => x) 2 (gaussianReal m v) := IsGaussian.memLp_two_id
  have hcenter : ∫ x : ℝ, (x - m) ^ 2 ∂gaussianReal m v = v := by
    have h := variance_eq_integral (X := fun x : ℝ => x) (μ := gaussianReal m v)
      (by fun_prop)
    simpa using h.symm
  have hsquare : ∫ x : ℝ, x ^ 2 ∂gaussianReal m v = m ^ 2 + v := by
    have h := variance_eq_sub hX
    simp only [variance_fun_id_gaussianReal, integral_id_gaussianReal, Pi.pow_apply] at h
    linarith
  rw [integral_congr_ae (gaussianReal_llr_eq_quadratic m v hv)]
  have h1 := integral_add
    ((integrable_const (-(Real.log (v : ℝ)) / 2)).sub
      ((hX.sub (memLp_const m)).integrable_sq.div_const (2 * v)))
    (hX.integrable_sq.div_const 2)
  simp only [Pi.sub_apply] at h1
  rw [h1]
  have h2 := integral_sub (integrable_const (-(Real.log (v : ℝ)) / 2))
    ((hX.sub (memLp_const m)).integrable_sq.div_const (2 * v))
  simp only [Pi.sub_apply] at h2
  rw [h2]
  simp_rw [integral_div]
  rw [integral_const, hcenter, hsquare]
  simp only [probReal_univ, smul_eq_mul, one_mul]
  have hvreal : (v : ℝ) ≠ 0 := NNReal.coe_ne_zero.mpr hv
  field_simp
  ring

/-- Relative entropy of a nondegenerate scalar Gaussian with respect to the
standard Gaussian, using Mathlib's actual Kullback--Leibler divergence. -/
theorem klDiv_gaussianReal_standard (m : ℝ) (v : ℝ≥0) (hv : v ≠ 0) :
    klDiv (gaussianReal m v) (gaussianReal 0 1) =
      ENNReal.ofReal ((m ^ 2 + v - 1 - Real.log v) / 2) := by
  have hac : gaussianReal m v ≪ gaussianReal 0 1 :=
    (gaussianReal_absolutelyContinuous m hv).trans
      (gaussianReal_absolutelyContinuous' 0 (by norm_num))
  rw [klDiv_of_ac_of_integrable hac (integrable_llr_gaussianReal m v hv),
    integral_llr_gaussianReal m v hv]
  simp

/-- The entropy formula for independent Gaussian coordinates, with possibly
different positive variances. The measures here are genuine finite products. -/
theorem klDiv_gaussian_pi_standard (n : ℕ) (m : Fin n → ℝ) (v : Fin n → ℝ≥0)
    (hv : ∀ i, v i ≠ 0) :
    klDiv (Measure.pi (fun i => gaussianReal (m i) (v i)))
        (Measure.pi (fun _ : Fin n => gaussianReal 0 1)) =
      ENNReal.ofReal (∑ i, ((m i) ^ 2 + v i - 1 - Real.log (v i)) / 2) := by
  rw [klDiv_pi_fin_probability]
  simp_rw [klDiv_gaussianReal_standard _ _ (hv _)]
  symm
  apply ENNReal.ofReal_sum_of_nonneg
  intro i hi
  have hpos : (0 : ℝ) < v i := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr (hv i))
  have hlog := Real.log_le_sub_one_of_pos hpos
  linarith [sq_nonneg (m i)]

/-- Independent scalar Gaussian coordinates give the multivariate Gaussian
with the corresponding diagonal covariance matrix. -/
theorem gaussian_pi_eq_multivariate {ι : Type*} [Fintype ι] [DecidableEq ι]
    (m : EuclideanSpace ℝ ι) (v : ι → ℝ≥0) :
    (Measure.pi (fun i => gaussianReal (m i) (v i))).map (WithLp.toLp 2) =
      multivariateGaussian m (Matrix.diagonal (fun i => (v i : ℝ))) := by
  apply Measure.ext_of_charFun
  ext t
  rw [charFun_pi, charFun_multivariateGaussian
    (Matrix.PosSemidef.diagonal (fun i => (v i).coe_nonneg))]
  simp_rw [charFun_gaussianReal, ← Complex.exp_sum]
  congr 1
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, dotProduct,
    Matrix.mulVec_diagonal, Complex.ofReal_sum, Finset.sum_mul, Finset.sum_sub_distrib,
    Finset.sum_div, Complex.ofReal_mul]
  congr 1 <;> apply Finset.sum_congr rfl <;> intro i hi <;> ring

/-- Relative entropy of a multivariate Gaussian with positive diagonal
covariance, obtained from actual independent-coordinate additivity. -/
theorem klDiv_diagonalGaussian_standard (n : ℕ) (m : EuclideanSpace ℝ (Fin n))
    (v : Fin n → ℝ≥0) (hv : ∀ i, v i ≠ 0) :
    klDiv (multivariateGaussian m (Matrix.diagonal (fun i => (v i : ℝ))))
        (stdGaussian (EuclideanSpace ℝ (Fin n))) =
      ENNReal.ofReal ((‖m‖ ^ 2 + ∑ i, ((v i : ℝ) - 1 - Real.log (v i))) / 2) := by
  rw [← gaussian_pi_eq_multivariate, ← map_pi_eq_stdGaussian]
  have h := klDiv_map_measurableEquiv (MeasurableEquiv.toLp 2 (Fin n → ℝ))
    (Measure.pi (fun i => gaussianReal (m i) (v i)))
    (Measure.pi (fun _ : Fin n => gaussianReal 0 1))
  change klDiv ((Measure.pi (fun i => gaussianReal (m i) (v i))).map (WithLp.toLp 2))
    ((Measure.pi (fun _ : Fin n => gaussianReal 0 1)).map (WithLp.toLp 2)) = _ at h
  rw [h, klDiv_gaussian_pi_standard _ _ _ hv]
  congr 1
  rw [← Finset.sum_div, EuclideanSpace.real_norm_sq_eq, ← Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  ring

/-- The genuine isotropic Gaussian entropy formula used in the paper. -/
theorem klDiv_isotropicGaussian_standard (n : ℕ) (m : EuclideanSpace ℝ (Fin n))
    (v : ℝ≥0) (hv : v ≠ 0) :
    klDiv (multivariateGaussian m ((v : ℝ) • (1 : Matrix (Fin n) (Fin n) ℝ)))
        (stdGaussian (EuclideanSpace ℝ (Fin n))) =
      ENNReal.ofReal ((‖m‖ ^ 2 + n * ((v : ℝ) - 1 - Real.log v)) / 2) := by
  have hmat : Matrix.diagonal (fun _ : Fin n => (v : ℝ)) =
      (v : ℝ) • (1 : Matrix (Fin n) (Fin n) ℝ) := by
    ext i j
    by_cases hij : i = j <;> simp [hij]
  rw [← hmat]
  simpa [mul_sub] using klDiv_diagonalGaussian_standard n m (fun _ => v) (fun _ => hv)

/-- Entropy of the precise Mehler Gaussian marginal used for the OU
projection. The stochastic identification of this law remains separate. -/
theorem klDiv_ou_marginal (n : ℕ) (z : EuclideanSpace ℝ (Fin n))
    (ρ t : ℝ) (hρ : 0 < ρ) (ht : 0 < t) :
    klDiv
        (multivariateGaussian (Real.exp (-ρ * t) • z)
          ((1 - Real.exp (-2 * ρ * t)) • (1 : Matrix (Fin n) (Fin n) ℝ)))
        (stdGaussian (EuclideanSpace ℝ (Fin n))) =
      ENNReal.ofReal ((Real.exp (-2 * ρ * t) * ‖z‖ ^ 2 +
        n * (-Real.exp (-2 * ρ * t) - Real.log (1 - Real.exp (-2 * ρ * t)))) / 2) := by
  have hvpos : 0 < 1 - Real.exp (-2 * ρ * t) := by
    apply sub_pos.mpr
    rw [Real.exp_lt_one_iff]
    nlinarith [mul_pos hρ ht]
  let v : ℝ≥0 := ⟨1 - Real.exp (-2 * ρ * t), hvpos.le⟩
  have hv : v ≠ 0 := NNReal.coe_ne_zero.mp hvpos.ne'
  have hnorm : ‖Real.exp (-ρ * t) • z‖ ^ 2 =
      Real.exp (-2 * ρ * t) * ‖z‖ ^ 2 := by
    rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
    congr 1
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  have h := klDiv_isotropicGaussian_standard n (Real.exp (-ρ * t) • z) v hv
  rw [hnorm] at h
  change klDiv
      (multivariateGaussian (Real.exp (-ρ * t) • z)
        ((1 - Real.exp (-2 * ρ * t)) • (1 : Matrix (Fin n) (Fin n) ℝ)))
      (stdGaussian (EuclideanSpace ℝ (Fin n))) =
    ENNReal.ofReal ((Real.exp (-2 * ρ * t) * ‖z‖ ^ 2 +
      n * ((1 - Real.exp (-2 * ρ * t)) - 1 - Real.log (1 - Real.exp (-2 * ρ * t)))) / 2) at h
  rw [h]
  congr 1
  ring

end CutoffRigidity
