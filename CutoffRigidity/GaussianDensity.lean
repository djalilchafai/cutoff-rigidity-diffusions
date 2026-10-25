module

public import CutoffRigidity.GaussianFisher
public import Mathlib.MeasureTheory.Measure.WithDensity

/-!
# Canonical smooth Gaussian Radon--Nikodym representatives

The positive product-density ratio is identified with the actual density of
the diagonal multivariate Gaussian relative to the standard Gaussian. This
supplies a certified smooth representative for the squared-gradient integrals.
-/

public section

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace CutoffRigidity

/-- Mapping a density through a measurable equivalence transforms it by the
inverse coordinate change. -/
theorem map_withDensity_measurableEquiv {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (e : α ≃ᵐ β) (μ : Measure α) (f : α → ℝ≥0∞) (hf : Measurable f) :
    (μ.withDensity f).map e = (μ.map e).withDensity (fun y => f (e.symm y)) := by
  ext s hs
  rw [Measure.map_apply e.measurable hs, withDensity_apply f (e.measurable hs),
    withDensity_apply (fun y => f (e.symm y)) hs]
  rw [setLIntegral_map (f := fun y => f (e.symm y)) hs
    (by exact hf.comp e.symm.measurable) e.measurable]
  simp

/-- Each nondegenerate scalar Gaussian is the standard Gaussian weighted by
its canonical positive smooth density ratio. -/
theorem gaussianReal_eq_withDensity_standard (m : ℝ) (v : ℝ≥0) (hv : v ≠ 0) :
    gaussianReal m v = (gaussianReal 0 1).withDensity
      (fun x => ENNReal.ofReal (gaussianPDFReal m v x / gaussianPDFReal 0 1 x)) := by
  have hr := Measure.rnDeriv_withDensity_right (gaussianReal m v) volume
    (measurable_gaussianPDF 0 1).aemeasurable
    (Filter.Eventually.of_forall fun x => (gaussianPDF_pos 0 (by norm_num) x).ne')
    (Filter.Eventually.of_forall fun x => (gaussianPDF_lt_top (μ := 0) (v := 1) (x := x)).ne)
  rw [← gaussianReal_of_var_ne_zero 0 (by norm_num)] at hr
  have hstd := gaussianReal_absolutelyContinuous 0 (v := 1) (by norm_num)
  have hpdf : (gaussianReal m v).rnDeriv (gaussianReal 0 1) =ᵐ[gaussianReal 0 1]
      fun x => ENNReal.ofReal (gaussianPDFReal m v x / gaussianPDFReal 0 1 x) := by
    filter_upwards [hstd.ae_le hr, hstd.ae_le (rnDeriv_gaussianReal m v)] with x hx hp
    rw [hx, hp, gaussianPDF_def, gaussianPDF_def, ENNReal.ofReal_div_of_pos
      (gaussianPDFReal_pos 0 1 x (by norm_num)), div_eq_mul_inv]
    ring
  have hac : gaussianReal m v ≪ gaussianReal 0 1 :=
    (gaussianReal_absolutelyContinuous m hv).trans
      (gaussianReal_absolutelyContinuous' 0 (by norm_num))
  calc
    _ = (gaussianReal 0 1).withDensity ((gaussianReal m v).rnDeriv (gaussianReal 0 1)) :=
      (Measure.withDensity_rnDeriv_eq _ _ hac).symm
    _ = _ := withDensity_congr_ae hpdf

/-- Coordinate densities multiply for finite products of probability measures. -/
theorem pi_eq_withDensity_of_coordinates (n : ℕ) (μ ν : Fin n → Measure ℝ)
    [∀ i, IsProbabilityMeasure (μ i)] [∀ i, IsProbabilityMeasure (ν i)]
    (f : Fin n → ℝ → ℝ≥0∞) (hf : ∀ i, Measurable (f i))
    (hμ : ∀ i, μ i = (ν i).withDensity (f i)) :
    Measure.pi μ = (Measure.pi ν).withDensity (fun x => ∏ i, f i (x i)) := by
  induction n with
  | zero =>
    simp only [Finset.univ_eq_empty, Finset.prod_empty]
    rw [← Pi.one_def, withDensity_one]
    congr 1
    funext i
    exact Fin.elim0 i
  | succ n ih =>
    let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0
    apply e.measurableEmbedding.map_injective
    rw [(measurePreserving_piFinSuccAbove μ 0).map_eq]
    rw [map_withDensity_measurableEquiv e _ _ (by fun_prop)]
    rw [(measurePreserving_piFinSuccAbove ν 0).map_eq]
    simp only [Fin.succAbove_zero]
    rw [hμ 0, ih (fun i => μ i.succ) (fun i => ν i.succ)
      (fun i => f i.succ) (fun i => hf i.succ) (fun i => hμ i.succ)]
    rw [prod_withDensity (hf 0) (by fun_prop)]
    congr 1
    ext z
    simp [e, MeasurableEquiv.piFinSuccAbove_symm_apply,
      Fin.insertNthEquiv, Fin.prod_univ_succ]

/-- The canonical pointwise ratio of diagonal Gaussian and standard Gaussian
densities. The strict positivity and smoothness are proved below. -/
@[expose] noncomputable def diagonalGaussianDensityRatio {ι : Type*} [Fintype ι]
    (m : EuclideanSpace ℝ ι) (v : ι → ℝ≥0) (x : EuclideanSpace ℝ ι) : ℝ :=
  (∏ i, gaussianPDFReal (m i) (v i) (x i)) / (∏ i, gaussianPDFReal 0 1 (x i))

theorem diagonalGaussianDensityRatio_pos {ι : Type*} [Fintype ι]
    (m : EuclideanSpace ℝ ι) (v : ι → ℝ≥0) (hv : ∀ i, v i ≠ 0)
    (x : EuclideanSpace ℝ ι) : 0 < diagonalGaussianDensityRatio m v x := by
  apply div_pos
  · exact Finset.prod_pos (fun i _ => gaussianPDFReal_pos _ _ _ (hv i))
  · exact Finset.prod_pos (fun i _ => gaussianPDFReal_pos _ _ _ (by norm_num))

theorem contDiff_diagonalGaussianDensityRatio {ι : Type*} [Fintype ι]
    (m : EuclideanSpace ℝ ι) (v : ι → ℝ≥0) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (diagonalGaussianDensityRatio m v) := by
  unfold diagonalGaussianDensityRatio
  apply ContDiff.div
  · unfold gaussianPDFReal
    fun_prop
  · unfold gaussianPDFReal
    fun_prop
  · intro x
    exact (Finset.prod_pos (fun i _ => gaussianPDFReal_pos 0 1 (x i) (by norm_num))).ne'

/-- Identification of the genuine diagonal Gaussian as standard Gaussian
weighted by its canonical positive product-density ratio. -/
theorem diagonalGaussian_eq_withDensity_standard (n : ℕ)
    (m : EuclideanSpace ℝ (Fin n)) (v : Fin n → ℝ≥0) (hv : ∀ i, v i ≠ 0) :
    multivariateGaussian m (Matrix.diagonal (fun i => (v i : ℝ))) =
      (stdGaussian (EuclideanSpace ℝ (Fin n))).withDensity
        (fun x => ENNReal.ofReal (diagonalGaussianDensityRatio m v x)) := by
  have hpi := pi_eq_withDensity_of_coordinates n
    (fun i => gaussianReal (m i) (v i)) (fun _ : Fin n => gaussianReal 0 1)
    (fun i x => ENNReal.ofReal (gaussianPDFReal (m i) (v i) x / gaussianPDFReal 0 1 x))
    (fun i => by fun_prop) (fun i => gaussianReal_eq_withDensity_standard _ _ (hv i))
  have hmap := congrArg (fun μ : Measure (Fin n → ℝ) => μ.map (WithLp.toLp 2)) hpi
  rw [gaussian_pi_eq_multivariate] at hmap
  change multivariateGaussian m (Matrix.diagonal (fun i => (v i : ℝ))) =
    ((Measure.pi (fun _ : Fin n => gaussianReal 0 1)).withDensity
      (fun x => ∏ i, ENNReal.ofReal
        (gaussianPDFReal (m i) (v i) (x i) / gaussianPDFReal 0 1 (x i)))).map
          (MeasurableEquiv.toLp 2 (Fin n → ℝ)) at hmap
  rw [map_withDensity_measurableEquiv _ _ _ (by fun_prop)] at hmap
  change multivariateGaussian m (Matrix.diagonal (fun i => (v i : ℝ))) =
    ((Measure.pi (fun _ : Fin n => gaussianReal 0 1)).map (WithLp.toLp 2)).withDensity
      (fun x => ∏ i, ENNReal.ofReal
        (gaussianPDFReal (m i) (v i) (x i) / gaussianPDFReal 0 1 (x i))) at hmap
  rw [map_pi_eq_stdGaussian] at hmap
  rw [hmap]
  congr 1
  ext x
  unfold diagonalGaussianDensityRatio
  rw [← Finset.prod_div_distrib, ENNReal.ofReal_prod_of_nonneg]
  intro i hi
  exact div_nonneg (gaussianPDFReal_nonneg _ _ _) (gaussianPDFReal_nonneg _ _ _)

/-- The canonical product-density ratio is a representative of the actual
Radon--Nikodym derivative relative to the standard Gaussian. -/
theorem rnDeriv_diagonalGaussian_standard (n : ℕ)
    (m : EuclideanSpace ℝ (Fin n)) (v : Fin n → ℝ≥0) (hv : ∀ i, v i ≠ 0) :
    (multivariateGaussian m (Matrix.diagonal (fun i => (v i : ℝ)))).rnDeriv
        (stdGaussian (EuclideanSpace ℝ (Fin n))) =ᵐ[stdGaussian (EuclideanSpace ℝ (Fin n))]
      fun x => ENNReal.ofReal (diagonalGaussianDensityRatio m v x) := by
  rw [diagonalGaussian_eq_withDensity_standard n m v hv]
  apply Measure.rnDeriv_withDensity
  exact ((contDiff_diagonalGaussianDensityRatio m v).continuous.measurable).ennreal_ofReal

/-- The same canonical RN representative is valid almost everywhere under
the diagonal Gaussian itself, by absolute continuity. -/
theorem rnDeriv_diagonalGaussian_standard_self_ae (n : ℕ)
    (m : EuclideanSpace ℝ (Fin n)) (v : Fin n → ℝ≥0) (hv : ∀ i, v i ≠ 0) :
    (multivariateGaussian m (Matrix.diagonal (fun i => (v i : ℝ)))).rnDeriv
        (stdGaussian (EuclideanSpace ℝ (Fin n)))
      =ᵐ[multivariateGaussian m (Matrix.diagonal (fun i => (v i : ℝ)))]
        fun x => ENNReal.ofReal (diagonalGaussianDensityRatio m v x) := by
  have hac : multivariateGaussian m (Matrix.diagonal (fun i => (v i : ℝ))) ≪
      stdGaussian (EuclideanSpace ℝ (Fin n)) := by
    rw [diagonalGaussian_eq_withDensity_standard n m v hv]
    exact withDensity_absolutelyContinuous _ _
  exact hac.ae_le (rnDeriv_diagonalGaussian_standard n m v hv)

/-- The canonical logarithmic RN representative is smooth everywhere. -/
theorem contDiff_log_diagonalGaussianDensityRatio {ι : Type*} [Fintype ι]
    (m : EuclideanSpace ℝ ι) (v : ι → ℝ≥0) (hv : ∀ i, v i ≠ 0) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x => Real.log (diagonalGaussianDensityRatio m v x)) := by
  exact (contDiff_diagonalGaussianDensityRatio m v).log
    (fun x => (diagonalGaussianDensityRatio_pos m v hv x).ne')

/-- Genuine multivariate log-likelihood ratio, identified with the smooth
canonical representative rather than differentiated as an arbitrary a.e. function. -/
theorem llr_diagonalGaussian_standard (n : ℕ)
    (m : EuclideanSpace ℝ (Fin n)) (v : Fin n → ℝ≥0) (hv : ∀ i, v i ≠ 0) :
    llr (multivariateGaussian m (Matrix.diagonal (fun i => (v i : ℝ))))
        (stdGaussian (EuclideanSpace ℝ (Fin n)))
      =ᵐ[multivariateGaussian m (Matrix.diagonal (fun i => (v i : ℝ)))]
        fun x => Real.log (diagonalGaussianDensityRatio m v x) := by
  filter_upwards [rnDeriv_diagonalGaussian_standard_self_ae n m v hv] with x hx
  rw [llr, hx, ENNReal.toReal_ofReal (diagonalGaussianDensityRatio_pos m v hv x).le]

/-- Fisher integral using the proven smooth canonical RN representative.
No derivative is taken of an arbitrary almost-everywhere RN representative. -/
theorem diagonalGaussian_canonical_fisher_integral (n : ℕ)
    (m : EuclideanSpace ℝ (Fin n)) (v : Fin n → ℝ≥0) (hv : ∀ i, v i ≠ 0) :
    ∫ x, ‖gradient (fun y => Real.log (diagonalGaussianDensityRatio m v y)) x‖ ^ 2
      ∂multivariateGaussian m (Matrix.diagonal (fun i => (v i : ℝ))) =
      ‖m‖ ^ 2 + ∑ i, ((v i : ℝ) - 1) ^ 2 / v i := by
  change (∫ x, ‖gradient (diagonalGaussianLogDensityRatio m v) x‖ ^ 2
      ∂multivariateGaussian m (Matrix.diagonal (fun i => (v i : ℝ)))) = _
  exact diagonalGaussian_fisher_integral_standard m v hv

end CutoffRigidity
