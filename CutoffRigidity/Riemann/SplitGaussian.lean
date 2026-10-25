module

public import CutoffRigidity.GaussianDensity
public import CutoffRigidity.GaussianEntropy

/-! # Lebesgue density of the isotropic Gaussian on Euclidean space -/

@[expose] public section

open ProbabilityTheory MeasureTheory
open scoped ENNReal NNReal

namespace CutCur

theorem pi_eq_withDensity_sigmaFinite (n : ℕ) (μ ν : Fin n → Measure ℝ)
    [∀ i, SigmaFinite (μ i)] [∀ i, SigmaFinite (ν i)]
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
    rw [CutoffRigidity.map_withDensity_measurableEquiv e _ _ (by fun_prop)]
    rw [(measurePreserving_piFinSuccAbove ν 0).map_eq]
    simp only [Fin.succAbove_zero]
    rw [hμ 0, ih (fun i => μ i.succ) (fun i => ν i.succ)
      (fun i => f i.succ) (fun i => hf i.succ) (fun i => hμ i.succ)]
    rw [prod_withDensity (hf 0) (by fun_prop)]
    congr 1
    ext z
    simp [e, MeasurableEquiv.piFinSuccAbove_symm_apply,
      Fin.insertNthEquiv, Fin.prod_univ_succ]

theorem multivariateGaussian_eq_withDensity (k : ℕ) {ρ : ℝ} (hρ : 0 < ρ) :
    multivariateGaussian (0 : EuclideanSpace ℝ (Fin k)) (ρ⁻¹ • (1 : Matrix (Fin k) (Fin k) ℝ)) =
      (volume : Measure (EuclideanSpace ℝ (Fin k))).withDensity
        (fun t => ENNReal.ofReal ((ρ / (2 * Real.pi)) ^ ((k : ℝ) / 2) *
          Real.exp (-(ρ / 2) * ‖t‖ ^ 2))) := by
  set v : ℝ≥0 := Real.toNNReal ρ⁻¹ with hv
  have hvc : (v : ℝ) = ρ⁻¹ := Real.coe_toNNReal _ (by positivity)
  have hv0 : v ≠ 0 := (Real.toNNReal_pos.2 (by positivity)).ne'
  have hmat : ρ⁻¹ • (1 : Matrix (Fin k) (Fin k) ℝ) =
      Matrix.diagonal (fun _ => (v : ℝ)) := by
    ext i j
    by_cases h : i = j <;> simp [Matrix.one_apply, Matrix.diagonal_apply, h, hvc]
  have hpi := pi_eq_withDensity_sigmaFinite k (fun _ => gaussianReal 0 v)
    (fun _ => volume) (fun _ => gaussianPDF 0 v) (fun _ => measurable_gaussianPDF 0 v)
    (fun _ => gaussianReal_of_var_ne_zero 0 hv0)
  have hmap := congrArg (fun μ : Measure (Fin k → ℝ) => μ.map (WithLp.toLp 2)) hpi
  have h1 := CutoffRigidity.gaussian_pi_eq_multivariate (0 : EuclideanSpace ℝ (Fin k)) (fun _ : Fin k => v)
  simp only [PiLp.zero_apply] at h1
  rw [hmat, ← h1]
  refine hmap.trans ?_
  change ((Measure.pi (fun _ : Fin k => (volume : Measure ℝ))).withDensity
      (fun x => ∏ i, gaussianPDF 0 v (x i))).map (MeasurableEquiv.toLp 2 (Fin k → ℝ)) = _
  rw [CutoffRigidity.map_withDensity_measurableEquiv _ _ _ (by fun_prop)]
  have hvol : (Measure.pi (fun _ : Fin k => (volume : Measure ℝ))).map (WithLp.toLp 2) =
      volume := (PiLp.volume_preserving_toLp (Fin k)).map_eq
  change ((Measure.pi (fun _ : Fin k => (volume : Measure ℝ))).map (WithLp.toLp 2)).withDensity _ = _
  rw [hvol]
  congr 1
  ext t
  show ∏ i, gaussianPDF 0 v ((MeasurableEquiv.toLp 2 (Fin k → ℝ)).symm t i) = _
  have hsymm : ∀ i, (MeasurableEquiv.toLp 2 (Fin k → ℝ)).symm t i = t i := fun i => rfl
  simp only [hsymm, gaussianPDF_def, gaussianPDFReal_def]
  rw [← ENNReal.ofReal_prod_of_nonneg (fun i _ => by positivity)]
  congr 1
  rw [Finset.prod_mul_distrib, Finset.prod_const, ← Real.exp_sum, Finset.card_univ,
    Fintype.card_fin, EuclideanSpace.norm_sq_eq]
  have h2 : (2 * Real.pi * (v : ℝ)) = 2 * Real.pi / ρ := by rw [hvc]; ring
  have h3 : ((ρ / (2 * Real.pi)) ^ ((k : ℝ) / 2)) = ((Real.sqrt (2 * Real.pi * v))⁻¹) ^ k := by
    have hq : 0 ≤ 2 * Real.pi / ρ := by positivity
    have : ρ / (2 * Real.pi) = (2 * Real.pi / ρ)⁻¹ := by rw [inv_div]
    rw [h2, inv_pow, this, Real.inv_rpow hq, Real.sqrt_eq_rpow, ← Real.rpow_natCast,
      ← Real.rpow_mul hq]
    congr 2
    ring
  rw [h3]
  congr 2
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hvc, Real.norm_eq_abs, sq_abs]
  field_simp
  ring_nf

theorem lintegral_exp_neg_sq (k : ℕ) {ρ : ℝ} (hρ : 0 < ρ) :
    ∫⁻ t : EuclideanSpace ℝ (Fin k), ENNReal.ofReal (Real.exp (-(ρ / 2) * ‖t‖ ^ 2)) =
      ENNReal.ofReal ((2 * Real.pi / ρ) ^ ((k : ℝ) / 2)) := by
  set c : ℝ := (ρ / (2 * Real.pi)) ^ ((k : ℝ) / 2) with hc
  have hcpos : 0 < c := by positivity
  have h := multivariateGaussian_eq_withDensity k hρ
  have h1 : (multivariateGaussian (0 : EuclideanSpace ℝ (Fin k))
      (ρ⁻¹ • (1 : Matrix (Fin k) (Fin k) ℝ))) Set.univ = 1 := measure_univ
  rw [h, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ] at h1
  rw [← hc] at h1
  simp_rw [ENNReal.ofReal_mul hcpos.le] at h1
  rw [lintegral_const_mul _ (by fun_prop)] at h1
  have hinv : (2 * Real.pi / ρ) ^ ((k : ℝ) / 2) = c⁻¹ := by
    rw [hc, ← Real.inv_rpow (by positivity), inv_div]
  rw [hinv, ENNReal.ofReal_inv_of_pos hcpos]
  exact (ENNReal.eq_inv_of_mul_eq_one_left (by rwa [mul_comm] at h1))

end CutCur
