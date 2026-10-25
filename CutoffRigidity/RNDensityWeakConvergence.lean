module
public import CutoffRigidity.LangevinL1Density
public import Mathlib.Topology.ContinuousMap.Bounded.Basic

/-! # Actual RN L¹ convergence implies weak test convergence

The RN reconstruction identity and the genuine norm-of-integral bound
transfer density approximation to actual measures.
-/
public section
namespace CutoffRigidity
open MeasureTheory Filter
open scoped Topology BoundedContinuousFunction

theorem integral_eq_integral_toReal_rnDeriv_mul
    {X : Type*} [MeasurableSpace X] (ν μ : Measure X)
    [IsFiniteMeasure ν] [SigmaFinite μ] (hAC : ν ≪ μ)
    {φ : X → ℝ} (hφ : Measurable φ) :
    (∫ x, φ x ∂ν) = ∫ x, (ν.rnDeriv μ x).toReal * φ x ∂μ := by
  calc
    _ = ∫ x, φ x ∂μ.withDensity (fun x => ENNReal.ofReal ((ν.rnDeriv μ x).toReal)) :=
      congrArg (fun ζ : Measure X => ∫ x, φ x ∂ζ)
        (withDensity_ofReal_toReal_rnDeriv_eq ν μ hAC).symm
    _ = _ := by
      rw [integral_withDensity_eq_integral_toReal_smul
        (Measure.measurable_rnDeriv ν μ).ennreal_toReal.ennreal_ofReal (by simp)]
      simp only [ENNReal.toReal_ofReal ENNReal.toReal_nonneg, smul_eq_mul]

theorem tendsto_integral_of_L1_rnDeriv
    {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    (μ ν : Measure X) [SigmaFinite μ] [IsFiniteMeasure ν]
    (νn : ℕ → Measure X) [∀ n, IsFiniteMeasure (νn n)]
    (hAC : ν ≪ μ) (hACn : ∀ n, νn n ≪ μ)
    (hlim : Tendsto (fun n => ∫ x,
      |((νn n).rnDeriv μ x).toReal - (ν.rnDeriv μ x).toReal| ∂μ) atTop (𝓝 0))
    (φ : X →ᵇ ℝ) :
    Tendsto (fun n => ∫ x, φ x ∂νn n) atTop (𝓝 (∫ x, φ x ∂ν)) := by
  let f := fun x => (ν.rnDeriv μ x).toReal
  let fn := fun n x => ((νn n).rnDeriv μ x).toReal
  have hf : Integrable f μ := integrable_toReal_rnDeriv_finite ν μ
  have hfn (n : ℕ) : Integrable (fn n) μ := integrable_toReal_rnDeriv_finite (νn n) μ
  have hfi : Integrable (fun x => f x * φ x) μ :=
    hf.mul_bdd φ.continuous.aestronglyMeasurable (Eventually.of_forall fun x => φ.norm_coe_le_norm x)
  have hfni (n : ℕ) : Integrable (fun x => fn n x * φ x) μ :=
    (hfn n).mul_bdd φ.continuous.aestronglyMeasurable (Eventually.of_forall fun x => φ.norm_coe_le_norm x)
  have hnorm : Tendsto (fun n => ‖(∫ x, φ x ∂νn n) - ∫ x, φ x ∂ν‖) atTop (𝓝 0) := by
    apply squeeze_zero (fun n => norm_nonneg _) _ (by simpa using hlim.const_mul ‖φ‖)
    intro n
    rw [integral_eq_integral_toReal_rnDeriv_mul (νn n) μ (hACn n) φ.continuous.measurable,
      integral_eq_integral_toReal_rnDeriv_mul ν μ hAC φ.continuous.measurable,
      ← integral_sub (hfni n) hfi]
    have hiW := ((hfni n).sub hfi).norm
    have hiB := ((hfn n).sub hf).abs.const_mul ‖φ‖
    apply (norm_integral_le_integral_norm _).trans
    rw [← integral_const_mul]
    apply integral_mono_ae hiW hiB
    apply Eventually.of_forall
    intro x
    simp only [Pi.sub_apply]
    rw [← sub_mul, norm_mul, Real.norm_eq_abs (fn n x - f x)]
    exact (mul_le_mul_of_nonneg_left (φ.norm_coe_le_norm x) (abs_nonneg _)).trans_eq (mul_comm _ _)
  exact tendsto_iff_norm_sub_tendsto_zero.mpr hnorm

end CutoffRigidity
