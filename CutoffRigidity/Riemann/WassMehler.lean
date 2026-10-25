module

public import CutoffRigidity.Riemann.TransportMain
public import CutoffRigidity.OUKernel

/-! # Mehler law of the Euclidean coordinate from the Mehler law of all linear functionals

If every real linear functional `x ↦ ⟪z, p x⟫` of the Euclidean coordinate `p` has the Gaussian
law `N(e^{-ρt}⟪z, p x₀⟫, (1-e^{-2ρt})‖z‖²/ρ)` under `ν`, then `ν.map p` is the Mehler law
(characteristic functions).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal RealInnerProductSpace

namespace CutoffRigidity.Riemann

variable {M N : Type*} [PseudoEMetricSpace M] [MeasurableSpace M] [OpensMeasurableSpace M]
  [PseudoEMetricSpace N] [MeasurableSpace N] {k : ℕ} {ρ : ℝ} {μ : Measure M}

theorem map_proj_eq_mehler (hρ : 0 < ρ) (D : SplitData M N k ρ μ) (ν : Measure M)
    [IsProbabilityMeasure ν] (t : ℝ≥0) (x₀ : M)
    (h : ∀ z : EuclideanSpace ℝ (Fin k),
      ν.map (fun x => ⟪z, D.proj x⟫) = gaussianReal (Real.exp (-ρ * t) * ⟪z, D.proj x₀⟫)
        (((1 - Real.exp (-2 * ρ * t)) * (‖z‖ ^ 2 / ρ)).toNNReal)) :
    ν.map D.proj = SplitData.mehler ρ t (D.proj x₀) := by
  have hq : 0 ≤ 1 - Real.exp (-2 * ρ * t) := by
    have : Real.exp (-2 * ρ * t) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith [t.coe_nonneg])
    linarith
  have hnn : 0 ≤ ρ⁻¹ * (1 - Real.exp (-2 * ρ * t)) := mul_nonneg (inv_nonneg.2 hρ.le) hq
  have hm : SplitData.mehler ρ t (D.proj x₀) = CutoffRigidity.affineGaussian
      (Real.exp (-ρ * t) • D.proj x₀) (Real.sqrt (ρ⁻¹ * (1 - Real.exp (-2 * ρ * t)))) := by
    rw [CutoffRigidity.affineGaussian_eq_multivariateGaussian _ _ (Real.sqrt_nonneg _),
      Real.sq_sqrt hnn]
    rfl
  rw [hm]
  refine Measure.ext_of_charFun (funext fun z => ?_)
  rw [charFun_map_eq_charFun_map_inner_one D.measurable_proj.aemeasurable z,
    CutoffRigidity.charFun_affineGaussian]
  simp_rw [real_inner_comm z]
  rw [h z, charFun_gaussianReal, Real.coe_toNNReal _ (mul_nonneg hq (by positivity))]
  congr 1
  rw [inner_smul_right]
  have hs : ((Real.sqrt (ρ⁻¹ * (1 - Real.exp (-2 * ρ * t))) : ℝ) : ℂ) ^ 2 =
      ((ρ⁻¹ * (1 - Real.exp (-2 * ρ * t)) : ℝ) : ℂ) := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt hnn]
  rw [hs]
  have hρ' : (ρ : ℂ) ≠ 0 := by exact_mod_cast hρ.ne'
  push_cast
  field_simp

end CutoffRigidity.Riemann
