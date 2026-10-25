module
public import CutoffRigidity.TransportMoments

/-! # Integrating a pointwise entropy-cost comparison over actual couplings

The quadratic transport infimum is taken over genuine coupling measures.
Infinite coupling costs are handled explicitly before real integration.
-/
public section
namespace CutoffRigidity
open MeasureTheory Filter
open scoped ENNReal
variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

theorem ofReal_le_mul_squaredWasserstein_of_pointwise
    (ν μ : Measure E) [IsProbabilityMeasure ν] [IsProbabilityMeasure μ]
    (A B : E → ℝ) (hA : Continuous A) (hB : Continuous B)
    (hAb : ∃ M : ℝ, ∀ x, ‖A x‖ ≤ M) (hBb : ∃ M : ℝ, ∀ x, ‖B x‖ ≤ M)
    (C H : ℝ) (hC : 0 < C) (hH : H = ∫ x, A x ∂ν)
    (hBmean : ∫ x, B x ∂μ ≤ 0)
    (hpoint : ∀ x y, A x ≤ B y + C * ‖x - y‖ ^ 2) :
    ENNReal.ofReal H ≤ ENNReal.ofReal C * squaredWasserstein ν μ := by
  rw [squaredWasserstein, ENNReal.mul_iInf_of_ne (ENNReal.ofReal_ne_zero_iff.mpr hC) ENNReal.ofReal_ne_top]
  apply le_iInf
  intro π
  by_cases hcost : (∫⁻ z, edist z.1 z.2 ^ 2 ∂π.val) = ⊤
  · simp [hcost, ENNReal.ofReal_ne_zero_iff.mpr hC]
  let := π.isProbabilityMeasure
  have he : (∫⁻ z : E × E, ENNReal.ofReal (‖z.1 - z.2‖ ^ 2) ∂π.val) =
      ∫⁻ z, edist z.1 z.2 ^ 2 ∂π.val := by
    apply lintegral_congr
    intro z
    rw [edist_dist, dist_eq_norm, ENNReal.ofReal_pow (norm_nonneg _) 2]
  have hci : Integrable (fun z : E × E => ‖z.1 - z.2‖ ^ 2) π.val := by
    refine ⟨by fun_prop, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun z => sq_nonneg _), he]
    exact lt_top_iff_ne_top.mpr hcost
  obtain ⟨M, hM⟩ := hAb
  obtain ⟨N, hN⟩ := hBb
  have hAi : Integrable (fun z : E × E => A z.1) π.val :=
    (integrable_const M).mono' (hA.comp continuous_fst).aestronglyMeasurable
      (Eventually.of_forall fun z => hM z.1)
  have hBi : Integrable (fun z : E × E => B z.2) π.val :=
    (integrable_const N).mono' (hB.comp continuous_snd).aestronglyMeasurable
      (Eventually.of_forall fun z => hN z.2)
  have hmeanA : (∫ z : E × E, A z.1 ∂π.val) = ∫ x, A x ∂ν := by
    have hi := integral_map (μ := π.val) measurable_fst.aemeasurable hA.measurable.aestronglyMeasurable
    rw [π.property.1] at hi
    exact hi.symm
  have hmeanB : (∫ z : E × E, B z.2 ∂π.val) = ∫ x, B x ∂μ := by
    have hi := integral_map (μ := π.val) measurable_snd.aemeasurable hB.measurable.aestronglyMeasurable
    rw [π.property.2] at hi
    exact hi.symm
  have hreal : H ≤ C * ∫ z : E × E, ‖z.1 - z.2‖ ^ 2 ∂π.val := by
    have hi := integral_mono_ae hAi (hBi.add (hci.const_mul C))
      (Eventually.of_forall fun z => hpoint z.1 z.2)
    simp only [Pi.add_apply] at hi
    rw [integral_add hBi (hci.const_mul C), integral_const_mul, hmeanA, hmeanB, ← hH] at hi
    linarith
  calc
    ENNReal.ofReal H ≤ ENNReal.ofReal (C * ∫ z : E × E, ‖z.1 - z.2‖ ^ 2 ∂π.val) :=
      ENNReal.ofReal_le_ofReal hreal
    _ = ENNReal.ofReal C * ENNReal.ofReal (∫ z : E × E, ‖z.1 - z.2‖ ^ 2 ∂π.val) :=
      ENNReal.ofReal_mul hC.le
    _ = _ := by
      rw [ofReal_integral_eq_lintegral_ofReal hci (Eventually.of_forall fun z => sq_nonneg _), he]

end CutoffRigidity
