module
public import CutoffRigidity.RNDensityWeakConvergence

/-! # Actual local measure domination from actual RN-density bounds -/
public section
namespace CutoffRigidity
open MeasureTheory Filter Set
open scoped ENNReal

 theorem measure_restrict_le_of_rnDeriv_toReal_bound
    {X : Type*} [MeasurableSpace X] (ν μ : Measure X) [IsFiniteMeasure ν] [SigmaFinite μ]
    (hAC : ν ≪ μ) (K : Set X) (hK : MeasurableSet K) (M : ℝ) (hM : 0 ≤ M)
    (hBound : ∀ᵐ x ∂μ, x ∈ K → (ν.rnDeriv μ x).toReal ≤ M) :
    ν.restrict K ≤ ENNReal.ofReal M • μ := by
  have hRN : ∀ᵐ x ∂μ, x ∈ K → ν.rnDeriv μ x ≤ ENNReal.ofReal M := by
    filter_upwards [hBound,Measure.rnDeriv_ne_top ν μ] with x hx hn
    intro hxK
    rw [← ENNReal.ofReal_toReal hn]
    exact ENNReal.ofReal_le_ofReal (hx hxK)
  apply Measure.le_iff.mpr
  intro A hA
  calc
    (ν.restrict K) A = ν (A ∩ K) := Measure.restrict_apply hA
    _ = ∫⁻ x in A ∩ K, ν.rnDeriv μ x ∂μ := by
      have he := congrArg (fun ζ : Measure X => ζ (A ∩ K)) (Measure.withDensity_rnDeriv_eq ν μ hAC).symm
      exact he.trans (withDensity_apply _ (hA.inter hK))
    _ ≤ ∫⁻ _x in A ∩ K, ENNReal.ofReal M ∂μ := by
      apply lintegral_mono_ae
      rw [ae_restrict_iff' (hA.inter hK)]
      filter_upwards [hRN] with x hx hxA
      exact hx hxA.2
    _ = ENNReal.ofReal M * μ (A ∩ K) := by simp [lintegral_const,mul_comm]
    _ ≤ ENNReal.ofReal M * μ A := mul_le_mul' le_rfl (measure_mono inter_subset_left)
    _ = (ENNReal.ofReal M • μ) A := by simp [Measure.smul_apply]

end CutoffRigidity
