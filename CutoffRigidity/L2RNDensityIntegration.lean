module
public import CutoffRigidity.GibbsRNFromL2Tests

/-! # Actual integration against genuine L² Radon--Nikodym densities

This is the actual RN reconstruction and Hilbert Cauchy--Schwarz bound,
including integrability of every genuine L² input under the target law.
-/
public section
namespace CutoffRigidity
open MeasureTheory Filter

theorem integrable_of_memLp_two_rnDeriv
    {X : Type*} [MeasurableSpace X] (ν μ : Measure X) [IsFiniteMeasure ν] [SigmaFinite μ]
    (hAC : ν ≪ μ)
    (hRN : MemLp (fun x => (ν.rnDeriv μ x).toReal) 2 μ)
    {f : X → ℝ} (hf : MemLp f 2 μ) : Integrable f ν := by
  have hi := hRN.integrable_mul hf
  have hrec := Measure.withDensity_rnDeriv_eq ν μ hAC
  rw [← hrec]
  apply (integrable_withDensity_iff_integrable_smul' (Measure.measurable_rnDeriv ν μ)
    (Measure.rnDeriv_lt_top ν μ)).mpr
  convert! hi using 1

theorem norm_integral_le_L2_rnDeriv
    {X : Type*} [MeasurableSpace X] (ν μ : Measure X) [IsFiniteMeasure ν] [SigmaFinite μ]
    (hAC : ν ≪ μ)
    (hRN : MemLp (fun x => (ν.rnDeriv μ x).toReal) 2 μ)
    {f : X → ℝ} (hfm : Measurable f) (hf : MemLp f 2 μ) :
    ‖∫ x, f x ∂ν‖ ≤ ‖hRN.toLp _‖ * ‖hf.toLp f‖ := by
  rw [integral_eq_integral_toReal_rnDeriv_mul ν μ hAC hfm,
    ← real_inner_toLp hRN hf]
  exact norm_inner_le_norm _ _

end CutoffRigidity
