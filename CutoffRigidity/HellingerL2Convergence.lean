module
public import CutoffRigidity.RelativeFisherInformation

/-! # Genuine RN-root L² convergence from density L¹ convergence

The pointwise square-root/Hellinger inequality controls actual L² norms
of actual Radon--Nikodym square-root classes by actual L¹ density errors.
-/
public section
namespace CutoffRigidity
open MeasureTheory Filter Set
open scoped ENNReal Topology

/-- The elementary Hellinger inequality, including zero endpoints. -/
theorem sq_sqrt_sub_sqrt_le_abs_sub {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (Real.sqrt a - Real.sqrt b) ^ 2 ≤ |a - b| := by
  rcases le_total a b with hab | hba
  · rw [abs_of_nonpos (sub_nonpos.mpr hab)]
    have hs := Real.sqrt_le_sqrt hab
    have hh := mul_nonneg (Real.sqrt_nonneg a) (sub_nonneg.mpr hs)
    nlinarith [Real.sq_sqrt ha, Real.sq_sqrt hb]
  · rw [abs_of_nonneg (sub_nonneg.mpr hba)]
    have hs := Real.sqrt_le_sqrt hba
    have hh := mul_nonneg (Real.sqrt_nonneg b) (sub_nonneg.mpr hs)
    nlinarith [Real.sq_sqrt ha, Real.sq_sqrt hb]

/-- Actual finite RN densities are integrable under the reference law. -/
theorem integrable_toReal_rnDeriv_finite {X : Type*} [MeasurableSpace X]
    (ν μ : Measure X) [IsFiniteMeasure ν] : Integrable (fun x => (ν.rnDeriv μ x).toReal) μ := by
  simpa only [integrableOn_univ] using
    (Measure.integrableOn_toReal_rnDeriv (μ := ν) (ν := μ) (s := Set.univ) (measure_ne_top ν _))

/-- The true L² RN-root distance is bounded by the true L¹ density error. -/
theorem norm_squareRootRNDensityLp_sub_sq_le {X : Type*} [MeasurableSpace X]
    (ν η μ : Measure X) [IsFiniteMeasure ν] [IsFiniteMeasure η] :
    ‖squareRootRNDensityLp ν μ - squareRootRNDensityLp η μ‖ ^ 2 ≤
      ∫ x, |(ν.rnDeriv μ x).toReal - (η.rnDeriv μ x).toReal| ∂μ := by
  have hi : Integrable (fun x => (squareRootRNDensity ν μ x - squareRootRNDensity η μ x) ^ 2) μ := by
    simpa only [Pi.sub_apply] using
      ((squareRootRNDensity_memLp ν μ).sub (squareRootRNDensity_memLp η μ)).integrable_sq
  have hRn : Integrable (fun x => |(ν.rnDeriv μ x).toReal - (η.rnDeriv μ x).toReal|) μ :=
    ((integrable_toReal_rnDeriv_finite ν μ).sub (integrable_toReal_rnDeriv_finite η μ)).abs
  have hEq : ‖squareRootRNDensityLp ν μ - squareRootRNDensityLp η μ‖ ^ 2 =
      ∫ x, (squareRootRNDensity ν μ x - squareRootRNDensity η μ x) ^ 2 ∂μ := by
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub (squareRootRNDensityLp ν μ) (squareRootRNDensityLp η μ),
      (squareRootRNDensity_memLp ν μ).coeFn_toLp, (squareRootRNDensity_memLp η μ).coeFn_toLp] with x hsub hx hy
    have hx' : (squareRootRNDensityLp ν μ : X → ℝ) x = squareRootRNDensity ν μ x := by convert! hx using 1
    have hy' : (squareRootRNDensityLp η μ : X → ℝ) x = squareRootRNDensity η μ x := by convert! hy using 1
    rw [hsub, Pi.sub_apply, hx', hy', Real.inner_apply]
    ring
  rw [hEq]
  apply integral_mono hi hRn
  intro x
  exact sq_sqrt_sub_sqrt_le_abs_sub ENNReal.toReal_nonneg ENNReal.toReal_nonneg

/-- Genuine strong L² convergence of actual RN roots follows from genuine
L¹ convergence of the actual finite RN densities. -/
theorem tendsto_squareRootRNDensityLp_of_L1_rnDeriv
    {X : Type*} [MeasurableSpace X] (μ ν : Measure X) [IsFiniteMeasure ν]
    (νn : ℕ → Measure X) [∀ n, IsFiniteMeasure (νn n)]
    (hlim : Tendsto (fun n => ∫ x,
      |((νn n).rnDeriv μ x).toReal - (ν.rnDeriv μ x).toReal| ∂μ) atTop (𝓝 0)) :
    Tendsto (fun n => squareRootRNDensityLp (νn n) μ) atTop (𝓝 (squareRootRNDensityLp ν μ)) := by
  have hsq : Tendsto (fun n => ‖squareRootRNDensityLp (νn n) μ - squareRootRNDensityLp ν μ‖ ^ 2)
      atTop (𝓝 0) := squeeze_zero (fun n => sq_nonneg _)
    (fun n => norm_squareRootRNDensityLp_sub_sq_le (νn n) ν μ) hlim
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hh := Real.continuous_sqrt.continuousAt.tendsto.comp hsq
  simpa only [Function.comp_def, Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] using hh

end CutoffRigidity
