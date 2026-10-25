module

public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Integral.Prod

/-! # Genuine pointwise representatives of bounded L² time integrals

Scalar Fubini and Hilbert duality identify the actual Bochner L² integral
with the integral of bounded jointly measurable representatives. The
almost-everywhere representatives need agree separately at each time only.
-/

public section

namespace CutoffRigidity

open MeasureTheory Filter

/-- A bounded jointly measurable representative may be integrated before
or after forming the genuine L² time integral. -/
theorem coeFn_integral_L2_of_bounded
    {J X : Type*} [MeasurableSpace J] [MeasurableSpace X]
    (η : Measure J) [IsFiniteMeasure η] (μ : Measure X) [IsProbabilityMeasure μ]
    (u : J → X →₂[μ] ℝ) (hu : Integrable u η) (F : J → X → ℝ)
    (hF : StronglyMeasurable (Function.uncurry F)) (M : ℝ) (hM : 0 ≤ M)
    (hb : ∀ s x, ‖F s x‖ ≤ M) (hrep : ∀ s, u s =ᵐ[μ] F s) :
    (∫ s, u s ∂η : X →₂[μ] ℝ) =ᵐ[μ] fun x => ∫ s, F s x ∂η := by
  let W : X → ℝ := fun x => ∫ s, F s x ∂η
  have hW : MemLp W 2 μ := by
    apply MemLp.of_bound hF.integral_prod_left.aestronglyMeasurable (M * η.real Set.univ)
    exact Filter.Eventually.of_forall (fun x => norm_integral_le_of_norm_le_const
      (Filter.Eventually.of_forall (fun s => hb s x)))
  have he : (∫ s, u s ∂η) = hW.toLp W := by
    apply ext_inner_left ℝ
    intro v
    have hv : Integrable (fun x => ‖v x‖) μ := ((Lp.memLp v).integrable (by norm_num)).norm
    have hInt : Integrable (fun p : J × X => v p.2 * F p.1 p.2) (η.prod μ) := by
      apply ((hv.comp_snd η).const_mul M).mono'
        ((Lp.stronglyMeasurable v).comp_measurable measurable_snd |>.mul hF).aestronglyMeasurable
      filter_upwards with p
      change ‖v p.2 * F p.1 p.2‖ ≤ M * ‖v p.2‖
      rw [norm_mul, Real.norm_eq_abs (v p.2)]
      have hh := mul_le_mul_of_nonneg_left (hb p.1 p.2) (abs_nonneg (v p.2))
      simpa only [mul_comm] using hh
    have hinner (s : J) : inner ℝ v (u s) = ∫ x, v x * F s x ∂μ := by
      rw [L2.inner_def]
      apply integral_congr_ae
      filter_upwards [hrep s] with x hx
      rw [hx, Real.inner_apply]
    calc
      inner ℝ v (∫ s, u s ∂η) = ∫ s, inner ℝ v (u s) ∂η := (integral_inner hu v).symm
      _ = ∫ s, ∫ x, v x * F s x ∂μ ∂η := integral_congr_ae (Filter.Eventually.of_forall hinner)
      _ = ∫ x, ∫ s, v x * F s x ∂η ∂μ := integral_integral_swap hInt
      _ = ∫ x, v x * W x ∂μ := by simp only [integral_const_mul, W]
      _ = inner ℝ v (hW.toLp W) := by
        rw [L2.inner_def]
        apply integral_congr_ae
        filter_upwards [hW.coeFn_toLp] with x hx
        rw [hx, Real.inner_apply]
  rw [he]
  exact hW.coeFn_toLp

end CutoffRigidity
