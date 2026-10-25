module

public import CutoffRigidity.LangevinMovingCompensator
public import Mathlib.Analysis.Calculus.Deriv.Shift

/-! # Shifted genuine space-time Dynkin identities

A bounded continuous source curve is required to equal the actual time
plus spatial generator of the compact smooth test. The identity follows
from the proved moving-test generator differentiation and FTC; it is not
an input field.
-/

public section

namespace CutoffRigidity

open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal BoundedContinuousFunction

variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

/-- The genuine space-time identity on an arbitrary forward time interval. -/
theorem langevinKernel_shifted_spacetime_dynkin
    {B : NNReal → Ω → E} {P : Measure Ω} (hB : IsEuclideanBrownian B P)
    {V : E → ℝ} (hV : ContDiff ℝ 2 V) (κ : ℝ) (hκ : 0 ≤ κ)
    (hHess : ∀ x z : E, κ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (q q' g : ℝ → E →ᵇ ℝ) (hqcont : Continuous q) (hgcont : Continuous g)
    (s t : ℝ) (ht : 0 ≤ t)
    (hq : ∀ r ∈ Ioo s (s + t), HasDerivAt q (q' r) r)
    (hqs : ∀ r ∈ Ioo s (s + t), ContDiff ℝ 2 (q r))
    (hqsc : ∀ r ∈ Ioo s (s + t), HasCompactSupport (q r))
    (hsource : ∀ r x, g r x = q' r x + langevinDifferentialOperator V (q r) x)
    (x : E) :
    (∫ y, q (s + t) y ∂langevinKernel V B P t.toNNReal x) = q s x +
      ∫ r in 0..t, ∫ y, g (s + r) y ∂langevinKernel V B P r.toNNReal x := by
  have hi (r : ℝ) : (∫ y, q' (s + r) y ∂langevinKernel V B P r.toNNReal x) +
      (∫ y, langevinDifferentialOperator V (q (s + r)) y
        ∂langevinKernel V B P r.toNNReal x) =
      ∫ y, g (s + r) y ∂langevinKernel V B P r.toNNReal x := by
    let := langevinKernel_isMarkovKernel hB hV κ hκ hHess r.toNNReal
    have hL : langevinDifferentialOperator V (q (s + r)) =
        fun y => g (s + r) y - q' (s + r) y := by
      funext y
      have hh := hsource (s + r) y
      linarith
    have hLi : Integrable (langevinDifferentialOperator V (q (s + r)))
        (langevinKernel V B P r.toNNReal x) := by
      rw [hL]
      exact ((g (s + r)).integrable _).sub ((q' (s + r)).integrable _)
    rw [← integral_add ((q' (s + r)).integrable _) hLi]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun y => (hsource (s + r) y).symm)
  have hgc : Continuous (fun r : ℝ => ∫ y, g (s + r) y
      ∂langevinKernel V B P r.toNNReal x) := by
    apply continuous_iff_continuousAt.mpr
    intro r
    exact tendsto_langevinKernel_integral_varying_bounded_test hB hV κ hκ hHess
      ((hgcont.comp (continuous_const.add continuous_id)).tendsto r)
      (continuous_real_toNNReal.tendsto r) x
  have hmem (r : ℝ) (hr : r ∈ Ioo (0 : ℝ) t) :
      s + r ∈ Ioo s (s + t) := by
    constructor
    · exact lt_add_of_pos_right s hr.1
    · simpa only [add_comm] using add_lt_add_left hr.2 s
  have hder (r : ℝ) (hr : r ∈ Ioo (0 : ℝ) t) :
      HasDerivAt (fun z : ℝ => q (s + z)) (q' (s + r)) r := by
    exact (hq _ (hmem r hr)).comp_const_add s r
  have hh := langevinKernel_spacetime_dynkin_identity hB hV κ hκ hHess
    (fun r => q (s + r)) (fun r => q' (s + r)) x ht
    (hqcont.comp (continuous_const.add continuous_id)).continuousOn
    hder
    (fun r hr => hqs _ (hmem r hr))
    (fun r hr => hqsc _ (hmem r hr))
    (by
      convert! hgc.intervalIntegrable (μ := (volume : Measure ℝ)) 0 t using 1
      funext r
      exact hi r)
  simp_rw [hi] at hh
  simpa only [add_zero] using hh

end CutoffRigidity
