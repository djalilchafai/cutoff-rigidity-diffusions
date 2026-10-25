module
public import CutoffRigidity.LangevinInverseLipschitz
public import Mathlib.Geometry.Euclidean.Volume.Measure

/-! # Actual localized flow volume distortion from inverse Lipschitz control

Hausdorff inverse-image control and its genuine Euclidean volume
normalization replace any unproved differentiable stochastic-flow Jacobian.
-/
public section
namespace CutoffRigidity
open MeasureTheory MeasureTheory.Measure Set Metric
open scoped ENNReal

/-- Actual inverse Lipschitz maps control normalized Euclidean Hausdorff
measure in every integer dimension. -/
theorem antilipschitz_euclideanHausdorffMeasure_preimage_le
    {X Y : Type*} [MetricSpace X] [MetricSpace Y]
    [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y] [BorelSpace Y]
    {f : X → Y} {K : NNReal} (hf : AntilipschitzWith K f) (d : ℕ) (A : Set Y) :
    euclideanHausdorffMeasure d (f ⁻¹' A) ≤ (K : ENNReal) ^ d * euclideanHausdorffMeasure d A := by
  have hh := hf.hausdorffMeasure_preimage_le (by positivity : (0 : ℝ) ≤ d) A
  rw [ENNReal.rpow_natCast] at hh
  simp only [euclideanHausdorffMeasure_def, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul]
  have hm := mul_le_mul_right hh
    (addHaarScalarFactor (volume : Measure (EuclideanSpace ℝ (Fin d))) (hausdorffMeasure d))
  convert! hm using 1
  ring

variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

/-- A genuinely inverse Lipschitz restriction gives the exact volume bound
on its full localized preimage, with no measurability premise on A. -/
theorem volume_localized_preimage_le_of_antilipschitz
    (f : E → E) (S A : Set E) {K : NNReal}
    (hf : AntilipschitzWith K (fun x : S => f x)) :
    volume (S ∩ f ⁻¹' A) ≤ (K : ENNReal) ^ d * volume A := by
  have hh := antilipschitz_euclideanHausdorffMeasure_preimage_le hf d A
  have hi := isometry_subtype_coe.euclideanHausdorffMeasure_image
    ((fun x : S => f x) ⁻¹' A) (d := d)
  have himage : (Subtype.val : S → E) '' ((fun x : S => f x) ⁻¹' A) = S ∩ f ⁻¹' A := by
    ext x
    constructor
    · rintro ⟨⟨y, hy⟩, ha, rfl⟩
      exact ⟨hy, ha⟩
    · rintro ⟨hx, ha⟩
      exact ⟨⟨x, hx⟩, ha, rfl⟩
  rw [himage, EuclideanSpace.euclideanHausdorffMeasure_eq_volume] at hi
  rw [← hi, EuclideanSpace.euclideanHausdorffMeasure_eq_volume] at hh
  exact hh

/-- Actual Langevin flow localized to trajectories staying in a fixed ball
has bounded volume distortion. The constant is derived from the C² potential. -/
theorem langevinSolution_localized_volume_bound
    {V : E → ℝ} (hV : ContDiff ℝ 2 V) (rate : ℝ) (hrate : 0 ≤ rate)
    (hHess : ∀ x z : E, rate * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z) (R : ℝ) :
    ∃ K : NNReal, ∀ (w : ℝ → E), Continuous w → ∀ (T : ℝ), 0 ≤ T → ∀ A : Set E,
      volume (langevinStayingSet V w T R ∩ (fun x => langevinSolution V w x T) ⁻¹' A) ≤
        (ENNReal.ofReal (Real.exp ((K : ℝ) * T))) ^ d * volume A := by
  obtain ⟨K, hK⟩ := langevinSolution_antilipschitz_stayingSet hV rate hrate hHess R
  refine ⟨K, fun w hw T hT A => ?_⟩
  have hh := volume_localized_preimage_le_of_antilipschitz
    (fun x => langevinSolution V w x T) (langevinStayingSet V w T R) A (hK w hw T hT)
  convert! hh using 1
  congr 2
  exact ENNReal.ofReal_eq_coe_nnreal (Real.exp_nonneg _)

/-- One fixed-horizon localization controls all earlier-time volume laws. -/
theorem langevinSolution_localized_volume_bound_uniform
    {V : E → ℝ} (hV : ContDiff ℝ 2 V) (rate : ℝ) (hrate : 0 ≤ rate)
    (hHess : ∀ x z : E, rate * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z) (R : ℝ) :
    ∃ K : NNReal, ∀ (w : ℝ → E), Continuous w → ∀ (T : ℝ), 0 ≤ T →
      ∀ s ∈ Icc 0 T, ∀ A : Set E,
      volume (langevinStayingSet V w T R ∩ (fun x => langevinSolution V w x s) ⁻¹' A) ≤
        (ENNReal.ofReal (Real.exp ((K : ℝ) * T))) ^ d * volume A := by
  obtain ⟨K, hK⟩ := langevinSolution_localized_volume_bound hV rate hrate hHess R
  refine ⟨K, fun w hw T hT s hs A => ?_⟩
  have hstay : langevinStayingSet V w T R ⊆ langevinStayingSet V w s R := by
    intro x hx r hr
    exact hx ⟨hr.1, hr.2.trans hs.2⟩
  have hfirst := (measure_mono (inter_subset_inter_left _ hstay)).trans (hK w hw s hs.1 A)
  have hex : ENNReal.ofReal (Real.exp ((K : ℝ) * s)) ≤ ENNReal.ofReal (Real.exp ((K : ℝ) * T)) :=
    ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hs.2 K.property))
  exact hfirst.trans (mul_le_mul_left (pow_le_pow_left' hex d) (volume A))

end CutoffRigidity
