module

public import CutoffRigidity.ContinuousOptionalExpectation
public import CutoffRigidity.LangevinDynkinMartingale

/-! # Genuine compact-test Dynkin expectation at bounded stopping times

The actual continuous Langevin Dynkin martingale is uniformly bounded on
each finite time interval. The proved continuous optional-expectation
argument therefore applies to every actual bounded stopping time of the
noise-history filtration. No stopping identity is assumed.
-/

public section

namespace CutoffRigidity

open MeasureTheory Set Filter Topology

variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

omit [MeasurableSpace Ω] in
/-- Compact tests give an actual deterministic bound on the compensated
functional on each bounded time interval. -/
theorem langevinDynkinProcess_bounded {V f : E → ℝ}
    (hV : ContDiff ℝ 2 V) (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (C : Ω → C(ℝ, E)) (x₀ : E) (T : NNReal) :
    ∃ K : ℝ, ∀ t ≤ T, ∀ ω, ‖langevinDynkinProcess V f C x₀ t ω‖ ≤ K := by
  obtain ⟨N, hN0, hN⟩ := compact_continuous_norm_bound hf.continuous hfc
  obtain ⟨M, hM0, hM⟩ := compact_continuous_norm_bound (continuous_langevinDifferentialOperator hV hf)
    (hasCompactSupport_langevinDifferentialOperator V hfc)
  refine ⟨2 * N + M * T, ?_⟩
  intro t ht ω
  have hi : ‖∫ r in 0..(t : ℝ), langevinDifferentialOperator V f
      (continuousLangevinVersion V C x₀ r.toNNReal ω)‖ ≤ M * t := by
    have hh := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := 0) (b := (t : ℝ)) (fun r _ => hM (continuousLangevinVersion V C x₀ r.toNNReal ω))
    simp only [sub_zero] at hh
    convert! hh using 1
    congr 1
    exact (abs_of_nonneg t.property).symm
  have hb := norm_sub_le (f (continuousLangevinVersion V C x₀ t ω) - f x₀)
    (∫ r in 0..(t : ℝ), langevinDifferentialOperator V f (continuousLangevinVersion V C x₀ r.toNNReal ω))
  have hbf := norm_sub_le (f (continuousLangevinVersion V C x₀ t ω)) (f x₀)
  have htt : (t : ℝ) ≤ T := ht
  change ‖f (continuousLangevinVersion V C x₀ t ω) - f x₀ - _‖ ≤ _
  nlinarith [hN (continuousLangevinVersion V C x₀ t ω), hN x₀]

/-- The actual compact-test compensated functional has mean zero at every
bounded stopping time of its actual driving-history filtration. -/
theorem langevinDynkinProcess_integral_stopping_time
    {B : NNReal → Ω → E} {P : Measure Ω} (hB : IsEuclideanBrownian B P)
    {V f : E → ℝ} (hV : ContDiff ℝ 2 V) (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (κ : ℝ) (hκ : 0 ≤ κ)
    (hHess : ∀ x z, κ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (x₀ : E) {C : Ω → C(ℝ, E)} (hC : Measurable C)
    (hCeq : ∀ᵐ ω ∂P, ∀ r : ℝ, C ω r = brownianDrivingPath B ω r)
    (T : NNReal) {τ : Ω → NNReal}
    (hτ : IsStoppingTime (drivingHistoryFiltration hC) (fun ω => (τ ω : WithTop NNReal)))
    (hτT : ∀ ω, τ ω ≤ T) :
    (∫ ω, langevinDynkinProcess V f C x₀ (τ ω) ω ∂P) = 0 := by
  have := hB.isProbabilityMeasure
  obtain ⟨K, hK⟩ := langevinDynkinProcess_bounded hV hf hfc C x₀ (T + 1)
  have he := integral_martingale_at_bounded_stopping_time (drivingHistoryFiltration hC)
    (langevinDynkinProcess_martingale hB hV hf hfc κ hκ hHess x₀ hC hCeq)
    (langevinDynkinProcess_continuous hV hf κ hκ hHess C x₀) T hτ hτT K hK
  rw [he]
  have hz (ω : Ω) : langevinDynkinProcess V f C x₀ 0 ω = 0 := by
    have hinit := langevinSolution_initial hV κ hκ hHess (C ω).continuous x₀
    change f (langevinSolution V (C ω) x₀ 0) - f x₀ - (∫ r in (0 : ℝ)..0, _) = 0
    rw [hinit]
    simp
  simp only [hz, integral_zero]

end CutoffRigidity
