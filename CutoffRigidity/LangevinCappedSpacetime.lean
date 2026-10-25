module

public import CutoffRigidity.LangevinSpacetimeMartingale

/-! # Genuine space-time martingales on a bounded horizon

The test equation is required only before the chosen horizon. Stopping the
actual compensated process at the deterministic horizon gives a genuine
martingale for all nonnegative times. No extension of a backward heat
solution beyond its terminal time is assumed.
-/

public section

namespace CutoffRigidity

open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal BoundedContinuousFunction

variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

/-- The actual moving compensated process stopped at a deterministic horizon. -/
@[expose] noncomputable def langevinCappedSpacetimeDynkinProcess (V : E → ℝ)
    (q g : ℝ → E →ᵇ ℝ) (C : Ω → C(ℝ, E)) (x₀ : E) (T t : NNReal) : Ω → ℝ :=
  langevinSpacetimeDynkinProcess V q g C x₀ (min t T)

/-- Genuine finite-horizon space-time Dynkin martingale. The differential
and compact spatial test conditions are imposed only on (0,T). -/
theorem langevinCappedSpacetimeDynkinProcess_martingale
    {B : NNReal → Ω → E} {P : Measure Ω} (hB : IsEuclideanBrownian B P)
    {V : E → ℝ} (hV : ContDiff ℝ 2 V) (κ : ℝ) (hκ : 0 ≤ κ)
    (hHess : ∀ x z : E, κ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (q q' g : ℝ → E →ᵇ ℝ) (hqcont : Continuous q) (hgcont : Continuous g)
    (hgb : ∃ M : ℝ, ∀ r x, ‖g r x‖ ≤ M) (x₀ : E) (T : NNReal)
    (hq : ∀ r ∈ Ioo (0 : ℝ) (T : ℝ), HasDerivAt q (q' r) r)
    (hqs : ∀ r ∈ Ioo (0 : ℝ) (T : ℝ), ContDiff ℝ 2 (q r))
    (hqsc : ∀ r ∈ Ioo (0 : ℝ) (T : ℝ), HasCompactSupport (q r))
    (hsource : ∀ r x, g r x = q' r x + langevinDifferentialOperator V (q r) x)
    {C : Ω → C(ℝ, E)} (hC : Measurable C)
    (hCeq : ∀ᵐ ω ∂P, ∀ r : ℝ, C ω r = brownianDrivingPath B ω r) :
    Martingale (langevinCappedSpacetimeDynkinProcess V q g C x₀ T)
      (drivingHistoryFiltration hC) P := by
  have := hB.isProbabilityMeasure
  have hadapt := langevinSpacetimeDynkinProcess_stronglyAdapted hV q g hgcont κ hκ hHess hC x₀
  refine ⟨fun t => (hadapt (min t T)).mono ((drivingHistoryFiltration hC).mono (min_le_left t T)), ?_⟩
  intro s t hst
  by_cases hs : s ≤ T
  · have hsb : s ≤ min t T := le_min hst hs
    have hsum : s + (min t T - s) = min t T := add_tsub_cancel_of_le hsb
    have hend : (s : ℝ) + ((min t T - s : NNReal) : ℝ) = (min t T : NNReal) := by
      simpa only [NNReal.coe_add] using congrArg (fun v : NNReal => (v : ℝ)) hsum
    have hmem (r : ℝ) (hr : r ∈ Ioo (s : ℝ) ((s : ℝ) + (min t T - s : NNReal))) :
        r ∈ Ioo (0 : ℝ) (T : ℝ) := by
      refine ⟨s.property.trans_lt hr.1, ?_⟩
      rw [hend] at hr
      exact hr.2.trans_le (show ((min t T : NNReal) : ℝ) ≤ T from min_le_right t T)
    have hh := langevinSpacetimeDynkinProcess_condExp_add hB hV κ hκ hHess q q' g
      hqcont hgcont hgb x₀ s (min t T - s)
      (fun r hr => hq r (hmem r hr)) (fun r hr => hqs r (hmem r hr))
      (fun r hr => hqsc r (hmem r hr)) hsource hC hCeq
    simpa only [langevinCappedSpacetimeDynkinProcess, min_eq_left hs, hsum] using hh
  · have hTs : T ≤ s := (lt_of_not_ge hs).le
    have hTt : T ≤ t := hTs.trans hst
    have hm := (hadapt T).mono ((drivingHistoryFiltration hC).mono hTs)
    have hi := langevinSpacetimeDynkinProcess_integrable (P := P) hV q g hgcont hgb κ hκ hHess hC x₀ T
    have hh := condExp_of_stronglyMeasurable ((drivingHistoryFiltration hC).le s) hm hi
    change P[langevinSpacetimeDynkinProcess V q g C x₀ (min t T) |
      drivingHistoryFiltration hC s] =ᵐ[P] langevinSpacetimeDynkinProcess V q g C x₀ (min s T)
    rw [min_eq_right hTs, min_eq_right hTt]
    exact Filter.EventuallyEq.of_eq hh

omit [MeasurableSpace Ω] in
/-- The capped moving functional has a genuine deterministic uniform bound. -/
theorem langevinCappedSpacetimeDynkinProcess_bounded
    (V : E → ℝ) (q g : ℝ → E →ᵇ ℝ) (hq : Continuous q)
    (hgb : ∃ M : ℝ, ∀ r x, ‖g r x‖ ≤ M)
    (C : Ω → C(ℝ, E)) (x₀ : E) (T : NNReal) :
    ∃ K : ℝ, ∀ t ω, ‖langevinCappedSpacetimeDynkinProcess V q g C x₀ T t ω‖ ≤ K := by
  obtain ⟨N,hN⟩ := (isCompact_Icc : IsCompact (Icc (0 : ℝ) (T : ℝ))).exists_bound_of_continuousOn hq.continuousOn
  obtain ⟨M,hM⟩ := hgb
  have hM0 : 0 ≤ M := (norm_nonneg (g 0 (0 : E))).trans (hM 0 0)
  refine ⟨N + ‖q 0 x₀‖ + M * T, ?_⟩
  intro t ω
  let v := min t T
  have hv : (v : ℝ) ∈ Icc (0 : ℝ) (T : ℝ) := ⟨v.property, min_le_right t T⟩
  have hval : ‖q v (continuousLangevinVersion V C x₀ v ω)‖ ≤ N :=
    ((q v).norm_coe_le_norm _).trans (hN _ hv)
  have hi : ‖∫ r in 0..(v : ℝ), g r (continuousLangevinVersion V C x₀ r.toNNReal ω)‖ ≤ M * v := by
    have hh := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := 0) (b := (v : ℝ)) (fun r _ => hM r (continuousLangevinVersion V C x₀ r.toNNReal ω))
    simp only [sub_zero] at hh
    convert! hh using 1
    congr 1
    exact (abs_of_nonneg v.property).symm
  have hb := norm_sub_le (q v (continuousLangevinVersion V C x₀ v ω) - q 0 x₀)
    (∫ r in 0..(v : ℝ), g r (continuousLangevinVersion V C x₀ r.toNNReal ω))
  have hb' := norm_sub_le (q v (continuousLangevinVersion V C x₀ v ω)) (q 0 x₀)
  change ‖q v (continuousLangevinVersion V C x₀ v ω) - q 0 x₀ - _‖ ≤ _
  nlinarith [mul_le_mul_of_nonneg_left hv.2 hM0]

/-- True stopped space-time Dynkin expectation on a finite horizon. The
moving test equation is required only before the terminal time. -/
theorem langevinSpacetimeDynkinProcess_integral_stopping_time
    {B : NNReal → Ω → E} {P : Measure Ω} (hB : IsEuclideanBrownian B P)
    {V : E → ℝ} (hV : ContDiff ℝ 2 V) (κ : ℝ) (hκ : 0 ≤ κ)
    (hHess : ∀ x z : E, κ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (q q' g : ℝ → E →ᵇ ℝ) (hqcont : Continuous q) (hgcont : Continuous g)
    (hgb : ∃ M : ℝ, ∀ r x, ‖g r x‖ ≤ M) (x₀ : E) (T : NNReal)
    (hq : ∀ r ∈ Ioo (0 : ℝ) (T : ℝ), HasDerivAt q (q' r) r)
    (hqs : ∀ r ∈ Ioo (0 : ℝ) (T : ℝ), ContDiff ℝ 2 (q r))
    (hqsc : ∀ r ∈ Ioo (0 : ℝ) (T : ℝ), HasCompactSupport (q r))
    (hsource : ∀ r x, g r x = q' r x + langevinDifferentialOperator V (q r) x)
    {C : Ω → C(ℝ, E)} (hC : Measurable C)
    (hCeq : ∀ᵐ ω ∂P, ∀ r : ℝ, C ω r = brownianDrivingPath B ω r)
    {τ : Ω → NNReal}
    (hτ : IsStoppingTime (drivingHistoryFiltration hC) (fun ω => (τ ω : WithTop NNReal)))
    (hτT : ∀ ω, τ ω ≤ T) :
    (∫ ω, langevinSpacetimeDynkinProcess V q g C x₀ (τ ω) ω ∂P) = 0 := by
  have := hB.isProbabilityMeasure
  obtain ⟨K,hK⟩ := langevinCappedSpacetimeDynkinProcess_bounded V q g hqcont hgb C x₀ T
  have hm := langevinCappedSpacetimeDynkinProcess_martingale hB hV κ hκ hHess
    q q' g hqcont hgcont hgb x₀ T hq hqs hqsc hsource hC hCeq
  have hc (ω : Ω) : Continuous (fun t => langevinCappedSpacetimeDynkinProcess V q g C x₀ T t ω) :=
    (langevinSpacetimeDynkinProcess_continuous hV q g hqcont hgcont κ hκ hHess C x₀ ω).comp
      (continuous_id.min continuous_const)
  have he := integral_martingale_at_bounded_stopping_time (drivingHistoryFiltration hC)
    hm hc T hτ hτT K (fun t _ ω => hK t ω)
  have hcap (ω : Ω) : langevinCappedSpacetimeDynkinProcess V q g C x₀ T (τ ω) ω =
      langevinSpacetimeDynkinProcess V q g C x₀ (τ ω) ω := by
    unfold langevinCappedSpacetimeDynkinProcess
    rw [min_eq_left (hτT ω)]
  have hz (ω : Ω) : langevinCappedSpacetimeDynkinProcess V q g C x₀ T 0 ω = 0 := by
    have hinit := langevinSolution_initial hV κ hκ hHess (C ω).continuous x₀
    unfold langevinCappedSpacetimeDynkinProcess
    rw [min_eq_left (show (0 : NNReal) ≤ T from T.property)]
    change q 0 (langevinSolution V (C ω) x₀ 0) - q 0 x₀ - (∫ r in (0 : ℝ)..0, _) = 0
    rw [hinit]
    simp
  simpa only [hcap, hz, integral_zero] using he

end CutoffRigidity
