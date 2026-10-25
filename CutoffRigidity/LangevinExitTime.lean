module
public import CutoffRigidity.ContinuousClosedHit
public import CutoffRigidity.LangevinHistoryFiltration
public import CutoffRigidity.LangevinSurvival

/-! # Actual bounded closed-ball exit times for Langevin history

Compact continuous path bundles make the finite-past hit event measurable
in the actual history sigma algebra. No right-continuity of the filtration
is assumed.
-/
public section
namespace CutoffRigidity
open MeasureTheory ProbabilityTheory Set Filter Topology
variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

@[expose] noncomputable def continuousLangevinPrefix
    {V : E → ℝ} (hV : ContDiff ℝ 2 V) (κ : ℝ) (hκ : 0 ≤ κ)
    (hHess : ∀ x z : E, κ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (C : Ω → C(ℝ, E)) (x₀ : E) (s : NNReal) (ω : Ω) : C(Icc 0 (s : ℝ), E) :=
  ⟨fun r => continuousLangevinVersion V C x₀ (⟨r, r.property.1⟩ : NNReal) ω,
    (continuousLangevinVersion_continuous hV κ hκ hHess C x₀ ω).comp
      (by fun_prop : Continuous (fun r : Icc 0 (s : ℝ) => (⟨r, r.property.1⟩ : NNReal)))⟩

theorem continuousLangevinPrefix_measurable_history
    {V : E → ℝ} (hV : ContDiff ℝ 2 V) (κ : ℝ) (hκ : 0 ≤ κ)
    (hHess : ∀ x z : E, κ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    {C : Ω → C(ℝ, E)} (hC : Measurable C) (x₀ : E) (s : NNReal) :
    Measurable[drivingHistoryFiltration hC s] (continuousLangevinPrefix hV κ hκ hHess C x₀ s) := by
  let ℱ := drivingHistoryFiltration hC
  have hA := continuousLangevinVersion_stronglyAdapted hV κ hκ hHess hC x₀
  let : MeasurableSpace Ω := ℱ s
  apply ContinuousMap.measurable_iff_eval.mpr
  intro r
  have hle : (⟨r, r.property.1⟩ : NNReal) ≤ s := r.property.2
  exact ((hA _).mono (ℱ.mono hle)).measurable

/-- A compact continuous path attains its norm, so closed-level hit events
are exactly threshold events for the genuine path-space norm. -/
theorem continuousMap_exists_norm_ge_iff
    {α F : Type*} [TopologicalSpace α] [CompactSpace α] [Nonempty α]
    [NormedAddCommGroup F] (f : C(α, F)) (R : ℝ) :
    (∃ t, R ≤ ‖f t‖) ↔ R ≤ ‖f‖ := by
  constructor
  · rintro ⟨t, ht⟩
    exact ht.trans (f.norm_coe_le_norm t)
  · intro hr
    obtain ⟨t, _, hmax⟩ := isCompact_univ.exists_isMaxOn Set.univ_nonempty f.continuous.norm.continuousOn
    have hnorm : ‖f‖ ≤ ‖f t‖ := (ContinuousMap.norm_le _ (norm_nonneg _)).mpr (fun r => hmax (mem_univ r))
    exact ⟨t, hr.trans hnorm⟩

@[expose] noncomputable def langevinExitTime
    (V : E → ℝ) (C : Ω → C(ℝ, E)) (x₀ : E) (R : ℝ) (T : NNReal) (ω : Ω) : NNReal :=
  cappedClosedHitTime (fun t => continuousLangevinVersion V C x₀ t ω) R T

omit [MeasurableSpace Ω] in
theorem langevin_hit_iff_prefix_norm
    {V : E → ℝ} (hV : ContDiff ℝ 2 V) (κ : ℝ) (hκ : 0 ≤ κ)
    (hHess : ∀ x z : E, κ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (C : Ω → C(ℝ, E)) (x₀ : E) (R : ℝ) (s : NNReal) (ω : Ω) :
    (∃ r : NNReal, r ≤ s ∧ R ≤ ‖continuousLangevinVersion V C x₀ r ω‖) ↔
      R ≤ ‖continuousLangevinPrefix hV κ hκ hHess C x₀ s ω‖ := by
  let : Nonempty (Icc 0 (s : ℝ)) := ⟨⟨0, ⟨le_rfl, s.property⟩⟩⟩
  rw [← continuousMap_exists_norm_ge_iff]
  constructor
  · rintro ⟨r, hrs, hr⟩
    exact ⟨⟨r, ⟨r.property, hrs⟩⟩, hr⟩
  · rintro ⟨r, hr⟩
    exact ⟨⟨r, r.property.1⟩, r.property.2, hr⟩

theorem langevinExitTime_isStoppingTime
    {V : E → ℝ} (hV : ContDiff ℝ 2 V) (κ : ℝ) (hκ : 0 ≤ κ)
    (hHess : ∀ x z : E, κ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    {C : Ω → C(ℝ, E)} (hC : Measurable C) (x₀ : E) (R : ℝ) (T : NNReal) :
    IsStoppingTime (drivingHistoryFiltration hC)
      (fun ω => (langevinExitTime V C x₀ R T ω : WithTop NNReal)) := by
  intro s
  by_cases hTs : T ≤ s
  · have heq : {ω | (langevinExitTime V C x₀ R T ω : WithTop NNReal) ≤ s} = univ := by
      ext ω
      simp only [mem_ofPred_eq, WithTop.coe_le_coe, mem_univ, iff_true]
      exact (cappedClosedHitTime_le_horizon _ R T).trans hTs
    rw [heq]
    exact MeasurableSet.univ
  · have heq : {ω | (langevinExitTime V C x₀ R T ω : WithTop NNReal) ≤ s} =
        {ω | R ≤ ‖continuousLangevinPrefix hV κ hκ hHess C x₀ s ω‖} := by
      ext ω
      simp only [mem_ofPred_eq, WithTop.coe_le_coe]
      rw [← langevin_hit_iff_prefix_norm hV κ hκ hHess C x₀ R s ω]
      rw [langevinExitTime, cappedClosedHitTime_le_iff (continuousLangevinVersion_continuous hV κ hκ hHess C x₀ ω)]
      constructor
      · rintro (hh | ⟨r, hrs, _, hr⟩)
        · exact False.elim (hTs hh)
        · exact ⟨r, hrs, hr⟩
      · rintro ⟨r, hrs, hr⟩
        exact Or.inr ⟨r, hrs, hrs.trans (le_of_not_ge hTs), hr⟩
    rw [heq]
    have hm := continuousLangevinPrefix_measurable_history hV κ hκ hHess hC x₀ s
    let : MeasurableSpace Ω := drivingHistoryFiltration hC s
    exact measurableSet_le measurable_const hm.norm

omit [MeasurableSpace Ω] in
theorem langevinExitTime_le_horizon
    (V : E → ℝ) (C : Ω → C(ℝ, E)) (x₀ : E) (R : ℝ) (T : NNReal) (ω : Ω) :
    langevinExitTime V C x₀ R T ω ≤ T := cappedClosedHitTime_le_horizon _ R T

omit [MeasurableSpace Ω] in
theorem norm_lt_before_langevinExitTime
    (V : E → ℝ) (C : Ω → C(ℝ, E)) (x₀ : E) (R : ℝ) (T t : NNReal) (ω : Ω)
    (ht : t < langevinExitTime V C x₀ R T ω) :
    ‖continuousLangevinVersion V C x₀ t ω‖ < R :=
  norm_lt_before_cappedClosedHitTime _ R T t ht

omit [MeasurableSpace Ω] in
/-- Starting in the closed localization ball, the entire path prefix up to
the capped hitting time remains in that closed ball. -/
theorem norm_le_before_or_at_langevinExitTime
    {V : E → ℝ} (hV : ContDiff ℝ 2 V) (κ : ℝ) (hκ : 0 ≤ κ)
    (hHess : ∀ x z : E, κ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (C : Ω → C(ℝ, E)) (x₀ : E) (R : ℝ) (hx₀ : ‖x₀‖ ≤ R)
    (T t : NNReal) (ω : Ω) (ht : t ≤ langevinExitTime V C x₀ R T ω) :
    ‖continuousLangevinVersion V C x₀ t ω‖ ≤ R := by
  rcases eq_or_lt_of_le ht with he | hl
  · rw [he]
    apply norm_le_at_cappedClosedHitTime
      (continuousLangevinVersion_continuous hV κ hκ hHess C x₀ ω)
    change ‖langevinSolution V (C ω) x₀ 0‖ ≤ R
    rw [langevinSolution_initial hV κ hκ hHess (C ω).continuous x₀]
    exact hx₀
  · exact (norm_lt_before_langevinExitTime V C x₀ R T t ω hl).le

@[expose] def langevinHitBy (V : E → ℝ) (C : Ω → C(ℝ, E)) (x₀ : E) (R : ℝ) (T : NNReal) : Set Ω :=
  {ω | ∃ r : NNReal, r ≤ T ∧ R ≤ ‖continuousLangevinVersion V C x₀ r ω‖}

theorem measurableSet_langevinHitBy
    {V : E → ℝ} (hV : ContDiff ℝ 2 V) (κ : ℝ) (hκ : 0 ≤ κ)
    (hHess : ∀ x z : E, κ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    {C : Ω → C(ℝ, E)} (hC : Measurable C) (x₀ : E) (R : ℝ) (T : NNReal) :
    MeasurableSet (langevinHitBy V C x₀ R T) := by
  have heq : langevinHitBy V C x₀ R T =
      {ω | R ≤ ‖continuousLangevinPrefix hV κ hκ hHess C x₀ T ω‖} := by
    ext ω
    exact langevin_hit_iff_prefix_norm hV κ hκ hHess C x₀ R T ω
  rw [heq]
  have hm := (continuousLangevinPrefix_measurable_history hV κ hκ hHess hC x₀ T).mono
    (drivingHistoryFiltration hC |>.le T) le_rfl
  exact measurableSet_le measurable_const hm.norm

/-- The genuine exit-by-T probability tends to zero as the radius diverges,
solely from actual sample-path boundedness on the compact time interval. -/
theorem langevinHitBy_measure_tendsto_zero
    {V : E → ℝ} (hV : ContDiff ℝ 2 V) (κ : ℝ) (hκ : 0 ≤ κ)
    (hHess : ∀ x z : E, κ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    {C : Ω → C(ℝ, E)} (hC : Measurable C) (x₀ : E) (T : NNReal)
    (P : Measure Ω) [IsFiniteMeasure P] :
    Tendsto (fun R : ℝ => P (langevinHitBy V C x₀ R T)) atTop (𝓝 0) := by
  have hanti : Antitone (fun R : ℝ => langevinHitBy V C x₀ R T) := by
    intro R S hRS ω hω
    obtain ⟨r, hr, hh⟩ := hω
    exact ⟨r, hr, hRS.trans hh⟩
  have hempty : (⋂ R : ℝ, langevinHitBy V C x₀ R T) = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro ω hω
    have hh := mem_iInter.mp hω (‖continuousLangevinPrefix hV κ hκ hHess C x₀ T ω‖ + 1)
    have hn := (langevin_hit_iff_prefix_norm hV κ hκ hHess C x₀ _ T ω).mp hh
    linarith
  have hh := tendsto_measure_iInter_atTop (μ := P)
    (fun R => (measurableSet_langevinHitBy hV κ hκ hHess hC x₀ R T).nullMeasurableSet)
    hanti ⟨0, measure_ne_top _ _⟩
  simpa only [hempty, measure_empty, Function.comp_def] using hh

omit [MeasurableSpace Ω] in
/-- Stopping inside the localization ball gives precisely the actual
prefix-survival event used in the killed occupation construction. -/
theorem langevin_survival_before_or_at_exit
    {V : E → ℝ} (hV : ContDiff ℝ 2 V) (κ : ℝ) (hκ : 0 ≤ κ)
    (hHess : ∀ x z : E, κ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (C : Ω → C(ℝ, E)) (x₀ : E) (R : ℝ) (hx₀ : ‖x₀‖ ≤ R)
    (T t : NNReal) (ω : Ω) (ht : t ≤ langevinExitTime V C x₀ R T ω) :
    ((t : ℝ), (x₀, C ω)) ∈ langevinSurvivalSet V R := by
  refine ⟨t.property, ?_⟩
  intro r hr
  have hn := norm_le_before_or_at_langevinExitTime hV κ hκ hHess C x₀ R hx₀ T
    (⟨r, hr.1⟩ : NNReal) ω ((show (⟨r, hr.1⟩ : NNReal) ≤ t from hr.2).trans ht)
  change ‖langevinSolution V (C ω) x₀ r‖ ≤ R at hn
  simpa only [Metric.mem_closedBall, dist_zero_right] using hn

omit [MeasurableSpace Ω] in
/-- Exiting strictly before the artificial terminal cap entails a genuine
closed-ball hit by the fixed horizon. -/
theorem langevinExitTime_strict_exit_subset_hit
    {V : E → ℝ} (hV : ContDiff ℝ 2 V) (κ : ℝ) (hκ : 0 ≤ κ)
    (hHess : ∀ x z : E, κ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (C : Ω → C(ℝ, E)) (x₀ : E) (R : ℝ) (T : NNReal) :
    {ω | langevinExitTime V C x₀ R T ω < T} ⊆ langevinHitBy V C x₀ R T := by
  intro ω hω
  exact cappedClosedHitTime_lt_implies_hit
    (continuousLangevinVersion_continuous hV κ hκ hHess C x₀ ω) R T hω

/-- In particular the actual boundary-error event for bounded stopping
vanishes as the localization radius tends to infinity. -/
theorem langevinExitTime_strict_exit_measure_tendsto_zero
    {V : E → ℝ} (hV : ContDiff ℝ 2 V) (κ : ℝ) (hκ : 0 ≤ κ)
    (hHess : ∀ x z : E, κ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    {C : Ω → C(ℝ, E)} (hC : Measurable C) (x₀ : E) (T : NNReal)
    (P : Measure Ω) [IsFiniteMeasure P] :
    Tendsto (fun R : ℝ => P {ω | langevinExitTime V C x₀ R T ω < T}) atTop (𝓝 0) := by
  apply tendsto_const_nhds.squeeze'
    (langevinHitBy_measure_tendsto_zero hV κ hκ hHess hC x₀ T P)
  · exact Filter.Eventually.of_forall (fun _ => zero_le)
  · exact Filter.Eventually.of_forall (fun R => measure_mono
      (langevinExitTime_strict_exit_subset_hit hV κ hκ hHess C x₀ R T))

omit [MeasurableSpace Ω] in
theorem langevinExitTime_le_iff
    {V : E → ℝ} (hV : ContDiff ℝ 2 V) (κ : ℝ) (hκ : 0 ≤ κ)
    (hHess : ∀ x z : E, κ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (C : Ω → C(ℝ, E)) (x₀ : E) (R : ℝ) (T s : NNReal) (ω : Ω) :
    langevinExitTime V C x₀ R T ω ≤ s ↔ T ≤ s ∨
      ∃ r : NNReal, r ≤ min s T ∧ R ≤ ‖continuousLangevinVersion V C x₀ r ω‖ := by
  unfold langevinExitTime
  simpa only [le_min_iff, and_assoc] using cappedClosedHitTime_le_iff
    (continuousLangevinVersion_continuous hV κ hκ hHess C x₀ ω) R T s

theorem langevinExitTime_measurable
    {V : E → ℝ} (hV : ContDiff ℝ 2 V) (κ : ℝ) (hκ : 0 ≤ κ)
    (hHess : ∀ x z : E, κ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    {C : Ω → C(ℝ, E)} (hC : Measurable C) (x₀ : E) (R : ℝ) (T : NNReal) :
    Measurable (langevinExitTime V C x₀ R T) := by
  apply measurable_of_Iic
  intro s
  have hh := langevinExitTime_isStoppingTime hV κ hκ hHess hC x₀ R T s
  have heq : {ω | (langevinExitTime V C x₀ R T ω : WithTop NNReal) ≤ s} =
      (langevinExitTime V C x₀ R T) ⁻¹' Iic s := by
    ext ω
    exact WithTop.coe_le_coe
  rw [heq] at hh
  exact (drivingHistoryFiltration hC |>.le s) _ hh

end CutoffRigidity
