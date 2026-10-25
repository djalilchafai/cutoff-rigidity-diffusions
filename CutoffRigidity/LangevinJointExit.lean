module
public import CutoffRigidity.LangevinExitTime
public import CutoffRigidity.LangevinGibbsOccupation

/-! # Joint initial-state/noise exit measurability and finite-product tails -/
public section
namespace CutoffRigidity
open MeasureTheory ProbabilityTheory Set Filter Topology
variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

@[expose] noncomputable def initialNoiseLangevinPrefix
    {V : E → ℝ} (hV : ContDiff ℝ 2 V) (κ : ℝ) (hκ : 0 ≤ κ)
    (hHess : ∀ x z : E, κ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (s : NNReal) (p : E × C(ℝ, E)) : C(Icc 0 (s : ℝ), E) :=
  ⟨fun r => langevinSolution V p.2 p.1 r,
    (langevinSolution_continuousOn hV κ hκ hHess p.2.continuous p.1).comp_continuous
      continuous_subtype_val (fun r => r.property.1)⟩

theorem initialNoiseLangevinPrefix_measurable
    {V : E → ℝ} (hV : ContDiff ℝ 2 V) (κ : ℝ) (hκ : 0 ≤ κ)
    (hHess : ∀ x z : E, κ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z) (s : NNReal) :
    Measurable (initialNoiseLangevinPrefix hV κ hκ hHess s) := by
  apply ContinuousMap.measurable_iff_eval.mpr
  intro r
  exact (langevinSolution_evaluation_continuous hV κ hκ hHess r.property.1).measurable

@[expose] noncomputable def initialNoiseLangevinExitTime
    (V : E → ℝ) (R : ℝ) (T : NNReal) (p : E × C(ℝ, E)) : NNReal :=
  cappedClosedHitTime (fun t : NNReal => langevinSolution V p.2 p.1 t) R T

theorem initialNoiseLangevin_hit_iff_prefix_norm
    {V : E → ℝ} (hV : ContDiff ℝ 2 V) (κ : ℝ) (hκ : 0 ≤ κ)
    (hHess : ∀ x z : E, κ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (R : ℝ) (s : NNReal) (p : E × C(ℝ, E)) :
    (∃ r : NNReal, r ≤ s ∧ R ≤ ‖langevinSolution V p.2 p.1 r‖) ↔
      R ≤ ‖initialNoiseLangevinPrefix hV κ hκ hHess s p‖ := by
  let : Nonempty (Icc 0 (s : ℝ)) := ⟨⟨0, ⟨le_rfl, s.property⟩⟩⟩
  rw [← continuousMap_exists_norm_ge_iff]
  constructor
  · rintro ⟨r, hrs, hr⟩
    exact ⟨⟨r, ⟨r.property, hrs⟩⟩, hr⟩
  · rintro ⟨r, hr⟩
    exact ⟨⟨r, r.property.1⟩, r.property.2, hr⟩

theorem initialNoiseLangevinExitTime_measurable
    {V : E → ℝ} (hV : ContDiff ℝ 2 V) (κ : ℝ) (hκ : 0 ≤ κ)
    (hHess : ∀ x z : E, κ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (R : ℝ) (T : NNReal) : Measurable (initialNoiseLangevinExitTime V R T) := by
  apply measurable_of_Iic
  intro s
  by_cases hTs : T ≤ s
  · have heq : (initialNoiseLangevinExitTime V R T) ⁻¹' Iic s = univ := by
      ext p
      exact iff_true_intro ((cappedClosedHitTime_le_horizon _ R T).trans hTs)
    rw [heq]
    exact MeasurableSet.univ
  · have heq : (initialNoiseLangevinExitTime V R T) ⁻¹' Iic s =
        {p | R ≤ ‖initialNoiseLangevinPrefix hV κ hκ hHess s p‖} := by
      ext p
      change cappedClosedHitTime (fun t : NNReal => langevinSolution V p.2 p.1 t) R T ≤ s ↔
        R ≤ ‖initialNoiseLangevinPrefix hV κ hκ hHess s p‖
      have hcont : Continuous (fun t : NNReal => langevinSolution V p.2 p.1 t) :=
        (langevinSolution_continuousOn hV κ hκ hHess p.2.continuous p.1).comp_continuous
          NNReal.continuous_coe (fun t => t.property)
      rw [← initialNoiseLangevin_hit_iff_prefix_norm hV κ hκ hHess R s p, cappedClosedHitTime_le_iff hcont]
      constructor
      · rintro (hh | ⟨r, hrs, _, hr⟩)
        · exact False.elim (hTs hh)
        · exact ⟨r, hrs, hr⟩
      · rintro ⟨r, hrs, hr⟩
        exact Or.inr ⟨r, hrs, hrs.trans (le_of_not_ge hTs), hr⟩
    rw [heq]
    exact measurableSet_le measurable_const (initialNoiseLangevinPrefix_measurable hV κ hκ hHess s).norm

variable {Ω : Type*} [MeasurableSpace Ω]

theorem langevinExitTime_jointly_measurable_initial
    {V : E → ℝ} (hV : ContDiff ℝ 2 V) (κ : ℝ) (hκ : 0 ≤ κ)
    (hHess : ∀ x z : E, κ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    {C : Ω → C(ℝ, E)} (hC : Measurable C) (R : ℝ) (T : NNReal) :
    Measurable (fun p : E × Ω => langevinExitTime V C p.1 R T p.2) :=
  (initialNoiseLangevinExitTime_measurable hV κ hκ hHess R T).comp
    (measurable_fst.prodMk (hC.comp measurable_snd))

@[expose] def langevinJointHitBy
    (V : E → ℝ) (C : Ω → C(ℝ, E)) (R : ℝ) (T : NNReal) : Set (E × Ω) :=
  {p | ∃ r : NNReal, r ≤ T ∧ R ≤ ‖continuousLangevinVersion V C p.1 r p.2‖}

theorem measurableSet_langevinJointHitBy
    {V : E → ℝ} (hV : ContDiff ℝ 2 V) (κ : ℝ) (hκ : 0 ≤ κ)
    (hHess : ∀ x z : E, κ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    {C : Ω → C(ℝ, E)} (hC : Measurable C) (R : ℝ) (T : NNReal) :
    MeasurableSet (langevinJointHitBy V C R T) := by
  have heq : langevinJointHitBy V C R T =
      {p : E × Ω | R ≤ ‖initialNoiseLangevinPrefix hV κ hκ hHess T (p.1, C p.2)‖} := by
    ext p
    exact initialNoiseLangevin_hit_iff_prefix_norm hV κ hκ hHess R T (p.1, C p.2)
  rw [heq]
  exact measurableSet_le measurable_const
    ((initialNoiseLangevinPrefix_measurable hV κ hκ hHess T).comp
      (measurable_fst.prodMk (hC.comp measurable_snd))).norm

/-- The true initial/noise product exit probability vanishes as the radius
diverges, with no moment bound or invariant-law assumption. -/
theorem langevinJointHitBy_measure_tendsto_zero
    {V : E → ℝ} (hV : ContDiff ℝ 2 V) (κ : ℝ) (hκ : 0 ≤ κ)
    (hHess : ∀ x z : E, κ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    {C : Ω → C(ℝ, E)} (hC : Measurable C) (T : NNReal)
    (ν : Measure E) [IsFiniteMeasure ν] (P : Measure Ω) [IsFiniteMeasure P] :
    Tendsto (fun R : ℝ => (ν.prod P) (langevinJointHitBy V C R T)) atTop (𝓝 0) := by
  have hanti : Antitone (fun R : ℝ => langevinJointHitBy V C R T) := by
    intro R S hRS p hp
    obtain ⟨r, hr, hh⟩ := hp
    exact ⟨r, hr, hRS.trans hh⟩
  have hempty : (⋂ R : ℝ, langevinJointHitBy V C R T) = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro p hp
    have hh := mem_iInter.mp hp (‖initialNoiseLangevinPrefix hV κ hκ hHess T (p.1, C p.2)‖ + 1)
    have hn := (initialNoiseLangevin_hit_iff_prefix_norm hV κ hκ hHess _ T (p.1, C p.2)).mp hh
    linarith
  have hh := tendsto_measure_iInter_atTop (μ := ν.prod P)
    (fun R => (measurableSet_langevinJointHitBy hV κ hκ hHess hC R T).nullMeasurableSet)
    hanti ⟨0, measure_ne_top _ _⟩
  simpa only [hempty, measure_empty, Function.comp_def] using hh

end CutoffRigidity
