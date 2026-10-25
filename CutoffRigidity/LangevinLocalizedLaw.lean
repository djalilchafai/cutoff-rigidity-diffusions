module
public import CutoffRigidity.LangevinLocalizedVolume
public import CutoffRigidity.GibbsCompactApproximation
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousMap
public import Mathlib.Topology.ContinuousMap.SecondCountableSpace

/-! # Actual localized Langevin laws have bounded Lebesgue densities

Initial law and continuous noise are independent under the actual product
measure. Localization is the genuine event that the selected trajectory
stays in a compact ball throughout the fixed time horizon.
-/
public section
namespace CutoffRigidity
open MeasureTheory MeasureTheory.Measure Set Metric
open scoped ENNReal
variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

@[expose] noncomputable def langevinStayingInputSet
    (V : E → ℝ) (T R : ℝ) : Set (E × C(ℝ, E)) :=
  {p | MapsTo (langevinSolution V p.2 p.1) (Icc 0 T) (closedBall (0 : E) R)}

theorem isClosed_langevinStayingInputSet
    {V : E → ℝ} (hV : ContDiff ℝ 2 V) (rate : ℝ) (hrate : 0 ≤ rate)
    (hHess : ∀ x z : E, rate * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (T R : ℝ) : IsClosed (langevinStayingInputSet V T R) := by
  have heq : langevinStayingInputSet V T R =
      ⋂ s : Icc 0 T, (fun p : E × C(ℝ, E) => langevinSolution V p.2 p.1 s) ⁻¹' closedBall (0 : E) R := by
    ext p
    simp only [langevinStayingInputSet, MapsTo, mem_ofPred_eq, mem_iInter, mem_preimage, Subtype.forall]
  rw [heq]
  exact isClosed_iInter (fun s => isClosed_closedBall.preimage
    (langevinSolution_evaluation_continuous hV rate hrate hHess s.property.1))

/-- The actual fixed-time localized law, obtained from the independent
initial-state/noise product measure, has a uniform density bound on [0,T]. -/
theorem langevinSolution_localized_law_le_volume
    {V : E → ℝ} (hV : ContDiff ℝ 2 V) (rate : ℝ) (hrate : 0 ≤ rate)
    (hHess : ∀ x z : E, rate * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z) (R : ℝ) :
    ∃ K : NNReal, ∀ (ν : Measure E) [IsFiniteMeasure ν]
      (η : Measure C(ℝ, E)) [IsProbabilityMeasure η] (C : ENNReal),
      ν ≤ C • volume → ∀ T : ℝ, 0 ≤ T → ∀ s ∈ Icc 0 T,
      Measure.map (fun p : E × C(ℝ, E) => langevinSolution V p.2 p.1 s)
        ((ν.prod η).restrict (langevinStayingInputSet V T R)) ≤
      (C * (ENNReal.ofReal (Real.exp ((K : ℝ) * T))) ^ d) • volume := by
  obtain ⟨K, hK⟩ := langevinSolution_localized_volume_bound_uniform hV rate hrate hHess R
  refine ⟨K, fun ν _ η _ C hν T hT s hs => ?_⟩
  apply Measure.le_iff.mpr
  intro A hA
  have hF : Measurable (fun p : E × C(ℝ, E) => langevinSolution V p.2 p.1 s) :=
    (langevinSolution_evaluation_continuous hV rate hrate hHess hs.1).measurable
  have hS := (isClosed_langevinStayingInputSet hV rate hrate hHess T R).measurableSet
  rw [Measure.map_apply hF hA, Measure.restrict_apply (hF hA), Measure.prod_apply_symm ((hF hA).inter hS)]
  have hpoint (w : C(ℝ, E)) :
      ν ((fun x => (x, w)) ⁻¹' ((fun p : E × C(ℝ, E) => langevinSolution V p.2 p.1 s) ⁻¹' A ∩
        langevinStayingInputSet V T R)) ≤
      C * (ENNReal.ofReal (Real.exp ((K : ℝ) * T))) ^ d * volume A := by
    have heq : (fun x => (x, w)) ⁻¹' ((fun p : E × C(ℝ, E) => langevinSolution V p.2 p.1 s) ⁻¹' A ∩
        langevinStayingInputSet V T R) = langevinStayingSet V w T R ∩
        (fun x => langevinSolution V w x s) ⁻¹' A := by
      ext x
      exact and_comm
    rw [heq]
    have hdom := Measure.le_iff'.mp hν (langevinStayingSet V w T R ∩ (fun x => langevinSolution V w x s) ⁻¹' A)
    rw [Measure.smul_apply, smul_eq_mul] at hdom
    have hm := mul_le_mul_right (hK w w.continuous T hT s hs A) C
    exact hdom.trans (hm.trans_eq (mul_assoc _ _ _).symm)
  have hi := lintegral_mono (μ := η) hpoint
  simpa only [lintegral_const, measure_univ, mul_one, Measure.smul_apply, smul_eq_mul] using hi

set_option maxHeartbeats 800000 in
/-- Actual joint measurability in forward time, initial state and continuous
noise follows from continuous trajectories and genuine evaluation continuity. -/
theorem langevinSolution_jointly_measurable_initial_noise_time
    {V : E → ℝ} (hV : ContDiff ℝ 2 V) (rate : ℝ) (hrate : 0 ≤ rate)
    (hHess : ∀ x z : E, rate * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z) :
    Measurable (fun q : ℝ × (E × C(ℝ, E)) => langevinSolution V q.2.2 q.2.1 q.1.toNNReal) := by
  have hcont (p : E × C(ℝ, E)) : Continuous (fun t : NNReal => langevinSolution V p.2 p.1 t) :=
    (langevinSolution_continuousOn hV rate hrate hHess p.2.continuous p.1).comp_continuous
      NNReal.continuous_coe (fun t => t.property)
  have hm (t : NNReal) : StronglyMeasurable (fun p : E × C(ℝ, E) => langevinSolution V p.2 p.1 t) :=
    (langevinSolution_evaluation_continuous hV rate hrate hHess t.property).measurable.stronglyMeasurable
  have hj : StronglyMeasurable (fun q : NNReal × (E × C(ℝ, E)) => langevinSolution V q.2.2 q.2.1 q.1) :=
    stronglyMeasurable_uncurry_of_continuous_of_stronglyMeasurable hcont hm
  have hmap : Measurable (fun q : ℝ × (E × C(ℝ, E)) => (q.1.toNNReal, q.2)) :=
    (continuous_real_toNNReal.measurable.comp measurable_fst).prodMk measurable_snd
  exact hj.measurable.comp hmap

/-- The actual localized occupation measure on [0,T], including its
independent initial/noise product construction. -/
@[expose] noncomputable def langevinLocalizedOccupation
    (V : E → ℝ) (ν : Measure E) (η : Measure C(ℝ, E)) (T R : ℝ) : Measure E :=
  Measure.map (fun q : ℝ × (E × C(ℝ, E)) => langevinSolution V q.2.2 q.2.1 q.1.toNNReal)
    ((volume.restrict (Icc 0 T)).prod ((ν.prod η).restrict (langevinStayingInputSet V T R)))

/-- Actual localized occupation has a finite explicit Lebesgue domination
whenever the initial law has an actual bounded density. -/
theorem langevinLocalizedOccupation_le_volume
    {V : E → ℝ} (hV : ContDiff ℝ 2 V) (rate : ℝ) (hrate : 0 ≤ rate)
    (hHess : ∀ x z : E, rate * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z) (R : ℝ) :
    ∃ K : NNReal, ∀ (ν : Measure E) [IsFiniteMeasure ν]
      (η : Measure C(ℝ, E)) [IsProbabilityMeasure η] (C : ENNReal),
      ν ≤ C • volume → ∀ T : ℝ, 0 ≤ T →
      langevinLocalizedOccupation V ν η T R ≤
        (C * (ENNReal.ofReal (Real.exp ((K : ℝ) * T))) ^ d * ENNReal.ofReal T) • volume := by
  obtain ⟨K, hK⟩ := langevinSolution_localized_law_le_volume hV rate hrate hHess R
  refine ⟨K, fun ν _ η _ C hν T hT => ?_⟩
  apply Measure.le_iff.mpr
  intro A hA
  let μ := (ν.prod η).restrict (langevinStayingInputSet V T R)
  have hF := langevinSolution_jointly_measurable_initial_noise_time hV rate hrate hHess
  rw [langevinLocalizedOccupation, Measure.map_apply hF hA, Measure.prod_apply (hF hA)]
  have hpoint : ∀ᵐ s ∂volume.restrict (Icc 0 T),
      μ ((fun p : E × C(ℝ, E) => (s, p)) ⁻¹'
        (fun q : ℝ × (E × C(ℝ, E)) => langevinSolution V q.2.2 q.2.1 q.1.toNNReal) ⁻¹' A) ≤
        C * (ENNReal.ofReal (Real.exp ((K : ℝ) * T))) ^ d * volume A := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
    have hh := Measure.le_iff'.mp (hK ν η C hν T hT s hs) A
    rw [Measure.map_apply (langevinSolution_evaluation_continuous hV rate hrate hHess hs.1).measurable hA,
      Measure.smul_apply, smul_eq_mul] at hh
    change μ ((fun p : E × C(ℝ, E) => langevinSolution V p.2 p.1 (s.toNNReal : ℝ)) ⁻¹' A) ≤ _
    rw [Real.coe_toNNReal s hs.1]
    exact hh
  have hi := lintegral_mono_ae hpoint
  simp only [lintegral_const, Measure.restrict_apply_univ, Real.volume_Icc, sub_zero] at hi
  change _ ≤ (C * ENNReal.ofReal (Real.exp ((K : ℝ) * T)) ^ d * ENNReal.ofReal T) * volume A
  exact hi.trans_eq (by ring)

end CutoffRigidity
