module
public import CutoffRigidity.LangevinSurvival

/-! # Actual killed occupation measure with time-dependent survival

Survival is tested only up to the integration time s. Thus the domination
below applies to the occupation term in stopped Dynkin arguments; it does
not multiply martingale identities by a future-survival event.
-/
public section
namespace CutoffRigidity
open MeasureTheory MeasureTheory.Measure Set Metric Filter
open scoped ENNReal
variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

@[expose] noncomputable def langevinKilledOccupation
    (V : E → ℝ) (ν : Measure E) (η : Measure C(ℝ, E)) (T R : ℝ) : Measure E :=
  Measure.map (fun q : ℝ × (E × C(ℝ, E)) => langevinSolution V q.2.2 q.2.1 q.1.toNNReal)
    (((volume.restrict (Icc 0 T)).prod (ν.prod η)).restrict (langevinSurvivalSet V R))

/-- Genuine prefix-killed occupation is dominated by Lebesgue measure,
with the constant derived from the actual C² flow and initial density. -/
theorem langevinKilledOccupation_le_volume
    {V : E → ℝ} (hV : ContDiff ℝ 2 V) (rate : ℝ) (hrate : 0 ≤ rate)
    (hHess : ∀ x z : E, rate * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z) (R : ℝ) :
    ∃ K : NNReal, ∀ (ν : Measure E) [IsFiniteMeasure ν]
      (η : Measure C(ℝ, E)) [IsProbabilityMeasure η] (C : ENNReal),
      ν ≤ C • volume → ∀ T : ℝ, 0 ≤ T →
      langevinKilledOccupation V ν η T R ≤
        (C * (ENNReal.ofReal (Real.exp ((K : ℝ) * T))) ^ d * ENNReal.ofReal T) • volume := by
  obtain ⟨K, hK⟩ := langevinSolution_localized_law_le_volume hV rate hrate hHess R
  refine ⟨K, fun ν _ η _ C hν T hT => ?_⟩
  apply Measure.le_iff.mpr
  intro A hA
  have hF := langevinSolution_jointly_measurable_initial_noise_time hV rate hrate hHess
  have hS := (isClosed_langevinSurvivalSet hV rate hrate hHess R).measurableSet
  rw [langevinKilledOccupation, Measure.map_apply hF hA, Measure.restrict_apply (hF hA),
    Measure.prod_apply ((hF hA).inter hS)]
  have hpoint : ∀ᵐ s ∂volume.restrict (Icc 0 T),
      (ν.prod η) ((fun p : E × C(ℝ, E) => (s, p)) ⁻¹'
        ((fun q : ℝ × (E × C(ℝ, E)) => langevinSolution V q.2.2 q.2.1 q.1.toNNReal) ⁻¹' A ∩ langevinSurvivalSet V R)) ≤
        C * (ENNReal.ofReal (Real.exp ((K : ℝ) * T))) ^ d * volume A := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
    have heq : (fun p : E × C(ℝ, E) => (s, p)) ⁻¹'
        ((fun q : ℝ × (E × C(ℝ, E)) => langevinSolution V q.2.2 q.2.1 q.1.toNNReal) ⁻¹' A ∩ langevinSurvivalSet V R) =
      (fun p : E × C(ℝ, E) => langevinSolution V p.2 p.1 s) ⁻¹' A ∩ langevinStayingInputSet V s R := by
      ext p
      change (langevinSolution V p.2 p.1 (s.toNNReal : ℝ) ∈ A ∧ 0 ≤ s ∧ p ∈ langevinStayingInputSet V s R) ↔ _
      rw [Real.coe_toNNReal s hs.1]
      change (langevinSolution V p.2 p.1 s ∈ A ∧ 0 ≤ s ∧ p ∈ langevinStayingInputSet V s R) ↔
        langevinSolution V p.2 p.1 s ∈ A ∧ p ∈ langevinStayingInputSet V s R
      have hs0 : 0 ≤ s := hs.1
      tauto
    rw [heq]
    have hh := Measure.le_iff'.mp (hK ν η C hν s hs.1 s ⟨hs.1, le_rfl⟩) A
    rw [Measure.map_apply (langevinSolution_evaluation_continuous hV rate hrate hHess hs.1).measurable hA,
      Measure.restrict_apply ((langevinSolution_evaluation_continuous hV rate hrate hHess hs.1).measurable hA),
      Measure.smul_apply, smul_eq_mul] at hh
    have hex : ENNReal.ofReal (Real.exp ((K : ℝ) * s)) ≤ ENNReal.ofReal (Real.exp ((K : ℝ) * T)) :=
      ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hs.2 K.property))
    exact hh.trans (mul_le_mul_left (mul_le_mul_right (pow_le_pow_left' hex d) C) (volume A))
  have hi := lintegral_mono_ae hpoint
  simp only [lintegral_const, Measure.restrict_apply_univ, Real.volume_Icc, sub_zero] at hi
  change _ ≤ (C * ENNReal.ofReal (Real.exp ((K : ℝ) * T)) ^ d * ENNReal.ofReal T) * volume A
  exact hi.trans_eq (by ring)

end CutoffRigidity
