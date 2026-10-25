module
public import CutoffRigidity.LangevinJointExit
public import CutoffRigidity.LangevinStoppedDynkin

/-! # Actual joint initial-state/time measurability of compact Dynkin functionals -/
public section
namespace CutoffRigidity
open MeasureTheory ProbabilityTheory Set Filter Topology
variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

set_option maxHeartbeats 700000 in
theorem langevinDynkinProcess_jointly_stronglyMeasurable_initial_time
    {V f : E → ℝ} (hV : ContDiff ℝ 2 V) (hf : ContDiff ℝ 2 f)
    (κ : ℝ) (hκ : 0 ≤ κ)
    (hHess : ∀ x z : E, κ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    {C : Ω → C(ℝ, E)} (hC : Measurable C) :
    StronglyMeasurable (fun q : NNReal × (E × Ω) => langevinDynkinProcess V f C q.2.1 q.1 q.2.2) := by
  have hstate (t : NNReal) : Measurable (fun p : E × Ω => continuousLangevinVersion V C p.1 t p.2) :=
    (langevinSolution_evaluation_continuous hV κ hκ hHess t.property).measurable.comp
      (measurable_fst.prodMk (hC.comp measurable_snd))
  have hg := continuous_langevinDifferentialOperator hV hf
  have hJ : StronglyMeasurable (fun q : ℝ × (E × Ω) =>
      langevinDifferentialOperator V f (continuousLangevinVersion V C q.2.1 q.1.toNNReal q.2.2)) := by
    apply stronglyMeasurable_uncurry_of_continuous_of_stronglyMeasurable
      (u := fun r : ℝ => fun p : E × Ω => langevinDifferentialOperator V f
        (continuousLangevinVersion V C p.1 r.toNNReal p.2))
    · intro p
      exact (hg.comp (continuousLangevinVersion_continuous hV κ hκ hHess C p.1 p.2)).comp continuous_real_toNNReal
    · intro r
      exact (hg.measurable.comp (hstate r.toNNReal)).stronglyMeasurable
  have hm (t : NNReal) : StronglyMeasurable (fun p : E × Ω => langevinDynkinProcess V f C p.1 t p.2) := by
    let η : Measure ℝ := volume.restrict (Ioc 0 (t : ℝ))
    have : IsFiniteMeasure η := by dsimp [η]; infer_instance
    have hQ : StronglyMeasurable (fun p : E × Ω => ∫ r,
        langevinDifferentialOperator V f (continuousLangevinVersion V C p.1 r.toNNReal p.2) ∂η) :=
      hJ.integral_prod_left
    have heq : (fun p : E × Ω => langevinDynkinProcess V f C p.1 t p.2) =
        fun p => f (continuousLangevinVersion V C p.1 t p.2) - f p.1 - ∫ r,
          langevinDifferentialOperator V f (continuousLangevinVersion V C p.1 r.toNNReal p.2) ∂η := by
      funext p
      change _ - _ - (∫ r in (0 : ℝ)..(t : ℝ), _) = _
      apply congrArg (fun z : ℝ => f (continuousLangevinVersion V C p.1 t p.2) - f p.1 - z)
      exact intervalIntegral.integral_of_le t.property
    rw [heq]
    exact ((hf.continuous.measurable.comp (hstate t)).stronglyMeasurable.sub
      (hf.continuous.measurable.comp measurable_fst).stronglyMeasurable).sub hQ
  exact stronglyMeasurable_uncurry_of_continuous_of_stronglyMeasurable
    (u := fun t : NNReal => fun p : E × Ω => langevinDynkinProcess V f C p.1 t p.2)
    (fun p => langevinDynkinProcess_continuous hV hf κ hκ hHess C p.1 p.2) hm

omit [MeasurableSpace Ω] in
/-- The compact test yields one genuine deterministic bound uniformly over
all initial states, all continuous noise samples, and a finite time window. -/
theorem langevinDynkinProcess_uniform_initial_bound
    {V f : E → ℝ} (hV : ContDiff ℝ 2 V) (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (C : Ω → C(ℝ, E)) (T : NNReal) :
    ∃ K : ℝ, ∀ (x₀ : E) (t : NNReal), t ≤ T → ∀ ω, ‖langevinDynkinProcess V f C x₀ t ω‖ ≤ K := by
  obtain ⟨N, hN0, hN⟩ := compact_continuous_norm_bound hf.continuous hfc
  obtain ⟨M, hM0, hM⟩ := compact_continuous_norm_bound (continuous_langevinDifferentialOperator hV hf)
    (hasCompactSupport_langevinDifferentialOperator V hfc)
  refine ⟨2 * N + M * T, fun x₀ t ht ω => ?_⟩
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

end CutoffRigidity
