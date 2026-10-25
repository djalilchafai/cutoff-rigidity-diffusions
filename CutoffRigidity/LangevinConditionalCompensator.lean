module

public import CutoffRigidity.ConditionalFubini
public import CutoffRigidity.LangevinContinuousVersion

/-! # Actual conditional expectation of the Langevin path compensator

Joint measurability comes from the actual continuous measurable solution
version. Set-integral conditional Fubini, actual Markov conditional means,
and compact-test bounds then identify the conditional expectation of the
actual time integral. No conditional-Fubini or martingale premise is used.
-/

public section

namespace CutoffRigidity

open Set MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology

variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

/-- Conditional Fubini for the genuine continuous solution version, with
all measurability and domination hypotheses derived from the actual dynamics. -/
theorem continuousLangevinVersion_condExp_time_integral
    {B : ℝ≥0 → Ω → E} {P : Measure Ω} (hB : IsEuclideanBrownian B P)
    {V g : E → ℝ} (hV : ContDiff ℝ 2 V) (hg : Continuous g) (hgc : HasCompactSupport g)
    (κ : ℝ) (hκ : 0 ≤ κ)
    (hHess : ∀ x z, κ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (x₀ : E) (s t : ℝ≥0)
    {C : Ω → C(ℝ, E)} (hC : Measurable C)
    (hCeq : ∀ᵐ ω ∂P, ∀ r : ℝ, C ω r = brownianDrivingPath B ω r) :
    P[fun ω => ∫ r in 0..(t : ℝ), g (continuousLangevinVersion V C x₀ (s + r.toNNReal) ω) |
      MeasurableSpace.comap (fun ω => (C ω).restrict (Icc 0 (s : ℝ))) inferInstance] =ᵐ[P]
      fun ω => ∫ r in 0..(t : ℝ),
        (∫ y, g y ∂langevinKernel V B P r.toNNReal (continuousLangevinVersion V C x₀ s ω)) := by
  classical
  let := hB.isProbabilityMeasure
  obtain ⟨M, _, hM⟩ := compact_continuous_norm_bound hg hgc
  let η : Measure ℝ := volume.restrict (Ioc 0 (t : ℝ))
  have : IsFiniteMeasure η := by dsimp [η]; infer_instance
  let F : ℝ → Ω → ℝ := fun r ω => g (continuousLangevinVersion V C x₀ (s + r.toNNReal) ω)
  let G : ℝ → Ω → ℝ := fun r ω => ∫ y, g y ∂langevinKernel V B P r.toNNReal
    (continuousLangevinVersion V C x₀ s ω)
  let history : Ω → C(Icc 0 (s : ℝ), E) := fun ω => (C ω).restrict (Icc 0 (s : ℝ))
  have hmHist : Measurable history := (ContinuousMap.continuous_restrict _).measurable.comp hC
  have hF : StronglyMeasurable (Function.uncurry F) := by
    apply stronglyMeasurable_uncurry_of_continuous_of_stronglyMeasurable
    · intro ω
      exact (hg.comp (continuousLangevinVersion_continuous hV κ hκ hHess C x₀ ω)).comp
        (continuous_const.add continuous_real_toNNReal)
    · intro r
      exact (hg.measurable.comp (continuousLangevinVersion_measurable hV κ hκ hHess hC x₀ _)).stronglyMeasurable
  have hG : StronglyMeasurable (Function.uncurry G) := by
    apply stronglyMeasurable_uncurry_of_continuous_of_stronglyMeasurable
    · intro ω
      exact (continuous_langevinKernel_integral_of_bounded_continuous hB hV hg ⟨M, hM⟩ κ hκ hHess _).comp
        continuous_real_toNNReal
    · intro r
      have hJ : StronglyMeasurable (fun x => ∫ y, g y ∂langevinKernel V B P r.toNNReal x) :=
        hg.measurable.stronglyMeasurable.integral_kernel
      exact hJ.comp_measurable (continuousLangevinVersion_measurable hV κ hκ hHess hC x₀ s)
  have hKjoint : StronglyMeasurable
      (Function.uncurry (fun r : ℝ => fun x : E => ∫ y, g y ∂langevinKernel V B P r.toNNReal x)) := by
    apply stronglyMeasurable_uncurry_of_continuous_of_stronglyMeasurable
    · intro x
      exact (continuous_langevinKernel_integral_of_bounded_continuous hB hV hg ⟨M, hM⟩ κ hκ hHess x).comp
        continuous_real_toNNReal
    · intro r
      exact hg.measurable.stronglyMeasurable.integral_kernel
  let Q : E → ℝ := fun x => ∫ r, (∫ y, g y ∂langevinKernel V B P r.toNNReal x) ∂η
  have hmQ : StronglyMeasurable Q := hKjoint.integral_prod_left
  let A : C(Icc 0 (s : ℝ), E) → E := fun h => intervalLangevinEvaluation V s.property (x₀, h)
  have hmA : Measurable A := ((intervalLangevinEvaluation_continuous hV κ hκ hHess s.property).comp
    (continuous_const.prodMk continuous_id)).measurable
  have hgm : AEStronglyMeasurable[MeasurableSpace.comap history inferInstance]
      (fun ω => ∫ r, G r ω ∂η) P := by
    have heq : (fun ω => ∫ r, G r ω ∂η) = fun ω => Q (A (history ω)) := by
      funext ω
      unfold Q G
      rw [continuousLangevinVersion_eq_history_evaluation hV κ hκ hHess C x₀ s ω]
    rw [heq]
    exact ((hmQ.measurable.comp hmA).comp (comap_measurable history)).stronglyMeasurable.aestronglyMeasurable
  have hversion := continuousLangevinVersion_eq_process_ae (V := V) hCeq x₀
  have hcond (r : ℝ) : P[F r | MeasurableSpace.comap history inferInstance] =ᵐ[P] G r := by
    have hraw := langevinProcess_condExp_history_markov hB hV hg ⟨M, hM⟩ κ hκ hHess x₀ s r.toNNReal hC hCeq
    have hFr : F r =ᵐ[P] fun ω => g (langevinProcess V B x₀ (s + r.toNNReal) ω) := by
      filter_upwards [hversion] with ω hω
      exact congrArg g (hω _)
    have hGr : G r =ᵐ[P] fun ω => ∫ y, g y ∂langevinKernel V B P r.toNNReal (langevinProcess V B x₀ s ω) := by
      filter_upwards [hversion] with ω hω
      exact congrArg (fun x => ∫ y, g y ∂langevinKernel V B P r.toNNReal x) (hω s)
    exact (condExp_congr_ae hFr).trans (hraw.trans hGr.symm)
  have hCE := condExp_integral_of_bounded_jointly_measurable η P F G hF hG
    (MeasurableSpace.comap history inferInstance) hmHist.comap_le
    ⟨M, fun r ω => hM _⟩
    ⟨M, fun r ω => langevinKernel_integral_compact_test_norm_le hB hV κ hκ hHess hM _ _⟩ hgm hcond
  have hFint : (fun ω => ∫ r in 0..(t : ℝ), F r ω) =ᵐ[P] fun ω => ∫ r, F r ω ∂η :=
    Filter.Eventually.of_forall (fun ω => intervalIntegral.integral_of_le t.property)
  have hGint : (fun ω => ∫ r in 0..(t : ℝ), G r ω) =ᵐ[P] fun ω => ∫ r, G r ω ∂η :=
    Filter.Eventually.of_forall (fun ω => intervalIntegral.integral_of_le t.property)
  exact (condExp_congr_ae hFint).trans (hCE.trans hGint.symm)

/-- The conditional expectation of the actual pathwise future compensator.
This is the conditional-Fubini step needed for the Dynkin martingale. -/
theorem langevinProcess_condExp_time_integral
    {B : ℝ≥0 → Ω → E} {P : Measure Ω} (hB : IsEuclideanBrownian B P)
    {V g : E → ℝ} (hV : ContDiff ℝ 2 V) (hg : Continuous g) (hgc : HasCompactSupport g)
    (κ : ℝ) (hκ : 0 ≤ κ)
    (hHess : ∀ x z, κ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (x₀ : E) (s t : ℝ≥0)
    {C : Ω → C(ℝ, E)} (hC : Measurable C)
    (hCeq : ∀ᵐ ω ∂P, ∀ r : ℝ, C ω r = brownianDrivingPath B ω r) :
    P[fun ω => ∫ r in 0..(t : ℝ), g (langevinProcess V B x₀ (s + r.toNNReal) ω) |
      MeasurableSpace.comap (fun ω => (C ω).restrict (Icc 0 (s : ℝ))) inferInstance] =ᵐ[P]
      fun ω => ∫ r in 0..(t : ℝ),
        (∫ y, g y ∂langevinKernel V B P r.toNNReal (langevinProcess V B x₀ s ω)) := by
  have hversion := continuousLangevinVersion_eq_process_ae (V := V) hCeq x₀
  have hF : (fun ω => ∫ r in 0..(t : ℝ), g (continuousLangevinVersion V C x₀ (s + r.toNNReal) ω)) =ᵐ[P]
      fun ω => ∫ r in 0..(t : ℝ), g (langevinProcess V B x₀ (s + r.toNNReal) ω) := by
    filter_upwards [hversion] with ω hω
    exact intervalIntegral.integral_congr (fun r _ => congrArg g (hω _))
  have hG : (fun ω => ∫ r in 0..(t : ℝ),
      (∫ y, g y ∂langevinKernel V B P r.toNNReal (continuousLangevinVersion V C x₀ s ω))) =ᵐ[P]
      fun ω => ∫ r in 0..(t : ℝ),
        (∫ y, g y ∂langevinKernel V B P r.toNNReal (langevinProcess V B x₀ s ω)) := by
    filter_upwards [hversion] with ω hω
    rw [hω s]
  exact (condExp_congr_ae hF.symm).trans
    ((continuousLangevinVersion_condExp_time_integral hB hV hg hgc κ hκ hHess x₀ s t hC hCeq).trans hG)

end CutoffRigidity
