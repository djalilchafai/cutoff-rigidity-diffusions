module

public import CutoffRigidity.LangevinConditionalCompensator
public import CutoffRigidity.LangevinVarianceInterpolation

/-! # Conditional Fubini for genuine moving Langevin tests

Actual conditional Markov means and bounded joint measurability give the
conditional compensator for a continuous curve of bounded spatial tests.
The curve bound is an explicit integration-domain condition; no conditional
identity, martingale property or local Poincare conclusion is assumed.
-/

public section

namespace CutoffRigidity

open Set MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology BoundedContinuousFunction

variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

/-- Actual conditional expectation commutes with the moving future test integral. -/
theorem continuousLangevinVersion_condExp_moving_time_integral
    {B : ℝ≥0 → Ω → E} {P : Measure Ω} (hB : IsEuclideanBrownian B P)
    {V : E → ℝ} (hV : ContDiff ℝ 2 V)
    (g : ℝ → E →ᵇ ℝ) (hg : Continuous g)
    (hgb : ∃ M : ℝ, ∀ r x, ‖g r x‖ ≤ M)
    (κ : ℝ) (hκ : 0 ≤ κ)
    (hHess : ∀ x z, κ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (x₀ : E) (s t : ℝ≥0)
    {C : Ω → C(ℝ, E)} (hC : Measurable C)
    (hCeq : ∀ᵐ ω ∂P, ∀ r : ℝ, C ω r = brownianDrivingPath B ω r) :
    P[fun ω => ∫ r in 0..(t : ℝ), g r (continuousLangevinVersion V C x₀ (s + r.toNNReal) ω) |
      MeasurableSpace.comap (fun ω => (C ω).restrict (Icc 0 (s : ℝ))) inferInstance] =ᵐ[P]
      fun ω => ∫ r in 0..(t : ℝ),
        (∫ y, g r y ∂langevinKernel V B P r.toNNReal (continuousLangevinVersion V C x₀ s ω)) := by
  classical
  let := hB.isProbabilityMeasure
  obtain ⟨M, hM⟩ := hgb
  let η : Measure ℝ := volume.restrict (Ioc 0 (t : ℝ))
  have : IsFiniteMeasure η := by dsimp [η]; infer_instance
  let F : ℝ → Ω → ℝ := fun r ω => g r (continuousLangevinVersion V C x₀ (s + r.toNNReal) ω)
  let G : ℝ → Ω → ℝ := fun r ω => ∫ y, g r y ∂langevinKernel V B P r.toNNReal
    (continuousLangevinVersion V C x₀ s ω)
  let history : Ω → C(Icc 0 (s : ℝ), E) := fun ω => (C ω).restrict (Icc 0 (s : ℝ))
  have hmHist : Measurable history := (ContinuousMap.continuous_restrict _).measurable.comp hC
  have hF : StronglyMeasurable (Function.uncurry F) := by
    apply stronglyMeasurable_uncurry_of_continuous_of_stronglyMeasurable
    · intro ω
      exact continuous_eval.comp (hg.prodMk
        ((continuousLangevinVersion_continuous hV κ hκ hHess C x₀ ω).comp
          (continuous_const.add continuous_real_toNNReal)))
    · intro r
      exact ((g r).continuous.measurable.comp (continuousLangevinVersion_measurable hV κ hκ hHess hC x₀ _)).stronglyMeasurable
  have hG : StronglyMeasurable (Function.uncurry G) := by
    apply stronglyMeasurable_uncurry_of_continuous_of_stronglyMeasurable
    · intro ω
      apply continuous_iff_continuousAt.mpr
      intro r
      exact tendsto_langevinKernel_integral_varying_bounded_test hB hV κ hκ hHess
        (hg.tendsto r) (continuous_real_toNNReal.tendsto r) _
    · intro r
      have hJ : StronglyMeasurable (fun x => ∫ y, g r y ∂langevinKernel V B P r.toNNReal x) :=
        (g r).continuous.measurable.stronglyMeasurable.integral_kernel
      exact hJ.comp_measurable (continuousLangevinVersion_measurable hV κ hκ hHess hC x₀ s)
  have hKjoint : StronglyMeasurable
      (Function.uncurry (fun r : ℝ => fun x : E => ∫ y, g r y ∂langevinKernel V B P r.toNNReal x)) := by
    apply stronglyMeasurable_uncurry_of_continuous_of_stronglyMeasurable
    · intro x
      apply continuous_iff_continuousAt.mpr
      intro r
      exact tendsto_langevinKernel_integral_varying_bounded_test hB hV κ hκ hHess
        (hg.tendsto r) (continuous_real_toNNReal.tendsto r) x
    · intro r
      exact (g r).continuous.measurable.stronglyMeasurable.integral_kernel
  let Q : E → ℝ := fun x => ∫ r, (∫ y, g r y ∂langevinKernel V B P r.toNNReal x) ∂η
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
    have hraw := langevinProcess_condExp_history_markov hB hV (g r).continuous ⟨M, hM r⟩ κ hκ hHess x₀ s r.toNNReal hC hCeq
    have hFr : F r =ᵐ[P] fun ω => g r (langevinProcess V B x₀ (s + r.toNNReal) ω) := by
      filter_upwards [hversion] with ω hω
      exact congrArg (g r) (hω _)
    have hGr : G r =ᵐ[P] fun ω => ∫ y, g r y ∂langevinKernel V B P r.toNNReal (langevinProcess V B x₀ s ω) := by
      filter_upwards [hversion] with ω hω
      exact congrArg (fun x => ∫ y, g r y ∂langevinKernel V B P r.toNNReal x) (hω s)
    exact (condExp_congr_ae hFr).trans (hraw.trans hGr.symm)
  have hCE := condExp_integral_of_bounded_jointly_measurable η P F G hF hG
    (MeasurableSpace.comap history inferInstance) hmHist.comap_le
    ⟨M, fun r ω => hM r _⟩
    ⟨M, fun r ω => langevinKernel_integral_compact_test_norm_le hB hV κ hκ hHess (hM r) _ _⟩ hgm hcond
  have hFint : (fun ω => ∫ r in 0..(t : ℝ), F r ω) =ᵐ[P] fun ω => ∫ r, F r ω ∂η :=
    Filter.Eventually.of_forall (fun ω => intervalIntegral.integral_of_le t.property)
  have hGint : (fun ω => ∫ r in 0..(t : ℝ), G r ω) =ᵐ[P] fun ω => ∫ r, G r ω ∂η :=
    Filter.Eventually.of_forall (fun ω => intervalIntegral.integral_of_le t.property)
  exact (condExp_congr_ae hFint).trans (hCE.trans hGint.symm)


end CutoffRigidity
