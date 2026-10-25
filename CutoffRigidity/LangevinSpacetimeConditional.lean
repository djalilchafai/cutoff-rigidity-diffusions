module

public import CutoffRigidity.LangevinSpacetimeKernel
public import CutoffRigidity.LangevinStoppedDynkin

/-! # Conditional space-time Dynkin increments on genuine Langevin paths

Actual shifted kernel Dynkin and conditional Markov means identify the
compensated increment for moving compact smooth tests. Time/source
continuity and bounds are explicit analytic domain conditions.
-/

public section

namespace CutoffRigidity

open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal BoundedContinuousFunction

variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

/-- Actual bounded moving path integrals are integrable random variables. -/
theorem continuousLangevinVersion_moving_integral_integrable
    {P : Measure Ω} [IsProbabilityMeasure P]
    {V : E → ℝ} (hV : ContDiff ℝ 2 V) (g : ℝ → E →ᵇ ℝ) (hg : Continuous g)
    (hgb : ∃ M : ℝ, ∀ r x, ‖g r x‖ ≤ M)
    (κ : ℝ) (hκ : 0 ≤ κ)
    (hHess : ∀ x z : E, κ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    {C : Ω → C(ℝ, E)} (hC : Measurable C) (x₀ : E) (s t : NNReal) :
    Integrable (fun ω => ∫ r in 0..(t : ℝ),
      g r (continuousLangevinVersion V C x₀ (s + r.toNNReal) ω)) P := by
  obtain ⟨M, hM⟩ := hgb
  let η : Measure ℝ := volume.restrict (Ioc 0 (t : ℝ))
  have : IsFiniteMeasure η := by dsimp [η]; infer_instance
  let F : ℝ → Ω → ℝ := fun r ω => g r (continuousLangevinVersion V C x₀ (s + r.toNNReal) ω)
  have hm : StronglyMeasurable (Function.uncurry F) := by
    apply stronglyMeasurable_uncurry_of_continuous_of_stronglyMeasurable
    · intro ω
      exact continuous_eval.comp (hg.prodMk
        ((continuousLangevinVersion_continuous hV κ hκ hHess C x₀ ω).comp
          (continuous_const.add continuous_real_toNNReal)))
    · intro r
      exact ((g r).continuous.measurable.comp
        (continuousLangevinVersion_measurable hV κ hκ hHess hC x₀ _)).stronglyMeasurable
  have hi : Integrable (Function.uncurry F) (η.prod P) :=
    Integrable.mono' (integrable_const M) hm.aestronglyMeasurable
      (Filter.Eventually.of_forall (fun p => hM p.1 _))
  have he : (fun ω => ∫ r in 0..(t : ℝ), F r ω) = fun ω => ∫ r, F r ω ∂η := by
    funext ω
    exact intervalIntegral.integral_of_le t.property
  change Integrable (fun ω => ∫ r in 0..(t : ℝ), F r ω) P
  rw [he]
  exact hi.integral_prod_right

/-- Actual conditional Dynkin increment for compact smooth space-time tests. -/
theorem continuousLangevinVersion_conditional_spacetime_dynkin
    {B : NNReal → Ω → E} {P : Measure Ω} (hB : IsEuclideanBrownian B P)
    {V : E → ℝ} (hV : ContDiff ℝ 2 V) (κ : ℝ) (hκ : 0 ≤ κ)
    (hHess : ∀ x z : E, κ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (q q' g : ℝ → E →ᵇ ℝ) (hqcont : Continuous q) (hgcont : Continuous g)
    (hgb : ∃ M : ℝ, ∀ r x, ‖g r x‖ ≤ M) (x₀ : E) (s t : NNReal)
    (hq : ∀ r ∈ Ioo (s : ℝ) ((s : ℝ) + t), HasDerivAt q (q' r) r)
    (hqs : ∀ r ∈ Ioo (s : ℝ) ((s : ℝ) + t), ContDiff ℝ 2 (q r))
    (hqsc : ∀ r ∈ Ioo (s : ℝ) ((s : ℝ) + t), HasCompactSupport (q r))
    (hsource : ∀ r x, g r x = q' r x + langevinDifferentialOperator V (q r) x)
    {C : Ω → C(ℝ, E)} (hC : Measurable C)
    (hCeq : ∀ᵐ ω ∂P, ∀ r : ℝ, C ω r = brownianDrivingPath B ω r) :
    P[fun ω => q ((s : ℝ) + t) (continuousLangevinVersion V C x₀ (s + t) ω) -
      (∫ r in 0..(t : ℝ), g ((s : ℝ) + r)
        (continuousLangevinVersion V C x₀ (s + r.toNNReal) ω)) |
        drivingHistoryFiltration hC s] =ᵐ[P]
      fun ω => q s (continuousLangevinVersion V C x₀ s ω) := by
  have := hB.isProbabilityMeasure
  let ambient : MeasurableSpace Ω := ‹MeasurableSpace Ω›
  let σ := drivingHistoryFiltration hC s
  let : MeasurableSpace Ω := ambient
  let Q := q ((s : ℝ) + t)
  let future (ω : Ω) := ∫ r in 0..(t : ℝ), g ((s : ℝ) + r)
    (continuousLangevinVersion V C x₀ (s + r.toNNReal) ω)
  have hv := continuousLangevinVersion_eq_process_ae (V := V) hCeq x₀
  have hFv : (fun ω => Q (continuousLangevinVersion V C x₀ (s + t) ω)) =ᵐ[P]
      fun ω => Q (langevinProcess V B x₀ (s + t) ω) := by
    filter_upwards [hv] with ω hω
    exact congrArg Q (hω _)
  have hJv : (fun ω => ∫ y, Q y ∂langevinKernel V B P t (continuousLangevinVersion V C x₀ s ω)) =ᵐ[P]
      fun ω => ∫ y, Q y ∂langevinKernel V B P t (langevinProcess V B x₀ s ω) := by
    filter_upwards [hv] with ω hω
    rw [hω s]
  have hraw := langevinProcess_condExp_history_markov hB hV Q.continuous
    ⟨‖Q‖, Q.norm_coe_le_norm⟩ κ hκ hHess x₀ s t hC hCeq
  have hCF := (condExp_congr_ae hFv).trans (hraw.trans hJv.symm)
  have hshift (y : E) := langevinKernel_shifted_spacetime_dynkin hB hV κ hκ hHess
    q q' g hqcont hgcont (s : ℝ) (t : ℝ) t.property hq hqs hqsc hsource y
  have hCJ := continuousLangevinVersion_condExp_moving_time_integral hB hV
    (fun r => g ((s : ℝ) + r)) (hgcont.comp (continuous_const.add continuous_id))
    (by obtain ⟨M, hM⟩ := hgb; exact ⟨M, fun r x => hM _ x⟩)
    κ hκ hHess x₀ s t hC hCeq
  have hiF : Integrable (fun ω => Q (continuousLangevinVersion V C x₀ (s + t) ω)) P :=
    Integrable.mono' (integrable_const ‖Q‖)
      (Q.continuous.measurable.comp
        (continuousLangevinVersion_measurable hV κ hκ hHess hC x₀ (s + t))).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun ω => Q.norm_coe_le_norm _))
  have hiJ : Integrable future P := continuousLangevinVersion_moving_integral_integrable hV
    (fun r => g ((s : ℝ) + r)) (hgcont.comp (continuous_const.add continuous_id))
    (by obtain ⟨M, hM⟩ := hgb; exact ⟨M, fun r x => hM _ x⟩)
    κ hκ hHess hC x₀ s t
  have hsub := condExp_sub hiF hiJ σ
  filter_upwards [hsub, hCF, hCJ] with ω hsω hFω hJω
  change P[fun ω => Q (continuousLangevinVersion V C x₀ (s + t) ω) - future ω | σ] ω = _ at hsω ⊢
  rw [hsω]
  change P[fun ω => Q (continuousLangevinVersion V C x₀ (s + t) ω) | σ] ω - P[future | σ] ω = _
  change P[fun ω => Q (continuousLangevinVersion V C x₀ (s + t) ω) | σ] ω = _ at hFω
  change P[future | σ] ω = _ at hJω
  rw [hFω, hJω]
  have he := hshift (continuousLangevinVersion V C x₀ s ω)
  rw [Real.toNNReal_coe] at he
  change (∫ y, Q y ∂langevinKernel V B P t (continuousLangevinVersion V C x₀ s ω)) - _ = _
  linarith only [he]

end CutoffRigidity
