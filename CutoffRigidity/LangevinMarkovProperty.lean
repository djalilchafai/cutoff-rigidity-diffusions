module

public import CutoffRigidity.LangevinForwardEquation
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic

/-! # Actual past-test Markov identities

The entire future Brownian driving path is independent of the actual past
noise history. The deterministic restart identity and their genuine product
law give the conditional-mean Markov identity tested against every bounded
measurable function of a measurable continuous history version.
-/

public section

namespace CutoffRigidity

open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal

/-- Integrating a bounded measurable function of two genuinely independent
variables is genuine iterated integration against the second variable's law. -/
theorem integral_independent_pair_eq_iterated
    {Ω H W : Type*} [MeasurableSpace Ω] [MeasurableSpace H] [MeasurableSpace W]
    {P : Measure Ω} [IsProbabilityMeasure P] {history : Ω → H} {future : Ω → W}
    (hh : AEMeasurable history P) (hw : AEMeasurable future P)
    (hindep : IndepFun history future P)
    {F : H × W → ℝ} (hF : Measurable F) (hbound : ∃ M : ℝ, ∀ p, ‖F p‖ ≤ M) :
    (∫ ω, F (history ω, future ω) ∂P) =
      ∫ ω, (∫ w, F (history ω, w) ∂P.map future) ∂P := by
  obtain ⟨M, hM⟩ := hbound
  have hint : Integrable F ((P.map history).prod (P.map future)) :=
    Integrable.mono' (integrable_const M) hF.aestronglyMeasurable
      (Filter.Eventually.of_forall hM)
  have hjoint := hindep.map_prod_eq_prod_map_map hh hw
  have hinner : StronglyMeasurable (fun h => ∫ w, F (h, w) ∂P.map future) :=
    (show StronglyMeasurable (Function.uncurry (fun h w => F (h, w))) from
      hF.stronglyMeasurable).integral_prod_right
  calc
    _ = ∫ p, F p ∂P.map (fun ω => (history ω, future ω)) :=
      (integral_map (hh.prodMk hw) hF.aestronglyMeasurable).symm
    _ = ∫ p, F p ∂(P.map history).prod (P.map future) := by rw [hjoint]
    _ = ∫ h, (∫ w, F (h, w) ∂P.map future) ∂P.map history := integral_prod F hint
    _ = _ := integral_map hh hinner.aestronglyMeasurable

variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

/-- The actual noise-law representation integrates continuous tests according
to the actual kernel, at every deterministic initial state. -/
theorem integral_langevinKernel_eq_noise_integral
    {B : ℝ≥0 → Ω → E} {P : Measure Ω} (hB : IsEuclideanBrownian B P)
    {V f : E → ℝ} (hV : ContDiff ℝ 2 V) (hf : Continuous f)
    (κ : ℝ) (hκ : 0 ≤ κ)
    (hHess : ∀ x z, κ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (x : E) (t : ℝ≥0) :
    (∫ y, f y ∂langevinKernel V B P t x) =
      ∫ w : C(ℝ, E), f (langevinEvaluation V t (x, w)) ∂brownianNoiseLaw B P := by
  rw [langevinKernel_apply_noiseLaw hB hV κ hκ hHess]
  have hm : Measurable (fun w : C(ℝ, E) => langevinEvaluation V t (x, w)) :=
    ((langevinEvaluation_continuous hV κ hκ hHess t).comp
      (continuous_const.prodMk continuous_id)).measurable
  exact integral_map hm.aemeasurable hf.measurable.aestronglyMeasurable

/-- The actual Markov conditional-mean identity against every bounded
measurable test of the entire continuous driving-noise history. The supplied
version is genuinely measurable and equals the actual driver simultaneously
at all times; such a version has already been constructed. -/
theorem langevinProcess_past_test_markov_identity
    {B : ℝ≥0 → Ω → E} {P : Measure Ω} (hB : IsEuclideanBrownian B P)
    {V f : E → ℝ} (hV : ContDiff ℝ 2 V) (hf : Continuous f)
    (hfb : ∃ M : ℝ, ∀ y, ‖f y‖ ≤ M)
    (κ : ℝ) (hκ : 0 ≤ κ)
    (hHess : ∀ x z, κ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (x₀ : E) (s t : ℝ≥0)
    {C : Ω → C(ℝ, E)} (hC : Measurable C)
    (hCeq : ∀ᵐ ω ∂P, ∀ r : ℝ, C ω r = brownianDrivingPath B ω r)
    (H : C(Icc 0 (s : ℝ), E) → ℝ) (hH : Measurable H)
    (hHb : ∃ N : ℝ, ∀ h, ‖H h‖ ≤ N) :
    (∫ ω, H ((C ω).restrict (Icc 0 (s : ℝ))) * f (langevinProcess V B x₀ (s + t) ω) ∂P) =
      ∫ ω, H ((C ω).restrict (Icc 0 (s : ℝ))) *
        (∫ y, f y ∂langevinKernel V B P t (langevinProcess V B x₀ s ω)) ∂P := by
  let := hB.isProbabilityMeasure
  let history : Ω → C(Icc 0 (s : ℝ), E) := fun ω => (C ω).restrict (Icc 0 (s : ℝ))
  let future := brownianContinuousDrivingPath (fun r ω => B (s + r) ω - B s ω)
  let A : C(Icc 0 (s : ℝ), E) → E := fun h => intervalLangevinEvaluation V s.property (x₀, h)
  have hmA : Continuous A := (intervalLangevinEvaluation_continuous hV κ hκ hHess s.property).comp
    (continuous_const.prodMk continuous_id)
  have hmHist : Measurable history := (ContinuousMap.continuous_restrict _).measurable.comp hC
  have hmFuture : AEMeasurable future P := brownianContinuousDrivingPath_aemeasurable (hB.shift s)
  have hHistEq : history =ᵐ[P] fun ω => (brownianContinuousDrivingPath B ω).restrict (Icc 0 (s : ℝ)) := by
    filter_upwards [hCeq, brownianContinuousDrivingPath_coe_ae hB] with ω hCω hraw
    apply ContinuousMap.ext
    intro r
    exact (hCω r).trans (congrFun hraw r).symm
  have hindep : IndepFun history future P :=
    (brownianContinuousDrivingPath_indep_history hB s).symm.congr hHistEq.symm Filter.EventuallyEq.rfl
  have hstate : (fun ω => A (history ω)) =ᵐ[P] langevinProcess V B x₀ s := by
    filter_upwards [hCeq] with ω hCω
    have hraw : (C ω : ℝ → E) = brownianDrivingPath B ω := funext hCω
    exact (intervalLangevinEvaluation_restrict hV κ hκ hHess s.property x₀ (C ω)).trans
      (congrArg (fun w => langevinSolution V w x₀ (s : ℝ)) hraw)
  let F : C(Icc 0 (s : ℝ), E) × C(ℝ, E) → ℝ := fun p => H p.1 * f (langevinEvaluation V t (A p.1, p.2))
  have hmF : Measurable F := hH.comp measurable_fst |>.mul
    (hf.measurable.comp (((langevinEvaluation_continuous hV κ hκ hHess t).comp
      ((hmA.comp continuous_fst).prodMk continuous_snd)).measurable))
  obtain ⟨M, hM⟩ := hfb
  obtain ⟨N, hN⟩ := hHb
  have hbF : ∃ L : ℝ, ∀ p, ‖F p‖ ≤ L := by
    refine ⟨N * M, ?_⟩
    intro p
    exact (norm_mul _ _).trans_le (mul_le_mul (hN _) (hM _) (norm_nonneg _) (by
      have h := hN p.1
      exact (norm_nonneg _).trans h))
  have hi := integral_independent_pair_eq_iterated hmHist.aemeasurable hmFuture hindep hmF hbF
  have hnoise : P.map future = brownianNoiseLaw B P := brownianNoiseLaw_shift hB s
  rw [hnoise] at hi
  calc
    _ = ∫ ω, F (history ω, future ω) ∂P := by
      apply integral_congr_ae
      filter_upwards [hstate, langevinProcess_restart_ae hB hV κ hκ hHess x₀ s t] with ω hsω hrω
      change H (history ω) * f (langevinProcess V B x₀ (s + t) ω) =
        H (history ω) * f (langevinEvaluation V t (A (history ω), future ω))
      rw [hsω, hrω]
    _ = ∫ ω, (∫ w, F (history ω, w) ∂brownianNoiseLaw B P) ∂P := hi
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [hstate] with ω hsω
      change (∫ w, H (history ω) * f (langevinEvaluation V t (A (history ω), w)) ∂brownianNoiseLaw B P) = _
      rw [integral_const_mul, ← integral_langevinKernel_eq_noise_integral hB hV hf κ hκ hHess,
        hsω]

/-- The actual conditional Markov expectation given the whole continuous
noise history, derived from the bounded measurable past-test identity. -/
theorem langevinProcess_condExp_history_markov
    {B : ℝ≥0 → Ω → E} {P : Measure Ω} (hB : IsEuclideanBrownian B P)
    {V f : E → ℝ} (hV : ContDiff ℝ 2 V) (hf : Continuous f)
    (hfb : ∃ M : ℝ, ∀ y, ‖f y‖ ≤ M)
    (κ : ℝ) (hκ : 0 ≤ κ)
    (hHess : ∀ x z, κ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (x₀ : E) (s t : ℝ≥0)
    {C : Ω → C(ℝ, E)} (hC : Measurable C)
    (hCeq : ∀ᵐ ω ∂P, ∀ r : ℝ, C ω r = brownianDrivingPath B ω r) :
    P[fun ω => f (langevinProcess V B x₀ (s + t) ω) |
      MeasurableSpace.comap (fun ω => (C ω).restrict (Icc 0 (s : ℝ))) inferInstance] =ᵐ[P]
      fun ω => ∫ y, f y ∂langevinKernel V B P t (langevinProcess V B x₀ s ω) := by
  classical
  let := hB.isProbabilityMeasure
  let := langevinKernel_isMarkovKernel hB hV κ hκ hHess t
  let history : Ω → C(Icc 0 (s : ℝ), E) := fun ω => (C ω).restrict (Icc 0 (s : ℝ))
  let A : C(Icc 0 (s : ℝ), E) → E := fun h => intervalLangevinEvaluation V s.property (x₀, h)
  let J : E → ℝ := fun x => ∫ y, f y ∂langevinKernel V B P t x
  have hmHist : Measurable history := (ContinuousMap.continuous_restrict _).measurable.comp hC
  have hmA : Measurable A := ((intervalLangevinEvaluation_continuous hV κ hκ hHess s.property).comp
    (continuous_const.prodMk continuous_id)).measurable
  have hmJ : StronglyMeasurable J := hf.measurable.stronglyMeasurable.integral_kernel
  have hstate : (fun ω => A (history ω)) =ᵐ[P] langevinProcess V B x₀ s := by
    filter_upwards [hCeq] with ω hCω
    have hraw : (C ω : ℝ → E) = brownianDrivingPath B ω := funext hCω
    exact (intervalLangevinEvaluation_restrict hV κ hκ hHess s.property x₀ (C ω)).trans
      (congrArg (fun w => langevinSolution V w x₀ (s : ℝ)) hraw)
  obtain ⟨M, hM⟩ := hfb
  have hfint : Integrable (fun ω => f (langevinProcess V B x₀ (s + t) ω)) P :=
    Integrable.mono' (integrable_const M)
      (hf.measurable.comp_aemeasurable (langevinProcess_aemeasurable_eval hB hV κ hκ hHess x₀ (s + t))).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun ω => hM _))
  have hJbound (x : E) : ‖J x‖ ≤ M :=
    langevinKernel_integral_compact_test_norm_le hB hV κ hκ hHess hM t x
  have hJint : Integrable (fun ω => J (A (history ω))) P :=
    Integrable.mono' (integrable_const M)
      ((hmJ.measurable.comp hmA).comp hmHist).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun ω => hJbound _))
  have hgm : AEStronglyMeasurable[MeasurableSpace.comap history inferInstance]
      (fun ω => J (A (history ω))) P :=
    ((hmJ.measurable.comp hmA).comp (comap_measurable history)).stronglyMeasurable.aestronglyMeasurable
  have hcond := ae_eq_condExp_of_forall_setIntegral_eq hmHist.comap_le hfint
    (fun S _ _ => hJint.integrableOn) (g := fun ω => J (A (history ω))) ?_ hgm
  · exact hcond.symm.trans (hstate.mono (fun ω hω => congrArg J hω))
  · rintro S ⟨D, hD, rfl⟩ _
    let H : C(Icc 0 (s : ℝ), E) → ℝ := D.indicator (fun _ => 1)
    have hmH : Measurable H := measurable_const.indicator hD
    have hbH : ∃ N : ℝ, ∀ h, ‖H h‖ ≤ N := by
      refine ⟨1, ?_⟩
      intro h
      by_cases hh : h ∈ D <;> simp [H, hh]
    have hw := langevinProcess_past_test_markov_identity hB hV hf ⟨M, hM⟩ κ hκ hHess x₀ s t hC hCeq H hmH hbH
    calc
      _ = ∫ ω, H (history ω) * J (langevinProcess V B x₀ s ω) ∂P := by
        rw [← integral_indicator (hmHist hD)]
        apply integral_congr_ae
        filter_upwards [hstate] with ω hω
        by_cases hh : history ω ∈ D <;> simp [H, hh, hω]
      _ = ∫ ω, H (history ω) * f (langevinProcess V B x₀ (s + t) ω) ∂P := hw.symm
      _ = _ := by
        rw [← integral_indicator (hmHist hD)]
        apply integral_congr_ae
        exact Filter.Eventually.of_forall (fun ω => by by_cases hh : history ω ∈ D <;> simp [H, hh])

/-- Actual conditional Dynkin expectation given the complete noise history.
The right side is the integral of the genuine transition expectation of Lf;
turning it into conditional expectation of the pathwise compensator is a
separate conditional-Fubini step. -/
theorem langevinProcess_conditional_dynkin_identity
    {B : ℝ≥0 → Ω → E} {P : Measure Ω} (hB : IsEuclideanBrownian B P)
    {V f : E → ℝ} (hV : ContDiff ℝ 2 V) (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (κ : ℝ) (hκ : 0 ≤ κ)
    (hHess : ∀ x z, κ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (x₀ : E) (s t : ℝ≥0)
    {C : Ω → C(ℝ, E)} (hC : Measurable C)
    (hCeq : ∀ᵐ ω ∂P, ∀ r : ℝ, C ω r = brownianDrivingPath B ω r) :
    P[fun ω => f (langevinProcess V B x₀ (s + t) ω) |
      MeasurableSpace.comap (fun ω => (C ω).restrict (Icc 0 (s : ℝ))) inferInstance] =ᵐ[P]
      fun ω => f (langevinProcess V B x₀ s ω) + ∫ r in 0..(t : ℝ),
        (∫ y, langevinDifferentialOperator V f y ∂langevinKernel V B P r.toNNReal (langevinProcess V B x₀ s ω)) := by
  obtain ⟨M, _, hM⟩ := compact_continuous_norm_bound hf.continuous hfc
  have h := langevinProcess_condExp_history_markov hB hV hf.continuous ⟨M, hM⟩ κ hκ hHess x₀ s t hC hCeq
  filter_upwards [h] with ω hω
  rw [hω]
  have hd := langevinKernel_dynkin_identity hB hV hf hfc κ hκ hHess (langevinProcess V B x₀ s ω) t.property
  have htEq : (t : ℝ).toNNReal = t := by
    apply NNReal.eq
    exact Real.coe_toNNReal _ t.property
  convert! hd using 1
  congr 3
  exact htEq.symm

end CutoffRigidity
