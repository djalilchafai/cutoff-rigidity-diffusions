module

public import CutoffRigidity.LangevinSpacetimeConditional

/-! # Genuine continuous Langevin space-time compensated tests

The actual moving compensator is adapted and integrable. The martingale
identity is derived from conditional space-time Dynkin increments, under
explicit compact smooth test and source-domain hypotheses.
-/

public section

namespace CutoffRigidity

open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal BoundedContinuousFunction

variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

/-- An actual time-integrated test of the continuous solution is adapted,
proved by restricting and extending the actual noise history. -/
theorem continuousLangevinVersion_moving_integral_stronglyMeasurable_history
    {V : E → ℝ} (hV : ContDiff ℝ 2 V) (g : ℝ → E →ᵇ ℝ) (hg : Continuous g)
    (κ : ℝ) (hκ : 0 ≤ κ)
    (hHess : ∀ x z, κ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    {C : Ω → C(ℝ, E)} (hC : Measurable C) (x₀ : E) (t : ℝ≥0) :
    StronglyMeasurable[drivingHistoryFiltration hC t]
      (fun ω => ∫ r in 0..(t : ℝ), g r (continuousLangevinVersion V C x₀ r.toNNReal ω)) := by
  let η : Measure ℝ := volume.restrict (Ioc 0 (t : ℝ))
  have : IsFiniteMeasure η := by dsimp [η]; infer_instance
  let Cext := historyNoiseExtension (d := d) t
  have hmExt : Measurable Cext := historyNoiseExtension_measurable t
  have hJ : StronglyMeasurable (Function.uncurry (fun r : ℝ => fun w : C(Icc 0 (t : ℝ), E) =>
      g r (continuousLangevinVersion V Cext x₀ r.toNNReal w))) := by
    apply stronglyMeasurable_uncurry_of_continuous_of_stronglyMeasurable
    · intro w
      exact continuous_eval.comp (hg.prodMk
        ((continuousLangevinVersion_continuous hV κ hκ hHess Cext x₀ w).comp continuous_real_toNNReal))
    · intro r
      exact ((g r).continuous.measurable.comp (continuousLangevinVersion_measurable hV κ hκ hHess hmExt x₀ _)).stronglyMeasurable
  have hQ : StronglyMeasurable (fun w : C(Icc 0 (t : ℝ), E) => ∫ r,
      g r (continuousLangevinVersion V Cext x₀ r.toNNReal w) ∂η) := hJ.integral_prod_left
  have heq : (fun ω => ∫ r in 0..(t : ℝ), g r (continuousLangevinVersion V C x₀ r.toNNReal ω)) =
      fun ω => ∫ r, g r (continuousLangevinVersion V Cext x₀ r.toNNReal (drivingHistory C t ω)) ∂η := by
    funext ω
    calc
      _ = ∫ r in 0..(t : ℝ), g r (continuousLangevinVersion V Cext x₀ r.toNNReal (drivingHistory C t ω)) := by
        apply intervalIntegral.integral_congr
        intro r hr
        have hr' : r ∈ Icc 0 (t : ℝ) :=
          ⟨(le_min le_rfl t.property).trans hr.1, hr.2.trans (max_le t.property le_rfl)⟩
        have hp := langevinSolution_eqOn_of_noise_eqOn hV κ hκ hHess (C ω).continuous
          (Cext (drivingHistory C t ω)).continuous x₀ t.property (fun a ha => ?_)
        · have hmem : ((r.toNNReal : ℝ)) ∈ Icc 0 (t : ℝ) := by
            rw [Real.coe_toNNReal _ hr'.1]
            exact hr'
          exact congrArg (g r) (hp hmem)
        · exact (IccExtend_of_mem t.property (drivingHistory C t ω) ha).symm
      _ = _ := intervalIntegral.integral_of_le t.property
  rw [heq]
  exact hQ.comp_measurable (comap_measurable (drivingHistory C t))


/-- The actual compensated moving test on the measurable continuous process. -/
@[expose] noncomputable def langevinSpacetimeDynkinProcess (V : E → ℝ)
    (q g : ℝ → E →ᵇ ℝ) (C : Ω → C(ℝ, E)) (x₀ : E) (t : NNReal) (ω : Ω) : ℝ :=
  q t (continuousLangevinVersion V C x₀ t ω) - q 0 x₀ -
    ∫ r in 0..(t : ℝ), g r (continuousLangevinVersion V C x₀ r.toNNReal ω)

/-- The genuine moving compensated test is strongly adapted. -/
theorem langevinSpacetimeDynkinProcess_stronglyAdapted
    {V : E → ℝ} (hV : ContDiff ℝ 2 V) (q g : ℝ → E →ᵇ ℝ) (hg : Continuous g)
    (κ : ℝ) (hκ : 0 ≤ κ)
    (hHess : ∀ x z, κ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    {C : Ω → C(ℝ, E)} (hC : Measurable C) (x₀ : E) :
    StronglyAdapted (drivingHistoryFiltration hC) (langevinSpacetimeDynkinProcess V q g C x₀) := by
  intro t
  exact (((q t).continuous.measurable.comp
    (continuousLangevinVersion_stronglyAdapted hV κ hκ hHess hC x₀ t).measurable).stronglyMeasurable.sub
      stronglyMeasurable_const).sub
    (continuousLangevinVersion_moving_integral_stronglyMeasurable_history hV g hg κ hκ hHess hC x₀ t)

/-- True integrability at each time follows from bounded spatial tests and source. -/
theorem langevinSpacetimeDynkinProcess_integrable
    {P : Measure Ω} [IsProbabilityMeasure P]
    {V : E → ℝ} (hV : ContDiff ℝ 2 V) (q g : ℝ → E →ᵇ ℝ) (hg : Continuous g)
    (hgb : ∃ M : ℝ, ∀ r x, ‖g r x‖ ≤ M)
    (κ : ℝ) (hκ : 0 ≤ κ)
    (hHess : ∀ x z, κ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    {C : Ω → C(ℝ, E)} (hC : Measurable C) (x₀ : E) (t : NNReal) :
    Integrable (langevinSpacetimeDynkinProcess V q g C x₀ t) P := by
  have hi : Integrable (fun ω => q t (continuousLangevinVersion V C x₀ t ω)) P :=
    Integrable.mono' (integrable_const ‖q t‖)
      ((q t).continuous.measurable.comp
        (continuousLangevinVersion_measurable hV κ hκ hHess hC x₀ t)).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun ω => (q t).norm_coe_le_norm _))
  have hc := continuousLangevinVersion_moving_integral_integrable (P := P) hV g hg hgb κ hκ hHess hC x₀ 0 t
  change Integrable (fun ω => q t (continuousLangevinVersion V C x₀ t ω) - q 0 x₀ -
    ∫ r in 0..(t : ℝ), g r (continuousLangevinVersion V C x₀ r.toNNReal ω)) P
  convert! (hi.sub (integrable_const (q 0 x₀))).sub hc using 1
  funext ω
  simp only [Pi.sub_apply, zero_add]

omit [MeasurableSpace Ω] in
/-- The genuine moving compensated test has continuous sample paths. -/
theorem langevinSpacetimeDynkinProcess_continuous
    {V : E → ℝ} (hV : ContDiff ℝ 2 V) (q g : ℝ → E →ᵇ ℝ)
    (hq : Continuous q) (hg : Continuous g)
    (κ : ℝ) (hκ : 0 ≤ κ)
    (hHess : ∀ x z, κ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (C : Ω → C(ℝ, E)) (x₀ : E) (ω : Ω) :
    Continuous (fun t => langevinSpacetimeDynkinProcess V q g C x₀ t ω) := by
  have hp := continuousLangevinVersion_continuous hV κ hκ hHess C x₀ ω
  have hval : Continuous (fun t : NNReal => q t (continuousLangevinVersion V C x₀ t ω)) :=
    continuous_eval.comp ((hq.comp continuous_subtype_val).prodMk hp)
  have hsrc : Continuous (fun r : ℝ => g r (continuousLangevinVersion V C x₀ r.toNNReal ω)) :=
    continuous_eval.comp (hg.prodMk (hp.comp continuous_real_toNNReal))
  have hprimitive := (intervalIntegral.differentiable_integral_of_continuous (a := 0) hsrc).continuous.comp
    (continuous_subtype_val : Continuous (fun t : NNReal => (t : ℝ)))
  exact (hval.sub continuous_const).sub hprimitive

omit [MeasurableSpace Ω] in
/-- Splitting an actual path compensator at time s gives the future shifted integral. -/
theorem continuousLangevinVersion_moving_integral_add
    {V : E → ℝ} (hV : ContDiff ℝ 2 V) (g : ℝ → E →ᵇ ℝ) (hg : Continuous g)
    (κ : ℝ) (hκ : 0 ≤ κ)
    (hHess : ∀ x z, κ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (C : Ω → C(ℝ, E)) (x₀ : E) (s u : ℝ≥0) (ω : Ω) :
    (∫ r in 0..((s + u : ℝ≥0) : ℝ), g r (continuousLangevinVersion V C x₀ r.toNNReal ω)) =
      (∫ r in 0..(s : ℝ), g r (continuousLangevinVersion V C x₀ r.toNNReal ω)) +
        ∫ r in 0..(u : ℝ), g ((s : ℝ) + r) (continuousLangevinVersion V C x₀ (s + r.toNNReal) ω) := by
  let a : ℝ → ℝ := fun r => g r (continuousLangevinVersion V C x₀ r.toNNReal ω)
  have ha : Continuous a := continuous_eval.comp (hg.prodMk
    ((continuousLangevinVersion_continuous hV κ hκ hHess C x₀ ω).comp continuous_real_toNNReal))
  have hshift : (∫ r in 0..(u : ℝ), g ((s : ℝ) + r) (continuousLangevinVersion V C x₀ (s + r.toNNReal) ω)) =
      ∫ r in (s : ℝ)..((s : ℝ) + u), a r := by
    calc
      _ = ∫ r in 0..(u : ℝ), a ((s : ℝ) + r) := by
        apply intervalIntegral.integral_congr
        intro r hr
        have hr' : 0 ≤ r := (le_min le_rfl u.property).trans hr.1
        have htime : s + r.toNNReal = ((s : ℝ) + r).toNNReal := by
          apply NNReal.eq
          rw [NNReal.coe_add, Real.coe_toNNReal _ hr']
          exact (Real.coe_toNNReal _ (add_nonneg s.property hr')).symm
        change g ((s : ℝ) + r) (continuousLangevinVersion V C x₀ (s + r.toNNReal) ω) = _
        rw [htime]
      _ = _ := by simpa only [add_zero] using intervalIntegral.integral_comp_add_left (a := 0) (b := (u : ℝ)) a (s : ℝ)
  rw [hshift, NNReal.coe_add]
  exact (intervalIntegral.integral_add_adjacent_intervals
    (ha.intervalIntegrable 0 (s : ℝ)) (ha.intervalIntegrable (s : ℝ) ((s : ℝ) + u))).symm


/-- The actual compensated moving test satisfies the martingale increment
identity whenever its genuine differential equation holds on that interval. -/
theorem langevinSpacetimeDynkinProcess_condExp_add
    {B : NNReal → Ω → E} {P : Measure Ω} (hB : IsEuclideanBrownian B P)
    {V : E → ℝ} (hV : ContDiff ℝ 2 V) (κ : ℝ) (hκ : 0 ≤ κ)
    (hHess : ∀ x z : E, κ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (q q' g : ℝ → E →ᵇ ℝ) (hqcont : Continuous q) (hgcont : Continuous g)
    (hgb : ∃ M : ℝ, ∀ r x, ‖g r x‖ ≤ M) (x₀ : E) (s u : NNReal)
    (hq : ∀ r ∈ Ioo (s : ℝ) ((s : ℝ) + u), HasDerivAt q (q' r) r)
    (hqs : ∀ r ∈ Ioo (s : ℝ) ((s : ℝ) + u), ContDiff ℝ 2 (q r))
    (hqsc : ∀ r ∈ Ioo (s : ℝ) ((s : ℝ) + u), HasCompactSupport (q r))
    (hsource : ∀ r x, g r x = q' r x + langevinDifferentialOperator V (q r) x)
    {C : Ω → C(ℝ, E)} (hC : Measurable C)
    (hCeq : ∀ᵐ ω ∂P, ∀ r : ℝ, C ω r = brownianDrivingPath B ω r) :
    P[langevinSpacetimeDynkinProcess V q g C x₀ (s + u) |
      drivingHistoryFiltration hC s] =ᵐ[P] langevinSpacetimeDynkinProcess V q g C x₀ s := by
  have := hB.isProbabilityMeasure
  let ambient : MeasurableSpace Ω := ‹MeasurableSpace Ω›
  let σ := drivingHistoryFiltration hC s
  let : MeasurableSpace Ω := ambient
  let past (ω : Ω) := ∫ r in 0..(s : ℝ), g r (continuousLangevinVersion V C x₀ r.toNNReal ω)
  let future (ω : Ω) := ∫ r in 0..(u : ℝ), g ((s : ℝ) + r)
    (continuousLangevinVersion V C x₀ (s + r.toNNReal) ω)
  let Z (ω : Ω) := q ((s : ℝ) + u) (continuousLangevinVersion V C x₀ (s + u) ω) - future ω
  have hipast : Integrable past P := by
    have hh := continuousLangevinVersion_moving_integral_integrable (P := P) hV g hgcont hgb
      κ hκ hHess hC x₀ 0 s
    simpa only [zero_add, past] using hh
  have hifuture : Integrable future P := continuousLangevinVersion_moving_integral_integrable
    hV (fun r => g ((s : ℝ) + r)) (hgcont.comp (continuous_const.add continuous_id))
    (by obtain ⟨M,hM⟩ := hgb; exact ⟨M,fun r x => hM _ x⟩) κ hκ hHess hC x₀ s u
  have hiF : Integrable (fun ω => q ((s : ℝ) + u) (continuousLangevinVersion V C x₀ (s + u) ω)) P :=
    Integrable.mono' (integrable_const ‖q ((s : ℝ) + u)‖)
      ((q ((s : ℝ) + u)).continuous.measurable.comp
        (continuousLangevinVersion_measurable hV κ hκ hHess hC x₀ (s + u))).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun ω => (q ((s : ℝ) + u)).norm_coe_le_norm _))
  have hiZ : Integrable Z P := hiF.sub hifuture
  have hCZ := continuousLangevinVersion_conditional_spacetime_dynkin hB hV κ hκ hHess
    q q' g hqcont hgcont hgb x₀ s u hq hqs hqsc hsource hC hCeq
  have hmPast : StronglyMeasurable[σ] past :=
    continuousLangevinVersion_moving_integral_stronglyMeasurable_history hV g hgcont κ hκ hHess hC x₀ s
  have hσle : σ ≤ ambient := (drivingHistoryFiltration hC).le s
  have hCP := condExp_of_stronglyMeasurable hσle hmPast hipast
  have hCC := condExp_const (μ := P) hσle (q 0 x₀)
  have heq : langevinSpacetimeDynkinProcess V q g C x₀ (s + u) = (Z - fun _ => q 0 x₀) - past := by
    funext ω
    unfold langevinSpacetimeDynkinProcess
    rw [continuousLangevinVersion_moving_integral_add hV g hgcont κ hκ hHess C x₀ s u ω]
    dsimp only [Z, past, future, Pi.sub_apply]
    rw [NNReal.coe_add]
    ring
  rw [heq]
  have hC1 := condExp_sub hiZ (integrable_const (q 0 x₀)) σ
  have hC2 := condExp_sub (hiZ.sub (integrable_const (q 0 x₀))) hipast σ
  filter_upwards [hC1, hC2, hCZ] with ω h1 h2 hz
  simp only [Pi.sub_apply] at h1 h2
  change P[Z | σ] ω = _ at hz
  rw [h2, h1, hz, hCC, hCP]
  rfl

/-- For genuine globally defined compact smooth moving tests, the actual
space-time compensated process is a martingale of the actual history. -/
theorem langevinSpacetimeDynkinProcess_martingale
    {B : NNReal → Ω → E} {P : Measure Ω} (hB : IsEuclideanBrownian B P)
    {V : E → ℝ} (hV : ContDiff ℝ 2 V) (κ : ℝ) (hκ : 0 ≤ κ)
    (hHess : ∀ x z : E, κ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (q q' g : ℝ → E →ᵇ ℝ) (hqcont : Continuous q) (hgcont : Continuous g)
    (hgb : ∃ M : ℝ, ∀ r x, ‖g r x‖ ≤ M) (x₀ : E)
    (hq : ∀ r > 0, HasDerivAt q (q' r) r)
    (hqs : ∀ r > 0, ContDiff ℝ 2 (q r))
    (hqsc : ∀ r > 0, HasCompactSupport (q r))
    (hsource : ∀ r x, g r x = q' r x + langevinDifferentialOperator V (q r) x)
    {C : Ω → C(ℝ, E)} (hC : Measurable C)
    (hCeq : ∀ᵐ ω ∂P, ∀ r : ℝ, C ω r = brownianDrivingPath B ω r) :
    Martingale (langevinSpacetimeDynkinProcess V q g C x₀) (drivingHistoryFiltration hC) P := by
  refine ⟨langevinSpacetimeDynkinProcess_stronglyAdapted hV q g hgcont κ hκ hHess hC x₀, ?_⟩
  intro s t hst
  have hh := langevinSpacetimeDynkinProcess_condExp_add hB hV κ hκ hHess q q' g hqcont hgcont hgb
    x₀ s (t - s)
    (fun r hr => hq r (s.property.trans_lt hr.1))
    (fun r hr => hqs r (s.property.trans_lt hr.1))
    (fun r hr => hqsc r (s.property.trans_lt hr.1)) hsource hC hCeq
  simpa only [add_tsub_cancel_of_le hst] using hh

end CutoffRigidity
