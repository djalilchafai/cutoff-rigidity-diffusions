module

public import CutoffRigidity.LangevinHistoryFiltration

/-! # The genuine Langevin Dynkin martingale

Compact C² tests have a bounded continuous generator. Actual conditional
Markov means, the proved conditional-Fubini compensator identity and genuine
history adaptation prove the martingale property. A continuous measurable
realization is used because the original Brownian predicate requires only
a.e. measurable evaluations; indistinguishability with the original actual
Dynkin functional is proved explicitly.
-/

public section

namespace CutoffRigidity

open Set MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology

variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

/-- Actual time-integrated bounded continuous tests are integrable random variables. -/
theorem continuousLangevinVersion_integral_integrable
    {P : Measure Ω} [IsProbabilityMeasure P]
    {V g : E → ℝ} (hV : ContDiff ℝ 2 V) (hg : Continuous g)
    (hgb : ∃ N : ℝ, ∀ x, ‖g x‖ ≤ N)
    (κ : ℝ) (hκ : 0 ≤ κ)
    (hHess : ∀ x z, κ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    {C : Ω → C(ℝ, E)} (hC : Measurable C) (x₀ : E) (t : ℝ≥0) :
    Integrable (fun ω => ∫ r in 0..(t : ℝ), g (continuousLangevinVersion V C x₀ r.toNNReal ω)) P := by
  obtain ⟨N, hN⟩ := hgb
  have hm := (continuousLangevinVersion_integral_stronglyMeasurable_history hV hg κ hκ hHess hC x₀ t).mono
    (drivingHistoryFiltration hC |>.le t)
  apply Integrable.mono' (integrable_const (N * (t : ℝ))) hm.aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro ω
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := 0) (b := (t : ℝ)) (f := fun r => g (continuousLangevinVersion V C x₀ r.toNNReal ω))
    (C := N) (fun r _ => hN _)
  simp only [sub_zero] at h
  convert! h using 1
  congr 1
  exact (abs_of_nonneg t.property).symm

omit [MeasurableSpace Ω] in
/-- Splitting an actual path compensator at time s gives the future shifted integral. -/
theorem continuousLangevinVersion_integral_add
    {V g : E → ℝ} (hV : ContDiff ℝ 2 V) (hg : Continuous g)
    (κ : ℝ) (hκ : 0 ≤ κ)
    (hHess : ∀ x z, κ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (C : Ω → C(ℝ, E)) (x₀ : E) (s u : ℝ≥0) (ω : Ω) :
    (∫ r in 0..((s + u : ℝ≥0) : ℝ), g (continuousLangevinVersion V C x₀ r.toNNReal ω)) =
      (∫ r in 0..(s : ℝ), g (continuousLangevinVersion V C x₀ r.toNNReal ω)) +
        ∫ r in 0..(u : ℝ), g (continuousLangevinVersion V C x₀ (s + r.toNNReal) ω) := by
  let a : ℝ → ℝ := fun r => g (continuousLangevinVersion V C x₀ r.toNNReal ω)
  have ha : Continuous a := (hg.comp (continuousLangevinVersion_continuous hV κ hκ hHess C x₀ ω)).comp
    continuous_real_toNNReal
  have hshift : (∫ r in 0..(u : ℝ), g (continuousLangevinVersion V C x₀ (s + r.toNNReal) ω)) =
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
        change g (continuousLangevinVersion V C x₀ (s + r.toNNReal) ω) = _
        rw [htime]
      _ = _ := by simpa only [add_zero] using intervalIntegral.integral_comp_add_left (a := 0) (b := (u : ℝ)) a (s : ℝ)
  rw [hshift, NNReal.coe_add]
  exact (intervalIntegral.integral_add_adjacent_intervals
    (ha.intervalIntegrable 0 (s : ℝ)) (ha.intervalIntegrable (s : ℝ) ((s : ℝ) + u))).symm

/-- Every actual compact-test Dynkin variable is integrable. -/
theorem langevinDynkinProcess_integrable
    {P : Measure Ω} [IsProbabilityMeasure P]
    {V f : E → ℝ} (hV : ContDiff ℝ 2 V) (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (κ : ℝ) (hκ : 0 ≤ κ)
    (hHess : ∀ x z, κ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    {C : Ω → C(ℝ, E)} (hC : Measurable C) (x₀ : E) (t : ℝ≥0) :
    Integrable (langevinDynkinProcess V f C x₀ t) P := by
  have hiF := integrable_compact_test_comp (P := P) hf.continuous hfc
    (continuousLangevinVersion_measurable hV κ hκ hHess hC x₀ t).aemeasurable
  have hLg := continuous_langevinDifferentialOperator hV hf
  obtain ⟨N, _, hN⟩ := compact_continuous_norm_bound hLg
    (hasCompactSupport_langevinDifferentialOperator V hfc)
  exact (hiF.sub (integrable_const (f x₀))).sub
    (continuousLangevinVersion_integral_integrable hV hLg ⟨N, hN⟩ κ hκ hHess hC x₀ t)

/-- The actual conditional Dynkin increment equation, with its pathwise compensator. -/
theorem langevinDynkinProcess_condExp_add
    {B : ℝ≥0 → Ω → E} {P : Measure Ω} (hB : IsEuclideanBrownian B P)
    {V f : E → ℝ} (hV : ContDiff ℝ 2 V) (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (κ : ℝ) (hκ : 0 ≤ κ)
    (hHess : ∀ x z, κ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (x₀ : E) (s u : ℝ≥0)
    {C : Ω → C(ℝ, E)} (hC : Measurable C)
    (hCeq : ∀ᵐ ω ∂P, ∀ r : ℝ, C ω r = brownianDrivingPath B ω r) :
    P[langevinDynkinProcess V f C x₀ (s + u) | drivingHistoryFiltration hC s] =ᵐ[P]
      langevinDynkinProcess V f C x₀ s := by
  let := hB.isProbabilityMeasure
  let ambient : MeasurableSpace Ω := ‹MeasurableSpace Ω›
  let σ := drivingHistoryFiltration hC s
  let : MeasurableSpace Ω := ambient
  let g := langevinDifferentialOperator V f
  let past : Ω → ℝ := fun ω => ∫ r in 0..(s : ℝ), g (continuousLangevinVersion V C x₀ r.toNNReal ω)
  let future : Ω → ℝ := fun ω => ∫ r in 0..(u : ℝ), g (continuousLangevinVersion V C x₀ (s + r.toNNReal) ω)
  have hg : Continuous g := continuous_langevinDifferentialOperator hV hf
  have hgc : HasCompactSupport g := hasCompactSupport_langevinDifferentialOperator V hfc
  obtain ⟨N, _, hN⟩ := compact_continuous_norm_bound hg hgc
  have hipast : Integrable past P := continuousLangevinVersion_integral_integrable hV hg ⟨N, hN⟩ κ hκ hHess hC x₀ s
  have hifuture : Integrable future P := by
    have hi := (continuousLangevinVersion_integral_integrable hV hg ⟨N, hN⟩ κ hκ hHess hC x₀ (s + u)).sub hipast
    apply hi.congr
    exact Filter.Eventually.of_forall (fun ω => by
      dsimp only [Pi.sub_apply]
      rw [continuousLangevinVersion_integral_add hV hg κ hκ hHess C x₀ s u ω]
      ring)
  have hiF := integrable_compact_test_comp (P := P) hf.continuous hfc
    (continuousLangevinVersion_measurable hV κ hκ hHess hC x₀ (s + u)).aemeasurable
  have hversion := continuousLangevinVersion_eq_process_ae (V := V) hCeq x₀
  have hraw := langevinProcess_conditional_dynkin_identity hB hV hf hfc κ hκ hHess x₀ s u hC hCeq
  have hFv : (fun ω => f (continuousLangevinVersion V C x₀ (s + u) ω)) =ᵐ[P]
      fun ω => f (langevinProcess V B x₀ (s + u) ω) :=
    hversion.mono (fun ω hω => congrArg f (hω _))
  have hRv : (fun ω => f (continuousLangevinVersion V C x₀ s ω) + ∫ r in 0..(u : ℝ),
      ∫ y, g y ∂langevinKernel V B P r.toNNReal (continuousLangevinVersion V C x₀ s ω)) =ᵐ[P]
      fun ω => f (langevinProcess V B x₀ s ω) + ∫ r in 0..(u : ℝ),
        ∫ y, g y ∂langevinKernel V B P r.toNNReal (langevinProcess V B x₀ s ω) := by
    filter_upwards [hversion] with ω hω
    rw [hω s]
  have hCF := (condExp_congr_ae hFv).trans (hraw.trans hRv.symm)
  have hCJ := continuousLangevinVersion_condExp_time_integral hB hV hg hgc κ hκ hHess x₀ s u hC hCeq
  let Z : Ω → ℝ := fun ω => f (continuousLangevinVersion V C x₀ (s + u) ω) - future ω
  have hiZ : Integrable Z P := hiF.sub hifuture
  have hCZ : P[Z | σ] =ᵐ[P] fun ω => f (continuousLangevinVersion V C x₀ s ω) := by
    have hsub := condExp_sub hiF hifuture σ
    filter_upwards [hsub, hCF, hCJ] with ω hsω hFω hJω
    change P[Z | σ] ω = _ at hsω ⊢
    rw [hsω]
    change P[fun ω => f (continuousLangevinVersion V C x₀ (s + u) ω) | σ] ω - P[future | σ] ω = _
    change P[fun ω => f (continuousLangevinVersion V C x₀ (s + u) ω) | σ] ω = _ at hFω
    change P[future | σ] ω = _ at hJω
    rw [hFω, hJω]
    ring
  have hmPast : StronglyMeasurable[σ] past :=
    continuousLangevinVersion_integral_stronglyMeasurable_history hV hg κ hκ hHess hC x₀ s
  have hσle : σ ≤ ‹MeasurableSpace Ω› := drivingHistoryFiltration hC |>.le s
  have hCP := condExp_of_stronglyMeasurable hσle hmPast hipast
  have hCC := condExp_const (μ := P) hσle (f x₀)
  have heq : langevinDynkinProcess V f C x₀ (s + u) = (Z - fun _ => f x₀) - past := by
    funext ω
    change f (continuousLangevinVersion V C x₀ (s + u) ω) - f x₀ -
      (∫ r in 0..((s + u : ℝ≥0) : ℝ), g (continuousLangevinVersion V C x₀ r.toNNReal ω)) = _
    rw [continuousLangevinVersion_integral_add hV hg κ hκ hHess C x₀ s u ω]
    dsimp only [Z, past, future, Pi.sub_apply]
    ring
  rw [heq]
  have hC1 := condExp_sub hiZ (integrable_const (f x₀)) σ
  have hC2 := condExp_sub (hiZ.sub (integrable_const (f x₀))) hipast σ
  filter_upwards [hC1, hC2, hCZ] with ω h1 h2 hz
  simp only [Pi.sub_apply] at h1 h2
  rw [h2, h1, hz, hCC, hCP]
  rfl

/-- The genuine compact-test Dynkin functional is an actual martingale for
the actual history filtration of a measurable continuous realization. -/
theorem langevinDynkinProcess_martingale
    {B : ℝ≥0 → Ω → E} {P : Measure Ω} (hB : IsEuclideanBrownian B P)
    {V f : E → ℝ} (hV : ContDiff ℝ 2 V) (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (κ : ℝ) (hκ : 0 ≤ κ)
    (hHess : ∀ x z, κ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (x₀ : E) {C : Ω → C(ℝ, E)} (hC : Measurable C)
    (hCeq : ∀ᵐ ω ∂P, ∀ r : ℝ, C ω r = brownianDrivingPath B ω r) :
    Martingale (langevinDynkinProcess V f C x₀) (drivingHistoryFiltration hC) P := by
  refine ⟨langevinDynkinProcess_stronglyAdapted hV hf κ hκ hHess hC x₀, ?_⟩
  intro s t hst
  have h := langevinDynkinProcess_condExp_add hB hV hf hfc κ hκ hHess x₀ s (t - s) hC hCeq
  simpa only [add_tsub_cancel_of_le hst] using h

/-- The actual martingale realization agrees with the original constructed
Brownian Langevin Dynkin functional simultaneously at every time a.e. -/
theorem langevinDynkinProcess_eq_actual_ae
    {B : ℝ≥0 → Ω → E} {P : Measure Ω} {V f : E → ℝ}
    {C : Ω → C(ℝ, E)} (hCeq : ∀ᵐ ω ∂P, ∀ r : ℝ, C ω r = brownianDrivingPath B ω r) (x₀ : E) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0, langevinDynkinProcess V f C x₀ t ω =
      f (langevinProcess V B x₀ t ω) - f x₀ -
        ∫ r in 0..(t : ℝ), langevinDifferentialOperator V f (langevinProcess V B x₀ r.toNNReal ω) := by
  filter_upwards [continuousLangevinVersion_eq_process_ae (V := V) hCeq x₀] with ω hω
  intro t
  change f (continuousLangevinVersion V C x₀ t ω) - f x₀ - _ = _
  rw [hω t]
  congr 1
  exact intervalIntegral.integral_congr (fun r _ => congrArg (langevinDifferentialOperator V f) (hω _))

omit [MeasurableSpace Ω] in
/-- The genuine Dynkin martingale has continuous sample paths. -/
theorem langevinDynkinProcess_continuous
    {V f : E → ℝ} (hV : ContDiff ℝ 2 V) (hf : ContDiff ℝ 2 f)
    (κ : ℝ) (hκ : 0 ≤ κ)
    (hHess : ∀ x z, κ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (C : Ω → C(ℝ, E)) (x₀ : E) (ω : Ω) :
    Continuous (fun t : ℝ≥0 => langevinDynkinProcess V f C x₀ t ω) := by
  have hpath := continuousLangevinVersion_continuous hV κ hκ hHess C x₀ ω
  have hsource : Continuous (fun r : ℝ => langevinDifferentialOperator V f
      (continuousLangevinVersion V C x₀ r.toNNReal ω)) :=
    ((continuous_langevinDifferentialOperator hV hf).comp hpath).comp continuous_real_toNNReal
  have hprimitive := (intervalIntegral.differentiable_integral_of_continuous
    (a := 0) hsource).continuous.comp (continuous_subtype_val : Continuous (fun t : ℝ≥0 => (t : ℝ)))
  exact ((hf.continuous.comp hpath).sub continuous_const).sub hprimitive

/-- A genuine continuous integrable Dynkin martingale realization exists for
the actual Brownian Langevin process, with simultaneous a.e. equality to its
original pathwise compensated test functional. No representation premise remains. -/
theorem exists_langevin_dynkin_martingale
    {B : ℝ≥0 → Ω → E} {P : Measure Ω} (hB : IsEuclideanBrownian B P)
    {V f : E → ℝ} (hV : ContDiff ℝ 2 V) (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (κ : ℝ) (hκ : 0 ≤ κ)
    (hHess : ∀ x z, κ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z) (x₀ : E) :
    ∃ (C : Ω → C(ℝ, E)) (hC : Measurable C),
      (∀ᵐ ω ∂P, ∀ r : ℝ, C ω r = brownianDrivingPath B ω r) ∧
      Martingale (langevinDynkinProcess V f C x₀) (drivingHistoryFiltration hC) P ∧
      (∀ t : ℝ≥0, Integrable (langevinDynkinProcess V f C x₀ t) P) ∧
      (∀ ω, Continuous (fun t : ℝ≥0 => langevinDynkinProcess V f C x₀ t ω)) ∧
      (∀ᵐ ω ∂P, ∀ t : ℝ≥0, langevinDynkinProcess V f C x₀ t ω =
        f (langevinProcess V B x₀ t ω) - f x₀ - ∫ r in 0..(t : ℝ),
          langevinDifferentialOperator V f (langevinProcess V B x₀ r.toNNReal ω)) := by
  let := hB.isProbabilityMeasure
  obtain ⟨C, hC, hCeq⟩ := exists_measurable_continuous_driving_version hB
  exact ⟨C, hC, hCeq, langevinDynkinProcess_martingale hB hV hf hfc κ hκ hHess x₀ hC hCeq,
    (fun t => langevinDynkinProcess_integrable hV hf hfc κ hκ hHess hC x₀ t),
    langevinDynkinProcess_continuous hV hf κ hκ hHess C x₀,
    langevinDynkinProcess_eq_actual_ae hCeq x₀⟩

end CutoffRigidity
