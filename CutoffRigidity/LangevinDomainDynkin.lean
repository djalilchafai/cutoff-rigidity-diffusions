module
public import CutoffRigidity.LangevinFeller
public import CutoffRigidity.LangevinL2Operator
public import CutoffRigidity.L2TimeIntegral

/-! # Pointwise evolution from the actual closed generator domain

The Hilbert Duhamel identity is upgraded to every initial state using
bounded representatives, genuine Fubini, Feller continuity and Gibbs full
support. No classical second derivative of the test function is required.
-/
public section
namespace CutoffRigidity
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal
variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

theorem langevinKernel_integral_coeFn_of_bounded
    {B : ℝ≥0 → Ω → E} {P : Measure Ω} (hB : IsEuclideanBrownian B P)
    {V f : E → ℝ} (hV : ContDiff ℝ 2 V) (hp : IsProbabilityMeasure (gibbsMeasure volume V))
    (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (hf : MemLp f 2 (gibbsMeasure volume V)) (t : ℝ≥0) :
    gibbsHeatSemigroup hV hp ρ hρ hHess t (hf.toLp f) =ᵐ[gibbsMeasure volume V]
      fun x => ∫ y, f y ∂langevinKernel V B P t x := by
  rw [← langevinL2Operator_eq_gibbsHeatSemigroup hB hV hp ρ hρ hHess]
  exact (langevinL2Operator_coeFn hB hV hp ρ hρ hHess t (hf.toLp f)).trans
    (invariantKernel_integral_congr_ae (langevinKernel V B P t)
      (langevinKernel_gibbs_invariant hB hV hp ρ hρ hHess t) hf.coeFn_toLp)

theorem langevinKernel_dynkin_of_operatorGraph
    {B : ℝ≥0 → Ω → E} {P : Measure Ω} (hB : IsEuclideanBrownian B P)
    {V f h : E → ℝ} (hV : ContDiff ℝ 2 V) (hp : IsProbabilityMeasure (gibbsMeasure volume V))
    (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (hf : Continuous f) (hh : Continuous h)
    (hfB : ∃ M : ℝ, ∀ x, ‖f x‖ ≤ M) (hhB : ∃ M : ℝ, ∀ x, ‖h x‖ ≤ M)
    (hfm : MemLp f 2 (gibbsMeasure volume V)) (hhm : MemLp h 2 (gibbsMeasure volume V))
    (hg : (hfm.toLp f, hhm.toLp h) ∈ (gibbsPositiveGenerator hV hp).graph)
    (t : ℝ≥0) (x : E) :
    (∫ y, f y ∂langevinKernel V B P t x) = f x -
      ∫ s in (0 : ℝ)..(t : ℝ), ∫ y, h y ∂langevinKernel V B P s.toNNReal x := by
  let := hp
  let μ := gibbsMeasure volume V
  let Q := gibbsHeatSemigroup hV hp ρ hρ hHess
  let F : ℝ → E → ℝ := fun s x => ∫ y, h y ∂langevinKernel V B P s.toNNReal x
  obtain ⟨M, hM⟩ := hhB
  have hM0 : 0 ≤ M := (norm_nonneg (h 0)).trans (hM 0)
  have hFB (s : ℝ) (x : E) : ‖F s x‖ ≤ M := by
    let := langevinKernel_isMarkovKernel hB hV ρ hρ.le hHess s.toNNReal
    simpa [F] using
      norm_integral_le_of_norm_le_const (μ := langevinKernel V B P s.toNNReal x)
        (Eventually.of_forall hM)
  have hFmeas : StronglyMeasurable (Function.uncurry F) := by
    apply stronglyMeasurable_uncurry_of_continuous_of_stronglyMeasurable
    · intro x
      exact (continuous_langevinKernel_integral_of_bounded_continuous hB hV hh
        ⟨M, hM⟩ ρ hρ.le hHess x).comp continuous_real_toNNReal
    · intro s
      exact hh.measurable.stronglyMeasurable.integral_kernel
  have hQcont : Continuous (fun s : ℝ => Q s.toNNReal (hhm.toLp h)) :=
    (continuous_gibbsHeatSemigroup_apply hV hp ρ hρ hHess _).comp continuous_real_toNNReal
  have hI := coeFn_integral_L2_of_bounded (volume.restrict (Ioc (0 : ℝ) (t : ℝ))) μ
    (fun s : ℝ => Q s.toNNReal (hhm.toLp h))
    (hQcont.integrableOn_Icc.mono_set Ioc_subset_Icc_self) F hFmeas M hM0 hFB
    (fun s => langevinKernel_integral_coeFn_of_bounded hB hV hp ρ hρ hHess hhm s.toNNReal)
  have hI' : (∫ s in (0 : ℝ)..(t : ℝ), Q s.toNNReal (hhm.toLp h)) =ᵐ[μ]
      fun x => ∫ s in (0 : ℝ)..(t : ℝ), F s x := by
    have hq : (∫ s in (0 : ℝ)..(t : ℝ), Q s.toNNReal (hhm.toLp h)) =
        ∫ s in Ioc (0 : ℝ) (t : ℝ), Q s.toNNReal (hhm.toLp h) :=
      intervalIntegral.integral_of_le t.property
    have hs (y : E) : (∫ s in (0 : ℝ)..(t : ℝ), F s y) =
        ∫ s in Ioc (0 : ℝ) (t : ℝ), F s y := intervalIntegral.integral_of_le t.property
    calc
      _ =ᵐ[μ] (∫ s in Ioc (0 : ℝ) (t : ℝ), Q s.toNNReal (hhm.toLp h)) := by rw [hq]
      _ =ᵐ[μ] fun y => ∫ s in Ioc (0 : ℝ) (t : ℝ), F s y := hI
      _ =ᵐ[μ] fun y => ∫ s in (0 : ℝ)..(t : ℝ), F s y :=
        Eventually.of_forall fun y => (hs y).symm
  have hAE : (fun x => ∫ y, f y ∂langevinKernel V B P t x) =ᵐ[μ]
      fun x => f x - ∫ s in (0 : ℝ)..(t : ℝ), F s x := by
    have hD := gibbsHeatSemigroup_integral_of_graph hV hp ρ hρ hHess t
      (hfm.toLp f) (hhm.toLp h) hg
    have hS := Lp.coeFn_sub (hfm.toLp f)
      (∫ s in (0 : ℝ)..(t : ℝ), Q s.toNNReal (hhm.toLp h))
    filter_upwards [langevinKernel_integral_coeFn_of_bounded hB hV hp ρ hρ hHess hfm t,
      hfm.coeFn_toLp, hS, hI'] with y hy hfY hs hi
    rw [← hy, hD, hs, Pi.sub_apply, hfY, hi]
  have hIntCont : Continuous (fun x => ∫ s in (0 : ℝ)..(t : ℝ), F s x) := by
    have he : (fun x => ∫ s in (0 : ℝ)..(t : ℝ), F s x) =
        fun x => ∫ s in Ioc (0 : ℝ) (t : ℝ), F s x := by
      funext y
      exact intervalIntegral.integral_of_le t.property
    rw [he]
    apply continuous_iff_continuousAt.mpr
    intro x
    apply tendsto_integral_filter_of_dominated_convergence (fun _ : ℝ => M)
    · exact Eventually.of_forall fun z =>
        (hFmeas.comp_measurable measurable_prodMk_right).aestronglyMeasurable
    · exact Eventually.of_forall fun z => Eventually.of_forall fun s => hFB s z
    · exact integrable_const M
    · exact Eventually.of_forall fun s =>
        (continuous_langevinKernel_integral_initial hB hV hh ⟨M,hM⟩ ρ hρ.le hHess s.toNNReal).tendsto x
  exact congrFun (gibbsMeasure_eq_of_ae_eq volume hV.continuous.measurable
    (continuous_langevinKernel_integral_initial hB hV hf hfB ρ hρ.le hHess t)
    (hf.sub hIntCont) hAE) x

/-- Genuine pointwise time differentiation on the closed generator domain. -/
theorem hasDerivAt_langevinKernel_integral_operatorGraph
    {B : ℝ≥0 → Ω → E} {P : Measure Ω} (hB : IsEuclideanBrownian B P)
    {V f h : E → ℝ} (hV : ContDiff ℝ 2 V) (hp : IsProbabilityMeasure (gibbsMeasure volume V))
    (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (hf : Continuous f) (hh : Continuous h)
    (hfB : ∃ M : ℝ, ∀ x, ‖f x‖ ≤ M) (hhB : ∃ M : ℝ, ∀ x, ‖h x‖ ≤ M)
    (hfm : MemLp f 2 (gibbsMeasure volume V)) (hhm : MemLp h 2 (gibbsMeasure volume V))
    (hg : (hfm.toLp f, hhm.toLp h) ∈ (gibbsPositiveGenerator hV hp).graph)
    (x : E) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun r : ℝ => ∫ y, f y ∂langevinKernel V B P r.toNNReal x)
      (-(∫ y, h y ∂langevinKernel V B P t.toNNReal x)) t := by
  have hc := (continuous_langevinKernel_integral_of_bounded_continuous hB hV hh hhB
    ρ hρ.le hHess x).comp continuous_real_toNNReal
  have hd := (intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable 0 t)
    hc.aestronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt).const_sub (f x)
  apply hd.congr_of_eventuallyEq
  filter_upwards [eventually_gt_nhds ht] with r hr
  have he := langevinKernel_dynkin_of_operatorGraph hB hV hp ρ hρ hHess hf hh hfB hhB
    hfm hhm hg r.toNNReal x
  convert! he using 1 <;> simp only [Real.coe_toNNReal r hr.le, Function.comp_apply]

end CutoffRigidity
