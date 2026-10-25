module
public import CutoffRigidity.LangevinDynkin

/-! # Feller continuity of actual bounded continuous expectations

Continuity of the genuine solution evaluation and dominated convergence
prove spatial continuity under the actual Brownian path law.
-/
public section
namespace CutoffRigidity
open MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal
variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

theorem continuous_langevinKernel_integral_initial
    {B : ℝ≥0 → Ω → E} {P : Measure Ω} (hB : IsEuclideanBrownian B P)
    {V g : E → ℝ} (hV : ContDiff ℝ 2 V) (hg : Continuous g)
    (hgb : ∃ M : ℝ, ∀ y, ‖g y‖ ≤ M)
    (ρ : ℝ) (hρ : 0 ≤ ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (t : ℝ≥0) : Continuous (fun x => ∫ y, g y ∂langevinKernel V B P t x) := by
  let := brownianNoiseLaw_isProbabilityMeasure hB
  obtain ⟨M, hM⟩ := hgb
  have he (x : E) : (∫ y, g y ∂langevinKernel V B P t x) =
      ∫ w : C(ℝ, E), g (langevinEvaluation V t (x, w)) ∂brownianNoiseLaw B P := by
    rw [langevinKernel_apply_noiseLaw hB hV ρ hρ hHess]
    exact integral_map
      (((langevinEvaluation_continuous hV ρ hρ hHess t).comp
        (continuous_const.prodMk continuous_id)).measurable.aemeasurable)
      hg.measurable.aestronglyMeasurable
  simp_rw [he]
  apply continuous_iff_continuousAt.mpr
  intro x
  apply tendsto_integral_filter_of_dominated_convergence (fun _ : C(ℝ, E) => M)
  · exact Eventually.of_forall fun z =>
      (hg.comp ((langevinEvaluation_continuous hV ρ hρ hHess t).comp
        (continuous_const.prodMk continuous_id))).measurable.aestronglyMeasurable
  · exact Eventually.of_forall fun z => Eventually.of_forall fun w => hM _
  · exact integrable_const M
  · exact Eventually.of_forall fun w =>
      (hg.comp ((langevinEvaluation_continuous hV ρ hρ hHess t).comp
        (continuous_id.prodMk continuous_const))).tendsto x

/-- Joint time/state continuity follows from the actual uniform same-noise
contraction and continuous sample paths. -/
theorem continuous_langevinSolution_time_initial
    {V : E → ℝ} (hV : ContDiff ℝ 2 V) (ρ : ℝ) (hρ : 0 ≤ ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (w : C(ℝ, E)) :
    Continuous (fun p : ℝ≥0 × E => langevinSolution V w p.2 p.1) := by
  apply continuous_iff_continuousAt.mpr
  intro p
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hc : Continuous (fun s : ℝ≥0 => langevinSolution V w p.2 s) :=
    (langevinSolution_continuousOn hV ρ hρ hHess w.continuous p.2).comp_continuous
      continuous_subtype_val (fun s => s.property)
  have hb : Tendsto (fun q : ℝ≥0 × E => ‖q.2 - p.2‖ +
      ‖langevinSolution V w p.2 q.1 - langevinSolution V w p.2 p.1‖) (𝓝 p) (𝓝 0) := by
    have hbc : Continuous (fun q : ℝ≥0 × E => ‖q.2 - p.2‖ +
        ‖langevinSolution V w p.2 q.1 - langevinSolution V w p.2 p.1‖) := by
      exact ((continuous_snd.sub continuous_const).norm).add
        (((hc.comp continuous_fst).sub continuous_const).norm)
    simpa using hbc.tendsto p
  apply squeeze_zero' (Eventually.of_forall fun q => norm_nonneg _) _ hb
  exact Eventually.of_forall fun q => by
    calc
      _ ≤ ‖langevinSolution V w q.2 q.1 - langevinSolution V w p.2 q.1‖ +
          ‖langevinSolution V w p.2 q.1 - langevinSolution V w p.2 p.1‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ ‖q.2 - p.2‖ + _ := by
        gcongr
        exact (langevinSolution_initial_point_contraction hV ρ hρ hHess w.continuous
          q.2 p.2 q.1.property).trans (mul_le_of_le_one_left (norm_nonneg _)
            (Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hρ) q.1.property)))

/-- Joint Feller continuity for actual bounded continuous tests. -/
theorem continuous_langevinKernel_integral_time_initial
    {B : ℝ≥0 → Ω → E} {P : Measure Ω} (hB : IsEuclideanBrownian B P)
    {V g : E → ℝ} (hV : ContDiff ℝ 2 V) (hg : Continuous g)
    (hgb : ∃ M : ℝ, ∀ y, ‖g y‖ ≤ M)
    (ρ : ℝ) (hρ : 0 ≤ ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z) :
    Continuous (fun p : ℝ≥0 × E => ∫ y, g y ∂langevinKernel V B P p.1 p.2) := by
  let := brownianNoiseLaw_isProbabilityMeasure hB
  obtain ⟨M, hM⟩ := hgb
  have he (p : ℝ≥0 × E) : (∫ y, g y ∂langevinKernel V B P p.1 p.2) =
      ∫ w : C(ℝ, E), g (langevinSolution V w p.2 p.1) ∂brownianNoiseLaw B P := by
    rw [langevinKernel_apply_noiseLaw hB hV ρ hρ hHess]
    exact integral_map
      (((langevinEvaluation_continuous hV ρ hρ hHess p.1).comp
        (continuous_const.prodMk continuous_id)).measurable.aemeasurable)
      hg.measurable.aestronglyMeasurable
  simp_rw [he]
  apply continuous_iff_continuousAt.mpr
  intro p
  apply tendsto_integral_filter_of_dominated_convergence (fun _ : C(ℝ, E) => M)
  · exact Eventually.of_forall fun q =>
      (hg.comp ((langevinEvaluation_continuous hV ρ hρ hHess q.1).comp
        (continuous_const.prodMk continuous_id))).measurable.aestronglyMeasurable
  · exact Eventually.of_forall fun q => Eventually.of_forall fun w => hM _
  · exact integrable_const M
  · exact Eventually.of_forall fun w =>
      (hg.comp (continuous_langevinSolution_time_initial hV ρ hρ hHess w)).tendsto p

end CutoffRigidity
