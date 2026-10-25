module
public import CutoffRigidity.LangevinEntropyContraction

/-! # Actual Fisher/entropy endpoint estimates by entropy dissipation

The actual full-domain Fisher contraction and genuine kernel semigroup
imply monotonicity. Monotone Fisher is integrable on finite intervals;
actual de Bruijn FTC and nonnegative KL give the endpoint bound.
-/
public section
namespace CutoffRigidity
open MeasureTheory ProbabilityTheory InformationTheory Filter Set
open scoped Topology ENNReal NNReal

/-- The exact entropy FTC argument behind the source endpoint estimate.
Monotonicity supplies integrability of I, so no continuity of Fisher is
postulated. -/
theorem fisher_entropy_endpoint_of_dissipation
    (H I : ℝ → ℝ) (hH : ContinuousOn H (Ici 0))
    (hD : ∀ r, 0 < r → HasDerivAt H (-I r) r)
    (hI : AntitoneOn I (Ici 0)) (hHnonneg : ∀ r, 0 ≤ H r)
    {s t : ℝ} (hs : 0 ≤ s) (hst : s < t) :
    I t ≤ H s / (t - s) := by
  have hII : IntervalIntegrable I volume s t :=
    (hI.mono (by rw [uIcc_of_le hst.le]; intro r hr; exact hs.trans hr.1)).intervalIntegrable
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hst.le
    (hH.mono (fun r hr => hs.trans hr.1))
    (fun r hr => hD r (hs.trans_lt hr.1)) hII.neg
  rw [intervalIntegral.integral_neg] at hFTC
  have hbound := intervalIntegral.integral_mono_on hst.le (intervalIntegrable_const (c := I t)) hII
    (fun r hr => hI (hs.trans hr.1) (hs.trans hst.le) hr.2)
  rw [intervalIntegral.integral_const, smul_eq_mul] at hbound
  apply (le_div_iff₀ (sub_pos.mpr hst)).mpr
  nlinarith only [hFTC, hbound, hHnonneg t]

variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

/-- Full actual Fisher monotonicity, derived from exponential contraction
and the genuine stochastic semigroup, for every initial probability law. -/
theorem relativeFisherInformation_langevinKernel_antitone
    {B : NNReal → Ω → E} {P : Measure Ω} (hB : IsEuclideanBrownian B P)
    {V : E → ℝ} (hV : ContDiff ℝ 2 V) (hp : IsProbabilityMeasure (gibbsMeasure volume V))
    (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (ν : Measure E) [IsProbabilityMeasure ν] (s t : NNReal) (hst : s ≤ t) :
    letI := langevinKernel_isMarkovKernel hB hV ρ hρ.le hHess s
    letI := langevinKernel_isMarkovKernel hB hV ρ hρ.le hHess t
    relativeFisherInformation hV hp (langevinKernel V B P t ∘ₘ ν) ≤
      relativeFisherInformation hV hp (langevinKernel V B P s ∘ₘ ν) := by
  let := hp
  let := langevinKernel_isMarkovKernel hB hV ρ hρ.le hHess s
  let := langevinKernel_isMarkovKernel hB hV ρ hρ.le hHess t
  let := langevinKernel_isMarkovKernel hB hV ρ hρ.le hHess (t - s)
  have hcomp : langevinKernel V B P (t - s) ∘ₘ (langevinKernel V B P s ∘ₘ ν) =
      langevinKernel V B P t ∘ₘ ν := by
    rw [Measure.comp_assoc, langevinKernel_comp hB hV ρ hρ.le hHess,
      add_tsub_cancel_of_le hst]
  have hh := relativeFisherInformation_langevinKernel_le hB hV hp ρ hρ hHess
    (langevinKernel V B P s ∘ₘ ν) (t - s)
  simp only [hcomp] at hh
  apply hh.trans
  have he : ENNReal.ofReal (Real.exp (-2 * ρ * ((t - s : NNReal) : ℝ))) ≤ 1 := by
    rw [← ENNReal.ofReal_one]
    apply ENNReal.ofReal_le_ofReal
    apply Real.exp_le_one_iff.mpr
    exact mul_nonpos_of_nonpos_of_nonneg (by linarith) (NNReal.coe_nonneg _)
  calc
    _ ≤ 1 * relativeFisherInformation hV hp (langevinKernel V B P s ∘ₘ ν) :=
      mul_le_mul he le_rfl (by positivity) (by positivity)
    _ = _ := one_mul _

set_option maxHeartbeats 750000 in
/-- The source actual Fisher endpoint bound on normalized positive
compact perturbations. The genuine entropy FTC and full Fisher decay,
not an endpoint or decay premise, prove this inequality. -/
theorem langevinKernel_fisher_entropy_endpoint_core
    {B : NNReal → Ω → E} {P : Measure Ω} (hB : IsEuclideanBrownian B P)
    {V g : E → ℝ} (hV : ContDiff ℝ 2 V) (hp : IsProbabilityMeasure (gibbsMeasure volume V))
    (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g)
    (c m : ℝ) (hm : 0 < m) (hpos : ∀ x, m ≤ c + g x)
    (hNorm : ∫ x, c + g x ∂gibbsMeasure volume V = 1)
    {s t : ℝ} (hs : 0 ≤ s) (hst : s < t) :
    let ν := (gibbsMeasure volume V).withDensity (fun x => ENNReal.ofReal (c + g x))
    ∃ hν : IsProbabilityMeasure ν, letI := hν
      letI := langevinKernel_isMarkovKernel hB hV ρ hρ.le hHess t.toNNReal
      relativeFisherInformation hV hp (langevinKernel V B P t.toNNReal ∘ₘ ν) ≤
        klDiv (langevinKernel V B P s.toNNReal ∘ₘ ν) (gibbsMeasure volume V) / ENNReal.ofReal (t - s) := by
  let := hp
  let μ := gibbsMeasure volume V
  let ν := μ.withDensity (fun x => ENNReal.ofReal (c + g x))
  obtain ⟨hν, _hKL0, hFI0⟩ := langevin_core_information_finite hB hV hp ρ hρ hHess
    (hg.of_le (by norm_num)) hgc c m hm hpos hNorm
  refine ⟨hν, ?_⟩
  let := hν
  have hMarkov (r : ℝ) : IsMarkovKernel (langevinKernel V B P r.toNNReal) :=
    langevinKernel_isMarkovKernel hB hV ρ hρ.le hHess r.toNNReal
  let H := fun r : ℝ => (klDiv (langevinKernel V B P r.toNNReal ∘ₘ ν) μ).toReal
  let I := fun r : ℝ => letI := hMarkov r
    (relativeFisherInformation hV hp (langevinKernel V B P r.toNNReal ∘ₘ ν)).toReal
  have hFIfin (r : ℝ) : letI := hMarkov r
      relativeFisherInformation hV hp (langevinKernel V B P r.toNNReal ∘ₘ ν) ≠ ⊤ := by
    let := hMarkov r
    exact ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hFI0)
      (relativeFisherInformation_langevinKernel_le hB hV hp ρ hρ hHess ν r.toNNReal)
  obtain ⟨M, hM⟩ := hgc.exists_bound_of_continuous hg.continuous
  have hKLfin (r : ℝ) : klDiv (langevinKernel V B P r.toNNReal ∘ₘ ν) μ ≠ ⊤ :=
    langevinKernel_klDiv_ne_top_of_bounded_density hB hV hp ρ hρ hHess
      (measurable_const.add hg.continuous.measurable) (fun x => (hm.trans_le (hpos x)).le)
      ⟨|c| + M, fun x => (norm_add_le _ _).trans (add_le_add (by simp) (hM x))⟩ hν r.toNNReal
  have hc : ContinuousOn H (Ici 0) :=
    ((continuous_klDiv_langevinKernel hB hV hp ρ hρ hHess (hg.of_le (by norm_num)) hgc c m hm hpos hν).comp
      continuous_real_toNNReal).continuousOn
  have hd (r : ℝ) (hr : 0 < r) : HasDerivAt H (-I r) r :=
    hasDerivAt_klDiv_langevinKernel hB hV hp ρ hρ hHess hg hgc c m hm hpos hν hr
  have hIanti : AntitoneOn I (Ici 0) := by
    intro a _ha b _hb hab
    let := hMarkov a
    let := hMarkov b
    exact ENNReal.toReal_mono (hFIfin a)
      (relativeFisherInformation_langevinKernel_antitone hB hV hp ρ hρ hHess ν
        a.toNNReal b.toNNReal (Real.toNNReal_mono hab))
  have hh := fisher_entropy_endpoint_of_dissipation H I hc hd hIanti (fun _ => ENNReal.toReal_nonneg) hs hst
  let := hMarkov t
  have he := ENNReal.ofReal_le_ofReal hh
  rw [ENNReal.ofReal_toReal (hFIfin t), ENNReal.ofReal_div_of_pos (sub_pos.mpr hst),
    ENNReal.ofReal_toReal (hKLfin s)] at he
  exact he

end CutoffRigidity
