module
public import CutoffRigidity.LogSobolev
public import CutoffRigidity.FisherDecay
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-! # Actual entropy contraction from logarithmic Sobolev and de Bruijn

The true evolved KL/Fisher functionals are finite on positive normalized
compact perturbations. The integrating-factor proof of Gronwall then
uses the actual de Bruijn derivative and the proved full logarithmic
Sobolev inequality, without an entropy-decay premise.
-/
public section
namespace CutoffRigidity
open MeasureTheory ProbabilityTheory InformationTheory Filter Set
open scoped Topology ENNReal NNReal

/-- The scalar integrating-factor argument, used below only after its
hypotheses have been proved for the actual KL/Fisher evolution. -/
theorem entropy_exponential_contraction_of_dissipation_lsi
    (H I : ℝ → ℝ) (ρ : ℝ)
    (hc : ContinuousOn H (Ici 0))
    (hd : ∀ r, 0 < r → HasDerivAt H (-I r) r)
    (hlsi : ∀ r, 0 < r → 2 * ρ * H r ≤ I r)
    {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    H t ≤ Real.exp (-2 * ρ * (t - s)) * H s := by
  let F := fun r => Real.exp (2 * ρ * r) * H r
  let D := fun r => Real.exp (2 * ρ * r) * (2 * ρ * H r - I r)
  have hFd (r : ℝ) (hr : 0 < r) : HasDerivAt F (D r) r := by
    have hh := (((hasDerivAt_id r).const_mul (2 * ρ)).exp).mul (hd r hr)
    simp only [id_eq, Pi.mul_def, mul_one] at hh
    convert hh using 1
    dsimp only [D]
    ring
  have hExp : Continuous (fun r : ℝ => Real.exp (2 * ρ * r)) := by fun_prop
  have hFc : ContinuousOn F (Ici 0) := hExp.continuousOn.mul hc
  have hanti : AntitoneOn F (Ici 0) :=
    antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ici _) hFc
      (fun r hr => (hFd r (by simpa only [interior_Ici, mem_Ioi] using hr)).hasDerivWithinAt)
      (fun r hr => mul_nonpos_of_nonneg_of_nonpos (Real.exp_nonneg _)
        (sub_nonpos.mpr (hlsi r (by simpa only [interior_Ici, mem_Ioi] using hr))))
  have hh := mul_le_mul_of_nonneg_left (hanti hs (hs.trans hst) hst) (Real.exp_nonneg (-2 * ρ * t))
  have ht : Real.exp (-2 * ρ * t) * Real.exp (2 * ρ * t) = 1 := by
    rw [← Real.exp_add, show -2 * ρ * t + 2 * ρ * t = 0 by ring, Real.exp_zero]
  have hts : Real.exp (-2 * ρ * t) * Real.exp (2 * ρ * s) = Real.exp (-2 * ρ * (t - s)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  simpa only [F, ← mul_assoc, ht, hts, one_mul] using hh

variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

/-- Actual initial KL/Fisher finiteness follows from the source positive
compact-perturbation assumptions and true normalization. -/
theorem langevin_core_information_finite
    {B : NNReal → Ω → E} {P : Measure Ω} (hB : IsEuclideanBrownian B P)
    {V g : E → ℝ} (hV : ContDiff ℝ 2 V) (hp : IsProbabilityMeasure (gibbsMeasure volume V))
    (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (hg : ContDiff ℝ 1 g) (hgc : HasCompactSupport g)
    (c m : ℝ) (hm : 0 < m) (hpos : ∀ x, m ≤ c + g x)
    (hNorm : ∫ x, c + g x ∂gibbsMeasure volume V = 1) :
    let ν := (gibbsMeasure volume V).withDensity (fun x => ENNReal.ofReal (c + g x))
    ∃ hν : IsProbabilityMeasure ν, letI := hν
      klDiv ν (gibbsMeasure volume V) ≠ ⊤ ∧ relativeFisherInformation hV hp ν ≠ ⊤ := by
  let := hp
  let μ := gibbsMeasure volume V
  let f := fun x => c + g x
  obtain ⟨hν, _⟩ := langevinKernel_evolved_relativeFisherInformation_le hB hV hp ρ hρ hHess
    hg hgc c m hm hpos hNorm 0
  refine ⟨hν, ?_⟩
  let := hν
  have hf : ContDiff ℝ 1 f := contDiff_const.add hg
  obtain ⟨M, hM⟩ := hgc.exists_bound_of_continuous hg.continuous
  have hfLp : MemLp f 2 μ := MemLp.of_bound hf.continuous.aestronglyMeasurable (|c| + M)
    (Eventually.of_forall (fun x => (norm_add_le _ _).trans (add_le_add (by simp) (hM x))))
  have hggrad : MemLp (gradient g) 2 μ := (continuous_gradient_of_c1 hg).memLp_of_hasCompactSupport
    ((hgc.fderiv ℝ).comp_left (g := (InnerProductSpace.toDual ℝ E).symm) (by simp))
  have heq : gradient f = gradient g := by
    funext x
    change (InnerProductSpace.toDual ℝ E).symm (fderiv ℝ (fun y => c + g y) x) = _
    rw [fderiv_const_add]
    rfl
  have hfgrad : MemLp (gradient f) 2 μ := by rw [heq]; exact hggrad
  refine ⟨klDiv_withDensity_ne_top_of_memLp_two hf.continuous.measurable hfLp
    (fun x => (hm.trans_le (hpos x)).le) hν, ?_⟩
  rw [relativeFisherInformation_withDensity_c1_of_memLp hV hp ρ hρ hHess hf m hm hpos hν hfgrad]
  exact ENNReal.ofReal_ne_top

set_option maxHeartbeats 750000 in
/-- Exponential contraction of the actual evolved KL divergence on the
source positive normalized compact-perturbation core. The actual full LSI
and de Bruijn identity discharge all scalar evolution hypotheses. -/
theorem langevinKernel_entropy_contraction_core
    {B : NNReal → Ω → E} {P : Measure Ω} (hB : IsEuclideanBrownian B P)
    {V g : E → ℝ} (hV : ContDiff ℝ 2 V) (hp : IsProbabilityMeasure (gibbsMeasure volume V))
    (hdim : 0 < d) (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g)
    (c m : ℝ) (hm : 0 < m) (hpos : ∀ x, m ≤ c + g x)
    (hNorm : ∫ x, c + g x ∂gibbsMeasure volume V = 1)
    {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    let ν := (gibbsMeasure volume V).withDensity (fun x => ENNReal.ofReal (c + g x))
    klDiv (langevinKernel V B P t.toNNReal ∘ₘ ν) (gibbsMeasure volume V) ≤
      ENNReal.ofReal (Real.exp (-2 * ρ * (t - s))) *
        klDiv (langevinKernel V B P s.toNNReal ∘ₘ ν) (gibbsMeasure volume V) := by
  let := hp
  let μ := gibbsMeasure volume V
  let ν := μ.withDensity (fun x => ENNReal.ofReal (c + g x))
  obtain ⟨hν, _hKL0, hFI0⟩ := langevin_core_information_finite hB hV hp ρ hρ hHess
    (hg.of_le (by norm_num)) hgc c m hm hpos hNorm
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
  have hlsi (r : ℝ) (_hr : 0 < r) : 2 * ρ * H r ≤ I r := by
    let := hMarkov r
    have hh := logSobolev_relativeFisherInformation hB hV hp hdim ρ hρ hHess
      (langevinKernel V B P r.toNNReal ∘ₘ ν)
    have hhR := ENNReal.toReal_mono
      (ENNReal.div_ne_top (hFIfin r) (ENNReal.ofReal_ne_zero_iff.mpr (by positivity : 0 < 2 * ρ))) hh
    rw [ENNReal.toReal_div, ENNReal.toReal_ofReal (by positivity : 0 ≤ 2 * ρ)] at hhR
    have hmul := (le_div_iff₀ (by positivity : 0 < 2 * ρ)).mp hhR
    change H r * (2 * ρ) ≤ I r at hmul
    nlinarith only [hmul]
  have hh := entropy_exponential_contraction_of_dissipation_lsi H I ρ hc hd hlsi hs hst
  have he := ENNReal.ofReal_le_ofReal hh
  simpa only [H, ENNReal.ofReal_toReal (hKLfin _), ENNReal.ofReal_mul (Real.exp_nonneg _)] using he

end CutoffRigidity
