module

public import CutoffRigidity.LogSobolevTransfer
public import CutoffRigidity.LangevinEntropyLimit
public import CutoffRigidity.LangevinDeBruijn

/-! # Genuine logarithmic Sobolev on a positive compact-perturbation core

Actual de Bruijn evolution, derived Fisher decay, and actual zero entropy
limit discharge every input of the scalar argument. The initial density is
normalized, bounded below and a constant plus a compact C² function.
Extension to the full closed Sobolev domain remains a further step.
-/

public section

namespace CutoffRigidity

open MeasureTheory ProbabilityTheory InformationTheory Filter Set Topology

variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

/-- The source LSI on a genuine positive compact-perturbation probability
core, with KL/Fisher finiteness and all analytic evolution inputs derived. -/
theorem logSobolev_compact_positive_density_real
    {B : NNReal → Ω → E} {P : Measure Ω} (hB : IsEuclideanBrownian B P)
    {V g : E → ℝ} (hV : ContDiff ℝ 2 V) (hp : IsProbabilityMeasure (gibbsMeasure volume V))
    (hd : 0 < d) (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g)
    (c m : ℝ) (hm : 0 < m) (hpos : ∀ x, m ≤ c + g x)
    (hNorm : ∫ x, c + g x ∂gibbsMeasure volume V = 1) :
    let ν := (gibbsMeasure volume V).withDensity (fun x => ENNReal.ofReal (c + g x))
    ∃ hν : IsProbabilityMeasure ν,
      letI := hν
      klDiv ν (gibbsMeasure volume V) ≠ ⊤ ∧ relativeFisherInformation hV hp ν ≠ ⊤ ∧
      (klDiv ν (gibbsMeasure volume V)).toReal ≤ (relativeFisherInformation hV hp ν).toReal / (2 * ρ) := by
  have := hp
  let μ := gibbsMeasure volume V
  let f : E → ℝ := fun x => c + g x
  let ν := μ.withDensity (fun x => ENNReal.ofReal (f x))
  obtain ⟨hν,_⟩ := langevinKernel_evolved_relativeFisherInformation_le hB hV hp ρ hρ hHess
    (hg.of_le (by norm_num)) hgc c m hm hpos hNorm 0
  refine ⟨hν, ?_⟩
  have := hν
  have hfm : Measurable f := measurable_const.add hg.continuous.measurable
  have hfn (x : E) : 0 ≤ f x := (hm.trans_le (hpos x)).le
  obtain ⟨M,hM⟩ := hgc.exists_bound_of_continuous hg.continuous
  have hfLp : MemLp f 2 μ := MemLp.of_bound hfm.aestronglyMeasurable (|c| + M)
    (Filter.Eventually.of_forall (fun x => (norm_add_le _ _).trans (add_le_add (by simp) (hM x))))
  have hKLfin := klDiv_withDensity_ne_top_of_memLp_two hfm hfLp hfn hν
  have hg1 : ContDiff ℝ 1 g := hg.of_le (by norm_num)
  have hgradg : MemLp (gradient g) 2 μ :=
    (continuous_gradient_of_c1 hg1).memLp_of_hasCompactSupport
      ((hgc.fderiv ℝ).comp_left (g := (InnerProductSpace.toDual ℝ E).symm) (by simp))
  have hgradEq : gradient f = gradient g := by
    funext x
    change (InnerProductSpace.toDual ℝ E).symm (fderiv ℝ (fun y => c + g y) x) = _
    rw [fderiv_const_add]
    rfl
  have hgrad : MemLp (gradient f) 2 μ := by rw [hgradEq]; exact hgradg
  have hFI := relativeFisherInformation_withDensity_c1_of_memLp hV hp ρ hρ hHess
    (contDiff_const.add hg1) m hm hpos hν hgrad
  have hFIfin : relativeFisherInformation hV hp ν ≠ ⊤ := by
    rw [hFI]
    exact ENNReal.ofReal_ne_top
  refine ⟨hKLfin,hFIfin,?_⟩
  let H (s : ℝ) := (klDiv (langevinKernel V B P s.toNNReal ∘ₘ ν) μ).toReal
  let I (s : ℝ) :=
    have := langevinKernel_isMarkovKernel hB hV ρ hρ.le hHess s.toNNReal
    (relativeFisherInformation hV hp (langevinKernel V B P s.toNNReal ∘ₘ ν)).toReal
  have hHc : ContinuousOn H (Ici 0) :=
    ((continuous_klDiv_langevinKernel hB hV hp ρ hρ hHess hg1 hgc c m hm hpos hν).comp
      continuous_real_toNNReal).continuousOn
  have hHd (s : ℝ) (hs : 0 < s) : HasDerivAt H (-I s) s :=
    hasDerivAt_klDiv_langevinKernel hB hV hp ρ hρ hHess hg hgc c m hm hpos hν hs
  have hId (s : ℝ) (hs : 0 < s) : I s ≤
      Real.exp (-2 * ρ * s) * (relativeFisherInformation hV hp ν).toReal := by
    obtain ⟨_,hh⟩ := langevinKernel_evolved_relativeFisherInformation_le hB hV hp ρ hρ hHess
      hg1 hgc c m hm hpos hNorm s.toNNReal
    have hb := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hFIfin) hh
    simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.exp_nonneg _),
      Real.coe_toNNReal _ hs.le] using hb
  have hHlim : Tendsto H atTop (𝓝 0) := tendsto_klDiv_langevinKernel_toReal_zero
    hB hV hp hd ρ hρ hHess hg hgc c m hm hpos hNorm
  have hh := entropy_le_fisher_div_of_dissipation_decay_limit H I ρ
    (relativeFisherInformation hV hp ν).toReal hρ hHc hHd hId hHlim
  change (klDiv (langevinKernel V B P (0 : ℝ).toNNReal ∘ₘ ν) μ).toReal ≤ _ at hh
  rwa [Real.toNNReal_zero, langevinKernel_zero hB hV ρ hρ.le hHess, Measure.id_comp] at hh

end CutoffRigidity
