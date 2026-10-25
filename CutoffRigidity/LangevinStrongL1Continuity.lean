module
public import CutoffRigidity.IntegrableCompactC2Approximation
public import CutoffRigidity.InvariantKernelL1
public import CutoffRigidity.LangevinEntropyFinite

/-! # Genuine strong L¹ continuity of actual Markov density evolution

Actual compact C² density in L¹, pathwise time continuity on bounded tests,
and the proved invariant-kernel L¹ contraction give the full L¹ limit.
-/
public section
namespace CutoffRigidity
open MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal
variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

set_option maxHeartbeats 800000 in
theorem tendsto_langevinKernel_L1_zero
    {B : NNReal → Ω → E} {P : Measure Ω} (hB : IsEuclideanBrownian B P)
    {V f : E → ℝ} (hV : ContDiff ℝ 2 V) (hp : IsProbabilityMeasure (gibbsMeasure volume V))
    (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (hfm : Measurable f) (hf : Integrable f (gibbsMeasure volume V)) :
    Tendsto (fun t : NNReal => ∫ x, ‖(∫ y, f y ∂langevinKernel V B P t x) - f x‖
      ∂gibbsMeasure volume V) (𝓝 0) (𝓝 0) := by
  let := hp
  let μ := gibbsMeasure volume V
  let K := langevinKernel V B P
  have hMarkov (t : NNReal) : IsMarkovKernel (K t) :=
    langevinKernel_isMarkovKernel hB hV ρ hρ.le hHess t
  have hInv (t : NNReal) : K t ∘ₘ μ = μ := langevinKernel_gibbs_invariant hB hV hp ρ hρ hHess t
  obtain ⟨g,hg,hgc,hDense⟩ := exists_compact_c2_L1_approx_of_integrable μ hf
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨n, hn⟩ := (hDense.eventually (gt_mem_nhds (by linarith : (0 : ℝ) < ε/4))).exists
  have hgI : Integrable (g n) μ := (hg n).continuous.integrable_of_hasCompactSupport (hgc n)
  obtain ⟨M,hM0,hM⟩ := compact_continuous_norm_bound (hg n).continuous (hgc n)
  have hKgB (t : NNReal) (x : E) : ‖∫ y, g n y ∂K t x‖ ≤ M := by
    let := hMarkov t
    simpa using norm_integral_le_of_norm_le_const (μ := K t x) (Eventually.of_forall hM)
  have hMid : Tendsto (fun t : NNReal => ∫ x, ‖(∫ y, g n y ∂K t x) - g n x‖ ∂μ) (𝓝 0) (𝓝 0) := by
    have hh := tendsto_integral_filter_of_dominated_convergence (μ := μ) (l := 𝓝 (0 : NNReal))
      (F := fun t x => ‖(∫ y, g n y ∂K t x) - g n x‖) (f := fun _ => (0 : ℝ))
      (fun _ => 2*M) ?_ ?_ (integrable_const _) ?_
    · simpa using hh
    · exact Eventually.of_forall fun t =>
        (((hg n).continuous.measurable.stronglyMeasurable.integral_kernel).sub
          (hg n).continuous.stronglyMeasurable).norm.aestronglyMeasurable
    · exact Eventually.of_forall fun t => Eventually.of_forall fun x => by
        rw [Real.norm_of_nonneg (norm_nonneg _)]
        exact (norm_sub_le _ _).trans (by linarith [hKgB t x,hM x])
    · apply Eventually.of_forall
      intro x
      have ht := (continuous_langevinKernel_integral_of_bounded_continuous hB hV
        (hg n).continuous ⟨M,hM⟩ ρ hρ.le hHess x).tendsto (0 : NNReal)
      have he : (∫ y, g n y ∂K 0 x) = g n x := by
        rw [show K 0 = Kernel.id from langevinKernel_zero hB hV ρ hρ.le hHess, Kernel.id_apply]
        exact integral_dirac _ _
      rw [he] at ht
      simpa using (ht.sub_const (g n x)).norm
  have hsmall := hMid.eventually (gt_mem_nhds (by linarith : (0 : ℝ) < ε/2))
  filter_upwards [hsmall] with t ht
  let := hMarkov t
  have hKf := invariantKernel_integral_integrable (K t) (hInv t) hfm hf
  have hKg := invariantKernel_integral_integrable (K t) (hInv t) (hg n).continuous.measurable hgI
  have hc := invariantKernel_L1_contraction (K t) (hInv t) hfm (hg n).continuous.measurable hf hgI
  simp only [← Real.norm_eq_abs] at hc
  have hpoint (x : E) : ‖(∫ y, f y ∂K t x) - f x‖ ≤
      ‖(∫ y, f y ∂K t x) - ∫ y, g n y ∂K t x‖ +
        ‖(∫ y, g n y ∂K t x) - g n x‖ + ‖g n x - f x‖ := by
    have ha := norm_sub_le_norm_sub_add_norm_sub (∫ y, f y ∂K t x)
      (∫ y, g n y ∂K t x) (f x)
    have hb := norm_sub_le_norm_sub_add_norm_sub (∫ y, g n y ∂K t x) (g n x) (f x)
    linarith
  have hbound := integral_mono (hKf.sub hf).norm
    (((hKf.sub hKg).norm.add (hKg.sub hgI).norm).add (hgI.sub hf).norm) hpoint
  have he1 := integral_add ((hKf.sub hKg).norm.add (hKg.sub hgI).norm) (hgI.sub hf).norm
  have he2 := integral_add (hKf.sub hKg).norm (hKg.sub hgI).norm
  simp only [Pi.add_apply, Pi.sub_apply] at he1 he2 hbound
  rw [he1,he2] at hbound
  have hrev : (∫ x, ‖g n x - f x‖ ∂μ) = ∫ x, ‖f x - g n x‖ ∂μ := by
    apply integral_congr_ae
    exact Eventually.of_forall fun x => norm_sub_rev _ _
  rw [hrev] at hbound
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (integral_nonneg fun x => norm_nonneg _)]
  linarith

end CutoffRigidity
