module

public import CutoffRigidity.SobolevScalarChain
public import CutoffRigidity.L2BoundedMultiplier
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
public import Mathlib.Analysis.Calculus.ContDiff.Deriv

/-! # Smooth normal contractions on the actual closed Gibbs gradient graph

This is proved by compact graph approximation and L² dominated convergence,
rather than by postulating a Sobolev chain rule.
-/

public section
namespace CutoffRigidity
open MeasureTheory Filter Topology
variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

set_option maxHeartbeats 700000 in
theorem gibbsSobolev_smooth_normal_contraction
    {V : E → ℝ} (hV : ContDiff ℝ 2 V)
    (hprob : IsProbabilityMeasure (gibbsMeasure volume V))
    {ψ : ℝ → ℝ} (hψ : ContDiff ℝ 2 ψ) (hψ0 : ψ 0 = 0)
    (hbound : ∀ r, |deriv ψ r| ≤ 1)
    (u : gibbsSobolevGraph hV hprob) :
    ∃ (v : gibbsSobolevGraph hV hprob),
      (gibbsSobolevInclusion hV hprob v =ᵐ[gibbsMeasure volume V]
        fun x => ψ (gibbsSobolevInclusion hV hprob u x)) ∧
      (gibbsSobolevDerivative hV hprob v =ᵐ[gibbsMeasure volume V]
        fun x => deriv ψ (gibbsSobolevInclusion hV hprob u x) • gibbsSobolevDerivative hV hprob u x) ∧
      ‖gibbsSobolevDerivative hV hprob v‖ ≤ ‖gibbsSobolevDerivative hV hprob u‖ := by
  let μ := gibbsMeasure volume V
  let G := compactGibbsGradient hV.continuous hprob
  let U := gibbsSobolevInclusion hV hprob u
  let D := gibbsSobolevDerivative hV hprob u
  have hψd := hψ.differentiable (by norm_num)
  have hdc : Continuous (deriv ψ) := hψ.continuous_deriv (by norm_num)
  let L := scalar_normal_contraction_lipschitz hψd hbound
  let C := L.compLp hψ0 (p := (2 : ENNReal)) (μ := μ)
  let a : E → ℝ := fun x => deriv ψ (U x)
  have ha : AEStronglyMeasurable a μ := hdc.comp_aestronglyMeasurable (Lp.aestronglyMeasurable U)
  have hb : ∀ᵐ x ∂μ, ‖a x‖ ≤ 1 := Eventually.of_forall (fun x => hbound _)
  let B := boundedScalarMulL2 a ha hb D
  have hmem : (U, D) ∈ closure (G.graph : Set _) := by
    change (U, D) ∈ G.graph.topologicalClosure
    rw [(compactGibbsGradient_isClosable hV hprob).graph_closure_eq_closure_graph]
    exact u.property
  obtain ⟨p, hp, hplim⟩ := mem_closure_iff_seq_limit.mp hmem
  have hfirst : Tendsto (fun n => (p n).1) atTop (𝓝 U) := (continuous_fst.tendsto _).comp hplim
  have hsecond : Tendsto (fun n => (p n).2) atTop (𝓝 D) := (continuous_snd.tendsto _).comp hplim
  obtain ⟨ns, hns, hae⟩ := (tendstoInMeasure_of_tendsto_Lp hfirst).exists_seq_tendsto_ae'
  let an : ℕ → E → ℝ := fun n x => deriv ψ ((p (ns n)).1 x)
  have han (n : ℕ) : AEStronglyMeasurable (an n) μ :=
    hdc.comp_aestronglyMeasurable (Lp.aestronglyMeasurable _)
  have hbn (n : ℕ) : ∀ᵐ x ∂μ, ‖an n x‖ ≤ 1 := Eventually.of_forall (fun x => hbound _)
  let Bn := fun n => boundedScalarMulL2 (an n) (han n) (hbn n) (p (ns n)).2
  have hB : Tendsto Bn atTop (𝓝 B) := by
    apply boundedScalarMulL2_tendsto han ha hbn hb
    · filter_upwards [hae] with x hx
      exact hdc.continuousAt.tendsto.comp hx
    · exact hsecond.comp hns
  have hC : Tendsto (fun n => C (p (ns n)).1) atTop (𝓝 (C U)) :=
    (L.continuous_compLp hψ0).continuousAt.tendsto.comp (hfirst.comp hns)
  have hpcomp (n : ℕ) : (C (p (ns n)).1, Bn n) ∈ (closedGibbsGradient hV hprob).graph := by
    obtain ⟨v, hv1, hv2⟩ := G.mem_graph_iff.mp (hp (ns n))
    let f := compactGibbsRepresentative V v
    have hf := (compactGibbsRepresentative_spec V v).1
    have hfrep : (p (ns n)).1 =ᵐ[μ] f := by
      rw [← hv1]
      exact (compactGibbsRepresentative_spec V v).2.2.symm
    have hgrep : (p (ns n)).2 =ᵐ[μ] gradient f := by
      rw [← hv2]
      exact (compactGibbsGradient_memLp hprob v).coeFn_toLp
    have hfLp : MemLp f 2 μ := (memLp_congr_ae hfrep).mp (Lp.memLp (p (ns n)).1)
    obtain ⟨hc, hg, hgmem⟩ := scalar_normal_comp_classical_graph hV hprob hf hfLp
      (compactGibbsGradient_memLp hprob v) hψ hψ0 hbound
    have hceq : C (p (ns n)).1 = hc.toLp (ψ ∘ f) := by
      apply Lp.ext
      filter_upwards [L.coeFn_compLp hψ0 (p (ns n)).1, hc.coeFn_toLp, hfrep] with x hx hy hz
      exact hx.trans (by simpa only [Function.comp_apply, hz] using hy.symm)
    have hgeq : Bn n = hg.toLp (gradient (ψ ∘ f)) := by
      apply Lp.ext
      filter_upwards [boundedScalarMulL2_coeFn (an n) (han n) (hbn n) (p (ns n)).2,
        hg.coeFn_toLp, hfrep, hgrep] with x hx hy hz hw
      rw [hx, hy, gradient_scalar_outer_comp hψd (hf.differentiable (by norm_num))]
      change deriv ψ ((p (ns n)).1 x) • (p (ns n)).2 x = _
      rw [hz, hw]
    rw [hceq, hgeq]
    exact hgmem
  have hclosed : (C U, B) ∈ (closedGibbsGradient hV hprob).graph :=
    (closedGibbsGradient_isClosed hV hprob).mem_of_tendsto (hC.prodMk_nhds hB)
      (Eventually.of_forall hpcomp)
  let v : gibbsSobolevGraph hV hprob := ⟨WithLp.toLp 2 (C U, B), hclosed⟩
  refine ⟨v, L.coeFn_compLp hψ0 U, boundedScalarMulL2_coeFn a ha hb D, ?_⟩
  change ‖B‖ ≤ ‖D‖
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [boundedScalarMulL2_coeFn a ha hb D, hb] with x hx hb'
  rw [hx, norm_smul]
  exact mul_le_of_le_one_left (norm_nonneg _) hb'

end CutoffRigidity
