module

public import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
public import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
public import Mathlib.MeasureTheory.Measure.LevyConvergence
public import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Basic
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.Analysis.Convex.Integral
public import Mathlib.Topology.Algebra.Module.Basic
public import Mathlib.Topology.Sequences

/-!
# Gaussian laws are closed under convergence in L²

This supports Gaussian time-integral calculations for the actual Brownian
driver in the paper's Mehler formula. The proof uses actual random variables,
continuity of first and second moments in L², convergence in distribution,
and characteristic functions. No Gaussian law is assumed for the limit.
-/

public section

open MeasureTheory ProbabilityTheory Filter Topology

namespace CutoffRigidity

variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]

theorem continuous_l2_expectation :
    Continuous (fun X : Ω →₂[P] ℝ => ∫ ω, X ω ∂P) := by
  have hc : MemLp (fun _ : Ω => (1 : ℝ)) 2 P := memLp_const 1
  let c : Ω →₂[P] ℝ := hc.toLp (fun _ => 1)
  have heq : (fun X : Ω →₂[P] ℝ => ∫ ω, X ω ∂P) =
      (fun X => inner ℝ X c) := by
    funext X
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hc.coeFn_toLp] with ω hω
    change X ω = inner ℝ (X ω) (hc.toLp (fun _ => 1) ω)
    rw [hω]
    simp
  rw [heq]
  exact continuous_id.inner continuous_const

omit [IsProbabilityMeasure P] in
theorem l2_integral_sq_eq_norm_sq (X : Ω →₂[P] ℝ) :
    (∫ ω, (X ω) ^ 2 ∂P) = ‖X‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  simp only [RCLike.inner_apply, conj_trivial, pow_two]

theorem continuous_l2_variance :
    Continuous (fun X : Ω →₂[P] ℝ => variance X P) := by
  have heq : (fun X : Ω →₂[P] ℝ => variance X P) =
      (fun X => ‖X‖ ^ 2 - (∫ ω, X ω ∂P) ^ 2) := by
    funext X
    rw [variance_eq_sub (Lp.memLp X)]
    change (∫ ω, (X ω) ^ 2 ∂P) - (∫ ω, X ω ∂P) ^ 2 = _
    rw [l2_integral_sq_eq_norm_sq]
  rw [heq]
  exact (continuous_norm.pow 2).sub ((continuous_l2_expectation P).pow 2)

/-- An L² limit of actual Gaussian random variables is Gaussian, including
degenerate limiting variance. -/
theorem hasGaussianLaw_of_tendsto_l2 {Xn : ℕ → Ω →₂[P] ℝ} {X : Ω →₂[P] ℝ}
    (hGaussian : ∀ n, HasGaussianLaw (Xn n) P)
    (hlim : Tendsto Xn atTop (𝓝 X)) : HasGaussianLaw X P := by
  have hm := ((continuous_l2_expectation P).tendsto X).comp hlim
  have hv := ((continuous_l2_variance P).tendsto X).comp hlim
  have hdist := (tendstoInMeasure_of_tendsto_Lp hlim).tendstoInDistribution
    (fun n => (Lp.memLp (Xn n)).aemeasurable)
  have hPX : IsProbabilityMeasure (P.map X) :=
    (Measure.isProbabilityMeasure_map_iff (Lp.memLp X).aemeasurable).mpr inferInstance
  have hLaw : P.map X = gaussianReal (∫ ω, X ω ∂P) (variance X P).toNNReal := by
    apply Measure.ext_of_charFun
    ext t
    let F : ℝ × ℝ → ℂ := fun p =>
      Complex.exp ((p.1 : ℂ) * t * Complex.I - (p.2 : ℂ) * t ^ 2 / 2)
    have hF : Continuous F := by fun_prop
    have heq (n : ℕ) : charFun (P.map (Xn n)) t =
        F (∫ ω, Xn n ω ∂P, variance (Xn n) P) := by
      rw [(hGaussian n).map_eq_gaussianReal, charFun_gaussianReal]
      rw [Real.coe_toNNReal (variance (Xn n) P) (variance_nonneg _ _)]
      dsimp only [F]
      congr 1
      ring
    have htarget : charFun (gaussianReal (∫ ω, X ω ∂P) (variance X P).toNNReal) t =
        F (∫ ω, X ω ∂P, variance X P) := by
      rw [charFun_gaussianReal]
      rw [Real.coe_toNNReal (variance X P) (variance_nonneg _ _)]
      dsimp only [F]
      congr 1
      ring
    have hFseq : Tendsto (fun n => F (∫ ω, Xn n ω ∂P, variance (Xn n) P)) atTop
        (𝓝 (F (∫ ω, X ω ∂P, variance X P))) :=
      (hF.tendsto _).comp (hm.prodMk_nhds hv)
    have hForm : Tendsto (fun n => charFun (P.map (Xn n)) t) atTop
        (𝓝 (charFun (gaussianReal (∫ ω, X ω ∂P) (variance X P).toNNReal) t)) := by
      rw [← htarget] at hFseq
      exact hFseq.congr' (Eventually.of_forall (fun n => (heq n).symm))
    exact tendsto_nhds_unique (hdist.tendsto_charFun t) hForm
  exact ⟨(Lp.memLp X).aemeasurable, by rw [hLaw]; infer_instance⟩

theorem isClosed_gaussian_l2 : IsClosed {X : Ω →₂[P] ℝ | HasGaussianLaw X P} :=
  IsSeqClosed.isClosed (fun _ _ hGaussian hlim => hasGaussianLaw_of_tendsto_l2 P hGaussian hlim)

omit [IsProbabilityMeasure P] in
/-- Every finite linear combination of an actual Gaussian process is Gaussian,
also when the process is represented by L² equivalence classes. -/
theorem hasGaussianLaw_mem_span_of_isGaussianProcess {T : Type*} (f : T → Ω →₂[P] ℝ)
    (hGaussian : IsGaussianProcess (fun t ω => f t ω) P)
    {X : Ω →₂[P] ℝ} (hX : X ∈ Submodule.span ℝ (Set.range f)) : HasGaussianLaw X P := by
  classical
  obtain ⟨c, rfl⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp hX
  let L : (c.support → ℝ) →L[ℝ] ℝ :=
    ∑ i : c.support, c i • ContinuousLinearMap.proj i
  have h := (hGaussian.hasGaussianLaw c.support).map L
  change HasGaussianLaw (c.linearCombination ℝ f) P
  apply h.congr
  have hrepresent := Lp.coeFn_linearCombination c f
  apply Filter.EventuallyEq.trans _ hrepresent.symm
  exact Eventually.of_forall (fun ω => by
    simp [L, Finsupp.linearCombination_apply, Finsupp.sum]
    exact Finset.sum_attach c.support (fun i => c i * f i ω))

/-- A finite-measure Bochner integral of a jointly Gaussian L²-valued process
is Gaussian. The proof integrates in its closed linear span. -/
theorem hasGaussianLaw_integral_l2 {T : Type*} [MeasurableSpace T]
    (μ : Measure T) [IsFiniteMeasure μ] (f : T → Ω →₂[P] ℝ)
    (hGaussian : IsGaussianProcess (fun t ω => f t ω) P) (hfi : Integrable f μ) :
    HasGaussianLaw (∫ t, f t ∂μ : Ω →₂[P] ℝ) P := by
  let S : Submodule ℝ (Ω →₂[P] ℝ) := Submodule.span ℝ (Set.range f)
  have hspan : (S : Set (Ω →₂[P] ℝ)) ⊆ {X | HasGaussianLaw X P} :=
    fun X hX => hasGaussianLaw_mem_span_of_isGaussianProcess P f hGaussian hX
  have hclosure : closure (S : Set (Ω →₂[P] ℝ)) ⊆ {X | HasGaussianLaw X P} :=
    closure_minimal hspan (isClosed_gaussian_l2 P)
  have hmem : (∫ t, f t ∂μ) ∈ S.topologicalClosure := by
    by_cases hμ : μ = 0
    · simp [hμ]
    have : NeZero μ := ⟨hμ⟩
    have ha := S.topologicalClosure.convex.average_mem S.isClosed_topologicalClosure
      (Eventually.of_forall (fun t => S.le_topologicalClosure (Submodule.subset_span ⟨t, rfl⟩))) hfi
    have hb := S.topologicalClosure.smul_mem (μ.real Set.univ) ha
    rwa [measure_smul_average] at hb
  apply hclosure
  change (∫ t, f t ∂μ) ∈ (S.topologicalClosure : Set (Ω →₂[P] ℝ)) at hmem
  rw [Submodule.topologicalClosure_coe] at hmem
  exact hmem

end CutoffRigidity
