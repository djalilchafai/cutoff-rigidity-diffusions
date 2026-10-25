module
public import CutoffRigidity.TransportMoments
public import Mathlib.MeasureTheory.Measure.Prokhorov
public import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric
public import Mathlib.MeasureTheory.Measure.Portmanteau

/-! # Genuine weak limits of cost-bounded couplings

Converging actual marginals force tightness. Prokhorov gives an actual
subsequential coupling limit and Portmanteau preserves its quadratic budget.
-/
public section
namespace CutoffRigidity
open MeasureTheory Filter Set
open scoped Topology ENNReal
variable {E : Type*} [NormedAddCommGroup E] [CompleteSpace E] [MeasurableSpace E]
  [BorelSpace E] [SecondCountableTopology E]

theorem isCompact_closure_range_of_tendsto {A : Type*} [TopologicalSpace A] [T2Space A]
    {f : ℕ → A} {a : A} (hf : Tendsto f atTop (𝓝 a)) : IsCompact (closure (range f)) := by
  have hc := hf.isCompact_insert_range
  exact hc.of_isClosed_subset isClosed_closure
    (closure_minimal (subset_insert a (range f)) hc.isClosed)

set_option maxHeartbeats 800000 in
/-- Source-free compactness bridge for actual coupling measures. It is used
with couplings constructed by compact-space strong duality. -/
theorem exists_coupling_limit_of_marginals_tendsto
    (πn : ℕ → ProbabilityMeasure (E×E)) (μ ν : ProbabilityMeasure E)
    (hFirst : Tendsto (fun n => (πn n).map Prod.fst) atTop (𝓝 μ))
    (hSecond : Tendsto (fun n => (πn n).map Prod.snd) atTop (𝓝 ν))
    (K : ENNReal) (hCost : ∀ n, (∫⁻ z, edist z.1 z.2^2 ∂(πn n : Measure (E×E))) ≤ K) :
    ∃ π : Coupling (μ : Measure E) (ν : Measure E),
      (∫⁻ z, edist z.1 z.2^2 ∂π.val) ≤ K := by
  have hTF := isTightMeasureSet_of_isCompact_closure (isCompact_closure_range_of_tendsto hFirst)
  have hTS := isTightMeasureSet_of_isCompact_closure (isCompact_closure_range_of_tendsto hSecond)
  let R : Set (Measure (E×E)) := range (fun n => (πn n : Measure (E×E)))
  have hRF : IsTightMeasureSet (Measure.fst '' R) := by
    convert! hTF using 1
    ext m
    constructor
    · rintro ⟨q,⟨n,rfl⟩,rfl⟩
      exact ⟨(πn n).map Prod.fst,⟨n,rfl⟩,rfl⟩
    · rintro ⟨q,⟨n,rfl⟩,rfl⟩
      exact ⟨(πn n : Measure (E×E)),⟨n,rfl⟩,rfl⟩
  have hRS : IsTightMeasureSet (Measure.snd '' R) := by
    convert! hTS using 1
    ext m
    constructor
    · rintro ⟨q,⟨n,rfl⟩,rfl⟩
      exact ⟨(πn n).map Prod.snd,⟨n,rfl⟩,rfl⟩
    · rintro ⟨q,⟨n,rfl⟩,rfl⟩
      exact ⟨(πn n : Measure (E×E)),⟨n,rfl⟩,rfl⟩
  have hT : IsTightMeasureSet R := hRF.prodMk hRS
  have hT' : IsTightMeasureSet {((q : ProbabilityMeasure (E×E)) : Measure (E×E)) | q ∈ range πn} := by
    convert! hT using 1
    ext m
    simp only [R,mem_setOf_eq,mem_range]
    constructor
    · rintro ⟨q,⟨n,rfl⟩,rfl⟩; exact ⟨n,rfl⟩
    · rintro ⟨n,rfl⟩; exact ⟨πn n,⟨n,rfl⟩,rfl⟩
  have hCompact := isCompact_closure_of_isTightMeasureSet hT'
  obtain ⟨π,hπ,φ,hφ,hlim⟩ := hCompact.tendsto_subseq (fun n => subset_closure (mem_range_self n))
  have hfLim := ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous _ _ hlim continuous_fst
  have hsLim := ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous _ _ hlim continuous_snd
  have hF : π.map Prod.fst = μ := tendsto_nhds_unique hfLim (hFirst.comp hφ.tendsto_atTop)
  have hS : π.map Prod.snd = ν := tendsto_nhds_unique hsLim (hSecond.comp hφ.tendsto_atTop)
  refine ⟨⟨(π : Measure (E×E)),?_,?_⟩,?_⟩
  · have hh := congrArg (fun q : ProbabilityMeasure E => (q : Measure E)) hF
    simpa only [ProbabilityMeasure.toMeasure_map,continuous_fst.measurable.aemeasurable,
      dite_true] using hh
  · have hh := congrArg (fun q : ProbabilityMeasure E => (q : Measure E)) hS
    simpa only [ProbabilityMeasure.toMeasure_map,continuous_snd.measurable.aemeasurable,
      dite_true] using hh
  have hLSC := lintegral_le_liminf_lintegral_of_forall_isOpen_measure_le_liminf_measure
    (μ := (π : Measure (E×E))) (μs := fun n => (πn (φ n) : Measure (E×E)))
    (f := fun z : E×E => ‖z.1-z.2‖^2) (by fun_prop) (fun z => sq_nonneg _)
    (fun G hG => ProbabilityMeasure.le_liminf_measure_open_of_tendsto hlim hG)
  have he (z : E×E) : ENNReal.ofReal (‖z.1-z.2‖^2) = edist z.1 z.2^2 := by
    rw [edist_dist,dist_eq_norm,ENNReal.ofReal_pow (norm_nonneg _) 2]
  simp_rw [he] at hLSC
  exact hLSC.trans (liminf_le_of_frequently_le (Frequently.of_forall fun n => hCost (φ n)))

end CutoffRigidity
