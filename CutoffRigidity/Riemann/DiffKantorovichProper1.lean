module

public import CutoffRigidity.TransportCouplingCompactness

/-! # Kantorovich duality on a proper metric space, part 1: weak limits of couplings

Generalisation of `exists_coupling_limit_of_marginals_tendsto` from normed spaces to arbitrary
complete separable metric spaces: if the marginals of probability measures `πₙ` on `X × X`
converge weakly, a subsequence of `πₙ` converges weakly to a coupling of the limits, and the
integral of every nonnegative continuous function is lower semicontinuous along it.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped Topology ENNReal

namespace CutoffRigidity.Riemann

section

variable {X : Type*} [MetricSpace X] [CompleteSpace X] [MeasurableSpace X]
  [BorelSpace X] [SecondCountableTopology X]

set_option maxHeartbeats 800000 in
/-- Weak subsequential limit of probability measures on `X × X` whose marginals converge. -/
theorem exists_weak_limit_coupling
    (πn : ℕ → ProbabilityMeasure (X × X)) (μ ν : ProbabilityMeasure X)
    (hFirst : Tendsto (fun n => (πn n).map Prod.fst) atTop (𝓝 μ))
    (hSecond : Tendsto (fun n => (πn n).map Prod.snd) atTop (𝓝 ν)) :
    ∃ (π : ProbabilityMeasure (X × X)) (φ : ℕ → ℕ), StrictMono φ ∧
      π.map Prod.fst = μ ∧ π.map Prod.snd = ν ∧ Tendsto (fun n => πn (φ n)) atTop (𝓝 π) := by
  have hTF := isTightMeasureSet_of_isCompact_closure
    (CutoffRigidity.isCompact_closure_range_of_tendsto hFirst)
  have hTS := isTightMeasureSet_of_isCompact_closure
    (CutoffRigidity.isCompact_closure_range_of_tendsto hSecond)
  let R : Set (Measure (X × X)) := range (fun n => (πn n : Measure (X × X)))
  have hRF : IsTightMeasureSet (Measure.fst '' R) := by
    convert! hTF using 1
    ext m
    constructor
    · rintro ⟨q, ⟨n, rfl⟩, rfl⟩
      exact ⟨(πn n).map Prod.fst, ⟨n, rfl⟩, rfl⟩
    · rintro ⟨q, ⟨n, rfl⟩, rfl⟩
      exact ⟨(πn n : Measure (X × X)), ⟨n, rfl⟩, rfl⟩
  have hRS : IsTightMeasureSet (Measure.snd '' R) := by
    convert! hTS using 1
    ext m
    constructor
    · rintro ⟨q, ⟨n, rfl⟩, rfl⟩
      exact ⟨(πn n).map Prod.snd, ⟨n, rfl⟩, rfl⟩
    · rintro ⟨q, ⟨n, rfl⟩, rfl⟩
      exact ⟨(πn n : Measure (X × X)), ⟨n, rfl⟩, rfl⟩
  have hT : IsTightMeasureSet R := hRF.prodMk hRS
  have hT' : IsTightMeasureSet
      {((q : ProbabilityMeasure (X × X)) : Measure (X × X)) | q ∈ range πn} := by
    convert! hT using 1
    ext m
    simp only [R, mem_ofPred_eq, mem_range]
    constructor
    · rintro ⟨q, ⟨n, rfl⟩, rfl⟩; exact ⟨n, rfl⟩
    · rintro ⟨n, rfl⟩; exact ⟨πn n, ⟨n, rfl⟩, rfl⟩
  have hCompact := isCompact_closure_of_isTightMeasureSet hT'
  obtain ⟨π, hπ, φ, hφ, hlim⟩ :=
    hCompact.tendsto_subseq (fun n => subset_closure (mem_range_self n))
  have hfLim := ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous _ _ hlim continuous_fst
  have hsLim := ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous _ _ hlim continuous_snd
  exact ⟨π, φ, hφ, tendsto_nhds_unique hfLim (hFirst.comp hφ.tendsto_atTop),
    tendsto_nhds_unique hsLim (hSecond.comp hφ.tendsto_atTop), hlim⟩

/-- Lower semicontinuity of `∫⁻ ofReal h` along a weakly convergent sequence. -/
theorem lintegral_le_liminf_of_tendsto {Y : Type*} [MetricSpace Y] [MeasurableSpace Y]
    [BorelSpace Y] {πn : ℕ → ProbabilityMeasure Y} {π : ProbabilityMeasure Y}
    (hlim : Tendsto πn atTop (𝓝 π)) {h : Y → ℝ} (hc : Continuous h) (hnn : 0 ≤ h) :
    ∫⁻ y, ENNReal.ofReal (h y) ∂(π : Measure Y) ≤
      liminf (fun n => ∫⁻ y, ENNReal.ofReal (h y) ∂(πn n : Measure Y)) atTop :=
  lintegral_le_liminf_lintegral_of_forall_isOpen_measure_le_liminf_measure
    (μ := (π : Measure Y)) (μs := fun n => (πn n : Measure Y)) hc hnn
    (fun G hG => ProbabilityMeasure.le_liminf_measure_open_of_tendsto hlim hG)

end

end CutoffRigidity.Riemann
