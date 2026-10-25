module

public import CutoffRigidity.Riemann.TransportUpper

/-! # Transport, step 2b: sufficient conditions for the two kernel inputs

* `w2Contraction_of_coupling`: a measurable family of couplings `Q (x,y)` of `P x, P y` with
  `∫ d² dQ(x,y) ≤ q d(x,y)²` (the synchronous / parallel coupling of the diffusion) gives
  `W₂²`-contraction.
* `bind_eq_of_reversible`: a Markov kernel reversible with respect to `μ` leaves `μ` invariant.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace CutoffRigidity.Riemann

variable {M : Type*} [PseudoEMetricSpace M] [MeasurableSpace M]

theorem w2Contraction_of_coupling (P : Kernel M M) {q : ℝ≥0∞} (hq0 : q ≠ 0) (hqT : q ≠ ⊤)
    (Q : Kernel (M × M) (M × M))
    (hQ1 : ∀ z, (Q z).map Prod.fst = P z.1) (hQ2 : ∀ z, (Q z).map Prod.snd = P z.2)
    (hcost : ∀ z : M × M, ∫⁻ w, edist w.1 w.2 ^ 2 ∂Q z ≤ q * edist z.1 z.2 ^ 2) :
    W2Contraction P q := by
  intro ν ν' _ _
  unfold cost2
  rw [ENNReal.mul_iInf_of_ne hq0 hqT]
  refine le_iInf fun π => ?_
  rw [ENNReal.mul_iInf_of_ne hq0 hqT]
  refine le_iInf fun hπ => ?_
  have hm : (π.bind Q).map Prod.fst = ν.bind P ∧ (π.bind Q).map Prod.snd = ν'.bind P := by
    constructor
    · rw [← hπ.1]
      ext s hs
      rw [Measure.map_apply measurable_fst hs,
        Measure.bind_apply (measurable_fst hs) Q.measurable.aemeasurable,
        Measure.bind_apply hs P.measurable.aemeasurable,
        lintegral_map (Kernel.measurable_coe P hs) measurable_fst]
      refine lintegral_congr fun z => ?_
      rw [← hQ1 z, Measure.map_apply measurable_fst hs]
    · rw [← hπ.2]
      ext s hs
      rw [Measure.map_apply measurable_snd hs,
        Measure.bind_apply (measurable_snd hs) Q.measurable.aemeasurable,
        Measure.bind_apply hs P.measurable.aemeasurable,
        lintegral_map (Kernel.measurable_coe P hs) measurable_snd]
      refine lintegral_congr fun z => ?_
      rw [← hQ2 z, Measure.map_apply measurable_snd hs]
  refine (cost2_le_cost _ hm).trans ?_
  refine (Measure.lintegral_bind_le _ π Q.measurable.aemeasurable).trans ?_
  calc ∫⁻ z, ∫⁻ w, edist w.1 w.2 ^ 2 ∂Q z ∂π ≤ ∫⁻ z, q * edist z.1 z.2 ^ 2 ∂π :=
        lintegral_mono hcost
    _ = q * ∫⁻ z, edist z.1 z.2 ^ 2 ∂π := lintegral_const_mul' _ _ hqT

/-- A Markov kernel reversible with respect to `μ` leaves `μ` invariant. -/
theorem bind_eq_of_reversible (μ : Measure M) (P : Kernel M M) [IsMarkovKernel P]
    (hrev : ∀ A B : Set M, MeasurableSet A → MeasurableSet B →
      ∫⁻ x in A, P x B ∂μ = ∫⁻ x in B, P x A ∂μ) : μ.bind P = μ := by
  ext A hA
  rw [Measure.bind_apply hA P.measurable.aemeasurable]
  have h := hrev A univ hA MeasurableSet.univ
  simp only [measure_univ, lintegral_const, Measure.restrict_apply_univ, one_mul] at h
  rw [h, Measure.restrict_univ]

end CutoffRigidity.Riemann
