module

public import CutoffRigidity.Transport

/-!
# Passing synchronous pathwise contraction to quadratic transport

For an actual measurable random update `T (x, ω)`, apply the same noise to
both coordinates of every coupling. A uniform pathwise Lipschitz bound then
gives the transport contraction. Constructing the Langevin solution map and
proving its pathwise bound remain separate analytic obligations.
-/

public section

namespace CutoffRigidity

open MeasureTheory
open scoped ENNReal NNReal

variable {E Ω : Type*} [MetricSpace E] [MeasurableSpace E] [BorelSpace E]
  [SecondCountableTopology E] [MeasurableSpace Ω]

/-- Law of a measurable update with independent initial state and driving noise. -/
@[expose] noncomputable def randomMapLaw (μ : Measure E) (η : Measure Ω)
    (T : E × Ω → E) : Measure E := (μ.prod η).map T

/-- The two updated states are coupled by giving them the same noise. -/
noncomputable def randomMapCoupling {μ ν : Measure E} [IsProbabilityMeasure μ]
    (π : Coupling μ ν) (η : Measure Ω) [IsProbabilityMeasure η]
    (T : E × Ω → E) (hT : Measurable T) :
    Coupling (randomMapLaw μ η T) (randomMapLaw ν η T) := by
  letI : IsProbabilityMeasure π.val := π.isProbabilityMeasure
  refine ⟨(π.val.prod η).map (fun z => (T (z.1.1, z.2), T (z.1.2, z.2))), ?_, ?_⟩
  · rw [Measure.map_map measurable_fst (by fun_prop)]
    have hprod : (π.val.prod η).map (Prod.map Prod.fst id) = μ.prod η := by
      rw [← Measure.map_prod_map _ _ measurable_fst measurable_id, π.property.1,
        Measure.map_id]
    change (π.val.prod η).map (T ∘ Prod.map Prod.fst id) = (μ.prod η).map T
    rw [← Measure.map_map hT (measurable_fst.prodMap measurable_id), hprod]
  · rw [Measure.map_map measurable_snd (by fun_prop)]
    have hprod : (π.val.prod η).map (Prod.map Prod.snd id) = ν.prod η := by
      rw [← Measure.map_prod_map _ _ measurable_snd measurable_id, π.property.2,
        Measure.map_id]
    change (π.val.prod η).map (T ∘ Prod.map Prod.snd id) = (ν.prod η).map T
    rw [← Measure.map_map hT (measurable_snd.prodMap measurable_id), hprod]

theorem randomMapCoupling_cost_le {μ ν : Measure E} [IsProbabilityMeasure μ]
    (π : Coupling μ ν) (η : Measure Ω) [IsProbabilityMeasure η]
    (T : E × Ω → E) (hT : Measurable T) (K : ℝ≥0)
    (hLip : ∀ ω, LipschitzWith K (fun x => T (x, ω))) :
    (∫⁻ z, edist z.1 z.2 ^ 2 ∂(randomMapCoupling π η T hT).val) ≤
      (K : ℝ≥0∞) ^ 2 * ∫⁻ z, edist z.1 z.2 ^ 2 ∂π.val := by
  have : IsProbabilityMeasure π.val := π.isProbabilityMeasure
  change (∫⁻ z, edist z.1 z.2 ^ 2
    ∂(π.val.prod η).map (fun z => (T (z.1.1, z.2), T (z.1.2, z.2)))) ≤ _
  rw [lintegral_map (by fun_prop) (by fun_prop)]
  calc
    _ ≤ ∫⁻ z : (E × E) × Ω,
        (K : ℝ≥0∞) ^ 2 * edist z.1.1 z.1.2 ^ 2 ∂π.val.prod η := by
      apply lintegral_mono
      intro z
      simpa only [mul_pow] using pow_le_pow_left' ((hLip z.2).edist_le_mul z.1.1 z.1.2) 2
    _ = _ := by
      have hi := lintegral_map (μ := π.val.prod η)
        (f := fun z : E × E => edist z.1 z.2 ^ 2) (by fun_prop) measurable_fst
      simp only [Measure.map_fst_prod, measure_univ, one_smul] at hi
      exact (lintegral_const_mul _ (by fun_prop)).trans
        (congrArg (fun r => (K : ℝ≥0∞) ^ 2 * r) hi.symm)

/-- Synchronous measurable random updates contract the genuine coupling
infimum when their pathwise Lipschitz constants are bounded uniformly. -/
theorem squaredWasserstein_randomMap_le (μ ν : Measure E)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (η : Measure Ω) [IsProbabilityMeasure η]
    (T : E × Ω → E) (hT : Measurable T) (K : ℝ≥0)
    (hLip : ∀ ω, LipschitzWith K (fun x => T (x, ω))) :
    squaredWasserstein (randomMapLaw μ η T) (randomMapLaw ν η T) ≤
      (K : ℝ≥0∞) ^ 2 * squaredWasserstein μ ν := by
  have : Nonempty (Coupling μ ν) := ⟨productCoupling μ ν⟩
  unfold squaredWasserstein
  rw [ENNReal.mul_iInf (by simp)]
  apply le_iInf
  intro π
  exact (iInf_le _ (randomMapCoupling π η T hT)).trans
    (randomMapCoupling_cost_le π η T hT K hLip)

end CutoffRigidity
