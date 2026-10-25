module
public import CutoffRigidity.ProductConditionCutoff

/-! # The information part of the source curvature-product theorem

This combines the actual TV and entropy cutoff endpoints for every fixed
precision parameter. All process and threshold objects are genuine; there
are no scalar-profile or mixing-window assumptions in the source data.
-/
public section
namespace CutoffRigidity
open MeasureTheory Filter Set
open scoped Topology ENNReal

/-- The TV and entropy assertions of the written curvature-product theorem,
for arbitrary actual probability spaces in the varying dimensions. -/
theorem curvature_product_condition_tv_entropy
    {Ξ : ℕ → Type*} [∀ n, MeasurableSpace (Ξ n)]
    (D : ∀ n : ℕ, CurvedLangevinData (Ξ n) n)
    (S : ∀ n : ℕ, Set (EuclideanSpace ℝ (Fin n))) (hS : ∀ n, (S n).Nonempty)
    (η : ℝ) (hη : 0 < η) (hη1 : η < 1)
    (hfinite : ∀ᶠ n in atTop, curvedMixingTime (D n) (S n) η < ⊤)
    (hprod : Tendsto (fun n => (D n).curvature*curvedCriticalTime (D n) (S n) η) atTop atTop) :
    ∀ ε : ℝ, 0 < ε → ε < 1 →
      Tendsto (fun n => curvedTVProfile (D n) (S n) ((1-ε)*curvedCriticalTime (D n) (S n) η)) atTop (𝓝 1) ∧
      Tendsto (fun n => curvedTVProfile (D n) (S n) ((1+ε)*curvedCriticalTime (D n) (S n) η)) atTop (𝓝 0) ∧
      Tendsto (fun n => curvedEntropyProfile (D n) (S n) ((1-ε)*curvedCriticalTime (D n) (S n) η)) atTop (𝓝 ⊤) ∧
      Tendsto (fun n => curvedEntropyProfile (D n) (S n) ((1+ε)*curvedCriticalTime (D n) (S n) η)) atTop (𝓝 0) := by
  intro ε hε hε1
  exact ⟨productCondition_totalVariation_before_cutoff D S hS η ε hη hε hε1 hfinite hprod,
    productCondition_totalVariation_after_cutoff D S hS η ε hη hη1 hε hfinite hprod,
    productCondition_entropy_before_cutoff D S hS η ε hη hε hε1 hfinite hprod,
    productCondition_entropy_after_cutoff D S hS η ε hη hη1 hε hfinite hprod⟩

/-- The full genuine Fisher assertions under the source additional lower
curvature and diverging mixing-time hypotheses. -/
theorem curvature_product_condition_fisher
    {Ξ : ℕ → Type*} [∀ n, MeasurableSpace (Ξ n)]
    (D : ∀ n : ℕ, CurvedLangevinData (Ξ n) n)
    (S : ∀ n : ℕ, Set (EuclideanSpace ℝ (Fin n))) (hS : ∀ n, (S n).Nonempty)
    (η : ℝ) (hη : 0 < η) (hη1 : η < 1)
    (hfinite : ∀ᶠ n in atTop, curvedMixingTime (D n) (S n) η < ⊤)
    (hprod : Tendsto (fun n => (D n).curvature*curvedCriticalTime (D n) (S n) η) atTop atTop)
    (hliminf : 0 < liminf (fun n => ENNReal.ofReal (D n).curvature) atTop)
    (ht0 : Tendsto (fun n => curvedCriticalTime (D n) (S n) η) atTop atTop) :
    ∀ ε : ℝ, 0 < ε → ε < 1 →
      Tendsto (fun n => curvedFisherProfile (D n) (S n) ((1-ε)*curvedCriticalTime (D n) (S n) η)) atTop (𝓝 ⊤) ∧
      Tendsto (fun n => curvedFisherProfile (D n) (S n) ((1+ε)*curvedCriticalTime (D n) (S n) η)) atTop (𝓝 0) := by
  intro ε hε hε1
  exact ⟨productCondition_fisher_before_cutoff D S hS η ε hη hε hε1 hfinite hprod hliminf,
    productCondition_fisher_after_cutoff D S hS η ε hη hη1 hε hfinite ht0⟩

end CutoffRigidity
