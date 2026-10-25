module
public import CutoffRigidity.ProductConditionWasserstein

/-! # The full curvature-product cutoff theorem for actual Langevin laws

The eight endpoints below use genuine total variation, relative entropy,
closed-domain relative Fisher information and quadratic Wasserstein coupling
cost. All estimates and mixing-window domains are derived from the actual
source data. The Wasserstein assertion is stated for its square, which has
exactly the same zero and infinite cutoff endpoints.
-/
public section
namespace CutoffRigidity
open MeasureTheory Filter Set
open scoped Topology ENNReal

/-- The source curvature-product theorem, including every one of its four
distances under the written additional assumptions for Fisher and W₂. -/
theorem curvature_product_condition_all_distances
    {Ξ : ℕ → Type*} [∀ n, MeasurableSpace (Ξ n)]
    (D : ∀ n : ℕ, CurvedLangevinData (Ξ n) n)
    (S : ∀ n : ℕ, Set (EuclideanSpace ℝ (Fin n))) (hS : ∀ n, (S n).Nonempty)
    (η : ℝ) (hη : 0 < η) (hη1 : η < 1)
    (hfinite : ∀ᶠ n in atTop, curvedMixingTime (D n) (S n) η < ⊤)
    (hprod : Tendsto (fun n => (D n).curvature*curvedCriticalTime (D n) (S n) η) atTop atTop)
    (hliminf : 0 < liminf (fun n => ENNReal.ofReal (D n).curvature) atTop)
    (ht0 : Tendsto (fun n => curvedCriticalTime (D n) (S n) η) atTop atTop) :
    ∀ ε : ℝ, 0 < ε → ε < 1 →
      Tendsto (fun n => curvedTVProfile (D n) (S n) ((1-ε)*curvedCriticalTime (D n) (S n) η)) atTop (𝓝 1) ∧
      Tendsto (fun n => curvedTVProfile (D n) (S n) ((1+ε)*curvedCriticalTime (D n) (S n) η)) atTop (𝓝 0) ∧
      Tendsto (fun n => curvedEntropyProfile (D n) (S n) ((1-ε)*curvedCriticalTime (D n) (S n) η)) atTop (𝓝 ⊤) ∧
      Tendsto (fun n => curvedEntropyProfile (D n) (S n) ((1+ε)*curvedCriticalTime (D n) (S n) η)) atTop (𝓝 0) ∧
      Tendsto (fun n => curvedFisherProfile (D n) (S n) ((1-ε)*curvedCriticalTime (D n) (S n) η)) atTop (𝓝 ⊤) ∧
      Tendsto (fun n => curvedFisherProfile (D n) (S n) ((1+ε)*curvedCriticalTime (D n) (S n) η)) atTop (𝓝 0) ∧
      Tendsto (fun n => curvedWassersteinSqProfile (D n) (S n) ((1-ε)*curvedCriticalTime (D n) (S n) η)) atTop (𝓝 ⊤) ∧
      Tendsto (fun n => curvedWassersteinSqProfile (D n) (S n) ((1+ε)*curvedCriticalTime (D n) (S n) η)) atTop (𝓝 0) := by
  intro ε hε hε1
  obtain ⟨hTVb,hTVa,hHb,hHa⟩ :=
    curvature_product_condition_tv_entropy D S hS η hη hη1 hfinite hprod ε hε hε1
  obtain ⟨hIb,hIa⟩ :=
    curvature_product_condition_fisher D S hS η hη hη1 hfinite hprod hliminf ht0 ε hε hε1
  obtain ⟨hWb,hWa⟩ :=
    curvature_product_condition_wasserstein D S hS η hη hη1 hfinite hprod hliminf ht0 ε hε hε1
  exact ⟨hTVb,hTVa,hHb,hHa,hIb,hIa,hWb,hWa⟩

end CutoffRigidity
