module

public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
public import Mathlib.MeasureTheory.Integral.Prod

/-! # Conditional Fubini from set-integral characterization

The identity is proved by ordinary Fubini on every set in the conditioning
sigma algebra. No equality between jointly selected conditional-expectation
representatives is required.
-/

public section

namespace CutoffRigidity

open MeasureTheory Set Filter

/-- Conditional expectation commutes with a finite time integral for actual
bounded jointly measurable integrands. Conditional values are only required
a.e. separately at each time; set-integral Fubini handles the quantifiers. -/
theorem condExp_integral_of_bounded_jointly_measurable
    {I Ω : Type*} [MeasurableSpace I] [mΩ : MeasurableSpace Ω]
    (η : Measure I) [IsFiniteMeasure η] (P : Measure Ω) [IsProbabilityMeasure P]
    (F G : I → Ω → ℝ)
    (hF : StronglyMeasurable (Function.uncurry F))
    (hG : StronglyMeasurable (Function.uncurry G))
    (σ : MeasurableSpace Ω) (hσ : σ ≤ mΩ)
    (hFb : ∃ M : ℝ, ∀ r ω, ‖F r ω‖ ≤ M)
    (hGb : ∃ N : ℝ, ∀ r ω, ‖G r ω‖ ≤ N)
    (hgm : AEStronglyMeasurable[σ] (fun ω => ∫ r, G r ω ∂η) P)
    (hcond : ∀ r, P[F r | σ] =ᵐ[P] G r) :
    P[fun ω => ∫ r, F r ω ∂η | σ] =ᵐ[P] fun ω => ∫ r, G r ω ∂η := by
  let : MeasurableSpace Ω := mΩ
  obtain ⟨M, hM⟩ := hFb
  obtain ⟨N, hN⟩ := hGb
  have hFprod : Integrable (Function.uncurry F) (η.prod P) :=
    Integrable.mono' (integrable_const M) hF.aestronglyMeasurable
      (Filter.Eventually.of_forall (fun p => hM p.1 p.2))
  have hGprod : Integrable (Function.uncurry G) (η.prod P) :=
    Integrable.mono' (integrable_const N) hG.aestronglyMeasurable
      (Filter.Eventually.of_forall (fun p => hN p.1 p.2))
  have hFr (r : I) : Integrable (F r) P :=
    Integrable.mono' (integrable_const M) hF.of_uncurry_left.aestronglyMeasurable
      (Filter.Eventually.of_forall (hM r))
  have h := ae_eq_condExp_of_forall_setIntegral_eq hσ hFprod.integral_prod_right
    (fun S _ _ => hGprod.integral_prod_right.integrableOn) (g := fun ω => ∫ r, G r ω ∂η) ?_ hgm
  · exact h.symm
  · intro S hS _
    have hSamb : MeasurableSet S := hσ S hS
    have hFprodS : Integrable (Function.uncurry F) (η.prod (P.restrict S)) :=
      Integrable.mono' (integrable_const M) hF.aestronglyMeasurable
        (Filter.Eventually.of_forall (fun p => hM p.1 p.2))
    have hGprodS : Integrable (Function.uncurry G) (η.prod (P.restrict S)) :=
      Integrable.mono' (integrable_const N) hG.aestronglyMeasurable
        (Filter.Eventually.of_forall (fun p => hN p.1 p.2))
    calc
      _ = ∫ r, ∫ ω in S, G r ω ∂P ∂η := (integral_integral_swap hGprodS).symm
      _ = ∫ r, ∫ ω in S, F r ω ∂P ∂η := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall (fun r => by
          calc
            _ = ∫ ω in S, P[F r | σ] ω ∂P :=
              integral_congr_ae (ae_restrict_of_ae (hcond r).symm)
            _ = _ := setIntegral_condExp hσ (hFr r) hS)
      _ = _ := integral_integral_swap hFprodS

end CutoffRigidity
