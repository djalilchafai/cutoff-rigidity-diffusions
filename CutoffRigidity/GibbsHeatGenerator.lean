module
public import CutoffRigidity.GibbsHeatIntegral
public import CutoffRigidity.GibbsGeneratorExtension

/-! # Actual operator-domain evolution for canonical Gibbs heat

The resolvent evolution identity is proved on true operator eigenspaces and
extended as an equality of bounded operators, then differentiated by FTC.
-/
public section
namespace CutoffRigidity
open MeasureTheory Filter Topology
variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

theorem gibbsHeatSemigroup_commutes_resolvent
    {V : E → ℝ} (hV : ContDiff ℝ 2 V)
    (hprob : IsProbabilityMeasure (gibbsMeasure volume V))
    (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (t : NNReal) :
    (gibbsHeatSemigroup hV hprob ρ hρ hHess t).comp (gibbsL2Resolvent hV hprob) =
      (gibbsL2Resolvent hV hprob).comp (gibbsHeatSemigroup hV hprob ρ hρ hHess t) := by
  apply gibbsCLM_eq_of_operatorEigen hV hprob ρ hρ hHess
  intro rate hrate u hu
  have hr : gibbsL2Resolvent hV hprob u = (1 + rate)⁻¹ • u := by
    simpa only [gibbsScaledL2Resolvent_one, one_mul] using
      gibbsScaledL2Resolvent_operatorEigen hV hprob 1 zero_lt_one rate hrate u hu
  change gibbsHeatSemigroup hV hprob ρ hρ hHess t (gibbsL2Resolvent hV hprob u) =
    gibbsL2Resolvent hV hprob (gibbsHeatSemigroup hV hprob ρ hρ hHess t u)
  rw [hr, map_smul, gibbsHeatSemigroup_operatorEigen hV hprob ρ hρ hHess t rate hrate u hu,
    map_smul, hr, smul_smul, smul_smul]
  congr 1
  exact mul_comm _ _

/-- The actual integrated heat-generator equation on the resolvent range. -/
theorem gibbsHeatSemigroup_resolvent_integral
    {V : E → ℝ} (hV : ContDiff ℝ 2 V)
    (hprob : IsProbabilityMeasure (gibbsMeasure volume V))
    (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (t : NNReal) (f : E →₂[gibbsMeasure volume V] ℝ) :
    gibbsHeatSemigroup hV hprob ρ hρ hHess t (gibbsL2Resolvent hV hprob f) =
      gibbsL2Resolvent hV hprob f -
        ∫ s in (0 : ℝ)..(t : ℝ), gibbsHeatSemigroup hV hprob ρ hρ hHess s.toNNReal
          (f - gibbsL2Resolvent hV hprob f) := by
  have heq : (gibbsHeatSemigroup hV hprob ρ hρ hHess t).comp (gibbsL2Resolvent hV hprob) =
      gibbsL2Resolvent hV hprob - (gibbsHeatTimeIntegral hV hprob ρ hρ hHess t).comp
        (ContinuousLinearMap.id ℝ _ - gibbsL2Resolvent hV hprob) := by
    apply gibbsCLM_eq_of_operatorEigen hV hprob ρ hρ hHess
    intro rate hrate u hu
    have hr : gibbsL2Resolvent hV hprob u = (1 + rate)⁻¹ • u := by
      simpa only [gibbsScaledL2Resolvent_one, one_mul] using
        gibbsScaledL2Resolvent_operatorEigen hV hprob 1 zero_lt_one rate hrate u hu
    have hsub : u - (1 + rate)⁻¹ • u = (1 - (1 + rate)⁻¹) • u := by
      rw [sub_smul, one_smul]
    change gibbsHeatSemigroup hV hprob ρ hρ hHess t (gibbsL2Resolvent hV hprob u) =
      gibbsL2Resolvent hV hprob u - gibbsHeatTimeIntegral hV hprob ρ hρ hHess t (u - gibbsL2Resolvent hV hprob u)
    rw [hr, map_smul, gibbsHeatSemigroup_operatorEigen hV hprob ρ hρ hHess t rate hrate u hu,
      hsub, map_smul, gibbsHeatTimeIntegral_operatorEigen hV hprob ρ hρ hHess t rate hrate u hu,
      smul_smul, smul_smul, ← sub_smul]
    congr 1
    have hh := heat_resolvent_scalar_identity (t : ℝ) rate hrate
    nlinarith only [hh]
  have hf := congrArg (fun F => F f) heq
  exact hf

/-- The genuine A-domain is preserved, with its true operator value
commuting with heat evolution. -/
theorem gibbsHeatSemigroup_preserves_operatorGraph
    {V : E → ℝ} (hV : ContDiff ℝ 2 V)
    (hprob : IsProbabilityMeasure (gibbsMeasure volume V))
    (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (t : NNReal) (u g : E →₂[gibbsMeasure volume V] ℝ)
    (hg : (u, g) ∈ (gibbsPositiveGenerator hV hprob).graph) :
    (gibbsHeatSemigroup hV hprob ρ hρ hHess t u, gibbsHeatSemigroup hV hprob ρ hρ hHess t g) ∈
      (gibbsPositiveGenerator hV hprob).graph := by
  change (u, g) ∈ (positiveResolventOperator (gibbsL2Resolvent hV hprob)).graph at hg
  rw [positiveResolventOperator_graph _ (gibbsL2Resolvent_injective hV hprob), mem_positiveResolventGraph] at hg
  obtain ⟨q, hq, hg⟩ := hg
  change _ ∈ (positiveResolventOperator (gibbsL2Resolvent hV hprob)).graph
  rw [positiveResolventOperator_graph _ (gibbsL2Resolvent_injective hV hprob), mem_positiveResolventGraph]
  refine ⟨gibbsHeatSemigroup hV hprob ρ hρ hHess t q, ?_, ?_⟩
  · have hc := congrArg (fun F => F q) (gibbsHeatSemigroup_commutes_resolvent hV hprob ρ hρ hHess t)
    change gibbsHeatSemigroup hV hprob ρ hρ hHess t (gibbsL2Resolvent hV hprob q) =
      gibbsL2Resolvent hV hprob (gibbsHeatSemigroup hV hprob ρ hρ hHess t q) at hc
    rw [← hc, hq]
  · have hc := congrArg (fun F => F q) (gibbsHeatSemigroup_commutes_resolvent hV hprob ρ hρ hHess t)
    change gibbsHeatSemigroup hV hprob ρ hρ hHess t (gibbsL2Resolvent hV hprob q) =
      gibbsL2Resolvent hV hprob (gibbsHeatSemigroup hV hprob ρ hρ hHess t q) at hc
    rw [← hc, ← map_sub, hg]

/-- The actual heat evolution satisfies the integrated generator equation
for every vector in the genuine self-adjoint operator domain. -/
theorem gibbsHeatSemigroup_integral_of_graph
    {V : E → ℝ} (hV : ContDiff ℝ 2 V)
    (hprob : IsProbabilityMeasure (gibbsMeasure volume V))
    (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (t : NNReal) (u g : E →₂[gibbsMeasure volume V] ℝ)
    (hg : (u, g) ∈ (gibbsPositiveGenerator hV hprob).graph) :
    gibbsHeatSemigroup hV hprob ρ hρ hHess t u = u -
      ∫ s in (0 : ℝ)..(t : ℝ), gibbsHeatSemigroup hV hprob ρ hρ hHess s.toNNReal g := by
  change (u, g) ∈ (positiveResolventOperator (gibbsL2Resolvent hV hprob)).graph at hg
  rw [positiveResolventOperator_graph _ (gibbsL2Resolvent_injective hV hprob), mem_positiveResolventGraph] at hg
  obtain ⟨q, hq, hg⟩ := hg
  have he := gibbsHeatSemigroup_resolvent_integral hV hprob ρ hρ hHess t q
  rw [hg, hq] at he
  exact he

/-- The actual A-domain trajectory has the prescribed right derivative,
including the initial time, by the genuine Bochner integral FTC. -/
theorem gibbsHeatSemigroup_hasDerivWithinAt_operatorGraph
    {V : E → ℝ} (hV : ContDiff ℝ 2 V)
    (hprob : IsProbabilityMeasure (gibbsMeasure volume V))
    (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (t : ℝ) (ht : 0 ≤ t) (u g : E →₂[gibbsMeasure volume V] ℝ)
    (hg : (u, g) ∈ (gibbsPositiveGenerator hV hprob).graph) :
    HasDerivWithinAt (fun s : ℝ => gibbsHeatSemigroup hV hprob ρ hρ hHess s.toNNReal u)
      (-gibbsHeatSemigroup hV hprob ρ hρ hHess t.toNNReal g) (Set.Ici 0) t := by
  let P := gibbsHeatSemigroup hV hprob ρ hρ hHess
  have hc : Continuous (fun s : ℝ => P s.toNNReal g) :=
    (continuous_gibbsHeatSemigroup_apply hV hprob ρ hρ hHess g).comp continuous_real_toNNReal
  have hm : StronglyMeasurableAtFilter (fun s : ℝ => P s.toNNReal g) (𝓝 t) volume :=
    hc.stronglyMeasurable.stronglyMeasurableAtFilter
  have hd := (intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable 0 t) hm hc.continuousAt).const_sub u
  have heq (s : ℝ) (hs : s ∈ Set.Ici 0) : P s.toNNReal u = u - ∫ r in (0 : ℝ)..s, P r.toNNReal g := by
    have he := gibbsHeatSemigroup_integral_of_graph hV hprob ρ hρ hHess s.toNNReal u g hg
    simpa only [Real.coe_toNNReal s hs] using he
  exact hd.hasDerivWithinAt.congr_of_mem heq ht

/-- At positive times the actual domain trajectory has a full derivative. -/
theorem gibbsHeatSemigroup_hasDerivAt_operatorGraph
    {V : E → ℝ} (hV : ContDiff ℝ 2 V)
    (hprob : IsProbabilityMeasure (gibbsMeasure volume V))
    (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (t : ℝ) (ht : 0 < t) (u g : E →₂[gibbsMeasure volume V] ℝ)
    (hg : (u, g) ∈ (gibbsPositiveGenerator hV hprob).graph) :
    HasDerivAt (fun s : ℝ => gibbsHeatSemigroup hV hprob ρ hρ hHess s.toNNReal u)
      (-gibbsHeatSemigroup hV hprob ρ hρ hHess t.toNNReal g) t :=
  (gibbsHeatSemigroup_hasDerivWithinAt_operatorGraph hV hprob ρ hρ hHess t ht.le u g hg).hasDerivAt
    (Ici_mem_nhds ht)

end CutoffRigidity
