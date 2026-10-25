module
public import CutoffRigidity.GibbsEulerApproximation

/-! # Canonical Gibbs L² heat evolution from genuine implicit Euler limits

This is the heat evolution of the actual closed form operator. Identification
with the Brownian Langevin kernel is a separate theorem.
-/
public section
namespace CutoffRigidity
open MeasureTheory Filter Topology
variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

@[expose] noncomputable def gibbsHeatSemigroup
    {V : E → ℝ} (hV : ContDiff ℝ 2 V)
    (hprob : IsProbabilityMeasure (gibbsMeasure volume V))
    (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (t : NNReal) : (E →₂[gibbsMeasure volume V] ℝ) →L[ℝ] (E →₂[gibbsMeasure volume V] ℝ) := by
  let F := gibbsEulerApproximation hV hprob t
  let p := fun u => Classical.choose (gibbsEulerApproximation_exists_limit hV hprob ρ hρ hHess t u)
  have hp : Tendsto (fun n u => F n u) atTop (𝓝 p) := tendsto_pi_nhds.mpr
    (fun u => Classical.choose_spec (gibbsEulerApproximation_exists_limit hV hprob ρ hρ hHess t u))
  have hb : Bornology.IsBounded (Set.range F) := by
    apply isBounded_iff_forall_norm_le.mpr
    refine ⟨1, ?_⟩
    rintro _ ⟨n, rfl⟩
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro u
    simpa only [one_mul] using norm_gibbsEulerApproximation_apply_le hV hprob t n u
  exact ContinuousLinearMap.ofTendstoOfBoundedRange p F hp hb

theorem gibbsEulerApproximation_tendsto_heat
    {V : E → ℝ} (hV : ContDiff ℝ 2 V)
    (hprob : IsProbabilityMeasure (gibbsMeasure volume V))
    (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (t : NNReal) (u : E →₂[gibbsMeasure volume V] ℝ) :
    Tendsto (fun n => gibbsEulerApproximation hV hprob t n u) atTop
      (𝓝 (gibbsHeatSemigroup hV hprob ρ hρ hHess t u)) := by
  exact Classical.choose_spec (gibbsEulerApproximation_exists_limit hV hprob ρ hρ hHess t u)

theorem norm_gibbsHeatSemigroup_apply_le
    {V : E → ℝ} (hV : ContDiff ℝ 2 V)
    (hprob : IsProbabilityMeasure (gibbsMeasure volume V))
    (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (t : NNReal) (u : E →₂[gibbsMeasure volume V] ℝ) :
    ‖gibbsHeatSemigroup hV hprob ρ hρ hHess t u‖ ≤ ‖u‖ :=
  le_of_tendsto (gibbsEulerApproximation_tendsto_heat hV hprob ρ hρ hHess t u).norm
    (Eventually.of_forall (fun n => norm_gibbsEulerApproximation_apply_le hV hprob t n u))

theorem gibbsHeatSemigroup_operatorEigen
    {V : E → ℝ} (hV : ContDiff ℝ 2 V)
    (hprob : IsProbabilityMeasure (gibbsMeasure volume V))
    (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (t : NNReal) (rate : ℝ) (hrate : 0 ≤ rate) (u : E →₂[gibbsMeasure volume V] ℝ)
    (hu : (u, rate • u) ∈ (gibbsPositiveGenerator hV hprob).graph) :
    gibbsHeatSemigroup hV hprob ρ hρ hHess t u = Real.exp (-(t : ℝ) * rate) • u :=
  tendsto_nhds_unique (gibbsEulerApproximation_tendsto_heat hV hprob ρ hρ hHess t u)
    (gibbsEulerApproximation_tendsto_operatorEigen hV hprob t rate hrate u hu)

/-- Equality of actual bounded operators can be verified on true A eigenspaces. -/
theorem gibbsCLM_eq_of_operatorEigen
    {V : E → ℝ} (hV : ContDiff ℝ 2 V)
    (hprob : IsProbabilityMeasure (gibbsMeasure volume V))
    (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (F G : (E →₂[gibbsMeasure volume V] ℝ) →L[ℝ] (E →₂[gibbsMeasure volume V] ℝ))
    (heq : ∀ rate : ℝ, ∀ _hrate : 0 ≤ rate, ∀ u : E →₂[gibbsMeasure volume V] ℝ,
      (u, rate • u) ∈ (gibbsPositiveGenerator hV hprob).graph → F u = G u) : F = G := by
  let S := (F - G).ker
  have hle : (⨆ rate : ℝ, gibbsOperatorEigenspace hV hprob rate) ≤ S := by
    apply iSup_le
    intro rate u hu
    change (F - G) u = 0
    by_cases hu0 : u = 0
    · simp [hu0]
    · have hrate := gibbsOperatorEigenvalue_nonneg hV hprob rate ⟨u, hu⟩
        (by intro hz; exact hu0 (congrArg Subtype.val hz))
      exact sub_eq_zero.mpr (heq rate hrate u hu)
  have hi : Sᗮ = ⊥ := by
    have hh := Submodule.orthogonal_le hle
    rw [gibbsOperator_eigenspaces_orthogonal_eq_bot hV hprob ρ hρ hHess] at hh
    exact le_antisymm hh bot_le
  let : CompleteSpace S := (F - G).isClosed_ker.completeSpace_coe
  have htop : S = ⊤ := Submodule.orthogonal_eq_bot_iff.mp hi
  apply ContinuousLinearMap.ext
  intro u
  have hu : u ∈ S := by rw [htop]; trivial
  exact sub_eq_zero.mp hu

theorem gibbsHeatSemigroup_zero
    {V : E → ℝ} (hV : ContDiff ℝ 2 V)
    (hprob : IsProbabilityMeasure (gibbsMeasure volume V))
    (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z) :
    gibbsHeatSemigroup hV hprob ρ hρ hHess 0 = ContinuousLinearMap.id ℝ _ := by
  apply ContinuousLinearMap.ext
  intro u
  apply tendsto_nhds_unique (gibbsEulerApproximation_tendsto_heat hV hprob ρ hρ hHess 0 u)
  simp [gibbsEulerApproximation_zero]

theorem gibbsHeatSemigroup_add
    {V : E → ℝ} (hV : ContDiff ℝ 2 V)
    (hprob : IsProbabilityMeasure (gibbsMeasure volume V))
    (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (s t : NNReal) :
    gibbsHeatSemigroup hV hprob ρ hρ hHess (s + t) =
      (gibbsHeatSemigroup hV hprob ρ hρ hHess s).comp (gibbsHeatSemigroup hV hprob ρ hρ hHess t) := by
  apply gibbsCLM_eq_of_operatorEigen hV hprob ρ hρ hHess
  intro rate hrate u hu
  change _ = gibbsHeatSemigroup hV hprob ρ hρ hHess s (gibbsHeatSemigroup hV hprob ρ hρ hHess t u)
  rw [gibbsHeatSemigroup_operatorEigen hV hprob ρ hρ hHess (s + t) rate hrate u hu,
    gibbsHeatSemigroup_operatorEigen hV hprob ρ hρ hHess t rate hrate u hu, map_smul,
    gibbsHeatSemigroup_operatorEigen hV hprob ρ hρ hHess s rate hrate u hu, smul_smul]
  congr 1
  rw [← Real.exp_add]
  congr 1
  simp only [NNReal.coe_add]
  ring

/-- Strong continuity of the actual implicit-Euler heat evolution. -/
theorem continuous_gibbsHeatSemigroup_apply
    {V : E → ℝ} (hV : ContDiff ℝ 2 V)
    (hprob : IsProbabilityMeasure (gibbsMeasure volume V))
    (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (u : E →₂[gibbsMeasure volume V] ℝ) :
    Continuous (fun t : NNReal => gibbsHeatSemigroup hV hprob ρ hρ hHess t u) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  let P := gibbsHeatSemigroup hV hprob ρ hρ hHess
  let S := strongContinuityDomain P t
  have hs : IsClosed (S : Set (E →₂[gibbsMeasure volume V] ℝ)) :=
    strongContinuityDomain_isClosed P t (norm_gibbsHeatSemigroup_apply_le hV hprob ρ hρ hHess)
  have hle : (⨆ rate : ℝ, gibbsOperatorEigenspace hV hprob rate) ≤ S := by
    apply iSup_le
    intro rate v hv
    change ContinuousAt (fun s => P s v) t
    by_cases hv0 : v = 0
    · simp only [hv0, map_zero]
      exact continuousAt_const
    · have hrate := gibbsOperatorEigenvalue_nonneg hV hprob rate ⟨v, hv⟩
        (by intro hz; exact hv0 (congrArg Subtype.val hz))
      have heq : (fun s => P s v) = (fun s : NNReal => Real.exp (-(s : ℝ) * rate) • v) := by
        funext s
        exact gibbsHeatSemigroup_operatorEigen hV hprob ρ hρ hHess s rate hrate v hv
      rw [heq]
      exact (by fun_prop : Continuous (fun s : NNReal => Real.exp (-(s : ℝ) * rate) • v)).continuousAt
  have hi : Sᗮ = ⊥ := by
    have hh := Submodule.orthogonal_le hle
    rw [gibbsOperator_eigenspaces_orthogonal_eq_bot hV hprob ρ hρ hHess] at hh
    exact le_antisymm hh bot_le
  let : CompleteSpace S := hs.completeSpace_coe
  have htop : S = ⊤ := Submodule.orthogonal_eq_bot_iff.mp hi
  have hu : u ∈ S := by rw [htop]; trivial
  exact hu

end CutoffRigidity
