module
public import CutoffRigidity.GibbsHeatSemigroup
public import CutoffRigidity.GibbsEulerMarkov

/-! # Markov and Gibbs-preservation properties of actual form heat evolution -/
public section
namespace CutoffRigidity
open MeasureTheory Filter Topology
variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)


theorem gibbsHeatSemigroup_symmetric
    {V : E → ℝ} (hV : ContDiff ℝ 2 V)
  (hprob : IsProbabilityMeasure (gibbsMeasure volume V))
  (ρ : ℝ) (hρ : 0 < ρ)
  (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)

    (t : NNReal)
    (f g : E →₂[gibbsMeasure volume V] ℝ) :
    inner ℝ (gibbsHeatSemigroup hV hprob ρ hρ hHess t f) g =
      inner ℝ f (gibbsHeatSemigroup hV hprob ρ hρ hHess t g) := by
  have hl : Tendsto (fun n => inner ℝ (gibbsEulerApproximation hV hprob t n f) g) atTop
      (𝓝 (inner ℝ (gibbsHeatSemigroup hV hprob ρ hρ hHess t f) g)) :=
    (gibbsEulerApproximation_tendsto_heat hV hprob ρ hρ hHess t f).inner tendsto_const_nhds
  have hr : Tendsto (fun n => inner ℝ f (gibbsEulerApproximation hV hprob t n g)) atTop
      (𝓝 (inner ℝ f (gibbsHeatSemigroup hV hprob ρ hρ hHess t g))) :=
    tendsto_const_nhds.inner (gibbsEulerApproximation_tendsto_heat hV hprob ρ hρ hHess t g)
  have heq (n : ℕ) := gibbsEulerApproximation_symmetric hV hprob t n f g
  exact tendsto_nhds_unique hl (by simpa only [← heq] using hr)

theorem gibbsHeatSemigroup_constant
    {V : E → ℝ} (hV : ContDiff ℝ 2 V)
  (hprob : IsProbabilityMeasure (gibbsMeasure volume V))
  (ρ : ℝ) (hρ : 0 < ρ)
  (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)

    (t : NNReal) (c : ℝ) :
    gibbsHeatSemigroup hV hprob ρ hρ hHess t (gibbsConstantLp hprob c) = gibbsConstantLp hprob c := by
  have he := gibbsHeatSemigroup_operatorEigen hV hprob ρ hρ hHess t 0 le_rfl
    (gibbsConstantLp hprob c) (by simpa only [zero_smul] using gibbsConstantLp_graph_mem hV hprob c)
  simpa only [mul_zero, Real.exp_zero, one_smul] using he

theorem gibbsHeatSemigroup_preserves_nonneg
    {V : E → ℝ} (hV : ContDiff ℝ 2 V)
  (hprob : IsProbabilityMeasure (gibbsMeasure volume V))
  (ρ : ℝ) (hρ : 0 < ρ)
  (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)

    (t : NNReal)
    (f : E →₂[gibbsMeasure volume V] ℝ) (hf : ∀ᵐ x ∂gibbsMeasure volume V, 0 ≤ f x) :
    ∀ᵐ x ∂gibbsMeasure volume V, 0 ≤ gibbsHeatSemigroup hV hprob ρ hρ hHess t f x := by
  have hh := gibbsEulerApproximation_tendsto_heat hV hprob ρ hρ hHess t f
  obtain ⟨ns, _, hae⟩ := (tendstoInMeasure_of_tendsto_Lp hh).exists_seq_tendsto_ae'
  have hpos : ∀ᵐ x ∂gibbsMeasure volume V, ∀ n : ℕ,
      0 ≤ gibbsEulerApproximation hV hprob t (ns n) f x :=
    ae_all_iff.mpr (fun n => gibbsEulerApproximation_preserves_nonneg hV hprob t (ns n) f hf)
  filter_upwards [hae, hpos] with x hx hp
  exact ge_of_tendsto hx (Eventually.of_forall hp)

theorem gibbsHeatSemigroup_preserves_order
    {V : E → ℝ} (hV : ContDiff ℝ 2 V)
  (hprob : IsProbabilityMeasure (gibbsMeasure volume V))
  (ρ : ℝ) (hρ : 0 < ρ)
  (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)

    (t : NNReal)
    (f g : E →₂[gibbsMeasure volume V] ℝ)
    (hfg : ∀ᵐ x ∂gibbsMeasure volume V, f x ≤ g x) :
    ∀ᵐ x ∂gibbsMeasure volume V,
      gibbsHeatSemigroup hV hprob ρ hρ hHess t f x ≤ gibbsHeatSemigroup hV hprob ρ hρ hHess t g x := by
  have hh : ∀ᵐ x ∂gibbsMeasure volume V, 0 ≤ (g - f) x := by
    filter_upwards [hfg, Lp.coeFn_sub g f] with x hx hy
    rw [hy, Pi.sub_apply]
    exact sub_nonneg.mpr hx
  have hr := gibbsHeatSemigroup_preserves_nonneg hV hprob ρ hρ hHess t (g - f) hh
  rw [map_sub] at hr
  filter_upwards [hr, Lp.coeFn_sub (gibbsHeatSemigroup hV hprob ρ hρ hHess t g)
    (gibbsHeatSemigroup hV hprob ρ hρ hHess t f)] with x hx hy
  rw [hy, Pi.sub_apply] at hx
  exact sub_nonneg.mp hx

theorem gibbsHeatSemigroup_submarkov
    {V : E → ℝ} (hV : ContDiff ℝ 2 V)
  (hprob : IsProbabilityMeasure (gibbsMeasure volume V))
  (ρ : ℝ) (hρ : 0 < ρ)
  (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)

    (t : NNReal)
    (f : E →₂[gibbsMeasure volume V] ℝ)
    (hf : ∀ᵐ x ∂gibbsMeasure volume V, f x ∈ Set.Icc (0 : ℝ) 1) :
    ∀ᵐ x ∂gibbsMeasure volume V,
      gibbsHeatSemigroup hV hprob ρ hρ hHess t f x ∈ Set.Icc (0 : ℝ) 1 := by
  have := hprob
  have hc : gibbsConstantLp hprob 1 =ᵐ[gibbsMeasure volume V] fun _ : E => (1 : ℝ) :=
    (memLp_const (1 : ℝ)).coeFn_toLp
  have h0 := gibbsHeatSemigroup_preserves_nonneg hV hprob ρ hρ hHess t f (hf.mono fun _ hx => hx.1)
  have h1 := gibbsHeatSemigroup_preserves_order hV hprob ρ hρ hHess t f (gibbsConstantLp hprob 1)
    (by filter_upwards [hf, hc] with x hx hy; rw [hy]; exact hx.2)
  rw [gibbsHeatSemigroup_constant] at h1
  filter_upwards [h0, h1, hc] with x hx hy hz
  exact ⟨hx, hy.trans_eq hz⟩

/-- Actual Gibbs integration is preserved by the canonical form heat
semigroup, independently of identification with the Brownian kernel. -/
theorem integral_gibbsHeatSemigroup
    {V : E → ℝ} (hV : ContDiff ℝ 2 V)
  (hprob : IsProbabilityMeasure (gibbsMeasure volume V))
  (ρ : ℝ) (hρ : 0 < ρ)
  (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)

    (t : NNReal)
    (f : E →₂[gibbsMeasure volume V] ℝ) :
    (∫ x, gibbsHeatSemigroup hV hprob ρ hρ hHess t f x ∂gibbsMeasure volume V) =
      ∫ x, f x ∂gibbsMeasure volume V := by
  have := hprob
  have hc : gibbsConstantLp hprob 1 =ᵐ[gibbsMeasure volume V] fun _ : E => (1 : ℝ) :=
    (memLp_const (1 : ℝ)).coeFn_toLp
  have he := gibbsHeatSemigroup_symmetric hV hprob ρ hρ hHess t f (gibbsConstantLp hprob 1)
  rw [gibbsHeatSemigroup_constant, L2.inner_def, L2.inner_def] at he
  have hl : (fun x => inner ℝ (gibbsHeatSemigroup hV hprob ρ hρ hHess t f x) (gibbsConstantLp hprob 1 x)) =ᵐ[gibbsMeasure volume V]
      fun x => gibbsHeatSemigroup hV hprob ρ hρ hHess t f x := by
    filter_upwards [hc] with x hx
    rw [hx]
    simp
  have hr : (fun x => inner ℝ (f x) (gibbsConstantLp hprob 1 x)) =ᵐ[gibbsMeasure volume V] fun x => f x := by
    filter_upwards [hc] with x hx
    rw [hx]
    simp
  exact (integral_congr_ae hl).symm.trans (he.trans (integral_congr_ae hr))

theorem norm_gibbsHeatSemigroup_le_one
    {V : E → ℝ} (hV : ContDiff ℝ 2 V)
  (hprob : IsProbabilityMeasure (gibbsMeasure volume V))
  (ρ : ℝ) (hρ : 0 < ρ)
  (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)

    (t : NNReal) :
    ‖gibbsHeatSemigroup hV hprob ρ hρ hHess t‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro f
  simpa only [one_mul] using norm_gibbsHeatSemigroup_apply_le hV hprob ρ hρ hHess t f

end CutoffRigidity
