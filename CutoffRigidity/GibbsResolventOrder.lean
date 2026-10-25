module
public import CutoffRigidity.GibbsSobolevPositivePart
public import CutoffRigidity.GibbsResolventBounds

/-! # Order positivity of the actual variational Gibbs resolvent

The negative part is a genuine closed-gradient-domain test. The variational
equation therefore proves positivity preservation, not just a nonnegative
quadratic form.
-/
public section
namespace CutoffRigidity
open MeasureTheory Filter Topology
variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

set_option maxHeartbeats 600000 in
theorem gibbsL2Resolvent_preserves_nonneg
    {V : E → ℝ} (hV : ContDiff ℝ 2 V)
    (hprob : IsProbabilityMeasure (gibbsMeasure volume V))
    (f : E →₂[gibbsMeasure volume V] ℝ) (hf : ∀ᵐ x ∂gibbsMeasure volume V, 0 ≤ f x) :
    ∀ᵐ x ∂gibbsMeasure volume V, 0 ≤ gibbsL2Resolvent hV hprob f x := by
  let μ := gibbsMeasure volume V
  let u := gibbsWeakResolvent hV hprob f
  let U := gibbsSobolevInclusion hV hprob u
  let D := gibbsSobolevDerivative hV hprob u
  obtain ⟨v, hv, hd, _⟩ := gibbsSobolev_positive_part hV hprob (-u)
  let W := gibbsSobolevInclusion hV hprob v
  have hUne : gibbsSobolevInclusion hV hprob (-u) = -U := map_neg _ _
  have hDne : gibbsSobolevDerivative hV hprob (-u) = -D := map_neg _ _
  have hv' : W =ᵐ[μ] fun x => max (-U x) 0 := by
    filter_upwards [hv, Lp.coeFn_neg U] with x hx hn
    rw [hUne, hn] at hx
    exact hx
  have hd' : gibbsSobolevDerivative hV hprob v =ᵐ[μ]
      fun x => positivePartSlope (-U x) • (-D x) := by
    filter_upwards [hd, Lp.coeFn_neg U, Lp.coeFn_neg D] with x hx hn hm
    rw [hUne, hDne, hn, hm] at hx
    exact hx
  have hW0 : ∀ᵐ x ∂μ, 0 ≤ W x := hv'.mono (fun x hx => hx ▸ le_max_right _ _)
  have hpair : inner ℝ U W = -inner ℝ W W := by
    rw [L2.inner_def, L2.inner_def, ← integral_neg]
    apply integral_congr_ae
    filter_upwards [hv'] with x hx
    change W x * U x = -(W x * W x)
    rw [hx]
    by_cases hh : 0 ≤ U x
    · rw [max_eq_right (by linarith : -U x ≤ 0)]
      ring
    · rw [max_eq_left (by linarith : 0 ≤ -U x)]
      ring
  have henergy : gibbsDirichletEnergy hV hprob u v ≤ 0 := by
    rw [gibbsDirichletEnergy_eq_integral]
    apply integral_nonpos_of_ae
    filter_upwards [hd'] with x hx
    change inner ℝ (D x) (gibbsSobolevDerivative hV hprob v x) ≤ 0
    rw [hx, real_inner_smul_right, inner_neg_right, real_inner_self_eq_norm_sq]
    exact mul_nonpos_of_nonneg_of_nonpos (positivePartSlope_nonneg _) (neg_nonpos.mpr (sq_nonneg _))
  have hrhs : 0 ≤ inner ℝ f W := by
    rw [L2.inner_def]
    apply integral_nonneg_of_ae
    filter_upwards [hf, hW0] with x hx hy
    change 0 ≤ W x * f x
    exact mul_nonneg hy hx
  have heq := gibbsWeakResolvent_equation hV hprob f v
  change inner ℝ U W + gibbsDirichletEnergy hV hprob u v = inner ℝ f W at heq
  have hWzero : W = 0 := by
    apply (inner_self_eq_zero (𝕜 := ℝ)).mp
    exact le_antisymm (by linarith) real_inner_self_nonneg
  change ∀ᵐ x ∂μ, 0 ≤ U x
  filter_upwards [hv', Lp.coeFn_zero ℝ 2 μ] with x hx hz
  rw [hWzero, hz] at hx
  have hmax : -U x ≤ 0 := (le_max_left (-U x) 0).trans hx.symm.le
  linarith

/-- The actual variational resolvent preserves almost-everywhere order. -/
theorem gibbsL2Resolvent_preserves_order
    {V : E → ℝ} (hV : ContDiff ℝ 2 V)
    (hprob : IsProbabilityMeasure (gibbsMeasure volume V))
    (f g : E →₂[gibbsMeasure volume V] ℝ)
    (hfg : ∀ᵐ x ∂gibbsMeasure volume V, f x ≤ g x) :
    ∀ᵐ x ∂gibbsMeasure volume V, gibbsL2Resolvent hV hprob f x ≤ gibbsL2Resolvent hV hprob g x := by
  have hh : ∀ᵐ x ∂gibbsMeasure volume V, 0 ≤ (g - f) x := by
    filter_upwards [hfg, Lp.coeFn_sub g f] with x hx hy
    rw [hy, Pi.sub_apply]
    exact sub_nonneg.mpr hx
  have hr := gibbsL2Resolvent_preserves_nonneg hV hprob (g - f) hh
  rw [map_sub] at hr
  filter_upwards [hr, Lp.coeFn_sub (gibbsL2Resolvent hV hprob g) (gibbsL2Resolvent hV hprob f)] with x hx hy
  rw [hy, Pi.sub_apply] at hx
  exact sub_nonneg.mp hx

/-- The genuine resolvent is sub-Markov: it sends [0,1]-valued L² data
into actual [0,1]-valued L² functions. -/
theorem gibbsL2Resolvent_submarkov
    {V : E → ℝ} (hV : ContDiff ℝ 2 V)
    (hprob : IsProbabilityMeasure (gibbsMeasure volume V))
    (f : E →₂[gibbsMeasure volume V] ℝ)
    (hf : ∀ᵐ x ∂gibbsMeasure volume V, f x ∈ Set.Icc (0 : ℝ) 1) :
    ∀ᵐ x ∂gibbsMeasure volume V, gibbsL2Resolvent hV hprob f x ∈ Set.Icc (0 : ℝ) 1 := by
  have := hprob
  have hconst : gibbsConstantLp hprob 1 =ᵐ[gibbsMeasure volume V] fun _ : E => (1 : ℝ) :=
    (memLp_const (1 : ℝ)).coeFn_toLp
  have h0 := gibbsL2Resolvent_preserves_nonneg hV hprob f (hf.mono fun _ hx => hx.1)
  have h1 := gibbsL2Resolvent_preserves_order hV hprob f (gibbsConstantLp hprob 1)
    (by filter_upwards [hf, hconst] with x hx hy; rw [hy]; exact hx.2)
  rw [gibbsL2Resolvent_constant] at h1
  filter_upwards [h0, h1, hconst] with x hx hy hz
  exact ⟨hx, hy.trans_eq hz⟩

end CutoffRigidity
