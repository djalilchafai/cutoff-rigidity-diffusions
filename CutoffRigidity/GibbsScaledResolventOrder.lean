module
public import CutoffRigidity.GibbsScaledResolvent

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
theorem gibbsScaledL2Resolvent_preserves_nonneg
    {V : E → ℝ} (hV : ContDiff ℝ 2 V)
    (hprob : IsProbabilityMeasure (gibbsMeasure volume V)) (h : ℝ) (hh : 0 < h)
    (f : E →₂[gibbsMeasure volume V] ℝ) (hf : ∀ᵐ x ∂gibbsMeasure volume V, 0 ≤ f x) :
    ∀ᵐ x ∂gibbsMeasure volume V, 0 ≤ gibbsScaledL2Resolvent hV hprob h hh f x := by
  let μ := gibbsMeasure volume V
  let u := gibbsScaledWeakResolvent hV hprob h hh f
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
  have heq := gibbsScaledWeakResolvent_equation hV hprob h hh f v
  change inner ℝ U W + h * gibbsDirichletEnergy hV hprob u v = inner ℝ f W at heq
  have henergyScaled : h * gibbsDirichletEnergy hV hprob u v ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hh.le henergy
  have hWzero : W = 0 := by
    apply (inner_self_eq_zero (𝕜 := ℝ)).mp
    exact le_antisymm (by linarith) real_inner_self_nonneg
  change ∀ᵐ x ∂μ, 0 ≤ U x
  filter_upwards [hv', Lp.coeFn_zero ℝ 2 μ] with x hx hz
  rw [hWzero, hz] at hx
  have hmax : -U x ≤ 0 := (le_max_left (-U x) 0).trans hx.symm.le
  linarith

/-- The actual variational resolvent preserves almost-everywhere order. -/
theorem gibbsScaledL2Resolvent_preserves_order
    {V : E → ℝ} (hV : ContDiff ℝ 2 V)
    (hprob : IsProbabilityMeasure (gibbsMeasure volume V)) (h : ℝ) (hh : 0 < h)
    (f g : E →₂[gibbsMeasure volume V] ℝ)
    (hfg : ∀ᵐ x ∂gibbsMeasure volume V, f x ≤ g x) :
    ∀ᵐ x ∂gibbsMeasure volume V, gibbsScaledL2Resolvent hV hprob h hh f x ≤ gibbsScaledL2Resolvent hV hprob h hh g x := by
  have hdata : ∀ᵐ x ∂gibbsMeasure volume V, 0 ≤ (g - f) x := by
    filter_upwards [hfg, Lp.coeFn_sub g f] with x hx hy
    rw [hy, Pi.sub_apply]
    exact sub_nonneg.mpr hx
  have hr := gibbsScaledL2Resolvent_preserves_nonneg hV hprob h hh (g - f) hdata
  rw [map_sub] at hr
  filter_upwards [hr, Lp.coeFn_sub (gibbsScaledL2Resolvent hV hprob h hh g) (gibbsScaledL2Resolvent hV hprob h hh f)] with x hx hy
  rw [hy, Pi.sub_apply] at hx
  exact sub_nonneg.mp hx

/-- The genuine resolvent is sub-Markov: it sends [0,1]-valued L² data
into actual [0,1]-valued L² functions. -/
theorem gibbsScaledL2Resolvent_submarkov
    {V : E → ℝ} (hV : ContDiff ℝ 2 V)
    (hprob : IsProbabilityMeasure (gibbsMeasure volume V)) (h : ℝ) (hh : 0 < h)
    (f : E →₂[gibbsMeasure volume V] ℝ)
    (hf : ∀ᵐ x ∂gibbsMeasure volume V, f x ∈ Set.Icc (0 : ℝ) 1) :
    ∀ᵐ x ∂gibbsMeasure volume V, gibbsScaledL2Resolvent hV hprob h hh f x ∈ Set.Icc (0 : ℝ) 1 := by
  have := hprob
  have hconst : gibbsConstantLp hprob 1 =ᵐ[gibbsMeasure volume V] fun _ : E => (1 : ℝ) :=
    (memLp_const (1 : ℝ)).coeFn_toLp
  have h0 := gibbsScaledL2Resolvent_preserves_nonneg hV hprob h hh f (hf.mono fun _ hx => hx.1)
  have h1 := gibbsScaledL2Resolvent_preserves_order hV hprob h hh f (gibbsConstantLp hprob 1)
    (by filter_upwards [hf, hconst] with x hx hy; rw [hy]; exact hx.2)
  rw [gibbsScaledL2Resolvent_constant] at h1
  filter_upwards [h0, h1, hconst] with x hx hy hz
  exact ⟨hx, hy.trans_eq hz⟩

/-- Gibbs integration is preserved by the actual form resolvent. This
concerns the variational resolvent and does not identify the stochastic kernel. -/
theorem integral_gibbsScaledL2Resolvent
    {V : E → ℝ} (hV : ContDiff ℝ 2 V)
    (hprob : IsProbabilityMeasure (gibbsMeasure volume V)) (h : ℝ) (hh : 0 < h)
    (f : E →₂[gibbsMeasure volume V] ℝ) :
    (∫ x, gibbsScaledL2Resolvent hV hprob h hh f x ∂gibbsMeasure volume V) =
      ∫ x, f x ∂gibbsMeasure volume V := by
  have := hprob
  have hconst : gibbsConstantLp hprob 1 =ᵐ[gibbsMeasure volume V] fun _ : E => (1 : ℝ) :=
    (memLp_const (1 : ℝ)).coeFn_toLp
  have he := gibbsScaledL2Resolvent_symmetric hV hprob h hh f (gibbsConstantLp hprob 1)
  rw [gibbsScaledL2Resolvent_constant, L2.inner_def, L2.inner_def] at he
  have hleft : (fun x => inner ℝ (gibbsScaledL2Resolvent hV hprob h hh f x) (gibbsConstantLp hprob 1 x)) =ᵐ[gibbsMeasure volume V]
      fun x => gibbsScaledL2Resolvent hV hprob h hh f x := by
    filter_upwards [hconst] with x hx
    rw [hx]
    simp
  have hright : (fun x => inner ℝ (f x) (gibbsConstantLp hprob 1 x)) =ᵐ[gibbsMeasure volume V]
      fun x => f x := by
    filter_upwards [hconst] with x hx
    rw [hx]
    simp
  exact (integral_congr_ae hleft).symm.trans (he.trans (integral_congr_ae hright))

/-- The scaled resolvent is a contraction on the actual Gibbs L² space. -/
theorem norm_gibbsScaledL2Resolvent_le_one
    {V : E → ℝ} (hV : ContDiff ℝ 2 V)
    (hprob : IsProbabilityMeasure (gibbsMeasure volume V)) (h : ℝ) (hh : 0 < h) :
    ‖gibbsScaledL2Resolvent hV hprob h hh‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro f
  simpa only [one_mul] using norm_gibbsScaledL2Resolvent_apply_le hV hprob h hh f

/-- Genuine operator eigenvectors have the expected scaled-resolvent
multiplier, proved from the full operator-domain inverse equation. -/
theorem gibbsScaledL2Resolvent_operatorEigen
    {V : E → ℝ} (hV : ContDiff ℝ 2 V)
    (hprob : IsProbabilityMeasure (gibbsMeasure volume V)) (h : ℝ) (hh : 0 < h)
    (rate : ℝ) (hrate : 0 ≤ rate) (u : E →₂[gibbsMeasure volume V] ℝ)
    (hu : (u, rate • u) ∈ (gibbsPositiveGenerator hV hprob).graph) :
    gibbsScaledL2Resolvent hV hprob h hh u = (1 + h * rate)⁻¹ • u := by
  have hc : (1 + h * rate) ≠ 0 := ne_of_gt (by positivity)
  have he := gibbsScaledL2Resolvent_of_graph hV hprob h hh u (rate • u) hu
  have harg : u + h • (rate • u) = (1 + h * rate) • u := by
    rw [add_smul, one_smul, mul_smul]
  rw [harg, map_smul] at he
  calc
    gibbsScaledL2Resolvent hV hprob h hh u =
        (1 + h * rate)⁻¹ • ((1 + h * rate) • gibbsScaledL2Resolvent hV hprob h hh u) := by
      rw [smul_smul, inv_mul_cancel₀ hc, one_smul]
    _ = _ := congrArg ((1 + h * rate)⁻¹ • ·) he

end CutoffRigidity
