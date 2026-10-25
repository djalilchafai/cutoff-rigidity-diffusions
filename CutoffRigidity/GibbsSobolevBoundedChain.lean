module
public import CutoffRigidity.GibbsSobolevContraction

/-! # Smooth bounded-derivative calculus on the genuine closed Gibbs graph

The general derivative bound follows by rescaling the already proved
normal-contraction chain rule. The weak gradient remains explicitly the
chain derivative times the original actual closed gradient.
-/
public section
namespace CutoffRigidity
open MeasureTheory Filter
variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

set_option maxHeartbeats 500000 in
theorem gibbsSobolev_smooth_bounded_derivative_chain
    {V : E → ℝ} (hV : ContDiff ℝ 2 V)
    (hp : IsProbabilityMeasure (gibbsMeasure volume V))
    {ψ : ℝ → ℝ} (hψ : ContDiff ℝ 2 ψ) (hψ0 : ψ 0=0)
    (K : ℝ) (hK : 0 < K) (hbound : ∀ r, |deriv ψ r| ≤ K)
    (u : gibbsSobolevGraph hV hp) :
    ∃ v : gibbsSobolevGraph hV hp,
      (gibbsSobolevInclusion hV hp v =ᵐ[gibbsMeasure volume V]
        fun x => ψ (gibbsSobolevInclusion hV hp u x)) ∧
      (gibbsSobolevDerivative hV hp v =ᵐ[gibbsMeasure volume V]
        fun x => deriv ψ (gibbsSobolevInclusion hV hp u x) • gibbsSobolevDerivative hV hp u x) := by
  let φ := fun r => ψ r / K
  have hφ : ContDiff ℝ 2 φ := hψ.div_const K
  have hφ0 : φ 0=0 := by simp [φ,hψ0]
  have hd (r : ℝ) : deriv φ r = deriv ψ r / K :=
    ((hψ.differentiable (by norm_num) r).hasDerivAt.mul_const K⁻¹).deriv
  have hb (r : ℝ) : |deriv φ r| ≤ 1 := by
    rw [hd,abs_div,abs_of_pos hK]
    exact (div_le_one hK).mpr (hbound r)
  obtain ⟨v,hv,hD,_⟩ := gibbsSobolev_smooth_normal_contraction hV hp hφ hφ0 hb u
  refine ⟨K • v,?_,?_⟩
  · have hrep := Lp.coeFn_smul K (gibbsSobolevInclusion hV hp v)
    filter_upwards [hrep,hv] with x hx hy
    rw [map_smul]
    rw [hx,Pi.smul_apply,smul_eq_mul,hy]
    dsimp only [φ]
    field_simp
  · have hrep := Lp.coeFn_smul K (gibbsSobolevDerivative hV hp v)
    filter_upwards [hrep,hD] with x hx hy
    rw [map_smul]
    rw [hx,Pi.smul_apply]
    have he : K * deriv φ (gibbsSobolevInclusion hV hp u x) =
        deriv ψ (gibbsSobolevInclusion hV hp u x) := by
      rw [hd]
      field_simp
    exact (congrArg (fun z : E => K • z) hy).trans ((smul_smul _ _ _).trans (congrArg (fun r : ℝ => r • gibbsSobolevDerivative hV hp u x) he))

end CutoffRigidity
