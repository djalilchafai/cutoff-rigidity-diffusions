module
public import Mathlib.Analysis.Calculus.FDeriv.Partial
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.Analysis.Calculus.Deriv.Comp

/-! # The path chain rule for continuous partial derivatives

This is the ordinary multivariable chain rule used in the BGL interpolation:
time and space partial derivatives are genuine derivatives and continuous.
-/
public section
namespace CutoffRigidity
open Filter Set
open scoped Topology

theorem hasDerivAt_along_path_of_continuous_partials
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f D : ℝ → E → ℝ) (L : ℝ → E → E →L[ℝ] ℝ)
    {a b t : ℝ} (ht : t ∈ Ioo a b)
    (hTime : ∀ s ∈ Ioo a b, ∀ x, HasDerivAt (fun r => f r x) (D s x) s)
    (hSpace : ∀ s x, HasFDerivAt (f s) (L s x) x)
    (hDc : Continuous (Function.uncurry D)) (hLc : Continuous (Function.uncurry L))
    (γ : ℝ → E) (v : E) (hγ : HasDerivAt γ v t) :
    HasDerivAt (fun s => f s (γ s)) (D t (γ t) + L t (γ t) v) t := by
  let A := fun s x => (1 : ℝ →L[ℝ] ℝ).smulRight (D s x)
  have hA : Continuous (Function.uncurry A) :=
    (((ContinuousLinearMap.smulRightL ℝ ℝ ℝ) 1).continuous.comp hDc)
  have hF : HasFDerivAt (Function.uncurry f)
      ((A t (γ t)).coprod (L t (γ t))) (t, γ t) := by
    convert! (hasStrictFDerivAt_uncurry_coprod (f := f) (f₁ := A) (f₂ := L)
      (u := (t, γ t)) ?_ ?_ ?_ ?_).hasFDerivAt using 1
    · have he : ∀ᶠ p : ℝ × E in 𝓝 (t, γ t), p.1 ∈ Ioo a b :=
        continuous_fst.continuousAt.eventually (Ioo_mem_nhds ht.1 ht.2)
      filter_upwards [he] with p hp
      exact (hTime p.1 hp p.2).hasFDerivAt
    · exact Eventually.of_forall fun p => hSpace p.1 p.2
    · exact hA.continuousAt
    · exact hLc.continuousAt
  have hh := hF.comp_hasDerivAt t ((hasDerivAt_id t).prodMk hγ)
  convert! hh using 1
  simp only [ContinuousLinearMap.coprod_apply, A, ContinuousLinearMap.smulRight_apply,
    one_apply_eq_self, one_smul]

end CutoffRigidity
