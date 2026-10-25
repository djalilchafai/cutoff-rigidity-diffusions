module

public import CutoffRigidity.Riemann.EigenLinear
public import CutoffRigidity.Riemann.DiffForm

/-! # Chain rule for the generator (workstream PENAL, P2)

`𝓛(θ ∘ f) = θ'(f) 𝓛f + θ''(f) Γ(f,f)` for `θ` smooth and `f` smooth.
-/

@[expose] public section

open Bundle MeasureTheory Filter Set
open scoped Manifold ContDiff ENNReal Topology NNReal

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace CutoffRigidity.Riemann.Diff

open CutCur CutoffRigidity.Riemann

section Chain

variable (F : Type) [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]
  {M : Type} [EMetricSpace M] [ChartedSpace F M] [IsManifold 𝓘(ℝ, F) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, F) ∞ F (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [MeasurableSpace M] [BorelSpace M]

/-- (Copy of `DiffDynkinBounded.sum_inner_smulRight`, to avoid importing that module, which clashes
with `DiffForm2`.) -/
theorem sum_inner_smulRight_pen {T : Type*} [NormedAddCommGroup T] [InnerProductSpace ℝ T]
    [FiniteDimensional ℝ T] (L : T →L[ℝ] ℝ) (v : T) :
    L v = ∑ i, inner ℝ ((L.smulRight v : T →L[ℝ] T) (stdOrthonormalBasis ℝ T i))
      (stdOrthonormalBasis ℝ T i) := by
  set b := stdOrthonormalBasis ℝ T
  conv_lhs => rw [← b.sum_repr' v]
  simp [map_sum, ContinuousLinearMap.smulRight_apply, real_inner_smul_right, real_inner_comm,
    mul_comm]

theorem mlaplacian_comp_real {θ : ℝ → ℝ} (hθ : ContDiff ℝ ∞ θ) {f : M → ℝ} (hf : MSmooth F f)
    (x : M) :
    mlaplacian F (θ ∘ f) x =
      deriv θ (f x) * mlaplacian F f x + deriv (deriv θ) (f x) * carre F f f x := by
  have hθ' : ContDiff ℝ ∞ (deriv θ) := (contDiff_infty_iff_deriv.1 hθ).2
  have hh : MSmooth F (fun y => deriv θ (f y)) := hθ'.contMDiff.comp hf
  have e : mgrad F (θ ∘ f) = (fun y => deriv θ (f y)) • mgrad F f := by
    funext y; exact mgrad_comp_real F hθ hf y
  have hcov := (CovariantDerivative.leviCivitaConnection 𝓘(ℝ, F) M).isCovariantDerivativeOn
    (s := Set.univ)
  have h1 := MDifferentiableAt.smul_section (hh x |>.mdifferentiableAt (by simp)) (mgrad_mdiffAt F hf x)
  have l1 := hcov.leibniz (mgrad_mdiffAt F hf x) (hh x |>.mdifferentiableAt (by simp)) (x := x)
  have hsum : ∀ (g k : M → ℝ), ∑ i, inner ℝ (((mvfderiv 𝓘(ℝ, F) g x).smulRight (mgrad F k x) :
        TangentSpace 𝓘(ℝ, F) x →L[ℝ] TangentSpace 𝓘(ℝ, F) x)
        (stdOrthonormalBasis ℝ (TangentSpace 𝓘(ℝ, F) x) i))
        (stdOrthonormalBasis ℝ (TangentSpace 𝓘(ℝ, F) x) i) = carre F k g x := by
    intro g k
    rw [carre_eq_mvfderiv F k g x]; exact (sum_inner_smulRight_pen _ _).symm
  unfold mlaplacian
  rw [e, l1]
  simp only [add_apply, smul_apply, inner_add_left,
    real_inner_smul_left, Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [hsum]
  have hc : carre F f (fun y => deriv θ (f y)) x = deriv (deriv θ) (f x) * carre F f f x := by
    rw [show carre F f (fun y => deriv θ (f y)) x = carre F (fun y => deriv θ (f y)) f x from
      real_inner_comm _ _]
    exact carre_comp_left F hθ' hf f x
  rw [hc]

theorem mgenerator_comp_real {V : M → ℝ} {θ : ℝ → ℝ} (hθ : ContDiff ℝ ∞ θ) {f : M → ℝ}
    (hf : MSmooth F f) (x : M) :
    mgenerator F V (θ ∘ f) x =
      deriv θ (f x) * mgenerator F V f x + deriv (deriv θ) (f x) * carre F f f x := by
  unfold mgenerator
  rw [mlaplacian_comp_real F hθ hf x, mgrad_comp_real F hθ hf x, real_inner_smul_right]
  ring

end Chain

end CutoffRigidity.Riemann.Diff
