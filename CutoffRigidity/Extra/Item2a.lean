module

public import CutoffRigidity.Statements
public import CutoffRigidity.Riemann.DiffDynkinBounded
public import CutoffRigidity.Riemann.DiffPerron0
public import CutoffRigidity.Riemann.DiffMarkov2

/-! # Item 2(a): the carre du champ is the operator carre du champ; Leibniz and chain rule

The manuscript (Section 1.4) defines `Gamma(f,g) = (L(fg) - f Lg - g Lf)/2` and
`Gamma_2(f,g) = (L Gamma(f,g) - Gamma(f,Lg) - Gamma(g,Lf))/2`, then states that for the
Langevin operator `L = Delta - <grad V, grad .>` they boil down to `Gamma(f) = |grad f|^2`.
The project's `carre f g = <grad f, grad g>`.  Here: `carre` equals the operator definition
(`carre_eq_operator`), Leibniz rule, diffusion property, chain rule, polarization, and the
polarized `Gamma_2`.
-/

@[expose] public section

open Bundle
open scoped Manifold ContDiff

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

namespace CutoffRigidity.Paper

open CutCur

variable (F : Type) [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]
  {M : Type} [EMetricSpace M] [ChartedSpace F M] [IsManifold 𝓘(ℝ, F) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, F) ∞ F (fun x : M => TangentSpace 𝓘(ℝ, F) x)]

/-- The manuscript's polarized `Gamma_2(f,g) = (L Gamma(f,g) - Gamma(f,Lg) - Gamma(g,Lf))/2`. -/
noncomputable def carre2Bil (V f g : M → ℝ) (x : M) : ℝ :=
  (mgenerator F V (carre F f g) x - carre F f (mgenerator F V g) x
    - carre F g (mgenerator F V f) x) / 2

/-- **Operator definition of `Gamma`** (manuscript Section 1.4): for smooth `f, g`,
`Gamma(f,g) = (L(fg) - f Lg - g Lf)/2`, with `Gamma = carre`. -/
theorem carre_eq_operator {V f g : M → ℝ} (hf : ContMDiff 𝓘(ℝ, F) 𝓘(ℝ, ℝ) ∞ f)
    (hg : ContMDiff 𝓘(ℝ, F) 𝓘(ℝ, ℝ) ∞ g) (x : M) :
    carre F f g x =
      (mgenerator F V (fun y => f y * g y) x - f x * mgenerator F V g x
        - g x * mgenerator F V f x) / 2 := by
  rw [CutoffRigidity.Riemann.Diff.mgenerator_mul F hf hg x]; ring

/-- Diffusion property: `L(fg) = f Lg + g Lf + 2 Gamma(f,g)`. -/
theorem generator_mul {V f g : M → ℝ} (hf : ContMDiff 𝓘(ℝ, F) 𝓘(ℝ, ℝ) ∞ f)
    (hg : ContMDiff 𝓘(ℝ, F) 𝓘(ℝ, ℝ) ∞ g) (x : M) :
    mgenerator F V (fun y => f y * g y) x =
      f x * mgenerator F V g x + g x * mgenerator F V f x + 2 * carre F f g x :=
  CutoffRigidity.Riemann.Diff.mgenerator_mul F hf hg x

/-- Leibniz rule for `Gamma`: `Gamma(fg, h) = f Gamma(g,h) + g Gamma(f,h)`. -/
theorem carre_mul_left' {f g h : M → ℝ} (hf : ContMDiff 𝓘(ℝ, F) 𝓘(ℝ, ℝ) ∞ f)
    (hg : ContMDiff 𝓘(ℝ, F) 𝓘(ℝ, ℝ) ∞ g) (x : M) :
    carre F (fun y => f y * g y) h x = f x * carre F g h x + g x * carre F f h x :=
  CutCur.carre_mul_left F (f := f) (g := g) (h := h) hf hg x

/-- `Gamma` is symmetric. -/
theorem carre_symm (f g : M → ℝ) (x : M) : carre F f g x = carre F g f x := real_inner_comm _ _

/-- Leibniz rule for `Gamma` in the second slot. -/
theorem carre_mul_right {f g h : M → ℝ} (hg : ContMDiff 𝓘(ℝ, F) 𝓘(ℝ, ℝ) ∞ g)
    (hh : ContMDiff 𝓘(ℝ, F) 𝓘(ℝ, ℝ) ∞ h) (x : M) :
    carre F f (fun y => g y * h y) x = g x * carre F f h x + h x * carre F f g x := by
  rw [carre_symm F f, carre_symm F f h, carre_symm F f g]
  exact CutCur.carre_mul_left F (f := g) (g := h) (h := f) hg hh x

/-- Chain rule: `L(theta ∘ f) = theta'(f) Lf + theta''(f) Gamma(f)`. -/
theorem generator_comp {V : M → ℝ} {θ : ℝ → ℝ} (hθ : ContDiff ℝ ∞ θ) {f : M → ℝ}
    (hf : ContMDiff 𝓘(ℝ, F) 𝓘(ℝ, ℝ) ∞ f) (x : M) :
    mgenerator F V (θ ∘ f) x =
      deriv θ (f x) * mgenerator F V f x + deriv (deriv θ) (f x) * carre F f f x := by
  letI : MeasurableSpace M := borel M
  haveI : BorelSpace M := ⟨rfl⟩
  exact CutoffRigidity.Riemann.Diff.mgenerator_comp_real F hθ hf x

/-- Chain rule for `Gamma`: `Gamma(theta ∘ f, g) = theta'(f) Gamma(f,g)`. -/
theorem carre_comp_left' {θ : ℝ → ℝ} (hθ : ContDiff ℝ ∞ θ) {f : M → ℝ}
    (hf : ContMDiff 𝓘(ℝ, F) 𝓘(ℝ, ℝ) ∞ f) (g : M → ℝ) (x : M) :
    carre F (θ ∘ f) g x = deriv θ (f x) * carre F f g x := by
  letI : MeasurableSpace M := borel M
  haveI : BorelSpace M := ⟨rfl⟩
  unfold carre
  rw [CutoffRigidity.Riemann.Diff.mgrad_comp_real F hθ hf x, real_inner_smul_left]

/-- Polarization: `Gamma(f,g) = (Gamma(f+g) - Gamma(f-g))/4`. -/
theorem carre_polarization (f g : M → ℝ) (hf : ContMDiff 𝓘(ℝ, F) 𝓘(ℝ, ℝ) ∞ f)
    (hg : ContMDiff 𝓘(ℝ, F) 𝓘(ℝ, ℝ) ∞ g) (x : M) :
    carre F f g x =
      (carre F (fun y => f y + g y) (fun y => f y + g y) x
        - carre F (fun y => f y - g y) (fun y => f y - g y) x) / 4 := by
  unfold carre
  have hs : mgrad F (fun y => f y - g y) x = mgrad F f x - mgrad F g x := by
    have e : (fun y => f y - g y) = fun y => f y + (-1 : ℝ) * g y := by
      funext y; ring
    have h1 : ContMDiff 𝓘(ℝ, F) 𝓘(ℝ, ℝ) ∞ fun y => (-1 : ℝ) * g y := contMDiff_const.mul hg
    have h2 := CutCur.mgrad_add' F hf h1 x
    rw [e, h2, CutCur.mgrad_const_mul F (-1 : ℝ) hg x]
    simp [sub_eq_add_neg]
  rw [CutCur.mgrad_add' F hf hg x, hs]
  simp only [inner_add_left, inner_add_right, inner_sub_left, inner_sub_right]
  rw [real_inner_comm (mgrad F g x) (mgrad F f x)]
  ring

/-- The diagonal of the polarized `Gamma_2` is the project's `carre2`. -/
theorem carre2Bil_self (V f : M → ℝ) (x : M) : carre2Bil F V f f x = carre2 F V f x := by
  unfold carre2Bil carre2
  rw [carre_symm F (f) (mgenerator F V f) x]
  ring

end CutoffRigidity.Paper
