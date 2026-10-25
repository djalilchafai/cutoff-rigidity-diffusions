module

public import CutoffRigidity.Riemann.WeightedBochnerDefs
public import CutoffRigidity.Riemann.WeightedRegularChart
public import CutoffRigidity.Riemann.WeightedPointwise

/-! # G2: the quadratic terms `½ Δ Γ(f)` and the formula for `Γ₂`

* `mlaplacian_carre_self`: `½ Δ|∇f|² = Σᵢ (⟨∇_{eᵢ}∇_{Zᵢ}u - ∇_{∇_{eᵢ}Zᵢ}u, u⟩ + |∇_{eᵢ}u|²)`.
* `carre2_eq`: `Γ₂(f) = ½ Δ Γ(f) - d(Δf)(∇f) + Hess V(∇f,∇f)`.
-/

@[expose] public section
open Bundle Filter Set VectorField
open scoped Manifold ContDiff Topology
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace CutCur.WBoch

section Quad

variable (F : Type) [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  {M : Type} [EMetricSpace M] [ChartedSpace F M] [IsManifold 𝓘(ℝ, F) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, F) ∞ F (fun x : M => TangentSpace 𝓘(ℝ, F) x)]

/-- Metric compatibility for the Levi-Civita connection, in directional form. -/
theorem mvfderiv_inner_lc {σ τ : (y : M) → TangentSpace 𝓘(ℝ, F) y} {x : M}
    (hσ : MDifferentiableAt 𝓘(ℝ, F) 𝓘(ℝ, F).tangent
      (fun y => (⟨y, σ y⟩ : TangentBundle 𝓘(ℝ, F) M)) x)
    (hτ : MDifferentiableAt 𝓘(ℝ, F) 𝓘(ℝ, F).tangent
      (fun y => (⟨y, τ y⟩ : TangentBundle 𝓘(ℝ, F) M)) x)
    (v : TangentSpace 𝓘(ℝ, F) x) :
    mvfderiv 𝓘(ℝ, F) (fun y => inner ℝ (σ y) (τ y)) x v =
      inner ℝ (CovariantDerivative.leviCivitaConnection 𝓘(ℝ, F) M σ x v) (τ x)
        + inner ℝ (σ x) (CovariantDerivative.leviCivitaConnection 𝓘(ℝ, F) M τ x v) := by
  have hh := (CovariantDerivative.isMetricCompatible_leviCivitaConnection 𝓘(ℝ, F)
    (M := M)).mvfderiv_inner_eq (FiberBundle.extend F v) hσ hτ
  have hv : FiberBundle.extend F v x = v := FiberBundle.extend_apply_self F v
  simp only [hv] at hh
  exact hh

theorem smAt_mgrad {f : M → ℝ} (hf : MSmooth F f) (x : M) : SmAt F (mgrad F f) x :=
  (CutCur.WReg.contMDiff_mgrad hf) x

theorem mdiffAt_of_smAt {X : (y : M) → TangentSpace 𝓘(ℝ, F) y} {x : M} (h : SmAt F X x) :
    MDifferentiableAt 𝓘(ℝ, F) 𝓘(ℝ, F).tangent
      (fun y => (⟨y, X y⟩ : TangentBundle 𝓘(ℝ, F) M)) x :=
  h.mdifferentiableAt (by simp)

/-- `⟨∇ φ, Y⟩ = dφ(Y)`. -/
theorem inner_mgrad_eq (φ : M → ℝ) (y : M) (w : TangentSpace 𝓘(ℝ, F) y) :
    inner ℝ (mgrad F φ y) w = mvfderiv 𝓘(ℝ, F) φ y w :=
  CutoffRigidity.inner_manifoldGradient (I := 𝓘(ℝ, F)) φ y w

theorem hessian_eq_fields_aux {φ : M → ℝ} (hφ : MSmooth F φ)
    {X Y : (y : M) → TangentSpace 𝓘(ℝ, F) y} {x : M} (hX : SmAt F X x) (hY : SmAt F Y x) :
    inner ℝ (CovariantDerivative.leviCivitaConnection 𝓘(ℝ, F) M (mgrad F φ) x (X x)) (Y x) =
      mvfderiv 𝓘(ℝ, F) (fun y => mvfderiv 𝓘(ℝ, F) φ y (Y y)) x (X x)
        - mvfderiv 𝓘(ℝ, F) φ x
          (CovariantDerivative.leviCivitaConnection 𝓘(ℝ, F) M Y x (X x)) := by
  have h := mvfderiv_inner_lc F (mdiffAt_of_smAt F (smAt_mgrad F hφ x)) (mdiffAt_of_smAt F hY)
    (X x)
  have e : (fun y => inner ℝ (mgrad F φ y) (Y y)) = fun y => mvfderiv 𝓘(ℝ, F) φ y (Y y) := by
    funext y; exact inner_mgrad_eq F φ y (Y y)
  rw [e] at h
  rw [h, inner_mgrad_eq]
  ring

/-- `dΓ(f)(w) = 2 ⟨∇_w u, u⟩`. -/
theorem mvfderiv_carre_apply {f : M → ℝ} (hf : MSmooth F f) (y : M)
    (w : TangentSpace 𝓘(ℝ, F) y) :
    mvfderiv 𝓘(ℝ, F) (carre F f f) y w =
      2 * inner ℝ (CovariantDerivative.leviCivitaConnection 𝓘(ℝ, F) M (mgrad F f) y w)
        (mgrad F f y) :=
  mvfderiv_carre_self F hf y w

theorem half_hessian_carre_term (hN : NabSmooth F M) {f : M → ℝ} (hf : MSmooth F f) (x : M)
    {Z : (y : M) → TangentSpace 𝓘(ℝ, F) y} (hZ : SmAt F Z x) :
    inner ℝ (CovariantDerivative.leviCivitaConnection 𝓘(ℝ, F) M (mgrad F (carre F f f)) x (Z x))
        (Z x) / 2 =
      inner ℝ (CovariantDerivative.leviCivitaConnection 𝓘(ℝ, F) M (nab F Z (mgrad F f)) x (Z x)
          - CovariantDerivative.leviCivitaConnection 𝓘(ℝ, F) M (mgrad F f) x
            (CovariantDerivative.leviCivitaConnection 𝓘(ℝ, F) M Z x (Z x)))
          (mgrad F f x)
        + ‖CovariantDerivative.leviCivitaConnection 𝓘(ℝ, F) M (mgrad F f) x (Z x)‖ ^ 2 := by
  have hφ : MSmooth F (carre F f f) := CutCur.WReg.msmooth_carre hf hf
  have hu := smAt_mgrad F hf x
  have hNZ : MDifferentiableAt 𝓘(ℝ, F) 𝓘(ℝ, F).tangent
      (fun y => (⟨y, nab F Z (mgrad F f) y⟩ : TangentBundle 𝓘(ℝ, F) M)) x :=
    mdiffAt_of_smAt F (hN Z (mgrad F f) x hZ hu)
  have h1 := hessian_eq_fields_aux F hφ hZ hZ
  have hin : MDifferentiableAt 𝓘(ℝ, F) 𝓘(ℝ, ℝ)
      (fun y => inner ℝ (nab F Z (mgrad F f) y) (mgrad F f y)) x :=
    MDifferentiableAt.inner_bundle (E := TangentSpace 𝓘(ℝ, F)) hNZ (mdiffAt_of_smAt F hu)
  have e : (fun y => mvfderiv 𝓘(ℝ, F) (carre F f f) y (Z y)) =
      fun y => (fun _ : M => (2 : ℝ)) y *
        (fun y => inner ℝ (nab F Z (mgrad F f) y) (mgrad F f y)) y := by
    funext y
    exact mvfderiv_carre_apply F hf y (Z y)
  rw [e] at h1
  have h2 := mvfderiv_fun_mul (f := fun _ : M => (2 : ℝ))
    (g := fun y => inner ℝ (nab F Z (mgrad F f) y) (mgrad F f y)) (x := x)
    mdifferentiableAt_const hin
  rw [h2, mvfderiv_const] at h1
  rw [h1]
  simp only [add_apply, smul_apply, zero_apply, smul_zero, add_zero, smul_eq_mul]
  rw [mvfderiv_inner_lc F hNZ (mdiffAt_of_smAt F hu), mvfderiv_carre_apply F hf,
    inner_sub_left]
  have : nab F Z (mgrad F f) x = CovariantDerivative.leviCivitaConnection 𝓘(ℝ, F) M
    (mgrad F f) x (Z x) := rfl
  rw [this, real_inner_comm (CovariantDerivative.leviCivitaConnection 𝓘(ℝ, F) M
    (mgrad F f) x (Z x))]
  have hn := real_inner_self_eq_norm_sq (CovariantDerivative.leviCivitaConnection 𝓘(ℝ, F) M
    (mgrad F f) x (Z x))
  linarith

theorem mlaplacian_carre_self (hN : NabSmooth F M) {f : M → ℝ} (hf : MSmooth F f) (x : M)
    (Z : Fin (Module.finrank ℝ (TangentSpace 𝓘(ℝ, F) x)) → (y : M) → TangentSpace 𝓘(ℝ, F) y)
    (hZ : ∀ i, SmAt F (Z i) x)
    (hZx : ∀ i, Z i x = stdOrthonormalBasis ℝ (TangentSpace 𝓘(ℝ, F) x) i) :
    mlaplacian F (carre F f f) x / 2 =
      ∑ i, (inner ℝ (CovariantDerivative.leviCivitaConnection 𝓘(ℝ, F) M (nab F (Z i) (mgrad F f)) x
            (stdOrthonormalBasis ℝ (TangentSpace 𝓘(ℝ, F) x) i)
          - CovariantDerivative.leviCivitaConnection 𝓘(ℝ, F) M (mgrad F f) x
            (CovariantDerivative.leviCivitaConnection 𝓘(ℝ, F) M (Z i) x
              (stdOrthonormalBasis ℝ (TangentSpace 𝓘(ℝ, F) x) i)))
          (mgrad F f x)
        + ‖CovariantDerivative.leviCivitaConnection 𝓘(ℝ, F) M (mgrad F f) x
            (stdOrthonormalBasis ℝ (TangentSpace 𝓘(ℝ, F) x) i)‖ ^ 2) := by
  unfold mlaplacian
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun i _ => ?_
  have := half_hessian_carre_term F hN hf x (hZ i)
  rw [hZx i] at this
  exact this

theorem carre2_eq (hN : NabSmooth F M) {V f : M → ℝ} (hV : MSmooth F V) (hf : MSmooth F f)
    (hsymm : ∀ φ : M → ℝ, MSmooth F φ → ∀ (y : M) (v w : TangentSpace 𝓘(ℝ, F) y),
      inner ℝ (CovariantDerivative.leviCivitaConnection 𝓘(ℝ, F) M (mgrad F φ) y v) w =
        inner ℝ (CovariantDerivative.leviCivitaConnection 𝓘(ℝ, F) M (mgrad F φ) y w) v)
    (hΔ : MSmooth F (mlaplacian F f)) (x : M) :
    carre2 F V f x = mlaplacian F (carre F f f) x / 2
      - mvfderiv 𝓘(ℝ, F) (mlaplacian F f) x (mgrad F f x)
      + inner ℝ (CovariantDerivative.leviCivitaConnection 𝓘(ℝ, F) M (mgrad F V) x (mgrad F f x))
          (mgrad F f x) := by
  have hu := mdiffAt_of_smAt F (smAt_mgrad F hf x)
  have hv := mdiffAt_of_smAt F (smAt_mgrad F hV x)
  have hin : MDifferentiableAt 𝓘(ℝ, F) 𝓘(ℝ, ℝ)
      (fun y => inner ℝ (mgrad F V y) (mgrad F f y)) x :=
    MDifferentiableAt.inner_bundle (E := TangentSpace 𝓘(ℝ, F)) hv hu
  have hΔd : MDifferentiableAt 𝓘(ℝ, F) 𝓘(ℝ, ℝ) (mlaplacian F f) x :=
    (hΔ x).mdifferentiableAt (by simp)
  have hg : mgenerator F V f = fun y => mlaplacian F f y - inner ℝ (mgrad F V y) (mgrad F f y) :=
    rfl
  have h1 : carre F f (mgenerator F V f) x =
      mvfderiv 𝓘(ℝ, F) (mlaplacian F f) x (mgrad F f x)
        - (inner ℝ (CovariantDerivative.leviCivitaConnection 𝓘(ℝ, F) M (mgrad F V) x (mgrad F f x))
            (mgrad F f x)
          + inner ℝ (mgrad F V x) (CovariantDerivative.leviCivitaConnection 𝓘(ℝ, F) M
              (mgrad F f) x (mgrad F f x))) := by
    rw [carre_eq_mvfderiv, hg, mvfderiv_fun_sub hΔd hin, sub_apply,
      mvfderiv_inner_lc F hv hu]
  have h2 : inner ℝ (mgrad F V x) (mgrad F (carre F f f) x) =
      2 * inner ℝ (CovariantDerivative.leviCivitaConnection 𝓘(ℝ, F) M (mgrad F f) x
        (mgrad F V x)) (mgrad F f x) := by
    rw [real_inner_comm, inner_mgrad_eq, mvfderiv_carre_apply F hf]
  have h3 := hsymm f hf x (mgrad F V x) (mgrad F f x)
  have h4 := real_inner_comm (CovariantDerivative.leviCivitaConnection 𝓘(ℝ, F) M
    (mgrad F f) x (mgrad F f x)) (mgrad F V x)
  unfold carre2
  rw [h1]
  simp only [mgenerator]
  rw [h2]
  linarith

end Quad

end CutCur.WBoch
