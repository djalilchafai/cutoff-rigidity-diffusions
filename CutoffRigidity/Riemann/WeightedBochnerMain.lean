module

public import CutoffRigidity.Riemann.WeightedBochnerDefs
public import CutoffRigidity.Riemann.WeightedBochnerHessian
public import CutoffRigidity.Riemann.WeightedBochnerCurv
public import CutoffRigidity.Riemann.WeightedBochnerTrace
public import CutoffRigidity.Riemann.WeightedBochnerQuad
public import CutoffRigidity.Riemann.WeightedBochnerTest
public import CutoffRigidity.Riemann.WeightedBochnerNabSmooth

/-! # G2: the Bochner inequality `‖Hess f‖² + ρ Γ(f) ≤ Γ₂(f)` from `CD ρ V`

Assembly of the pieces `WeightedBochner{Hessian,Curv,Trace,Quad,Test,NabSmooth}`:
the defect `Γ₂(f)(x) - ‖Hess f(x)‖²` equals `-Σᵢ ⟨curv(∇f, Zᵢ, ∇f), eᵢ⟩ + Hess V(∇f,∇f)`, which depends
only on `∇f(x)` by tensoriality of `curv`; testing against a function with the same gradient
at `x` and vanishing Hessian at `x` gives the claim.
-/

@[expose] public section
open Bundle Filter Set VectorField
open scoped Manifold ContDiff Topology
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace CutCur.WBoch

variable (F : Type) [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  {M : Type} [EMetricSpace M] [ChartedSpace F M] [IsManifold 𝓘(ℝ, F) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, F) ∞ F (fun x : M => TangentSpace 𝓘(ℝ, F) x)]

/-- the second covariant derivative expression `∇_X(∇_Y u) - ∇_{∇_X Y} u` at `x`. -/
noncomputable def Sx (u X Y : (y : M) → TangentSpace 𝓘(ℝ, F) y) (x : M) : TangentSpace 𝓘(ℝ, F) x :=
  CovariantDerivative.leviCivitaConnection 𝓘(ℝ, F) M (nab F Y u) x (X x)
    - CovariantDerivative.leviCivitaConnection 𝓘(ℝ, F) M u x
      (CovariantDerivative.leviCivitaConnection 𝓘(ℝ, F) M Y x (X x))

theorem Sx_sub_Sx (u X Y : (y : M) → TangentSpace 𝓘(ℝ, F) y) {x : M} (hX : SmAt F X x)
    (hY : SmAt F Y x) :
    Sx F u X Y x - Sx F u Y X x = curv F X Y u x := by
  have htor := (CovariantDerivative.torsion_eq_zero_iff (CovariantDerivative.leviCivitaConnection 𝓘(ℝ, F) M)).mp
    (CovariantDerivative.torsion_leviCivitaConnection_eq_zero 𝓘(ℝ, F)) (X := X) (Y := Y) (x := x)
    (hX.mdifferentiableAt (by simp)) (hY.mdifferentiableAt (by simp))
  unfold Sx curv
  rw [← htor, map_sub]
  abel


theorem inner_Sx_symm (hN : NabSmooth F M) {f : M → ℝ} (hf : MSmooth F f)
    {X Y Z : (y : M) → TangentSpace 𝓘(ℝ, F) y} {x : M}
    (hX : SmAt F X x) (hY : SmAt F Y x) (hZ : SmAt F Z x) :
    inner ℝ (Sx F (mgrad F f) X Y x) (Z x) = inner ℝ (Sx F (mgrad F f) X Z x) (Y x) := by
  set u := mgrad F f with hu
  have hcompat := CovariantDerivative.isMetricCompatible_leviCivitaConnection (𝓘(ℝ, F)) (M := M)
  have hu_sm : SmAt F u x := (CutCur.WReg.contMDiff_mgrad hf x : _)
  have hNY : MDifferentiableAt 𝓘(ℝ, F) 𝓘(ℝ, F).tangent (T% (nab F Y u)) x :=
    (hN Y u x hY hu_sm).mdifferentiableAt (by simp)
  have hNZ : MDifferentiableAt 𝓘(ℝ, F) 𝓘(ℝ, F).tangent (T% (nab F Z u)) x :=
    (hN Z u x hZ hu_sm).mdifferentiableAt (by simp)
  have hYd := hY.mdifferentiableAt (by simp)
  have hZd := hZ.mdifferentiableAt (by simp)
  have e1 := hcompat.mvfderiv_inner_eq X hNY hZd
  have e2 := hcompat.mvfderiv_inner_eq X hNZ hYd
  have hfun : (fun y => inner ℝ (nab F Y u y) (Z y)) = fun y => inner ℝ (nab F Z u y) (Y y) := by
    funext y
    exact hessian_symm F hf y (Y y) (Z y)
  have e3 : mvfderiv 𝓘(ℝ, F) (fun y => inner ℝ (nab F Y u y) (Z y)) x (X x) =
      mvfderiv 𝓘(ℝ, F) (fun y => inner ℝ (nab F Z u y) (Y y)) x (X x) := by rw [hfun]
  have s1 := hessian_symm F hf x (Y x) (CovariantDerivative.leviCivitaConnection 𝓘(ℝ, F) M Z x (X x))
  have s2 := hessian_symm F hf x (Z x) (CovariantDerivative.leviCivitaConnection 𝓘(ℝ, F) M Y x (X x))
  simp only [Sx, inner_sub_left]
  simp only [nab] at e1 e2 e3 ⊢
  rw [e1, e2] at e3
  linarith [real_inner_comm (Y x) (CovariantDerivative.leviCivitaConnection 𝓘(ℝ, F) M u x (CovariantDerivative.leviCivitaConnection 𝓘(ℝ, F) M Z x (X x)))]


theorem carre2_sub_hess (hN : NabSmooth F M) {V f : M → ℝ} (hV : MSmooth F V) (hf : MSmooth F f)
    (x : M)
    (Z : Fin (Module.finrank ℝ (TangentSpace 𝓘(ℝ, F) x)) → (y : M) → TangentSpace 𝓘(ℝ, F) y)
    (hZ : ∀ i, SmAt F (Z i) x)
    (hZx : ∀ i, Z i x = stdOrthonormalBasis ℝ (TangentSpace 𝓘(ℝ, F) x) i)
    (htr : ∀ v : TangentSpace 𝓘(ℝ, F) x,
        mvfderiv 𝓘(ℝ, F) (mlaplacian F f) x v =
          ∑ i, inner ℝ (CovariantDerivative.leviCivitaConnection 𝓘(ℝ, F) M (nab F (Z i) (mgrad F f)) x v - CovariantDerivative.leviCivitaConnection 𝓘(ℝ, F) M (mgrad F f) x (CovariantDerivative.leviCivitaConnection 𝓘(ℝ, F) M (Z i) x v))
            (stdOrthonormalBasis ℝ (TangentSpace 𝓘(ℝ, F) x) i))
    (hc2 : carre2 F V f x = mlaplacian F (carre F f f) x / 2
      - mvfderiv 𝓘(ℝ, F) (mlaplacian F f) x (mgrad F f x)
      + inner ℝ (CovariantDerivative.leviCivitaConnection 𝓘(ℝ, F) M (mgrad F V) x (mgrad F f x)) (mgrad F f x)) :
    carre2 F V f x - mHessNormSq F f x =
      - ∑ i, inner ℝ (curv F (mgrad F f) (Z i) (mgrad F f) x)
          (stdOrthonormalBasis ℝ (TangentSpace 𝓘(ℝ, F) x) i)
      + inner ℝ (CovariantDerivative.leviCivitaConnection 𝓘(ℝ, F) M (mgrad F V) x (mgrad F f x)) (mgrad F f x) := by
  set u := mgrad F f with hu
  have hu_sm : SmAt F u x := (CutCur.WReg.contMDiff_mgrad hf x : _)
  rw [hc2, mlaplacian_carre_self F hN hf x Z hZ hZx, htr]
  have hH : mHessNormSq F f x = ∑ i, ‖CovariantDerivative.leviCivitaConnection 𝓘(ℝ, F) M u x
      (stdOrthonormalBasis ℝ (TangentSpace 𝓘(ℝ, F) x) i)‖ ^ 2 := rfl
  rw [hH]
  simp only [← hu]
  have key : ∀ i, inner ℝ (CovariantDerivative.leviCivitaConnection 𝓘(ℝ, F) M (nab F (Z i) u) x (u x)
        - CovariantDerivative.leviCivitaConnection 𝓘(ℝ, F) M u x
          (CovariantDerivative.leviCivitaConnection 𝓘(ℝ, F) M (Z i) x (u x)))
        (stdOrthonormalBasis ℝ (TangentSpace 𝓘(ℝ, F) x) i)
      = inner ℝ (CovariantDerivative.leviCivitaConnection 𝓘(ℝ, F) M (nab F (Z i) u) x
          (stdOrthonormalBasis ℝ (TangentSpace 𝓘(ℝ, F) x) i)
          - CovariantDerivative.leviCivitaConnection 𝓘(ℝ, F) M u x
            (CovariantDerivative.leviCivitaConnection 𝓘(ℝ, F) M (Z i) x
              (stdOrthonormalBasis ℝ (TangentSpace 𝓘(ℝ, F) x) i))) (u x)
        + inner ℝ (curv F u (Z i) u x) (stdOrthonormalBasis ℝ (TangentSpace 𝓘(ℝ, F) x) i) := by
    intro i
    have h1 := Sx_sub_Sx F u u (Z i) hu_sm (hZ i)
    have h2 := inner_Sx_symm F hN hf (X := Z i) (Y := u) (Z := Z i) (hZ i) hu_sm (hZ i)
    have h5 : Sx F u u (Z i) x = Sx F u (Z i) u x + curv F u (Z i) u x := by
      rw [← h1]; abel
    have h6 : inner ℝ (Sx F u u (Z i) x) (stdOrthonormalBasis ℝ (TangentSpace 𝓘(ℝ, F) x) i)
        = inner ℝ (Sx F u (Z i) (Z i) x) (u x)
          + inner ℝ (curv F u (Z i) u x) (stdOrthonormalBasis ℝ (TangentSpace 𝓘(ℝ, F) x) i) := by
      rw [h5, inner_add_left, ← hZx i]
      rw [h2]
    have h7 : Sx F u (Z i) (Z i) x = CovariantDerivative.leviCivitaConnection 𝓘(ℝ, F) M (nab F (Z i) u) x
          (stdOrthonormalBasis ℝ (TangentSpace 𝓘(ℝ, F) x) i)
        - CovariantDerivative.leviCivitaConnection 𝓘(ℝ, F) M u x
          (CovariantDerivative.leviCivitaConnection 𝓘(ℝ, F) M (Z i) x
            (stdOrthonormalBasis ℝ (TangentSpace 𝓘(ℝ, F) x) i)) := by
      rw [← hZx i]; rfl
    rw [← h7]
    exact h6
  have hsum : ∀ i, inner ℝ (CovariantDerivative.leviCivitaConnection 𝓘(ℝ, F) M (nab F (Z i) u) x
      (stdOrthonormalBasis ℝ (TangentSpace 𝓘(ℝ, F) x) i)
        - CovariantDerivative.leviCivitaConnection 𝓘(ℝ, F) M u x
          (CovariantDerivative.leviCivitaConnection 𝓘(ℝ, F) M (Z i) x
            (stdOrthonormalBasis ℝ (TangentSpace 𝓘(ℝ, F) x) i))) (u x)
      = inner ℝ (CovariantDerivative.leviCivitaConnection 𝓘(ℝ, F) M (nab F (Z i) u) x (u x)
        - CovariantDerivative.leviCivitaConnection 𝓘(ℝ, F) M u x
          (CovariantDerivative.leviCivitaConnection 𝓘(ℝ, F) M (Z i) x (u x)))
        (stdOrthonormalBasis ℝ (TangentSpace 𝓘(ℝ, F) x) i)
        - inner ℝ (curv F u (Z i) u x) (stdOrthonormalBasis ℝ (TangentSpace 𝓘(ℝ, F) x) i) := by
    intro i; rw [key i]; ring
  simp only [hsum, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  ring


/-- The Bochner defect of a smooth function at `x`: `Γ₂(f) - ‖Hess f‖²` as a function of the frame,
the gradient field and `V`. -/
theorem carre2_sub_hess_eq (hN : NabSmooth F M) {V f : M → ℝ} (hV : MSmooth F V) (hf : MSmooth F f)
    (x : M)
    (Z : Fin (Module.finrank ℝ (TangentSpace 𝓘(ℝ, F) x)) → (y : M) → TangentSpace 𝓘(ℝ, F) y)
    (hZ : ∀ i, SmAt F (Z i) x)
    (hZx : ∀ i, Z i x = stdOrthonormalBasis ℝ (TangentSpace 𝓘(ℝ, F) x) i)
    (htr : ∀ f : M → ℝ, MSmooth F f → ∀ v : TangentSpace 𝓘(ℝ, F) x,
        mvfderiv 𝓘(ℝ, F) (mlaplacian F f) x v =
          ∑ i, inner ℝ (CovariantDerivative.leviCivitaConnection 𝓘(ℝ, F) M (nab F (Z i) (mgrad F f)) x v - CovariantDerivative.leviCivitaConnection 𝓘(ℝ, F) M (mgrad F f) x (CovariantDerivative.leviCivitaConnection 𝓘(ℝ, F) M (Z i) x v))
            (stdOrthonormalBasis ℝ (TangentSpace 𝓘(ℝ, F) x) i)) :
    carre2 F V f x - mHessNormSq F f x =
      - ∑ i, inner ℝ (curv F (mgrad F f) (Z i) (mgrad F f) x)
          (stdOrthonormalBasis ℝ (TangentSpace 𝓘(ℝ, F) x) i)
      + inner ℝ (CovariantDerivative.leviCivitaConnection 𝓘(ℝ, F) M (mgrad F V) x (mgrad F f x)) (mgrad F f x) :=
  carre2_sub_hess F hN hV hf x Z hZ hZx (htr f hf)
    (carre2_eq F hN hV hf (fun φ hφ y v w => hessian_symm F hφ y v w) (msmooth_mlaplacian F hN hf) x)

/-- **(G2)** The Bochner inequality `‖Hess f‖² + ρ Γ(f) ≤ Γ₂(f)` from the Challenge's `CD ρ V`. -/
theorem weightedBochnerIneq_of_CD {V : M → ℝ} (hV : MSmooth F V) {ρ : ℝ} (hCD : CD F ρ V) :
    WeightedBochnerIneq F V ρ := by
  intro f hf x
  have hN : NabSmooth F M := fun X Y x hX hY => nabSmooth X Y x hX hY
  obtain ⟨Z, hZ, hZx, htr⟩ := exists_frame_trace F hN x
  obtain ⟨g, hg, hgx, hHg⟩ := exists_test_function F x (mgrad F f x)
  have hDf := carre2_sub_hess_eq F hN hV hf x Z hZ hZx htr
  have hDg := carre2_sub_hess_eq F hN hV hg x Z hZ hZx htr
  have huf : SmAt F (mgrad F f) x := CutCur.WReg.contMDiff_mgrad hf x
  have hug : SmAt F (mgrad F g) x := CutCur.WReg.contMDiff_mgrad hg x
  have hcurv : ∀ i, curv F (mgrad F f) (Z i) (mgrad F f) x = curv F (mgrad F g) (Z i) (mgrad F g) x := by
    intro i
    rw [curv_congr_left hN huf hug (hZ i) huf hgx.symm]
    exact curv_congr_right hN hug (hZ i) huf hug
      (fun φ hφ => mvfderiv_mlieBracket F hφ hug (hZ i)) hgx.symm
  simp only [hcurv] at hDf
  simp only [hgx] at hDg
  have hcarre : carre F g g x = carre F f f x := by
    simp only [carre, hgx]
  have h1 := hCD g hg x
  rw [hHg] at hDg
  rw [hcarre] at h1
  linarith

end CutCur.WBoch

namespace CutCur

/-- **(G2)** `WeightedBochnerIneq` from the Challenge hypothesis `CD ρ V`. -/
theorem weightedBochnerIneq_of_CD (F : Type) [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ F]
    {M : Type} [EMetricSpace M] [ChartedSpace F M] [IsManifold 𝓘(ℝ, F) ∞ M]
    [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
    [IsContMDiffRiemannianBundle 𝓘(ℝ, F) ∞ F (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
    {V : M → ℝ} (hV : MSmooth F V) {ρ : ℝ} (hCD : CD F ρ V) : WeightedBochnerIneq F V ρ :=
  WBoch.weightedBochnerIneq_of_CD F hV hCD

end CutCur
