module

public import CutoffRigidity.Statements
public import CutoffRigidity.Extra.RicciBochner

/-! # Item 2(b): the Bochner formula in vector form, `∇𝓛 = 𝓛∇ - Hess(V)∇ - Ric(∇,·)`

Manuscript Section 1.4: "The formula for `Γ₂` follows from the Bochner formula
`∇𝓛 = 𝓛∇ - Hess(V)∇ - Ric(∇,∇)`".  The project's scalar `bochner_identity` is already the
contracted form (it contains `mHessSq` and `mRic`).  The vector form adds the identity between
1-forms/vectors: for smooth `f`, `V`, `x`, `v ∈ T_x M`,

`d(𝓛f)(v) = ⟨𝓛_vec ∇f, v⟩ - Hess V(∇f, v) - Ric(v, ∇f)`,

where `𝓛_vec X = tr ∇²X - ∇_{∇V} X` is the Langevin operator on vector fields and the rough
Laplacian is the trace of the second covariant derivative along the (chart-constant) frame `mExt`.
-/

@[expose] public section

open Bundle Filter Set VectorField
open scoped Manifold ContDiff Topology

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace CutoffRigidity.Paper

open CutCur CutCur.WBoch

section

variable (F : Type) [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  {M : Type} [EMetricSpace M] [ChartedSpace F M] [IsManifold 𝓘(ℝ, F) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, F) ∞ F (fun x : M => TangentSpace 𝓘(ℝ, F) x)]

theorem mExt_eventually_frm (x : M) (i : Fin (Module.finrank ℝ (TangentSpace 𝓘(ℝ, F) x))) :
    ∀ᶠ y in nhds x, CutCur.mExt F x (stdOrthonormalBasis ℝ (TangentSpace 𝓘(ℝ, F) x) i) y =
      frm (F := F) x i y := by
  filter_upwards [(trv (F := F) x).open_baseSet.mem_nhds (mem_base (F := F) x)] with y hy
  set e := stdOrthonormalBasis ℝ (TangentSpace 𝓘(ℝ, F) x) i with he
  set c := (trivializationAt F (TangentSpace 𝓘(ℝ, F)) x (Bundle.TotalSpace.mk' F x e)).2 with hc
  have h1 : (trv (F := F) x).symm x c = e := by
    have := mExt_apply_self F x e
    unfold CutCur.mExt at this
    exact this
  have h2 : (trv (F := F) x).symmL ℝ x c = c := symmL_self x c
  have h3 : (trv (F := F) x).symmL ℝ x c = (trv (F := F) x).symm x c :=
    Trivialization.symmL_apply (R := ℝ) (trv (F := F) x) (mem_base x) c
  have hc' : c = bas (F := F) x i := by
    have : c = e := by rw [← h2, h3, h1]
    rw [this]; exact (congrFun (OrthonormalBasis.coe_toBasis (stdOrthonormalBasis ℝ (TangentSpace 𝓘(ℝ, F) x))) i).symm
  unfold CutCur.mExt
  rw [frm, Trivialization.localFrame_apply_of_mem_baseSet _ _ hy]
  simp only [Trivialization.basisAt, Trivialization.linearEquivAt_symm_apply, Module.Basis.map_apply]
  rw [← hc']

theorem mSecondDeriv_mExt_eq (hN : NabSmooth F M) {u : (y : M) → TangentSpace 𝓘(ℝ, F) y} {x : M}
    (hu : SmAt F u x) (i : Fin (Module.finrank ℝ (TangentSpace 𝓘(ℝ, F) x))) :
    mSecondDeriv F u (CutCur.mExt F x (stdOrthonormalBasis ℝ (TangentSpace 𝓘(ℝ, F) x) i))
      (CutCur.mExt F x (stdOrthonormalBasis ℝ (TangentSpace 𝓘(ℝ, F) x) i)) x =
    Sx F u (frm (F := F) x i) (frm (F := F) x i) x := by
  set E := CutCur.mExt F x (stdOrthonormalBasis ℝ (TangentSpace 𝓘(ℝ, F) x) i) with hE
  have hEs : SmAt F E x := mExt_smooth F x _
  have hZs : SmAt F (frm (F := F) x i) x := smAt_frm x i
  have hev := mExt_eventually_frm F x i
  have hEx : E x = frm (F := F) x i x := by rw [hE, mExt_apply_self, frm_self]
  have h1 : ∀ᶠ y in nhds x, nab F E u y = nab F (frm (F := F) x i) u y := by
    filter_upwards [hev] with y hy
    have hy' : E y = frm (F := F) x i y := hy
    simp only [nab, hy']
  unfold mSecondDeriv Sx
  have e1 : CovariantDerivative.leviCivitaConnection 𝓘(ℝ, F) M (fun y => CovariantDerivative.leviCivitaConnection 𝓘(ℝ, F) M u y (E y)) x (E x) =
      CovariantDerivative.leviCivitaConnection 𝓘(ℝ, F) M (nab F (frm (F := F) x i) u) x (frm (F := F) x i x) := by
    rw [hEx]
    exact cov_congr_ev (hN E u x hEs hu) (hN _ u x hZs hu) h1 _
  have e2 : CovariantDerivative.leviCivitaConnection 𝓘(ℝ, F) M E x (E x) =
      CovariantDerivative.leviCivitaConnection 𝓘(ℝ, F) M (frm (F := F) x i) x (frm (F := F) x i x) := by
    rw [hEx]; exact cov_congr_ev hEs hZs hev _
  rw [e2]
  rw [e1]

variable {F} in
theorem curv_swap (x : M) {A B C : (y : M) → TangentSpace 𝓘(ℝ, F) y} :
    curv F A B C x = - curv F B A C x := by
  unfold curv
  rw [VectorField.mlieBracket_swap_apply (V := A) (W := B)]
  simp only [map_neg]
  abel

/-- **Bochner formula in vector form** (manuscript Section 1.4, `∇𝓛 = 𝓛∇ - Hess(V)∇ - Ric(∇,·)`),
paired with an arbitrary tangent vector `v`:
`d(𝓛f)(v) = ⟨𝓛_vec ∇f, v⟩ - Hess V(∇f, v) - Ric(v, ∇f)`. -/
theorem bochner_vector {V f : M → ℝ} (hV : ContMDiff 𝓘(ℝ, F) 𝓘(ℝ, ℝ) ∞ V)
    (hf : ContMDiff 𝓘(ℝ, F) 𝓘(ℝ, ℝ) ∞ f) (x : M) (v : TangentSpace 𝓘(ℝ, F) x) :
    mvfderiv 𝓘(ℝ, F) (mgenerator F V f) x v =
      inner ℝ (mVecGenerator F V (mgrad F f) x) v
        - mHess F V x (mgrad F f x) v - mRic F x v (mgrad F f x) := by
  have hN : NabSmooth F M := fun X Y x hX hY => nabSmooth X Y x hX hY
  set u := mgrad F f with hu
  have huS : SmAt F u x := smAt_mgrad F hf x
  have hVS : SmAt F (mgrad F V) x := smAt_mgrad F hV x
  set X : (y : M) → TangentSpace 𝓘(ℝ, F) y := FiberBundle.extend F v with hXdef
  have hX : SmAt F X x := FiberBundle.contMDiffAt_extend (k := ∞) 𝓘(ℝ, F) F v
  have hXx : X x = v := FiberBundle.extend_apply_self F v
  -- Laplacian part
  have hlap := mvfderiv_mlaplacian_frm (F := F) x hN hf v
  have hterm : ∀ i, inner ℝ (CovariantDerivative.leviCivitaConnection 𝓘(ℝ, F) M
          (nab F (frm (F := F) x i) u) x v
        - CovariantDerivative.leviCivitaConnection 𝓘(ℝ, F) M u x
          (CovariantDerivative.leviCivitaConnection 𝓘(ℝ, F) M (frm (F := F) x i) x v))
        (stdOrthonormalBasis ℝ (TangentSpace 𝓘(ℝ, F) x) i) =
      inner ℝ (Sx F u (frm (F := F) x i) (frm (F := F) x i) x) v
        - inner ℝ (mCurv F (CutCur.mExt F x (stdOrthonormalBasis ℝ (TangentSpace 𝓘(ℝ, F) x) i))
            (CutCur.mExt F x v) (CutCur.mExt F x (u x)) x)
          (stdOrthonormalBasis ℝ (TangentSpace 𝓘(ℝ, F) x) i) := by
    intro i
    have hZs : SmAt F (frm (F := F) x i) x := smAt_frm x i
    have hZx := frm_self (F := F) x i
    have h1 := Sx_sub_Sx F u X (frm (F := F) x i) hX hZs
    have h2 := inner_Sx_symm F hN hf (X := frm (F := F) x i) (Y := X) (Z := frm (F := F) x i)
      hZs hX hZs
    have hS : Sx F u X (frm (F := F) x i) x =
        CovariantDerivative.leviCivitaConnection 𝓘(ℝ, F) M (nab F (frm (F := F) x i) u) x v
        - CovariantDerivative.leviCivitaConnection 𝓘(ℝ, F) M u x
          (CovariantDerivative.leviCivitaConnection 𝓘(ℝ, F) M (frm (F := F) x i) x v) := by
      unfold Sx; rw [hXx]
    have hc : curv F (frm (F := F) x i) X u x =
        mCurv F (CutCur.mExt F x (stdOrthonormalBasis ℝ (TangentSpace 𝓘(ℝ, F) x) i))
          (CutCur.mExt F x v) (CutCur.mExt F x (u x)) x := by
      rw [mCurv_eq_curv]
      exact curv_tensor F hN hZs (mExt_smooth F x _) hX (mExt_smooth F x _) huS
        (mExt_smooth F x _) (by rw [mExt_apply_self, hZx]) (by rw [mExt_apply_self, hXx])
        (by rw [mExt_apply_self])
    have h3 : Sx F u X (frm (F := F) x i) x = Sx F u (frm (F := F) x i) X x
        + curv F X (frm (F := F) x i) u x := by rw [← h1]; abel
    have h4 : curv F X (frm (F := F) x i) u x = - curv F (frm (F := F) x i) X u x :=
      curv_swap x
    rw [← hS, h3, h4, hc, inner_add_left, inner_neg_left, ← hZx, h2, hXx]
    ring
  have hrough : inner ℝ (mRoughLaplacian F u x) v =
      ∑ i, inner ℝ (Sx F u (frm (F := F) x i) (frm (F := F) x i) x) v := by
    unfold mRoughLaplacian
    rw [sum_inner]
    exact Finset.sum_congr rfl fun i _ => by rw [mSecondDeriv_mExt_eq F hN huS i]
  have hlap' : mvfderiv 𝓘(ℝ, F) (mlaplacian F f) x v =
      inner ℝ (mRoughLaplacian F u x) v - mRic F x v (u x) := by
    rw [hlap, hrough]
    unfold mRic
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => hterm i
  have hdl : MDifferentiableAt 𝓘(ℝ, F) 𝓘(ℝ, ℝ) (mlaplacian F f) x :=
    (msmooth_mlaplacian F hN hf x).mdifferentiableAt (by simp)
  have hdi : MDifferentiableAt 𝓘(ℝ, F) 𝓘(ℝ, ℝ) (fun y => inner ℝ (mgrad F V y) (u y)) x :=
    (CutCur.WReg.msmooth_carre hV hf x).mdifferentiableAt (by simp)
  have hgen : mvfderiv 𝓘(ℝ, F) (mgenerator F V f) x v =
      mvfderiv 𝓘(ℝ, F) (mlaplacian F f) x v
        - mvfderiv 𝓘(ℝ, F) (fun y => inner ℝ (mgrad F V y) (u y)) x v := by
    show mvfderiv 𝓘(ℝ, F) (fun y => mlaplacian F f y - inner ℝ (mgrad F V y) (u y)) x v = _
    rw [mvfderiv_fun_sub hdl hdi]
    rfl
  have hinn := mvfderiv_inner_lc F (mdiffAt_of_smAt F hVS) (mdiffAt_of_smAt F huS) v
  have s1 := hessian_symm F hV x (u x) v
  have s2 := hessian_symm F hf x v (mgrad F V x)
  unfold mVecGenerator mHess
  rw [hgen, hlap', hinn, inner_sub_left, s1, real_inner_comm _ (mgrad F V x), s2]
  ring

end

end CutoffRigidity.Paper
