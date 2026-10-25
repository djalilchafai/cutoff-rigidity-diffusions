module

public import CutoffRigidity.Statements
public import CutoffRigidity.Riemann.WeightedBochnerMain

/-! # Bochner identity and `CD(ρ,∞) ⇔ Ric + Hess V ≥ ρ g` (manuscript lines ~641-663)

The Ricci tensor is defined from Mathlib's Levi-Civita connection and Lie bracket only:
`mCurv X Y Z = ∇_X ∇_Y Z - ∇_Y ∇_X Z - ∇_[X,Y] Z`, applied to the (choice-free) extensions of tangent
vectors obtained from the canonical trivialization at the base point, and
`mRic x v w = ∑ᵢ ⟨R(eᵢ,v)w, eᵢ⟩`.  The definitions are in `Challenge.lean`, namespace `CutCur`
(they are in `Challenge.lean`), the theorems in `CutoffRigidity.Paper`.
-/

@[expose] public section

open Bundle Filter Set
open scoped Manifold ContDiff Topology

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

namespace CutoffRigidity.Paper

open CutCur CutCur.WBoch

section

variable (F : Type) [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  {M : Type} [EMetricSpace M] [ChartedSpace F M] [IsManifold 𝓘(ℝ, F) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, F) ∞ F (fun x : M => TangentSpace 𝓘(ℝ, F) x)]

theorem mCurv_eq_curv (X Y Z : (y : M) → TangentSpace 𝓘(ℝ, F) y) (x : M) :
    CutCur.mCurv F X Y Z x = curv F X Y Z x := rfl

theorem mHessSq_eq (f : M → ℝ) (x : M) : CutCur.mHessSq F f x = CutCur.mHessNormSq F f x := rfl

theorem mExt_apply_self (x : M) (v : TangentSpace 𝓘(ℝ, F) x) : CutCur.mExt F x v x = v := by
  unfold CutCur.mExt
  have hx : x ∈ (trivializationAt F (TangentSpace 𝓘(ℝ, F)) x).baseSet :=
    FiberBundle.mem_baseSet_trivializationAt F _ x
  exact (trivializationAt F (TangentSpace 𝓘(ℝ, F)) x).symm_apply_apply_mk hx v

theorem mExt_smooth (x : M) (v : TangentSpace 𝓘(ℝ, F) x) : SmAt F (CutCur.mExt F x v) x := by
  unfold SmAt
  rw [contMDiffAt_section]
  set t := trivializationAt F (TangentSpace 𝓘(ℝ, F)) x
  have hx : x ∈ t.baseSet := FiberBundle.mem_baseSet_trivializationAt F _ x
  have : (fun y => (trivializationAt F (TangentSpace 𝓘(ℝ, F)) x
      ⟨y, CutCur.mExt F x v y⟩).2) =ᶠ[nhds x] fun _ => (t (Bundle.TotalSpace.mk' F x v)).2 := by
    filter_upwards [t.open_baseSet.mem_nhds hx] with y hy
    have h := congrArg Prod.snd (t.apply_mk_symm hy (t (Bundle.TotalSpace.mk' F x v)).2)
    exact h
  exact contMDiffAt_const.congr_of_eventuallyEq this

theorem curv_tensor (hN : NabSmooth F M)
    {X X' Y Y' Z Z' : (y : M) → TangentSpace 𝓘(ℝ, F) y} {x : M}
    (hX : SmAt F X x) (hX' : SmAt F X' x) (hY : SmAt F Y x) (hY' : SmAt F Y' x)
    (hZ : SmAt F Z x) (hZ' : SmAt F Z' x)
    (h1 : X x = X' x) (h2 : Y x = Y' x) (h3 : Z x = Z' x) :
    curv F X Y Z x = curv F X' Y' Z' x := by
  have swap : ∀ {A B C : (y : M) → TangentSpace 𝓘(ℝ, F) y}, curv F A B C x = - curv F B A C x := by
    intro A B C
    unfold curv
    rw [VectorField.mlieBracket_swap_apply (V := A) (W := B)]
    simp only [map_neg]
    abel
  have a : curv F X Y Z x = curv F X' Y Z x := curv_congr_left hN hX hX' hY hZ h1
  have b : curv F X' Y Z x = curv F X' Y' Z x := by
    rw [swap, swap (A := X'), curv_congr_left hN hY hY' hX' hZ h2]
  have c : curv F X' Y' Z x = curv F X' Y' Z' x :=
    curv_congr_right hN hX' hY' hZ hZ' (fun φ hφ => WBoch.mvfderiv_mlieBracket F hφ hX' hY') h3
  rw [a, b, c]

/-- **Bochner identity** (manuscript lines 641-654), pointwise:
`Γ₂(f) = ‖Hess f‖² + Ric(∇f,∇f) + Hess V(∇f,∇f)`. -/
theorem bochner_identity {V f : M → ℝ} (hV : ContMDiff 𝓘(ℝ, F) 𝓘(ℝ, ℝ) ∞ V)
    (hf : ContMDiff 𝓘(ℝ, F) 𝓘(ℝ, ℝ) ∞ f) (x : M) :
    CutCur.carre2 F V f x = CutCur.mHessSq F f x +
      (CutCur.mRic F x (CutCur.mgrad F f x) (CutCur.mgrad F f x) +
        CutCur.mHess F V x (CutCur.mgrad F f x) (CutCur.mgrad F f x)) := by
  have hN : NabSmooth F M := fun X Y x hX hY => nabSmooth X Y x hX hY
  obtain ⟨Z, hZ, hZx, htr⟩ := exists_frame_trace F hN x
  have hDf := carre2_sub_hess_eq F hN hV hf x Z hZ hZx htr
  have huf : SmAt F (CutCur.mgrad F f) x := CutCur.WReg.contMDiff_mgrad hf x
  have swap : ∀ {A B C : (y : M) → TangentSpace 𝓘(ℝ, F) y}, curv F A B C x = - curv F B A C x := by
    intro A B C
    unfold curv
    rw [VectorField.mlieBracket_swap_apply (V := A) (W := B)]
    simp only [map_neg]
    abel
  have key : ∀ i, curv F (CutCur.mgrad F f) (Z i) (CutCur.mgrad F f) x
      = - CutCur.mCurv F (CutCur.mExt F x (stdOrthonormalBasis ℝ (TangentSpace 𝓘(ℝ, F) x) i))
        (CutCur.mExt F x (CutCur.mgrad F f x)) (CutCur.mExt F x (CutCur.mgrad F f x)) x := by
    intro i
    rw [swap, mCurv_eq_curv]
    congr 1
    exact curv_tensor F hN (hZ i) (mExt_smooth F x _) huf (mExt_smooth F x _) huf
      (mExt_smooth F x _) (by rw [mExt_apply_self, hZx]) (by rw [mExt_apply_self])
      (by rw [mExt_apply_self])
  simp only [key, inner_neg_left, Finset.sum_neg_distrib, neg_neg] at hDf
  unfold CutCur.mRic CutCur.mHess
  rw [mHessSq_eq]
  linarith

/-- **`CD(ρ,∞) ⇔ Ric + Hess V ≥ ρ g`** (manuscript lines 655-663). -/
theorem CD_iff_ricci {V : M → ℝ} (hV : ContMDiff 𝓘(ℝ, F) 𝓘(ℝ, ℝ) ∞ V) (ρ : ℝ) :
    CutCur.CD F ρ V ↔ ∀ (x : M) (v : TangentSpace 𝓘(ℝ, F) x),
      ρ * ‖v‖ ^ 2 ≤ CutCur.mRic F x v v + CutCur.mHess F V x v v := by
  constructor
  · intro h x v
    obtain ⟨g, hg, hgx, hH⟩ := exists_test_function F x v
    have := h g hg x
    rw [bochner_identity F hV hg x, hgx] at this
    have h2 : CutCur.mHessSq F g x = 0 := by rw [mHessSq_eq]; exact hH
    simp only [CutCur.carre, hgx, h2, real_inner_self_eq_norm_sq] at this
    linarith
  · intro h f hf x
    rw [bochner_identity F hV hf x]
    have := h x (CutCur.mgrad F f x)
    have h0 : 0 ≤ CutCur.mHessSq F f x := by rw [mHessSq_eq]; exact CutCur.mHessNormSq_nonneg F f x
    simp only [CutCur.carre, real_inner_self_eq_norm_sq]
    linarith

end

end CutoffRigidity.Paper
