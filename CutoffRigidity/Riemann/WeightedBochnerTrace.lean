module

public import CutoffRigidity.Riemann.WeightedBochnerDefs
public import CutoffRigidity.Riemann.WeightedRegularChart

/-! # G2: derivative of the Laplacian along a chart frame (trace derivative)

For a smooth `f` and the local frame `Z i` of the chart trivialization at `x` built from the
orthonormal basis of `T_xM`, the Laplacian `Δ f = Σ_i coeff_i (∇_{Z i} ∇f)` near `x`; this gives
smoothness of `Δ f` and the formula for `d(Δ f)(v)` in terms of covariant derivatives only.
-/

@[expose] public section
set_option linter.unusedSectionVars false
open Bundle Filter Set VectorField
open scoped Manifold ContDiff Topology
set_option backward.isDefEq.respectTransparency false

namespace CutCur.WBoch
variable {F : Type} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  {M : Type} [EMetricSpace M] [ChartedSpace F M] [IsManifold 𝓘(ℝ, F) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, F) ∞ F (fun x : M => TangentSpace 𝓘(ℝ, F) x)]

abbrev MdAt (X : (y : M) → TangentSpace 𝓘(ℝ, F) y) (x : M) : Prop :=
  MDifferentiableAt 𝓘(ℝ, F) 𝓘(ℝ, F).tangent (T% X) x

theorem SmAt.mdAt {X : (y : M) → TangentSpace 𝓘(ℝ, F) y} {x : M} (h : SmAt F X x) : MdAt X x :=
  ContMDiffAt.mdifferentiableAt h (by simp)

theorem mvfderiv_fun_sum' {ι : Type*} (s : Finset ι) {g : ι → M → ℝ} {x : M}
    (hg : ∀ i ∈ s, MDifferentiableAt 𝓘(ℝ, F) 𝓘(ℝ, ℝ) (g i) x) :
    mvfderiv 𝓘(ℝ, F) (fun y => ∑ i ∈ s, g i y) x = ∑ i ∈ s, mvfderiv 𝓘(ℝ, F) (g i) x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [mvfderiv_const]
  | insert a s ha ih =>
    simp only [Finset.mem_insert, forall_eq_or_imp] at hg
    have h1 : MDifferentiableAt 𝓘(ℝ, F) 𝓘(ℝ, ℝ) (fun y => ∑ i ∈ s, g i y) x := by
      have := MDifferentiableAt.sum (z := x) (t := s) (f := g) (I := 𝓘(ℝ, F)) (fun i hi => hg.2 i hi)
      have e : (fun y => ∑ i ∈ s, g i y) = ∑ i ∈ s, g i := by funext y; simp [Finset.sum_apply]
      rw [e]; exact this
    have := mvfderiv_add (I := 𝓘(ℝ, F)) hg.1 h1
    simp only [Finset.sum_insert ha]
    exact (this.trans (by rw [ih hg.2]))

theorem cov_sum {ι : Type*} (s : Finset ι) {σ : ι → (y : M) → TangentSpace 𝓘(ℝ, F) y} {x : M}
    (hσ : ∀ i ∈ s, SmAt F (σ i) x) :
    CovariantDerivative.leviCivitaConnection 𝓘(ℝ, F) M (fun y => ∑ i ∈ s, σ i y) x =
      ∑ i ∈ s, CovariantDerivative.leviCivitaConnection 𝓘(ℝ, F) M (σ i) x := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact (CovariantDerivative.leviCivitaConnection 𝓘(ℝ, F) M).isCovariantDerivativeOn.zero (x := x)
  | insert a s ha ih =>
    simp only [Finset.mem_insert, forall_eq_or_imp] at hσ
    have h1 : MdAt (fun y => ∑ i ∈ s, σ i y) x :=
      MDifferentiableAt.sum_section (fun i hi => (hσ.2 i hi).mdAt)
    have := (CovariantDerivative.leviCivitaConnection 𝓘(ℝ, F) M).isCovariantDerivativeOn.add
      hσ.1.mdAt h1 (x := x)
    have e : (fun y => ∑ i ∈ insert a s, σ i y) = σ a + (fun y => ∑ i ∈ s, σ i y) := by
      funext y; simp [Finset.sum_insert ha]
    rw [e, this, ih hσ.2, Finset.sum_insert ha]

section
variable (x : M)
/-- trivialization at x -/
noncomputable abbrev trv : Trivialization F (TotalSpace.proj : TotalSpace F (TangentSpace 𝓘(ℝ, F) : M → Type) → M) :=
  trivializationAt F (TangentSpace 𝓘(ℝ, F)) x

noncomputable abbrev bas : Module.Basis (Fin (Module.finrank ℝ (TangentSpace 𝓘(ℝ, F) x))) ℝ F :=
  (stdOrthonormalBasis ℝ (TangentSpace 𝓘(ℝ, F) x)).toBasis

noncomputable abbrev frm : Fin (Module.finrank ℝ (TangentSpace 𝓘(ℝ, F) x)) → (y : M) → TangentSpace 𝓘(ℝ, F) y :=
  (trv (F := F) x).localFrame (bas (F := F) x)

theorem mem_base : x ∈ (trv (F := F) x).baseSet := by simp [trv]

theorem symmL_self (u : F) : (trv (F := F) x).symmL ℝ x u = u :=
  CutoffRigidity.chartFrame_self (I := 𝓘(ℝ, F)) x u

theorem basisAt_self : (trv (F := F) x).basisAt (bas (F := F) x) (mem_base x) = bas (F := F) x := by
  apply Module.Basis.eq_of_apply_eq
  intro i
  simp only [Trivialization.basisAt, Module.Basis.map_apply, Trivialization.linearEquivAt_symm_apply]
  rw [← Trivialization.symmL_apply (R := ℝ) (trv (F := F) x) (mem_base x), symmL_self]
  rfl

theorem frm_self (i) : frm (F := F) x i x = stdOrthonormalBasis ℝ (TangentSpace 𝓘(ℝ, F) x) i := by
  rw [frm, Trivialization.localFrame_apply_of_mem_baseSet _ _ (mem_base x)]
  simp [Trivialization.basisAt, Trivialization.linearEquivAt_symm_apply]
  have h2 : ∀ u : F, (trv (F := F) x).symmL ℝ x u = u := fun u => CutoffRigidity.chartFrame_self (I := 𝓘(ℝ, F)) x u
  have h3 := Trivialization.symmL_apply (R := ℝ) (trv (F := F) x) (mem_base x) ((bas (F := F) x) i)
  rw [← h3, h2]
  exact congrFun (OrthonormalBasis.coe_toBasis _) i

/-- frame coefficient functional -/
noncomputable abbrev cf (i : Fin (Module.finrank ℝ (TangentSpace 𝓘(ℝ, F) x))) (y : M) :
    TangentSpace 𝓘(ℝ, F) y →ₗ[ℝ] ℝ :=
  (trv (F := F) x).localFrameCoeff 𝓘(ℝ, F) (bas (F := F) x) i y

theorem smAt_frm (i) : SmAt F (frm (F := F) x i) x := by
  exact contMDiffAt_localFrame_of_mem ∞ (trv (F := F) x) (bas (F := F) x) i (mem_base x)

theorem mlaplacian_eq_sum_cf (f : M → ℝ) {y : M} (hy : y ∈ (trv (F := F) x).baseSet) :
    mlaplacian F f y = ∑ i, cf (F := F) x i y
      (CovariantDerivative.leviCivitaConnection 𝓘(ℝ, F) M (mgrad F f) y (frm (F := F) x i y)) := by
  have h1 : mlaplacian F f y = LinearMap.trace ℝ (TangentSpace 𝓘(ℝ, F) y)
      (CovariantDerivative.leviCivitaConnection 𝓘(ℝ, F) M (mgrad F f) y).toLinearMap :=
    CutoffRigidity.manifoldLaplacian_eq_trace (I := 𝓘(ℝ, F)) f y
  rw [h1, LinearMap.trace_eq_matrix_trace ℝ ((trv (F := F) x).basisAt (bas (F := F) x) hy)]
  simp only [Matrix.trace, Matrix.diag, LinearMap.toMatrix_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  have := Trivialization.localFrameCoeff_apply_of_mem_baseSet (I := 𝓘(ℝ, F)) (trv (F := F) x) (bas (F := F) x) hy
    (fun y' => CovariantDerivative.leviCivitaConnection 𝓘(ℝ, F) M (mgrad F f) y' (frm (F := F) x i y')) i
  refine Eq.trans ?_ this.symm
  have h4 : frm (F := F) x i y = (trv (F := F) x).basisAt (bas (F := F) x) hy i := by
    rw [frm, Trivialization.localFrame_apply_of_mem_baseSet _ _ hy]
  rw [h4]
  rfl

theorem cf_self (i) (w : TangentSpace 𝓘(ℝ, F) x) :
    cf (F := F) x i x w = inner ℝ (stdOrthonormalBasis ℝ (TangentSpace 𝓘(ℝ, F) x) i) w := by
  have := Trivialization.localFrameCoeff_apply_of_mem_baseSet (I := 𝓘(ℝ, F)) (trv (F := F) x)
    (bas (F := F) x) (mem_base x) (FiberBundle.extend F w) i
  rw [FiberBundle.extend_apply_self] at this
  refine this.trans ?_
  rw [basisAt_self]
  exact (OrthonormalBasis.coe_toBasis_repr_apply _ _ _).trans (OrthonormalBasis.repr_apply_apply _ _ _)
end

theorem contMDiffAt_fun_sum' {ι : Type*} (s : Finset ι) {g : ι → M → ℝ} {x : M}
    (hg : ∀ i ∈ s, ContMDiffAt 𝓘(ℝ, F) 𝓘(ℝ, ℝ) ∞ (g i) x) :
    ContMDiffAt 𝓘(ℝ, F) 𝓘(ℝ, ℝ) ∞ (fun y => ∑ i ∈ s, g i y) x := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using contMDiffAt_const
  | insert a s ha ih =>
    simp only [Finset.mem_insert, forall_eq_or_imp] at hg
    simp only [Finset.sum_insert ha]
    exact (hg.1).add (ih hg.2)

section main
variable (x : M) {f : M → ℝ}

/-- coefficient of `∇_{Z_i} u` on `Z_j` -/
noncomputable def nu (f : M → ℝ) (i j : Fin (Module.finrank ℝ (TangentSpace 𝓘(ℝ, F) x))) (y : M) : ℝ :=
  cf (F := F) x j y (nab F (frm (F := F) x i) (mgrad F f) y)

theorem smAt_nab (hN : NabSmooth F M) (hf : MSmooth F f) (i) :
    SmAt F (nab F (frm (F := F) x i) (mgrad F f)) x :=
  hN _ _ x (smAt_frm x i) (CutCur.WReg.contMDiff_mgrad hf x)

theorem contMDiffAt_nu (hN : NabSmooth F M) (hf : MSmooth F f) (i j) :
    ContMDiffAt 𝓘(ℝ, F) 𝓘(ℝ, ℝ) ∞ (nu (F := F) x f i j) x :=
  contMDiffAt_localFrameCoeff (bas (F := F) x) (mem_base x) (smAt_nab x hN hf i) j

theorem mlaplacian_eventuallyEq :
    mlaplacian F f =ᶠ[𝓝 x] fun y => ∑ i, nu (F := F) x f i i y := by
  filter_upwards [(trv (F := F) x).open_baseSet.mem_nhds (mem_base x)] with y hy
  exact mlaplacian_eq_sum_cf x f hy

theorem msmooth_mlaplacian_aux (hN : NabSmooth F M) (hf : MSmooth F f) : MSmooth F (mlaplacian F f) := by
  intro x
  have : ContMDiffAt 𝓘(ℝ, F) 𝓘(ℝ, ℝ) ∞ (fun y => ∑ i, nu (F := F) x f i i y) x :=
    contMDiffAt_fun_sum' _ fun i _ => contMDiffAt_nu x hN hf i i
  exact this.congr_of_eventuallyEq (mlaplacian_eventuallyEq x)

theorem cov_nab_expand (hN : NabSmooth F M) (hf : MSmooth F f) (i) (v : TangentSpace 𝓘(ℝ, F) x) :
    CovariantDerivative.leviCivitaConnection 𝓘(ℝ, F) M (nab F (frm (F := F) x i) (mgrad F f)) x v =
      ∑ j, (nu (F := F) x f i j x • CovariantDerivative.leviCivitaConnection 𝓘(ℝ, F) M
          (frm (F := F) x j) x v
        + mvfderiv 𝓘(ℝ, F) (nu (F := F) x f i j) x v • frm (F := F) x j x) := by
  have hSm : ∀ j, SmAt F (fun y => nu (F := F) x f i j y • frm (F := F) x j y) x := fun j =>
    (contMDiffAt_nu x hN hf i j).smul_section (smAt_frm x j)
  have hev : nab F (frm (F := F) x i) (mgrad F f) =ᶠ[𝓝 x]
      fun y => ∑ j, nu (F := F) x f i j y • frm (F := F) x j y := by
    filter_upwards [(trv (F := F) x).open_baseSet.mem_nhds (mem_base x)] with y hy
    exact (Trivialization.eq_sum_localFrameCoeff_smul (I := 𝓘(ℝ, F)) (e := trv (F := F) x)
      (b := bas (F := F) x) (s := nab F (frm (F := F) x i) (mgrad F f)) hy)
  have h1 := (CovariantDerivative.leviCivitaConnection 𝓘(ℝ, F) M).isCovariantDerivativeOn.congr_of_eventuallyEq
    (smAt_nab x hN hf i).mdAt
    (MDifferentiableAt.sum_section (fun j _ => (hSm j).mdAt)) Filter.univ_mem hev
  rw [h1, cov_sum _ (fun j _ => hSm j), _root_.sum_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hl := (CovariantDerivative.leviCivitaConnection 𝓘(ℝ, F) M).isCovariantDerivativeOn.leibniz
    (g := nu (F := F) x f i j) (x := x) (smAt_frm x j).mdAt
    ((contMDiffAt_nu x hN hf i j).mdifferentiableAt (by simp))
  have hl' : CovariantDerivative.leviCivitaConnection 𝓘(ℝ, F) M
      (fun y => nu (F := F) x f i j y • frm (F := F) x j y) x v =
      nu (F := F) x f i j x • CovariantDerivative.leviCivitaConnection 𝓘(ℝ, F) M
          (frm (F := F) x j) x v
        + mvfderiv 𝓘(ℝ, F) (nu (F := F) x f i j) x v • frm (F := F) x j x :=
    congrArg (fun L => L v) hl
  exact hl'

theorem cf_frm_self (i j) :
    cf (F := F) x i x (frm (F := F) x j x) = if i = j then 1 else 0 := by
  rw [cf_self, frm_self]
  exact orthonormal_iff_ite.mp (stdOrthonormalBasis ℝ (TangentSpace 𝓘(ℝ, F) x)).orthonormal i j

theorem mvfderiv_mlaplacian_frm (hN : NabSmooth F M) (hf : MSmooth F f)
    (v : TangentSpace 𝓘(ℝ, F) x) :
    mvfderiv 𝓘(ℝ, F) (mlaplacian F f) x v =
      ∑ i, inner ℝ (CovariantDerivative.leviCivitaConnection 𝓘(ℝ, F) M
          (nab F (frm (F := F) x i) (mgrad F f)) x v
        - CovariantDerivative.leviCivitaConnection 𝓘(ℝ, F) M (mgrad F f) x
          (CovariantDerivative.leviCivitaConnection 𝓘(ℝ, F) M (frm (F := F) x i) x v))
        (stdOrthonormalBasis ℝ (TangentSpace 𝓘(ℝ, F) x) i) := by
  have hev := mlaplacian_eventuallyEq (F := F) (f := f) x
  have hd1 : mvfderiv 𝓘(ℝ, F) (mlaplacian F f) x =
      mvfderiv 𝓘(ℝ, F) (fun y => ∑ i, nu (F := F) x f i i y) x := by
    unfold mvfderiv
    rw [hev.mfderiv_eq, hev.self_of_nhds]
    rfl
  rw [hd1, mvfderiv_fun_sum' _ (fun i _ => (contMDiffAt_nu x hN hf i i).mdifferentiableAt (by simp))]
  set u' := CovariantDerivative.leviCivitaConnection 𝓘(ℝ, F) M (mgrad F f) x with hu'
  set w : Fin (Module.finrank ℝ (TangentSpace 𝓘(ℝ, F) x)) → TangentSpace 𝓘(ℝ, F) x := fun i =>
    CovariantDerivative.leviCivitaConnection 𝓘(ℝ, F) M (frm (F := F) x i) x v with hw
  have hcf : ∀ i (a : TangentSpace 𝓘(ℝ, F) x),
      inner ℝ a (stdOrthonormalBasis ℝ (TangentSpace 𝓘(ℝ, F) x) i) = cf (F := F) x i x a := by
    intro i a
    rw [cf_self, real_inner_comm]
  have h1 : ∀ i, cf (F := F) x i x (CovariantDerivative.leviCivitaConnection 𝓘(ℝ, F) M
      (nab F (frm (F := F) x i) (mgrad F f)) x v) =
      ∑ j, nu (F := F) x f i j x * cf (F := F) x i x (w j)
        + mvfderiv 𝓘(ℝ, F) (nu (F := F) x f i i) x v := by
    intro i
    rw [cov_nab_expand x hN hf i v, map_sum]
    simp only [map_add, map_smul, cf_frm_self, smul_eq_mul, mul_ite, mul_one, mul_zero,
      Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    rfl
  have h2 : ∀ i, cf (F := F) x i x (u' (w i)) = ∑ k, cf (F := F) x k x (w i) * nu (F := F) x f k i x := by
    intro i
    have hexp : w i = ∑ k, cf (F := F) x k x (w i) • frm (F := F) x k x := by
      have := (stdOrthonormalBasis ℝ (TangentSpace 𝓘(ℝ, F) x)).sum_repr' (w i)
      conv_lhs => rw [← this]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [cf_self, frm_self]
    conv_lhs => rw [hexp]
    rw [map_sum, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [map_smul, smul_eq_mul]
    rfl
  simp only [hcf, map_sub]
  simp only [hw] at h1 h2
  simp only [h1, h2, Finset.sum_sub_distrib, Finset.sum_add_distrib, _root_.sum_apply]
  rw [Finset.sum_comm (f := fun i k => (cf (F := F) x k x) (CovariantDerivative.leviCivitaConnection 𝓘(ℝ, F) M (frm (F := F) x i) x v) * nu (F := F) x f k i x)]
  simp only [mul_comm]
  ring
end main

section final
variable (F) in
/-- **(P3)** Trace derivative: for the chart-trivialization frame `Z i` (smooth at `x`,
orthonormal at `x`) and every smooth `f`,
`d(Δf)(v) = Σ_i ⟨∇_v ∇_{Z i} ∇f - ∇_{∇_v Z i} ∇f, e_i⟩`. -/
theorem exists_frame_trace (hN : NabSmooth F M) (x : M) :
    ∃ Z : Fin (Module.finrank ℝ (TangentSpace 𝓘(ℝ, F) x)) → (y : M) → TangentSpace 𝓘(ℝ, F) y,
      (∀ i, SmAt F (Z i) x) ∧
      (∀ i, Z i x = stdOrthonormalBasis ℝ (TangentSpace 𝓘(ℝ, F) x) i) ∧
      ∀ f : M → ℝ, MSmooth F f → ∀ v : TangentSpace 𝓘(ℝ, F) x,
        mvfderiv 𝓘(ℝ, F) (mlaplacian F f) x v =
          ∑ i, inner ℝ (CovariantDerivative.leviCivitaConnection 𝓘(ℝ, F) M
              (nab F (Z i) (mgrad F f)) x v
            - CovariantDerivative.leviCivitaConnection 𝓘(ℝ, F) M (mgrad F f) x
              (CovariantDerivative.leviCivitaConnection 𝓘(ℝ, F) M (Z i) x v))
            (stdOrthonormalBasis ℝ (TangentSpace 𝓘(ℝ, F) x) i) :=
  ⟨frm (F := F) x, smAt_frm x, frm_self x, fun _ hf v => mvfderiv_mlaplacian_frm x hN hf v⟩

variable (F) in
/-- The Laplace-Beltrami operator maps smooth functions to smooth functions. -/
theorem msmooth_mlaplacian (hN : NabSmooth F M) {f : M → ℝ} (hf : MSmooth F f) :
    MSmooth F (mlaplacian F f) :=
  msmooth_mlaplacian_aux hN hf
end final

end CutCur.WBoch
