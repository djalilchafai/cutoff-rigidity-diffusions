module

public import CutoffRigidity.Riemann.WeightedBochnerDefs

/-! # G2: tensoriality of the curvature expression `curv`

`curv F X Y Z x` depends on `X` and `Z` only through `X x` and `Z x` (for fields smooth at `x`).
We argue directly with smooth germs (Mathlib's `TensorialAt` quantifies over merely
differentiable sections, for which `∇_Y Z` need not be differentiable).
-/

@[expose] public section
open Bundle Filter Set VectorField
open scoped Manifold ContDiff Topology
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

namespace CutCur.WBoch

section Curv

variable (F : Type) [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  {M : Type} [EMetricSpace M] [ChartedSpace F M] [IsManifold 𝓘(ℝ, F) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, F) ∞ F (fun x : M => TangentSpace 𝓘(ℝ, F) x)]

local notation "LC" => CovariantDerivative.leviCivitaConnection 𝓘(ℝ, F) M

variable {F}

theorem SmAt.mdiffAt {X : (y : M) → TangentSpace 𝓘(ℝ, F) y} {x : M} (h : SmAt F X x) :
    MDifferentiableAt 𝓘(ℝ, F) 𝓘(ℝ, F).tangent (T% X) x :=
  h.mdifferentiableAt (by simp)

theorem SmAt.eventually_mdiffAt {X : (y : M) → TangentSpace 𝓘(ℝ, F) y} {x : M}
    (h : SmAt F X x) :
    ∀ᶠ y in 𝓝 x, MDifferentiableAt 𝓘(ℝ, F) 𝓘(ℝ, F).tangent (T% X) y := by
  have h1 : ContMDiffAt 𝓘(ℝ, F) 𝓘(ℝ, F).tangent 1 (T% X) x := h.of_le (by simp)
  have := (contMDiffAt_iff_contMDiffAt_nhds (n := 1) (by simp)).1 h1
  exact this.mono fun y hy => hy.mdifferentiableAt (by simp)

theorem SmAt.add {X Y : (y : M) → TangentSpace 𝓘(ℝ, F) y} {x : M} (hX : SmAt F X x)
    (hY : SmAt F Y x) : SmAt F (X + Y) x :=
  ContMDiffAt.add_section hX hY

theorem SmAt.smul {φ : M → ℝ} {X : (y : M) → TangentSpace 𝓘(ℝ, F) y} {x : M}
    (hφ : ContMDiffAt 𝓘(ℝ, F) 𝓘(ℝ, ℝ) ∞ φ x) (hX : SmAt F X x) : SmAt F (φ • X) x :=
  ContMDiffAt.smul_section hφ hX

theorem contMDiffAt_one_mvfderiv_apply {φ : M → ℝ} {Y : (y : M) → TangentSpace 𝓘(ℝ, F) y}
    {x : M} (hφ : ContMDiffAt 𝓘(ℝ, F) 𝓘(ℝ, ℝ) ∞ φ x) (hY : SmAt F Y x) :
    ContMDiffAt 𝓘(ℝ, F) 𝓘(ℝ, ℝ) 1 (fun y => mvfderiv 𝓘(ℝ, F) φ y (Y y)) x := by
  have h2 : ContMDiffAt 𝓘(ℝ, F) 𝓘(ℝ, ℝ) 2 φ x := hφ.of_le (by simp)
  obtain ⟨u, hu, hφu⟩ := (contMDiffAt_iff_contMDiffOn_nhds (n := 2) (by simp)).1 h2
  obtain ⟨v, hvu, hv, hxv⟩ := mem_nhds_iff.1 hu
  have hφv : ContMDiffOn 𝓘(ℝ, F) 𝓘(ℝ, ℝ) 2 φ v := hφu.mono hvu
  have hT := hφv.contMDiffOn_tangentMapWithin (m := 1) (by norm_num) hv.uniqueMDiffOn
  have hY1 : ContMDiffAt 𝓘(ℝ, F) 𝓘(ℝ, F).tangent 1 (T% Y) x := hY.of_le (by simp)
  have hmem : (T% Y) x ∈ (TotalSpace.proj : TangentBundle 𝓘(ℝ, F) M → M) ⁻¹' v := hxv
  have hTa : ContMDiffAt 𝓘(ℝ, F).tangent 𝓘(ℝ, ℝ).tangent 1
      (tangentMapWithin 𝓘(ℝ, F) 𝓘(ℝ, ℝ) φ v) ((T% Y) x) := by
    refine (hT _ hmem).contMDiffAt ?_
    exact ((FiberBundle.continuous_proj F (TangentSpace 𝓘(ℝ, F))).continuousAt).preimage_mem_nhds (hv.mem_nhds hxv)
  have hc := (contMDiff_snd_tangentBundle_modelSpace (n := 1) ℝ 𝓘(ℝ, ℝ)).contMDiffAt.comp x
    (hTa.comp x hY1)
  refine hc.congr_of_eventuallyEq ?_
  filter_upwards [hv.mem_nhds hxv] with y hy
  simp only [Function.comp, tangentMapWithin, mfderivWithin_of_isOpen hv hy]
  rfl

theorem mdiffAt_mvfderiv_apply {φ : M → ℝ} {Y : (y : M) → TangentSpace 𝓘(ℝ, F) y}
    {x : M} (hφ : ContMDiffAt 𝓘(ℝ, F) 𝓘(ℝ, ℝ) ∞ φ x) (hY : SmAt F Y x) :
    MDifferentiableAt 𝓘(ℝ, F) 𝓘(ℝ, ℝ) (fun y => mvfderiv 𝓘(ℝ, F) φ y (Y y)) x :=
  (contMDiffAt_one_mvfderiv_apply hφ hY).mdifferentiableAt one_ne_zero

theorem curv_smul_left (hN : NabSmooth F M) {φ : M → ℝ}
    {X Y Z : (y : M) → TangentSpace 𝓘(ℝ, F) y} {x : M}
    (hφ : ContMDiffAt 𝓘(ℝ, F) 𝓘(ℝ, ℝ) ∞ φ x) (hX : SmAt F X x) (hY : SmAt F Y x)
    (hZ : SmAt F Z x) : curv F (φ • X) Y Z x = φ x • curv F X Y Z x := by
  have hφd : MDifferentiableAt 𝓘(ℝ, F) 𝓘(ℝ, ℝ) φ x := hφ.mdifferentiableAt (by simp)
  have hnab : nab F (φ • X) Z = φ • nab F X Z := by funext y; simp [nab]
  have hN1 : SmAt F (nab F X Z) x := hN X Z x hX hZ
  have hlb := mlieBracket_smul_left (I := 𝓘(ℝ, F)) (W := Y) hφd hX.mdiffAt
  have hl := congrArg (fun L => L (Y x))
    ((LC).isCovariantDerivativeOn.leibniz (s := Set.univ) hN1.mdiffAt hφd (hx := trivial))
  unfold curv
  rw [hnab, hlb]
  simp only [add_apply, smul_apply,
    ContinuousLinearMap.smulRight_apply] at hl
  simp only [Pi.smul_apply, map_add, map_neg, map_smul, smul_add, smul_neg] at hl ⊢
  rw [hl]
  simp only [nab, smul_eq_mul, Pi.smul_apply, smul_add]
  have hpx : (φ • X) x = φ x • X x := rfl
  rw [hpx, map_smul]
  module

theorem curv_add_left (hN : NabSmooth F M)
    {X X' Y Z : (y : M) → TangentSpace 𝓘(ℝ, F) y} {x : M}
    (hX : SmAt F X x) (hX' : SmAt F X' x) (hY : SmAt F Y x)
    (hZ : SmAt F Z x) : curv F (X + X') Y Z x = curv F X Y Z x + curv F X' Y Z x := by
  have hnab : nab F (X + X') Z = nab F X Z + nab F X' Z := by funext y; simp [nab]
  have h1 : SmAt F (nab F X Z) x := hN X Z x hX hZ
  have h2 : SmAt F (nab F X' Z) x := hN X' Z x hX' hZ
  have hlb := mlieBracket_add_left (I := 𝓘(ℝ, F)) (W := Y) hX.mdiffAt hX'.mdiffAt
  have hl := congrArg (fun L => L (Y x))
    ((LC).isCovariantDerivativeOn.add (s := Set.univ) h1.mdiffAt h2.mdiffAt (hx := trivial))
  unfold curv
  rw [hnab, hlb]
  simp only [add_apply] at hl
  have hpx : (X + X') x = X x + X' x := rfl
  rw [hl, hpx, map_add, map_add]
  abel

theorem nab_add_ev {Y Z Z' : (y : M) → TangentSpace 𝓘(ℝ, F) y} {x : M}
    (hZ : SmAt F Z x) (hZ' : SmAt F Z' x) :
    ∀ᶠ y in 𝓝 x, nab F Y (Z + Z') y = (nab F Y Z + nab F Y Z') y := by
  filter_upwards [hZ.eventually_mdiffAt, hZ'.eventually_mdiffAt] with y hy hy'
  have := congrArg (fun L => L (Y y))
    ((LC).isCovariantDerivativeOn.add (s := Set.univ) hy hy' (hx := trivial))
  simpa [nab] using this

/-- `∇_v` of a field only depends on the germ of the field (for fields smooth at `x`). -/
theorem cov_congr_ev' {A B : (y : M) → TangentSpace 𝓘(ℝ, F) y} {x : M}
    (hA : MDifferentiableAt 𝓘(ℝ, F) 𝓘(ℝ, F).tangent (T% A) x)
    (hB : MDifferentiableAt 𝓘(ℝ, F) 𝓘(ℝ, F).tangent (T% B) x)
    (hAB : ∀ᶠ y in 𝓝 x, A y = B y) (v : TangentSpace 𝓘(ℝ, F) x) :
    LC A x v = LC B x v :=
  congrArg (fun L => L v)
    ((LC).isCovariantDerivativeOn.congr_of_eventuallyEq (s := Set.univ)
      hA hB Filter.univ_mem hAB)

theorem cov_congr_ev {A B : (y : M) → TangentSpace 𝓘(ℝ, F) y} {x : M}
    (hA : SmAt F A x) (hB : SmAt F B x) (hAB : ∀ᶠ y in 𝓝 x, A y = B y) (v : TangentSpace 𝓘(ℝ, F) x) :
    LC A x v = LC B x v :=
  cov_congr_ev' hA.mdiffAt hB.mdiffAt hAB v

theorem cov_smul_apply {g : M → ℝ} {σ : (y : M) → TangentSpace 𝓘(ℝ, F) y} {x : M}
    (hg : MDifferentiableAt 𝓘(ℝ, F) 𝓘(ℝ, ℝ) g x)
    (hσ : MDifferentiableAt 𝓘(ℝ, F) 𝓘(ℝ, F).tangent (T% σ) x) (v : TangentSpace 𝓘(ℝ, F) x) :
    LC (g • σ) x v = g x • LC σ x v + mvfderiv 𝓘(ℝ, F) g x v • σ x := by
  have := congrArg (fun L => L v)
    ((LC).isCovariantDerivativeOn.leibniz (s := Set.univ) hσ hg (hx := trivial))
  simpa using this

theorem cov_add_apply {σ τ : (y : M) → TangentSpace 𝓘(ℝ, F) y} {x : M}
    (hσ : MDifferentiableAt 𝓘(ℝ, F) 𝓘(ℝ, F).tangent (T% σ) x)
    (hτ : MDifferentiableAt 𝓘(ℝ, F) 𝓘(ℝ, F).tangent (T% τ) x) (v : TangentSpace 𝓘(ℝ, F) x) :
    LC (σ + τ) x v = LC σ x v + LC τ x v := by
  have := congrArg (fun L => L v)
    ((LC).isCovariantDerivativeOn.add (s := Set.univ) hσ hτ (hx := trivial))
  simpa using this

theorem nab_smul_ev {φ : M → ℝ} {Y Z : (y : M) → TangentSpace 𝓘(ℝ, F) y} {x : M}
    (hφ : ContMDiffAt 𝓘(ℝ, F) 𝓘(ℝ, ℝ) ∞ φ x) (hZ : SmAt F Z x) :
    ∀ᶠ y in 𝓝 x, nab F Y (φ • Z) y =
      (φ • nab F Y Z + (fun y => mvfderiv 𝓘(ℝ, F) φ y (Y y)) • Z) y := by
  have h1 : ContMDiffAt 𝓘(ℝ, F) 𝓘(ℝ, ℝ) 1 φ x := hφ.of_le (by simp)
  have h2 := (contMDiffAt_iff_contMDiffAt_nhds (n := 1) (by simp)).1 h1
  filter_upwards [h2, hZ.eventually_mdiffAt] with y hy hy'
  have := cov_smul_apply (hy.mdifferentiableAt (by simp)) hy' (Y y)
  simpa [nab, add_comm] using this

theorem curv_add_right (hN : NabSmooth F M)
    {X Y Z Z' : (y : M) → TangentSpace 𝓘(ℝ, F) y} {x : M}
    (hX : SmAt F X x) (hY : SmAt F Y x)
    (hZ : SmAt F Z x) (hZ' : SmAt F Z' x) :
    curv F X Y (Z + Z') x = curv F X Y Z x + curv F X Y Z' x := by
  have hZZ : SmAt F (Z + Z') x := hZ.add hZ'
  have hY1 : SmAt F (nab F Y Z) x := hN Y Z x hY hZ
  have hY2 : SmAt F (nab F Y Z') x := hN Y Z' x hY hZ'
  have hX1 : SmAt F (nab F X Z) x := hN X Z x hX hZ
  have hX2 : SmAt F (nab F X Z') x := hN X Z' x hX hZ'
  have e1 := cov_congr_ev (hN Y (Z + Z') x hY hZZ) (hY1.add hY2) (nab_add_ev hZ hZ') (X x)
  have e2 := cov_congr_ev (hN X (Z + Z') x hX hZZ) (hX1.add hX2) (nab_add_ev hZ hZ') (Y x)
  have a1 := congrArg (fun L => L (X x))
    ((LC).isCovariantDerivativeOn.add (s := Set.univ) hY1.mdiffAt hY2.mdiffAt (hx := trivial))
  have a2 := congrArg (fun L => L (Y x))
    ((LC).isCovariantDerivativeOn.add (s := Set.univ) hX1.mdiffAt hX2.mdiffAt (hx := trivial))
  have a3 := congrArg (fun L => L (mlieBracket 𝓘(ℝ, F) X Y x))
    ((LC).isCovariantDerivativeOn.add (s := Set.univ) hZ.mdiffAt hZ'.mdiffAt (hx := trivial))
  simp only [add_apply] at a1 a2 a3
  unfold curv
  rw [e1, e2, a1, a2, a3]
  abel

theorem curv_smul_right (hN : NabSmooth F M) {φ : M → ℝ}
    {X Y Z : (y : M) → TangentSpace 𝓘(ℝ, F) y} {x : M}
    (hφ : ContMDiffAt 𝓘(ℝ, F) 𝓘(ℝ, ℝ) ∞ φ x) (hX : SmAt F X x) (hY : SmAt F Y x)
    (hZ : SmAt F Z x)
    (hbr : ∀ φ : M → ℝ, ContMDiffAt 𝓘(ℝ, F) 𝓘(ℝ, ℝ) ∞ φ x →
      mvfderiv 𝓘(ℝ, F) φ x (mlieBracket 𝓘(ℝ, F) X Y x) =
        mvfderiv 𝓘(ℝ, F) (fun y => mvfderiv 𝓘(ℝ, F) φ y (Y y)) x (X x)
          - mvfderiv 𝓘(ℝ, F) (fun y => mvfderiv 𝓘(ℝ, F) φ y (X y)) x (Y x)) :
    curv F X Y (φ • Z) x = φ x • curv F X Y Z x := by
  have hφd : MDifferentiableAt 𝓘(ℝ, F) 𝓘(ℝ, ℝ) φ x := hφ.mdifferentiableAt (by simp)
  have hφZ : SmAt F (φ • Z) x := hZ.smul hφ
  have hYZ : SmAt F (nab F Y Z) x := hN Y Z x hY hZ
  have hXZ : SmAt F (nab F X Z) x := hN X Z x hX hZ
  have hψY := mdiffAt_mvfderiv_apply (Y := Y) hφ hY
  have hψX := mdiffAt_mvfderiv_apply (Y := X) hφ hX
  have hA : MDifferentiableAt 𝓘(ℝ, F) 𝓘(ℝ, F).tangent
      (T% (φ • nab F Y Z + (fun y => mvfderiv 𝓘(ℝ, F) φ y (Y y)) • Z)) x :=
    mdifferentiableAt_add_section (hφd.smul_section hYZ.mdiffAt) (hψY.smul_section hZ.mdiffAt)
  have hB : MDifferentiableAt 𝓘(ℝ, F) 𝓘(ℝ, F).tangent
      (T% (φ • nab F X Z + (fun y => mvfderiv 𝓘(ℝ, F) φ y (X y)) • Z)) x :=
    mdifferentiableAt_add_section (hφd.smul_section hXZ.mdiffAt) (hψX.smul_section hZ.mdiffAt)
  have e1 := cov_congr_ev' (hN Y (φ • Z) x hY hφZ).mdiffAt hA (nab_smul_ev hφ hZ) (X x)
  have e2 := cov_congr_ev' (hN X (φ • Z) x hX hφZ).mdiffAt hB (nab_smul_ev hφ hZ) (Y x)
  rw [cov_add_apply (hφd.smul_section hYZ.mdiffAt) (hψY.smul_section hZ.mdiffAt),
    cov_smul_apply hφd hYZ.mdiffAt, cov_smul_apply hψY hZ.mdiffAt] at e1
  rw [cov_add_apply (hφd.smul_section hXZ.mdiffAt) (hψX.smul_section hZ.mdiffAt),
    cov_smul_apply hφd hXZ.mdiffAt, cov_smul_apply hψX hZ.mdiffAt] at e2
  have e3 := cov_smul_apply hφd hZ.mdiffAt (mlieBracket 𝓘(ℝ, F) X Y x)
  have hb := hbr φ hφ
  unfold curv
  rw [e1, e2, e3]
  simp only [nab, hb, map_sub, sub_smul]
  module

theorem exists_frame_decomp {D : (y : M) → TangentSpace 𝓘(ℝ, F) y} {x : M}
    (hD : SmAt F D x) (hDx : D x = 0) :
    ∃ (ι : Type) (_ : Fintype ι) (d : ι → M → ℝ)
      (s : ι → (y : M) → TangentSpace 𝓘(ℝ, F) y),
      (∀ i, ContMDiffAt 𝓘(ℝ, F) 𝓘(ℝ, ℝ) ∞ (d i) x) ∧ (∀ i, d i x = 0) ∧
      (∀ i, SmAt F (s i) x) ∧ ∀ᶠ y in 𝓝 x, D y = ∑ i, d i y • s i y := by
  let t := trivializationAt F (TangentSpace 𝓘(ℝ, F)) x
  have hx : x ∈ t.baseSet := FiberBundle.mem_baseSet_trivializationAt F _ x
  let b := Module.Basis.ofVectorSpace ℝ F
  refine ⟨_, inferInstance, fun i y => t.localFrameCoeff 𝓘(ℝ, F) b i y (D y), t.localFrame b,
    fun i => ?_, fun i => ?_, fun i => ?_, ?_⟩
  · exact contMDiffAt_localFrameCoeff (e := t) b hx hD i
  · simp [hDx]
  · exact contMDiffAt_localFrame_of_mem (e := t) _ b i hx
  · exact t.eventually_eq_localFrame_sum_coeff_smul b hx

theorem curv_ev_left (hN : NabSmooth F M)
    {X X' Y Z : (y : M) → TangentSpace 𝓘(ℝ, F) y} {x : M}
    (hX : SmAt F X x) (hX' : SmAt F X' x) (hZ : SmAt F Z x) (h : ∀ᶠ y in 𝓝 x, X y = X' y) :
    curv F X Y Z x = curv F X' Y Z x := by
  have hx : X x = X' x := h.self_of_nhds
  have e1 : ∀ᶠ y in 𝓝 x, nab F X Z y = nab F X' Z y := by
    filter_upwards [h] with y hy
    simp [nab, hy]
  have e2 := cov_congr_ev (hN X Z x hX hZ) (hN X' Z x hX' hZ) e1 (Y x)
  have h' : X =ᶠ[𝓝 x] X' := h
  have e3 : mlieBracket 𝓘(ℝ, F) X Y x = mlieBracket 𝓘(ℝ, F) X' Y x :=
    Filter.EventuallyEq.mlieBracket_vectorField_eq h' Filter.EventuallyEq.rfl
  unfold curv
  rw [e2, e3, hx]

theorem curv_sum_left (hN : NabSmooth F M) {ι : Type}
    {W : ι → (y : M) → TangentSpace 𝓘(ℝ, F) y} {Y Z : (y : M) → TangentSpace 𝓘(ℝ, F) y}
    {x : M} (hW : ∀ i, SmAt F (W i) x) (hY : SmAt F Y x) (hZ : SmAt F Z x)
    (t : Finset ι) :
    curv F (fun y => ∑ i ∈ t, W i y) Y Z x = ∑ i ∈ t, curv F (W i) Y Z x := by
  classical
  induction t using Finset.induction_on with
  | empty =>
    have h0 : SmAt F (fun y => ∑ i ∈ (∅ : Finset ι), W i y) x :=
      ContMDiffAt.sum_section (fun i hi => (hW i))
    have := curv_add_left hN h0 h0 hY hZ
    have hz : ((fun y => ∑ i ∈ (∅ : Finset ι), W i y) + fun y => ∑ i ∈ (∅ : Finset ι), W i y) =
        fun y => ∑ i ∈ (∅ : Finset ι), W i y := by funext y; simp
    rw [hz] at this
    simpa using this
  | insert a t ha ih =>
    have h1 : SmAt F (fun y => ∑ i ∈ t, W i y) x :=
      ContMDiffAt.sum_section (fun i hi => (hW i))
    have hfun : (fun y => ∑ i ∈ insert a t, W i y) = W a + fun y => ∑ i ∈ t, W i y := by
      funext y; simp [Finset.sum_insert ha]
    rw [hfun, curv_add_left hN (hW a) h1 hY hZ, ih, Finset.sum_insert ha]

theorem curv_zero_left (hN : NabSmooth F M)
    {D Y Z : (y : M) → TangentSpace 𝓘(ℝ, F) y} {x : M}
    (hD : SmAt F D x) (hDx : D x = 0) (hY : SmAt F Y x) (hZ : SmAt F Z x) :
    curv F D Y Z x = 0 := by
  obtain ⟨ι, _, d, s, hd, hd0, hs, hev⟩ := exists_frame_decomp hD hDx
  have hW : ∀ i, SmAt F (d i • s i) x := fun i => (hd i).smul_section (hs i)
  have hS : SmAt F (fun y => ∑ i, (d i • s i) y) x :=
    ContMDiffAt.sum_section (fun i _ => hW i)
  rw [curv_ev_left hN hD hS hZ (by simpa using hev), curv_sum_left hN hW hY hZ]
  apply Finset.sum_eq_zero
  intro i _
  rw [curv_smul_left hN (hd i) (hs i) hY hZ, hd0 i, zero_smul]

theorem curv_congr_left (hN : NabSmooth F M)
    {X X' Y Z : (y : M) → TangentSpace 𝓘(ℝ, F) y} {x : M}
    (hX : SmAt F X x) (hX' : SmAt F X' x) (hY : SmAt F Y x) (hZ : SmAt F Z x)
    (h : X x = X' x) : curv F X Y Z x = curv F X' Y Z x := by
  have hD : SmAt F (X' - X) x := ContMDiffAt.sub_section hX' hX
  have hDx : (X' - X) x = 0 := by simp [h]
  have h1 := curv_zero_left hN hD hDx hY hZ
  have h2 := curv_add_left hN hX hD hY hZ
  have h3 : X + (X' - X) = X' := by funext y; simp
  rw [h3] at h2
  rw [h2, h1, add_zero]

theorem nab_ev_right {X Z Z' : (y : M) → TangentSpace 𝓘(ℝ, F) y} {x : M}
    (hZ : SmAt F Z x) (hZ' : SmAt F Z' x) (h : ∀ᶠ y in 𝓝 x, Z y = Z' y) :
    ∀ᶠ y in 𝓝 x, nab F X Z y = nab F X Z' y := by
  filter_upwards [h.eventually_nhds, hZ.eventually_mdiffAt, hZ'.eventually_mdiffAt]
    with y hy hy1 hy2
  exact cov_congr_ev' hy1 hy2 hy _

theorem curv_ev_right (hN : NabSmooth F M)
    {X Y Z Z' : (y : M) → TangentSpace 𝓘(ℝ, F) y} {x : M}
    (hX : SmAt F X x) (hY : SmAt F Y x)
    (hZ : SmAt F Z x) (hZ' : SmAt F Z' x) (h : ∀ᶠ y in 𝓝 x, Z y = Z' y) :
    curv F X Y Z x = curv F X Y Z' x := by
  have e1 := cov_congr_ev (hN Y Z x hY hZ) (hN Y Z' x hY hZ') (nab_ev_right hZ hZ' h) (X x)
  have e2 := cov_congr_ev (hN X Z x hX hZ) (hN X Z' x hX hZ') (nab_ev_right hZ hZ' h) (Y x)
  have e3 := cov_congr_ev hZ hZ' h (mlieBracket 𝓘(ℝ, F) X Y x)
  unfold curv
  rw [e1, e2, e3]

theorem curv_sum_right (hN : NabSmooth F M) {ι : Type}
    {W : ι → (y : M) → TangentSpace 𝓘(ℝ, F) y} {X Y : (y : M) → TangentSpace 𝓘(ℝ, F) y}
    {x : M} (hW : ∀ i, SmAt F (W i) x) (hX : SmAt F X x) (hY : SmAt F Y x)
    (t : Finset ι) :
    curv F X Y (fun y => ∑ i ∈ t, W i y) x = ∑ i ∈ t, curv F X Y (W i) x := by
  classical
  induction t using Finset.induction_on with
  | empty =>
    have h0 : SmAt F (fun y => ∑ i ∈ (∅ : Finset ι), W i y) x :=
      ContMDiffAt.sum_section (fun i hi => (hW i))
    have := curv_add_right hN hX hY h0 h0
    have hz : ((fun y => ∑ i ∈ (∅ : Finset ι), W i y) + fun y => ∑ i ∈ (∅ : Finset ι), W i y) =
        fun y => ∑ i ∈ (∅ : Finset ι), W i y := by funext y; simp
    rw [hz] at this
    simpa using this
  | insert a t ha ih =>
    have h1 : SmAt F (fun y => ∑ i ∈ t, W i y) x :=
      ContMDiffAt.sum_section (fun i hi => (hW i))
    have hfun : (fun y => ∑ i ∈ insert a t, W i y) = W a + fun y => ∑ i ∈ t, W i y := by
      funext y; simp [Finset.sum_insert ha]
    rw [hfun, curv_add_right hN hX hY (hW a) h1, ih, Finset.sum_insert ha]

theorem curv_congr_right (hN : NabSmooth F M)
    {X Y Z Z' : (y : M) → TangentSpace 𝓘(ℝ, F) y} {x : M}
    (hX : SmAt F X x) (hY : SmAt F Y x) (hZ : SmAt F Z x) (hZ' : SmAt F Z' x)
    (hbr : ∀ φ : M → ℝ, ContMDiffAt 𝓘(ℝ, F) 𝓘(ℝ, ℝ) ∞ φ x →
      mvfderiv 𝓘(ℝ, F) φ x (mlieBracket 𝓘(ℝ, F) X Y x) =
        mvfderiv 𝓘(ℝ, F) (fun y => mvfderiv 𝓘(ℝ, F) φ y (Y y)) x (X x)
          - mvfderiv 𝓘(ℝ, F) (fun y => mvfderiv 𝓘(ℝ, F) φ y (X y)) x (Y x))
    (h : Z x = Z' x) : curv F X Y Z x = curv F X Y Z' x := by
  have hD : SmAt F (Z' - Z) x := ContMDiffAt.sub_section hZ' hZ
  have hDx : (Z' - Z) x = 0 := by simp [h]
  obtain ⟨ι, _, d, s, hd, hd0, hs, hev⟩ := exists_frame_decomp hD hDx
  have hW : ∀ i, SmAt F (d i • s i) x := fun i => (hd i).smul_section (hs i)
  have hS : SmAt F (fun y => ∑ i, (d i • s i) y) x :=
    ContMDiffAt.sum_section (fun i _ => hW i)
  have h1 : curv F X Y (Z' - Z) x = 0 := by
    rw [curv_ev_right hN hX hY hD hS (by simpa using hev), curv_sum_right hN hW hX hY]
    apply Finset.sum_eq_zero
    intro i _
    rw [curv_smul_right hN (hd i) hX hY (hs i) hbr, hd0 i, zero_smul]
  have h2 := curv_add_right hN hX hY hZ hD
  have h3 : Z + (Z' - Z) = Z' := by funext y; simp
  rw [h3] at h2
  rw [h2, h1, add_zero]

end Curv

end CutCur.WBoch
