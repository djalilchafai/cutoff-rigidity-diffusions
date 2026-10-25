module

public import CutoffRigidity.Riemann.WeightedBochnerDefs
public import CutoffRigidity.Riemann.WeightedRegularChart

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

theorem hessian_eq_fields {φ : M → ℝ} (hφ : MSmooth F φ) {X Y : (y : M) → TangentSpace 𝓘(ℝ, F) y}
    {x : M} (hX : SmAt F X x) (hY : SmAt F Y x) :
    inner ℝ (CovariantDerivative.leviCivitaConnection 𝓘(ℝ, F) M (mgrad F φ) x (X x)) (Y x) =
      mvfderiv 𝓘(ℝ, F) (fun y => mvfderiv 𝓘(ℝ, F) φ y (Y y)) x (X x)
        - mvfderiv 𝓘(ℝ, F) φ x (CovariantDerivative.leviCivitaConnection 𝓘(ℝ, F) M Y x (X x)) := by
  have hg : MDifferentiableAt 𝓘(ℝ, F) 𝓘(ℝ, F).tangent (T% (mgrad F φ)) x :=
    (WReg.contMDiff_mgrad hφ x).mdifferentiableAt (by simp)
  have hY' : MDifferentiableAt 𝓘(ℝ, F) 𝓘(ℝ, F).tangent (T% Y) x :=
    hY.mdifferentiableAt (by simp)
  have h := (CovariantDerivative.isMetricCompatible_leviCivitaConnection (I := 𝓘(ℝ, F))
    (M := M)).mvfderiv_inner_eq X hg hY'
  have e1 : (fun y => inner ℝ (mgrad F φ y) (Y y)) = fun y => mvfderiv 𝓘(ℝ, F) φ y (Y y) := by
    funext y; exact CutoffRigidity.inner_manifoldGradient _ φ y (Y y)
  have e2 : inner ℝ (mgrad F φ x) (CovariantDerivative.leviCivitaConnection 𝓘(ℝ, F) M Y x (X x))
      = mvfderiv 𝓘(ℝ, F) φ x (CovariantDerivative.leviCivitaConnection 𝓘(ℝ, F) M Y x (X x)) :=
    CutoffRigidity.inner_manifoldGradient _ φ x _
  beta_reduce at h
  rw [e2, e1] at h
  linarith


open CutoffRigidity in
/-- chart expression of a field is the trivialization coordinate -/
theorem chartCoordinateField_eq_coord (x₀ : M) {Y : (y : M) → TangentSpace 𝓘(ℝ, F) y} {z : F}
    (hz : z ∈ (extChartAt 𝓘(ℝ, F) x₀).target) :
    chartCoordinateField (I := 𝓘(ℝ, F)) x₀ Y z =
      WReg.coord x₀ Y ((extChartAt 𝓘(ℝ, F) x₀).symm z) := by
  have hy : (extChartAt 𝓘(ℝ, F) x₀).symm z ∈ (chartAt F x₀).source := by
    simpa only [extChartAt_source] using (extChartAt 𝓘(ℝ, F) x₀).map_target hz
  have hyt := WReg.mem_baseSet_of_mem_source (F := F) hy
  have h1 := chartFrame_chartCoordinateField (I := 𝓘(ℝ, F)) x₀ hz Y
  have h2 := WReg.chartFrame_coord (x₀ := x₀) hy Y
  have h3 := h1.trans h2.symm
  have h4 := congrArg ((trivializationAt F (TangentSpace 𝓘(ℝ, F)) x₀).continuousLinearMapAt ℝ
    ((extChartAt 𝓘(ℝ, F) x₀).symm z)) h3
  unfold chartFrame chartFrameCLM at h4
  rwa [(trivializationAt F (TangentSpace 𝓘(ℝ, F)) x₀).continuousLinearMapAt_symmL hyt,
    (trivializationAt F (TangentSpace 𝓘(ℝ, F)) x₀).continuousLinearMapAt_symmL hyt] at h4

open CutoffRigidity in
theorem fderiv_chart_vec (x₀ : M) {f : M → ℝ} (hf : MDifferentiableAt 𝓘(ℝ, F) 𝓘(ℝ, ℝ) f x₀)
    (w : F) :
    fderiv ℝ (f ∘ (extChartAt 𝓘(ℝ, F) x₀).symm) (extChartAt 𝓘(ℝ, F) x₀ x₀) w =
      mvfderiv 𝓘(ℝ, F) f x₀ w := by
  have := fderiv_chartScalar_direction x₀ hf (chartFrame (I := 𝓘(ℝ, F)) x₀ w)
  rw [chartCoordinateField_self, chartFrame_self] at this
  exact this

open CutoffRigidity in
theorem mlieBracket_center (x₀ : M) (X Y : (y : M) → TangentSpace 𝓘(ℝ, F) y) :
    mlieBracket 𝓘(ℝ, F) X Y x₀ =
      lieBracket ℝ (chartCoordinateField (I := 𝓘(ℝ, F)) x₀ X)
        (chartCoordinateField (I := 𝓘(ℝ, F)) x₀ Y) (extChartAt 𝓘(ℝ, F) x₀ x₀) := by
  rw [← mlieBracketWithin_univ, mlieBracketWithin_apply, mfderiv_extChartAt_self,
    ContinuousLinearMap.inverse_id]
  simp only [preimage_univ, univ_inter]
  change lieBracketWithin ℝ (chartCoordinateField (I := 𝓘(ℝ, F)) x₀ X)
    (chartCoordinateField (I := 𝓘(ℝ, F)) x₀ Y) (range 𝓘(ℝ, F)) _ = _
  rw [ModelWithCorners.Boundaryless.range_eq_univ, lieBracketWithin_univ]


open CutoffRigidity in
theorem mvfderiv_dphi_field {φ : M → ℝ} {B : (y : M) → TangentSpace 𝓘(ℝ, F) y} {x : M}
    (hφ : ContMDiffAt 𝓘(ℝ, F) 𝓘(ℝ, ℝ) ∞ φ x) (hB : SmAt F B x) (v : F) :
    mvfderiv 𝓘(ℝ, F) (fun y => mvfderiv 𝓘(ℝ, F) φ y (B y)) x v =
      fderiv ℝ (fderiv ℝ (φ ∘ (extChartAt 𝓘(ℝ, F) x).symm)) (extChartAt 𝓘(ℝ, F) x x) v
          (chartCoordinateField (I := 𝓘(ℝ, F)) x B (extChartAt 𝓘(ℝ, F) x x))
        + fderiv ℝ (φ ∘ (extChartAt 𝓘(ℝ, F) x).symm) (extChartAt 𝓘(ℝ, F) x x)
          (fderiv ℝ (chartCoordinateField (I := 𝓘(ℝ, F)) x B) (extChartAt 𝓘(ℝ, F) x x) v) := by
  set e := extChartAt 𝓘(ℝ, F) x with he
  set z0 := e x with hz0
  have hsymm : ContMDiffAt 𝓘(ℝ, F) 𝓘(ℝ, F) ∞ e.symm z0 :=
    (contMDiffOn_extChartAt_symm x).contMDiffAt (WReg.extChartAt_target_mem_nhds x)
  have hφ2 : ContDiffAt ℝ 2 (φ ∘ e.symm) z0 :=
    ((hφ.of_le (by norm_num)).comp_of_eq (hsymm.of_le (by norm_num)) (extChartAt_to_inv x)).contDiffAt
  -- the chart expression of `B`
  have hB' : ContDiffAt ℝ ∞ (chartCoordinateField (I := 𝓘(ℝ, F)) x B) z0 := by
    have h1 : ContMDiffAt 𝓘(ℝ, F) 𝓘(ℝ, F) ∞ (fun z => WReg.coord x B (e.symm z)) z0 :=
      (WReg.contMDiffAt_coord (x₀ := x) (y := x) (mem_chart_source F x) hB).comp_of_eq hsymm
        (extChartAt_to_inv x)
    refine h1.contDiffAt.congr_of_eventuallyEq ?_
    filter_upwards [WReg.extChartAt_target_mem_nhds x] with z hz
    exact chartCoordinateField_eq_coord F x hz
  -- eventual differentiability of `φ`
  have hev : ∀ᶠ z in 𝓝 z0, ContMDiffAt 𝓘(ℝ, F) 𝓘(ℝ, ℝ) 2 φ (e.symm z) := by
    have h1 : ∀ᶠ y in 𝓝 x, ContMDiffAt 𝓘(ℝ, F) 𝓘(ℝ, ℝ) 2 φ y :=
      (contMDiffAt_iff_contMDiffAt_nhds (by simp)).1 (hφ.of_le (by norm_num : (2 : ℕ∞ω) ≤ ∞))
    have h2 : ∀ᶠ y in 𝓝 (e.symm z0), ContMDiffAt 𝓘(ℝ, F) 𝓘(ℝ, ℝ) 2 φ y := by
      rw [he, hz0, extChartAt_to_inv]; exact h1
    exact (continuousAt_extChartAt_symm x).eventually h2
  set k : F → ℝ := fun z => fderiv ℝ (φ ∘ e.symm) z (chartCoordinateField (I := 𝓘(ℝ, F)) x B z)
    with hk
  have hkeq : ∀ᶠ z in 𝓝 z0, k z = mvfderiv 𝓘(ℝ, F) φ (e.symm z) (B (e.symm z)) := by
    filter_upwards [WReg.extChartAt_target_mem_nhds x, hev] with z hz hφz
    have hf : MDifferentiableAt 𝓘(ℝ, F) 𝓘(ℝ, ℝ) φ (e.symm z) :=
      hφz.mdifferentiableAt (by norm_num)
    have := fderiv_chartScalar_frame (I := 𝓘(ℝ, F)) x hz hf
      (chartCoordinateField (I := 𝓘(ℝ, F)) x B z)
    rw [chartFrame_chartCoordinateField x hz B] at this
    exact this
  have hkd : DifferentiableAt ℝ k z0 := by
    have h1 : DifferentiableAt ℝ (fderiv ℝ (φ ∘ e.symm)) z0 :=
      (hφ2.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
    exact h1.clm_apply (hB'.differentiableAt (by simp))
  have hkd' : fderiv ℝ k z0 v =
      fderiv ℝ (fderiv ℝ (φ ∘ e.symm)) z0 v (chartCoordinateField (I := 𝓘(ℝ, F)) x B z0)
        + fderiv ℝ (φ ∘ e.symm) z0
          (fderiv ℝ (chartCoordinateField (I := 𝓘(ℝ, F)) x B) z0 v) := by
    have h1 : DifferentiableAt ℝ (fderiv ℝ (φ ∘ e.symm)) z0 :=
      (hφ2.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
    rw [hk, fderiv_clm_apply h1 (hB'.differentiableAt (by simp))]
    simp
    ring
  -- g
  set g : M → ℝ := fun y => mvfderiv 𝓘(ℝ, F) φ y (B y) with hg
  have hgk : g =ᶠ[𝓝 x] fun y => k (e y) := by
    have h1 : ∀ᶠ y in 𝓝 x, k (e y) = mvfderiv 𝓘(ℝ, F) φ (e.symm (e y)) (B (e.symm (e y))) :=
      (continuousAt_extChartAt x).eventually (by rw [← hz0]; exact hkeq)
    filter_upwards [h1, chart_source_mem_nhds F x] with y hy hys
    have hys' : y ∈ e.source := by simpa only [he, extChartAt_source] using hys
    rw [hy, e.left_inv hys']
  have hkM : MDifferentiableAt 𝓘(ℝ, F) 𝓘(ℝ, ℝ) (fun y => k (e y)) x := by
    have h1 : MDifferentiableAt 𝓘(ℝ, F) 𝓘(ℝ, ℝ) k z0 := hkd.mdifferentiableAt
    exact h1.comp x (mdifferentiableAt_extChartAt (I := 𝓘(ℝ, F)) (mem_chart_source F x))
  have hgM : MDifferentiableAt 𝓘(ℝ, F) 𝓘(ℝ, ℝ) g x := hkM.congr_of_eventuallyEq hgk
  have h2 := fderiv_chart_vec F x hgM v
  have h3 : (g ∘ e.symm) =ᶠ[𝓝 z0] k := by
    filter_upwards [WReg.extChartAt_target_mem_nhds x, hkeq] with z hz hz2
    simp only [Function.comp, hg]
    exact hz2.symm
  rw [← h2, h3.fderiv_eq, hkd']

open CutoffRigidity in
theorem mvfderiv_mlieBracket {φ : M → ℝ} {X Y : (y : M) → TangentSpace 𝓘(ℝ, F) y} {x : M}
    (hφ : ContMDiffAt 𝓘(ℝ, F) 𝓘(ℝ, ℝ) ∞ φ x) (hX : SmAt F X x) (hY : SmAt F Y x) :
    mvfderiv 𝓘(ℝ, F) φ x (mlieBracket 𝓘(ℝ, F) X Y x) =
      mvfderiv 𝓘(ℝ, F) (fun y => mvfderiv 𝓘(ℝ, F) φ y (Y y)) x (X x)
        - mvfderiv 𝓘(ℝ, F) (fun y => mvfderiv 𝓘(ℝ, F) φ y (X y)) x (Y x) := by
  set e := extChartAt 𝓘(ℝ, F) x with he
  set z0 := e x with hz0
  have hsymm : ContMDiffAt 𝓘(ℝ, F) 𝓘(ℝ, F) ∞ e.symm z0 :=
    (contMDiffOn_extChartAt_symm x).contMDiffAt (WReg.extChartAt_target_mem_nhds x)
  have hφ2 : ContDiffAt ℝ 2 (φ ∘ e.symm) z0 :=
    ((hφ.of_le (by norm_num)).comp_of_eq (hsymm.of_le (by norm_num)) (extChartAt_to_inv x)).contDiffAt
  have hsy := hφ2.isSymmSndFDerivAt (by simp)
  have hφM : MDifferentiableAt 𝓘(ℝ, F) 𝓘(ℝ, ℝ) φ x := hφ.mdifferentiableAt (by simp)
  have hX0 : chartCoordinateField (I := 𝓘(ℝ, F)) x X z0 = X x := chartCoordinateField_self x X
  have hY0 : chartCoordinateField (I := 𝓘(ℝ, F)) x Y z0 = Y x := chartCoordinateField_self x Y
  have hcoord : ∀ {B : (y : M) → TangentSpace 𝓘(ℝ, F) y}, SmAt F B x →
      DifferentiableAt ℝ (chartCoordinateField (I := 𝓘(ℝ, F)) x B) z0 := by
    intro B hB
    have h1 : ContMDiffAt 𝓘(ℝ, F) 𝓘(ℝ, F) ∞ (fun z => WReg.coord x B (e.symm z)) z0 :=
      (WReg.contMDiffAt_coord (x₀ := x) (y := x) (mem_chart_source F x) hB).comp_of_eq hsymm
        (extChartAt_to_inv x)
    refine (h1.contDiffAt.congr_of_eventuallyEq ?_).differentiableAt (by simp)
    filter_upwards [WReg.extChartAt_target_mem_nhds x] with z hz
    exact chartCoordinateField_eq_coord F x hz
  rw [mlieBracket_center, ← fderiv_chart_vec F x hφM,
    mvfderiv_dphi_field F hφ hY, mvfderiv_dphi_field F hφ hX, lieBracket_eq]
  simp only [← he, ← hz0] at *
  rw [map_sub, hX0, hY0]
  have := hsy (X x) (Y x)
  rw [this]
  ring

theorem hessian_symm {φ : M → ℝ} (hφ : MSmooth F φ) (x : M) (v w : TangentSpace 𝓘(ℝ, F) x) :
    inner ℝ (CovariantDerivative.leviCivitaConnection 𝓘(ℝ, F) M (mgrad F φ) x v) w =
      inner ℝ (CovariantDerivative.leviCivitaConnection 𝓘(ℝ, F) M (mgrad F φ) x w) v := by
  set X : (y : M) → TangentSpace 𝓘(ℝ, F) y := FiberBundle.extend F v with hXdef
  set Y : (y : M) → TangentSpace 𝓘(ℝ, F) y := FiberBundle.extend F w with hYdef
  have hX : SmAt F X x := FiberBundle.contMDiffAt_extend (k := ∞) 𝓘(ℝ, F) F v
  have hY : SmAt F Y x := FiberBundle.contMDiffAt_extend (k := ∞) 𝓘(ℝ, F) F w
  have hXx : X x = v := FiberBundle.extend_apply_self F v
  have hYx : Y x = w := FiberBundle.extend_apply_self F w
  have h1 := hessian_eq_fields F hφ hX hY
  have h2 := hessian_eq_fields F hφ hY hX
  have hbr := mvfderiv_mlieBracket F (hφ x) hX hY
  have htor := (CovariantDerivative.torsion_eq_zero_iff
    (cov := CovariantDerivative.leviCivitaConnection 𝓘(ℝ, F) M)).1
    (CovariantDerivative.torsion_leviCivitaConnection_eq_zero 𝓘(ℝ, F)) (x := x)
    (hX.mdifferentiableAt (by simp)) (hY.mdifferentiableAt (by simp))
  rw [hXx, hYx] at h1 h2 hbr
  rw [hXx, hYx] at htor
  rw [h1, h2]
  have h3 : mvfderiv 𝓘(ℝ, F) φ x
      (CovariantDerivative.leviCivitaConnection 𝓘(ℝ, F) M Y x v -
        CovariantDerivative.leviCivitaConnection 𝓘(ℝ, F) M X x w) =
      mvfderiv 𝓘(ℝ, F) φ x (mlieBracket 𝓘(ℝ, F) X Y x) := by rw [htor]
  rw [hbr, map_sub] at h3
  linarith

end CutCur.WBoch
