module

public import CutoffRigidity.Riemann.WeightedBochnerDefs
public import CutoffRigidity.Riemann.WeightedRegularChart

/-! # G2: smoothness of the Levi-Civita derivative of smooth fields (`nabSmooth`)

Koszul formula in the chart frame + inverse of the chart metric.
-/

@[expose] public section
open Bundle Filter Set VectorField
open scoped Manifold ContDiff Topology
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

namespace CutCur.WBoch

open CutCur.WReg CutoffRigidity

section NabSmooth

variable {F : Type} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  {M : Type} [EMetricSpace M] [ChartedSpace F M] [IsManifold 𝓘(ℝ, F) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, F) ∞ F (fun x : M => TangentSpace 𝓘(ℝ, F) x)]

/-- A scalar function smooth at `x` is differentiable near `x`. -/
theorem eventually_mdiff_scalar {g : M → ℝ} {x : M}
    (hg : ContMDiffAt 𝓘(ℝ, F) 𝓘(ℝ, ℝ) ∞ g x) :
    ∀ᶠ y in 𝓝 x, MDifferentiableAt 𝓘(ℝ, F) 𝓘(ℝ, ℝ) g y := by
  have h1 : ContMDiffAt 𝓘(ℝ, F) 𝓘(ℝ, ℝ) 1 g x := hg.of_le (by simp)
  have := (contMDiffAt_iff_contMDiffAt_nhds (by simp)).mp h1
  exact this.mono fun y hy => hy.mdifferentiableAt (by simp)

/-- A section smooth at `x` is differentiable near `x`. -/
theorem eventually_mdiff_section {X : (y : M) → TangentSpace 𝓘(ℝ, F) y} {x : M}
    (hX : SmAt F X x) :
    ∀ᶠ y in 𝓝 x, MDifferentiableAt 𝓘(ℝ, F) 𝓘(ℝ, F).tangent (T% X) y := by
  have h1 : ContMDiffAt 𝓘(ℝ, F) 𝓘(ℝ, F).tangent 1 (T% X) x := hX.of_le (by simp)
  have := (contMDiffAt_iff_contMDiffAt_nhds (by simp)).mp h1
  exact this.mono fun y hy => hy.mdifferentiableAt (by simp)

/-- `y ↦ dφ_y (X y)` is smooth at `x` for `φ` and `X` smooth at `x`. -/
theorem contMDiffAt_mvfderiv_field {x₀ : M} {g : M → ℝ}
    (hg : ContMDiffAt 𝓘(ℝ, F) 𝓘(ℝ, ℝ) ∞ g x₀)
    {X : (y : M) → TangentSpace 𝓘(ℝ, F) y} (hX : SmAt F X x₀) :
    ContMDiffAt 𝓘(ℝ, F) 𝓘(ℝ, ℝ) ∞ (fun y => mvfderiv 𝓘(ℝ, F) g y (X y)) x₀ := by
  let e := extChartAt 𝓘(ℝ, F) x₀
  have hG : ContDiffAt ℝ ∞ (g ∘ e.symm) (e x₀) :=
    (hg.comp_of_eq ((contMDiffOn_extChartAt_symm x₀).contMDiffAt
      (WReg.extChartAt_target_mem_nhds x₀)) (extChartAt_to_inv x₀)).contDiffAt
  have hD : ContDiffAt ℝ ∞ (fderiv ℝ (g ∘ e.symm)) (e x₀) := hG.fderiv_right (m := ∞) (by simp)
  have hW : ContMDiffAt 𝓘(ℝ, F) 𝓘(ℝ, F) ∞ (coord x₀ X) x₀ :=
    contMDiffAt_coord (mem_chart_source F x₀) hX
  have h1 : ContMDiffAt 𝓘(ℝ, F) 𝓘(ℝ, ℝ) ∞
      (fun y => fderiv ℝ (g ∘ e.symm) (e y) (coord x₀ X y)) x₀ :=
    (hD.contMDiffAt.comp x₀ (contMDiffAt_extChartAt (I := 𝓘(ℝ, F)) (x := x₀) (n := ∞))).clm_apply hW
  apply h1.congr_of_eventuallyEq
  filter_upwards [chart_source_mem_nhds F x₀, eventually_mdiff_scalar hg] with y hy hgy
  have hys : y ∈ e.source := by simpa only [e, extChartAt_source] using hy
  have hz : e y ∈ e.target := e.map_source hys
  have hfy : MDifferentiableAt 𝓘(ℝ, F) 𝓘(ℝ, ℝ) g (e.symm (e y)) := by
    simpa only [e.left_inv hys] using hgy
  have := fderiv_chartScalar_frame (I := 𝓘(ℝ, F)) x₀ hz hfy (coord x₀ X y)
  rw [e.left_inv hys] at this
  rw [chartFrame_coord hy X] at this
  exact this.symm

/-- Criterion: a section is smooth at `x` if its inner products with the chart frame are. -/
theorem smAt_of_inner_frame {N : (y : M) → TangentSpace 𝓘(ℝ, F) y} {x : M}
    (h : ∀ w : F, ContMDiffAt 𝓘(ℝ, F) 𝓘(ℝ, ℝ) ∞
      (fun y => inner ℝ (N y) (chartFrame (I := 𝓘(ℝ, F)) x w y)) x) :
    SmAt F N x := by
  let e := extChartAt 𝓘(ℝ, F) x
  have hsymm : ContMDiffAt 𝓘(ℝ, F) 𝓘(ℝ, F) ∞ e.symm (e x) :=
    (contMDiffOn_extChartAt_symm x).contMDiffAt (WReg.extChartAt_target_mem_nhds x)
  let Λ : F → (F →L[ℝ] ℝ) := fun z =>
    (innerSL ℝ (E := TangentSpace 𝓘(ℝ, F) (e.symm z)) (N (e.symm z))).comp
      (chartFrameCLM (I := 𝓘(ℝ, F)) x (e.symm z))
  have hΛ : ContDiffAt ℝ ∞ Λ (e x) := by
    rw [← contDiffWithinAt_univ]
    apply contDiffWithinAt_clm_apply.mpr
    intro w
    have hk := (h w).comp_of_eq hsymm (extChartAt_to_inv x)
    exact hk.contDiffAt.contDiffWithinAt (s := univ)
  have hg : ContDiffAt ℝ ∞ (fun z => (chartMetric (I := 𝓘(ℝ, F)) x z).inverse (Λ z)) (e x) :=
    (WReg.contDiffAt_chartMetric_inverse x).clm_apply hΛ
  have hc : ContMDiffAt 𝓘(ℝ, F) 𝓘(ℝ, F) ∞
      (fun y => (chartMetric (I := 𝓘(ℝ, F)) x (e y)).inverse (Λ (e y))) x :=
    hg.contMDiffAt.comp x (contMDiffAt_extChartAt (I := 𝓘(ℝ, F)) (x := x) (n := ∞))
  have hcoord : ∀ y ∈ (chartAt F x).source,
      coord x N y = (chartMetric (I := 𝓘(ℝ, F)) x (e y)).inverse (Λ (e y)) := by
    intro y hy
    have hys : y ∈ e.source := by simpa only [e, extChartAt_source] using hy
    have hz : e y ∈ e.target := e.map_source hys
    symm
    apply (chartMetric_isInvertible_of_mem_target (I := 𝓘(ℝ, F)) x hz).inverse_apply_eq.mpr
    ext w
    rw [chartMetric_apply]
    have hl : (extChartAt 𝓘(ℝ, F) x).symm (e y) = y := e.left_inv hys
    change inner ℝ (N (e.symm (e y))) (chartFrame (I := 𝓘(ℝ, F)) x w (e.symm (e y))) =
      inner ℝ (chartFrame (I := 𝓘(ℝ, F)) x (coord x N y) ((extChartAt 𝓘(ℝ, F) x).symm (e y)))
        (chartFrame (I := 𝓘(ℝ, F)) x w ((extChartAt 𝓘(ℝ, F) x).symm (e y)))
    rw [hl, chartFrame_coord hy N]
  have hcoordc : ContMDiffAt 𝓘(ℝ, F) 𝓘(ℝ, F) ∞ (coord x N) x := by
    apply hc.congr_of_eventuallyEq
    filter_upwards [chart_source_mem_nhds F x] with y hy
    exact hcoord y hy
  have := contMDiffAt_section_of_coord (x₀ := x) (mem_chart_source F x) hcoordc
  unfold SmAt
  apply this.congr_of_eventuallyEq
  filter_upwards [chart_source_mem_nhds F x] with y hy
  exact congrArg (fun v => (⟨y, v⟩ : TangentBundle 𝓘(ℝ, F) M)) (chartFrame_coord hy N).symm

/-- Smoothness of the Koszul expression for `⟪∇_X Y, E_w⟫`. -/
theorem contMDiffAt_inner_nab_frame {X Y : (y : M) → TangentSpace 𝓘(ℝ, F) y} {x : M}
    (hX : SmAt F X x) (hY : SmAt F Y x) (w : F) :
    ContMDiffAt 𝓘(ℝ, F) 𝓘(ℝ, ℝ) ∞
      (fun y => inner ℝ (nab F X Y y) (chartFrame (I := 𝓘(ℝ, F)) x w y)) x := by
  set Z : (y : M) → TangentSpace 𝓘(ℝ, F) y := chartFrame (I := 𝓘(ℝ, F)) x w with hZdef
  have hZ : SmAt F Z x := contMDiffAt_chartFrame' (mem_chart_source F x) w
  have inn : ∀ {A B : (y : M) → TangentSpace 𝓘(ℝ, F) y}, SmAt F A x → SmAt F B x →
      ContMDiffAt 𝓘(ℝ, F) 𝓘(ℝ, ℝ) ∞ (fun y' => inner ℝ (A y') (B y')) x :=
    fun hA hB => ContMDiffAt.inner_bundle (E := TangentSpace 𝓘(ℝ, F)) hA hB
  have : IsManifold 𝓘(ℝ, F) (minSmoothness ℝ 2) M :=
    IsManifold.of_le (n := ∞) (by simp)
  have h1 : ((∞ : ℕ∞ω) + 1) = ∞ := by
    rfl
  have : IsManifold 𝓘(ℝ, F) (∞ + 1) M := by
    rw [h1]; infer_instance
  have br : ∀ {A B : (y : M) → TangentSpace 𝓘(ℝ, F) y}, SmAt F A x → SmAt F B x →
      SmAt F (VectorField.mlieBracket 𝓘(ℝ, F) A B) x :=
    fun hA hB => ContMDiffAt.mlieBracket_vectorField (m := ⊤) (n := ⊤) hA hB (by simp)
  have key : (fun y => inner ℝ (nab F X Y y) (Z y)) =ᶠ[𝓝 x] fun y =>
      (mvfderiv 𝓘(ℝ, F) (fun v => inner ℝ (Y v) (Z v)) y (X y)
        + mvfderiv 𝓘(ℝ, F) (fun v => inner ℝ (Z v) (X v)) y (Y y)
        - mvfderiv 𝓘(ℝ, F) (fun v => inner ℝ (X v) (Y v)) y (Z y)
        - inner ℝ (Y y) (VectorField.mlieBracket 𝓘(ℝ, F) X Z y)
        - inner ℝ (Z y) (VectorField.mlieBracket 𝓘(ℝ, F) Y X y)
        + inner ℝ (X y) (VectorField.mlieBracket 𝓘(ℝ, F) Z Y y)) / 2 := by
    filter_upwards [chart_source_mem_nhds F x, eventually_mdiff_section hX,
      eventually_mdiff_section hY] with y hy hXy hYy
    exact CovariantDerivative.leviCivitaConnection_apply_inner 𝓘(ℝ, F) hXy hYy
      ((contMDiffAt_chartFrame' hy w).mdifferentiableAt (by simp))
  refine ContMDiffAt.congr_of_eventuallyEq ?_ key
  simp only [div_eq_mul_inv]
  refine ContMDiffAt.mul ?_ contMDiffAt_const
  refine ContMDiffAt.add (ContMDiffAt.sub (ContMDiffAt.sub (ContMDiffAt.sub
    (ContMDiffAt.add ?_ ?_) ?_) ?_) ?_) ?_
  · exact contMDiffAt_mvfderiv_field (inn hY hZ) hX
  · exact contMDiffAt_mvfderiv_field (inn hZ hX) hY
  · exact contMDiffAt_mvfderiv_field (inn hX hY) hZ
  · exact inn hY (br hX hZ)
  · exact inn hZ (br hY hX)
  · exact inn hX (br hZ hY)

theorem nabSmooth : NabSmooth F M := by
  intro X Y x hX hY
  exact smAt_of_inner_frame (fun w => contMDiffAt_inner_nab_frame hX hY w)

end NabSmooth

end CutCur.WBoch
