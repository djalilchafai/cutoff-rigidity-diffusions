module

public import CutoffRigidity.Riemann.DiffInstance2
public import CutoffRigidity.Riemann.DiffRellichRn

/-! # Zero extension of chart-supported test functions to `F` (workstream HPOS) -/

@[expose] public section

open Bundle MeasureTheory Filter Set
open scoped Manifold ContDiff ENNReal Topology

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace CutoffRigidity.Riemann.Diff

open CutCur

section Ext

variable (F : Type) [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]
  {M : Type} [EMetricSpace M] [ChartedSpace F M] [IsManifold 𝓘(ℝ, F) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, F) ∞ F (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [MeasurableSpace M] [BorelSpace M] (x₀ : M)

open Classical in
/-- The function `g ∘ φ⁻¹` on the chart target, extended by zero to `F`. -/
noncomputable def chartRestr (g : M → ℝ) : F → ℝ := fun z =>
  if z ∈ (chartAt F x₀).target then g ((chartAt F x₀).symm z) else 0

theorem chartRestr_of_mem {g : M → ℝ} {z : F} (hz : z ∈ (chartAt F x₀).target) :
    chartRestr F x₀ g z = g ((chartAt F x₀).symm z) := by
  simp [chartRestr, hz]

theorem chartRestr_of_notMem {g : M → ℝ} {z : F} (hz : z ∉ (chartAt F x₀).target) :
    chartRestr F x₀ g z = 0 := by
  simp [chartRestr, hz]

theorem chartRestr_sub (g g' : M → ℝ) :
    chartRestr F x₀ (fun x => g x - g' x) = fun z => chartRestr F x₀ g z - chartRestr F x₀ g' z := by
  funext z
  by_cases hz : z ∈ (chartAt F x₀).target
  · simp [chartRestr_of_mem F x₀ hz]
  · simp [chartRestr_of_notMem F x₀ hz]

variable {x₀} {K₀ : Set M}

theorem chartRestr_eq_zero' {g : M → ℝ} (hs : tsupport g ⊆ K₀)
    {z : F} (hz : z ∉ (chartAt F x₀) '' K₀) : chartRestr F x₀ g z = 0 := by
  by_cases hT : z ∈ (chartAt F x₀).target
  · rw [chartRestr_of_mem F x₀ hT]
    by_contra h
    refine hz ⟨_, hs (subset_tsupport _ h), (chartAt F x₀).right_inv hT⟩
  · exact chartRestr_of_notMem F x₀ hT

theorem contDiff_chartRestr {g : M → ℝ} (hg : MSmooth F g) (hs : tsupport g ⊆ K₀)
    (hK₀ : IsCompact K₀) (hsrc : K₀ ⊆ (chartAt F x₀).source) :
    ContDiff ℝ ∞ (chartRestr F x₀ g) := by
  have hKc : IsCompact ((chartAt F x₀) '' K₀) := hK₀.image_of_continuousOn
    ((chartAt F x₀).continuousOn.mono hsrc)
  rw [contDiff_iff_contDiffAt]
  intro z
  by_cases hz : z ∈ (chartAt F x₀).target
  · have h1 : ContDiffAt ℝ ∞ (g ∘ (chartAt F x₀).symm) z :=
      (contDiffOn_chartCoord F x₀ hg).contDiffAt ((chartAt F x₀).open_target.mem_nhds hz)
    refine h1.congr_of_eventuallyEq ?_
    filter_upwards [(chartAt F x₀).open_target.mem_nhds hz] with w hw
    exact chartRestr_of_mem F x₀ hw
  · have hzK : z ∉ (chartAt F x₀) '' K₀ := by
      rintro ⟨y, hy, rfl⟩
      exact hz ((chartAt F x₀).map_source (hsrc hy))
    refine (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq ?_
    filter_upwards [hKc.isClosed.isOpen_compl.mem_nhds hzK] with w hw
    exact chartRestr_eq_zero' F hs hw

theorem hasCompactSupport_chartRestr {g : M → ℝ} (hs : tsupport g ⊆ K₀)
    (hK₀ : IsCompact K₀) (hsrc : K₀ ⊆ (chartAt F x₀).source) :
    HasCompactSupport (chartRestr F x₀ g) :=
  HasCompactSupport.intro (hK₀.image_of_continuousOn ((chartAt F x₀).continuousOn.mono hsrc))
    fun _ hz => chartRestr_eq_zero' F hs hz

theorem gradient_chartRestr_of_mem {g : M → ℝ} {z : F} (hz : z ∈ (chartAt F x₀).target) :
    gradient (chartRestr F x₀ g) z = chartGrad F x₀ g z := by
  unfold gradient chartGrad
  have : chartRestr F x₀ g =ᶠ[𝓝 z] g ∘ (chartAt F x₀).symm := by
    filter_upwards [(chartAt F x₀).open_target.mem_nhds hz] with w hw
    exact chartRestr_of_mem F x₀ hw
  rw [this.fderiv_eq]
  rfl

theorem gradient_chartRestr_eq_zero {g : M → ℝ} (hs : tsupport g ⊆ K₀)
    (hK₀ : IsCompact K₀) (hsrc : K₀ ⊆ (chartAt F x₀).source) {z : F}
    (hz : z ∉ (chartAt F x₀) '' K₀) : gradient (chartRestr F x₀ g) z = 0 := by
  have hKc : IsCompact ((chartAt F x₀) '' K₀) := hK₀.image_of_continuousOn
    ((chartAt F x₀).continuousOn.mono hsrc)
  unfold gradient
  have : chartRestr F x₀ g =ᶠ[𝓝 z] fun _ => (0 : ℝ) := by
    filter_upwards [hKc.isClosed.isOpen_compl.mem_nhds hz] with w hw
    exact chartRestr_eq_zero' F hs hw
  rw [this.fderiv_eq]
  simp

end Ext

end CutoffRigidity.Riemann.Diff
