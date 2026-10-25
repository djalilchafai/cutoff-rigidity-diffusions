module

public import CutoffRigidity.Riemann.DiffReg1

/-! # Regularity bootstrap, part 2: chart-wise `H^m_loc` regularity and gluing (workstream KER-REG)

* `ChartLocSob F m v`: `v ∘ φ_{x₀}⁻¹ ∈ H^m_loc(target)` for all charts.
* `chartLocSob_zero`: every `L²(μ)` function is `ChartLocSob 0`.
* `chartLocSob_step`: `u ∈ Q`, `E(u,φ) + λ⟪u,φ⟫ = ⟪g,φ⟫` and `ChartLocSob m g` give `ChartLocSob (m+2) u`.
* `exists_smooth_of_chartLocSob`: `ChartLocSob m v` for all `m` gives a smooth representative.
-/

@[expose] public section

open Bundle MeasureTheory Filter Set Topology
open scoped ContDiff ENNReal Manifold

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace CutoffRigidity.Riemann.Diff

open CutCur

section ChartSob

variable (F : Type) [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]
  {M : Type} [EMetricSpace M] [ChartedSpace F M] [IsManifold 𝓘(ℝ, F) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, F) ∞ F (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [MeasurableSpace M] [BorelSpace M]
  [IsRiemannianManifold 𝓘(ℝ, F) M] [ConnectedSpace M] [CompleteSpace M]
  {V : M → ℝ} (hV : MSmooth F V) {μ : Measure M} [IsFiniteMeasure μ]
  (hμ : IsWeightedVolume F μ V)

/-- `v` is `H^m_loc` in every chart. -/
def ChartLocSob (m : ℕ) (v : M → ℝ) : Prop :=
  ∀ x₀ : M, LocSob (stdOrthonormalBasis ℝ F) (chartAt F x₀).target m
    (fun z => v ((chartAt F x₀).symm z))

theorem ChartLocSob.mono {m m' : ℕ} (h : m ≤ m') {v : M → ℝ} (hv : ChartLocSob F m' v) :
    ChartLocSob F m v := fun x₀ => LocSob.mono _ h (hv x₀)

include hV hμ in
theorem locL2_chart (g : M →₂[μ] ℝ) (x₀ : M) :
    LocL2 (chartAt F x₀).target (fun z => (g : M → ℝ) ((chartAt F x₀).symm z)) := by
  intro K hK hKT
  have hgm : StronglyMeasurable (g : M → ℝ) := Lp.stronglyMeasurable g
  have hint : Integrable (fun x => (g : M → ℝ) x ^ 2) μ :=
    (memLp_two_iff_integrable_sq (Lp.memLp g).aestronglyMeasurable).1 (Lp.memLp g)
  have hTm : MeasurableSet (chartAt F x₀).target := (chartAt F x₀).open_target.measurableSet
  have hmeas : AEMeasurable (fun z => (g : M → ℝ) ((chartAt F x₀).symm z))
      (volume.restrict (chartAt F x₀).target) :=
    hgm.measurable.comp_aemeasurable ((chartAt F x₀).continuousOn_symm.aemeasurable hTm)
  haveI := isFiniteMeasure_chartNu F hV hμ x₀
  have hmeasν : AEStronglyMeasurable (fun z => (g : M → ℝ) ((chartAt F x₀).symm z))
      (chartNu F V x₀) :=
    (hmeas.mono_ac (withDensity_absolutelyContinuous _ _)).aestronglyMeasurable
  have hν : MemLp (fun z => (g : M → ℝ) ((chartAt F x₀).symm z)) 2 (chartNu F V x₀) := by
    rw [memLp_two_iff_integrable_sq hmeasν]
    refine ⟨(hmeasν.pow 2), ?_⟩
    have h1 := lintegral_chartNu_comp F hV hμ x₀ (fun x => ‖(g : M → ℝ) x ^ 2‖ₑ)
      (hgm.measurable.pow_const 2).enorm
    exact lt_of_le_of_lt h1 hint.2
  exact memLp_restrict_of_nu F hV x₀ hK hKT hν

include hV hμ in
theorem chartLocSob_zero (g : M →₂[μ] ℝ) : ChartLocSob F 0 (g : M → ℝ) := fun x₀ _ hχ =>
  memLp_mul_test (locL2_chart F hV hμ g x₀) hχ

variable (T : DirFriedrichs (diffFormData F hV hμ))

include hV hμ in
/-- **One regularity step on the manifold.** -/
theorem chartLocSob_step {u : M →₂[μ] ℝ} (hu : u ∈ T.Q) {lam : ℝ} (g : M →₂[μ] ℝ)
    (hweak : ∀ φ ∈ T.Q, T.E u φ + lam * inner ℝ u φ = inner ℝ g φ) (m : ℕ)
    (hg : ChartLocSob F m (g : M → ℝ)) : ChartLocSob F (m + 2) (u : M → ℝ) := by
  intro x₀
  obtain ⟨Du, hW, hE⟩ := chart_weak_equation F hV hμ x₀ T hu g (g : M → ℝ)
    (Lp.stronglyMeasurable g).measurable Filter.EventuallyEq.rfl hweak
  have hwg : IsWeakGradOn F (chartAt F x₀).target (fun z => (u : M → ℝ) ((chartAt F x₀).symm z)) Du :=
    ⟨fun K hK hKT => memLp_restrict_of_nu F hV x₀ hK hKT hW.memLp_u,
     fun K hK hKT => memLp_restrict_of_nu F hV x₀ hK hKT hW.memLp_Du, hW.weak⟩
  have hz' : ∀ z ∈ (chartAt F x₀).target, z ∈ (extChartAt 𝓘(ℝ, F) x₀).target := fun z hz => by
    rw [CutoffRigidity.extChartAt_target_eq]; exact hz
  exact regularity_step_Rn F (chartAt F x₀).open_target (contDiffOn_chartCoeff F x₀)
    (contDiffOn_chartRho F hV x₀)
    (fun z hz v w => chartCoeff_symm F x₀ (hz' z hz) v w)
    (fun z hz => exists_chartCoeff_elliptic F x₀ (hz' z hz))
    (fun z hz => chartRho_pos F V x₀ hz) (locL2_chart F hV hμ g x₀) hwg
    (fun ψ hψ hψc hψT => hE ψ hψ hψc hψT) m (hg x₀)

include hV hμ in
/-- Chart-wise smooth representatives glue to a global smooth representative. -/
theorem exists_smooth_of_chart_smooth (u : M →₂[μ] ℝ)
    (hloc : ∀ x₀ : M, ∃ ū : F → ℝ, ContDiffOn ℝ ∞ ū (chartAt F x₀).target ∧
      (fun z => (u : M → ℝ) ((chartAt F x₀).symm z)) =ᵐ[volume.restrict (chartAt F x₀).target] ū) :
    ∃ ū : M → ℝ, MSmooth F ū ∧ (u : M → ℝ) =ᵐ[μ] ū := by
  classical
  have hopen := isOpenPosMeasure_of_isWeightedVolume F hV hμ
  haveI := sigmaCompactSpace_of_complete_riemannian (F := F) (M := M)
  choose w hwsm hwae using hloc
  -- a.e. equality on each chart source
  have hae : ∀ x₀ : M, ∀ᵐ x ∂μ.restrict (chartAt F x₀).source,
      (u : M → ℝ) x = w x₀ (chartAt F x₀ x) := by
    intro x₀
    set φ := chartAt F x₀ with hφ
    have h1 := hwae x₀
    have hac : (μ.restrict φ.source).map φ ≪ volume.restrict φ.target := by
      rw [chart_map_eq F hμ x₀]; exact withDensity_absolutelyContinuous _ _
    have h2 : ∀ᵐ z ∂((μ.restrict φ.source).map φ), (u : M → ℝ) (φ.symm z) = w x₀ z :=
      hac.ae_le h1
    have h3 := ae_of_ae_map (φ.continuousOn.aemeasurable φ.open_source.measurableSet) h2
    filter_upwards [h3, ae_restrict_mem φ.open_source.measurableSet] with x hx hxS
    rw [← hx, φ.left_inv hxS]
  set ū : M → ℝ := fun x => w x (chartAt F x x) with hū
  have hmaps : ∀ x₀ : M, ContinuousOn (fun y => w x₀ (chartAt F x₀ y)) (chartAt F x₀).source :=
    fun x₀ => (hwsm x₀).continuousOn.comp (chartAt F x₀).continuousOn (chartAt F x₀).mapsTo
  have hcons : ∀ x₀ : M, EqOn ū (fun y => w x₀ (chartAt F x₀ y)) (chartAt F x₀).source := by
    intro x₀ y hy
    set W := (chartAt F x₀).source ∩ (chartAt F y).source with hW
    have hWo : IsOpen W := (chartAt F x₀).open_source.inter (chartAt F y).open_source
    have hyW : y ∈ W := ⟨hy, mem_chart_source F y⟩
    have hae1 : ∀ᵐ x ∂μ.restrict W, (u : M → ℝ) x = w x₀ (chartAt F x₀ x) :=
      ae_restrict_of_ae_restrict_of_subset inter_subset_left (hae x₀)
    have hae2 : ∀ᵐ x ∂μ.restrict W, (u : M → ℝ) x = w y (chartAt F y x) :=
      ae_restrict_of_ae_restrict_of_subset inter_subset_right (hae y)
    have hfg : (fun x => w x₀ (chartAt F x₀ x)) =ᵐ[μ.restrict W] fun x => w y (chartAt F y x) := by
      filter_upwards [hae1, hae2] with x h1 h2
      rw [← h1, ← h2]
    have := Measure.eqOn_open_of_ae_eq hfg hWo ((hmaps x₀).mono inter_subset_left)
      ((hmaps y).mono inter_subset_right) hyW
    exact this.symm
  have hsmooth : MSmooth F ū := by
    intro x₀
    have h1 : ContDiffAt ℝ ∞ (w x₀) (chartAt F x₀ x₀) :=
      (hwsm x₀).contDiffAt ((chartAt F x₀).open_target.mem_nhds (mem_chart_target F x₀))
    have h2 : ContMDiffAt 𝓘(ℝ, F) 𝓘(ℝ, F) ∞ (extChartAt 𝓘(ℝ, F) x₀) x₀ := contMDiffAt_extChartAt
    have h3 : ContMDiffAt 𝓘(ℝ, F) 𝓘(ℝ, ℝ) ∞ ((w x₀) ∘ (extChartAt 𝓘(ℝ, F) x₀)) x₀ :=
      h1.contMDiffAt.comp x₀ h2
    refine h3.congr_of_eventuallyEq ?_
    filter_upwards [(chartAt F x₀).open_source.mem_nhds (mem_chart_source F x₀)] with y hy
    exact hcons x₀ hy
  refine ⟨ū, hsmooth, ?_⟩
  obtain ⟨t, ht, hcov⟩ := countable_cover_nhds_of_sigmaCompact
    (f := fun x : M => (chartAt F x).source)
    (fun x => (chartAt F x).open_source.mem_nhds (mem_chart_source F x))
  have key : ∀ᵐ x ∂μ.restrict (⋃ x ∈ t, (chartAt F x).source), (u : M → ℝ) x = ū x := by
    rw [ae_restrict_biUnion_iff _ ht]
    intro x₀ _
    filter_upwards [hae x₀, ae_restrict_mem (chartAt F x₀).open_source.measurableSet] with x hx hxS
    rw [hx, hcons x₀ hxS]
  rw [hcov, Measure.restrict_univ] at key
  exact key


include hV hμ in
/-- If `u ∈ L²` is `H^m_loc` in every chart for all `m`, it has a smooth representative. -/
theorem exists_smooth_of_chartLocSob (u : M →₂[μ] ℝ)
    (h : ∀ m, ChartLocSob F m (u : M → ℝ)) :
    ∃ ū : M → ℝ, MSmooth F ū ∧ (u : M → ℝ) =ᵐ[μ] ū :=
  exists_smooth_of_chart_smooth F hV hμ u fun x₀ =>
    exists_smooth_global (stdOrthonormalBasis ℝ F) (chartAt F x₀).open_target fun m => h m x₀

end ChartSob

end CutoffRigidity.Riemann.Diff
