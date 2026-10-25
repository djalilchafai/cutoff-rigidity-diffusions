module

public import CutoffRigidity.Riemann.DiffChart5

/-! # From the chart weak equation to smoothness (workstream DIR)

`EllipticRegularityRn F` is the interior elliptic regularity statement in `F` supplied by workstream
REGn (`weak_solution_smooth`); it is taken as a hypothesis of the glueing theorem
`Q_smooth_of_weak_eq`, to be instantiated when REGn lands.  Given it, an element `u ∈ Q` of the
form domain solving `E(u,·) + λ⟪u,·⟫ = ⟪g,·⟫` with `g` smooth has a smooth representative.
-/

@[expose] public section

open Bundle MeasureTheory Filter Set
open scoped Manifold ContDiff ENNReal Topology

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace CutoffRigidity.Riemann.Diff

open CutCur

section Reg

variable (F : Type) [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]

/-- `Du` is a weak gradient of `u` on the open set `Ω` (Lebesgue measure; `u, Du ∈ L²_loc(Ω)`). -/
structure IsWeakGradOn (Ω : Set F) (u : F → ℝ) (Du : F → F) : Prop where
  memLp_u : ∀ K : Set F, IsCompact K → K ⊆ Ω → MemLp u 2 (volume.restrict K)
  memLp_Du : ∀ K : Set F, IsCompact K → K ⊆ Ω → MemLp Du 2 (volume.restrict K)
  weak : ∀ ψ : F → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → tsupport ψ ⊆ Ω →
    ∀ w : F, ∫ z, u z * fderiv ℝ ψ z w = -∫ z, inner ℝ (Du z) w * ψ z

/-- Interior elliptic regularity in `F` for divergence form operators with smooth coefficients
(statement expected from workstream REGn): a weak `H¹_loc` solution of
`-div(ϱ a ∇u) + λ ϱ u = ϱ g` with `g` smooth is smooth. -/
def EllipticRegularityRn : Prop :=
  ∀ (Ω : Set F), IsOpen Ω → ∀ (a : F → F →L[ℝ] F) (ϱ : F → ℝ) (lam : ℝ),
    ContDiffOn ℝ ∞ a Ω → ContDiffOn ℝ ∞ ϱ Ω →
    (∀ x ∈ Ω, ∀ v w : F, inner ℝ (a x v) w = inner ℝ v (a x w)) →
    (∀ x ∈ Ω, ∃ c > 0, ∀ v : F, c * ‖v‖ ^ 2 ≤ inner ℝ (a x v) v) →
    (∀ x ∈ Ω, 0 < ϱ x) → ∀ (u g : F → ℝ) (Du : F → F), ContDiffOn ℝ ∞ g Ω →
    IsWeakGradOn F Ω u Du →
    (∀ ψ : F → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → tsupport ψ ⊆ Ω →
      ∫ x in Ω, (inner ℝ (a x (Du x)) (gradient ψ x) + lam * u x * ψ x) * ϱ x =
        ∫ x in Ω, g x * ψ x * ϱ x) →
    ∃ ū : F → ℝ, ContDiffOn ℝ ∞ ū Ω ∧ u =ᵐ[volume.restrict Ω] ū

end Reg

section Glue

variable (F : Type) [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]
  {M : Type} [EMetricSpace M] [ChartedSpace F M] [IsManifold 𝓘(ℝ, F) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, F) ∞ F (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [MeasurableSpace M] [BorelSpace M]
  [IsRiemannianManifold 𝓘(ℝ, F) M] [ConnectedSpace M] [CompleteSpace M]
  {V : M → ℝ} (hV : MSmooth F V) {μ : Measure M} [IsFiniteMeasure μ]
  (hμ : IsWeightedVolume F μ V) (T : DirFriedrichs (diffFormData F hV hμ))

include hV hμ in
/-- In every chart a solution `u ∈ Q` of the weak equation with smooth right-hand side is
a.e. equal to a function smooth on the chart target. -/
theorem chart_regular (REG : EllipticRegularityRn F) {u : M →₂[μ] ℝ} (hu : u ∈ T.Q) {lam : ℝ}
    (g : M →₂[μ] ℝ) (g' : M → ℝ) (hg's : MSmooth F g')
    (hgg' : (g : M → ℝ) =ᵐ[μ] g')
    (hweak : ∀ φ ∈ T.Q, T.E u φ + lam * inner ℝ u φ = inner ℝ g φ) (x₀ : M) :
    ∃ ū : F → ℝ, ContDiffOn ℝ ∞ ū (chartAt F x₀).target ∧
      (fun z => (u : M → ℝ) ((chartAt F x₀).symm z)) =ᵐ[volume.restrict (chartAt F x₀).target] ū := by
  obtain ⟨Du, hW, hE⟩ := chart_weak_equation F hV hμ x₀ T hu g g' hg's.continuous.measurable hgg' hweak
  have hwg : IsWeakGradOn F (chartAt F x₀).target (fun z => (u : M → ℝ) ((chartAt F x₀).symm z)) Du :=
    ⟨fun K hK hKT => memLp_restrict_of_nu F hV x₀ hK hKT hW.memLp_u,
     fun K hK hKT => memLp_restrict_of_nu F hV x₀ hK hKT hW.memLp_Du, hW.weak⟩
  have hz' : ∀ z ∈ (chartAt F x₀).target, z ∈ (extChartAt 𝓘(ℝ, F) x₀).target := fun z hz => by
    rw [CutoffRigidity.extChartAt_target_eq]; exact hz
  refine REG _ (chartAt F x₀).open_target (chartCoeff F x₀) (chartRho F V x₀) lam
    (contDiffOn_chartCoeff F x₀) (contDiffOn_chartRho F hV x₀)
    (fun z hz v w => chartCoeff_symm F x₀ (hz' z hz) v w)
    (fun z hz => exists_chartCoeff_elliptic F x₀ (hz' z hz))
    (fun z hz => chartRho_pos F V x₀ hz) _ (fun z => g' ((chartAt F x₀).symm z))
    Du ?_ hwg ?_
  · exact contDiffOn_chartCoord F x₀ hg's
  · intro ψ hψ hψc hψT
    exact hE ψ hψ hψc hψT

include hV hμ in
/-- **Smoothness of the solution of the weak equation** (given interior elliptic regularity in
`F`): an element `u ∈ Q` with `E(u,φ) + λ⟪u,φ⟫ = ⟪g,φ⟫` for all `φ ∈ Q` (any real `λ`), and `g` a.e. equal
to a smooth function, has a smooth representative. -/
theorem Q_smooth_of_weak_eq (REG : EllipticRegularityRn F) {u : M →₂[μ] ℝ} (hu : u ∈ T.Q)
    {lam : ℝ} (g : M →₂[μ] ℝ) (g' : M → ℝ) (hg's : MSmooth F g')
    (hgg' : (g : M → ℝ) =ᵐ[μ] g')
    (hweak : ∀ φ ∈ T.Q, T.E u φ + lam * inner ℝ u φ = inner ℝ g φ) :
    ∃ ū : M → ℝ, MSmooth F ū ∧ (u : M → ℝ) =ᵐ[μ] ū := by
  classical
  have hopen := isOpenPosMeasure_of_isWeightedVolume F hV hμ
  haveI := sigmaCompactSpace_of_complete_riemannian (F := F) (M := M)
  choose w hwsm hwae using chart_regular F hV hμ T REG hu g g' hg's hgg' hweak
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

end Glue

end CutoffRigidity.Riemann.Diff
