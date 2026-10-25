module

public import CutoffRigidity.Riemann.DiffChart4

/-! # Chart transfer of the weak equation (workstream DIR)

`Q_chart_weak`: for `u ∈ Q` and a chart `chartAt F x₀`, `ũ = u ∘ φ⁻¹` has a weak gradient `Du`
(in `L²_loc(target)`), the energy pairs as `E(u, b) = ∫ ρ ⟪a Du, ∇ψ⟫`, and, if `u` solves
`E(u,·) + λ⟪u,·⟫ = ⟪g,·⟫` on `Q`, then in the chart
`∫ (⟪a Du, ∇ψ⟫ + λ ũ ψ) ρ = ∫ g̃ ψ ρ` for all `ψ ∈ C_c^∞(target)`.
-/

@[expose] public section

open Bundle MeasureTheory Filter Set
open scoped Manifold ContDiff ENNReal Topology

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace CutoffRigidity.Riemann.Diff

open CutCur

section Basic

variable (F : Type) [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]
  {M : Type} [EMetricSpace M] [ChartedSpace F M] [IsManifold 𝓘(ℝ, F) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, F) ∞ F (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [MeasurableSpace M] [BorelSpace M]
  {V : M → ℝ} (hV : MSmooth F V) {μ : Measure M}
  (hμ : IsWeightedVolume F μ V) (x₀ : M)

include hV hμ in
/-- **Change of variables for Bochner integrals.** -/
theorem integral_chart_comp (G : F → ℝ)
    (hG : AEStronglyMeasurable G (volume.restrict (chartAt F x₀).target)) :
    ∫ x in (chartAt F x₀).source, G ((chartAt F x₀) x) ∂μ =
      ∫ z in (chartAt F x₀).target, chartRho F V x₀ z * G z := by
  set φ := chartAt F x₀ with hφ
  have hTm : MeasurableSet φ.target := φ.open_target.measurableSet
  have hSm : MeasurableSet φ.source := φ.open_source.measurableSet
  have hmap := chart_map_eq F hμ x₀
  have hφm : AEMeasurable φ (μ.restrict φ.source) := φ.continuousOn.aemeasurable hSm
  have hG' : AEStronglyMeasurable G ((μ.restrict φ.source).map φ) := by
    rw [hmap]
    exact hG.mono_ac (withDensity_absolutelyContinuous _ _)
  rw [← integral_map hφm hG', hmap]
  rw [integral_withDensity_eq_integral_toReal_smul₀ (measurable_chartRho_aemeasurable F hV x₀)
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  refine setIntegral_congr_fun hTm fun z hz => ?_
  simp [ENNReal.toReal_ofReal (chartRho_pos F V x₀ hz).le]

end Basic

section Extend

variable (F : Type) [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]
  {M : Type} [EMetricSpace M] [ChartedSpace F M] [IsManifold 𝓘(ℝ, F) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, F) ∞ F (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [MeasurableSpace M] [BorelSpace M] (x₀ : M)

open Classical in
/-- Extension by zero to `M` of a function on the chart target. -/
noncomputable def chartExtend (ψ : F → ℝ) : M → ℝ := fun x =>
  if x ∈ (chartAt F x₀).source then ψ ((chartAt F x₀) x) else 0

theorem chartExtend_eq {ψ : F → ℝ} {x : M} (hx : x ∈ (chartAt F x₀).source) :
    chartExtend F x₀ ψ x = ψ ((chartAt F x₀) x) := by
  simp [chartExtend, hx]

theorem chartExtend_eq_zero {ψ : F → ℝ} {x : M} (hx : x ∉ (chartAt F x₀).source) :
    chartExtend F x₀ ψ x = 0 := by
  simp [chartExtend, hx]

theorem chartExtend_symm {ψ : F → ℝ} {z : F} (hz : z ∈ (chartAt F x₀).target) :
    chartExtend F x₀ ψ ((chartAt F x₀).symm z) = ψ z := by
  rw [chartExtend_eq F x₀ ((chartAt F x₀).map_target hz), (chartAt F x₀).right_inv hz]

theorem chartExtend_mem {ψ : F → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ)
    (hψT : tsupport ψ ⊆ (chartAt F x₀).target) :
    chartExtend F x₀ ψ ∈ testSub F M ∧ tsupport (chartExtend F x₀ ψ) ⊆ (chartAt F x₀).source := by
  set φ := chartAt F x₀ with hφ
  set K' := φ.symm '' tsupport ψ with hK'
  have hK'c : IsCompact K' := hψc.image_of_continuousOn (φ.continuousOn_symm.mono hψT)
  have hK'S : K' ⊆ φ.source := by
    rintro _ ⟨z, hz, rfl⟩; exact φ.map_target (hψT hz)
  have hzero : ∀ x, x ∉ K' → chartExtend F x₀ ψ x = 0 := by
    intro x hx
    by_cases hS : x ∈ φ.source
    · rw [chartExtend_eq F x₀ hS]
      by_contra hne
      apply hx
      refine ⟨φ x, subset_tsupport ψ hne, φ.left_inv hS⟩
    · exact chartExtend_eq_zero F x₀ hS
  have hsm : MSmooth F (chartExtend F x₀ ψ) := by
    intro x
    by_cases hS : x ∈ φ.source
    · have h1 : ContMDiffAt 𝓘(ℝ, F) 𝓘(ℝ, F) ∞ (extChartAt 𝓘(ℝ, F) x₀) x :=
        contMDiffAt_extChartAt' (by simpa using hS)
      have h2 : ContMDiffAt 𝓘(ℝ, F) 𝓘(ℝ, ℝ) ∞ (ψ ∘ (extChartAt 𝓘(ℝ, F) x₀)) x :=
        hψ.contMDiff.contMDiffAt.comp x h1
      refine h2.congr_of_eventuallyEq ?_
      filter_upwards [φ.open_source.mem_nhds hS] with y hy
      rw [chartExtend_eq F x₀ hy]
      rfl
    · have hxK : x ∉ K' := fun h => hS (hK'S h)
      have hev : chartExtend F x₀ ψ =ᶠ[𝓝 x] fun _ => (0 : ℝ) := by
        filter_upwards [hK'c.isClosed.isOpen_compl.mem_nhds hxK] with y hy
        exact hzero y hy
      exact (contMDiffAt_const).congr_of_eventuallyEq hev
  have hcs : HasCompactSupport (chartExtend F x₀ ψ) := by
    refine HasCompactSupport.intro hK'c hzero
  refine ⟨⟨hsm, hcs⟩, ?_⟩
  refine (closure_minimal ?_ hK'c.isClosed).trans hK'S
  intro x hx
  by_contra hxK
  exact hx (hzero x hxK)

end Extend

section Main

variable (F : Type) [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]
  {M : Type} [EMetricSpace M] [ChartedSpace F M] [IsManifold 𝓘(ℝ, F) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, F) ∞ F (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [MeasurableSpace M] [BorelSpace M]

/-- `Du` is a weak gradient of `ũ = u∘φ⁻¹` on the chart target: `ũ, Du ∈ L²(ν)` (hence in
`L²_loc` of the target, see `IsChartWeakGrad.memLp_restrict`) and
`∫ ũ ∂_wψ dz = - ∫ ⟪Du, w⟫ ψ dz` for `ψ ∈ C_c^∞(target)`. -/
structure IsChartWeakGrad (V : M → ℝ) (x₀ : M) (u : M → ℝ) (Du : F → F) : Prop where
  memLp_u : MemLp (fun z => u ((chartAt F x₀).symm z)) 2 (chartNu F V x₀)
  memLp_Du : MemLp Du 2 (chartNu F V x₀)
  weak : ∀ ψ : F → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → tsupport ψ ⊆ (chartAt F x₀).target →
    ∀ w : F, ∫ z, u ((chartAt F x₀).symm z) * fderiv ℝ ψ z w = -∫ z, inner ℝ (Du z) w * ψ z

variable {V : M → ℝ} (hV : MSmooth F V) {μ : Measure M} [IsFiniteMeasure μ]
  (hμ : IsWeightedVolume F μ V) (x₀ : M)

include hV in
/-- On a compact subset `K` of the target, `L²(ν) ⊆ L²(dz)`. -/
theorem memLp_restrict_of_nu {W : Type*} [NormedAddCommGroup W] {f : F → W} {K : Set F}
    (hK : IsCompact K) (hKT : K ⊆ (chartAt F x₀).target)
    (hf : MemLp f 2 (chartNu F V x₀)) : MemLp f 2 (volume.restrict K) := by
  rcases K.eq_empty_or_nonempty with rfl | hne
  · simp
  obtain ⟨z₀, hz₀, hmin⟩ := hK.exists_isMinOn hne
    ((continuousOn_chartKappa F hV x₀).mono hKT)
  have hc₀ : 0 < chartKappa F V x₀ z₀ := chartKappa_pos F V x₀ (hKT hz₀)
  refine MemLp.of_measure_le_smul (c := ENNReal.ofReal (chartKappa F V x₀ z₀)⁻¹) (by simp) ?_ hf
  rw [Measure.le_iff]
  intro s hs
  have hTm : MeasurableSet (chartAt F x₀).target := (chartAt F x₀).open_target.measurableSet
  rw [Measure.smul_apply, smul_eq_mul, Measure.restrict_apply hs]
  unfold chartNu
  rw [withDensity_apply _ hs]
  have h1 : ENNReal.ofReal (chartKappa F V x₀ z₀) * volume (s ∩ K) ≤
      ∫⁻ z in s, ENNReal.ofReal (chartKappa F V x₀ z) ∂(volume.restrict (chartAt F x₀).target) := by
    rw [Measure.restrict_restrict hs]
    calc ENNReal.ofReal (chartKappa F V x₀ z₀) * volume (s ∩ K)
        = ∫⁻ z in s ∩ K, ENNReal.ofReal (chartKappa F V x₀ z₀) ∂volume := by
          rw [setLIntegral_const]
      _ ≤ ∫⁻ z in s ∩ K, ENNReal.ofReal (chartKappa F V x₀ z) ∂volume := by
          refine setLIntegral_mono' (hs.inter hK.isClosed.measurableSet) fun z hz => ?_
          exact ENNReal.ofReal_le_ofReal (hmin hz.2)
      _ ≤ ∫⁻ z in s ∩ (chartAt F x₀).target, ENNReal.ofReal (chartKappa F V x₀ z) ∂volume := by
          refine lintegral_mono_set ?_
          exact inter_subset_inter_right _ hKT
  have h2 : volume (s ∩ K) ≤ ENNReal.ofReal (chartKappa F V x₀ z₀)⁻¹ *
      ∫⁻ z in s, ENNReal.ofReal (chartKappa F V x₀ z) ∂(volume.restrict (chartAt F x₀).target) := by
    calc volume (s ∩ K) = ENNReal.ofReal (chartKappa F V x₀ z₀)⁻¹ *
          (ENNReal.ofReal (chartKappa F V x₀ z₀) * volume (s ∩ K)) := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul (inv_nonneg.2 hc₀.le), inv_mul_cancel₀ hc₀.ne']
          simp
      _ ≤ _ := by gcongr
  exact h2

end Main

section Weak

variable (F : Type) [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]
  {M : Type} [EMetricSpace M] [ChartedSpace F M] [IsManifold 𝓘(ℝ, F) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, F) ∞ F (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [MeasurableSpace M] [BorelSpace M]
  [IsRiemannianManifold 𝓘(ℝ, F) M] [ConnectedSpace M] [CompleteSpace M]
  {V : M → ℝ} (hV : MSmooth F V) {μ : Measure M} [IsFiniteMeasure μ]
  (hμ : IsWeightedVolume F μ V) (x₀ : M) (T : DirFriedrichs (diffFormData F hV hμ))

include hV hμ in
/-- **Chart transfer of an element of the form domain.**  For `u ∈ Q` the coordinate expression
`ũ = u∘φ⁻¹` has a weak gradient `Du ∈ L²(ν)`, and the energy pairs with test functions supported in
the chart as `E(u,b) = ∫_T ρ ⟪∇(b∘φ⁻¹), a Du⟫ dz`. -/
theorem Q_chart_weak {u : M →₂[μ] ℝ} (hu : u ∈ T.Q) :
    ∃ Du : F → F, IsChartWeakGrad F V x₀ (u : M → ℝ) Du ∧
      ∀ b : testSub F M, tsupport (b : M → ℝ) ⊆ (chartAt F x₀).source →
        T.E u (testToL2 F μ b) =
          ∫ z in (chartAt F x₀).target, chartRho F V x₀ z *
            inner ℝ (chartGrad F x₀ (b : M → ℝ) z) (chartCoeff F x₀ z (Du z)) := by
  obtain ⟨a, Ĝ, hconv, hcau, hG, hs⟩ := exists_gradient_limit F hV hμ x₀ T hu
  refine ⟨fun z => Ĝ z, ⟨?_, Lp.memLp Ĝ, ?_⟩, fun b hb =>
    energy_pairing_of_limit F hV hμ x₀ T a Ĝ hconv hcau hG b hb⟩
  · exact memLp_chartPull F hV hμ x₀ (Lp.stronglyMeasurable u).measurable (Lp.memLp u)
  · intro ψ hψ hψc hψT w
    exact weak_gradient_identity_of_limit F hV hμ x₀ a Ĝ hG hs hψ hψc hψT w

end Weak

section WeakEq

variable (F : Type) [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]
  {M : Type} [EMetricSpace M] [ChartedSpace F M] [IsManifold 𝓘(ℝ, F) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, F) ∞ F (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [MeasurableSpace M] [BorelSpace M]
  {V : M → ℝ} (hV : MSmooth F V) {μ : Measure M}
  (hμ : IsWeightedVolume F μ V) (x₀ : M)

theorem integrable_inner_memLp {α W : Type*} [MeasurableSpace α] [NormedAddCommGroup W]
    [InnerProductSpace ℝ W] {ν : Measure α} {f g : α → W} (hf : MemLp f 2 ν) (hg : MemLp g 2 ν) :
    Integrable (fun z => inner ℝ (f z) (g z)) ν := by
  have := MeasureTheory.L2.integrable_inner (𝕜 := ℝ) (hf.toLp f) (hg.toLp g)
  refine this.congr ?_
  filter_upwards [MemLp.coeFn_toLp hf, MemLp.coeFn_toLp hg] with z h1 h2
  rw [h1, h2]

include hV in
/-- `κ ⟪f, g⟫` is Lebesgue integrable on the chart target when `f, g ∈ L²(ν)`. -/
theorem integrableOn_kappa_inner {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]
    {f g : F → W} (hf : MemLp f 2 (chartNu F V x₀)) (hg : MemLp g 2 (chartNu F V x₀)) :
    Integrable (fun z => chartKappa F V x₀ z * inner ℝ (f z) (g z))
      (volume.restrict (chartAt F x₀).target) := by
  have h1 := integrable_inner_memLp hf hg
  unfold chartNu at h1
  rw [integrable_withDensity_iff_integrable_smul₀' (aemeasurable_chartKappa F hV x₀)
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)] at h1
  refine h1.congr ?_
  filter_upwards [ae_restrict_mem (chartAt F x₀).open_target.measurableSet] with z hz
  simp [ENNReal.toReal_ofReal (chartKappa_pos F V x₀ hz).le]

end WeakEq

section WeakEq2

variable (F : Type) [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]
  {M : Type} [EMetricSpace M] [ChartedSpace F M] [IsManifold 𝓘(ℝ, F) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, F) ∞ F (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [MeasurableSpace M] [BorelSpace M]
  {V : M → ℝ} (hV : MSmooth F V) {μ : Measure M} [IsFiniteMeasure μ]
  (hμ : IsWeightedVolume F μ V) (x₀ : M)

/-- The test function on `M` obtained from `ψ ∈ C_c^∞(target)`. -/
noncomputable def chartTestFn {ψ : F → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ)
    (hψT : tsupport ψ ⊆ (chartAt F x₀).target) : testSub F M :=
  ⟨chartExtend F x₀ ψ, (chartExtend_mem F x₀ hψ hψc hψT).1⟩

theorem coe_chartTestFn {ψ : F → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ)
    (hψT : tsupport ψ ⊆ (chartAt F x₀).target) :
    (chartTestFn F x₀ hψ hψc hψT : M → ℝ) = chartExtend F x₀ ψ := rfl

theorem chartGrad_chartExtend {ψ : F → ℝ} {z : F} (hz : z ∈ (chartAt F x₀).target) :
    chartGrad F x₀ (chartExtend F x₀ ψ) z = gradient ψ z := by
  have hev : (chartExtend F x₀ ψ ∘ (chartAt F x₀).symm) =ᶠ[𝓝 z] ψ := by
    filter_upwards [(chartAt F x₀).open_target.mem_nhds hz] with w hw
    exact chartExtend_symm F x₀ hw
  unfold chartGrad gradient
  rw [hev.fderiv_eq]

include hV hμ in
/-- `⟪w, b⟫_{L²(μ)}` for `b` supported in the chart, as a chart integral (for any measurable
representative `h` of `w`). -/
theorem inner_lp_chartTestFn (w : M →₂[μ] ℝ) (h : M → ℝ) (hm : Measurable h)
    (hw : (w : M → ℝ) =ᵐ[μ] h) {ψ : F → ℝ} (hψ : ContDiff ℝ ∞ ψ)
    (hψc : HasCompactSupport ψ) (hψT : tsupport ψ ⊆ (chartAt F x₀).target) :
    inner ℝ w (testToL2 F μ (chartTestFn F x₀ hψ hψc hψT)) =
      ∫ z in (chartAt F x₀).target, chartRho F V x₀ z * (h ((chartAt F x₀).symm z) * ψ z) := by
  set φ := chartAt F x₀ with hφ
  set b := chartTestFn F x₀ hψ hψc hψT with hb
  have hTm : MeasurableSet φ.target := φ.open_target.measurableSet
  have hbS := (chartExtend_mem F x₀ hψ hψc hψT).2
  have e1 : inner ℝ w (testToL2 F μ b) = ∫ x, h x * (b : M → ℝ) x ∂μ := by
    rw [MeasureTheory.L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [coeFn_testToL2 F μ b, hw] with x hx hx2
    rw [hx, hx2]; simp [mul_comm]
  have hb0 : ∀ x, x ∉ φ.source → h x * (b : M → ℝ) x = 0 := fun x hx => by
    rw [hb, coe_chartTestFn, chartExtend_eq_zero F x₀ hx, mul_zero]
  rw [e1, ← setIntegral_eq_integral_of_forall_compl_eq_zero hb0]
  have hG : AEStronglyMeasurable (fun z => h (φ.symm z) * ψ z) (volume.restrict φ.target) := by
    have h1 : AEMeasurable (fun z => h (φ.symm z)) (volume.restrict φ.target) :=
      hm.comp_aemeasurable (φ.continuousOn_symm.aemeasurable hTm)
    exact (h1.aestronglyMeasurable).mul hψ.continuous.aestronglyMeasurable
  rw [← integral_chart_comp F hV hμ x₀ _ hG]
  refine setIntegral_congr_fun φ.open_source.measurableSet fun x hx => ?_
  rw [hb, coe_chartTestFn, chartExtend_eq F x₀ hx, φ.left_inv hx]

end WeakEq2

section WeakEq3

variable (F : Type) [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]
  {M : Type} [EMetricSpace M] [ChartedSpace F M] [IsManifold 𝓘(ℝ, F) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, F) ∞ F (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [MeasurableSpace M] [BorelSpace M]
  [IsRiemannianManifold 𝓘(ℝ, F) M] [ConnectedSpace M] [CompleteSpace M]
  {V : M → ℝ} (hV : MSmooth F V) {μ : Measure M} [IsFiniteMeasure μ]
  (hμ : IsWeightedVolume F μ V) (x₀ : M)

include hV hμ in
theorem integrableOn_term1 {Du : F → F} (hDu : MemLp Du 2 (chartNu F V x₀)) {ψ : F → ℝ}
    (hψ : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ) (hψT : tsupport ψ ⊆ (chartAt F x₀).target) :
    Integrable (fun z => inner ℝ (chartCoeff F x₀ z (Du z)) (gradient ψ z) * chartRho F V x₀ z)
      (volume.restrict (chartAt F x₀).target) := by
  set b := chartTestFn F x₀ hψ hψc hψT with hb
  have hbS := (chartExtend_mem F x₀ hψ hψc hψT).2
  have hH := memLp_chartTest F hV hμ x₀ b.2.1 b.2.2 hbS
  have hI := integrableOn_kappa_inner F hV x₀ hH hDu
  refine hI.congr ?_
  filter_upwards [ae_restrict_mem (chartAt F x₀).open_target.measurableSet] with z hz
  have hz' : z ∈ (extChartAt 𝓘(ℝ, F) x₀).target := by
    rw [CutoffRigidity.extChartAt_target_eq]; exact hz
  have hκ := chartKappa_pos F V x₀ hz
  have hg : chartGrad F x₀ (b : M → ℝ) z = gradient ψ z := chartGrad_chartExtend F x₀ hz
  simp only [hg, inner_smul_left, conj_trivial]
  rw [real_inner_comm, ← chartCoeff_symm F x₀ hz']
  field_simp

include hV hμ in
theorem integrableOn_term2 {f : F → ℝ} (hf : MemLp f 2 (chartNu F V x₀)) {ψ : F → ℝ}
    (hψ : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ) (hψT : tsupport ψ ⊆ (chartAt F x₀).target) :
    Integrable (fun z => f z * ψ z * chartRho F V x₀ z) (volume.restrict (chartAt F x₀).target) := by
  have hθ : MemLp (fun z => chartRho F V x₀ z * ψ z / chartKappa F V x₀ z) 2 (chartNu F V x₀) := by
    refine memLp_chartNu_of_continuousOn F hV hμ x₀ hψc hψT ?_ ?_
    · intro z hz
      have hz' : z ∈ (extChartAt 𝓘(ℝ, F) x₀).target := by
        rw [CutoffRigidity.extChartAt_target_eq]; exact hz
      exact (((contDiffAt_chartRho F hV x₀ hz').continuousAt.continuousWithinAt).mul
        hψ.continuous.continuousWithinAt).div ((continuousOn_chartKappa F hV x₀) z hz)
        (chartKappa_pos F V x₀ hz).ne'
    · intro z hz hzK
      have : ψ z = 0 := image_eq_zero_of_notMem_tsupport hzK
      simp [this]
  have hI := integrableOn_kappa_inner F hV x₀ hθ hf
  refine hI.congr ?_
  filter_upwards [ae_restrict_mem (chartAt F x₀).open_target.measurableSet] with z hz
  have hκ := (chartKappa_pos F V x₀ hz).ne'
  simp only [RCLike.inner_apply, conj_trivial]
  field_simp

end WeakEq3

section WeakEq4

variable (F : Type) [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]
  {M : Type} [EMetricSpace M] [ChartedSpace F M] [IsManifold 𝓘(ℝ, F) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, F) ∞ F (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [MeasurableSpace M] [BorelSpace M]
  [IsRiemannianManifold 𝓘(ℝ, F) M] [ConnectedSpace M] [CompleteSpace M]
  {V : M → ℝ} (hV : MSmooth F V) {μ : Measure M} [IsFiniteMeasure μ]
  (hμ : IsWeightedVolume F μ V) (x₀ : M) (T : DirFriedrichs (diffFormData F hV hμ))

include hV hμ in
/-- **Chart transfer of the weak equation.**  If `u ∈ Q` satisfies
`E(u,φ) + λ⟪u,φ⟫ = ⟪g,φ⟫` for all `φ ∈ Q` (e.g. `u = R_λ g`), then in the chart
`∫_T (⟪a Du, ∇ψ⟫ + λ ũ ψ) ρ dz = ∫_T g̃ ψ ρ dz` for all `ψ ∈ C_c^∞(T)`, where
`ũ = u∘φ⁻¹`, `g̃ = g∘φ⁻¹`, `a = chartCoeff` (inverse metric), `ρ = chartRho`, and `Du` is the weak
gradient of `ũ`. -/
theorem chart_weak_equation {u : M →₂[μ] ℝ} (hu : u ∈ T.Q) {lam : ℝ} (g : M →₂[μ] ℝ)
    (g' : M → ℝ) (hg'm : Measurable g') (hgg' : (g : M → ℝ) =ᵐ[μ] g')
    (hweak : ∀ φ ∈ T.Q, T.E u φ + lam * inner ℝ u φ = inner ℝ g φ) :
    ∃ Du : F → F, IsChartWeakGrad F V x₀ (u : M → ℝ) Du ∧
      ∀ ψ : F → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
        tsupport ψ ⊆ (chartAt F x₀).target →
        ∫ z in (chartAt F x₀).target,
            (inner ℝ (chartCoeff F x₀ z (Du z)) (gradient ψ z) +
              lam * (u : M → ℝ) ((chartAt F x₀).symm z) * ψ z) * chartRho F V x₀ z =
          ∫ z in (chartAt F x₀).target,
            g' ((chartAt F x₀).symm z) * ψ z * chartRho F V x₀ z := by
  obtain ⟨Du, hW, hE⟩ := Q_chart_weak F hV hμ x₀ T hu
  refine ⟨Du, hW, fun ψ hψ hψc hψT => ?_⟩
  set b := chartTestFn F x₀ hψ hψc hψT with hb
  have hbS := (chartExtend_mem F x₀ hψ hψc hψT).2
  have hTm : MeasurableSet (chartAt F x₀).target := (chartAt F x₀).open_target.measurableSet
  have hmem : (testToL2 F μ b : M →₂[μ] ℝ) ∈ T.Q := T.coe_mem ⟨testToL2 F μ b, b, rfl⟩
  have h1 := hweak _ hmem
  rw [hE b hbS, inner_lp_chartTestFn F hV hμ x₀ u (u : M → ℝ) (Lp.stronglyMeasurable u).measurable
      Filter.EventuallyEq.rfl hψ hψc hψT,
    inner_lp_chartTestFn F hV hμ x₀ g g' hg'm hgg' hψ hψc hψT] at h1
  have e1 : ∫ z in (chartAt F x₀).target, chartRho F V x₀ z *
      inner ℝ (chartGrad F x₀ (b : M → ℝ) z) (chartCoeff F x₀ z (Du z)) =
      ∫ z in (chartAt F x₀).target, inner ℝ (chartCoeff F x₀ z (Du z)) (gradient ψ z) *
        chartRho F V x₀ z := by
    refine setIntegral_congr_fun hTm fun z hz => ?_
    rw [coe_chartTestFn, chartGrad_chartExtend F x₀ hz, real_inner_comm, mul_comm]
  have e2 : ∫ z in (chartAt F x₀).target, chartRho F V x₀ z *
      ((u : M → ℝ) ((chartAt F x₀).symm z) * ψ z) =
      ∫ z in (chartAt F x₀).target, (u : M → ℝ) ((chartAt F x₀).symm z) * ψ z * chartRho F V x₀ z := by
    refine setIntegral_congr_fun hTm fun z hz => ?_
    ring
  have e3 : ∫ z in (chartAt F x₀).target, chartRho F V x₀ z *
      (g' ((chartAt F x₀).symm z) * ψ z) =
      ∫ z in (chartAt F x₀).target, g' ((chartAt F x₀).symm z) * ψ z * chartRho F V x₀ z := by
    refine setIntegral_congr_fun hTm fun z hz => ?_
    ring
  rw [e1, e2, e3] at h1
  have hi1 := integrableOn_term1 F hV hμ x₀ hW.memLp_Du hψ hψc hψT
  have hi2 := (integrableOn_term2 F hV hμ x₀ hW.memLp_u hψ hψc hψT).const_mul lam
  have : (fun z => (inner ℝ (chartCoeff F x₀ z (Du z)) (gradient ψ z) +
      lam * (u : M → ℝ) ((chartAt F x₀).symm z) * ψ z) * chartRho F V x₀ z) =
      fun z => inner ℝ (chartCoeff F x₀ z (Du z)) (gradient ψ z) * chartRho F V x₀ z +
        lam * ((u : M → ℝ) ((chartAt F x₀).symm z) * ψ z * chartRho F V x₀ z) := by
    funext z; ring
  rw [this, integral_add hi1 hi2, integral_const_mul]
  exact h1

end WeakEq4

end CutoffRigidity.Riemann.Diff
