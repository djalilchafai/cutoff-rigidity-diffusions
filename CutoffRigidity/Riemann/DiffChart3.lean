module

public import CutoffRigidity.Riemann.DiffChart2

/-! # The coordinate gradient of an element of the form domain (workstream DIR)

For `u ∈ Q` (limit of an energy-Cauchy sequence `fₙ = aₙ ∈ 𝒟`), the coordinate gradients
`∇(aₙ∘φ⁻¹)` are Cauchy in `L²(ν, F)`; the limit `Du` is the weak gradient of `ũ = u∘φ⁻¹`.
-/

@[expose] public section

open Bundle MeasureTheory Filter Set
open scoped Manifold ContDiff ENNReal Topology

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace CutoffRigidity.Riemann.Diff

open CutCur

section Limit

variable (F : Type) [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]
  {M : Type} [EMetricSpace M] [ChartedSpace F M] [IsManifold 𝓘(ℝ, F) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, F) ∞ F (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [MeasurableSpace M] [BorelSpace M]
  {V : M → ℝ} (hV : MSmooth F V) {μ : Measure M} [IsFiniteMeasure μ]
  (hμ : IsWeightedVolume F μ V) (x₀ : M)

include hV hμ in
theorem memLp_chartGrad (a : testSub F M) :
    MemLp (chartGrad F x₀ (a : M → ℝ)) 2 (chartNu F V x₀) := by
  have hTm : MeasurableSet (chartAt F x₀).target := (chartAt F x₀).open_target.measurableSet
  have hasm : AEStronglyMeasurable (chartGrad F x₀ (a : M → ℝ)) (chartNu F V x₀) :=
    ((continuousOn_chartGrad F x₀ a.2.1).aestronglyMeasurable hTm).mono_ac (chartNu_ac F x₀)
  have h1 := eLpNorm_two_sq hasm
  have h2 := chartGrad_lintegral_le F hV hμ x₀ a
  have h3 : eLpNorm (chartGrad F x₀ (a : M → ℝ)) 2 (chartNu F V x₀) ^ 2 < ⊤ := by
    rw [h1]; exact lt_of_le_of_lt h2 ENNReal.ofReal_lt_top
  show eLpNorm _ 2 _ < ⊤
  by_contra hcon
  rw [not_lt, top_le_iff] at hcon
  rw [hcon] at h3
  simp at h3

include hV hμ in
theorem memLp_chartPull {H : M → ℝ} (hH : Measurable H) (hmem : MemLp H 2 μ) :
    MemLp (fun z => H ((chartAt F x₀).symm z)) 2 (chartNu F V x₀) := by
  obtain ⟨hasm, hle⟩ := eLpNorm_chartNu_comp_le F hV hμ x₀ hH
  exact lt_of_le_of_lt hle hmem

/-- The `L²(ν, F)`-element given by the coordinate gradient of a test function. -/
noncomputable def gradLp (a : testSub F M) : Lp F 2 (chartNu F V x₀) :=
  (memLp_chartGrad F hV hμ x₀ a).toLp (chartGrad F x₀ (a : M → ℝ))

include hV hμ in
theorem norm_gradLp_sub_sq_le (a b : testSub F M) :
    ‖gradLp F hV hμ x₀ a - gradLp F hV hμ x₀ b‖ ^ 2 ≤
      ∫ x, carre F ((a - b : testSub F M) : M → ℝ) ((a - b : testSub F M) : M → ℝ) x ∂μ := by
  set ν := chartNu F V x₀ with hν
  have hTm : MeasurableSet (chartAt F x₀).target := (chartAt F x₀).open_target.measurableSet
  have hc := memLp_chartGrad F hV hμ x₀ (a - b)
  have hae : (fun z => chartGrad F x₀ (a : M → ℝ) z - chartGrad F x₀ (b : M → ℝ) z) =ᵐ[ν]
      chartGrad F x₀ ((a - b : testSub F M) : M → ℝ) := by
    have : ∀ᵐ z ∂(volume.restrict (chartAt F x₀).target), z ∈ (chartAt F x₀).target :=
      ae_restrict_mem hTm
    filter_upwards [(chartNu_ac F x₀).ae_le this] with z hz
    exact (chartGrad_sub F x₀ a.2.1 b.2.1 hz).symm
  have e1 : gradLp F hV hμ x₀ a - gradLp F hV hμ x₀ b =
      ((memLp_chartGrad F hV hμ x₀ a).sub (memLp_chartGrad F hV hμ x₀ b)).toLp
        (fun z => chartGrad F x₀ (a : M → ℝ) z - chartGrad F x₀ (b : M → ℝ) z) := by
    unfold gradLp
    exact (MemLp.toLp_sub _ _).symm
  rw [e1, Lp.norm_toLp]
  have hasm1 : AEStronglyMeasurable
      (fun z => chartGrad F x₀ (a : M → ℝ) z - chartGrad F x₀ (b : M → ℝ) z) ν :=
    ((memLp_chartGrad F hV hμ x₀ a).sub (memLp_chartGrad F hV hμ x₀ b)).aestronglyMeasurable
  have h2 := eLpNorm_two_sq hasm1
  have h3 : ∫⁻ z, ‖chartGrad F x₀ (a : M → ℝ) z - chartGrad F x₀ (b : M → ℝ) z‖ₑ ^ 2 ∂ν =
      ∫⁻ z, ‖chartGrad F x₀ ((a - b : testSub F M) : M → ℝ) z‖ₑ ^ 2 ∂ν := by
    refine lintegral_congr_ae ?_
    filter_upwards [hae] with z hz
    rw [hz]
  have h4 := chartGrad_lintegral_le F hV hμ x₀ (a - b)
  have h5 : eLpNorm (fun z => chartGrad F x₀ (a : M → ℝ) z - chartGrad F x₀ (b : M → ℝ) z) 2 ν ^ 2
      ≤ ENNReal.ofReal (∫ x, carre F ((a - b : testSub F M) : M → ℝ)
        ((a - b : testSub F M) : M → ℝ) x ∂μ) := by
    rw [h2, h3]; exact h4
  have hfin : eLpNorm (fun z => chartGrad F x₀ (a : M → ℝ) z - chartGrad F x₀ (b : M → ℝ) z) 2 ν
      ≠ ⊤ := ((memLp_chartGrad F hV hμ x₀ a).sub (memLp_chartGrad F hV hμ x₀ b)).ne
  have := ENNReal.toReal_mono ENNReal.ofReal_ne_top h5
  rw [ENNReal.toReal_pow, ENNReal.toReal_ofReal (integral_nonneg fun x => carre_nonneg F _ x)] at this
  exact this

/-- Transport to the chart of a measurable `L²(μ)` function, as an element of `L²(ν)`. -/
noncomputable def pullLp {H : M → ℝ} (hH : Measurable H) (hmem : MemLp H 2 μ) :
    Lp ℝ 2 (chartNu F V x₀) :=
  (memLp_chartPull F hV hμ x₀ hH hmem).toLp (fun z => H ((chartAt F x₀).symm z))

include hV hμ in
theorem norm_pullLp_sub_le {H H' : M → ℝ} (hH : Measurable H) (hmem : MemLp H 2 μ)
    (hH' : Measurable H') (hmem' : MemLp H' 2 μ) :
    ‖pullLp F hV hμ x₀ hH hmem - pullLp F hV hμ x₀ hH' hmem'‖ ≤ (eLpNorm (H - H') 2 μ).toReal := by
  have e1 : pullLp F hV hμ x₀ hH hmem - pullLp F hV hμ x₀ hH' hmem' =
      ((memLp_chartPull F hV hμ x₀ hH hmem).sub (memLp_chartPull F hV hμ x₀ hH' hmem')).toLp
        ((fun z => H ((chartAt F x₀).symm z)) - fun z => H' ((chartAt F x₀).symm z)) := by
    unfold pullLp
    exact (MemLp.toLp_sub _ _).symm
  rw [e1, Lp.norm_toLp]
  have := (eLpNorm_chartNu_comp_le F hV hμ x₀ (hH.sub hH')).2
  refine ENNReal.toReal_mono (hmem.sub hmem').ne ?_
  exact this

end Limit

section FormLimit

variable (F : Type) [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]
  {M : Type} [EMetricSpace M] [ChartedSpace F M] [IsManifold 𝓘(ℝ, F) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, F) ∞ F (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [MeasurableSpace M] [BorelSpace M]
  [IsRiemannianManifold 𝓘(ℝ, F) M] [ConnectedSpace M] [CompleteSpace M]
  {V : M → ℝ} (hV : MSmooth F V) {μ : Measure M} [IsFiniteMeasure μ]
  (hμ : IsWeightedVolume F μ V) (x₀ : M) (T : DirFriedrichs (diffFormData F hV hμ))

/-- The scalar transport of a test function as an element of `L²(ν)`. -/
noncomputable def testPullLp (a : testSub F M) : Lp ℝ 2 (chartNu F V x₀) :=
  pullLp F hV hμ x₀ a.2.1.continuous.measurable (testSub_memLp F a μ)

/-- The scalar transport of an `L²(μ)` class (via its strongly measurable representative). -/
noncomputable def lpPullLp (u : M →₂[μ] ℝ) : Lp ℝ 2 (chartNu F V x₀) :=
  pullLp F hV hμ x₀ (Lp.stronglyMeasurable u).measurable (Lp.memLp u)

theorem norm_toL2_sub_eq (a : testSub F M) (u : M →₂[μ] ℝ) :
    ‖testToL2 F μ a - u‖ = (eLpNorm ((a : M → ℝ) - (u : M → ℝ)) 2 μ).toReal := by
  have hmem := testSub_memLp F a μ
  have hu : MemLp (u : M → ℝ) 2 μ := Lp.memLp u
  have e2 : testToL2 F μ a - u = (hmem.sub hu).toLp ((a : M → ℝ) - (u : M → ℝ)) := by
    rw [MemLp.toLp_sub hmem hu, Lp.toLp_coeFn]
    rfl
  rw [e2, Lp.norm_toLp]

include hV hμ in
theorem exists_gradient_limit {u : M →₂[μ] ℝ} (hu : u ∈ T.Q) :
    ∃ (a : ℕ → testSub F M) (Ĝ : Lp F 2 (chartNu F V x₀)),
      Tendsto (fun n => testToL2 F μ (a n)) atTop (𝓝 u) ∧
      (diffFormData F hV hμ).EnCauchy (fun n => ⟨testToL2 F μ (a n), a n, rfl⟩) ∧
      Tendsto (fun n => gradLp F hV hμ x₀ (a n)) atTop (𝓝 Ĝ) ∧
      Tendsto (fun n => testPullLp F hV hμ x₀ (a n)) atTop (𝓝 (lpPullLp F hV hμ x₀ u)) := by
  obtain ⟨f, hf, hfc⟩ := (T.mem_Q u).1 hu
  choose a ha using fun n => (f n).2
  have hfa : ∀ n, f n = ⟨testToL2 F μ (a n), a n, rfl⟩ := fun n => Subtype.ext (ha n).symm
  have hfa' : f = fun n => ⟨testToL2 F μ (a n), a n, rfl⟩ := funext hfa
  have hconv : Tendsto (fun n => testToL2 F μ (a n)) atTop (𝓝 u) := by
    refine hf.congr (fun n => ?_)
    exact (ha n).symm
  have hcau : (diffFormData F hV hμ).EnCauchy (fun n => ⟨testToL2 F μ (a n), a n, rfl⟩) := by
    rw [← hfa']; exact hfc
  -- energy of differences
  have hen : ∀ m n, (diffFormData F hV hμ).en (⟨testToL2 F μ (a m), a m, rfl⟩ - ⟨testToL2 F μ (a n), a n, rfl⟩)
      (⟨testToL2 F μ (a m), a m, rfl⟩ - ⟨testToL2 F μ (a n), a n, rfl⟩) =
      ∫ x, carre F ((a m - a n : testSub F M) : M → ℝ) ((a m - a n : testSub F M) : M → ℝ) x ∂μ := by
    intro m n
    have : (⟨testToL2 F μ (a m), a m, rfl⟩ - ⟨testToL2 F μ (a n), a n, rfl⟩ :
        (diffFormData F hV hμ).D) = ⟨testToL2 F μ (a m - a n), a m - a n, rfl⟩ :=
      Subtype.ext (by simp [map_sub])
    rw [this, en_diffFormData F hV hμ]
  have hcs : CauchySeq (fun n => gradLp F hV hμ x₀ (a n)) := by
    rw [Metric.cauchySeq_iff]
    intro ε hε
    obtain ⟨N, hN⟩ := hcau (ε ^ 2) (by positivity)
    refine ⟨N, fun m hm n hn => ?_⟩
    rw [dist_eq_norm]
    have h1 := norm_gradLp_sub_sq_le F hV hμ x₀ (a m) (a n)
    have h2 := hN m hm n hn
    rw [hen] at h2
    exact (abs_lt.1 (abs_lt_of_sq_lt_sq (lt_of_le_of_lt h1 h2) hε.le)).2
  obtain ⟨Ĝ, hĜ⟩ := cauchySeq_tendsto_of_complete hcs
  refine ⟨a, Ĝ, hconv, hcau, hĜ, ?_⟩
  · -- scalar convergence
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have h0 : Tendsto (fun n => ‖testToL2 F μ (a n) - u‖) atTop (𝓝 0) :=
      tendsto_iff_norm_sub_tendsto_zero.1 hconv
    refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) h0
    rw [norm_toL2_sub_eq F (a n) u]
    exact norm_pullLp_sub_le F hV hμ x₀ _ _ _ _

end FormLimit

section Pairing

theorem tendsto_integral_inner_of_tendsto {α E : Type*} [MeasurableSpace α]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] {ν : Measure α} (θ : α → E)
    (hθ : MemLp θ 2 ν) (G : ℕ → Lp E 2 ν) (Ĝ : Lp E 2 ν) (h : Tendsto G atTop (𝓝 Ĝ)) :
    Tendsto (fun n => ∫ z, inner ℝ (θ z) (G n z) ∂ν) atTop
      (𝓝 (∫ z, inner ℝ (θ z) (Ĝ z) ∂ν)) := by
  have key : ∀ K : Lp E 2 ν, inner ℝ (hθ.toLp θ) K = ∫ z, inner ℝ (θ z) (K z) ∂ν := by
    intro K
    rw [MeasureTheory.L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [MemLp.coeFn_toLp hθ] with z hz
    rw [hz]
  have := Filter.Tendsto.inner (𝕜 := ℝ) (tendsto_const_nhds (x := hθ.toLp θ)) h
  simpa only [key] using this

end Pairing

section Test

variable (F : Type) [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]
  {M : Type} [EMetricSpace M] [ChartedSpace F M] [IsManifold 𝓘(ℝ, F) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, F) ∞ F (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [MeasurableSpace M] [BorelSpace M]
  {V : M → ℝ} (hV : MSmooth F V) {μ : Measure M} [IsFiniteMeasure μ]
  (hμ : IsWeightedVolume F μ V) (x₀ : M)

theorem ae_chartNu_mem_target : ∀ᵐ z ∂(chartNu F V x₀), z ∈ (chartAt F x₀).target :=
  (chartNu_ac F x₀).ae_le (ae_restrict_mem (chartAt F x₀).open_target.measurableSet)

include hV hμ in
/-- A function continuous on the chart target and supported (inside the target) in a compact
subset of it is in `L²(ν)`. -/
theorem memLp_chartNu_of_continuousOn {W : Type*} [NormedAddCommGroup W] {θ : F → W} {K : Set F}
    (hK : IsCompact K) (hKT : K ⊆ (chartAt F x₀).target) (hc : ContinuousOn θ (chartAt F x₀).target)
    (hz : ∀ z ∈ (chartAt F x₀).target, z ∉ K → θ z = 0) : MemLp θ 2 (chartNu F V x₀) := by
  haveI := isFiniteMeasure_chartNu F hV hμ x₀
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn (hc.mono hKT)
  have hasm : AEStronglyMeasurable θ (chartNu F V x₀) :=
    (hc.aestronglyMeasurable (chartAt F x₀).open_target.measurableSet).mono_ac (chartNu_ac F x₀)
  refine MemLp.of_bound hasm (max C 0) ?_
  filter_upwards [ae_chartNu_mem_target F x₀] with z hzT
  by_cases hzK : z ∈ K
  · exact (hC z hzK).trans (le_max_left _ _)
  · rw [hz z hzT hzK]; simp

end Test

section Energy

variable (F : Type) [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]
  {M : Type} [EMetricSpace M] [ChartedSpace F M] [IsManifold 𝓘(ℝ, F) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, F) ∞ F (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [MeasurableSpace M] [BorelSpace M]
  [IsRiemannianManifold 𝓘(ℝ, F) M] [ConnectedSpace M] [CompleteSpace M]
  {V : M → ℝ} (hV : MSmooth F V) {μ : Measure M} [IsFiniteMeasure μ]
  (hμ : IsWeightedVolume F μ V) (x₀ : M) (T : DirFriedrichs (diffFormData F hV hμ))

/-- `chartGrad b` vanishes on the target outside the image of the support of `b`. -/
theorem chartGrad_eq_zero_off {b : M → ℝ} (hbc : HasCompactSupport b)
    (hS : tsupport b ⊆ (chartAt F x₀).source) {z : F} (hz : z ∈ (chartAt F x₀).target)
    (hzK : z ∉ (chartAt F x₀) '' tsupport b) : chartGrad F x₀ b z = 0 := by
  set φ := chartAt F x₀ with hφ
  have hK : IsCompact (φ '' tsupport b) := hbc.image_of_continuousOn (φ.continuousOn.mono hS)
  have hev : (b ∘ φ.symm) =ᶠ[𝓝 z] fun _ => (0 : ℝ) := by
    filter_upwards [hK.isClosed.isOpen_compl.mem_nhds hzK, φ.open_target.mem_nhds hz] with w hw hwT
    by_contra hne
    apply hw
    exact ⟨φ.symm w, subset_tsupport b hne, φ.right_inv hwT⟩
  unfold chartGrad gradient
  rw [hev.fderiv_eq]
  simp

include hV hμ in
theorem memLp_chartTest {b : M → ℝ} (hb : MSmooth F b) (hbc : HasCompactSupport b)
    (hS : tsupport b ⊆ (chartAt F x₀).source) :
    MemLp (fun z => (chartRho F V x₀ z / chartKappa F V x₀ z) •
      chartCoeff F x₀ z (chartGrad F x₀ b z)) 2 (chartNu F V x₀) := by
  set φ := chartAt F x₀ with hφ
  have hK : IsCompact (φ '' tsupport b) := hbc.image_of_continuousOn (φ.continuousOn.mono hS)
  have hKT : φ '' tsupport b ⊆ φ.target := by
    rintro _ ⟨x, hx, rfl⟩; exact φ.map_source (hS hx)
  refine memLp_chartNu_of_continuousOn F hV hμ x₀ hK hKT ?_ ?_
  · intro z hz
    have hz' : z ∈ (extChartAt 𝓘(ℝ, F) x₀).target := by
      rw [CutoffRigidity.extChartAt_target_eq]; exact hz
    have h1 : ContinuousAt (chartRho F V x₀) z := (contDiffAt_chartRho F hV x₀ hz').continuousAt
    have h2 : ContinuousWithinAt (chartKappa F V x₀) φ.target z :=
      (continuousOn_chartKappa F hV x₀) z hz
    have h3 : ContinuousWithinAt (chartCoeff F x₀) φ.target z :=
      (contDiffOn_chartCoeff F x₀ z hz).continuousWithinAt
    have h4 := (continuousOn_chartGrad F x₀ hb) z hz
    exact ((h1.continuousWithinAt.div h2 (chartKappa_pos F V x₀ hz).ne').smul
      (h3.clm_apply h4))
  · intro z hz hzK
    simp [chartGrad_eq_zero_off F x₀ hbc hS hz hzK]

include hV hμ in
/-- **Energy pairing in a chart**: for `u ∈ Q` and `b ∈ 𝒟` supported in the chart,
`E(u, b) = ∫_T ρ ⟪∇(b∘φ⁻¹), a ∇u⟫ dz`, with `∇u` the weak gradient `Ĝ`. -/
theorem energy_pairing_of_limit {u : M →₂[μ] ℝ} (a : ℕ → testSub F M)
    (Ĝ : Lp F 2 (chartNu F V x₀))
    (hconv : Tendsto (fun n => testToL2 F μ (a n)) atTop (𝓝 u))
    (hcau : (diffFormData F hV hμ).EnCauchy (fun n => ⟨testToL2 F μ (a n), a n, rfl⟩))
    (hG : Tendsto (fun n => gradLp F hV hμ x₀ (a n)) atTop (𝓝 Ĝ))
    (b : testSub F M) (hS : tsupport (b : M → ℝ) ⊆ (chartAt F x₀).source) :
    T.E u (testToL2 F μ b) =
      ∫ z in (chartAt F x₀).target, chartRho F V x₀ z *
        inner ℝ (chartGrad F x₀ (b : M → ℝ) z) (chartCoeff F x₀ z (Ĝ z)) := by
  set φ := chartAt F x₀ with hφ
  have hTm : MeasurableSet φ.target := φ.open_target.measurableSet
  set H : F → F := fun z => (chartRho F V x₀ z / chartKappa F V x₀ z) •
      chartCoeff F x₀ z (chartGrad F x₀ (b : M → ℝ) z) with hH
  have hHmem : MemLp H 2 (chartNu F V x₀) := memLp_chartTest F hV hμ x₀ b.2.1 b.2.2 hS
  -- the energy side
  have h1 := T.E_lim (fun n => ⟨testToL2 F μ (a n), a n, rfl⟩) (fun _ => ⟨testToL2 F μ b, b, rfl⟩) u
    (testToL2 F μ b) hconv hcau tendsto_const_nhds (DirFormData.EnCauchy.const _)
  -- the chart side
  have h2 := tendsto_integral_inner_of_tendsto H hHmem (fun n => gradLp F hV hμ x₀ (a n)) Ĝ hG
  have hpair : ∀ (k : F → F), ∫ z, inner ℝ (H z) (k z) ∂(chartNu F V x₀) =
      ∫ z in φ.target, chartRho F V x₀ z *
        inner ℝ (chartGrad F x₀ (b : M → ℝ) z) (chartCoeff F x₀ z (k z)) := by
    intro k
    unfold chartNu
    rw [integral_withDensity_eq_integral_toReal_smul₀ (aemeasurable_chartKappa F hV x₀)
      (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
    refine setIntegral_congr_fun hTm fun z hz => ?_
    have hz' : z ∈ (extChartAt 𝓘(ℝ, F) x₀).target := by
      rw [CutoffRigidity.extChartAt_target_eq]; exact hz
    have hκ := chartKappa_pos F V x₀ hz
    simp only [smul_eq_mul, ENNReal.toReal_ofReal hκ.le, hH, inner_smul_left, conj_trivial]
    rw [← chartCoeff_symm F x₀ hz', real_inner_comm]
    field_simp
  rw [← hpair (fun z => Ĝ z)]
  refine tendsto_nhds_unique h1 (h2.congr fun n => ?_)
  -- equality of the two sequences
  have hae : ∀ᵐ z ∂(chartNu F V x₀), gradLp F hV hμ x₀ (a n) z = chartGrad F x₀ (a n : M → ℝ) z :=
    MemLp.coeFn_toLp (memLp_chartGrad F hV hμ x₀ (a n))
  have e1 : ∫ z, inner ℝ (H z) (gradLp F hV hμ x₀ (a n) z) ∂(chartNu F V x₀) =
      ∫ z, inner ℝ (H z) (chartGrad F x₀ (a n : M → ℝ) z) ∂(chartNu F V x₀) := by
    refine integral_congr_ae ?_
    filter_upwards [hae] with z hz
    rw [hz]
  rw [e1, hpair (fun z => chartGrad F x₀ (a n : M → ℝ) z)]
  have e2 : (diffFormData F hV hμ).en ⟨testToL2 F μ (a n), a n, rfl⟩ ⟨testToL2 F μ b, b, rfl⟩ =
      ∫ x, carre F (a n : M → ℝ) (b : M → ℝ) x ∂μ := en_diffFormData F hV hμ (a n) b
  rw [e2]
  have e3 : ∫ x, carre F (a n : M → ℝ) (b : M → ℝ) x ∂μ =
      ∫ x, carre F (b : M → ℝ) (a n : M → ℝ) x ∂μ :=
    integral_congr_ae (Eventually.of_forall fun x => carre_comm F _ _ x)
  rw [e3, integral_carre_chart F hV hμ x₀ b.2.1 (a n).2.1 hS]
  rfl

end Energy

end CutoffRigidity.Riemann.Diff
